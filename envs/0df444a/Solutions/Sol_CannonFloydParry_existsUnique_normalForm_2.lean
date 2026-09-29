-- Prove2me | solution 2 for CannonFloydParry.existsUnique_normalForm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T17:56:27.586994+00:00
-- url     : https://prove2.me/submissions/82eb1b84-32ea-47bd-84e9-1b1f84410c93

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib
import Theorems.Thm_CannonFloydParry_represents_mul
import Theorems.Thm_CannonFloydParry_getLast_exponents_eq_zero
import Theorems.Thm_CannonFloydParry_exists_isNormalFormData
import Theorems.Thm_CannonFloydParry_exists_isReduced_represents
import Theorems.Thm_CannonFloydParry_isReduced_represents_unique

namespace CannonFloydParry

/-! ### `extend` of the two generators is the underlying function on the line -/

lemma extend_mapA (z : ℝ) : extend mapA z = aFun z := by
  by_cases h : z ∈ Set.Icc (0 : ℝ) 1
  · rw [extend_apply, extendFun_of_mem _ h]
    show ((mapA ⟨z, h⟩ : UI) : ℝ) = aFun z
    rw [mapA, restrict_coe]
    rfl
  · rw [extend_apply, extendFun_of_notMem _ h]
    simp only [Set.mem_Icc, not_and_or, not_le] at h
    rcases h with h | h
    · exact (aFun_of_le_zero (le_of_lt h)).symm
    · exact (aFun_of_one_le (le_of_lt h)).symm

lemma extend_mapB (z : ℝ) : extend mapB z = bFun z := by
  by_cases h : z ∈ Set.Icc (0 : ℝ) 1
  · rw [extend_apply, extendFun_of_mem _ h]
    show ((mapB ⟨z, h⟩ : UI) : ℝ) = bFun z
    rw [mapB, restrict_coe]
    rfl
  · rw [extend_apply, extendFun_of_notMem _ h]
    simp only [Set.mem_Icc, not_and_or, not_le] at h
    rcases h with h | h
    · exact (bFun_of_le_half (by linarith)).symm
    · exact (bFun_of_one_le (le_of_lt h)).symm

lemma coe_extend_mapA : (⇑(extend mapA) : ℝ → ℝ) = aFun := funext extend_mapA

lemma coe_extend_mapB : (⇑(extend mapB) : ℝ → ℝ) = bFun := funext extend_mapB

/-! ### Marks lie strictly inside, and `marksAux` is natural for affine maps -/

lemma marksAux_mem_Ioo : ∀ (t : TTree) (a b : ℝ), a < b →
    ∀ x ∈ t.marksAux a b, a < x ∧ x < b := by
  intro t
  induction t with
  | leaf => intro a b _ x hx; simp [TTree.marksAux] at hx
  | node l r ihl ihr =>
      intro a b hab x hx
      have hm1 : a < (a + b) / 2 := by linarith
      have hm2 : (a + b) / 2 < b := by linarith
      rw [TTree.marksAux] at hx
      rcases List.mem_append.mp hx with h | h
      · obtain ⟨h1, h2⟩ := ihl a ((a + b) / 2) hm1 x h
        exact ⟨h1, lt_trans h2 hm2⟩
      · rcases List.mem_cons.mp h with rfl | h
        · exact ⟨hm1, hm2⟩
        · obtain ⟨h1, h2⟩ := ihr ((a + b) / 2) b hm2 x h
          exact ⟨lt_trans hm1 h1, h2⟩

/-- An affine map carries the marks of a tree on `[a,b]` to the marks of the same tree on the
image interval.  Only the values of `L` on `[a,b]` matter, which is what lets this be applied
piece by piece to a map that is merely piecewise affine. -/
lemma marksAux_map_affine {L : ℝ → ℝ} : ∀ (t : TTree) (a b p q : ℝ), a < b →
    (∀ z ∈ Set.Icc a b, L z = p * z + q) →
    (t.marksAux a b).map L = t.marksAux (p * a + q) (p * b + q) := by
  intro t
  induction t with
  | leaf => intro a b p q _ _; simp [TTree.marksAux]
  | node l r ihl ihr =>
      intro a b p q hab hL
      have hm1 : a < (a + b) / 2 := by linarith
      have hm2 : (a + b) / 2 < b := by linarith
      have hLm : L ((a + b) / 2) = p * ((a + b) / 2) + q :=
        hL _ ⟨by linarith, by linarith⟩
      have hmid : ((p * a + q) + (p * b + q)) / 2 = p * ((a + b) / 2) + q := by ring
      have hR : TTree.marksAux (TTree.node l r) (p * a + q) (p * b + q)
          = TTree.marksAux l (p * a + q) (p * ((a + b) / 2) + q)
            ++ (p * ((a + b) / 2) + q)
              :: TTree.marksAux r (p * ((a + b) / 2) + q) (p * b + q) := by
        rw [TTree.marksAux, hmid]
      rw [TTree.marksAux, List.map_append, List.map_cons, hR, hLm,
        ihl a ((a + b) / 2) p q hm1 (fun z hz => hL z ⟨hz.1, by linarith [hz.2]⟩),
        ihr ((a + b) / 2) b p q hm2 (fun z hz => hL z ⟨by linarith [hz.1], hz.2⟩)]

/-! ### `A` is the rotation at the root

`A` carries `[0,1/2]`, `[1/2,3/4]`, `[3/4,1]` affinely onto `[0,1/4]`, `[1/4,1/2]`, `[1/2,1]`.
Reading those as the three blocks of `node l (node x y)` and of `node (node l x) y`, `A` carries
the marks of the first tree to the marks of the second, whatever `l`, `x`, `y` are. -/

lemma aFun_affine1 : ∀ z ∈ Set.Icc (0 : ℝ) (1 / 2), aFun z = (1 / 2) * z + 0 := by
  intro z hz; rw [aFun_of_mem1 hz.1 hz.2]; ring

lemma aFun_affine2 : ∀ z ∈ Set.Icc (1 / 2 : ℝ) (3 / 4), aFun z = 1 * z + (-(1 / 4)) := by
  intro z hz; rw [aFun_of_mem2 hz.1 hz.2]; ring

lemma aFun_affine3 : ∀ z ∈ Set.Icc (3 / 4 : ℝ) 1, aFun z = 2 * z + (-1) := by
  intro z hz; rw [aFun_of_mem3 hz.1 hz.2]; ring

lemma marksAux_rotA_dom (l x y : TTree) :
    (TTree.node l (TTree.node x y)).marksAux 0 1
      = l.marksAux 0 (1 / 2) ++ (1 / 2 : ℝ) ::
          (x.marksAux (1 / 2) (3 / 4) ++ (3 / 4 : ℝ) :: y.marksAux (3 / 4) 1) := by
  rw [TTree.marksAux, show ((0 : ℝ) + 1) / 2 = 1 / 2 by norm_num, TTree.marksAux,
    show ((1 : ℝ) / 2 + 1) / 2 = 3 / 4 by norm_num]

lemma marksAux_rotA_ran (l x y : TTree) :
    (TTree.node (TTree.node l x) y).marksAux 0 1
      = (l.marksAux 0 (1 / 4) ++ (1 / 4 : ℝ) :: x.marksAux (1 / 4) (1 / 2))
          ++ (1 / 2 : ℝ) :: y.marksAux (1 / 2) 1 := by
  rw [TTree.marksAux, show ((0 : ℝ) + 1) / 2 = 1 / 2 by norm_num, TTree.marksAux,
    show ((0 : ℝ) + 1 / 2) / 2 = 1 / 4 by norm_num]

lemma marks_rotA (l x y : TTree) :
    (TTree.node l (TTree.node x y)).marks.map (extend mapA)
      = (TTree.node (TTree.node l x) y).marks := by
  have h1 : (l.marksAux 0 (1 / 2)).map aFun = l.marksAux 0 (1 / 4) := by
    have h := marksAux_map_affine l 0 (1 / 2) (1 / 2) 0 (by norm_num) aFun_affine1
    rw [show ((1 : ℝ) / 2) * 0 + 0 = 0 by ring,
      show ((1 : ℝ) / 2) * (1 / 2) + 0 = 1 / 4 by ring] at h
    exact h
  have h2 : (x.marksAux (1 / 2) (3 / 4)).map aFun = x.marksAux (1 / 4) (1 / 2) := by
    have h := marksAux_map_affine x (1 / 2) (3 / 4) 1 (-(1 / 4)) (by norm_num) aFun_affine2
    rw [show (1 : ℝ) * (1 / 2) + (-(1 / 4)) = 1 / 4 by ring,
      show (1 : ℝ) * (3 / 4) + (-(1 / 4)) = 1 / 2 by ring] at h
    exact h
  have h3 : (y.marksAux (3 / 4) 1).map aFun = y.marksAux (1 / 2) 1 := by
    have h := marksAux_map_affine y (3 / 4) 1 2 (-1) (by norm_num) aFun_affine3
    rw [show (2 : ℝ) * (3 / 4) + (-1) = 1 / 2 by ring,
      show (2 : ℝ) * 1 + (-1) = 1 by ring] at h
    exact h
  have e0 : aFun 0 = 0 := by rw [aFun_of_mem1 (le_refl 0) (by norm_num)]; ring
  have e1 : aFun (1 / 2) = 1 / 4 := by rw [aFun_of_mem1 (by norm_num) (le_refl _)]; ring
  have e2 : aFun (3 / 4) = 1 / 2 := by rw [aFun_of_mem2 (by norm_num) (le_refl _)]; ring
  have e3 : aFun 1 = 1 := by rw [aFun_of_one_le (le_refl 1)]
  show ((0 : ℝ) :: ((TTree.node l (TTree.node x y)).marksAux 0 1 ++ [1])).map (extend mapA)
      = (0 : ℝ) :: ((TTree.node (TTree.node l x) y).marksAux 0 1 ++ [1])
  rw [coe_extend_mapA, marksAux_rotA_dom, marksAux_rotA_ran, List.map_cons, List.map_append,
    List.map_cons, List.map_append, List.map_cons, List.map_append, List.map_cons,
    h1, h2, h3, e0, e1, e2, e3]
  simp [List.append_assoc]

/-! ### `B` is the rotation one step down the right side -/

lemma bFun_affine0 : ∀ z ∈ Set.Icc (0 : ℝ) (1 / 2), bFun z = 1 * z + 0 := by
  intro z hz; rw [bFun_of_le_half hz.2]; ring

lemma bFun_affine1 : ∀ z ∈ Set.Icc (1 / 2 : ℝ) (3 / 4), bFun z = (1 / 2) * z + (1 / 4) := by
  intro z hz; rw [bFun_of_mem1 hz.1 hz.2]; ring

lemma bFun_affine2 : ∀ z ∈ Set.Icc (3 / 4 : ℝ) (7 / 8), bFun z = 1 * z + (-(1 / 8)) := by
  intro z hz; rw [bFun_of_mem2 hz.1 hz.2]; ring

lemma bFun_affine3 : ∀ z ∈ Set.Icc (7 / 8 : ℝ) 1, bFun z = 2 * z + (-1) := by
  intro z hz; rw [bFun_of_mem3 hz.1 hz.2]; ring

lemma marksAux_rotB_dom (w l x y : TTree) :
    (TTree.node w (TTree.node l (TTree.node x y))).marksAux 0 1
      = w.marksAux 0 (1 / 2) ++ (1 / 2 : ℝ) ::
          (l.marksAux (1 / 2) (3 / 4) ++ (3 / 4 : ℝ) ::
            (x.marksAux (3 / 4) (7 / 8) ++ (7 / 8 : ℝ) :: y.marksAux (7 / 8) 1)) := by
  rw [TTree.marksAux, show ((0 : ℝ) + 1) / 2 = 1 / 2 by norm_num, TTree.marksAux,
    show ((1 : ℝ) / 2 + 1) / 2 = 3 / 4 by norm_num, TTree.marksAux,
    show ((3 : ℝ) / 4 + 1) / 2 = 7 / 8 by norm_num]

lemma marksAux_rotB_ran (w l x y : TTree) :
    (TTree.node w (TTree.node (TTree.node l x) y)).marksAux 0 1
      = w.marksAux 0 (1 / 2) ++ (1 / 2 : ℝ) ::
          ((l.marksAux (1 / 2) (5 / 8) ++ (5 / 8 : ℝ) :: x.marksAux (5 / 8) (3 / 4))
            ++ (3 / 4 : ℝ) :: y.marksAux (3 / 4) 1) := by
  rw [TTree.marksAux, show ((0 : ℝ) + 1) / 2 = 1 / 2 by norm_num, TTree.marksAux,
    show ((1 : ℝ) / 2 + 1) / 2 = 3 / 4 by norm_num, TTree.marksAux,
    show ((1 : ℝ) / 2 + 3 / 4) / 2 = 5 / 8 by norm_num]

lemma marks_rotB (w l x y : TTree) :
    (TTree.node w (TTree.node l (TTree.node x y))).marks.map (extend mapB)
      = (TTree.node w (TTree.node (TTree.node l x) y)).marks := by
  have h0 : (w.marksAux 0 (1 / 2)).map bFun = w.marksAux 0 (1 / 2) := by
    have h := marksAux_map_affine w 0 (1 / 2) 1 0 (by norm_num) bFun_affine0
    rw [show (1 : ℝ) * 0 + 0 = 0 by ring,
      show (1 : ℝ) * (1 / 2) + 0 = 1 / 2 by ring] at h
    exact h
  have h1 : (l.marksAux (1 / 2) (3 / 4)).map bFun = l.marksAux (1 / 2) (5 / 8) := by
    have h := marksAux_map_affine l (1 / 2) (3 / 4) (1 / 2) (1 / 4) (by norm_num) bFun_affine1
    rw [show ((1 : ℝ) / 2) * (1 / 2) + 1 / 4 = 1 / 2 by ring,
      show ((1 : ℝ) / 2) * (3 / 4) + 1 / 4 = 5 / 8 by ring] at h
    exact h
  have h2 : (x.marksAux (3 / 4) (7 / 8)).map bFun = x.marksAux (5 / 8) (3 / 4) := by
    have h := marksAux_map_affine x (3 / 4) (7 / 8) 1 (-(1 / 8)) (by norm_num) bFun_affine2
    rw [show (1 : ℝ) * (3 / 4) + (-(1 / 8)) = 5 / 8 by ring,
      show (1 : ℝ) * (7 / 8) + (-(1 / 8)) = 3 / 4 by ring] at h
    exact h
  have h3 : (y.marksAux (7 / 8) 1).map bFun = y.marksAux (3 / 4) 1 := by
    have h := marksAux_map_affine y (7 / 8) 1 2 (-1) (by norm_num) bFun_affine3
    rw [show (2 : ℝ) * (7 / 8) + (-1) = 3 / 4 by ring,
      show (2 : ℝ) * 1 + (-1) = 1 by ring] at h
    exact h
  have e0 : bFun 0 = 0 := by rw [bFun_of_le_half (by norm_num)]
  have e1 : bFun (1 / 2) = 1 / 2 := by rw [bFun_of_le_half (le_refl _)]
  have e2 : bFun (3 / 4) = 5 / 8 := by rw [bFun_of_mem1 (by norm_num) (le_refl _)]; ring
  have e3 : bFun (7 / 8) = 3 / 4 := by rw [bFun_of_mem2 (by norm_num) (le_refl _)]; ring
  have e4 : bFun 1 = 1 := by rw [bFun_of_one_le (le_refl 1)]
  show ((0 : ℝ) :: ((TTree.node w (TTree.node l (TTree.node x y))).marksAux 0 1 ++ [1])).map
        (extend mapB)
      = (0 : ℝ) :: ((TTree.node w (TTree.node (TTree.node l x) y)).marksAux 0 1 ++ [1])
  rw [coe_extend_mapB, marksAux_rotB_dom, marksAux_rotB_ran, List.map_cons, List.map_append,
    List.map_cons, List.map_append, List.map_cons, List.map_append, List.map_cons,
    List.map_append, List.map_cons, h0, h1, h2, h3, e0, e1, e2, e3, e4]
  simp [List.append_assoc]

end CannonFloydParry

namespace CannonFloydParry

/-! ### Chains from a uniform relation -/

lemma chain_getD {R : ℝ → ℝ → Prop} : ∀ (xs : List ℝ), List.IsChain R xs →
    ∀ j, j + 1 < xs.length → R (xs.getD j 0) (xs.getD (j + 1) 0) := by
  intro xs
  induction xs with
  | nil => intro _ j hj; simp at hj
  | cons x rest ih =>
      intro hch j hj
      cases j with
      | zero =>
          cases rest with
          | nil => simp at hj
          | cons y t =>
              have := (List.isChain_cons.mp hch).1 y (by simp)
              simpa using this
      | succ j =>
          have hch' := (List.isChain_cons.mp hch).2
          have := ih hch' j (by simpa using hj)
          simpa using this

lemma getD_chain {R : ℝ → ℝ → Prop} : ∀ (xs : List ℝ),
    (∀ j, j + 1 < xs.length → R (xs.getD j 0) (xs.getD (j + 1) 0)) → List.IsChain R xs := by
  intro xs
  induction xs with
  | nil => intro _; exact List.isChain_nil
  | cons x rest ih =>
      intro h
      refine List.isChain_cons.mpr ⟨?_, ih ?_⟩
      · intro y hy
        cases rest with
        | nil => simp at hy
        | cons z t =>
            have hyz : z = y := by simpa using hy
            subst hyz
            have := h 0 (by simp)
            simpa using this
      · intro j hj
        have := h (j + 1) (by simpa using hj)
        simpa using this

lemma getD_mem {xs : List ℝ} {j : ℕ} (h : j < xs.length) : xs.getD j 0 ∈ xs := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

lemma isChain_of_pairs {R : ℝ → ℝ → Prop} (xs : List ℝ)
    (h : ∀ u ∈ xs, ∀ v ∈ xs, R u v) : List.IsChain R xs := by
  refine getD_chain _ ?_
  intro j hj
  exact h _ (getD_mem (by omega)) _ (getD_mem (by omega))

lemma mem_Icc_of_mem_block (t : TTree) {a b : ℝ} (hab : a < b) :
    ∀ u ∈ a :: (t.marksAux a b ++ [b]), u ∈ Set.Icc a b := by
  intro u hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact ⟨le_refl _, le_of_lt hab⟩
  · rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨h1, h2⟩ := marksAux_mem_Ioo t a b hab u hu
      exact ⟨le_of_lt h1, le_of_lt h2⟩
    · have hub : u = b := by simpa using hu
      exact ⟨by rw [hub]; exact le_of_lt hab, by rw [hub]⟩

/-- On a block whose endpoints bound one affine piece of `L`, every consecutive pair of marks
admits the same affine formula. -/
lemma isChain_affine_block {L : ℝ ≃o ℝ} (t : TTree) (a b p q : ℝ) (hab : a < b)
    (hL : ∀ z ∈ Set.Icc a b, L z = p * z + q) :
    List.IsChain (fun u v => ∃ p' q' : ℝ, ∀ z ∈ Set.Icc u v, L z = p' * z + q')
      (a :: (t.marksAux a b ++ [b])) := by
  refine isChain_of_pairs _ ?_
  intro u hu v hv
  obtain ⟨hu1, hu2⟩ := mem_Icc_of_mem_block t hab u hu
  obtain ⟨hv1, hv2⟩ := mem_Icc_of_mem_block t hab v hv
  exact ⟨p, q, fun z hz => hL z ⟨le_trans hu1 hz.1, le_trans hz.2 hv2⟩⟩

end CannonFloydParry

namespace CannonFloydParry

/-! ### The marks of a tree increase -/

lemma isChain_lt_marksAux : ∀ (t : TTree) (a b : ℝ), a < b →
    List.IsChain (· < ·) (a :: (t.marksAux a b ++ [b])) := by
  intro t
  induction t with
  | leaf =>
      intro a b hab
      simp only [TTree.marksAux, List.nil_append]
      exact List.isChain_pair.mpr hab
  | node l r ihl ihr =>
      intro a b hab
      have hm1 : a < (a + b) / 2 := by linarith
      have hm2 : (a + b) / 2 < b := by linarith
      have Hl := ihl a ((a + b) / 2) hm1
      have Hr := ihr ((a + b) / 2) b hm2
      rw [TTree.marksAux]
      have := List.IsChain.append_overlap (R := (· < · : ℝ → ℝ → Prop))
        (l₁ := a :: TTree.marksAux l a ((a + b) / 2))
        (l₂ := [(a + b) / 2])
        (l₃ := TTree.marksAux r ((a + b) / 2) b ++ [b])
        (by simpa using Hl) (by simpa using Hr) (by simp)
      simpa using this

lemma isChain_lt_marks (t : TTree) : List.IsChain (· < ·) t.marks := by
  have h := isChain_lt_marksAux t 0 1 (by norm_num)
  simpa [TTree.marks] using h

lemma marks_getD_lt (t : TTree) {j : ℕ} (hj : j + 1 < t.marks.length) :
    t.marks.getD j 0 < t.marks.getD (j + 1) 0 :=
  chain_getD _ (isChain_lt_marks t) j hj

lemma marks_length_eq (t : TTree) : t.marks.length = t.leafCount + 1 := by
  have haux : ∀ (u : TTree) (a b : ℝ), (u.marksAux a b).length + 1 = u.leafCount := by
    intro u
    induction u with
    | leaf => intro a b; simp [TTree.marksAux, TTree.leafCount]
    | node l r ihl ihr =>
        intro a b
        rw [TTree.marksAux, TTree.leafCount]
        have h1 := ihl a ((a + b) / 2)
        have h2 := ihr ((a + b) / 2) b
        simp only [List.length_append, List.length_cons]
        omega
  show ((0 : ℝ) :: (t.marksAux 0 1 ++ [1])).length = t.leafCount + 1
  have := haux t 0 1
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

lemma one_le_leafCount' (t : TTree) : 1 ≤ t.leafCount := by
  induction t with
  | leaf => simp [TTree.leafCount]
  | node l r ihl ihr => rw [TTree.leafCount]; omega

/-! ### Every point of `[0,1]` lies in one of the pieces -/

/-! ### An element is determined by its diagram -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### The two generators lie in `F` -/

lemma coe_mapA (z : UI) : (mapA z : ℝ) = aFun (z : ℝ) := by
  rw [mapA, restrict_coe]; rfl

lemma coe_mapB (z : UI) : (mapB z : ℝ) = bFun (z : ℝ) := by
  rw [mapB, restrict_coe]; rfl

lemma isThompson_mapA : IsThompson mapA := by
  refine ⟨{0, 1/2, 3/4, 1}, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨0, 0, by norm_num⟩
    · exact ⟨1, 1, by norm_num⟩
    · exact ⟨3, 2, by norm_num⟩
    · exact ⟨1, 0, by norm_num⟩
  · intro x y hxy hgap
    rw [Set.eq_empty_iff_forall_notMem] at hgap
    have hb : ∀ b : ℝ, b ∈ ({0, 1/2, 3/4, 1} : Finset ℝ) →
        b ≤ (x : ℝ) ∨ (y : ℝ) ≤ b := by
      intro b hbm
      by_contra hc
      push_neg at hc
      exact hgap b ⟨⟨hc.1, hc.2⟩, by exact_mod_cast hbm⟩
    have h0 := hb 0 (by simp)
    have h1 := hb (1/2) (by simp)
    have h2 := hb (3/4) (by simp)
    have h3 := hb 1 (by simp)
    rcases h0 with h0 | h0
    · rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · rcases h3 with h3 | h3
          · refine ⟨0, 0, fun z hz => ?_⟩
            rw [coe_mapA, aFun_of_one_le (by linarith [hz.1])]; norm_num
          · refine ⟨1, -1, fun z hz => ?_⟩
            rw [coe_mapA, aFun_of_mem3 (by linarith [hz.1]) (by linarith [hz.2]), zpow_one]
            ring
        · refine ⟨0, -(1/4), fun z hz => ?_⟩
          rw [coe_mapA, aFun_of_mem2 (by linarith [hz.1]) (by linarith [hz.2]), zpow_zero]
          ring
      · refine ⟨-1, 0, fun z hz => ?_⟩
        rw [coe_mapA, aFun_of_mem1 (by linarith [hz.1]) (by linarith [hz.2]),
          zpow_neg, zpow_one]
        ring
    · refine ⟨0, 0, fun z hz => ?_⟩
      rw [coe_mapA, aFun_of_le_zero (by linarith [hz.2])]; norm_num

lemma isThompson_mapB : IsThompson mapB := by
  refine ⟨{0, 1/2, 3/4, 7/8, 1}, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, 0, by norm_num⟩
    · exact ⟨1, 1, by norm_num⟩
    · exact ⟨3, 2, by norm_num⟩
    · exact ⟨7, 3, by norm_num⟩
    · exact ⟨1, 0, by norm_num⟩
  · intro x y hxy hgap
    rw [Set.eq_empty_iff_forall_notMem] at hgap
    have hb : ∀ b : ℝ, b ∈ ({0, 1/2, 3/4, 7/8, 1} : Finset ℝ) →
        b ≤ (x : ℝ) ∨ (y : ℝ) ≤ b := by
      intro b hbm
      by_contra hc
      push_neg at hc
      exact hgap b ⟨⟨hc.1, hc.2⟩, by exact_mod_cast hbm⟩
    have h0 := hb 0 (by simp)
    have h1 := hb (1/2) (by simp)
    have h2 := hb (3/4) (by simp)
    have h3 := hb (7/8) (by simp)
    have h4 := hb 1 (by simp)
    rcases h0 with h0 | h0
    · rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · rcases h3 with h3 | h3
          · rcases h4 with h4 | h4
            · refine ⟨0, 0, fun z hz => ?_⟩
              rw [coe_mapB, bFun_of_one_le (by linarith [hz.1])]; norm_num
            · refine ⟨1, -1, fun z hz => ?_⟩
              rw [coe_mapB, bFun_of_mem3 (by linarith [hz.1]) (by linarith [hz.2]), zpow_one]
              ring
          · refine ⟨0, -(1/8), fun z hz => ?_⟩
            rw [coe_mapB, bFun_of_mem2 (by linarith [hz.1]) (by linarith [hz.2]), zpow_zero]
            ring
        · refine ⟨-1, 1/4, fun z hz => ?_⟩
          rw [coe_mapB, bFun_of_mem1 (by linarith [hz.1]) (by linarith [hz.2]),
            zpow_neg, zpow_one]
          ring
      · refine ⟨0, 0, fun z hz => ?_⟩
        rw [coe_mapB, bFun_of_le_half (by linarith [hz.2]), zpow_zero]; ring
    · refine ⟨0, 0, fun z hz => ?_⟩
      rw [coe_mapB, bFun_of_le_half (by linarith [hz.2]), zpow_zero]; ring

lemma mapA_mem_F : mapA ∈ F := mem_F_of_isThompson isThompson_mapA

lemma mapB_mem_F : mapB ∈ F := mem_F_of_isThompson isThompson_mapB

/-! ### Affineness on the pieces, for the two rotations -/

lemma extendA_affine1 : ∀ z ∈ Set.Icc (0 : ℝ) (1 / 2),
    extend mapA z = (1 / 2) * z + 0 := by
  intro z hz; rw [extend_mapA]; exact aFun_affine1 z hz

lemma extendA_affine2 : ∀ z ∈ Set.Icc (1 / 2 : ℝ) (3 / 4),
    extend mapA z = 1 * z + (-(1 / 4)) := by
  intro z hz; rw [extend_mapA]; exact aFun_affine2 z hz

lemma extendA_affine3 : ∀ z ∈ Set.Icc (3 / 4 : ℝ) 1,
    extend mapA z = 2 * z + (-1) := by
  intro z hz; rw [extend_mapA]; exact aFun_affine3 z hz

lemma affineOnPieces_rotA (l x y : TTree) :
    AffineOnPieces (extend mapA) (TTree.node l (TTree.node x y)).marks := by
  have CB1 := isChain_affine_block l 0 (1 / 2) (1 / 2) 0 (by norm_num) extendA_affine1
  have CB2 := isChain_affine_block x (1 / 2) (3 / 4) 1 (-(1 / 4)) (by norm_num) extendA_affine2
  have CB3 := isChain_affine_block y (3 / 4) 1 2 (-1) (by norm_num) extendA_affine3
  have G1 := List.IsChain.append_overlap
    (R := fun u v => ∃ p' q' : ℝ, ∀ z ∈ Set.Icc u v, extend mapA z = p' * z + q')
    (l₁ := (0 : ℝ) :: l.marksAux 0 (1 / 2))
    (l₂ := [(1 / 2 : ℝ)])
    (l₃ := x.marksAux (1 / 2) (3 / 4) ++ [(3 / 4 : ℝ)])
    (by simpa using CB1) (by simpa using CB2) (by simp)
  have G2 := List.IsChain.append_overlap
    (R := fun u v => ∃ p' q' : ℝ, ∀ z ∈ Set.Icc u v, extend mapA z = p' * z + q')
    (l₁ := ((0 : ℝ) :: l.marksAux 0 (1 / 2)) ++ [(1 / 2 : ℝ)] ++ x.marksAux (1 / 2) (3 / 4))
    (l₂ := [(3 / 4 : ℝ)])
    (l₃ := y.marksAux (3 / 4) 1 ++ [(1 : ℝ)])
    (by simpa using G1) (by simpa using CB3) (by simp)
  show List.IsChain (fun u v => ∃ p' q' : ℝ, ∀ z ∈ Set.Icc u v, extend mapA z = p' * z + q')
    ((0 : ℝ) :: ((TTree.node l (TTree.node x y)).marksAux 0 1 ++ [1]))
  rw [marksAux_rotA_dom]
  simpa using G2

lemma extendB_affine0 : ∀ z ∈ Set.Icc (0 : ℝ) (1 / 2), extend mapB z = 1 * z + 0 := by
  intro z hz; rw [extend_mapB]; exact bFun_affine0 z hz

lemma extendB_affine1 : ∀ z ∈ Set.Icc (1 / 2 : ℝ) (3 / 4),
    extend mapB z = (1 / 2) * z + (1 / 4) := by
  intro z hz; rw [extend_mapB]; exact bFun_affine1 z hz

lemma extendB_affine2 : ∀ z ∈ Set.Icc (3 / 4 : ℝ) (7 / 8),
    extend mapB z = 1 * z + (-(1 / 8)) := by
  intro z hz; rw [extend_mapB]; exact bFun_affine2 z hz

lemma extendB_affine3 : ∀ z ∈ Set.Icc (7 / 8 : ℝ) 1, extend mapB z = 2 * z + (-1) := by
  intro z hz; rw [extend_mapB]; exact bFun_affine3 z hz

lemma affineOnPieces_rotB (w l x y : TTree) :
    AffineOnPieces (extend mapB) (TTree.node w (TTree.node l (TTree.node x y))).marks := by
  have CB0 := isChain_affine_block w 0 (1 / 2) 1 0 (by norm_num) extendB_affine0
  have CB1 := isChain_affine_block l (1 / 2) (3 / 4) (1 / 2) (1 / 4) (by norm_num)
    extendB_affine1
  have CB2 := isChain_affine_block x (3 / 4) (7 / 8) 1 (-(1 / 8)) (by norm_num) extendB_affine2
  have CB3 := isChain_affine_block y (7 / 8) 1 2 (-1) (by norm_num) extendB_affine3
  have G1 := List.IsChain.append_overlap
    (R := fun u v => ∃ p' q' : ℝ, ∀ z ∈ Set.Icc u v, extend mapB z = p' * z + q')
    (l₁ := (0 : ℝ) :: w.marksAux 0 (1 / 2))
    (l₂ := [(1 / 2 : ℝ)])
    (l₃ := l.marksAux (1 / 2) (3 / 4) ++ [(3 / 4 : ℝ)])
    (by simpa using CB0) (by simpa using CB1) (by simp)
  have G2 := List.IsChain.append_overlap
    (R := fun u v => ∃ p' q' : ℝ, ∀ z ∈ Set.Icc u v, extend mapB z = p' * z + q')
    (l₁ := ((0 : ℝ) :: w.marksAux 0 (1 / 2)) ++ [(1 / 2 : ℝ)] ++ l.marksAux (1 / 2) (3 / 4))
    (l₂ := [(3 / 4 : ℝ)])
    (l₃ := x.marksAux (3 / 4) (7 / 8) ++ [(7 / 8 : ℝ)])
    (by simpa using G1) (by simpa using CB2) (by simp)
  have G3 := List.IsChain.append_overlap
    (R := fun u v => ∃ p' q' : ℝ, ∀ z ∈ Set.Icc u v, extend mapB z = p' * z + q')
    (l₁ := ((0 : ℝ) :: w.marksAux 0 (1 / 2)) ++ [(1 / 2 : ℝ)] ++ l.marksAux (1 / 2) (3 / 4)
      ++ [(3 / 4 : ℝ)] ++ x.marksAux (3 / 4) (7 / 8))
    (l₂ := [(7 / 8 : ℝ)])
    (l₃ := y.marksAux (7 / 8) 1 ++ [(1 : ℝ)])
    (by simpa using G2) (by simpa using CB3) (by simp)
  show List.IsChain (fun u v => ∃ p' q' : ℝ, ∀ z ∈ Set.Icc u v, extend mapB z = p' * z + q')
    ((0 : ℝ) :: ((TTree.node w (TTree.node l (TTree.node x y))).marksAux 0 1 ++ [1]))
  rw [marksAux_rotB_dom]
  simpa using G3

/-! ### The two rotations, as tree diagrams -/

lemma leafCount_rotA (l x y : TTree) :
    (TTree.node l (TTree.node x y)).leafCount = (TTree.node (TTree.node l x) y).leafCount := by
  simp only [TTree.leafCount]; omega

lemma leafCount_rotB (w l x y : TTree) :
    (TTree.node w (TTree.node l (TTree.node x y))).leafCount
      = (TTree.node w (TTree.node (TTree.node l x) y)).leafCount := by
  simp only [TTree.leafCount]; omega

lemma represents_rotA (l x y : TTree) :
    Represents ⟨TTree.node l (TTree.node x y), TTree.node (TTree.node l x) y,
      leafCount_rotA l x y⟩ mapA :=
  ⟨mapA_mem_F, affineOnPieces_rotA l x y, marks_rotA l x y⟩

lemma represents_rotB (w l x y : TTree) :
    Represents ⟨TTree.node w (TTree.node l (TTree.node x y)),
      TTree.node w (TTree.node (TTree.node l x) y), leafCount_rotB w l x y⟩ mapB :=
  ⟨mapB_mem_F, affineOnPieces_rotB w l x y, marks_rotB w l x y⟩

end CannonFloydParry

namespace CannonFloydParry

/-! ### The identity and inverses, as tree diagrams -/

lemma extend_one_apply (z : ℝ) : extend (1 : UI ≃o UI) z = z := by
  by_cases h : z ∈ Set.Icc (0 : ℝ) 1
  · rw [extend_apply, extendFun_of_mem _ h]; rfl
  · rw [extend_apply, extendFun_of_notMem _ h]

lemma coe_extend_one : (⇑(extend (1 : UI ≃o UI)) : ℝ → ℝ) = id := funext extend_one_apply

lemma inv_eq_symm (f : UI ≃o UI) : f⁻¹ = f.symm := rfl

lemma extend_inv_apply (f : UI ≃o UI) (z : ℝ) : extend f⁻¹ (extend f z) = z := by
  show extendFun (⇑(f⁻¹)) (extendFun (⇑f) z) = z
  rw [inv_eq_symm]
  exact extendFun_left_inv f z

lemma extend_apply_inv (f : UI ≃o UI) (z : ℝ) : extend f (extend f⁻¹ z) = z := by
  show extendFun (⇑f) (extendFun (⇑(f⁻¹)) z) = z
  rw [inv_eq_symm]
  have h := extendFun_left_inv f.symm z
  rw [OrderIso.symm_symm] at h
  exact h

lemma represents_inv {R S : TTree} (h : R.leafCount = S.leafCount) {f : UI ≃o UI}
    (hf : Represents ⟨R, S, h⟩ f) : Represents ⟨S, R, h.symm⟩ f⁻¹ := by
  obtain ⟨hF, hA, hM⟩ := hf
  have hA' : AffineOnPieces (extend f) R.marks := hA
  have hM' : R.marks.map (extend f) = S.marks := hM
  have hlen : R.marks.length = S.marks.length := by
    rw [marks_length_eq, marks_length_eq, h]
  have hmapj : ∀ i, i < R.marks.length →
      extend f (R.marks.getD i 0) = S.marks.getD i 0 := by
    intro i hi
    have e : (R.marks.map (extend f)).getD i 0 = S.marks.getD i 0 := by rw [hM']
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      ← List.getD_eq_getElem _ _ hi] at e
    exact e
  have hinvj : ∀ i, i < R.marks.length →
      extend f⁻¹ (S.marks.getD i 0) = R.marks.getD i 0 := by
    intro i hi
    rw [← hmapj i hi, extend_inv_apply]
  refine ⟨inv_mem hF, ?_, ?_⟩
  · -- the inverse of an affine map is affine
    show AffineOnPieces (extend f⁻¹) S.marks
    refine getD_chain _ ?_
    intro j hj
    have hjR : j + 1 < R.marks.length := by rw [hlen]; exact hj
    obtain ⟨p, q, hpq⟩ := chain_getD _ hA' j hjR
    have hltR := marks_getD_lt R hjR
    have hltS := marks_getD_lt S hj
    have E1 : p * R.marks.getD j 0 + q = S.marks.getD j 0 := by
      rw [← hpq _ ⟨le_refl _, le_of_lt hltR⟩]; exact hmapj j (by omega)
    have E2 : p * R.marks.getD (j + 1) 0 + q = S.marks.getD (j + 1) 0 := by
      rw [← hpq _ ⟨le_of_lt hltR, le_refl _⟩]; exact hmapj (j + 1) (by omega)
    have hp : 0 < p := by
      rcases lt_trichotomy 0 p with h | h | h
      · exact h
      · exfalso; nlinarith [hltR, hltS, E1, E2]
      · exfalso; nlinarith [hltR, hltS, E1, E2]
    refine ⟨1 / p, -(q / p), ?_⟩
    intro w hw
    -- `extend f⁻¹ w` lies in the corresponding piece of the domain partition
    have hz1 : R.marks.getD j 0 ≤ extend f⁻¹ w := by
      have hmono := (extend f⁻¹).monotone hw.1
      rwa [hinvj j (by omega)] at hmono
    have hz2 : extend f⁻¹ w ≤ R.marks.getD (j + 1) 0 := by
      have hmono := (extend f⁻¹).monotone hw.2
      rwa [hinvj (j + 1) (by omega)] at hmono
    have hval : p * (extend f⁻¹ w) + q = w := by
      rw [← hpq _ ⟨hz1, hz2⟩, extend_apply_inv]
    field_simp
    linarith
  · -- the marks come back
    show S.marks.map (extend f⁻¹) = R.marks
    rw [← hM', List.map_map]
    have : (fun z => extend f⁻¹ (extend f z)) = (id : ℝ → ℝ) :=
      funext fun z => extend_inv_apply f z
    rw [show (⇑(extend f⁻¹) ∘ ⇑(extend f) : ℝ → ℝ) = id from this, List.map_id]

/-! ### Spines: a sequence of left subtrees hanging off the right side -/

def spine : List TTree → TTree → TTree
  | [], T => T
  | w :: ws, T => TTree.node w (spine ws T)

lemma leafCount_spine_rot (ws : List TTree) (l x y : TTree) :
    (spine ws (TTree.node l (TTree.node x y))).leafCount
      = (spine ws (TTree.node (TTree.node l x) y)).leafCount := by
  induction ws with
  | nil => exact leafCount_rotA l x y
  | cons w ws ih => rw [spine, spine, TTree.leafCount, TTree.leafCount, ih]

/-! ### Words -/

lemma wordFrom_incrHead (i : ℕ) (a : ℕ) (as : List ℕ) :
    wordFrom i (TTree.incrHead (a :: as)) = X i * wordFrom i (a :: as) := by
  rw [TTree.incrHead, wordFrom, wordFrom, pow_succ']
  group

lemma wordFrom_append : ∀ (as bs : List ℕ) (i : ℕ),
    wordFrom i (as ++ bs) = wordFrom i as * wordFrom (i + as.length) bs := by
  intro as
  induction as with
  | nil => intro bs i; rw [List.nil_append, wordFrom]; simp
  | cons a as ih =>
      intro bs i
      have hidx : i + 1 + as.length = i + (a :: as).length := by
        simp only [List.length_cons]; omega
      rw [List.cons_append, wordFrom, wordFrom, ih bs (i + 1), mul_assoc, hidx]

lemma wordFrom_replicate_zero : ∀ (m i : ℕ) (cs : List ℕ),
    wordFrom i (List.replicate m 0 ++ cs) = wordFrom (i + m) cs := by
  intro m
  induction m with
  | zero => intro i cs; simp
  | succ m ih =>
      intro i cs
      rw [List.replicate_succ, List.cons_append, wordFrom, pow_zero, one_mul, ih (i + 1) cs]
      congr 1
      omega

end CannonFloydParry

namespace CannonFloydParry

/-! ### Composition of tree diagrams (the source's rule on p. 222) -/

lemma getD_map {l : List ℝ} {g : ℝ → ℝ} {i : ℕ} (hi : i < l.length) :
    (l.map g).getD i 0 = g (l.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi,
    List.getElem_map]


/-! ### `Xₘ` is the rotation `m` steps down the right side

`X₀ = A` rotates at the root and `X₁ = B` one step down; the recursion
`X_{m+2} = A⁻¹ X_{m+1} A` then pushes the rotation one step further each time, because `A` itself
turns a spine `w₀, w₁, …` into the spine `⟨w₀,w₁⟩, …`, one shorter. -/

lemma X_succ_succ (n : ℕ) : X (n + 2) = mapA⁻¹ * X (n + 1) * mapA := by
  show (mapA ^ (n + 1))⁻¹ * mapB * mapA ^ (n + 1)
      = mapA⁻¹ * ((mapA ^ n)⁻¹ * mapB * mapA ^ n) * mapA
  rw [pow_succ]
  group

lemma represents_X : ∀ (m : ℕ) (ws : List TTree), ws.length = m → ∀ (l x y : TTree),
    Represents ⟨spine ws (TTree.node l (TTree.node x y)),
      spine ws (TTree.node (TTree.node l x) y), leafCount_spine_rot ws l x y⟩ (X m) := by
  intro m
  induction m with
  | zero =>
      intro ws hws l x y
      obtain rfl : ws = [] := List.length_eq_zero_iff.mp hws
      exact represents_rotA l x y
  | succ m ih =>
      intro ws hws l x y
      obtain ⟨w, ws', rfl⟩ : ∃ w ws', ws = w :: ws' := by
        cases ws with
        | nil => exact absurd hws (by simp)
        | cons w ws' => exact ⟨w, ws', rfl⟩
      have hws' : ws'.length = m := by simpa using hws
      cases m with
      | zero =>
          obtain rfl : ws' = [] := List.length_eq_zero_iff.mp hws'
          rw [X_one]
          exact represents_rotB w l x y
      | succ n =>
          obtain ⟨w1, ws'', rfl⟩ : ∃ w1 ws'', ws' = w1 :: ws'' := by
            cases ws' with
            | nil => exact absurd hws' (by simp)
            | cons w1 ws'' => exact ⟨w1, ws'', rfl⟩
          have hws'' : ws''.length = n := by simpa using hws'
          -- the three stages: `A`, then `X (n+1)` on a spine one shorter, then `A⁻¹`
          have hA1 := represents_rotA w w1 (spine ws'' (TTree.node l (TTree.node x y)))
          have hA2 := represents_rotA w w1 (spine ws'' (TTree.node (TTree.node l x) y))
          have hX := ih (TTree.node w w1 :: ws'') (by simpa using hws'') l x y
          have hA2' := represents_inv _ hA2
          have step1 := represents_mul _ _ hA1 hX
          have step2 := represents_mul _ _ step1 hA2'
          rw [X_succ_succ, mul_assoc]
          exact step2

end CannonFloydParry

namespace CannonFloydParry

/-! ### Exponents of a spine, and of a rotation -/

lemma leftRuns_ne_nil' (t : TTree) : t.leftRuns ≠ [] := by
  induction t with
  | leaf => simp [TTree.leftRuns]
  | node l r ihl ihr =>
      rw [TTree.leftRuns]
      cases hl : l.leftRuns with
      | nil => exact absurd hl ihl
      | cons a as => simp [TTree.incrHead]

lemma exponents_ne_nil (t : TTree) : t.exponents ≠ [] := by
  induction t with
  | leaf => simp [TTree.exponents]
  | node l r _ ihr =>
      rw [TTree.exponents]
      simpa using fun _ => ihr

lemma incrHead_append {as bs : List ℕ} (h : as ≠ []) :
    TTree.incrHead (as ++ bs) = TTree.incrHead as ++ bs := by
  cases as with
  | nil => exact absurd rfl h
  | cons a as => rfl

lemma sum_incrHead {as : List ℕ} (h : as ≠ []) :
    (TTree.incrHead as).sum = as.sum + 1 := by
  cases as with
  | nil => exact absurd rfl h
  | cons a as => simp [TTree.incrHead]; omega

/-- Rotating at the root increments the first exponent and leaves the rest alone. -/
lemma exponents_rot (l x y : TTree) :
    (TTree.node (TTree.node l x) y).exponents
      = TTree.incrHead (TTree.node l (TTree.node x y)).exponents := by
  have e1 : (TTree.node (TTree.node l x) y).exponents
      = (TTree.incrHead l.leftRuns ++ x.leftRuns) ++ y.exponents := by
    rw [TTree.exponents, TTree.leftRuns]
  have e2 : (TTree.node l (TTree.node x y)).exponents
      = l.leftRuns ++ (x.leftRuns ++ y.exponents) := by
    rw [TTree.exponents, TTree.exponents]
  rw [e1, e2, incrHead_append (leftRuns_ne_nil' l), List.append_assoc]

lemma exponents_spine_replicate : ∀ (m : ℕ) (T : TTree),
    (spine (List.replicate m TTree.leaf) T).exponents = List.replicate m 0 ++ T.exponents := by
  intro m
  induction m with
  | zero => intro T; simp [spine]
  | succ m ih =>
      intro T
      rw [List.replicate_succ, spine, TTree.exponents, ih T, List.replicate_succ]
      simp [TTree.leftRuns]

/-! ### Trees with all exponents zero are the right combs -/

lemma getD_memN {xs : List ℕ} {j : ℕ} (h : j < xs.length) : xs.getD j 0 ∈ xs := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

lemma leftRuns_getD_zero_node' (l r : TTree) : 0 < (TTree.node l r).leftRuns.getD 0 0 := by
  rw [TTree.leftRuns]
  cases hl : l.leftRuns with
  | nil => exact absurd hl (leftRuns_ne_nil' l)
  | cons a as =>
      rw [TTree.incrHead]
      simp

lemma comb_succ (n : ℕ) : TTree.comb (n + 1) = TTree.node TTree.leaf (TTree.comb n) := rfl

lemma leafCount_comb : ∀ n : ℕ, (TTree.comb n).leafCount = n + 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [comb_succ, TTree.leafCount, ih]
      simp only [TTree.leafCount]
      omega

lemma eq_comb_of_sum_eq_zero : ∀ (R : TTree), R.exponents.sum = 0 →
    R = TTree.comb (R.leafCount - 1) := by
  intro R
  induction R with
  | leaf => intro _; rfl
  | node l r ihl ihr =>
      intro hsum
      rw [TTree.exponents, List.sum_append] at hsum
      have h1 : l.leftRuns.sum = 0 := by omega
      have h2 : r.exponents.sum = 0 := by omega
      have hl : l = TTree.leaf := by
        cases l with
        | leaf => rfl
        | node a b =>
            exfalso
            have hpos := leftRuns_getD_zero_node' a b
            have hmem : (TTree.node a b).leftRuns.getD 0 0 ∈ (TTree.node a b).leftRuns := by
              refine getD_memN ?_
              have := leftRuns_ne_nil' (TTree.node a b)
              exact List.length_pos_iff.mpr this
            have hle : (TTree.node a b).leftRuns.getD 0 0 ≤ (TTree.node a b).leftRuns.sum :=
              List.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem
            omega
      subst hl
      obtain ⟨k, hk⟩ : ∃ k, r.leafCount = k + 1 := ⟨r.leafCount - 1, by
        have := one_le_leafCount' r; omega⟩
      have hr : r = TTree.comb k := by
        have hrec := ihr h2
        rwa [hk, Nat.add_sub_cancel] at hrec
      have hlc : (TTree.node TTree.leaf r).leafCount - 1 = k + 1 := by
        rw [TTree.leafCount, TTree.leafCount, hk]
        omega
      rw [hlc, comb_succ, ← hr]

/-! ### A tree with a positive exponent is a spine over a rotatable node -/

lemma exists_spine_rot : ∀ (R : TTree), 0 < R.exponents.sum →
    ∃ (m : ℕ) (l x y : TTree),
      R = spine (List.replicate m TTree.leaf) (TTree.node (TTree.node l x) y) := by
  intro R
  induction R with
  | leaf => intro h; exfalso; simp [TTree.exponents] at h
  | node l r ihl ihr =>
      intro h
      cases l with
      | leaf =>
          have hr : 0 < r.exponents.sum := by
            rw [TTree.exponents, TTree.leftRuns, List.sum_append] at h
            simpa using h
          obtain ⟨m, a, b, c, hrm⟩ := ihr hr
          exact ⟨m + 1, a, b, c, by rw [List.replicate_succ, spine, hrm]⟩
      | node a b => exact ⟨0, a, b, r, by simp [spine]⟩

/-! ### Words with total exponent zero are trivial -/

lemma wordFrom_of_sum_eq_zero : ∀ (cs : List ℕ), cs.sum = 0 → ∀ i, wordFrom i cs = 1 := by
  intro cs
  induction cs with
  | nil => intro _ i; rfl
  | cons c cs ih =>
      intro hsum i
      rw [List.sum_cons] at hsum
      have hc : c = 0 := by omega
      have hcs : cs.sum = 0 := by omega
      rw [wordFrom, hc, pow_zero, one_mul, ih hcs (i + 1)]

/-! ### The identity, on a diagram whose two trees happen to coincide -/

lemma represents_id_of_eq {R C : TTree} (h : R.leafCount = C.leafCount) (hRC : R = C) :
    Represents ⟨R, C, h⟩ (1 : UI ≃o UI) := by
  refine ⟨one_mem F, ?_, ?_⟩
  · show AffineOnPieces (extend (1 : UI ≃o UI)) R.marks
    refine isChain_of_pairs _ ?_
    intro u _ v _
    exact ⟨1, 0, fun z _ => by rw [extend_one_apply]; ring⟩
  · show R.marks.map (extend (1 : UI ≃o UI)) = C.marks
    rw [coe_extend_one, List.map_id, hRC]

/-! ### The induction of the source's proof: peel one rotation at a time -/

lemma represents_word_inv : ∀ (N : ℕ) (R : TTree) (n : ℕ)
    (hn : R.leafCount = (TTree.comb n).leafCount), R.exponents.sum ≤ N →
    Represents ⟨R, TTree.comb n, hn⟩ (word R.exponents)⁻¹ := by
  intro N
  induction N with
  | zero =>
      intro R n hn hle
      have hsum : R.exponents.sum = 0 := by omega
      have hw : word R.exponents = 1 := wordFrom_of_sum_eq_zero _ hsum 0
      have hcomb : R = TTree.comb n := by
        have h := eq_comb_of_sum_eq_zero R hsum
        rw [leafCount_comb] at hn
        rw [h]
        congr 1
        omega
      rw [hw, inv_one]
      exact represents_id_of_eq hn hcomb
  | succ N ih =>
      intro R n hn hle
      rcases Nat.eq_zero_or_pos R.exponents.sum with hz | hp
      · have hw : word R.exponents = 1 := wordFrom_of_sum_eq_zero _ hz 0
        have hcomb : R = TTree.comb n := by
          have h := eq_comb_of_sum_eq_zero R hz
          rw [leafCount_comb] at hn
          rw [h]
          congr 1
          omega
        rw [hw, inv_one]
        exact represents_id_of_eq hn hcomb
      · obtain ⟨m, l, x, y, rfl⟩ := exists_spine_rot R hp
        -- the tree one rotation back
        set N₁ : TTree := TTree.node l (TTree.node x y) with hN₁
        set N₂ : TTree := TTree.node (TTree.node l x) y with hN₂
        set R₀ : TTree := spine (List.replicate m TTree.leaf) N₁ with hR₀
        have hlc : R₀.leafCount = (spine (List.replicate m TTree.leaf) N₂).leafCount :=
          leafCount_spine_rot _ l x y
        -- exponents of the two spines
        obtain ⟨a, as, hNa⟩ := List.exists_cons_of_ne_nil (exponents_ne_nil N₁)
        have hE₂ : N₂.exponents = TTree.incrHead N₁.exponents := exponents_rot l x y
        have hER : (spine (List.replicate m TTree.leaf) N₂).exponents
            = List.replicate m 0 ++ TTree.incrHead N₁.exponents := by
          rw [exponents_spine_replicate, hE₂]
        have hER₀ : R₀.exponents = List.replicate m 0 ++ N₁.exponents :=
          exponents_spine_replicate m N₁
        -- the sum drops by one
        have hsum : (spine (List.replicate m TTree.leaf) N₂).exponents.sum
            = R₀.exponents.sum + 1 := by
          rw [hER, hER₀, List.sum_append, List.sum_append,
            sum_incrHead (exponents_ne_nil N₁)]
          omega
        -- the word gains a factor `X m` on the left
        have hword : word (spine (List.replicate m TTree.leaf) N₂).exponents
            = X m * word R₀.exponents := by
          rw [hER, hER₀]
          show wordFrom 0 (List.replicate m 0 ++ TTree.incrHead N₁.exponents)
              = X m * wordFrom 0 (List.replicate m 0 ++ N₁.exponents)
          rw [wordFrom_replicate_zero, wordFrom_replicate_zero, Nat.zero_add, hNa,
            wordFrom_incrHead]
        -- the rotation itself, and its inverse
        have hX : Represents ⟨R₀, spine (List.replicate m TTree.leaf) N₂, hlc⟩ (X m) :=
          represents_X m (List.replicate m TTree.leaf) (by simp) l x y
        have hXinv := represents_inv _ hX
        -- the inductive hypothesis, applied one rotation back
        have hn₀ : R₀.leafCount = (TTree.comb n).leafCount := by rw [hlc]; exact hn
        have hle₀ : R₀.exponents.sum ≤ N := by omega
        have hIH := ih R₀ n hn₀ hle₀
        have hcomp := represents_mul _ _ hXinv hIH
        rw [hword, mul_inv_rev]
        exact hcomp


end CannonFloydParry

namespace CannonFloydParry

/-! ### Lengths -/

lemma one_le_leafCount (t : TTree) : 1 ≤ t.leafCount := by
  induction t with
  | leaf => simp [TTree.leafCount]
  | node l r ihl ihr => rw [TTree.leafCount]; omega

lemma incrHead_length (l : List ℕ) : (TTree.incrHead l).length = l.length := by
  cases l with
  | nil => rfl
  | cons a as => rfl

lemma leftRuns_length (t : TTree) : t.leftRuns.length = t.leafCount := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
      rw [TTree.leftRuns, TTree.leafCount, List.length_append, incrHead_length, ihl, ihr]

lemma exponents_length (t : TTree) : t.exponents.length = t.leafCount := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
      rw [TTree.exponents, TTree.leafCount, List.length_append, leftRuns_length, ihr]

/-! ### Unfolding `caretAt` and `endsInCaret`

Both are defined by overlapping pattern matches, so they are unfolded here through `rfl`
equations rather than by rewriting with the definitions. -/

lemma caretAt_leaf (k : ℕ) : TTree.leaf.caretAt k = false := rfl

lemma caretAt_node (l r : TTree) (k : ℕ) :
    (TTree.node l r).caretAt k =
      if k + 1 < l.leafCount then l.caretAt k
      else if l.leafCount ≤ k then r.caretAt (k - l.leafCount)
      else (match l, r with
            | TTree.leaf, TTree.leaf => true
            | _, _ => false) := rfl

lemma caretAt_node_left {l r : TTree} {k : ℕ} (h : k + 1 < l.leafCount) :
    (TTree.node l r).caretAt k = l.caretAt k := by
  rw [caretAt_node, if_pos h]

lemma caretAt_node_right {l r : TTree} {k : ℕ} (h1 : ¬ (k + 1 < l.leafCount))
    (h2 : l.leafCount ≤ k) :
    (TTree.node l r).caretAt k = r.caretAt (k - l.leafCount) := by
  rw [caretAt_node, if_neg h1, if_pos h2]

lemma caretAt_node_straddle_false {l r : TTree} {k : ℕ} (h1 : ¬ (k + 1 < l.leafCount))
    (h2 : ¬ (l.leafCount ≤ k)) (h3 : l ≠ TTree.leaf ∨ r ≠ TTree.leaf) :
    (TTree.node l r).caretAt k = false := by
  rw [caretAt_node, if_neg h1, if_neg h2]
  cases l with
  | leaf =>
      cases r with
      | leaf => rcases h3 with h3 | h3 <;> exact absurd rfl h3
      | node c e => rfl
  | node a b =>
      cases r with
      | leaf => rfl
      | node c e => rfl

lemma caretAt_leaf_leaf_zero : (TTree.node TTree.leaf TTree.leaf).caretAt 0 = true := rfl

lemma endsInCaret_leaf : TTree.leaf.endsInCaret = false := rfl

lemma endsInCaret_leaf_leaf : (TTree.node TTree.leaf TTree.leaf).endsInCaret = true := rfl

lemma endsInCaret_right_leaf {l : TTree} (h : l ≠ TTree.leaf) :
    (TTree.node l TTree.leaf).endsInCaret = false := by
  cases l with
  | leaf => exact absurd rfl h
  | node a b => rfl

lemma endsInCaret_node_node (l a b : TTree) :
    (TTree.node l (TTree.node a b)).endsInCaret = (TTree.node a b).endsInCaret := by
  cases l with
  | leaf => rfl
  | node c e => rfl

/-! ### `incrHead` touches only the head -/

lemma incrHead_getD_zero {l : List ℕ} (h : l ≠ []) :
    (TTree.incrHead l).getD 0 0 = l.getD 0 0 + 1 := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as => rfl

lemma incrHead_getD_succ (l : List ℕ) (k : ℕ) :
    (TTree.incrHead l).getD (k + 1) 0 = l.getD (k + 1) 0 := by
  cases l with
  | nil => rfl
  | cons a as => rfl

/-! ### The first and last left-runs

The leftmost leaf of a node is a left child, so its run is positive; the rightmost leaf of any
tree is a right child (or the whole tree), so its run is zero. -/

lemma leftRuns_ne_nil (t : TTree) : t.leftRuns ≠ [] := by
  intro h
  have hlen := leftRuns_length t
  have := one_le_leafCount t
  rw [h] at hlen
  simp at hlen
  omega

lemma leftRuns_getD_zero_node (l r : TTree) : 0 < (TTree.node l r).leftRuns.getD 0 0 := by
  have hne : l.leftRuns ≠ [] := leftRuns_ne_nil l
  rw [TTree.leftRuns,
    List.getD_append _ _ _ _ (by rw [incrHead_length]; exact List.length_pos_iff.mpr hne),
    incrHead_getD_zero hne]
  omega

lemma leftRuns_getD_last (t : TTree) : t.leftRuns.getD (t.leafCount - 1) 0 = 0 := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
      have hm := one_le_leafCount l
      have hp := one_le_leafCount r
      have hlenL : (TTree.incrHead l.leftRuns).length = l.leafCount := by
        rw [incrHead_length, leftRuns_length]
      have hidx : (TTree.node l r).leafCount - 1 = l.leafCount + (r.leafCount - 1) := by
        rw [TTree.leafCount]; omega
      rw [TTree.leftRuns, hidx,
        List.getD_append_right _ _ _ _ (by rw [hlenL]; omega), hlenL]
      simpa using ihr

/-! ### Carets and left-runs

The `k`th and `(k+1)`th leaves are siblings exactly when the left-run from the `k`th is positive
and the run from the `(k+1)`th is zero: the first says the `k`th leaf is a left child, the second
that the `(k+1)`th is a right child, and adjacency then forces them to share a parent. -/

lemma caretAt_iff_leftRuns : ∀ (t : TTree) (k : ℕ),
    (t.caretAt k = true ↔ (0 < t.leftRuns.getD k 0 ∧ t.leftRuns.getD (k + 1) 0 = 0)) := by
  intro t
  induction t with
  | leaf =>
      intro k
      have h1 : (TTree.leaf.leftRuns).getD k 0 = 0 := by
        show ([0] : List ℕ).getD k 0 = 0
        cases k with
        | zero => rfl
        | succ k => rfl
      rw [caretAt_leaf, h1]
      constructor
      · intro h; exact Bool.noConfusion h
      · intro h; exact absurd h.1 (lt_irrefl 0)
  | node l r ihl ihr =>
      intro k
      have hm := one_le_leafCount l
      have hp := one_le_leafCount r
      have hlenL : (TTree.incrHead l.leftRuns).length = l.leafCount := by
        rw [incrHead_length, leftRuns_length]
      rw [TTree.leftRuns]
      rcases Nat.lt_or_ge (k + 1) l.leafCount with hk1 | hk1
      · -- the pair lies inside the left subtree
        rw [caretAt_node_left hk1,
          List.getD_append _ _ _ _ (by rw [hlenL]; omega),
          List.getD_append _ _ _ _ (by rw [hlenL]; omega)]
        cases k with
        | zero =>
            -- the head is the one entry `incrHead` changes, but it was positive anyway
            obtain ⟨a, b, rfl⟩ : ∃ a b, l = TTree.node a b := by
              cases l with
              | leaf => exfalso; rw [TTree.leafCount] at hk1; omega
              | node a b => exact ⟨a, b, rfl⟩
            have hpos : 0 < (TTree.node a b).leftRuns.getD 0 0 := leftRuns_getD_zero_node a b
            rw [incrHead_getD_zero (leftRuns_ne_nil (TTree.node a b)), incrHead_getD_succ,
              ihl 0]
            constructor
            · exact fun h => ⟨by omega, h.2⟩
            · exact fun h => ⟨hpos, h.2⟩
        | succ j =>
            rw [incrHead_getD_succ, incrHead_getD_succ]
            exact ihl (j + 1)
      · rcases Nat.lt_or_ge k l.leafCount with hk2 | hk2
        · -- the pair straddles the two subtrees: `k + 1 = l.leafCount`
          rw [List.getD_append _ _ _ _ (by rw [hlenL]; omega),
            List.getD_append_right _ _ _ _ (by rw [hlenL]; omega), hlenL]
          cases l with
          | leaf =>
              -- `l` is a single leaf, so its (incremented) entry is `1`
              have hk0 : k = 0 := by
                rw [TTree.leafCount] at hk2; omega
              subst hk0
              have hone : (TTree.incrHead (TTree.leaf.leftRuns)).getD 0 0 = 1 := rfl
              rw [hone, show (0 : ℕ) + 1 - TTree.leaf.leafCount = 0 from rfl]
              cases r with
              | leaf =>
                  rw [caretAt_leaf_leaf_zero]
                  have : (TTree.leaf.leftRuns).getD 0 0 = 0 := rfl
                  rw [this]
                  simp
              | node c e =>
                  have hpos : 0 < (TTree.node c e).leftRuns.getD 0 0 :=
                    leftRuns_getD_zero_node c e
                  rw [caretAt_node_straddle_false (by rw [TTree.leafCount]; omega)
                    (by rw [TTree.leafCount]; omega) (Or.inr (by intro h; exact TTree.noConfusion h))]
                  constructor
                  · intro h; exact Bool.noConfusion h
                  · intro h; exact absurd h.2 (by omega)
          | node a b =>
              -- the left entry is the last left-run of `l`, which is `0`
              have hna := one_le_leafCount a
              have hnb := one_le_leafCount b
              have hk1' : 1 ≤ k := by rw [TTree.leafCount] at hk1 hk2; omega
              obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
              rw [incrHead_getD_succ]
              have hzero : (TTree.node a b).leftRuns.getD (j + 1) 0 = 0 := by
                have h := leftRuns_getD_last (TTree.node a b)
                rw [show (TTree.node a b).leafCount - 1 = j + 1 by
                  rw [TTree.leafCount] at hk1 hk2 ⊢; omega] at h
                exact h
              rw [hzero, caretAt_node_straddle_false (by omega) (by omega)
                (Or.inl (by intro h; exact TTree.noConfusion h))]
              constructor
              · intro h; exact Bool.noConfusion h
              · intro h; exact absurd h.1 (lt_irrefl 0)
        · -- the pair lies inside the right subtree
          rw [caretAt_node_right (by omega) hk2,
            List.getD_append_right _ _ _ _ (by rw [hlenL]; omega),
            List.getD_append_right _ _ _ _ (by rw [hlenL]; omega), hlenL,
            show k + 1 - l.leafCount = (k - l.leafCount) + 1 by omega]
          exact ihr (k - l.leafCount)

/-- Past the last adjacent pair there is no caret. -/
lemma caretAt_of_le : ∀ (t : TTree) (k : ℕ), t.leafCount ≤ k + 1 → t.caretAt k = false := by
  intro t
  induction t with
  | leaf => intro k _; rfl
  | node l r ihl ihr =>
      intro k hk
      have hm := one_le_leafCount l
      have hp := one_le_leafCount r
      rw [TTree.leafCount] at hk
      rw [caretAt_node_right (by omega) (by omega)]
      exact ihr (k - l.leafCount) (by omega)

/-! ### The exponent at the last pair, and carets read off the exponents -/

lemma caretAt_iff_exponents : ∀ (t : TTree) (k : ℕ), k + 2 < t.leafCount →
    (t.caretAt k = true ↔ (0 < t.exponents.getD k 0 ∧ t.exponents.getD (k + 1) 0 = 0)) := by
  intro t
  induction t with
  | leaf => intro k hk; rw [TTree.leafCount] at hk; omega
  | node l r ihl ihr =>
      intro k hk
      have hm := one_le_leafCount l
      have hp := one_le_leafCount r
      rw [TTree.leafCount] at hk
      have hlenL : (l.leftRuns).length = l.leafCount := leftRuns_length l
      rw [TTree.exponents]
      rcases Nat.lt_or_ge (k + 1) l.leafCount with hk1 | hk1
      · -- inside the left subtree, where the exponents restrict to the *left-runs* of `l`
        rw [caretAt_node_left hk1,
          List.getD_append _ _ _ _ (by rw [hlenL]; omega),
          List.getD_append _ _ _ _ (by rw [hlenL]; omega)]
        exact caretAt_iff_leftRuns l k
      · rcases Nat.lt_or_ge k l.leafCount with hk2 | hk2
        · -- straddling: the left entry is the last left-run of `l`, which is `0`
          rw [List.getD_append _ _ _ _ (by rw [hlenL]; omega)]
          have hzero : l.leftRuns.getD k 0 = 0 := by
            rw [show k = l.leafCount - 1 by omega]; exact leftRuns_getD_last l
          have hrne : r ≠ TTree.leaf := by
            intro h
            rw [h, TTree.leafCount] at hk
            omega
          rw [hzero, caretAt_node_straddle_false (by omega) (by omega) (Or.inr hrne)]
          constructor
          · intro h; exact Bool.noConfusion h
          · intro h; exact absurd h.1 (lt_irrefl 0)
        · -- inside the right subtree
          rw [caretAt_node_right (by omega) hk2,
            List.getD_append_right _ _ _ _ (by rw [hlenL]; omega),
            List.getD_append_right _ _ _ _ (by rw [hlenL]; omega), hlenL,
            show k + 1 - l.leafCount = (k - l.leafCount) + 1 by omega]
          exact ihr (k - l.leafCount) (by omega)

/-! ### `endsInCaret` is the caret at the last pair -/

lemma endsInCaret_eq_caretAt : ∀ (t : TTree), 2 ≤ t.leafCount →
    t.endsInCaret = t.caretAt (t.leafCount - 2) := by
  intro t
  induction t with
  | leaf => intro h; rw [TTree.leafCount] at h; omega
  | node l r ihl ihr =>
      intro _
      have hm := one_le_leafCount l
      have hp := one_le_leafCount r
      rcases Nat.lt_or_ge r.leafCount 2 with hp2 | hp2
      · -- `r` is a single leaf, so the last pair straddles
        obtain rfl : r = TTree.leaf := by
          cases r with
          | leaf => rfl
          | node a b =>
              exfalso
              have := one_le_leafCount a
              have := one_le_leafCount b
              rw [TTree.leafCount] at hp2
              omega
        rw [show (TTree.node l TTree.leaf).leafCount - 2 = l.leafCount - 1 by
          rw [TTree.leafCount]; omega]
        cases l with
        | leaf => rw [endsInCaret_leaf_leaf]; exact caretAt_leaf_leaf_zero.symm
        | node a b =>
            have hne : TTree.node a b ≠ TTree.leaf := by
              intro h; exact TTree.noConfusion h
            rw [endsInCaret_right_leaf hne,
              caretAt_node_straddle_false (by omega) (by omega) (Or.inl hne)]
      · -- `r` has at least two leaves, so the last pair lies inside it
        obtain ⟨a, b, rfl⟩ : ∃ a b, r = TTree.node a b := by
          cases r with
          | leaf => exfalso; rw [TTree.leafCount] at hp2; omega
          | node a b => exact ⟨a, b, rfl⟩
        rw [endsInCaret_node_node,
          show (TTree.node l (TTree.node a b)).leafCount - 2
              = l.leafCount + ((TTree.node a b).leafCount - 2) by rw [TTree.leafCount]; omega,
          caretAt_node_right (by omega) (by omega),
          show l.leafCount + ((TTree.node a b).leafCount - 2) - l.leafCount
              = (TTree.node a b).leafCount - 2 by omega]
        exact ihr hp2

end CannonFloydParry

namespace CannonFloydParry

/-! ### `getD` bookkeeping for `ℕ`-lists -/

lemma getD_ge_length {l : List ℕ} {j : ℕ} (h : l.length ≤ j) : l.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-! ### The last two exponents of a tree are zero -/

lemma getD_getLastN : ∀ (xs : List ℕ) (v : ℕ), xs.getLast? = some v →
    xs.getD (xs.length - 1) 0 = v := by
  intro xs
  induction xs with
  | nil => intro v h; simp at h
  | cons x rest ih =>
      intro v h
      cases rest with
      | nil =>
          have hxv : x = v := by simpa using h
          simp [hxv]
      | cons y t =>
          have h' : (y :: t).getLast? = some v := by
            rw [List.getLast?_cons_cons] at h; exact h
          have hrec := ih v h'
          show (x :: y :: t).getD (t.length + 1) 0 = v
          rw [List.getD_cons_succ]
          simpa using hrec


lemma exponents_getD_last (t : TTree) : t.exponents.getD (t.leafCount - 1) 0 = 0 := by
  have h := getD_getLastN _ 0 (getLast_exponents_eq_zero t)
  rwa [exponents_length] at h


end CannonFloydParry

namespace CannonFloydParry

/-! ### The mark list determines the tree (from `existsUnique_tree_marks_eq`) -/

/-! ### Realising a list of naturals as an exponent list

Rotating at the root increments the first exponent (`exponents_rot`), and it is available as long
as the right side has length at least two.  Starting from a comb, which has all exponents zero
and a long right side, a list is built right to left: prepend a leaf (which prepends a zero
exponent) and rotate the required number of times. -/

/-- The rotation at the root, extended by the identity where it does not apply. -/
def rot : TTree → TTree
  | TTree.node l (TTree.node x y) => TTree.node (TTree.node l x) y
  | t => t

lemma rot_node (l x y : TTree) :
    rot (TTree.node l (TTree.node x y)) = TTree.node (TTree.node l x) y := rfl

lemma exists_of_two_le_rightSideLen {t : TTree} (h : 2 ≤ t.rightSideLen) :
    ∃ l x y, t = TTree.node l (TTree.node x y) := by
  cases t with
  | leaf => simp [TTree.rightSideLen] at h
  | node l r =>
      cases r with
      | leaf => simp [TTree.rightSideLen] at h
      | node x y => exact ⟨l, x, y, rfl⟩

lemma incrHead_iterate : ∀ (c a : ℕ) (as : List ℕ),
    (TTree.incrHead)^[c] (a :: as) = (a + c) :: as := by
  intro c
  induction c with
  | zero => intro a as; rfl
  | succ c ih =>
      intro a as
      rw [Function.iterate_succ_apply, show TTree.incrHead (a :: as) = (a + 1) :: as from rfl,
        ih, Nat.add_assoc, Nat.add_comm 1 c]

/-- `c` rotations at the root, given a right side of length at least `c + 1`. -/
lemma rot_iterate_spec : ∀ (c : ℕ) (t : TTree), c + 1 ≤ t.rightSideLen →
    (rot^[c] t).rightSideLen + c = t.rightSideLen ∧
    (rot^[c] t).exponents = (TTree.incrHead)^[c] t.exponents ∧
    (rot^[c] t).leafCount = t.leafCount := by
  intro c
  induction c with
  | zero => intro t _; exact ⟨rfl, rfl, rfl⟩
  | succ c ih =>
      intro t ht
      obtain ⟨l, x, y, rfl⟩ := exists_of_two_le_rightSideLen (t := t) (by omega)
      have hrsl : (TTree.node (TTree.node l x) y).rightSideLen + 1
          = (TTree.node l (TTree.node x y)).rightSideLen := by
        simp only [TTree.rightSideLen]
      have hrsl' : c + 1 ≤ (TTree.node (TTree.node l x) y).rightSideLen := by omega
      obtain ⟨h1, h2, h3⟩ := ih _ hrsl'
      rw [Function.iterate_succ_apply, rot_node]
      refine ⟨by omega, ?_, ?_⟩
      · rw [h2, exponents_rot, Function.iterate_succ_apply]
      · rw [h3, leafCount_rotA]

lemma exponents_comb : ∀ k : ℕ, (TTree.comb k).exponents = List.replicate (k + 1) 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [comb_succ, TTree.exponents, ih, List.replicate_succ]
      rfl

lemma rightSideLen_comb : ∀ k : ℕ, (TTree.comb k).rightSideLen = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [comb_succ, TTree.rightSideLen, ih]

lemma word_eq' (cs : List ℕ) : word cs = wordFrom 0 cs := rfl

/-- The tree with exponent list `cs` followed by `k + 1` zeros, for `k ≥ cs.sum`. -/
def build : List ℕ → ℕ → TTree
  | [], k => TTree.comb k
  | c :: cs, k => rot^[c] (TTree.node TTree.leaf (build cs k))

lemma build_spec : ∀ (cs : List ℕ) (k : ℕ), cs.sum ≤ k →
    (build cs k).rightSideLen + cs.sum = k + cs.length ∧
    (build cs k).exponents = cs ++ List.replicate (k + 1) 0 := by
  intro cs
  induction cs with
  | nil =>
      intro k _
      exact ⟨by rw [build, rightSideLen_comb]; simp, by rw [build, exponents_comb]; simp⟩
  | cons c cs ih =>
      intro k hk
      rw [List.sum_cons] at hk
      obtain ⟨h1, h2⟩ := ih k (by omega)
      have hrsl : c + 1 ≤ (TTree.node TTree.leaf (build cs k)).rightSideLen := by
        simp only [TTree.rightSideLen]
        omega
      obtain ⟨r1, r2, -⟩ := rot_iterate_spec c _ hrsl
      rw [build]
      refine ⟨?_, ?_⟩
      · simp only [TTree.rightSideLen, List.sum_cons, List.length_cons] at r1 ⊢
        omega
      · rw [r2, TTree.exponents, TTree.leftRuns, h2, List.singleton_append, incrHead_iterate,
          Nat.zero_add, List.cons_append]

end CannonFloydParry

namespace CannonFloydParry

@[simp] lemma extend_one : extend (1 : UI ≃o UI) = 1 := by
  ext x
  by_cases h : x ∈ Set.Icc (0:ℝ) 1
  · rw [extend_apply, extendFun_of_mem _ h]; rfl
  · rw [extend_apply, extendFun_of_notMem _ h]; rfl


end CannonFloydParry

namespace CannonFloydParry

end CannonFloydParry

namespace CannonFloydParry


end CannonFloydParry

namespace CannonFloydParry

/-! ### Small tools -/

/-! ### One piece of the uniform partition -/

/-! ### Every Thompson map has a tree diagram -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### Index bookkeeping for mark lists -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### Deleting a caret

`delCaret t k` merges the `k`th and `(k+1)`th leaves when they are siblings, and is the identity
otherwise.  Its recursion mirrors `caretAt`. -/

def delCaret : TTree → ℕ → TTree
  | TTree.leaf, _ => TTree.leaf
  | TTree.node l r, k =>
      if k + 1 < l.leafCount then TTree.node (delCaret l k) r
      else if l.leafCount ≤ k then TTree.node l (delCaret r (k - l.leafCount))
      else (match l, r with
            | TTree.leaf, TTree.leaf => TTree.leaf
            | _, _ => TTree.node l r)

lemma delCaret_node (l r : TTree) (k : ℕ) :
    delCaret (TTree.node l r) k =
      if k + 1 < l.leafCount then TTree.node (delCaret l k) r
      else if l.leafCount ≤ k then TTree.node l (delCaret r (k - l.leafCount))
      else (match l, r with
            | TTree.leaf, TTree.leaf => TTree.leaf
            | _, _ => TTree.node l r) := rfl

lemma delCaret_node_left {l r : TTree} {k : ℕ} (h : k + 1 < l.leafCount) :
    delCaret (TTree.node l r) k = TTree.node (delCaret l k) r := by
  rw [delCaret_node, if_pos h]

lemma delCaret_node_right {l r : TTree} {k : ℕ} (h1 : ¬ (k + 1 < l.leafCount))
    (h2 : l.leafCount ≤ k) :
    delCaret (TTree.node l r) k = TTree.node l (delCaret r (k - l.leafCount)) := by
  rw [delCaret_node, if_neg h1, if_pos h2]

/-- In the straddling case a caret forces both subtrees to be leaves. -/
lemma leaves_of_caret_straddle {l r : TTree} {k : ℕ} (h1 : ¬ (k + 1 < l.leafCount))
    (h2 : ¬ (l.leafCount ≤ k)) (hc : (TTree.node l r).caretAt k = true) :
    l = TTree.leaf ∧ r = TTree.leaf ∧ k = 0 := by
  have hl : l = TTree.leaf := by
    by_contra hne
    rw [caretAt_node_straddle_false h1 h2 (Or.inl hne)] at hc
    exact Bool.noConfusion hc
  have hr : r = TTree.leaf := by
    by_contra hne
    rw [caretAt_node_straddle_false h1 h2 (Or.inr hne)] at hc
    exact Bool.noConfusion hc
  subst hl
  refine ⟨rfl, hr, ?_⟩
  simp only [TTree.leafCount] at h1 h2
  omega

lemma marksAux_length' : ∀ (t : TTree) (a b : ℝ), (t.marksAux a b).length + 1 = t.leafCount := by
  intro t
  induction t with
  | leaf => intro a b; simp [TTree.marksAux, TTree.leafCount]
  | node l r ihl ihr =>
      intro a b
      rw [TTree.marksAux, TTree.leafCount]
      have h1 := ihl a ((a + b) / 2)
      have h2 := ihr ((a + b) / 2) b
      simp only [List.length_append, List.length_cons]
      omega

lemma leafCount_delCaret : ∀ (t : TTree) (k : ℕ), t.caretAt k = true →
    (delCaret t k).leafCount + 1 = t.leafCount := by
  intro t
  induction t with
  | leaf => intro k h; rw [caretAt_leaf] at h; exact Bool.noConfusion h
  | node l r ihl ihr =>
      intro k hc
      rcases Nat.lt_or_ge (k + 1) l.leafCount with h1 | h1
      · rw [caretAt_node_left h1] at hc
        rw [delCaret_node_left h1, TTree.leafCount, TTree.leafCount]
        have := ihl k hc
        omega
      · rcases Nat.lt_or_ge k l.leafCount with h2 | h2
        · obtain ⟨rfl, rfl, rfl⟩ := leaves_of_caret_straddle (by omega) (by omega) hc
          rfl
        · rw [caretAt_node_right (by omega) h2] at hc
          rw [delCaret_node_right (by omega) h2, TTree.leafCount, TTree.leafCount]
          have := ihr _ hc
          omega

lemma marksAux_delCaret : ∀ (t : TTree) (k : ℕ) (a b : ℝ), t.caretAt k = true →
    (delCaret t k).marksAux a b = (t.marksAux a b).eraseIdx k := by
  intro t
  induction t with
  | leaf => intro k a b h; rw [caretAt_leaf] at h; exact Bool.noConfusion h
  | node l r ihl ihr =>
      intro k a b hc
      have hlen := marksAux_length' l a ((a + b) / 2)
      rcases Nat.lt_or_ge (k + 1) l.leafCount with h1 | h1
      · rw [caretAt_node_left h1] at hc
        rw [delCaret_node_left h1, TTree.marksAux, TTree.marksAux, ihl k _ _ hc,
          List.eraseIdx_append_of_lt_length (by omega)]
      · rcases Nat.lt_or_ge k l.leafCount with h2 | h2
        · obtain ⟨rfl, rfl, rfl⟩ := leaves_of_caret_straddle (by omega) (by omega) hc
          rfl
        · rw [caretAt_node_right (by omega) h2] at hc
          rw [delCaret_node_right (by omega) h2, TTree.marksAux, TTree.marksAux, ihr _ _ _ hc,
            List.eraseIdx_append_of_length_le (by omega),
            show k - (l.marksAux a ((a + b) / 2)).length = (k - l.leafCount) + 1 by omega,
            List.eraseIdx_cons_succ]

/-- The full mark list of `t` placed on `[a,b]`. -/
noncomputable def mk (t : TTree) (a b : ℝ) : List ℝ := a :: (t.marksAux a b ++ [b])

lemma marks_eq_mk (t : TTree) : t.marks = mk t 0 1 := rfl

lemma mk_node (l r : TTree) (a b : ℝ) :
    mk (TTree.node l r) a b = (a :: l.marksAux a ((a + b) / 2)) ++ mk r ((a + b) / 2) b := by
  simp [mk, TTree.marksAux]

lemma mk_node_getD_le (l r : TTree) (a b : ℝ) {j : ℕ} (hj : j ≤ l.leafCount) :
    (mk (TTree.node l r) a b).getD j 0 = (mk l a ((a + b) / 2)).getD j 0 := by
  have hlen := marksAux_length' l a ((a + b) / 2)
  rw [mk_node]
  rcases Nat.lt_or_ge j l.leafCount with h | h
  · rw [List.getD_append _ _ _ _ (by simp; omega)]
    show (a :: l.marksAux a ((a + b) / 2)).getD j 0
      = ((a :: l.marksAux a ((a + b) / 2)) ++ [(a + b) / 2]).getD j 0
    rw [List.getD_append _ _ _ _ (by simp; omega)]
  · have hj' : j = l.leafCount := by omega
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    show (mk r ((a + b) / 2) b).getD (j - (l.marksAux a ((a + b) / 2)).length - 1) 0
      = ((a :: l.marksAux a ((a + b) / 2)) ++ [(a + b) / 2]).getD j 0
    rw [List.getD_append_right _ _ _ _ (by simp; omega),
      show j - (l.marksAux a ((a + b) / 2)).length - 1 = 0 by omega,
      show j - (a :: l.marksAux a ((a + b) / 2)).length = 0 by simp; omega]
    rfl

lemma mk_node_getD_ge (l r : TTree) (a b : ℝ) {j : ℕ} (hj : l.leafCount ≤ j) :
    (mk (TTree.node l r) a b).getD j 0 = (mk r ((a + b) / 2) b).getD (j - l.leafCount) 0 := by
  have hlen := marksAux_length' l a ((a + b) / 2)
  rw [mk_node, List.getD_append_right _ _ _ _ (by simp; omega)]
  congr 1
  simp only [List.length_cons]
  omega

/-- A caret's middle mark is the midpoint of its two neighbours. -/
lemma mk_caret_mid : ∀ (t : TTree) (k : ℕ) (a b : ℝ), t.caretAt k = true →
    2 * (mk t a b).getD (k + 1) 0 = (mk t a b).getD k 0 + (mk t a b).getD (k + 2) 0 := by
  intro t
  induction t with
  | leaf => intro k a b h; rw [caretAt_leaf] at h; exact Bool.noConfusion h
  | node l r ihl ihr =>
      intro k a b hc
      rcases Nat.lt_or_ge (k + 1) l.leafCount with h1 | h1
      · rw [caretAt_node_left h1] at hc
        rw [mk_node_getD_le l r a b (by omega), mk_node_getD_le l r a b (by omega),
          mk_node_getD_le l r a b (by omega)]
        exact ihl k _ _ hc
      · rcases Nat.lt_or_ge k l.leafCount with h2 | h2
        · obtain ⟨rfl, rfl, rfl⟩ := leaves_of_caret_straddle (by omega) (by omega) hc
          simp [mk, TTree.marksAux]
          ring
        · rw [caretAt_node_right (by omega) h2] at hc
          rw [mk_node_getD_ge l r a b (by omega), mk_node_getD_ge l r a b (by omega),
            mk_node_getD_ge l r a b (by omega),
            show k + 1 - l.leafCount = (k - l.leafCount) + 1 by omega,
            show k + 2 - l.leafCount = (k - l.leafCount) + 2 by omega]
          exact ihr _ _ _ hc

lemma marks_delCaret {t : TTree} {k : ℕ} (hc : t.caretAt k = true) :
    (delCaret t k).marks = t.marks.eraseIdx (k + 1) := by
  have hk : k < (t.marksAux 0 1).length := by
    have h1 := marksAux_length' t 0 1
    have h2 := caretAt_of_le t k
    by_contra hcon
    have : t.leafCount ≤ k + 1 := by omega
    rw [h2 (by omega)] at hc
    exact Bool.noConfusion hc
  show (0 : ℝ) :: ((delCaret t k).marksAux 0 1 ++ [1]) = ((0 : ℝ) :: (t.marksAux 0 1 ++ [1])).eraseIdx (k + 1)
  rw [marksAux_delCaret t k 0 1 hc, List.eraseIdx_cons_succ,
    List.eraseIdx_append_of_lt_length hk]

/-! ### `getD` through `eraseIdx`, and chains through `eraseIdx` -/

lemma getD_eraseIdx_lt : ∀ (xs : List ℝ) (j i : ℕ), i < j →
    (xs.eraseIdx j).getD i 0 = xs.getD i 0 := by
  intro xs
  induction xs with
  | nil => intro j i _; simp
  | cons x t ih =>
      intro j i hij
      cases j with
      | zero => omega
      | succ j =>
          rw [List.eraseIdx_cons_succ]
          cases i with
          | zero => rfl
          | succ i => rw [List.getD_cons_succ, List.getD_cons_succ]; exact ih j i (by omega)

lemma getD_eraseIdx_ge : ∀ (xs : List ℝ) (j i : ℕ), j ≤ i →
    (xs.eraseIdx j).getD i 0 = xs.getD (i + 1) 0 := by
  intro xs
  induction xs with
  | nil => intro j i _; simp
  | cons x t ih =>
      intro j i hij
      cases j with
      | zero => rw [List.eraseIdx_cons_zero, List.getD_cons_succ]
      | succ j =>
          rw [List.eraseIdx_cons_succ]
          cases i with
          | zero => omega
          | succ i => rw [List.getD_cons_succ, List.getD_cons_succ]; exact ih j i (by omega)

lemma length_eraseIdx_of_lt {xs : List ℝ} {j : ℕ} (h : j < xs.length) :
    (xs.eraseIdx j).length + 1 = xs.length := by
  rw [List.length_eraseIdx_of_lt h]; omega

/-! ### Deleting a common caret preserves the element -/

lemma affine_merge {x0 x1 x2 y0 y1 y2 p q p' q' : ℝ} {L : ℝ → ℝ}
    (hx : x0 < x1) (hx' : x1 < x2) (hmx : 2 * x1 = x0 + x2) (hmy : 2 * y1 = y0 + y2)
    (h0 : p * x0 + q = y0) (h1 : p * x1 + q = y1) (h1' : p' * x1 + q' = y1)
    (h2 : p' * x2 + q' = y2)
    (hL : ∀ z ∈ Set.Icc x0 x1, L z = p * z + q) (hL' : ∀ z ∈ Set.Icc x1 x2, L z = p' * z + q') :
    ∀ z ∈ Set.Icc x0 x2, L z = p * z + q := by
  have hpp : p * (x1 - x0) = p' * (x2 - x1) := by linarith
  have hd : x1 - x0 = x2 - x1 := by linarith
  have hp : p = p' := by
    rw [hd] at hpp
    have : x2 - x1 ≠ 0 := by linarith
    exact mul_right_cancel₀ this hpp
  have hq : q = q' := by rw [hp] at h1; linarith
  intro z hz
  rcases le_or_gt z x1 with h | h
  · exact hL z ⟨hz.1, h⟩
  · rw [hL' z ⟨le_of_lt h, hz.2⟩, hp, hq]

lemma represents_delCaret {R S : TTree} {h : R.leafCount = S.leafCount} {f : UI ≃o UI}
    (hr : Represents ⟨R, S, h⟩ f) {k : ℕ} (hcR : R.caretAt k = true) (hcS : S.caretAt k = true) :
    Represents ⟨delCaret R k, delCaret S k, by
      have := leafCount_delCaret R k hcR
      have := leafCount_delCaret S k hcS
      omega⟩ f := by
  obtain ⟨hF, hA, hM⟩ := hr
  have hA' : AffineOnPieces (extend f) R.marks := hA
  have hM' : R.marks.map (extend f) = S.marks := hM
  have hlenR := marks_length_eq R
  have hlenS := marks_length_eq S
  have hk2 : k + 2 < R.marks.length := by
    have := caretAt_of_le R k
    by_contra hcon
    rw [this (by omega)] at hcR
    exact Bool.noConfusion hcR
  have hmap : ∀ i, i < R.marks.length → extend f (R.marks.getD i 0) = S.marks.getD i 0 := by
    intro i hi
    rw [← hM', getD_map hi]
  have hmidR := mk_caret_mid R k 0 1 hcR
  have hmidS := mk_caret_mid S k 0 1 hcS
  rw [← marks_eq_mk] at hmidR hmidS
  refine ⟨hF, ?_, ?_⟩
  · show AffineOnPieces (extend f) (delCaret R k).marks
    rw [marks_delCaret hcR]
    refine getD_chain _ ?_
    intro j hj
    have hlen' := length_eraseIdx_of_lt (xs := R.marks) (j := k + 1) (by omega)
    rcases Nat.lt_or_ge (j + 1) (k + 1) with hjk | hjk
    · -- an untouched pair below the caret
      rw [getD_eraseIdx_lt _ _ _ (by omega), getD_eraseIdx_lt _ _ _ hjk]
      exact chain_getD _ hA' j (by omega)
    · rcases Nat.lt_or_ge j (k + 1) with hjk' | hjk'
      · -- the merged pair
        have hjk'' : j = k := by omega
        subst hjk''
        rw [getD_eraseIdx_lt _ _ _ (by omega), getD_eraseIdx_ge _ _ _ (by omega)]
        obtain ⟨p, q, hpq⟩ := chain_getD _ hA' j (by omega)
        obtain ⟨p', q', hpq'⟩ := chain_getD _ hA' (j + 1) (by omega)
        have hx := marks_getD_lt R (j := j) (by omega)
        have hx' := marks_getD_lt R (j := j + 1) (by omega)
        refine ⟨p, q, affine_merge hx hx' hmidR hmidS ?_ ?_ ?_ ?_ hpq hpq'⟩
        · rw [← hpq _ ⟨le_refl _, le_of_lt hx⟩]; exact hmap j (by omega)
        · rw [← hpq _ ⟨le_of_lt hx, le_refl _⟩]; exact hmap (j + 1) (by omega)
        · rw [← hpq' _ ⟨le_refl _, le_of_lt hx'⟩]; exact hmap (j + 1) (by omega)
        · rw [← hpq' _ ⟨le_of_lt hx', le_refl _⟩]; exact hmap (j + 2) (by omega)
      · -- an untouched pair above the caret
        rw [getD_eraseIdx_ge _ _ _ hjk', getD_eraseIdx_ge _ _ _ (by omega)]
        exact chain_getD _ hA' (j + 1) (by omega)
  · show (delCaret R k).marks.map (extend f) = (delCaret S k).marks
    rw [marks_delCaret hcR, marks_delCaret hcS, ← List.eraseIdx_map, hM']

/-! ### A diagram with the fewest leaves is reduced -/


end CannonFloydParry

namespace CannonFloydParry

/-! ### Standard dyadic intervals are nested or have disjoint interiors -/

/-! ### Affine images of standard dyadic subintervals -/

/-! ### Membership in mark lists -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### The two halves of a standard dyadic interval, as casts -/

lemma caretAt_le {t : TTree} {k : ℕ} (h : t.caretAt k = true) : k + 2 ≤ t.leafCount := by
  by_contra hcon
  rw [caretAt_of_le t k (by omega)] at h
  exact Bool.noConfusion h

/-! ### The parent of a caret is a standard dyadic interval -/

/-! ### Two consecutive leaves whose union is standard dyadic are siblings -/

/-! ### A standard dyadic interval with a mark strictly inside contains a caret -/

/-! ### The three lemmas specialised to `[0,1]` -/

/-! ### Strictly increasing lists with the same members are equal -/

/-! ### Uniqueness of the reduced diagram -/


end CannonFloydParry

namespace CannonFloydParry

/-! ### A diagram for any pair of exponent lists -/

lemma represents_build (as bs : List ℕ) (k : ℕ) (hk1 : as.sum ≤ k) (hk2 : bs.sum ≤ k)
    (hlen : as.length = bs.length) :
    Represents ⟨build as k, build bs k, by
      obtain ⟨-, hEA⟩ := build_spec as k hk1
      obtain ⟨-, hEB⟩ := build_spec bs k hk2
      rw [← exponents_length, ← exponents_length, hEA, hEB]
      simp [hlen]⟩ (word bs * (word as)⁻¹) := by
  obtain ⟨-, hEA⟩ := build_spec as k hk1
  obtain ⟨-, hEB⟩ := build_spec bs k hk2
  have hlc : (build as k).leafCount = (build bs k).leafCount := by
    rw [← exponents_length, ← exponents_length, hEA, hEB]
    simp [hlen]
  have hzero : (List.replicate (k + 1) 0).sum = 0 := by simp
  have hwA : word (build as k).exponents = word as := by
    rw [hEA, word_eq', wordFrom_append, wordFrom_of_sum_eq_zero _ hzero, mul_one, word_eq']
  have hwB : word (build bs k).exponents = word bs := by
    rw [hEB, word_eq', wordFrom_append, wordFrom_of_sum_eq_zero _ hzero, mul_one, word_eq']
  have hdom : (build as k).leafCount = (TTree.comb ((build as k).leafCount - 1)).leafCount := by
    rw [leafCount_comb]; have := one_le_leafCount' (build as k); omega
  have hran : (build bs k).leafCount = (TTree.comb ((build as k).leafCount - 1)).leafCount := by
    rw [← hlc]; exact hdom
  have hR := represents_word_inv _ (build as k) _ hdom le_rfl
  have hS := represents_word_inv _ (build bs k) _ hran le_rfl
  have hS' := represents_inv _ hS
  rw [inv_inv] at hS'
  have hcomp := represents_mul _ _ hR hS'
  rw [hwA, hwB] at hcomp
  exact hcomp

/-! ### Deleting the last caret drops a trailing zero exponent -/

lemma exponents_delCaret_last : ∀ t : TTree, t.endsInCaret = true →
    (delCaret t (t.leafCount - 2)).exponents ++ [0] = t.exponents := by
  intro t
  induction t with
  | leaf => intro h; rw [endsInCaret_leaf] at h; exact Bool.noConfusion h
  | node l r ihl ihr =>
      intro h
      cases r with
      | leaf =>
          cases l with
          | leaf => rfl
          | node a b =>
              rw [endsInCaret_right_leaf (by intro h'; exact TTree.noConfusion h')] at h
              exact Bool.noConfusion h
      | node a b =>
          rw [endsInCaret_node_node] at h
          have hr2 : 2 ≤ (TTree.node a b).leafCount := by
            have := one_le_leafCount a
            have := one_le_leafCount b
            rw [TTree.leafCount]; omega
          have hl1 := one_le_leafCount l
          have hidx : (TTree.node l (TTree.node a b)).leafCount - 2
              = l.leafCount + ((TTree.node a b).leafCount - 2) := by
            simp only [TTree.leafCount] at hr2 ⊢; omega
          rw [hidx, delCaret_node_right (by omega) (by omega),
            show l.leafCount + ((TTree.node a b).leafCount - 2) - l.leafCount
              = (TTree.node a b).leafCount - 2 by omega,
            TTree.exponents, TTree.exponents, List.append_assoc, ihr h]

/-! ### Reducing a diagram whose exponent lists are padded normal-form data -/

/-- The exponent lists of `d` are `as` and `bs` padded with `i` zeros. -/
def Padded (as bs : List ℕ) (i : ℕ) (d : TreeDiagram) : Prop :=
  d.dom.exponents = as ++ List.replicate i 0 ∧ d.ran.exponents = bs ++ List.replicate i 0

lemma getD_replicate_zero (m i : ℕ) : (List.replicate m 0).getD i 0 = 0 := by
  rcases Nat.lt_or_ge i m with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp
  · exact getD_ge_length (by simpa using h)

lemma getD_padded {as : List ℕ} {i j : ℕ} :
    (as ++ List.replicate i 0).getD j 0 = as.getD j 0 := by
  rcases Nat.lt_or_ge j as.length with h | h
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ h, getD_replicate_zero, getD_ge_length h]

lemma two_le_of_endsInCaret {t : TTree} (h : t.endsInCaret = true) : 2 ≤ t.leafCount := by
  cases t with
  | leaf => rw [endsInCaret_leaf] at h; exact Bool.noConfusion h
  | node l r =>
      have := one_le_leafCount l
      have := one_le_leafCount r
      rw [TTree.leafCount]; omega

/-- With normal-form data, the padding is at least one zero. -/
lemma padded_pos {as bs : List ℕ} {i : ℕ} {d : TreeDiagram} (hNF : IsNormalFormData as bs)
    (hP : Padded as bs i d) : 1 ≤ i := by
  obtain ⟨hne, hlen, hlast, -⟩ := hNF
  by_contra hi
  have hi0 : i = 0 := by omega
  rw [hi0] at hP
  obtain ⟨hA, hB⟩ := hP
  simp only [List.replicate_zero, List.append_nil] at hA hB
  have hLA : as.length = d.dom.leafCount := by rw [← hA, exponents_length]
  have hLB : bs.length = d.ran.leafCount := by rw [← hB, exponents_length]
  have hA0 := exponents_getD_last d.dom
  have hB0 := exponents_getD_last d.ran
  rw [hA, ← hLA] at hA0
  rw [hB, ← hLB, ← hlen] at hB0
  rcases hlast with ⟨-, h⟩ | ⟨h, -⟩ <;> omega

/-- A common caret of a padded normal-form diagram can only sit at the last pair. -/
lemma common_caret_last {as bs : List ℕ} {i : ℕ} {d : TreeDiagram} (hNF : IsNormalFormData as bs)
    (hP : Padded as bs i d) {k : ℕ} (hcR : d.dom.caretAt k = true) (hcS : d.ran.caretAt k = true) :
    k + 2 = d.dom.leafCount := by
  obtain ⟨hne, hlen, hlast, hint⟩ := hNF
  obtain ⟨hA, hB⟩ := hP
  have hk := caretAt_le hcR
  by_contra hcon
  have hk2 : k + 2 < d.dom.leafCount := by omega
  obtain ⟨ha, ha'⟩ := (caretAt_iff_exponents d.dom k hk2).mp hcR
  obtain ⟨hb, hb'⟩ :=
    (caretAt_iff_exponents d.ran k (by rw [← d.leaves_eq]; exact hk2)).mp hcS
  rw [hA, getD_padded] at ha ha'
  rw [hB, getD_padded] at hb hb'
  rcases Nat.lt_or_ge k as.length with hkL | hkL
  · rcases Nat.lt_or_ge (k + 1) as.length with hk1 | hk1
    · rcases hint k hk1 ha hb with h | h <;> omega
    · have hkeq : k = as.length - 1 := by omega
      rw [← hkeq] at hlast
      rcases hlast with ⟨h, -⟩ | ⟨-, h⟩ <;> omega
  · rw [getD_ge_length hkL] at ha
    exact lt_irrefl _ ha

lemma padded_delCaret {as bs : List ℕ} {i : ℕ} {R S : TTree} {h : R.leafCount = S.leafCount}
    (hNF : IsNormalFormData as bs) (hP : Padded as bs (i + 1) ⟨R, S, h⟩)
    (hR : R.endsInCaret = true) (hS : S.endsInCaret = true) :
    Padded as bs i ⟨delCaret R (R.leafCount - 2), delCaret S (R.leafCount - 2), by
      have hcS2 : S.caretAt (R.leafCount - 2) = true := by
        rw [h, ← endsInCaret_eq_caretAt S (two_le_of_endsInCaret hS)]; exact hS
      have hcR2 : R.caretAt (R.leafCount - 2) = true := by
        rw [← endsInCaret_eq_caretAt R (two_le_of_endsInCaret hR)]; exact hR
      have h1 := leafCount_delCaret R _ hcR2
      have h2 := leafCount_delCaret S _ hcS2
      omega⟩ := by
  obtain ⟨hA, hB⟩ := hP
  have eA := exponents_delCaret_last R hR
  have eB := exponents_delCaret_last S hS
  rw [← h] at eB
  constructor
  · show (delCaret R (R.leafCount - 2)).exponents = as ++ List.replicate i 0
    have : (delCaret R (R.leafCount - 2)).exponents ++ [0]
        = (as ++ List.replicate i 0) ++ [0] := by
      rw [eA, hA, List.append_assoc, List.replicate_succ']
    exact List.append_cancel_right this
  · show (delCaret S (R.leafCount - 2)).exponents = bs ++ List.replicate i 0
    have : (delCaret S (R.leafCount - 2)).exponents ++ [0]
        = (bs ++ List.replicate i 0) ++ [0] := by
      rw [eB, hB, List.append_assoc, List.replicate_succ']
    exact List.append_cancel_right this

lemma endsInCaret_of_last_caret {t : TTree} {k : ℕ} (hk : k + 2 = t.leafCount)
    (hc : t.caretAt k = true) : t.endsInCaret = true := by
  rw [endsInCaret_eq_caretAt t (by omega), show t.leafCount - 2 = k by omega]
  exact hc

/-- From a padded normal-form diagram, deleting last carets reaches a reduced diagram with the
same normal-form data. -/
lemma reduced_of_padded : ∀ (N : ℕ) {f : UI ≃o UI} {as bs : List ℕ} (d : TreeDiagram),
    d.dom.leafCount ≤ N → IsNormalFormData as bs → Represents d f → (∃ i, Padded as bs i d) →
    ∃ d' : TreeDiagram, IsReduced d' ∧ Represents d' f ∧ ∃ j, Padded as bs j d' := by
  intro N
  induction N with
  | zero =>
      intro f as bs d hN _ _ _
      have := one_le_leafCount d.dom
      omega
  | succ N ih =>
      intro f as bs d hN hNF hr ⟨i, hP⟩
      by_cases hred : IsReduced d
      · exact ⟨d, hred, hr, i, hP⟩
      · obtain ⟨k, hcR, hcS⟩ : ∃ k, d.dom.caretAt k = true ∧ d.ran.caretAt k = true := by
          simp only [IsReduced, not_forall, not_not] at hred
          exact hred
        have hlast := common_caret_last hNF hP hcR hcS
        have hR := endsInCaret_of_last_caret hlast hcR
        have hS := endsInCaret_of_last_caret (by rw [← d.leaves_eq]; exact hlast) hcS
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by have := padded_pos hNF hP; omega⟩
        obtain ⟨R, S, h⟩ := d
        have hP' : Padded as bs (i' + 1) ⟨R, S, h⟩ := hP
        have hr' : Represents ⟨R, S, h⟩ f := hr
        have hcR' : R.caretAt (R.leafCount - 2) = true := by
          rw [show R.leafCount - 2 = k by simp only at hlast; omega]; exact hcR
        have hcS' : S.caretAt (S.leafCount - 2) = true := by
          rw [show S.leafCount - 2 = k by simp only at hlast; rw [← h]; omega]; exact hcS
        have hsmall := represents_delCaret hr' hcR' (by rw [h]; exact hcS')
        have hPd := padded_delCaret hNF hP' hR hS
        have hlc := leafCount_delCaret R _ hcR'
        refine ih _ ?_ hNF hsmall ⟨i', ?_⟩
        · show (delCaret R (R.leafCount - 2)).leafCount ≤ N
          simp only at hN; omega
        · exact hPd

/-! ### Normal-form data with equal padded lists agree -/

lemma padded_eq {as bs as' bs' : List ℕ} {j j' : ℕ}
    (hNF : IsNormalFormData as bs) (hNF' : IsNormalFormData as' bs')
    (hA : as ++ List.replicate j 0 = as' ++ List.replicate j' 0)
    (hB : bs ++ List.replicate j 0 = bs' ++ List.replicate j' 0) :
    as = as' ∧ bs = bs' := by
  obtain ⟨hne, hlen, hlast, -⟩ := hNF
  obtain ⟨hne', hlen', hlast', -⟩ := hNF'
  have hL : as.length + j = as'.length + j' := by
    have := congrArg List.length hA
    simpa using this
  -- the shorter data, padded, would have both last entries zero
  have key : ∀ (as bs as' bs' : List ℕ) (j j' : ℕ), as.length < as'.length →
      as.length = bs.length → as'.length = bs'.length →
      as.length + j = as'.length + j' →
      as ++ List.replicate j 0 = as' ++ List.replicate j' 0 →
      bs ++ List.replicate j 0 = bs' ++ List.replicate j' 0 →
      ∀ i, as.length ≤ i → as'.getD i 0 = 0 ∧ bs'.getD i 0 = 0 := by
    intro as bs as' bs' j j' hlt hl hl' hL hA hB i hi
    obtain ⟨m, hm⟩ : ∃ m, j = (as'.length - as.length) + m := ⟨j - (as'.length - as.length), by omega⟩
    have hj' : j' = m := by omega
    subst hj'
    rw [hm, List.replicate_add, ← List.append_assoc] at hA hB
    have hA' := List.append_cancel_right hA
    have hB' := List.append_cancel_right hB
    constructor
    · rw [← hA', List.getD_append_right _ _ _ _ hi, getD_replicate_zero]
    · rw [← hB', List.getD_append_right _ _ _ _ (by omega), getD_replicate_zero]
  rcases Nat.lt_trichotomy as.length as'.length with hlt | heq | hgt
  · exfalso
    obtain ⟨h1, h2⟩ := key as bs as' bs' j j' hlt hlen hlen' hL hA hB (as'.length - 1) (by omega)
    rcases hlast' with ⟨-, h⟩ | ⟨h, -⟩ <;> omega
  · have hj : j = j' := by omega
    subst hj
    exact ⟨List.append_cancel_right hA, List.append_cancel_right hB⟩
  · exfalso
    obtain ⟨h1, h2⟩ := key as' bs' as bs j' j hgt hlen' hlen (by omega) hA.symm hB.symm
      (as.length - 1) (by omega)
    rcases hlast with ⟨-, h⟩ | ⟨h, -⟩ <;> omega

/-! ### Corollary-Definition 2.7 -/

lemma reduced_of_nf {f : UI ≃o UI} {as bs : List ℕ} (hNF : IsNormalFormData as bs)
    (hf : f = word bs * (word as)⁻¹) :
    ∃ d : TreeDiagram, IsReduced d ∧ Represents d f ∧ ∃ j, Padded as bs j d := by
  have hlen := hNF.2.1
  set k := as.sum + bs.sum with hk
  have hr := represents_build as bs k (by omega) (by omega) hlen
  rw [← hf] at hr
  obtain ⟨-, hEA⟩ := build_spec as k (by omega)
  obtain ⟨-, hEB⟩ := build_spec bs k (by omega)
  exact reduced_of_padded _ _ le_rfl hNF hr ⟨k + 1, hEA, hEB⟩

theorem existsUnique_normalForm' {f : UI ≃o UI} (hf : f ∈ F) (hne : f ≠ 1) :
    ∃! p : List ℕ × List ℕ, IsNormalFormData p.1 p.2 ∧ f = word p.2 * (word p.1)⁻¹ := by
  obtain ⟨d, hd, hr⟩ := exists_isReduced_represents hf
  obtain ⟨as, bs, hNF, hfeq⟩ := exists_isNormalFormData hd hr hne
  refine ⟨(as, bs), ⟨hNF, hfeq⟩, ?_⟩
  rintro ⟨as', bs'⟩ ⟨hNF', hfeq'⟩
  obtain ⟨d₁, hd₁, hr₁, j₁, hP₁⟩ := reduced_of_nf hNF' hfeq'
  obtain ⟨d₂, hd₂, hr₂, j₂, hP₂⟩ := reduced_of_nf hNF hfeq
  have hdd : d₁ = d₂ := isReduced_represents_unique hd₁ hr₁ hd₂ hr₂
  subst hdd
  obtain ⟨hA, hB⟩ := padded_eq hNF' hNF (hP₁.1.symm.trans hP₂.1) (hP₁.2.symm.trans hP₂.2)
  simp only [Prod.mk.injEq]
  exact ⟨hA, hB⟩

end CannonFloydParry

open CannonFloydParry

theorem solution {f : UI ≃o UI} (hf : f ∈ F) (hne : f ≠ 1) :
    ∃! p : List ℕ × List ℕ, IsNormalFormData p.1 p.2 ∧ f = word p.2 * (word p.1)⁻¹ :=
  existsUnique_normalForm' hf hne
