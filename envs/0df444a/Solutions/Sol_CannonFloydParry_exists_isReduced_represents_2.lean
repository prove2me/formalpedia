-- Prove2me | solution 2 for CannonFloydParry.exists_isReduced_represents
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-22T13:36:18.154945+00:00
-- url     : https://prove2.me/submissions/fbd63e9d-760e-41e1-b832-4553e6ea0a58

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson

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

lemma two_le_marks_length (t : TTree) : 2 ≤ t.marks.length := by
  have := marks_length_eq t
  have := one_le_leafCount' t
  omega

lemma marks_getD_zero (t : TTree) : t.marks.getD 0 0 = 0 := rfl

lemma getD_getLast : ∀ (xs : List ℝ) (v : ℝ), xs.getLast? = some v →
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

lemma marks_getD_last (t : TTree) : t.marks.getD (t.marks.length - 1) 0 = 1 := by
  refine getD_getLast _ 1 ?_
  show ((0 : ℝ) :: (t.marksAux 0 1 ++ [1])).getLast? = some 1
  rw [← List.cons_append,
    List.getLast?_append_of_ne_nil _ (by simp : ([(1 : ℝ)] : List ℝ) ≠ [])]
  rfl

/-! ### Every point of `[0,1]` lies in one of the pieces -/

lemma exists_piece (t : TTree) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    ∃ j, j + 1 < t.marks.length ∧ t.marks.getD j 0 ≤ z ∧ z ≤ t.marks.getD (j + 1) 0 := by
  classical
  set xs := t.marks with hxs
  set n : ℕ := xs.length - 2 with hn
  have hlen : 2 ≤ xs.length := two_le_marks_length t
  set P : ℕ → Prop := fun j => xs.getD j 0 ≤ z with hP
  have hP0 : P 0 := by
    show xs.getD 0 0 ≤ z
    rw [hxs, marks_getD_zero]
    exact hz.1
  have hjle : Nat.findGreatest P n ≤ n := Nat.findGreatest_le n
  have hjP : P (Nat.findGreatest P n) := Nat.findGreatest_spec (Nat.zero_le n) hP0
  refine ⟨Nat.findGreatest P n, by omega, hjP, ?_⟩
  rcases Nat.lt_or_ge (Nat.findGreatest P n) n with hlt | hge
  · -- not the last piece: `j + 1` fails the predicate
    have hnot : ¬ P (Nat.findGreatest P n + 1) :=
      Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (by omega)
    simp only [hP, not_le] at hnot
    exact le_of_lt hnot
  · -- the last piece: its right endpoint is `1`
    have hidx : Nat.findGreatest P n + 1 = xs.length - 1 := by omega
    rw [hidx, hxs, marks_getD_last]
    exact hz.2

/-! ### An element is determined by its diagram -/

lemma affine_eq_of_endpoints {u v z p q p' q' : ℝ} (huv : u < v)
    (h1 : p * u + q = p' * u + q') (h2 : p * v + q = p' * v + q') :
    p * z + q = p' * z + q' := by
  have hpp : (p - p') * (u - v) = 0 := by linear_combination h1 - h2
  have hp : p = p' := by
    rcases mul_eq_zero.mp hpp with h | h
    · linarith
    · exfalso; linarith
  have hq : q = q' := by rw [hp] at h1; linarith
  rw [hp, hq]

lemma represents_unique {d : TreeDiagram} {f g : UI ≃o UI}
    (hf : Represents d f) (hg : Represents d g) : f = g := by
  obtain ⟨-, hfA, hfM⟩ := hf
  obtain ⟨-, hgA, hgM⟩ := hg
  have hfA' : AffineOnPieces (extend f) d.dom.marks := hfA
  have hgA' : AffineOnPieces (extend g) d.dom.marks := hgA
  have hmap : ∀ i, i < d.dom.marks.length →
      extend f (d.dom.marks.getD i 0) = extend g (d.dom.marks.getD i 0) := by
    intro i hi
    have e1 : (d.dom.marks.map (extend f)).getD i 0 = d.ran.marks.getD i 0 := by rw [hfM]
    have e2 : (d.dom.marks.map (extend g)).getD i 0 = d.ran.marks.getD i 0 := by rw [hgM]
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      ← List.getD_eq_getElem _ _ hi] at e1 e2
    rw [e1, e2]
  -- equal on `[0,1]`, hence equal
  have hpt : ∀ w : UI, (f w : ℝ) = (g w : ℝ) := by
    intro w
    obtain ⟨j, hj, hj1, hj2⟩ := exists_piece d.dom w.2
    obtain ⟨p, q, hpq⟩ := chain_getD _ hfA' j hj
    obtain ⟨p', q', hpq'⟩ := chain_getD _ hgA' j hj
    have hlt := marks_getD_lt d.dom hj
    have E1 := hmap j (by omega)
    have E2 := hmap (j + 1) (by omega)
    rw [hpq _ ⟨le_refl _, le_of_lt hlt⟩, hpq' _ ⟨le_refl _, le_of_lt hlt⟩] at E1
    rw [hpq _ ⟨le_of_lt hlt, le_refl _⟩, hpq' _ ⟨le_of_lt hlt, le_refl _⟩] at E2
    have key : extend f (w : ℝ) = extend g (w : ℝ) := by
      rw [hpq _ ⟨hj1, hj2⟩, hpq' _ ⟨hj1, hj2⟩]
      exact affine_eq_of_endpoints hlt E1 E2
    rw [extend_apply, extend_apply, extendFun_of_mem _ w.2, extendFun_of_mem _ w.2] at key
    have : (⟨(w : ℝ), w.2⟩ : UI) = w := rfl
    rw [this] at key
    exact key
  ext w
  exact hpt w

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

lemma represents_id (t : TTree) : Represents ⟨t, t, rfl⟩ (1 : UI ≃o UI) := by
  refine ⟨one_mem F, ?_, ?_⟩
  · show AffineOnPieces (extend (1 : UI ≃o UI)) t.marks
    refine isChain_of_pairs _ ?_
    intro u _ v _
    exact ⟨1, 0, fun z _ => by rw [extend_one_apply]; ring⟩
  · show t.marks.map (extend (1 : UI ≃o UI)) = t.marks
    rw [coe_extend_one, List.map_id]

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

lemma extend_mul_apply (f g : UI ≃o UI) (z : ℝ) :
    extend (g * f) z = extend g (extend f z) := by
  by_cases h : z ∈ Set.Icc (0 : ℝ) 1
  · have h1 : extend f z = ((f ⟨z, h⟩ : UI) : ℝ) := by
      rw [extend_apply, extendFun_of_mem _ h]
    have h2 : ((f ⟨z, h⟩ : UI) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := (f ⟨z, h⟩).2
    rw [h1, extend_apply (g * f) z, extend_apply g ((f ⟨z, h⟩ : UI) : ℝ),
      extendFun_of_mem _ h, extendFun_of_mem _ h2]
    rfl
  · have h1 : extend f z = z := by rw [extend_apply, extendFun_of_notMem _ h]
    rw [h1, extend_apply (g * f) z, extend_apply g z, extendFun_of_notMem _ h,
      extendFun_of_notMem _ h]

lemma represents_mul {Q R S : TTree} {f g : UI ≃o UI}
    (hQR : Q.leafCount = R.leafCount) (hRS : R.leafCount = S.leafCount)
    (hf : Represents ⟨Q, R, hQR⟩ f) (hg : Represents ⟨R, S, hRS⟩ g) :
    Represents ⟨Q, S, hQR.trans hRS⟩ (g * f) := by
  obtain ⟨hfF, hfA, hfM⟩ := hf
  obtain ⟨hgF, hgA, hgM⟩ := hg
  have hfA' : AffineOnPieces (extend f) Q.marks := hfA
  have hgA' : AffineOnPieces (extend g) R.marks := hgA
  have hfM' : Q.marks.map (extend f) = R.marks := hfM
  have hgM' : R.marks.map (extend g) = S.marks := hgM
  have hlenQR : Q.marks.length = R.marks.length := by
    rw [marks_length_eq, marks_length_eq, hQR]
  have hmapj : ∀ i, i < Q.marks.length → extend f (Q.marks.getD i 0) = R.marks.getD i 0 := by
    intro i hi
    have h : (Q.marks.map (extend f)).getD i 0 = R.marks.getD i 0 := by rw [hfM']
    rw [getD_map hi] at h
    exact h
  refine ⟨mul_mem hgF hfF, ?_, ?_⟩
  · show AffineOnPieces (extend (g * f)) Q.marks
    refine getD_chain _ ?_
    intro j hj
    obtain ⟨a, c, hac⟩ := chain_getD _ hfA' j hj
    obtain ⟨a', c', hac'⟩ := chain_getD _ hgA' j (by rw [← hlenQR]; exact hj)
    refine ⟨a' * a, a' * c + c', ?_⟩
    intro z hz
    have hfz : extend f z ∈ Set.Icc (R.marks.getD j 0) (R.marks.getD (j + 1) 0) := by
      constructor
      · rw [← hmapj j (by omega)]
        exact (extend f).monotone hz.1
      · rw [← hmapj (j + 1) (by omega)]
        exact (extend f).monotone hz.2
    rw [extend_mul_apply, hac' _ hfz, hac _ hz]
    ring
  · show Q.marks.map (extend (g * f)) = S.marks
    calc Q.marks.map (extend (g * f))
        = Q.marks.map (fun z => extend g (extend f z)) := by
          refine List.map_congr_left ?_
          intro x _
          exact extend_mul_apply f g x
      _ = (Q.marks.map (extend f)).map (extend g) := by rw [List.map_map]; rfl
      _ = R.marks.map (extend g) := by rw [hfM']
      _ = S.marks := hgM'

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

lemma isDyadic_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨m', k', rfl⟩ := hy
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k', ?_⟩
  push_cast
  field_simp
  ring

lemma isDyadic_neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨-m, k, by push_cast; ring⟩

lemma isDyadic_zpow_mul {n : ℤ} {x : ℝ} (hx : IsDyadic x) : IsDyadic (2 ^ n * x) := by
  obtain ⟨m, k, rfl⟩ := hx
  by_cases hn : 0 ≤ n
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    refine ⟨m * 2 ^ j, k, ?_⟩
    push_cast
    rw [zpow_natCast]
    ring
  · push_neg at hn
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -(j : ℤ) := ⟨(-n).toNat, by omega⟩
    refine ⟨m, k + j, ?_⟩
    rw [zpow_neg, zpow_natCast]
    push_cast
    field_simp
    ring

/-- Around any point outside a finite set there is a two-sided interval missing the set. -/
lemma exists_gap_around {B : Finset ℝ} {x : ℝ} (hx : x ∉ (B : Set ℝ)) :
    ∃ ε > 0, Set.Ioo (x - ε) (x + ε) ∩ (B : Set ℝ) = ∅ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp B.finite_toSet.isClosed.isOpen_compl x hx
  refine ⟨ε, hε, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_Ioo, Finset.mem_coe, Set.mem_empty_iff_false, iff_false,
    not_and]
  rintro ⟨hz1, hz2⟩ hzB
  exact hball (by rw [Real.ball_eq_Ioo]; exact ⟨hz1, hz2⟩) hzB


/-- **An element of the line model carries dyadic rationals to dyadic rationals.**

This is Cannon–Floyd–Parry's own argument, immediately following their definition: `f(0) = 0`,
so on the first piece `f x = 2 ^ n * x` with dyadic intercept `0`; since the right endpoint of a
piece is dyadic and its image is therefore dyadic, the next piece's intercept is dyadic too; and
so on inductively along the breakpoints.  Note that dyadic intercepts are *derived* here, not
assumed — the definition asks only that breakpoints be dyadic and slopes be powers of two. -/
theorem isDyadic_apply {f : ℝ ≃o ℝ} (hf : IsThompsonLine f) {x : ℝ} (hx : IsDyadic x) :
    IsDyadic (f x) := by
  obtain ⟨hlo, hhi, B, hBd, hB⟩ := hf
  -- adjoin `0`, so that every point of `[0, ∞)` has a breakpoint of the enlarged set below it
  set B' : Finset ℝ := insert 0 B with hB'def
  have hB'd : ∀ b ∈ B', IsDyadic b := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ⟨0, 0, by norm_num⟩
    · exact hBd b hb
  have hzero : (0:ℝ) ∈ B' := Finset.mem_insert_self _ _
  -- induction along the breakpoints, on how many of them lie below the point
  have key : ∀ n : ℕ, ∀ y : ℝ, (B'.filter (fun b => b < y)).card = n → 0 ≤ y →
      IsDyadic y → IsDyadic (f y) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y hcard hy0 hyd
      rcases eq_or_lt_of_le hy0 with hy | hy
      · rw [← hy, hlo 0 le_rfl]; exact ⟨0, 0, by norm_num⟩
      · -- `p` is the last breakpoint strictly below `y`
        have hmem0 : (0:ℝ) ∈ B'.filter (fun b => b < y) := Finset.mem_filter.mpr ⟨hzero, hy⟩
        have hne : (B'.filter (fun b => b < y)).Nonempty := ⟨0, hmem0⟩
        set p := (B'.filter (fun b => b < y)).max' hne with hpdef
        have hpmem : p ∈ B'.filter (fun b => b < y) := Finset.max'_mem _ _
        have hpB' : p ∈ B' := (Finset.mem_filter.mp hpmem).1
        have hpy : p < y := by
          have := (Finset.mem_filter.mp hpmem).2
          simpa using this
        have hp0 : 0 ≤ p := Finset.le_max' _ 0 hmem0
        -- nothing of `B` lies strictly between `p` and `y`
        have hgap : Set.Ioo p y ∩ (B : Set ℝ) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro b ⟨⟨hb1, hb2⟩, hbB⟩
          have hbf : b ∈ B'.filter (fun b => b < y) :=
            Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hbB, by simpa using hb2⟩
          exact absurd (Finset.le_max' _ b hbf) (not_le.mpr hb1)
        obtain ⟨m, c, haff⟩ := hB p y hpy hgap
        -- the induction hypothesis applies at `p`, which has strictly fewer breakpoints below it
        have hsub : B'.filter (fun b => b < p) ⊆ B'.filter (fun b => b < y) := by
          intro b hb
          obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
          exact Finset.mem_filter.mpr ⟨hb1, lt_trans hb2 hpy⟩
        have hssub : B'.filter (fun b => b < p) ⊂ B'.filter (fun b => b < y) :=
          (Finset.ssubset_iff_of_subset hsub).mpr ⟨p, hpmem, by simp⟩
        have hlt : (B'.filter (fun b => b < p)).card < n := by
          rw [← hcard]; exact Finset.card_lt_card hssub
        have hfp : IsDyadic (f p) := ih _ hlt p rfl hp0 (hB'd p hpB')
        -- hence the intercept of this piece is dyadic
        have hcp : f p = 2 ^ m * p + c := haff p ⟨le_rfl, le_of_lt hpy⟩
        have hcd : IsDyadic c := by
          have hc : c = f p + -(2 ^ m * p) := by linarith
          rw [hc]
          exact isDyadic_add hfp (isDyadic_neg (isDyadic_zpow_mul (hB'd p hpB')))
        rw [haff y ⟨le_of_lt hpy, le_rfl⟩]
        exact isDyadic_add (isDyadic_zpow_mul hyd) hcd
  rcases le_or_gt 0 x with hx0 | hx0
  · exact key _ x rfl hx0 hx
  · rw [hlo x (le_of_lt hx0)]; exact hx

theorem isThompsonLine_one : IsThompsonLine (1 : ℝ ≃o ℝ) := by
  refine ⟨fun x _ => rfl, fun x _ => rfl, ∅, by simp, fun x y _ _ => ?_⟩
  exact ⟨0, 0, fun z _ => by norm_num⟩

theorem isThompsonLine_inv {f : ℝ ≃o ℝ} (hf : IsThompsonLine f) : IsThompsonLine f⁻¹ := by
  obtain ⟨h0, h1, B, hBd, hB⟩ := hf
  have hinv : ∀ x : ℝ, (f⁻¹ : ℝ ≃o ℝ) x = f.symm x := fun _ => rfl
  refine ⟨fun x hx => ?_, fun x hx => ?_, B.image f, ?_, fun x y hxy hgap => ?_⟩
  · rw [hinv, f.symm_apply_eq]; exact (h0 x hx).symm
  · rw [hinv, f.symm_apply_eq]; exact (h1 x hx).symm
  · intro b hb
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    exact isDyadic_apply ⟨h0, h1, B, hBd, hB⟩ (hBd b' hb')
  · have hlt : f.symm x < f.symm y := by simpa using hxy
    have hgap' : Set.Ioo (f.symm x) (f.symm y) ∩ (B : Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨⟨hb1, hb2⟩, hbB⟩
      have h1' : x < f b := by simpa using (OrderIso.lt_iff_lt f).mpr hb1
      have h2' : f b < y := by simpa using (OrderIso.lt_iff_lt f).mpr hb2
      rw [Set.eq_empty_iff_forall_notMem] at hgap
      exact hgap (f b) ⟨⟨h1', h2'⟩, by exact_mod_cast Finset.mem_image_of_mem f hbB⟩
    obtain ⟨n, c, haff⟩ := hB _ _ hlt hgap'
    have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
    refine ⟨-n, -(2 ^ (-n) * c), fun w hw => ?_⟩
    have hmem : f.symm w ∈ Set.Icc (f.symm x) (f.symm y) :=
      ⟨(OrderIso.le_iff_le f.symm).mpr hw.1, (OrderIso.le_iff_le f.symm).mpr hw.2⟩
    have hkey : w = 2 ^ n * f.symm w + c := by
      have := haff _ hmem
      rwa [f.apply_symm_apply] at this
    rw [hinv, zpow_neg]
    field_simp
    linarith [hkey]

theorem isThompsonLine_mul {f g : ℝ ≃o ℝ} (hf : IsThompsonLine f) (hg : IsThompsonLine g) :
    IsThompsonLine (f * g) := by
  have hginv := isThompsonLine_inv hg
  obtain ⟨hf0, hf1, Bf, hBfd, hBf⟩ := hf
  obtain ⟨hg0, hg1, Bg, hBgd, hBg⟩ := hg
  have hmul : ∀ x : ℝ, (f * g : ℝ ≃o ℝ) x = f (g x) := fun _ => rfl
  refine ⟨fun x hx => ?_, fun x hx => ?_, Bg ∪ Bf.image (fun b => g.symm b), ?_,
    fun x y hxy hgap => ?_⟩
  · rw [hmul, hg0 x hx, hf0 x hx]
  · rw [hmul, hg1 x hx, hf1 x hx]
  · intro b hb
    rcases Finset.mem_union.mp hb with h | h
    · exact hBgd b h
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp h
      exact isDyadic_apply hginv (hBfd b' hb')
  · rw [Set.eq_empty_iff_forall_notMem] at hgap
    have hgapg : Set.Ioo x y ∩ (Bg : Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨hb1, hb2⟩
      exact hgap b ⟨hb1, by simp [Finset.mem_union, hb2]⟩
    obtain ⟨m, d, haffg⟩ := hBg _ _ hxy hgapg
    have hgxy : g x < g y := by simpa using hxy
    have hgapf : Set.Ioo (g x) (g y) ∩ (Bf : Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨⟨hb1, hb2⟩, hbB⟩
      have h1' : x < g.symm b := by simpa using (OrderIso.lt_iff_lt g.symm).mpr hb1
      have h2' : g.symm b < y := by simpa using (OrderIso.lt_iff_lt g.symm).mpr hb2
      refine hgap (g.symm b) ⟨⟨h1', h2'⟩, ?_⟩
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      exact Or.inr (Finset.mem_image_of_mem _ hbB)
    obtain ⟨n, e, hafff⟩ := hBf _ _ hgxy hgapf
    refine ⟨n + m, 2 ^ n * d + e, fun z hz => ?_⟩
    have hgz : g z ∈ Set.Icc (g x) (g y) :=
      ⟨(OrderIso.le_iff_le g).mpr hz.1, (OrderIso.le_iff_le g).mpr hz.2⟩
    rw [hmul, hafff _ hgz, haffg z hz, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    ring

/-- An order isomorphism of `[0,1]` fixes the left endpoint. -/
lemma coe_apply_zero (f : UI ≃o UI) : (f ⟨0, zero_mem_UI⟩ : ℝ) = 0 := by
  set b : UI := ⟨0, zero_mem_UI⟩ with hb
  have hge : (0:ℝ) ≤ (f b : ℝ) := (f b).2.1
  have hle : (f b : ℝ) ≤ 0 := by
    have h1 : b ≤ f.symm b := by
      show (0:ℝ) ≤ ((f.symm b : UI) : ℝ)
      exact (f.symm b).2.1
    have h2 := (OrderIso.le_iff_le f).mpr h1
    rw [f.apply_symm_apply] at h2
    exact h2
  linarith

/-- An order isomorphism of `[0,1]` fixes the right endpoint. -/
lemma coe_apply_one (f : UI ≃o UI) : (f ⟨1, one_mem_UI⟩ : ℝ) = 1 := by
  set t : UI := ⟨1, one_mem_UI⟩ with ht
  have hle : (f t : ℝ) ≤ 1 := (f t).2.2
  have hge : (1:ℝ) ≤ (f t : ℝ) := by
    have h1 : f.symm t ≤ t := by
      show ((f.symm t : UI) : ℝ) ≤ (1:ℝ)
      exact (f.symm t).2.2
    have h2 := (OrderIso.le_iff_le f).mpr h1
    rw [f.apply_symm_apply] at h2
    exact h2
  linarith

lemma extend_eq_self_of_le_zero (f : UI ≃o UI) {x : ℝ} (hx : x ≤ 0) : extend f x = x := by
  rcases lt_or_eq_of_le hx with h | h
  · exact extendFun_of_notMem f (fun hm => absurd hm.1 (not_le.mpr h))
  · subst h
    rw [extend_apply, extendFun_of_mem f zero_mem_UI, coe_apply_zero f]

lemma extend_eq_self_of_one_le (f : UI ≃o UI) {x : ℝ} (hx : 1 ≤ x) : extend f x = x := by
  rcases lt_or_eq_of_le hx with h | h
  · exact extendFun_of_notMem f (fun hm => absurd hm.2 (not_le.mpr h))
  · subst h
    rw [extend_apply, extendFun_of_mem f one_mem_UI, coe_apply_one f]

lemma extend_coe (f : UI ≃o UI) (z : UI) : extend f (z : ℝ) = (f z : ℝ) := by
  rw [extend_apply, extendFun_of_mem f z.2]

/-- The two models agree on membership: `f` satisfies the textbook condition on `[0,1]` exactly
when its extension by the identity satisfies the line condition.  This is a statement about the
two predicates; that the groups they cut out are isomorphic is `F_mulEquiv_Fline`. -/
theorem isThompsonLine_extend_iff (f : UI ≃o UI) : IsThompsonLine (extend f) ↔ IsThompson f := by
  constructor
  · rintro ⟨-, -, B, hBd, hB⟩
    refine ⟨B, hBd, fun x y hxy hgap => ?_⟩
    obtain ⟨n, c, haff⟩ := hB (x:ℝ) (y:ℝ) hxy hgap
    refine ⟨n, c, fun z hz => ?_⟩
    rw [← extend_coe f z]
    exact haff (z:ℝ) hz
  · rintro ⟨B, hBd, hB⟩
    refine ⟨fun x hx => extend_eq_self_of_le_zero f hx,
      fun x hx => extend_eq_self_of_one_le f hx,
      insert 0 (insert 1 B), ?_, fun x y hxy hgap => ?_⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨0, 0, by norm_num⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨1, 0, by norm_num⟩
      · exact hBd b hb
    · rw [Set.eq_empty_iff_forall_notMem] at hgap
      have h0 : (0:ℝ) ∉ Set.Ioo x y := fun h => hgap 0 ⟨h, by simp⟩
      have h1 : (1:ℝ) ∉ Set.Ioo x y := fun h => hgap 1 ⟨h, by simp⟩
      simp only [Set.mem_Ioo, not_and, not_lt] at h0 h1
      by_cases hx0 : (0:ℝ) ≤ x <;> by_cases hy1 : y ≤ (1:ℝ)
      · -- the interval sits inside `[0,1]`: use the hypothesis on `f`
        have hxm : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx0, le_trans (le_of_lt hxy) hy1⟩
        have hym : y ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hx0 (le_of_lt hxy), hy1⟩
        have hgap' : Set.Ioo (x:ℝ) (y:ℝ) ∩ (B : Set ℝ) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro b hb
          exact hgap b ⟨hb.1, by simp [hb.2]⟩
        obtain ⟨n, c, haff⟩ :=
          hB ⟨x, hxm⟩ ⟨y, hym⟩ hxy hgap'
        refine ⟨n, c, fun z hz => ?_⟩
        have hzm : z ∈ Set.Icc (0:ℝ) 1 := ⟨le_trans hx0 hz.1, le_trans hz.2 hy1⟩
        rw [show z = ((⟨z, hzm⟩ : UI) : ℝ) from rfl, extend_coe f]
        exact haff ⟨z, hzm⟩ hz
      · -- `y > 1`, so `x ≥ 1` and the whole interval is fixed
        have hx1 : (1:ℝ) ≤ x := not_lt.mp (fun hc => absurd (h1 hc) hy1)
        exact ⟨0, 0, fun z hz => by
          rw [extend_eq_self_of_one_le f (le_trans hx1 hz.1)]; norm_num⟩
      · -- `x < 0`, so `y ≤ 0` and the whole interval is fixed
        have hy0 : y ≤ (0:ℝ) := h0 (lt_of_not_ge hx0)
        exact ⟨0, 0, fun z hz => by
          rw [extend_eq_self_of_le_zero f (le_trans hz.2 hy0)]; norm_num⟩
      · exact absurd (h0 (lt_of_not_ge hx0)) (not_le.mpr (lt_trans one_pos (lt_of_not_ge hy1)))

@[simp] lemma extend_one : extend (1 : UI ≃o UI) = 1 := by
  ext x
  by_cases h : x ∈ Set.Icc (0:ℝ) 1
  · rw [extend_apply, extendFun_of_mem _ h]; rfl
  · rw [extend_apply, extendFun_of_notMem _ h]; rfl

lemma extend_mul (f g : UI ≃o UI) : extend (f * g) = extend f * extend g := by
  ext x
  show extend (f * g) x = extend f (extend g x)
  by_cases h : x ∈ Set.Icc (0:ℝ) 1
  · rw [extend_apply, extend_apply, extend_apply, extendFun_of_mem _ h,
      extendFun_of_mem g h, extendFun_of_mem f (g ⟨x, h⟩).2]
    rfl
  · rw [extend_apply, extend_apply, extend_apply, extendFun_of_notMem _ h,
      extendFun_of_notMem g h, extendFun_of_notMem f h]

/-- Extension by the identity, as a group homomorphism. -/
noncomputable def extendHom : (UI ≃o UI) →* (ℝ ≃o ℝ) where
  toFun := extend
  map_one' := extend_one
  map_mul' := extend_mul

lemma extend_injective : Function.Injective extend := by
  intro f g h
  ext z
  have hz : extend f (z : ℝ) = extend g (z : ℝ) := congrArg (fun L : ℝ ≃o ℝ => L (z : ℝ)) h
  rw [extend_coe, extend_coe] at hz
  exact hz

lemma extend_restrict (L : ℝ ≃o ℝ) (hlo : ∀ x ≤ (0:ℝ), L x = x)
    (hhi : ∀ x, (1:ℝ) ≤ x → L x = x) : extend (restrict L hlo hhi) = L := by
  ext x
  by_cases h : x ∈ Set.Icc (0:ℝ) 1
  · rw [extend_apply, extendFun_of_mem _ h]; rfl
  · rw [extend_apply, extendFun_of_notMem _ h]
    rcases not_and_or.mp h with hc | hc
    · exact (hlo x (le_of_lt (lt_of_not_ge hc))).symm
    · exact (hhi x (le_of_lt (lt_of_not_ge hc))).symm





/-- `A` lies in the line model of `F`. -/
theorem isThompsonLine_lineA : IsThompsonLine lineA := by
  refine ⟨fun x hx => aFun_of_le_zero hx, fun x hx => aFun_of_one_le hx,
    {0, 1/2, 3/4, 1}, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨0, 0, by norm_num⟩
    · exact ⟨1, 1, by norm_num⟩
    · exact ⟨3, 2, by norm_num⟩
    · exact ⟨1, 0, by norm_num⟩
  · intro x y hxy hgap
    rw [Set.eq_empty_iff_forall_notMem] at hgap
    have hb : ∀ b : ℝ, b ∈ ({0, 1/2, 3/4, 1} : Finset ℝ) → b ≤ x ∨ y ≤ b := by
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
            rw [lineA_apply, aFun_of_one_le (by linarith [hz.1])]; norm_num
          · refine ⟨1, -1, fun z hz => ?_⟩
            rw [lineA_apply, aFun_of_mem3 (by linarith [hz.1]) (by linarith [hz.2]), zpow_one]
            ring
        · refine ⟨0, -(1/4), fun z hz => ?_⟩
          rw [lineA_apply, aFun_of_mem2 (by linarith [hz.1]) (by linarith [hz.2]), zpow_zero]
          ring
      · refine ⟨-1, 0, fun z hz => ?_⟩
        rw [lineA_apply, aFun_of_mem1 (by linarith [hz.1]) (by linarith [hz.2]),
          zpow_neg, zpow_one]
        ring
    · refine ⟨0, 0, fun z hz => ?_⟩
      rw [lineA_apply, aFun_of_le_zero (by linarith [hz.2])]; norm_num


end CannonFloydParry

namespace CannonFloydParry

/-- The midpoint of the standard dyadic interval `[c/2^k, (c+1)/2^k]`, written so that it is
visibly a dyadic rational of level `k+1`. -/
noncomputable def md (c k : ℕ) : ℝ := (2 * (c : ℝ) + 1) / 2 ^ (k + 1)

lemma md_eq (c k : ℕ) :
    md c k = ((c : ℝ) / 2 ^ k + ((c : ℝ) + 1) / 2 ^ k) / 2 := by
  have h : (2 : ℝ) ^ k ≠ 0 := by positivity
  rw [md]
  field_simp
  ring

lemma lt_md (c k : ℕ) : (c : ℝ) / 2 ^ k < md c k := by
  have h : (0 : ℝ) < 2 ^ k := by positivity
  have e : ((c : ℝ) + 1) / 2 ^ k - (c : ℝ) / 2 ^ k = 1 / 2 ^ k := by field_simp; ring
  have hp : (0 : ℝ) < 1 / 2 ^ k := by positivity
  rw [md_eq]
  linarith

lemma md_lt (c k : ℕ) : md c k < ((c : ℝ) + 1) / 2 ^ k := by
  have h : (0 : ℝ) < 2 ^ k := by positivity
  have e : ((c : ℝ) + 1) / 2 ^ k - (c : ℝ) / 2 ^ k = 1 / 2 ^ k := by field_simp; ring
  have hp : (0 : ℝ) < 1 / 2 ^ k := by positivity
  rw [md_eq]
  linarith

/-- A standard dyadic interval is a genuine interval: its left endpoint is below its right one. -/
lemma sdi_lt {x y : ℝ} (h : IsStandardDyadicInterval x y) : x < y := by
  obtain ⟨a, n, -, rfl, rfl⟩ := h
  have hp : (0 : ℝ) < 1 / 2 ^ n := by positivity
  have e : ((a : ℝ) + 1) / 2 ^ n - (a : ℝ) / 2 ^ n = 1 / 2 ^ n := by field_simp; ring
  linarith

/-- **No straddling.** A standard dyadic interval sitting inside `[c/2^k, (c+1)/2^k]` cannot
contain the midpoint `md c k` in its interior unless it *is* `[c/2^k, (c+1)/2^k]`. -/
lemma no_straddle {x y : ℝ} (h : IsStandardDyadicInterval x y) {c k : ℕ}
    (hlo : (c : ℝ) / 2 ^ k ≤ x) (hhi : y ≤ ((c : ℝ) + 1) / 2 ^ k)
    (h1 : x < md c k) (h2 : md c k < y) :
    x = (c : ℝ) / 2 ^ k ∧ y = ((c : ℝ) + 1) / 2 ^ k := by
  obtain ⟨a, n, han, rfl, rfl⟩ := h
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  -- the interval is no longer than the ambient one, so `k ≤ n`
  have hd : (1 : ℝ) / 2 ^ n ≤ 1 / 2 ^ k := by
    have e1 : ((a : ℝ) + 1) / 2 ^ n - (a : ℝ) / 2 ^ n = 1 / 2 ^ n := by field_simp; ring
    have e2 : ((c : ℝ) + 1) / 2 ^ k - (c : ℝ) / 2 ^ k = 1 / 2 ^ k := by field_simp; ring
    linarith
  have hkn : k ≤ n := by
    rcases Nat.lt_or_ge n k with hcon | hle
    · exfalso
      have hnat : (2 : ℕ) ^ n < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hcon
      have hlt : (2 : ℝ) ^ n < 2 ^ k := by exact_mod_cast hnat
      have : (1 : ℝ) / 2 ^ k < 1 / 2 ^ n := one_div_lt_one_div_of_lt h2n hlt
      linarith
    · exact hle
  rcases eq_or_lt_of_le hkn with rfl | hlt
  · -- same level: the numerators must agree
    have hca : (c : ℝ) ≤ (a : ℝ) := by
      have := (div_le_div_iff_of_pos_right h2k).mp hlo
      exact this
    have hac : (a : ℝ) + 1 ≤ (c : ℝ) + 1 := (div_le_div_iff_of_pos_right h2k).mp hhi
    have : (a : ℝ) = (c : ℝ) := le_antisymm (by linarith) hca
    rw [this]
    exact ⟨rfl, rfl⟩
  · -- strictly deeper level: the midpoint is itself a multiple of `1/2^n`, so it cannot lie
    -- strictly between two consecutive multiples
    exfalso
    obtain ⟨d, hd'⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
    set M : ℕ := (2 * c + 1) * 2 ^ d with hM
    have hmd : md c k = (M : ℝ) / 2 ^ n := by
      have hk : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
      have hdd : (2 : ℝ) ^ d ≠ 0 := by positivity
      have hsplit : (2 : ℝ) ^ n = 2 ^ (k + 1) * 2 ^ d := by rw [hd', pow_add]
      rw [md, hM, hsplit]
      push_cast
      field_simp
    rw [hmd] at h1 h2
    have hlt1 : (a : ℝ) < (M : ℝ) := (div_lt_div_iff_of_pos_right h2n).mp h1
    have hlt2 : (M : ℝ) < (a : ℝ) + 1 := (div_lt_div_iff_of_pos_right h2n).mp h2
    have n1 : a < M := by exact_mod_cast hlt1
    have n2 : M < a + 1 := by
      have : (M : ℝ) < ((a + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    omega

/-- In a chain of standard dyadic intervals with at least two entries, the head is strictly
below the last entry. -/
lemma chain_lt_getLast : ∀ (l : List ℝ) (x v : ℝ),
    List.IsChain IsStandardDyadicInterval (x :: l) → (x :: l).getLast? = some v → l ≠ [] →
    x < v := by
  intro l
  induction l with
  | nil => intro x v _ _ h; exact absurd rfl h
  | cons y t ih =>
      intro x v hch hlast _
      have hxy : IsStandardDyadicInterval x y :=
        (List.isChain_cons.mp hch).1 y (by simp)
      have hch' : List.IsChain IsStandardDyadicInterval (y :: t) := (List.isChain_cons.mp hch).2
      have hlast' : (y :: t).getLast? = some v := by
        rw [List.getLast?_cons_cons] at hlast; exact hlast
      rcases eq_or_ne t [] with rfl | ht
      · have : v = y := by simpa using hlast'.symm
        subst this; exact sdi_lt hxy
      · exact lt_trans (sdi_lt hxy) (ih y v hch' hlast' ht)

/-- **The midpoint is a mark.** A chain of standard dyadic intervals running from `c/2^k` up to
`(c+1)/2^k` must contain the midpoint, unless it is the two-element chain consisting of the
ambient interval itself. -/
lemma md_mem (c k : ℕ) : ∀ (xs : List ℝ), List.IsChain IsStandardDyadicInterval xs →
    ∀ u, xs.head? = some u → (c : ℝ) / 2 ^ k ≤ u →
    xs.getLast? = some (((c : ℝ) + 1) / 2 ^ k) → u < md c k →
    md c k ∈ xs ∨ (u = (c : ℝ) / 2 ^ k ∧ xs.length = 2) := by
  intro xs
  induction xs with
  | nil => intro _ u hh; simp at hh
  | cons x rest ih =>
      intro hch u hh hlo hlast hu
      have hux : u = x := by simpa using hh.symm
      subst hux
      cases rest with
      | nil =>
          exfalso
          have : u = ((c : ℝ) + 1) / 2 ^ k := by simpa using hlast
          have := md_lt c k
          linarith
      | cons y t =>
          have hxy : IsStandardDyadicInterval u y :=
            (List.isChain_cons.mp hch).1 y (by simp)
          have hch' : List.IsChain IsStandardDyadicInterval (y :: t) := (List.isChain_cons.mp hch).2
          have hlast' : (y :: t).getLast? = some (((c : ℝ) + 1) / 2 ^ k) := by
            rw [List.getLast?_cons_cons] at hlast; exact hlast
          have hy_le : y ≤ ((c : ℝ) + 1) / 2 ^ k := by
            rcases eq_or_ne t [] with rfl | ht
            · have : y = ((c : ℝ) + 1) / 2 ^ k := by simpa using hlast'
              exact le_of_eq this
            · exact le_of_lt (chain_lt_getLast t y _ hch' hlast' ht)
          rcases lt_trichotomy (md c k) y with hmy | hmy | hmy
          · -- straddle: forced to be the whole interval, hence a two-element chain
            obtain ⟨hx, hy⟩ := no_straddle hxy hlo hy_le hu hmy
            refine Or.inr ⟨hx, ?_⟩
            have ht : t = [] := by
              by_contra ht
              have := chain_lt_getLast t y _ hch' hlast' ht
              rw [hy] at this
              exact absurd this (lt_irrefl _)
            subst ht
            simp
          · exact Or.inl (by simp [hmy])
          · have hlo' : (c : ℝ) / 2 ^ k ≤ y := le_of_lt (lt_of_le_of_lt hlo (sdi_lt hxy))
            rcases ih hch' y (by simp) hlo' hlast' hmy with hmem | ⟨hyc, -⟩
            · exact Or.inl (by simp [hmem])
            · exfalso
              have := sdi_lt hxy
              rw [hyc] at this
              linarith

/-- **Existence.** Every chain of standard dyadic intervals from `c/2^k` to `(c+1)/2^k` is the
mark list of a tree placed on that interval. Strong induction on the length: the chain is split
at the midpoint, and each half is a chain one level deeper. -/
lemma exists_tree : ∀ (N : ℕ) (xs : List ℝ), xs.length ≤ N →
    List.IsChain IsStandardDyadicInterval xs →
    ∀ c k : ℕ, c + 1 ≤ 2 ^ k →
    xs.head? = some ((c : ℝ) / 2 ^ k) → xs.getLast? = some (((c : ℝ) + 1) / 2 ^ k) →
    ∃ t : TTree, xs = (c : ℝ) / 2 ^ k ::
      (t.marksAux ((c : ℝ) / 2 ^ k) (((c : ℝ) + 1) / 2 ^ k) ++ [((c : ℝ) + 1) / 2 ^ k]) := by
  intro N
  induction N with
  | zero =>
      intro xs hlen _ c k _ hh _
      exfalso
      have : xs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst this
      simp at hh
  | succ N ih =>
      intro xs hlen hch c k hc hh hlast
      -- the two halves live at level `k+1`
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have hlow : ((2 * c : ℕ) : ℝ) / 2 ^ (k + 1) = (c : ℝ) / 2 ^ k := by
        have h : (2 : ℝ) ^ k ≠ 0 := by positivity
        push_cast; field_simp; ring
      have hmidL : (((2 * c : ℕ) : ℝ) + 1) / 2 ^ (k + 1) = md c k := by
        rw [md]; push_cast; ring
      have hmidR : ((2 * c + 1 : ℕ) : ℝ) / 2 ^ (k + 1) = md c k := by
        rw [md]; push_cast; ring
      have htop : (((2 * c + 1 : ℕ) : ℝ) + 1) / 2 ^ (k + 1) = ((c : ℝ) + 1) / 2 ^ k := by
        have h : (2 : ℝ) ^ k ≠ 0 := by positivity
        push_cast; field_simp; ring
      -- length two is the leaf case
      rcases eq_or_ne xs.length 2 with hlen2 | hlen2
      · match xs, hlen2 with
        | [p, q], _ =>
            refine ⟨TTree.leaf, ?_⟩
            have hp : p = (c : ℝ) / 2 ^ k := by simpa using hh
            have hq : q = ((c : ℝ) + 1) / 2 ^ k := by simpa using hlast
            subst hp; subst hq
            simp [TTree.marksAux]
      · -- otherwise the midpoint is one of the marks
        have hmem : md c k ∈ xs := by
          rcases md_mem c k xs hch _ hh le_rfl hlast (lt_md c k) with h | ⟨-, h2⟩
          · exact h
          · exact absurd h2 hlen2
        obtain ⟨xs₁, xs₂, rfl⟩ := List.append_of_mem hmem
        have hne1 : xs₁ ≠ [] := by
          intro h; subst h
          simp at hh
          have := lt_md c k
          rw [← hh] at this
          exact absurd this (lt_irrefl _)
        have hne2 : xs₂ ≠ [] := by
          intro h; subst h
          rw [List.getLast?_append_of_ne_nil _ (by simp)] at hlast
          simp at hlast
          have := md_lt c k
          rw [hlast] at this
          exact absurd this (lt_irrefl _)
        -- the two halves, as lists
        have hsplit : xs₁ ++ md c k :: xs₂ = (xs₁ ++ [md c k]) ++ xs₂ := by simp
        have hchL : List.IsChain IsStandardDyadicInterval (xs₁ ++ [md c k]) := by
          refine hch.prefix ⟨xs₂, ?_⟩
          simp
        have hchR : List.IsChain IsStandardDyadicInterval (md c k :: xs₂) :=
          hch.right_of_append
        -- heads and last entries of the two halves
        have hhL : (xs₁ ++ [md c k]).head? = some (((2 * c : ℕ) : ℝ) / 2 ^ (k + 1)) := by
          rw [hlow]
          rw [List.head?_append_of_ne_nil _ hne1]
          rw [List.head?_append_of_ne_nil _ hne1] at hh
          exact hh
        have hlastL : (xs₁ ++ [md c k]).getLast? = some ((((2 * c : ℕ) : ℝ) + 1) / 2 ^ (k + 1)) := by
          rw [hmidL, List.getLast?_append_of_ne_nil _ (by simp)]
          simp
        have hhR : (md c k :: xs₂).head? = some (((2 * c + 1 : ℕ) : ℝ) / 2 ^ (k + 1)) := by
          rw [hmidR]; simp
        have hlastR :
            (md c k :: xs₂).getLast? = some ((((2 * c + 1 : ℕ) : ℝ) + 1) / 2 ^ (k + 1)) := by
          rw [htop]
          rw [List.getLast?_cons_of_ne_nil hne2]
          rw [hsplit, List.getLast?_append_of_ne_nil _ hne2] at hlast
          exact hlast
        -- lengths shrink
        have hl1 : 1 ≤ xs₁.length := List.length_pos_iff.mpr hne1
        have hl2 : 1 ≤ xs₂.length := List.length_pos_iff.mpr hne2
        have hlenAll : xs₁.length + 1 + xs₂.length ≤ N + 1 := by
          simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlen
        have hlenL : (xs₁ ++ [md c k]).length ≤ N := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        have hlenR : (md c k :: xs₂).length ≤ N := by
          simp only [List.length_cons]
          omega
        obtain ⟨l, hlEq⟩ := ih _ hlenL hchL (2 * c) (k + 1) (by omega) hhL hlastL
        obtain ⟨r, hrEq⟩ := ih _ hlenR hchR (2 * c + 1) (k + 1) (by omega) hhR hlastR
        rw [hlow, hmidL] at hlEq
        rw [hmidR, htop] at hrEq
        -- read the two halves off and reassemble
        have hxs1 : xs₁ = (c : ℝ) / 2 ^ k :: l.marksAux ((c : ℝ) / 2 ^ k) (md c k) := by
          have : xs₁ ++ [md c k] =
              ((c : ℝ) / 2 ^ k :: l.marksAux ((c : ℝ) / 2 ^ k) (md c k)) ++ [md c k] := by
            rw [hlEq]; simp
          exact List.append_cancel_right this
        have hxs2 : xs₂ = r.marksAux (md c k) (((c : ℝ) + 1) / 2 ^ k) ++ [((c : ℝ) + 1) / 2 ^ k] := by
          have := hrEq
          simpa using this
        refine ⟨TTree.node l r, ?_⟩
        rw [hxs1, hxs2, TTree.marksAux, ← md_eq]
        simp [List.append_assoc]

/-- **Uniqueness.** The mark list of a tree on a nondegenerate interval determines the tree. -/
lemma marksAux_inj : ∀ (t t' : TTree) (a b : ℝ), a < b →
    t.marksAux a b = t'.marksAux a b → t = t' := by
  intro t
  induction t with
  | leaf =>
      intro t' a b hab h
      cases t' with
      | leaf => rfl
      | node l r => exfalso; rw [TTree.marksAux, TTree.marksAux] at h; simp at h
  | node l r ihl ihr =>
      intro t' a b hab h
      cases t' with
      | leaf => exfalso; rw [TTree.marksAux, TTree.marksAux] at h; simp at h
      | node l' r' =>
          have hm1 : a < (a + b) / 2 := by linarith
          have hm2 : (a + b) / 2 < b := by linarith
          rw [TTree.marksAux, TTree.marksAux] at h
          set m : ℝ := (a + b) / 2 with hmdef
          -- keep only the entries below the midpoint: that is exactly the left subtree's list
          have hfl : ∀ u : TTree,
              (u.marksAux a m).filter (fun x => decide (x < m)) = u.marksAux a m := by
            intro u
            refine List.filter_eq_self.mpr ?_
            intro x hx
            simpa using (marksAux_mem_Ioo u a m hm1 x hx).2
          have hfr : ∀ u : TTree,
              (m :: u.marksAux m b).filter (fun x => decide (x < m)) = [] := by
            intro u
            refine List.filter_eq_nil_iff.mpr ?_
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · simp
            · have := (marksAux_mem_Ioo u m b hm2 x hx).1
              simp only [decide_eq_true_eq]
              linarith
          have hfilt := congrArg (fun z : List ℝ => z.filter (fun x => decide (x < m))) h
          simp only [List.filter_append, hfl, hfr, List.append_nil] at hfilt
          have hll : l = l' := ihl l' a m hm1 hfilt
          subst hll
          have htail : m :: r.marksAux m b = m :: r'.marksAux m b :=
            List.append_cancel_left h
          have : r.marksAux m b = r'.marksAux m b := by
            simpa using htail
          rw [ihr r' m b hm2 this]

lemma marks_inj {t t' : TTree} (h : t.marks = t'.marks) : t = t' := by
  rw [TTree.marks, TTree.marks] at h
  have h1 : t.marksAux 0 1 ++ [(1 : ℝ)] = t'.marksAux 0 1 ++ [(1 : ℝ)] := by
    simpa using h
  exact marksAux_inj t t' 0 1 (by norm_num) (List.append_cancel_right h1)

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

lemma exponents_getD_last_pair : ∀ (t : TTree), 2 ≤ t.leafCount →
    t.exponents.getD (t.leafCount - 2) 0 = 0 := by
  intro t
  induction t with
  | leaf => intro h; rw [TTree.leafCount] at h; omega
  | node l r ihl ihr =>
      intro _
      have hm := one_le_leafCount l
      have hp := one_le_leafCount r
      have hlenL : (l.leftRuns).length = l.leafCount := leftRuns_length l
      rw [TTree.exponents]
      rcases Nat.lt_or_ge r.leafCount 2 with hp2 | hp2
      · -- `r` is a single leaf: the index falls at the last entry of the left block
        rw [show (TTree.node l r).leafCount - 2 = l.leafCount - 1 by rw [TTree.leafCount]; omega,
          List.getD_append _ _ _ _ (by rw [hlenL]; omega)]
        exact leftRuns_getD_last l
      · -- `r` has at least two leaves: recurse into it
        rw [show (TTree.node l r).leafCount - 2 = l.leafCount + (r.leafCount - 2) by
            rw [TTree.leafCount]; omega,
          List.getD_append_right _ _ _ _ (by rw [hlenL]; omega), hlenL]
        simpa using ihr hp2

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

/-! ### Small tools -/

/-- A uniform bound over a finite set of eventually-true properties. -/
lemma finset_uniform (S : Finset ℝ) (P : ℝ → ℕ → Prop)
    (h : ∀ b ∈ S, ∃ K : ℕ, ∀ M, K ≤ M → P b M) :
    ∃ K : ℕ, ∀ b ∈ S, ∀ M, K ≤ M → P b M := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, fun b hb => absurd hb (Finset.notMem_empty b)⟩
  | insert a s _ ih =>
      obtain ⟨Ka, hKa⟩ := h a (Finset.mem_insert_self a s)
      obtain ⟨Ks, hKs⟩ := ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
      refine ⟨max Ka Ks, fun b hb M hM => ?_⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hKa M (le_trans (le_max_left _ _) hM)
      · exact hKs b hb M (le_trans (le_max_right _ _) hM)

lemma isDyadic_den' {v : ℝ} (h : IsDyadic v) :
    ∃ K : ℕ, ∀ M, K ≤ M → ∃ a : ℤ, v = (a : ℝ) / 2 ^ M := by
  obtain ⟨m, k, rfl⟩ := h
  refine ⟨k, fun M hM => ⟨m * 2 ^ (M - k), ?_⟩⟩
  have hk : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  have hd : ((2 : ℝ) ^ (M - k)) ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ M = 2 ^ k * 2 ^ (M - k) := by
    rw [← pow_add]; congr 1; omega
  rw [h2]
  push_cast
  field_simp

lemma getD_range_map {g : ℕ → ℝ} {n k : ℕ} (hk : k < n) :
    ((List.range n).map g).getD k 0 = g k := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]

lemma head?_eq_getD {l : List ℝ} (h : l ≠ []) : l.head? = some (l.getD 0 0) := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

lemma getLast?_eq_getD : ∀ (l : List ℝ), l ≠ [] →
    l.getLast? = some (l.getD (l.length - 1) 0) := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
      intro _
      cases t with
      | nil => rfl
      | cons b t' =>
          rw [List.getLast?_cons_cons, ih (by simp)]
          show some ((b :: t').getD (t'.length) 0) = some ((a :: b :: t').getD (t'.length + 1) 0)
          rw [List.getD_cons_succ]

lemma two_zpow_div_pow {e : ℤ} {p q : ℕ} (hq : (q : ℤ) = p - e) :
    (2 : ℝ) ^ e / 2 ^ p = 1 / 2 ^ q := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  rw [← zpow_natCast (2 : ℝ) p, ← zpow_sub₀ h2, ← zpow_natCast (2 : ℝ) q, hq, one_div,
    ← zpow_neg, neg_sub]

/-- The tree whose marks are a given standard dyadic partition (existence half of
`existsUnique_tree_marks_eq`). -/
lemma exists_tree_marks {xs : List ℝ} (h : IsStandardDyadicPartition xs) :
    ∃ t : TTree, t.marks = xs := by
  obtain ⟨hh, hl, hc⟩ := h
  have hh' : xs.head? = some ((0 : ℕ) / (2 : ℝ) ^ (0 : ℕ)) := by norm_num [hh]
  have hl' : xs.getLast? = some ((((0 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (0 : ℕ)) := by norm_num [hl]
  obtain ⟨t, ht⟩ := exists_tree xs.length xs le_rfl hc 0 0 (by norm_num) hh' hl'
  refine ⟨t, ?_⟩
  show (0 : ℝ) :: (t.marksAux 0 1 ++ [1]) = xs
  rw [ht]
  norm_num

/-! ### One piece of the uniform partition -/

/-- On a piece `[k/2^p, (k+1)/2^p]` of the uniform partition with `p = 2K`, where `K` bounds the
dyadic denominators of the breakpoints and of their images: `f` is affine on the piece, and the
image of the piece is a standard dyadic interval. -/
lemma piece_spec {f : UI ≃o UI} {B' : Finset ℝ}
    (hB'01 : ∀ b ∈ B', b ∈ Set.Icc (0 : ℝ) 1)
    (hform : ∀ u v : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → v ∈ Set.Icc (0 : ℝ) 1 → u < v →
      Set.Ioo u v ∩ (B' : Set ℝ) = ∅ →
      ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc u v, extend f z = 2 ^ n * z + c)
    (hrange : ∀ z ∈ Set.Icc (0 : ℝ) 1, extend f z ∈ Set.Icc (0 : ℝ) 1)
    (K : ℕ)
    (hK : ∀ b ∈ insert (0 : ℝ) (insert 1 B'), ∀ M, K ≤ M →
      (∃ a : ℤ, b = (a : ℝ) / 2 ^ M) ∧ (∃ a : ℤ, extend f b = (a : ℝ) / 2 ^ M))
    (k : ℕ) (hk : k < 2 ^ (2 * K)) :
    (∃ (a c : ℝ), ∀ z ∈ Set.Icc ((k : ℝ) / 2 ^ (2 * K)) (((k : ℝ) + 1) / 2 ^ (2 * K)),
      extend f z = a * z + c) ∧
    IsStandardDyadicInterval (extend f ((k : ℝ) / 2 ^ (2 * K)))
      (extend f (((k : ℝ) + 1) / 2 ^ (2 * K))) := by
  classical
  set p := 2 * K with hp
  have hpos : (0 : ℝ) < 2 ^ p := by positivity
  set xk : ℝ := (k : ℝ) / 2 ^ p with hxk
  set xk1 : ℝ := ((k : ℝ) + 1) / 2 ^ p with hxk1
  have hk' : (k : ℝ) + 1 ≤ 2 ^ p := by exact_mod_cast hk
  have hxk0 : 0 ≤ xk := by positivity
  have hxklt : xk < xk1 := by
    rw [hxk, hxk1, div_lt_div_iff_of_pos_right hpos]; linarith
  have hxk1le : xk1 ≤ 1 := by
    rw [hxk1, div_le_one hpos]; exact hk'
  have hxk_lt1 : xk < 1 := lt_of_lt_of_le hxklt hxk1le
  -- the nearest breakpoint at or below the piece
  set S₀ : Finset ℝ := (insert (0 : ℝ) B').filter (fun b => b ≤ xk) with hS₀
  have hS₀ne : S₀.Nonempty := ⟨0, by simp [hS₀, hxk0]⟩
  set b : ℝ := S₀.max' hS₀ne with hb
  have hb_mem : b ∈ S₀ := Finset.max'_mem _ _
  have hb_le : b ≤ xk := (Finset.mem_filter.mp hb_mem).2
  have hb_in : b ∈ insert (0 : ℝ) B' := (Finset.mem_filter.mp hb_mem).1
  have hb01 : b ∈ Set.Icc (0 : ℝ) 1 := by
    rcases Finset.mem_insert.mp hb_in with h0 | hb'
    · rw [h0]; exact ⟨le_refl _, by norm_num⟩
    · exact hB'01 b hb'
  -- the nearest breakpoint strictly above it
  set S₁ : Finset ℝ := (insert (1 : ℝ) B').filter (fun c => b < c) with hS₁
  have hS₁ne : S₁.Nonempty := ⟨1, by simp [hS₁]; linarith⟩
  set bp : ℝ := S₁.min' hS₁ne with hbp
  have hbp_mem : bp ∈ S₁ := Finset.min'_mem _ _
  have hbp_gt : b < bp := (Finset.mem_filter.mp hbp_mem).2
  have hbp_in : bp ∈ insert (1 : ℝ) B' := (Finset.mem_filter.mp hbp_mem).1
  have hbp01 : bp ∈ Set.Icc (0 : ℝ) 1 := by
    rcases Finset.mem_insert.mp hbp_in with h1 | hbp'
    · rw [h1]; exact ⟨by norm_num, le_refl _⟩
    · exact hB'01 bp hbp'
  -- no breakpoint strictly between them
  have hgap : Set.Ioo b bp ∩ (B' : Set ℝ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro c ⟨hc, hcB⟩
    have hcS₁ : c ∈ S₁ := by
      simp only [hS₁, Finset.mem_filter, Finset.mem_insert]
      exact ⟨Or.inr hcB, hc.1⟩
    have := Finset.min'_le S₁ c hcS₁
    linarith [hc.2]
  obtain ⟨e, c₀, hform'⟩ := hform b bp hb01 hbp01 hbp_gt hgap
  -- the piece lies inside the gap
  have hbp_gt_xk : xk < bp := by
    by_contra hcon
    push_neg at hcon
    have hbp_ne1 : bp ≠ 1 := by intro h1; rw [h1] at hcon; linarith
    have hbpB : bp ∈ B' := by
      rcases Finset.mem_insert.mp hbp_in with h1 | h
      · exact absurd h1 hbp_ne1
      · exact h
    have hbpS₀ : bp ∈ S₀ := by
      simp only [hS₀, Finset.mem_filter, Finset.mem_insert]
      exact ⟨Or.inr hbpB, hcon⟩
    have := Finset.le_max' S₀ bp hbpS₀
    linarith
  have hKp : K ≤ p := by omega
  have hbp_in' : bp ∈ insert (0 : ℝ) (insert 1 B') := by
    rcases Finset.mem_insert.mp hbp_in with h1 | h
    · rw [h1]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
  have hb_in' : b ∈ insert (0 : ℝ) (insert 1 B') := by
    rcases Finset.mem_insert.mp hb_in with h0 | h
    · rw [h0]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
  obtain ⟨⟨abp, habp⟩, -⟩ := hK bp hbp_in' p hKp
  have hxk1_le_bp : xk1 ≤ bp := by
    rw [habp] at hbp_gt_xk ⊢
    rw [hxk, div_lt_div_iff_of_pos_right hpos] at hbp_gt_xk
    rw [hxk1, div_le_div_iff_of_pos_right hpos]
    have : (k : ℤ) < abp := by exact_mod_cast hbp_gt_xk
    have : (k : ℤ) + 1 ≤ abp := this
    exact_mod_cast this
  have hsub : ∀ z ∈ Set.Icc xk xk1, z ∈ Set.Icc b bp := fun z hz =>
    ⟨le_trans hb_le hz.1, le_trans hz.2 hxk1_le_bp⟩
  refine ⟨⟨2 ^ e, c₀, fun z hz => hform' z (hsub z hz)⟩, ?_⟩
  -- the values at the two ends of the piece
  have hy := hform' xk (hsub xk ⟨le_refl _, le_of_lt hxklt⟩)
  have hy1 := hform' xk1 (hsub xk1 ⟨le_of_lt hxklt, le_refl _⟩)
  have hfb := hform' b ⟨le_refl _, le_of_lt hbp_gt⟩
  have hfbp := hform' bp ⟨le_of_lt hbp_gt, le_refl _⟩
  -- dyadic data for `b`, `bp`, `f b` at level `K` and at level `p`
  obtain ⟨⟨β, hβ⟩, ⟨γ, hγ⟩⟩ := hK b hb_in' K le_rfl
  obtain ⟨⟨βp, hβp⟩, -⟩ := hK b hb_in' p hKp
  obtain ⟨⟨β', hβ'⟩, -⟩ := hK bp hbp_in' K le_rfl
  -- the slope exponent is at most `K`: the gap is at least `2^{-K}` long and maps into `[0,1]`
  have hKpos : (0 : ℝ) < 2 ^ K := by positivity
  have hgaplen : (1 : ℝ) / 2 ^ K ≤ bp - b := by
    rw [hβ, hβ'] at hbp_gt ⊢
    rw [div_lt_div_iff_of_pos_right hKpos] at hbp_gt
    have h1 : β + 1 ≤ β' := by exact_mod_cast hbp_gt
    have h2 : (β : ℝ) + 1 ≤ β' := by exact_mod_cast h1
    rw [← sub_div, div_le_div_iff_of_pos_right hKpos]
    linarith
  have hfb0 : 0 ≤ extend f b := (hrange b hb01).1
  have hfbp1 : extend f bp ≤ 1 := (hrange bp hbp01).2
  have hslope : (2 : ℝ) ^ e * (bp - b) ≤ 1 := by
    have : extend f bp - extend f b = 2 ^ e * (bp - b) := by rw [hfbp, hfb]; ring
    linarith
  have heK : e ≤ (K : ℤ) := by
    by_contra hcon
    push_neg at hcon
    have h1 : (2 : ℝ) ^ ((K : ℤ) + 1) ≤ 2 ^ e :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ ((K : ℤ) + 1) = 2 * 2 ^ K := by
      rw [zpow_add_one₀ (by norm_num), zpow_natCast]; ring
    have h3 : (2 : ℝ) ^ e * (bp - b) ≥ 2 * 2 ^ K * (1 / 2 ^ K) := by
      rw [← h2]
      exact mul_le_mul h1 hgaplen (by positivity) (by positivity)
    have h4 : (2 : ℝ) * 2 ^ K * (1 / 2 ^ K) = 2 := by field_simp
    linarith
  -- the level of the image piece
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = (p : ℤ) - e :=
    ⟨((p : ℤ) - e).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hKq : K ≤ q := by omega
  have hqpos : (0 : ℝ) < 2 ^ q := by positivity
  have hzp : (2 : ℝ) ^ e / 2 ^ p = 1 / 2 ^ q := two_zpow_div_pow hq
  have h2q : (2 : ℝ) ^ q = 2 ^ K * 2 ^ (q - K) := by
    rw [← pow_add]; congr 1; omega
  -- the numerator of the left endpoint of the image piece
  set m : ℤ := (k : ℤ) - βp + γ * 2 ^ (q - K) with hm
  have hy_eq : extend f xk = (m : ℝ) / 2 ^ q := by
    have hc₀ : c₀ = extend f b - 2 ^ e * b := by linarith [hfb]
    rw [hy, hc₀, hγ, hβp, hxk, hm]
    push_cast
    have e1 : (2 : ℝ) ^ e * ((k : ℝ) / 2 ^ p) = (k : ℝ) * (1 / 2 ^ q) := by
      rw [← hzp]; ring
    have e2 : (2 : ℝ) ^ e * ((βp : ℝ) / 2 ^ p) = (βp : ℝ) * (1 / 2 ^ q) := by
      rw [← hzp]; ring
    have e3 : (γ : ℝ) / 2 ^ K = (γ : ℝ) * 2 ^ (q - K) / 2 ^ q := by
      rw [h2q]; field_simp
    rw [e1, e2, e3]
    field_simp
    ring
  have hy1_eq : extend f xk1 = ((m : ℝ) + 1) / 2 ^ q := by
    have hd : extend f xk1 = extend f xk + 2 ^ e / 2 ^ p := by
      rw [hy1, hy, hxk1, hxk]; ring
    rw [hd, hy_eq, hzp]
    field_simp
  -- the numerator is nonnegative and the right endpoint is at most `1`
  have hy0 : 0 ≤ extend f xk := (hrange xk ⟨hxk0, le_of_lt hxk_lt1⟩).1
  have hy11 : extend f xk1 ≤ 1 := (hrange xk1 ⟨by positivity, hxk1le⟩).2
  have hm0 : 0 ≤ m := by
    rw [hy_eq] at hy0
    have : (0 : ℝ) ≤ (m : ℝ) := by
      by_contra hcon; push_neg at hcon
      have : (m : ℝ) / 2 ^ q < 0 := div_neg_of_neg_of_pos hcon hqpos
      linarith
    exact_mod_cast this
  have hm1 : m + 1 ≤ 2 ^ q := by
    rw [hy1_eq, div_le_one hqpos] at hy11
    exact_mod_cast hy11
  refine ⟨m.toNat, q, ?_, ?_, ?_⟩
  · have hcast : ((m.toNat : ℤ)) = m := Int.toNat_of_nonneg hm0
    have h : (m.toNat : ℤ) + 1 ≤ ((2 ^ q : ℕ) : ℤ) := by
      rw [hcast]; push_cast; exact hm1
    exact_mod_cast h
  · rw [hy_eq]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hm0).symm
  · rw [hy1_eq]
    congr 1
    have : ((m.toNat : ℤ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm0
    rw [← this]
    push_cast
    ring

/-! ### Every Thompson map has a tree diagram -/

/-- **CFP Lemma 2.2**, in tree form: a map satisfying the Thompson condition is represented by
some tree diagram.  The domain tree cuts `[0,1]` into `2 ^ p` equal parts with `p` large. -/
theorem exists_represents_of_isThompson {f : UI ≃o UI} (hf : IsThompson f) :
    ∃ d : TreeDiagram, Represents d f := by
  classical
  obtain ⟨B, hBd, hB⟩ := hf
  have hL : IsThompsonLine (extend f) := (isThompsonLine_extend_iff f).mpr ⟨B, hBd, hB⟩
  have hf0 : extend f 0 = 0 := extend_eq_self_of_le_zero f (le_refl 0)
  have hf1 : extend f 1 = 1 := extend_eq_self_of_one_le f (le_refl 1)
  have hmono : Monotone (extend f) := (extend f).monotone
  have hrange : ∀ z ∈ Set.Icc (0 : ℝ) 1, extend f z ∈ Set.Icc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨by rw [← hf0]; exact hmono hz.1, by rw [← hf1]; exact hmono hz.2⟩
  -- the breakpoints inside `[0,1]`
  set B' : Finset ℝ := B.filter (fun b => b ∈ Set.Icc (0 : ℝ) 1) with hB'
  have hB'01 : ∀ b ∈ B', b ∈ Set.Icc (0 : ℝ) 1 := fun b hb => (Finset.mem_filter.mp hb).2
  have hform : ∀ u v : ℝ, u ∈ Set.Icc (0 : ℝ) 1 → v ∈ Set.Icc (0 : ℝ) 1 → u < v →
      Set.Ioo u v ∩ (B' : Set ℝ) = ∅ →
      ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc u v, extend f z = 2 ^ n * z + c := by
    intro u v hu hv huv hgap
    have hgapB : Set.Ioo (u : ℝ) v ∩ (B : Set ℝ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem] at hgap ⊢
      intro c ⟨hc, hcB⟩
      refine hgap c ⟨hc, ?_⟩
      rw [Finset.mem_coe, hB', Finset.mem_filter]
      exact ⟨Finset.mem_coe.mp hcB, ⟨le_trans hu.1 (le_of_lt hc.1), le_trans (le_of_lt hc.2) hv.2⟩⟩
    obtain ⟨n, c, h⟩ := hB ⟨u, hu⟩ ⟨v, hv⟩ huv hgapB
    refine ⟨n, c, fun z hz => ?_⟩
    have hz01 : z ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hu.1 hz.1, le_trans hz.2 hv.2⟩
    rw [extend_apply, extendFun_of_mem _ hz01]
    exact h ⟨z, hz01⟩ hz
  -- a uniform dyadic denominator for the breakpoints, the endpoints, and their images
  set S : Finset ℝ := insert 0 (insert 1 B') with hS
  have hSd : ∀ b ∈ S, IsDyadic b := by
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ⟨0, 0, by norm_num⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ⟨1, 0, by norm_num⟩
    exact hBd b (Finset.mem_filter.mp hb).1
  obtain ⟨K, hK⟩ := finset_uniform S
    (fun b M => (∃ a : ℤ, b = (a : ℝ) / 2 ^ M) ∧ (∃ a : ℤ, extend f b = (a : ℝ) / 2 ^ M))
    (by
      intro b hb
      obtain ⟨K₁, hK₁⟩ := isDyadic_den' (hSd b hb)
      obtain ⟨K₂, hK₂⟩ := isDyadic_den' (isDyadic_apply hL (hSd b hb))
      exact ⟨max K₁ K₂, fun M hM =>
        ⟨hK₁ M (le_trans (le_max_left _ _) hM), hK₂ M (le_trans (le_max_right _ _) hM)⟩⟩)
  have hpieces := fun k hk => piece_spec hB'01 hform hrange K hK k hk
  set p := 2 * K with hp
  have hpos : (0 : ℝ) < 2 ^ p := by positivity
  -- the uniform partition and its image
  set xs : List ℝ := (List.range (2 ^ p + 1)).map (fun k : ℕ => (k : ℝ) / 2 ^ p) with hxs
  have hxs_len : xs.length = 2 ^ p + 1 := by simp [hxs]
  have hxs_ne : xs ≠ [] := by
    intro h; rw [h] at hxs_len; simp at hxs_len
  have hxs_getD : ∀ k, k ≤ 2 ^ p → xs.getD k 0 = (k : ℝ) / 2 ^ p := fun k hk =>
    getD_range_map (Nat.lt_succ_of_le hk)
  have hxs0 : xs.getD 0 0 = 0 := by rw [hxs_getD 0 (Nat.zero_le _)]; simp
  have hxs1 : xs.getD (xs.length - 1) 0 = 1 := by
    rw [hxs_len, Nat.add_sub_cancel, hxs_getD _ le_rfl]
    push_cast
    field_simp
  set ys : List ℝ := xs.map (extend f) with hys
  have hys_len : ys.length = 2 ^ p + 1 := by rw [hys, List.length_map, hxs_len]
  have hys_ne : ys ≠ [] := by
    intro h; rw [h] at hys_len; simp at hys_len
  have hys_getD : ∀ k, k ≤ 2 ^ p → ys.getD k 0 = extend f ((k : ℝ) / 2 ^ p) := by
    intro k hk
    rw [hys, getD_map (by rw [hxs_len]; exact Nat.lt_succ_of_le hk), hxs_getD k hk]
  have hxs_sdp : IsStandardDyadicPartition xs := by
    refine ⟨?_, ?_, ?_⟩
    · rw [head?_eq_getD hxs_ne, hxs0]
    · rw [getLast?_eq_getD xs hxs_ne, hxs1]
    · refine getD_chain _ ?_
      intro j hj
      rw [hxs_len] at hj
      rw [hxs_getD j (by omega), hxs_getD (j + 1) (by omega)]
      exact ⟨j, p, by omega, rfl, by push_cast; rfl⟩
  have hys_sdp : IsStandardDyadicPartition ys := by
    refine ⟨?_, ?_, ?_⟩
    · rw [head?_eq_getD hys_ne, hys_getD 0 (Nat.zero_le _)]
      simp [hf0]
    · rw [getLast?_eq_getD ys hys_ne, hys_len, Nat.add_sub_cancel, hys_getD _ le_rfl]
      have : ((2 ^ p : ℕ) : ℝ) / 2 ^ p = 1 := by push_cast; field_simp
      rw [this, hf1]
    · refine getD_chain _ ?_
      intro j hj
      rw [hys_len] at hj
      rw [hys_getD j (by omega), hys_getD (j + 1) (by omega)]
      have := (hpieces j (by omega)).2
      push_cast
      exact this
  obtain ⟨R, hR⟩ := exists_tree_marks hxs_sdp
  obtain ⟨T, hT⟩ := exists_tree_marks hys_sdp
  have hlc : R.leafCount = T.leafCount := by
    have h1 := marks_length_eq R
    have h2 := marks_length_eq T
    rw [hR, hxs_len] at h1
    rw [hT, hys_len] at h2
    omega
  refine ⟨⟨R, T, hlc⟩, mem_F_of_isThompson ⟨B, hBd, hB⟩, ?_, ?_⟩
  · show AffineOnPieces (extend f) R.marks
    rw [hR]
    refine getD_chain _ ?_
    intro j hj
    rw [hxs_len] at hj
    rw [hxs_getD j (by omega), hxs_getD (j + 1) (by omega)]
    have := (hpieces j (by omega)).1
    push_cast
    exact this
  · show R.marks.map (extend f) = T.marks
    rw [hR, hT]

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

lemma delCaret_leaf_leaf : delCaret (TTree.node TTree.leaf TTree.leaf) 0 = TTree.leaf := rfl

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

lemma mk_length (t : TTree) (a b : ℝ) : (mk t a b).length = t.leafCount + 1 := by
  have := marksAux_length' t a b
  simp only [mk, List.length_cons, List.length_append, List.length_nil]
  omega

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

theorem exists_isReduced_represents' {f : UI ≃o UI} (hf : f ∈ F) :
    ∃ d : TreeDiagram, IsReduced d ∧ Represents d f := by
  classical
  have hT : IsThompson f := mem_F_iff_isThompson.mp hf
  obtain ⟨d₀, hd₀⟩ := exists_represents_of_isThompson hT
  have hex : ∃ n, ∃ d : TreeDiagram, d.dom.leafCount = n ∧ Represents d f := ⟨_, d₀, rfl, hd₀⟩
  obtain ⟨d, hdn, hd⟩ := Nat.find_spec hex
  refine ⟨d, ?_, hd⟩
  intro k ⟨hcR, hcS⟩
  obtain ⟨R, S, hRS⟩ := d
  have hd' : Represents ⟨R, S, hRS⟩ f := hd
  have hsmall := represents_delCaret hd' hcR hcS
  have hlt : (delCaret R k).leafCount < Nat.find hex := by
    have := leafCount_delCaret R k hcR
    show (delCaret R k).leafCount < Nat.find hex
    have hdn' : R.leafCount = Nat.find hex := hdn
    omega
  exact Nat.find_min hex hlt ⟨_, rfl, hsmall⟩

end CannonFloydParry

open CannonFloydParry

theorem solution {f : UI ≃o UI} (hf : f ∈ F) :
    ∃ d : TreeDiagram, IsReduced d ∧ Represents d f :=
  exists_isReduced_represents' hf
