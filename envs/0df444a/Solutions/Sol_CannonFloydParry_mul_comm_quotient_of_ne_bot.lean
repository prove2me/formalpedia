-- Prove2me | solution 1 for CannonFloydParry.mul_comm_quotient_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-17T06:18:09.281594+00:00
-- url     : https://prove2.me/submissions/2d54b242-b963-4967-8b30-586631cf7255

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

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

/-- **Theorem 2.5, first statement.** -/
lemma represents_word_exponents {d : TreeDiagram} {f : UI ≃o UI} (h : Represents d f) :
    f = word d.ran.exponents * (word d.dom.exponents)⁻¹ := by
  have hdom : d.dom.leafCount = (TTree.comb (d.dom.leafCount - 1)).leafCount := by
    rw [leafCount_comb]
    have := one_le_leafCount' d.dom
    omega
  have hran : d.ran.leafCount = (TTree.comb (d.dom.leafCount - 1)).leafCount := by
    rw [← d.leaves_eq]; exact hdom
  have hR := represents_word_inv d.dom.exponents.sum d.dom _ hdom le_rfl
  have hS := represents_word_inv d.ran.exponents.sum d.ran _ hran le_rfl
  have hS' := represents_inv _ hS
  rw [inv_inv] at hS'
  have hcomp := represents_mul _ _ hR hS'
  exact represents_unique h hcomp

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

/-- The group `F` is exactly the set of Thompson maps (the section 1 statement that `F` is a
subgroup, reproved inline). -/
lemma mem_F_iff_isThompson' {f : UI ≃o UI} : f ∈ F ↔ IsThompson f := by
  refine ⟨fun hf => ?_, mem_F_of_isThompson⟩
  induction hf using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact (isThompsonLine_extend_iff 1).mp (by rw [extend_one]; exact isThompsonLine_one)
  | mul x y _ _ hx hy =>
      refine (isThompsonLine_extend_iff _).mp ?_
      rw [extend_mul]
      exact isThompsonLine_mul ((isThompsonLine_extend_iff x).mpr hx)
        ((isThompsonLine_extend_iff y).mpr hy)
  | inv x _ hx =>
      refine (isThompsonLine_extend_iff _).mp ?_
      rw [show extend x⁻¹ = (extend x)⁻¹ from map_inv extendHom x]
      exact isThompsonLine_inv ((isThompsonLine_extend_iff x).mpr hx)

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

/-! ### The generators `Xₙ` lie in the subgroup generated by `A` and `B` -/

lemma mapA_mem_closure : mapA ∈ Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) :=
  Subgroup.subset_closure (Set.mem_insert _ _)

lemma mapB_mem_closure : mapB ∈ Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

lemma X_mem_closure : ∀ n : ℕ, X n ∈ Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI))
  | 0 => mapA_mem_closure
  | n + 1 => by
      show (mapA ^ n)⁻¹ * mapB * mapA ^ n ∈ _
      exact mul_mem (mul_mem (inv_mem (pow_mem mapA_mem_closure n)) mapB_mem_closure)
        (pow_mem mapA_mem_closure n)

lemma wordFrom_mem_closure : ∀ (cs : List ℕ) (i : ℕ),
    wordFrom i cs ∈ Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) := by
  intro cs
  induction cs with
  | nil => intro i; rw [wordFrom]; exact one_mem _
  | cons c cs ih =>
      intro i
      rw [wordFrom]
      exact mul_mem (pow_mem (X_mem_closure i) c) (ih (i + 1))

/-- **Corollary 2.6**: `F` is generated by `A` and `B`. -/
theorem closure_mapA_mapB_eq_F' : Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) = F := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · exact mapA_mem_F
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact mapB_mem_F
  · intro f hf
    have hT : IsThompson f := mem_F_iff_isThompson'.mp hf
    obtain ⟨d, hd⟩ := exists_represents_of_isThompson hT
    rw [represents_word_exponents hd]
    exact mul_mem (wordFrom_mem_closure _ _) (inv_mem (wordFrom_mem_closure _ _))

end CannonFloydParry

namespace CannonFloydParry

/-! ### The relation `Xₙ Xₖ = Xₖ Xₙ₊₁` for `k < n`, read off the rotation diagrams -/

lemma spine_append (a b : List TTree) (T : TTree) : spine (a ++ b) T = spine a (spine b T) := by
  induction a with
  | nil => rfl
  | cons w a ih => rw [List.cons_append, spine, spine, ih]

lemma represents_congr {R S R' S' : TTree} {h : R.leafCount = S.leafCount} {f : UI ≃o UI}
    (hR : R = R') (hS : S = S') (hr : Represents ⟨R, S, h⟩ f) :
    Represents ⟨R', S', by rw [← hR, ← hS]; exact h⟩ f := by
  subst hR; subst hS; exact hr

lemma X_comm {k n : ℕ} (hkn : k < n) : X n * X k = X k * X (n + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = k + 1 + j := ⟨n - k - 1, by omega⟩
  -- the innermost rotatable node and its rotation
  set N : TTree := TTree.node TTree.leaf (TTree.node TTree.leaf TTree.leaf) with hN
  set N' : TTree := TTree.node (TTree.node TTree.leaf TTree.leaf) TTree.leaf with hN'
  set Y : TTree := spine (List.replicate j TTree.leaf) N with hY
  set Y' : TTree := spine (List.replicate j TTree.leaf) N' with hY'
  -- the spines involved
  have hsplit : List.replicate (k + 1 + j + 1) TTree.leaf
      = List.replicate k TTree.leaf ++ [TTree.leaf] ++ [TTree.leaf]
        ++ List.replicate j TTree.leaf := by
    rw [show k + 1 + j + 1 = k + 1 + 1 + j by omega, List.replicate_add, List.replicate_add,
      List.replicate_add]
    rfl
  have hT : spine (List.replicate (k + 1 + j + 1) TTree.leaf) N
      = spine (List.replicate k TTree.leaf) (TTree.node TTree.leaf (TTree.node TTree.leaf Y)) := by
    rw [hsplit, spine_append, spine_append, spine_append]; rfl
  have hT' : spine (List.replicate (k + 1 + j + 1) TTree.leaf) N'
      = spine (List.replicate k TTree.leaf)
          (TTree.node TTree.leaf (TTree.node TTree.leaf Y')) := by
    rw [hsplit, spine_append, spine_append, spine_append]; rfl
  have hU : spine (List.replicate k TTree.leaf ++ [TTree.node TTree.leaf TTree.leaf]
        ++ List.replicate j TTree.leaf) N
      = spine (List.replicate k TTree.leaf)
          (TTree.node (TTree.node TTree.leaf TTree.leaf) Y) := by
    rw [spine_append, spine_append]; rfl
  have hV : spine (List.replicate k TTree.leaf ++ [TTree.node TTree.leaf TTree.leaf]
        ++ List.replicate j TTree.leaf) N'
      = spine (List.replicate k TTree.leaf)
          (TTree.node (TTree.node TTree.leaf TTree.leaf) Y') := by
    rw [spine_append, spine_append]; rfl
  -- the four diagrams
  have hA := represents_congr hT hT'
    (represents_X (k + 1 + j + 1) _ (by simp) TTree.leaf TTree.leaf TTree.leaf)
  have hB := represents_X k (List.replicate k TTree.leaf) (by simp) TTree.leaf TTree.leaf Y'
  have hC := represents_X k (List.replicate k TTree.leaf) (by simp) TTree.leaf TTree.leaf Y
  have hD := represents_congr hU hV
    (represents_X (k + 1 + j) _ (by simp; omega) TTree.leaf TTree.leaf TTree.leaf)
  -- both products have the same diagram
  have h1 := represents_mul _ _ hA hB
  have h2 := represents_mul _ _ hC hD
  exact represents_unique h2 h1

/-! ### Pushing a generator through a positive word -/

lemma X_pow_comm {i k : ℕ} (hik : i < k) : ∀ d : ℕ, X k * X i ^ d = X i ^ d * X (k + d) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, X_comm (by omega), ← mul_assoc, ← pow_succ,
        show k + d + 1 = k + (d + 1) by omega]

lemma wordFrom_pad {a b : ℕ} (hab : a ≤ b) (es : List ℕ) :
    wordFrom b es = wordFrom a (List.replicate (b - a) 0 ++ es) := by
  rw [wordFrom_replicate_zero, show a + (b - a) = b by omega]

lemma X_mul_wordFrom : ∀ (ds : List ℕ) (k i : ℕ),
    ∃ es, X k * wordFrom i ds = wordFrom (min i k) es := by
  intro ds
  induction ds with
  | nil =>
      intro k i
      refine ⟨List.replicate (k - min i k) 0 ++ [1], ?_⟩
      rw [wordFrom, mul_one, ← wordFrom_pad (by omega), wordFrom, wordFrom, pow_one, mul_one]
  | cons d ds ih =>
      intro k i
      rcases Nat.lt_or_ge i k with hik | hki
      · -- `k > i`: commute past `Xᵢ ^ d`, raising the index
        obtain ⟨es', hes'⟩ := ih (k + d) (i + 1)
        rw [show min (i + 1) (k + d) = i + 1 by omega] at hes'
        refine ⟨d :: es', ?_⟩
        rw [wordFrom, ← mul_assoc, X_pow_comm hik, mul_assoc, hes', wordFrom,
          show min i k = i by omega]
      · -- `k ≤ i`: the generator is absorbed at the front, with zero padding
        refine ⟨TTree.incrHead (List.replicate (i - k) 0 ++ d :: ds), ?_⟩
        rw [show min i k = k by omega, wordFrom_pad hki (d :: ds)]
        cases hrep : List.replicate (i - k) 0 ++ d :: ds with
        | nil => exact absurd hrep (by simp)
        | cons a as => rw [wordFrom_incrHead]

lemma X_pow_mul_wordFrom : ∀ (c k m : ℕ) (es : List ℕ),
    ∃ es', X k ^ c * wordFrom m es = wordFrom (min m k) es' := by
  intro c
  induction c with
  | zero =>
      intro k m es
      exact ⟨_, by rw [pow_zero, one_mul, wordFrom_pad (Nat.min_le_left m k)]⟩
  | succ c ih =>
      intro k m es
      obtain ⟨es₁, h₁⟩ := ih k m es
      obtain ⟨es₂, h₂⟩ := X_mul_wordFrom es₁ k (min m k)
      refine ⟨es₂, ?_⟩
      rw [pow_succ', mul_assoc, h₁, h₂, show min (min m k) k = min m k by omega]

lemma wordFrom_mul_wordFrom : ∀ (cs : List ℕ) (i j : ℕ) (ds : List ℕ),
    ∃ es, wordFrom i cs * wordFrom j ds = wordFrom (min i j) es := by
  intro cs
  induction cs with
  | nil =>
      intro i j ds
      exact ⟨_, by rw [wordFrom, one_mul, wordFrom_pad (Nat.min_le_right i j)]⟩
  | cons c cs ih =>
      intro i j ds
      obtain ⟨es₁, h₁⟩ := ih (i + 1) j ds
      obtain ⟨es₂, h₂⟩ := X_pow_mul_wordFrom c i (min (i + 1) j) es₁
      refine ⟨es₂, ?_⟩
      rw [wordFrom, mul_assoc, h₁, h₂, show min (min (i + 1) j) i = min i j by omega]

end CannonFloydParry

open CannonFloydParry

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

open Function

/-- The homomorphism `ℤ ⊕ ℤ → A` sending `(m, n)` to `u ^ m * v ^ n`, for `A` abelian. -/
def pairHom {A : Type*} [CommGroup A] (u v : A) : Multiplicative (ℤ × ℤ) →* A where
  toFun m := u ^ (Multiplicative.toAdd m).1 * v ^ (Multiplicative.toAdd m).2
  map_one' := by simp
  map_mul' x y := by
    show u ^ ((Multiplicative.toAdd x).1 + (Multiplicative.toAdd y).1) *
        v ^ ((Multiplicative.toAdd x).2 + (Multiplicative.toAdd y).2) = _
    rw [zpow_add, zpow_add, mul_mul_mul_comm]

lemma pairHom_apply {A : Type*} [CommGroup A] (u v : A) (m : Multiplicative (ℤ × ℤ)) :
    pairHom u v m = u ^ (Multiplicative.toAdd m).1 * v ^ (Multiplicative.toAdd m).2 := rfl

/-- If `u` and `v` generate the abelian group `A`, then `pairHom u v` is onto. -/
lemma pairHom_surjective {A : Type*} [CommGroup A] (u v : A)
    (h : Subgroup.closure ({u, v} : Set A) = ⊤) : Surjective (pairHom u v) := by
  rw [← MonoidHom.range_eq_top]
  rw [← top_le_iff, ← h, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact ⟨Multiplicative.ofAdd (1, 0), by simp [pairHom_apply]⟩
  · exact ⟨Multiplicative.ofAdd (0, 1), by simp [pairHom_apply]⟩

/-- A surjective endomorphism of `ℤ ⊕ ℤ` (written multiplicatively) is injective. -/
lemma injective_of_surjective_endo (e : Multiplicative (ℤ × ℤ) →* Multiplicative (ℤ × ℤ))
    (he : Surjective e) : Injective e := by
  let f : (ℤ × ℤ) →+ (ℤ × ℤ) :=
    { toFun := fun w => Multiplicative.toAdd (e (Multiplicative.ofAdd w))
      map_zero' := by simp
      map_add' := fun w z => by
        show Multiplicative.toAdd (e (Multiplicative.ofAdd w * Multiplicative.ofAdd z)) = _
        rw [map_mul]; rfl }
  have hfs : Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := he (Multiplicative.ofAdd y)
    exact ⟨Multiplicative.toAdd x, by simpa [f] using congrArg Multiplicative.toAdd hx⟩
  have hfi : Injective f :=
    IsNoetherian.injective_of_surjective_endomorphism f.toIntLinearMap hfs
  intro x y hxy
  have : f (Multiplicative.toAdd x) = f (Multiplicative.toAdd y) := by
    simpa [f] using congrArg Multiplicative.toAdd hxy
  simpa using hfi this

/-- The group-theoretic step of Theorem 4.1 (section 4 milestone 8), reproved inline. -/
theorem ker_eq_commutator_of_two_generators_of_surjective' {K : Type*} [Group K] (a b : K)
    (hgen : Subgroup.closure {a, b} = ⊤)
    (φ : K →* Multiplicative (ℤ × ℤ)) (hφ : Function.Surjective φ) :
    φ.ker = commutator K := by
  classical
  set ψ : Abelianization K →* Multiplicative (ℤ × ℤ) := Abelianization.lift φ with hψdef
  have hψφ : ∀ x : K, ψ (Abelianization.of x) = φ x := fun x => rfl
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := hφ y
    exact ⟨Abelianization.of x, by rw [hψφ]; exact hx⟩
  -- the abelianization is generated by the images of `a` and `b`
  have hAB : Subgroup.closure ({Abelianization.of a, Abelianization.of b} :
      Set (Abelianization K)) = ⊤ := by
    have hmap : (Subgroup.closure ({a, b} : Set K)).map
        (Abelianization.of (G := K)) =
        Subgroup.closure ({Abelianization.of a, Abelianization.of b} :
          Set (Abelianization K)) := by
      rw [MonoidHom.map_closure]
      congr 1
      simp [Set.image_insert_eq]
    have hofsurj : Function.Surjective (Abelianization.of (G := K)) := fun y =>
      QuotientGroup.induction_on y fun z => ⟨z, rfl⟩
    rw [← hmap, hgen, Subgroup.map_top_of_surjective _ hofsurj]
  have hχsurj : Function.Surjective (pairHom (Abelianization.of a) (Abelianization.of b)) :=
    pairHom_surjective _ _ hAB
  have hcompinj : Function.Injective
      (ψ.comp (pairHom (Abelianization.of a) (Abelianization.of b))) :=
    injective_of_surjective_endo _ (hψsurj.comp hχsurj)
  have hψinj : Function.Injective ψ := by
    intro p q hpq
    obtain ⟨u, rfl⟩ := hχsurj p
    obtain ⟨v, rfl⟩ := hχsurj q
    exact congrArg _ (hcompinj hpq)
  rw [← Abelianization.ker_of]
  ext x
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hx
    refine hψinj ?_
    rw [hψφ, hx, map_one]
  · intro hx
    rw [← hψφ, hx, map_one]

end CannonFloydParry

namespace CannonFloydParry

/-! ### The slope of a Thompson map at the two endpoints

An element of `F` is affine on some `[0, ε]`, with slope a power of two and, since it fixes `0`,
no intercept: `f z = 2 ^ n z` there. Likewise near `1`: `1 - f z = 2 ^ m (1 - z)`. The exponents
`n`, `m` are the source's "right derivative at `0`" and "left derivative at `1`", and
`f ↦ (n, m)` is the homomorphism `φ` of Theorem 4.1. -/

def HasSlope0 (f : UI ≃o UI) (n : ℤ) : Prop :=
  ∃ ε > (0 : ℝ), ∀ z : UI, (z : ℝ) ≤ ε → (f z : ℝ) = 2 ^ n * (z : ℝ)

def HasSlope1 (f : UI ≃o UI) (n : ℤ) : Prop :=
  ∃ ε > (0 : ℝ), ∀ z : UI, 1 - ε ≤ (z : ℝ) → 1 - (f z : ℝ) = 2 ^ n * (1 - (z : ℝ))

lemma two_zpow_injective {n m : ℤ} (h : (2 : ℝ) ^ n = 2 ^ m) : n = m :=
  zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) h

lemma hasSlope0_unique {f : UI ≃o UI} {n m : ℤ} (hn : HasSlope0 f n) (hm : HasSlope0 f m) :
    n = m := by
  obtain ⟨ε, hε, hn⟩ := hn
  obtain ⟨ε', hε', hm⟩ := hm
  set z : ℝ := min (min ε ε') 1 with hz
  have hz0 : 0 < z := lt_min (lt_min hε hε') one_pos
  have hz1 : z ≤ 1 := min_le_right _ _
  have hzε : z ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
  have hzε' : z ≤ ε' := le_trans (min_le_left _ _) (min_le_right _ _)
  have h1 := hn ⟨z, le_of_lt hz0, hz1⟩ hzε
  have h2 := hm ⟨z, le_of_lt hz0, hz1⟩ hzε'
  have : (2 : ℝ) ^ n * z = 2 ^ m * z := by rw [← h1, ← h2]
  exact two_zpow_injective (mul_right_cancel₀ (ne_of_gt hz0) this)

lemma hasSlope1_unique {f : UI ≃o UI} {n m : ℤ} (hn : HasSlope1 f n) (hm : HasSlope1 f m) :
    n = m := by
  obtain ⟨ε, hε, hn⟩ := hn
  obtain ⟨ε', hε', hm⟩ := hm
  set d : ℝ := min (min ε ε') 1 with hd
  have hd0 : 0 < d := lt_min (lt_min hε hε') one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  have hdε : d ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
  have hdε' : d ≤ ε' := le_trans (min_le_left _ _) (min_le_right _ _)
  have hz : (1 - d) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h1 := hn ⟨1 - d, hz⟩ (by simp; linarith)
  have h2 := hm ⟨1 - d, hz⟩ (by simp; linarith)
  simp only [Subtype.coe_mk, sub_sub_cancel] at h1 h2
  have : (2 : ℝ) ^ n * d = 2 ^ m * d := by rw [← h1, ← h2]
  exact two_zpow_injective (mul_right_cancel₀ (ne_of_gt hd0) this)

/-- A point of `(0, 1]` below every positive breakpoint. -/
lemma exists_gap_above_zero (B : Finset ℝ) :
    ∃ y : ℝ, 0 < y ∧ y ≤ 1 ∧ Set.Ioo (0 : ℝ) y ∩ (B : Set ℝ) = ∅ := by
  classical
  set P := B.filter (fun b => 0 < b) with hP
  by_cases hne : P.Nonempty
  · refine ⟨min (P.min' hne) 1, lt_min ?_ one_pos, min_le_right _ _, ?_⟩
    · have := Finset.min'_mem P hne
      exact (Finset.mem_filter.mp this).2
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨⟨hb0, hb1⟩, hbB⟩
      have hbP : b ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hbB, hb0⟩
      have := Finset.min'_le P b hbP
      have := min_le_left (P.min' hne) 1
      linarith
  · refine ⟨1, one_pos, le_refl _, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro b ⟨⟨hb0, -⟩, hbB⟩
    exact hne ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hbB, hb0⟩⟩

/-- A point of `[0, 1)` above every breakpoint below `1`. -/
lemma exists_gap_below_one (B : Finset ℝ) :
    ∃ x : ℝ, 0 ≤ x ∧ x < 1 ∧ Set.Ioo x (1 : ℝ) ∩ (B : Set ℝ) = ∅ := by
  classical
  set P := B.filter (fun b => b < 1) with hP
  by_cases hne : P.Nonempty
  · refine ⟨max (P.max' hne) 0, le_max_right _ _, max_lt ?_ one_pos, ?_⟩
    · have := Finset.max'_mem P hne
      exact (Finset.mem_filter.mp this).2
    · rw [Set.eq_empty_iff_forall_notMem]
      rintro b ⟨⟨hb0, hb1⟩, hbB⟩
      have hbP : b ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hbB, hb1⟩
      have := Finset.le_max' P b hbP
      have := le_max_left (P.max' hne) 0
      linarith
  · refine ⟨0, le_refl _, one_pos, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro b ⟨⟨-, hb1⟩, hbB⟩
    exact hne ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hbB, hb1⟩⟩

lemma exists_hasSlope0 {f : UI ≃o UI} (hf : IsThompson f) : ∃ n, HasSlope0 f n := by
  obtain ⟨B, -, hB⟩ := hf
  obtain ⟨y, hy0, hy1, hgap⟩ := exists_gap_above_zero B
  obtain ⟨n, c, h⟩ := hB ⟨0, zero_mem_UI⟩ ⟨y, le_of_lt hy0, hy1⟩ hy0 hgap
  have h0 := h ⟨0, zero_mem_UI⟩ ⟨le_refl _, le_of_lt hy0⟩
  rw [coe_apply_zero] at h0
  have hc : c = 0 := by simpa using h0.symm
  refine ⟨n, y, hy0, fun z hz => ?_⟩
  have := h z ⟨z.2.1, hz⟩
  rw [this, hc, add_zero]

lemma exists_hasSlope1 {f : UI ≃o UI} (hf : IsThompson f) : ∃ n, HasSlope1 f n := by
  obtain ⟨B, -, hB⟩ := hf
  obtain ⟨x, hx0, hx1, hgap⟩ := exists_gap_below_one B
  obtain ⟨n, c, h⟩ := hB ⟨x, hx0, le_of_lt hx1⟩ ⟨1, one_mem_UI⟩ hx1 hgap
  have h1 := h ⟨1, one_mem_UI⟩ ⟨le_of_lt hx1, le_refl _⟩
  rw [coe_apply_one] at h1
  refine ⟨n, 1 - x, by linarith, fun z hz => ?_⟩
  have := h z ⟨by simp at hz; linarith, z.2.2⟩
  rw [this]
  simp only [Subtype.coe_mk] at h1
  linarith

lemma hasSlope0_mul {f g : UI ≃o UI} {n m : ℤ} (hf : HasSlope0 f n) (hg : HasSlope0 g m) :
    HasSlope0 (f * g) (n + m) := by
  obtain ⟨ε, hε, hf⟩ := hf
  obtain ⟨δ, hδ, hg⟩ := hg
  have hm : (0 : ℝ) < 2 ^ m := zpow_pos (by norm_num) _
  refine ⟨min δ (ε / 2 ^ m), lt_min hδ (div_pos hε hm), fun z hz => ?_⟩
  have hzδ : (z : ℝ) ≤ δ := le_trans hz (min_le_left _ _)
  have hzε : (z : ℝ) ≤ ε / 2 ^ m := le_trans hz (min_le_right _ _)
  have hgz : (g z : ℝ) = 2 ^ m * z := hg z hzδ
  have hgz' : (g z : ℝ) ≤ ε := by
    rw [hgz]; rw [le_div_iff₀ hm] at hzε; linarith
  show (f (g z) : ℝ) = 2 ^ (n + m) * z
  rw [hf (g z) hgz', hgz, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

lemma hasSlope1_mul {f g : UI ≃o UI} {n m : ℤ} (hf : HasSlope1 f n) (hg : HasSlope1 g m) :
    HasSlope1 (f * g) (n + m) := by
  obtain ⟨ε, hε, hf⟩ := hf
  obtain ⟨δ, hδ, hg⟩ := hg
  have hm : (0 : ℝ) < 2 ^ m := zpow_pos (by norm_num) _
  refine ⟨min δ (ε / 2 ^ m), lt_min hδ (div_pos hε hm), fun z hz => ?_⟩
  have hmin1 := min_le_left δ (ε / 2 ^ m)
  have hmin2 := min_le_right δ (ε / 2 ^ m)
  have hzδ : 1 - δ ≤ (z : ℝ) := by linarith
  have hzε : 1 - ε / 2 ^ m ≤ (z : ℝ) := by linarith
  have hgz : 1 - (g z : ℝ) = 2 ^ m * (1 - z) := hg z hzδ
  have hgz' : 1 - ε ≤ (g z : ℝ) := by
    have : (1 : ℝ) - z ≤ ε / 2 ^ m := by linarith
    rw [le_div_iff₀ hm] at this
    linarith
  show 1 - (f (g z) : ℝ) = 2 ^ (n + m) * (1 - z)
  rw [hf (g z) hgz', hgz, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-! ### The homomorphism `φ` -/

noncomputable def slope0 (f : F) : ℤ :=
  Classical.choose (exists_hasSlope0 (mem_F_iff_isThompson'.mp f.2))

noncomputable def slope1 (f : F) : ℤ :=
  Classical.choose (exists_hasSlope1 (mem_F_iff_isThompson'.mp f.2))

lemma hasSlope0_slope0 (f : F) : HasSlope0 (f : UI ≃o UI) (slope0 f) :=
  Classical.choose_spec (exists_hasSlope0 (mem_F_iff_isThompson'.mp f.2))

lemma hasSlope1_slope1 (f : F) : HasSlope1 (f : UI ≃o UI) (slope1 f) :=
  Classical.choose_spec (exists_hasSlope1 (mem_F_iff_isThompson'.mp f.2))

lemma slope0_eq {f : F} {n : ℤ} (h : HasSlope0 (f : UI ≃o UI) n) : slope0 f = n :=
  hasSlope0_unique (hasSlope0_slope0 f) h

lemma slope1_eq {f : F} {n : ℤ} (h : HasSlope1 (f : UI ≃o UI) n) : slope1 f = n :=
  hasSlope1_unique (hasSlope1_slope1 f) h

lemma hasSlope0_one : HasSlope0 (1 : UI ≃o UI) 0 :=
  ⟨1, one_pos, fun z _ => by simp⟩

lemma hasSlope1_one : HasSlope1 (1 : UI ≃o UI) 0 :=
  ⟨1, one_pos, fun z _ => by simp⟩

noncomputable def φ : F →* Multiplicative (ℤ × ℤ) where
  toFun f := Multiplicative.ofAdd (slope0 f, slope1 f)
  map_one' := by
    have h0 : slope0 (1 : F) = 0 := slope0_eq hasSlope0_one
    have h1 : slope1 (1 : F) = 0 := slope1_eq hasSlope1_one
    rw [h0, h1]; rfl
  map_mul' f g := by
    have h0 : slope0 (f * g) = slope0 f + slope0 g :=
      slope0_eq (hasSlope0_mul (hasSlope0_slope0 f) (hasSlope0_slope0 g))
    have h1 : slope1 (f * g) = slope1 f + slope1 g :=
      slope1_eq (hasSlope1_mul (hasSlope1_slope1 f) (hasSlope1_slope1 g))
    rw [h0, h1]; rfl

lemma φ_apply (f : F) : φ f = Multiplicative.ofAdd (slope0 f, slope1 f) := rfl

/-! ### Values on the generators, and surjectivity -/

lemma hasSlope0_mapA : HasSlope0 mapA (-1) :=
  ⟨1 / 2, by norm_num, fun z hz => by
    rw [coe_mapA, aFun_of_mem1 z.2.1 hz, zpow_neg_one]; ring⟩

lemma hasSlope1_mapA : HasSlope1 mapA 1 :=
  ⟨1 / 4, by norm_num, fun z hz => by
    rw [coe_mapA, aFun_of_mem3 (by linarith) z.2.2, zpow_one]; ring⟩

lemma hasSlope0_mapB : HasSlope0 mapB 0 :=
  ⟨1 / 2, by norm_num, fun z hz => by
    rw [coe_mapB, bFun_of_le_half hz, zpow_zero]; ring⟩

lemma hasSlope1_mapB : HasSlope1 mapB 1 :=
  ⟨1 / 8, by norm_num, fun z hz => by
    rw [coe_mapB, bFun_of_mem3 (by linarith) z.2.2, zpow_one]; ring⟩

/-- `A` and `B` as elements of the subgroup `F`. -/
noncomputable def genA : F := ⟨mapA, mapA_mem_F⟩
noncomputable def genB : F := ⟨mapB, mapB_mem_F⟩

lemma φ_genA : φ genA = Multiplicative.ofAdd (-1, 1) := by
  rw [φ_apply, slope0_eq hasSlope0_mapA, slope1_eq hasSlope1_mapA]

lemma φ_genB : φ genB = Multiplicative.ofAdd (0, 1) := by
  rw [φ_apply, slope0_eq hasSlope0_mapB, slope1_eq hasSlope1_mapB]

lemma φ_surjective : Function.Surjective φ := by
  intro w
  refine ⟨genA ^ (-(Multiplicative.toAdd w).1) * genB ^ ((Multiplicative.toAdd w).1 + (Multiplicative.toAdd w).2), ?_⟩
  rw [map_mul, map_zpow, map_zpow, φ_genA, φ_genB, ← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_add]
  conv_rhs => rw [← ofAdd_toAdd w]
  congr 1
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; ring

/-- `F` is generated by `A` and `B`, as elements of `F` (Corollary 2.6 lifted to the subtype). -/
lemma closure_genA_genB : Subgroup.closure ({genA, genB} : Set F) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : (x : UI ≃o UI) ∈ Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) := by
    rw [closure_mapA_mapB_eq_F']; exact x.2
  have hmap : (Subgroup.closure ({genA, genB} : Set F)).map F.subtype
      = Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI)) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq, genA, genB]
  rw [← hmap] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have : y = x := Subtype.ext hyx
  rw [← this]; exact hy

lemma ker_φ : φ.ker = commutator F :=
  ker_eq_commutator_of_two_generators_of_surjective' genA genB closure_genA_genB φ φ_surjective

/-! ### Slope zero is triviality near the endpoint -/

lemma trivialNearZero_iff_slope0 (f : F) : TrivialNearZero (f : UI ≃o UI) ↔ slope0 f = 0 := by
  constructor
  · rintro ⟨ε, hε, h⟩
    refine slope0_eq ⟨ε / 2, half_pos hε, fun z hz => ?_⟩
    rw [h z (by linarith), zpow_zero, one_mul]
  · intro h0
    obtain ⟨ε, hε, h⟩ := hasSlope0_slope0 f
    rw [h0] at h
    exact ⟨ε, hε, fun z hz => by rw [h z (le_of_lt hz), zpow_zero, one_mul]⟩

lemma trivialNearOne_iff_slope1 (f : F) : TrivialNearOne (f : UI ≃o UI) ↔ slope1 f = 0 := by
  constructor
  · rintro ⟨ε, hε, h⟩
    refine slope1_eq ⟨ε / 2, half_pos hε, fun z hz => ?_⟩
    rw [h z (by linarith), zpow_zero, one_mul]
  · intro h0
    obtain ⟨ε, hε, h⟩ := hasSlope1_slope1 f
    rw [h0] at h
    exact ⟨ε, hε, fun z hz => by
      have := h z (le_of_lt hz)
      rw [zpow_zero, one_mul] at this
      linarith⟩

/-! ### Theorem 4.1 -/

theorem mem_commutator_iff' (g : F) :
    g ∈ commutator F ↔ TrivialNearZero (g : UI ≃o UI) ∧ TrivialNearOne (g : UI ≃o UI) := by
  rw [← ker_φ, MonoidHom.mem_ker, φ_apply, trivialNearZero_iff_slope0, trivialNearOne_iff_slope1]
  constructor
  · intro h
    have h' : (slope0 g, slope1 g) = ((0 : ℤ), (0 : ℤ)) := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    exact ⟨(Prod.mk.injEq _ _ _ _).mp h' |>.1, (Prod.mk.injEq _ _ _ _).mp h' |>.2⟩
  · rintro ⟨h0, h1⟩
    rw [h0, h1]; rfl

theorem nonempty_abelianization_mulEquiv_zsq' :
    Nonempty (Abelianization F ≃* Multiplicative (ℤ × ℤ)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq ker_φ).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ φ_surjective)⟩

end CannonFloydParry

/-!
# Dyadic piecewise-linear machinery for Cannon–Floyd–Parry Lemma 4.2

Shared development, kept as its own file while it is being built.  It is concatenated into the
self-contained solution files that are submitted to the platform.

Two independent parts:

* `SumPow` — the arithmetic core: a positive integer `q` is a sum of *exactly* `k` integer
  powers of two whenever `q < 2 ^ k`.
* the piecewise-linear constructor — from strictly monotone dyadic breakpoint data `s` and
  target data `t` whose consecutive gaps have power-of-two ratios, an order isomorphism of `ℝ`
  that is the identity off `[0,1]` and carries `s j` to `t j`.
-/

open CannonFloydParry

namespace CFPLib

/-! ### Sums of exactly `k` powers of two -/

/-- `SumPow k q`: the real number `q` is a sum of exactly `k` integer powers of two. -/
def SumPow (k : ℕ) (q : ℝ) : Prop :=
  ∃ l : List ℤ, l.length = k ∧ (l.map fun e => (2 : ℝ) ^ e).sum = q

lemma two_ne_zero' : (2 : ℝ) ≠ 0 := by norm_num

lemma SumPow.one (e : ℤ) : SumPow 1 ((2 : ℝ) ^ e) := ⟨[e], rfl, by simp⟩

lemma SumPow.cons {k : ℕ} {q : ℝ} (e : ℤ) (h : SumPow k q) :
    SumPow (k + 1) ((2 : ℝ) ^ e + q) := by
  obtain ⟨l, hl, hs⟩ := h
  exact ⟨e :: l, by simp [hl], by simp [hs]⟩

lemma halves (e : ℤ) : (2 : ℝ) ^ (e - 1) + (2 : ℝ) ^ (e - 1) = (2 : ℝ) ^ e := by
  have h : (2 : ℝ) ^ (e - 1) + (2 : ℝ) ^ (e - 1) = (2 : ℝ) ^ (1 : ℤ) * (2 : ℝ) ^ (e - 1) := by
    rw [zpow_one]; ring
  rw [h, ← zpow_add₀ two_ne_zero']
  congr 1
  ring

/-- Splitting one summand in half increases the number of summands by one. -/
lemma SumPow.split {k : ℕ} {q : ℝ} (h : SumPow k q) (hk : 1 ≤ k) : SumPow (k + 1) q := by
  obtain ⟨l, hl, hs⟩ := h
  cases l with
  | nil => simp at hl; omega
  | cons e rest =>
      refine ⟨(e - 1) :: (e - 1) :: rest, by simpa using hl, ?_⟩
      simp only [List.map_cons, List.sum_cons] at hs ⊢
      rw [← add_assoc, halves, hs]

lemma SumPow.le {k m : ℕ} {q : ℝ} (h : SumPow k q) (hk : 1 ≤ k) (hm : k ≤ m) : SumPow m q := by
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hlt | hge
      · exact (ih (by omega)).split (by omega)
      · have : k = m + 1 := by omega
        exact this ▸ h

lemma sumPow_zpow {m : ℕ} (hm : 1 ≤ m) (e : ℤ) : SumPow m ((2 : ℝ) ^ e) :=
  (SumPow.one e).le le_rfl hm

/-- A positive integer is a sum of exactly `k` integer powers of two as soon as `q < 2 ^ k`. -/
lemma sumPow_nat : ∀ (k q : ℕ), 1 ≤ q → q < 2 ^ k → SumPow k (q : ℝ) := by
  intro k
  induction k with
  | zero => intro q h1 h2; simp at h2; omega
  | succ k ih =>
      intro q h1 h2
      rcases Nat.lt_or_ge q (2 ^ k) with hlt | hge
      · have hk : 1 ≤ k := by
          by_contra hc
          have : k = 0 := by omega
          subst this
          simp at hlt
          omega
        exact (ih q h1 hlt).split hk
      · set r := q - 2 ^ k with hr
        have hqr : (q : ℝ) = (2 : ℝ) ^ (k : ℤ) + (r : ℝ) := by
          have hq : q = 2 ^ k + r := by omega
          rw [hq]
          push_cast
          rw [zpow_natCast]
        have hrlt : r < 2 ^ k := by
          have h3 : q < 2 ^ (k + 1) := h2
          have h4 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
          omega
        rcases Nat.eq_zero_or_pos r with hr0 | hrpos
        · have hq2 : (q : ℝ) = (2 : ℝ) ^ (k : ℤ) := by rw [hqr, hr0]; simp
          rw [hq2]
          exact sumPow_zpow (by omega) _
        · rw [hqr]
          exact SumPow.cons _ (ih r hrpos hrlt)

/-! ### Dyadic arithmetic -/

lemma isDyadic_zero : IsDyadic (0 : ℝ) := ⟨0, 0, by norm_num⟩

lemma isDyadic_add_c {u v : ℝ} (hu : IsDyadic u) (hv : IsDyadic v) : IsDyadic (u + v) := by
  obtain ⟨m, k, rfl⟩ := hu
  obtain ⟨m', k', rfl⟩ := hv
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k', ?_⟩
  push_cast
  field_simp
  ring

lemma isDyadic_zpow (a : ℤ) : IsDyadic ((2 : ℝ) ^ a) := by
  rcases le_or_gt 0 a with h | h
  · refine ⟨2 ^ a.toNat, 0, ?_⟩
    have h1 : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg h
    push_cast
    rw [pow_zero, div_one, ← zpow_natCast, h1]
  · refine ⟨1, (-a).toNat, ?_⟩
    have h1 : (((-a).toNat : ℕ) : ℤ) = -a := Int.toNat_of_nonneg (by omega)
    push_cast
    rw [eq_div_iff (by positivity), ← zpow_natCast (2 : ℝ) ((-a).toNat), ← zpow_add₀ two_ne_zero',
      h1]
    simp

lemma isDyadic_natDiv (j M : ℕ) : IsDyadic ((j : ℝ) * (2 : ℝ) ^ (-(M : ℤ))) := by
  refine ⟨j, M, ?_⟩
  rw [zpow_neg, ← zpow_natCast (2 : ℝ) M]
  field_simp
  norm_cast

/-- A scaled sum of powers of two is dyadic. -/
lemma isDyadic_scaled_sum (l : List ℤ) (M : ℕ) :
    IsDyadic (((l.map fun e => (2 : ℝ) ^ e).sum) * (2 : ℝ) ^ (-(M : ℤ))) := by
  induction l with
  | nil => simpa using isDyadic_zero
  | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons, add_mul]
      refine isDyadic_add_c ?_ ih
      rw [← zpow_add₀ two_ne_zero']
      exact isDyadic_zpow _

/-! ### Assembling the exponent list -/

/-- A list all of whose entries vanish reads off as `0` at every index. -/
lemma getD_eq_zero_of_all {l : List ℤ} (h : ∀ e ∈ l, e = 0) (j : ℕ) : l.getD j 0 = 0 := by
  rcases Nat.lt_or_ge j l.length with hj | hj
  · rw [List.getD_eq_getElem l 0 hj]
    exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default l 0 hj]

/-- One gap's worth of exponents: the all-zero list when the gap keeps its length, and a
representation of the target length as a sum of powers of two otherwise. -/
lemma exists_block (k q : ℕ) (hq : 1 ≤ q) (hlt : q < 2 ^ k) :
    ∃ l : List ℤ, l.length = k ∧ (l.map fun e => (2 : ℝ) ^ e).sum = (q : ℝ) ∧
      (k = q → ∀ e ∈ l, e = 0) := by
  by_cases hkq : k = q
  · refine ⟨List.replicate k 0, by simp, ?_, fun _ e he => List.eq_of_mem_replicate he⟩
    simp [hkq]
  · obtain ⟨l, hl, hls⟩ := sumPow_nat k q hq hlt
    exact ⟨l, hl, hls, fun h => absurd h hkq⟩

/-- Concatenating the per-gap representations gives one exponent list whose prefix sums hit
every target partition point, and which is identically zero on any gap that keeps its length. -/
lemma exists_exponents : ∀ (n : ℕ) (k q : ℕ → ℕ), (∀ i, i < n → 1 ≤ k i) →
    (∀ i, i < n → 1 ≤ q i) → (∀ i, i < n → q i < 2 ^ (k i)) →
    ∃ L : List ℤ, L.length = ∑ i ∈ Finset.range n, k i ∧
      (∀ m, m ≤ n → ((L.take (∑ i ∈ Finset.range m, k i)).map fun e => (2 : ℝ) ^ e).sum
        = ∑ i ∈ Finset.range m, (q i : ℝ)) ∧
      (∀ i, i < n → k i = q i → ∀ j, ∑ i' ∈ Finset.range i, k i' ≤ j →
        j < ∑ i' ∈ Finset.range (i + 1), k i' → L.getD j 0 = 0) := by
  intro n
  induction n with
  | zero =>
      intro k q _ _ _
      refine ⟨[], by simp, ?_, ?_⟩
      · intro m hm
        have : m = 0 := by omega
        subst this
        simp
      · intro i hi
        omega
  | succ n ih =>
      intro k q hk hq hlt
      obtain ⟨L', hlen', hsum', hz'⟩ := ih k q (fun i hi => hk i (by omega))
        (fun i hi => hq i (by omega)) (fun i hi => hlt i (by omega))
      obtain ⟨l, hl, hls, hlz⟩ := exists_block (k n) (q n) (hq n (by omega)) (hlt n (by omega))
      have hfull : (L' ++ l).length = ∑ i ∈ Finset.range (n + 1), k i := by
        rw [List.length_append, hlen', hl, Finset.sum_range_succ]
      refine ⟨L' ++ l, hfull, ?_, ?_⟩
      · intro m hm
        rcases Nat.lt_or_ge m (n + 1) with h | h
        · have hmn : m ≤ n := by omega
          have hle : ∑ i ∈ Finset.range m, k i ≤ L'.length := by
            rw [hlen']
            have hsub : Finset.range m ⊆ Finset.range n := Finset.range_subset_range.mpr hmn
            exact Finset.sum_le_sum_of_subset hsub
          rw [List.take_append_of_le_length hle]
          exact hsum' m (by omega)
        · have hmn : m = n + 1 := by omega
          subst hmn
          have hLfull : L'.take (∑ i ∈ Finset.range n, k i) = L' := by
            rw [← hlen', List.take_length]
          have hL' : ((L'.map fun e => (2 : ℝ) ^ e).sum) = ∑ i ∈ Finset.range n, (q i : ℝ) := by
            have hh := hsum' n le_rfl
            rwa [hLfull] at hh
          rw [← hfull, List.take_length, List.map_append, List.sum_append, hL', hls,
            Finset.sum_range_succ]
      · intro i hi hkq j hj1 hj2
        rcases Nat.lt_or_ge i n with h | h
        · -- the block lies inside `L'`
          have hjlt : j < L'.length := by
            rw [hlen']
            have hsub : Finset.range (i + 1) ⊆ Finset.range n :=
              Finset.range_subset_range.mpr (by omega)
            have := Finset.sum_le_sum_of_subset (f := k) hsub
            omega
          rw [List.getD_append _ _ _ _ hjlt]
          exact hz' i h hkq j hj1 hj2
        · -- the last block, which is all zeros
          have hin : i = n := by omega
          subst hin
          have hjge : L'.length ≤ j := by rw [hlen']; exact hj1
          rw [List.getD_append_right _ _ _ _ hjge]
          exact getD_eq_zero_of_all (hlz hkq) _

/-! ### The clamp ("ramp") function -/

/-- `ramp a b z` is the length of `[a, b] ∩ (-∞, z]`, for `a ≤ b`. -/
noncomputable def ramp (a b z : ℝ) : ℝ := min (max z a) b - a

lemma ramp_of_le_left {a b z : ℝ} (h : z ≤ a) (hab : a ≤ b) : ramp a b z = 0 := by
  unfold ramp
  rw [max_eq_right h, min_eq_left hab]
  ring

lemma ramp_of_right_le {a b z : ℝ} (h : b ≤ z) (hab : a ≤ b) : ramp a b z = b - a := by
  unfold ramp
  rw [max_eq_left (hab.trans h), min_eq_right h]

lemma ramp_of_mem {a b z : ℝ} (h1 : a ≤ z) (h2 : z ≤ b) : ramp a b z = z - a := by
  unfold ramp
  rw [max_eq_left h1, min_eq_left h2]

lemma ramp_mono (a b : ℝ) : Monotone (ramp a b) := by
  intro z w h
  unfold ramp
  have : max z a ≤ max w a := max_le_max h le_rfl
  exact sub_le_sub_right (min_le_min this le_rfl) a

/-! ### Piecewise-linear data -/

/-- The data of a dyadic piecewise-linear order isomorphism of `[0,1]`: breakpoints `s`,
targets `t`, and slope exponents `e`. -/
structure PLData where
  N : ℕ
  s : ℕ → ℝ
  t : ℕ → ℝ
  e : ℕ → ℤ
  hN : 1 ≤ N
  hs0 : s 0 = 0
  hsN : s N = 1
  ht0 : t 0 = 0
  htN : t N = 1
  hsmono : ∀ j, j < N → s j < s (j + 1)
  hslope : ∀ j, j < N → t (j + 1) - t j = (2 : ℝ) ^ (e j) * (s (j + 1) - s j)
  hsdy : ∀ j, j ≤ N → IsDyadic (s j)
  htdy : ∀ j, j ≤ N → IsDyadic (t j)

namespace PLData

variable (D : PLData)

lemma s_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.N) : D.s i ≤ D.s j := by
  induction j with
  | zero => have : i = 0 := by omega
            simp [this]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact (ih (by omega) (by omega)).trans (le_of_lt (D.hsmono j (by omega)))
      · have : i = j + 1 := by omega
        simp [this]

lemma s_nonneg {j : ℕ} (hj : j ≤ D.N) : 0 ≤ D.s j := by
  have := D.s_le (Nat.zero_le j) hj
  rwa [D.hs0] at this

lemma s_le_one {j : ℕ} (hj : j ≤ D.N) : D.s j ≤ 1 := by
  have := D.s_le hj le_rfl
  rwa [D.hsN] at this

lemma t_sub {j : ℕ} (hj : j < D.N) : D.t j < D.t (j + 1) := by
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (D.e j) := zpow_pos (by norm_num) _
  have h2 : 0 < D.s (j + 1) - D.s j := sub_pos.mpr (D.hsmono j hj)
  have := D.hslope j hj
  nlinarith

lemma t_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ D.N) : D.t i ≤ D.t j := by
  induction j with
  | zero => have : i = 0 := by omega
            simp [this]
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · exact (ih (by omega) (by omega)).trans (le_of_lt (D.t_sub (by omega)))
      · have : i = j + 1 := by omega
        simp [this]

/-- Partial sums of the target gaps: `∑_{j < k} (t (j+1) - t j) = t k`. -/
lemma sum_gaps (k : ℕ) : ∑ j ∈ Finset.range k, (D.t (j + 1) - D.t j) = D.t k - D.t 0 :=
  Finset.sum_range_sub (fun j => D.t j) k

/-- The underlying function. -/
noncomputable def fn (z : ℝ) : ℝ :=
  min z 0 + (∑ j ∈ Finset.range D.N, (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z)
    + max (z - 1) 0

lemma fn_monotone : Monotone D.fn := by
  intro z w hzw
  unfold fn
  have h1 : min z 0 ≤ min w 0 := min_le_min hzw le_rfl
  have h2 : ∀ j ∈ Finset.range D.N,
      (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
        ≤ (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) w := fun j _ =>
    mul_le_mul_of_nonneg_left (ramp_mono _ _ hzw) (le_of_lt (zpow_pos (by norm_num) _))
  have h3 : max (z - 1) 0 ≤ max (w - 1) 0 := max_le_max (sub_le_sub_right hzw 1) le_rfl
  exact add_le_add (add_le_add h1 (Finset.sum_le_sum h2)) h3

lemma fn_of_nonpos {z : ℝ} (hz : z ≤ 0) : D.fn z = z := by
  unfold fn
  have h1 : min z 0 = z := min_eq_left hz
  have h2 : max (z - 1) 0 = 0 := max_eq_right (by linarith)
  have h3 : ∀ j ∈ Finset.range D.N,
      (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z = 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [ramp_of_le_left (hz.trans (D.s_nonneg (by omega)))
      (le_of_lt (D.hsmono j hj)), mul_zero]
  rw [h1, h2, Finset.sum_congr rfl h3]
  simp

lemma total_mass : ∑ j ∈ Finset.range D.N,
    (2 : ℝ) ^ (D.e j) * (D.s (j + 1) - D.s j) = 1 := by
  have h : ∀ j ∈ Finset.range D.N,
      (2 : ℝ) ^ (D.e j) * (D.s (j + 1) - D.s j) = D.t (j + 1) - D.t j := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact (D.hslope j hj).symm
  rw [Finset.sum_congr rfl h, D.sum_gaps D.N, D.ht0, D.htN]
  ring

lemma fn_of_one_le {z : ℝ} (hz : 1 ≤ z) : D.fn z = z := by
  unfold fn
  have h1 : min z 0 = 0 := min_eq_right (by linarith)
  have h2 : max (z - 1) 0 = z - 1 := max_eq_left (by linarith)
  have h3 : ∀ j ∈ Finset.range D.N,
      (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
        = (2 : ℝ) ^ (D.e j) * (D.s (j + 1) - D.s j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [ramp_of_right_le ((D.s_le_one (by omega)).trans hz) (le_of_lt (D.hsmono j hj))]
  rw [h1, h2, Finset.sum_congr rfl h3, D.total_mass]
  ring

/-- The affine formula on the `k`-th piece. -/
lemma fn_piece {k : ℕ} (hk : k < D.N) {z : ℝ} (hz1 : D.s k ≤ z) (hz2 : z ≤ D.s (k + 1)) :
    D.fn z = D.t k + (2 : ℝ) ^ (D.e k) * (z - D.s k) := by
  have hz0 : 0 ≤ z := (D.s_nonneg (by omega)).trans hz1
  have hz1' : z ≤ 1 := hz2.trans (D.s_le_one (by omega))
  unfold fn
  have hmin : min z 0 = 0 := min_eq_right hz0
  have hmax : max (z - 1) 0 = 0 := max_eq_right (by linarith)
  rw [hmin, hmax]
  -- split the sum at `k`
  have hsplit : ∑ j ∈ Finset.range D.N, (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
      = (∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z)
        + ∑ j ∈ Finset.Ico (k + 1) D.N,
            (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le (k + 1)) (by omega)]
  have htail : ∑ j ∈ Finset.Ico (k + 1) D.N,
      (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hzs : z ≤ D.s j := hz2.trans (D.s_le (by omega) (by omega))
    rw [ramp_of_le_left hzs (le_of_lt (D.hsmono j (by omega))), mul_zero]
  have hhead : ∑ j ∈ Finset.range k, (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
      = D.t k := by
    have h : ∀ j ∈ Finset.range k, (2 : ℝ) ^ (D.e j) * ramp (D.s j) (D.s (j + 1)) z
        = D.t (j + 1) - D.t j := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hsj : D.s (j + 1) ≤ z := (D.s_le (by omega) (by omega)).trans hz1
      rw [ramp_of_right_le hsj (le_of_lt (D.hsmono j (by omega)))]
      exact (D.hslope j (by omega)).symm
    rw [Finset.sum_congr rfl h, D.sum_gaps k, D.ht0]
    ring
  rw [hsplit, htail, Finset.sum_range_succ, hhead, ramp_of_mem hz1 hz2]
  ring

/-- The largest breakpoint index at or below a point of `[0,1]`. -/
lemma exists_max_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ k, k ≤ D.N ∧ D.s k ≤ z ∧ ∀ j, j ≤ D.N → D.s j ≤ z → j ≤ k := by
  classical
  have hN := D.hN
  set S : Finset ℕ := (Finset.range (D.N + 1)).filter (fun j => D.s j ≤ z) with hS
  have h0 : 0 ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [D.hs0]; exact hz0⟩
  have hne : S.Nonempty := ⟨0, h0⟩
  refine ⟨S.max' hne, ?_, ?_, ?_⟩
  · have := (Finset.mem_filter.mp (S.max'_mem hne)).1
    rw [Finset.mem_range] at this
    omega
  · exact (Finset.mem_filter.mp (S.max'_mem hne)).2
  · intro j hj hjz
    refine S.le_max' _ ?_
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hjz⟩

/-- Every point of `[0,1]` lies on some piece. -/
lemma exists_piece_c {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ k, k < D.N ∧ D.s k ≤ z ∧ z ≤ D.s (k + 1) := by
  have hN := D.hN
  obtain ⟨k, hkN, hkz, hmax⟩ := D.exists_max_le hz0 hz1
  rcases Nat.lt_or_ge k D.N with hlt | hge
  · refine ⟨k, hlt, hkz, ?_⟩
    by_contra hc
    push_neg at hc
    have := hmax (k + 1) (by omega) (le_of_lt hc)
    omega
  · -- `k = N`, so `z = 1`; use the last piece
    have hkN' : k = D.N := by omega
    have hz : z = 1 := by
      have h : D.s D.N ≤ z := by rw [← hkN']; exact hkz
      rw [D.hsN] at h
      linarith
    refine ⟨D.N - 1, by omega, ?_, ?_⟩
    · have h : D.s (D.N - 1) ≤ D.s D.N := D.s_le (by omega) le_rfl
      rw [D.hsN] at h
      linarith
    · have h : D.N - 1 + 1 = D.N := by omega
      rw [h, D.hsN, hz]

/-- An interval inside `[0,1]` whose interior avoids every breakpoint lies inside one piece. -/
lemma exists_piece_of_gap {x y : ℝ} (hx0 : 0 ≤ x) (hy1 : y ≤ 1) (hxy : x < y)
    (hgap : ∀ j, j ≤ D.N → D.s j ∉ Set.Ioo x y) :
    ∃ k, k < D.N ∧ D.s k ≤ x ∧ y ≤ D.s (k + 1) := by
  have hN := D.hN
  obtain ⟨k, hkN, hkz, hmax⟩ := D.exists_max_le hx0 (le_of_lt (lt_of_lt_of_le hxy hy1))
  have hklt : k < D.N := by
    rcases Nat.lt_or_ge k D.N with h | h
    · exact h
    · exfalso
      have hkN' : k = D.N := by omega
      have h1 : D.s D.N ≤ x := by rw [← hkN']; exact hkz
      rw [D.hsN] at h1
      linarith
  refine ⟨k, hklt, hkz, ?_⟩
  by_contra hc
  push_neg at hc
  have hgt : x < D.s (k + 1) := by
    by_contra hle
    push_neg at hle
    have := hmax (k + 1) (by omega) hle
    omega
  exact hgap (k + 1) (by omega) ⟨hgt, hc⟩

/-- The map takes each breakpoint to its target. -/
lemma fn_s {j : ℕ} (hj : j ≤ D.N) : D.fn (D.s j) = D.t j := by
  rcases Nat.lt_or_ge j D.N with h | h
  · rw [D.fn_piece h le_rfl (le_of_lt (D.hsmono j h))]; ring
  · have hj' : j = D.N := by omega
    rw [hj', D.hsN, D.fn_of_one_le (le_refl (1 : ℝ)), D.htN]

/-! ### The inverse -/

/-- The inverse data: swap breakpoints and targets, negate the slope exponents. -/
def symm : PLData where
  N := D.N
  s := D.t
  t := D.s
  e := fun j => -(D.e j)
  hN := D.hN
  hs0 := D.ht0
  hsN := D.htN
  ht0 := D.hs0
  htN := D.hsN
  hsmono := fun j hj => D.t_sub hj
  hslope := by
    intro j hj
    have hne : ((2 : ℝ) ^ (D.e j)) ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
    rw [zpow_neg, D.hslope j hj, inv_mul_cancel_left₀ hne]
  hsdy := D.htdy
  htdy := D.hsdy

@[simp] lemma symm_N : D.symm.N = D.N := rfl
@[simp] lemma symm_s : D.symm.s = D.t := rfl
@[simp] lemma symm_t : D.symm.t = D.s := rfl
@[simp] lemma symm_e (j : ℕ) : D.symm.e j = -(D.e j) := rfl

/-- The image of a piece is the corresponding target piece. -/
lemma fn_mem_piece {k : ℕ} (hk : k < D.N) {z : ℝ} (hz1 : D.s k ≤ z) (hz2 : z ≤ D.s (k + 1)) :
    D.t k ≤ D.fn z ∧ D.fn z ≤ D.t (k + 1) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (D.e k) := zpow_pos (by norm_num) _
  have hsl := D.hslope k hk
  rw [D.fn_piece hk hz1 hz2]
  constructor
  · nlinarith [sub_nonneg.mpr hz1]
  · nlinarith [sub_nonneg.mpr hz2]

lemma symm_fn_fn (z : ℝ) : D.symm.fn (D.fn z) = z := by
  rcases le_or_gt z 0 with hz | hz
  · rw [D.fn_of_nonpos hz, D.symm.fn_of_nonpos hz]
  rcases le_or_gt 1 z with hz1 | hz1
  · rw [D.fn_of_one_le hz1, D.symm.fn_of_one_le hz1]
  obtain ⟨k, hk, h1, h2⟩ := D.exists_piece_c (le_of_lt hz) (le_of_lt hz1)
  obtain ⟨ha, hb⟩ := D.fn_mem_piece hk h1 h2
  have hne : ((2 : ℝ) ^ (D.e k)) ≠ 0 := ne_of_gt (zpow_pos (by norm_num) _)
  rw [D.symm.fn_piece (show k < D.symm.N from hk) ha hb, D.fn_piece hk h1 h2]
  simp only [symm_t, symm_s, symm_e]
  have hcollapse : D.t k + (2 : ℝ) ^ (D.e k) * (z - D.s k) - D.t k
      = (2 : ℝ) ^ (D.e k) * (z - D.s k) := by ring
  rw [hcollapse, zpow_neg, inv_mul_cancel_left₀ hne]
  ring

lemma symm_symm_fn : D.symm.symm.fn = D.fn := by
  funext z
  simp [fn, symm]

lemma fn_symm_fn (y : ℝ) : D.fn (D.symm.fn y) = y := by
  have h := D.symm.symm_fn_fn y
  rwa [D.symm_symm_fn] at h

lemma fn_injective : Function.Injective D.fn :=
  Function.LeftInverse.injective D.symm_fn_fn

lemma fn_surjective : Function.Surjective D.fn := fun y => ⟨D.symm.fn y, D.fn_symm_fn y⟩

lemma fn_strictMono : StrictMono D.fn :=
  D.fn_monotone.strictMono_of_injective D.fn_injective

/-- The order isomorphism of the line determined by the data. -/
noncomputable def iso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective D.fn D.fn_strictMono D.fn_surjective

@[simp] lemma iso_apply (z : ℝ) : D.iso z = D.fn z := rfl

/-! ### The data defines an element of the line model -/

lemma isThompsonLine_iso : IsThompsonLine D.iso := by
  classical
  refine ⟨fun x hx => D.fn_of_nonpos hx, fun x hx => D.fn_of_one_le hx,
    (Finset.range (D.N + 1)).image D.s, ?_, ?_⟩
  · intro b hb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    rw [Finset.mem_range] at hj
    exact D.hsdy j (by omega)
  · intro x y hxy hgap
    have hgap' : ∀ j, j ≤ D.N → D.s j ∉ Set.Ioo x y := by
      intro j hj hmem
      have hB : D.s j ∈ (((Finset.range (D.N + 1)).image D.s : Finset ℝ) : Set ℝ) := by
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image]
        exact ⟨j, by simp; omega, rfl⟩
      have hx : D.s j ∈ Set.Ioo x y ∩
          (((Finset.range (D.N + 1)).image D.s : Finset ℝ) : Set ℝ) := ⟨hmem, hB⟩
      rw [hgap] at hx
      exact hx
    rcases le_or_gt y 0 with hy | hy
    · exact ⟨0, 0, fun z hz => by
        rw [iso_apply, D.fn_of_nonpos (hz.2.trans hy)]; simp⟩
    rcases le_or_gt 1 x with hx1 | hx1
    · exact ⟨0, 0, fun z hz => by
        rw [iso_apply, D.fn_of_one_le (hx1.trans hz.1)]; simp⟩
    have hx0 : 0 ≤ x := by
      by_contra hc
      push_neg at hc
      exact hgap' 0 (by omega) (by rw [D.hs0]; exact ⟨hc, hy⟩)
    have hy1 : y ≤ 1 := by
      by_contra hc
      push_neg at hc
      exact hgap' D.N le_rfl (by rw [D.hsN]; exact ⟨hx1, hc⟩)
    obtain ⟨k, hk, h1, h2⟩ := D.exists_piece_of_gap hx0 hy1 hxy hgap'
    refine ⟨D.e k, D.t k - 2 ^ (D.e k) * D.s k, fun z hz => ?_⟩
    rw [iso_apply, D.fn_piece hk (h1.trans hz.1) (hz.2.trans h2)]
    ring

/-! ### Stretches where the data is already the identity -/

lemma t_eq_s_of_zero {a b : ℕ} (hb : b ≤ D.N) (hstart : D.t a = D.s a)
    (hzero : ∀ j, a ≤ j → j < b → D.e j = 0) :
    ∀ j, a ≤ j → j ≤ b → D.t j = D.s j := by
  intro j
  induction j with
  | zero =>
      intro hj1 _
      have : a = 0 := by omega
      rw [← this]; exact hstart
  | succ j ih =>
      intro hj1 hj2
      rcases Nat.lt_or_ge a (j + 1) with h | h
      · have hprev := ih (by omega) (by omega)
        have hsl := D.hslope j (by omega)
        rw [hzero j (by omega) (by omega), zpow_zero, one_mul] at hsl
        linarith
      · have : a = j + 1 := by omega
        rw [← this]; exact hstart

lemma fn_id_on {a b : ℕ} (ha : a ≤ b) (hb : b ≤ D.N)
    (hts : ∀ j, a ≤ j → j ≤ b → D.t j = D.s j)
    (hzero : ∀ j, a ≤ j → j < b → D.e j = 0) :
    ∀ z, D.s a ≤ z → z ≤ D.s b → D.fn z = z := by
  intro z hz1 hz2
  have hz0 : 0 ≤ z := (D.s_nonneg (by omega)).trans hz1
  have hz1' : z ≤ 1 := hz2.trans (D.s_le_one hb)
  obtain ⟨k, hk, h1, h2⟩ := D.exists_piece_c hz0 hz1'
  rcases Nat.lt_or_ge k a with hka | hka
  · have hle : D.s (k + 1) ≤ D.s a := D.s_le (by omega) (by omega)
    have hzeq : z = D.s a := le_antisymm (h2.trans hle) hz1
    rw [hzeq, D.fn_s (by omega), hts a le_rfl ha]
  · rcases Nat.lt_or_ge k b with hkb | hkb
    · rw [D.fn_piece hk h1 h2, hzero k hka hkb, hts k hka (by omega), zpow_zero]
      ring
    · have hle : D.s b ≤ D.s k := D.s_le hkb (by omega)
      have hzeq : z = D.s b := le_antisymm hz2 (hle.trans h1)
      rw [hzeq, D.fn_s hb, hts b ha le_rfl]

lemma iso_of_le_zero : ∀ x ≤ (0 : ℝ), D.iso x = x := fun x hx => D.fn_of_nonpos hx

lemma iso_of_one_le : ∀ x, (1 : ℝ) ≤ x → D.iso x = x := fun x hx => D.fn_of_one_le hx

end PLData

/-! ### Transfer to the unit-interval model -/

/-- Restricting a line-model element to `[0,1]` gives an interval-model element. -/
lemma isThompson_restrict {L : ℝ ≃o ℝ} (hlo : ∀ x ≤ (0 : ℝ), L x = x)
    (hhi : ∀ x, (1 : ℝ) ≤ x → L x = x)
    (hB : ∃ B : Finset ℝ, (∀ b ∈ B, IsDyadic b) ∧ ∀ x y : ℝ, x < y →
      Set.Ioo x y ∩ (B : Set ℝ) = ∅ →
        ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc x y, L z = 2 ^ n * z + c) :
    IsThompson (restrict L hlo hhi) := by
  obtain ⟨B, hBdy, hBaff⟩ := hB
  refine ⟨B, hBdy, fun x y hxy hgap => ?_⟩
  obtain ⟨n, c, hc⟩ := hBaff (x : ℝ) (y : ℝ) hxy hgap
  exact ⟨n, c, fun z hz => hc (z : ℝ) hz⟩

/-- The interval-model element determined by piecewise-linear data. -/
noncomputable def PLData.uiMap (D : PLData) : UI ≃o UI :=
  restrict D.iso D.iso_of_le_zero D.iso_of_one_le

lemma PLData.isThompson_uiMap (D : PLData) : IsThompson D.uiMap := by
  refine isThompson_restrict D.iso_of_le_zero D.iso_of_one_le ?_
  obtain ⟨_, _, hB⟩ := D.isThompsonLine_iso
  exact hB

lemma PLData.uiMap_mem_F (D : PLData) : D.uiMap ∈ F :=
  mem_F_of_isThompson D.isThompson_uiMap

@[simp] lemma PLData.uiMap_coe (D : PLData) (z : UI) : ((D.uiMap z : UI) : ℝ) = D.fn (z : ℝ) :=
  rfl

/-! ### From a pair of integer partitions to the data -/

lemma isDyadic_den {v : ℝ} (h : IsDyadic v) :
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

lemma pow_bound (m : ℕ) : 2 * m + 2 < 2 ^ (m + 2) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      have h : 2 ^ (m + 1 + 2) = 2 * 2 ^ (m + 2) := by ring
      omega

lemma sum_take_succ (L : List ℤ) {j : ℕ} (hj : j < L.length) :
    ((L.take (j + 1)).map fun e => (2 : ℝ) ^ e).sum
      = ((L.take j).map fun e => (2 : ℝ) ^ e).sum + (2 : ℝ) ^ (L.getD j 0) := by
  rw [List.take_succ, List.map_append, List.sum_append]
  congr 1
  rw [List.getElem?_eq_getElem hj, List.getD_eq_getElem L 0 hj]
  simp

/-- The core construction.  Two integer partitions of `[0, 2 ^ M₀]` with the same number of
parts give a dyadic piecewise-linear map of `[0,1]` carrying the first to the second, and that
map is the identity on any part the two partitions share. -/
theorem exists_PLData_of_int (n : ℕ) (hn : 1 ≤ n) (M₀ : ℕ) (A B : ℕ → ℤ)
    (hA0 : A 0 = 0) (hAn : A n = 2 ^ M₀) (hB0 : B 0 = 0) (hBn : B n = 2 ^ M₀)
    (hAm : ∀ i, i < n → A i < A (i + 1)) (hBm : ∀ i, i < n → B i < B (i + 1)) :
    ∃ D : PLData,
      (∀ i, i ≤ n → D.fn ((A i : ℝ) / 2 ^ M₀) = (B i : ℝ) / 2 ^ M₀) ∧
      (∀ i, i < n → A i = B i → A (i + 1) = B (i + 1) →
        ∀ z, (A i : ℝ) / 2 ^ M₀ ≤ z → z ≤ (A (i + 1) : ℝ) / 2 ^ M₀ → D.fn z = z) := by
  classical
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ, R = M₀ + 2 := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = M₀ + R := ⟨_, rfl⟩
  have hMR : M < 2 ^ R := by
    have h := pow_bound M₀
    rw [hMdef, hRdef]
    omega
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℕ, ∀ i, K i = (A (i + 1) - A i).toNat * 2 ^ R :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → ℕ, ∀ i, Q i = (B (i + 1) - B i).toNat * 2 ^ R :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ, ∀ i, P i = ∑ i' ∈ Finset.range i, K i' := ⟨_, fun _ => rfl⟩
  obtain ⟨PQ, hPQ⟩ : ∃ PQ : ℕ → ℕ, ∀ i, PQ i = ∑ i' ∈ Finset.range i, Q i' := ⟨_, fun _ => rfl⟩
  -- power bookkeeping
  have hzM : (2 : ℝ) ^ (-(M : ℤ)) = ((2 : ℝ) ^ (M : ℕ))⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hRM : (2 : ℝ) ^ (R : ℕ) * (2 : ℝ) ^ (-(M : ℤ)) = ((2 : ℝ) ^ (M₀ : ℕ))⁻¹ := by
    have h1 : ((2 : ℝ) ^ (M₀ : ℕ)) ≠ 0 := by positivity
    have h2 : ((2 : ℝ) ^ (R : ℕ)) ≠ 0 := by positivity
    rw [hzM, hMdef, pow_add]
    field_simp
  -- each block accounts for one gap
  have hblock : ∀ (C : ℕ → ℤ), (∀ i, i < n → C i < C (i + 1)) → ∀ i, i < n →
      (((C (i + 1) - C i).toNat * 2 ^ R : ℕ) : ℝ) * 2 ^ (-(M : ℤ))
        = (C (i + 1) : ℝ) / 2 ^ M₀ - (C i : ℝ) / 2 ^ M₀ := by
    intro C hC i hi
    have h0 : (0 : ℤ) ≤ C (i + 1) - C i := by have := hC i hi; omega
    have hcast : (((C (i + 1) - C i).toNat : ℕ) : ℝ) = (C (i + 1) : ℝ) - (C i : ℝ) := by
      have h := Int.toNat_of_nonneg h0
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
    have hmain : ((((C (i + 1) - C i).toNat * 2 ^ R : ℕ)) : ℝ)
        = ((C (i + 1) : ℝ) - (C i : ℝ)) * 2 ^ (R : ℕ) := by
      push_cast
      rw [hcast]
    rw [hmain, mul_assoc, hRM]
    ring
  have hblockA : ∀ i, i < n → (K i : ℝ) * 2 ^ (-(M : ℤ))
      = (A (i + 1) : ℝ) / 2 ^ M₀ - (A i : ℝ) / 2 ^ M₀ := by
    intro i hi; rw [hK i]; exact hblock A hAm i hi
  have hblockB : ∀ i, i < n → (Q i : ℝ) * 2 ^ (-(M : ℤ))
      = (B (i + 1) : ℝ) / 2 ^ M₀ - (B i : ℝ) / 2 ^ M₀ := by
    intro i hi; rw [hQ i]; exact hblock B hBm i hi
  -- prefix sums track the partition points
  have hPX : ∀ i, i ≤ n → (P i : ℝ) * 2 ^ (-(M : ℤ)) = (A i : ℝ) / 2 ^ M₀ := by
    intro i
    induction i with
    | zero => intro _; rw [hP 0]; simp [hA0]
    | succ i ih =>
        intro hi
        have hPs : P (i + 1) = P i + K i := by rw [hP, hP, Finset.sum_range_succ]
        rw [hPs, Nat.cast_add, add_mul, ih (by omega), hblockA i (by omega)]
        ring
  have hPY : ∀ i, i ≤ n → (PQ i : ℝ) * 2 ^ (-(M : ℤ)) = (B i : ℝ) / 2 ^ M₀ := by
    intro i
    induction i with
    | zero => intro _; rw [hPQ 0]; simp [hB0]
    | succ i ih =>
        intro hi
        have hPs : PQ (i + 1) = PQ i + Q i := by rw [hPQ, hPQ, Finset.sum_range_succ]
        rw [hPs, Nat.cast_add, add_mul, ih (by omega), hblockB i (by omega)]
        ring
  -- the grid has exactly `2 ^ M` steps
  have hone : (((2 : ℤ) ^ M₀ : ℤ) : ℝ) / 2 ^ (M₀ : ℕ) = 1 := by
    have h2 : ((2 : ℝ) ^ (M₀ : ℕ)) ≠ 0 := by positivity
    push_cast
    field_simp
  have hMne : ((2 : ℝ) ^ (M : ℕ)) ≠ 0 := by positivity
  have hsolve : ∀ c : ℕ, (c : ℝ) * 2 ^ (-(M : ℤ)) = 1 → c = 2 ^ M := by
    intro c hc
    have h := congrArg (fun x : ℝ => x * (2 : ℝ) ^ (M : ℕ)) hc
    simp only [one_mul] at h
    rw [hzM, mul_assoc, inv_mul_cancel₀ hMne, mul_one] at h
    exact_mod_cast h
  have hPn : P n = 2 ^ M := by
    have h := hPX n le_rfl
    rw [hAn, hone] at h
    exact hsolve _ h
  have hPQn : PQ n = 2 ^ M := by
    have h := hPY n le_rfl
    rw [hBn, hone] at h
    exact hsolve _ h
  -- block sizes and the bound that makes the arithmetic lemma apply
  have hKlb : ∀ i, i < n → 2 ^ R ≤ K i := by
    intro i hi
    rw [hK i]
    have h := hAm i hi
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hQlb : ∀ i, i < n → 1 ≤ Q i := by
    intro i hi
    rw [hQ i]
    have h := hBm i hi
    have h1 : 0 < (B (i + 1) - B i).toNat := by omega
    have h2 : 0 < 2 ^ R := by positivity
    have := Nat.mul_pos h1 h2
    omega
  have hQub : ∀ i, i < n → Q i ≤ 2 ^ M := by
    intro i hi
    rw [← hPQn, hPQ n]
    exact Finset.single_le_sum (f := Q) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
  have hQlt : ∀ i, i < n → Q i < 2 ^ (K i) := by
    intro i hi
    have h1 : Q i ≤ 2 ^ M := hQub i hi
    have h2 : (2 : ℕ) ^ M < 2 ^ (2 ^ R) := Nat.pow_lt_pow_right (by norm_num) hMR
    have h3 : (2 : ℕ) ^ (2 ^ R) ≤ 2 ^ (K i) :=
      Nat.pow_le_pow_right (by norm_num) (hKlb i hi)
    omega
  -- the exponent list
  obtain ⟨L, hLlen, hLsum, hLzero⟩ := exists_exponents n K Q
    (fun i hi => le_trans (Nat.one_le_two_pow) (hKlb i hi)) hQlb hQlt
  have hLlen' : L.length = 2 ^ M := by rw [hLlen, ← hP n, hPn]
  -- the prefix sums of the exponent list are the target partition points
  have hTval : ∀ i, i ≤ n →
      ((L.take (P i)).map fun e => (2 : ℝ) ^ e).sum * 2 ^ (-(M : ℤ)) = (B i : ℝ) / 2 ^ M₀ := by
    intro i hi
    have h := hLsum i hi
    rw [← hP i] at h
    rw [h]
    have h2 : ∑ i' ∈ Finset.range i, (Q i' : ℝ) = ((PQ i : ℕ) : ℝ) := by
      rw [hPQ i]; push_cast; ring
    rw [h2]
    exact hPY i hi
  have hPle : ∀ i, i ≤ n → P i ≤ 2 ^ M := by
    intro i hi
    rw [← hPn, hP i, hP n]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hi)
  -- the data
  obtain ⟨D, hDN, hDs, hDt, hDe⟩ : ∃ D : PLData, D.N = 2 ^ M ∧
      (∀ j, D.s j = (j : ℝ) * 2 ^ (-(M : ℤ))) ∧
      (∀ j, D.t j = ((L.take j).map fun e => (2 : ℝ) ^ e).sum * 2 ^ (-(M : ℤ))) ∧
      (∀ j, D.e j = L.getD j 0) := by
    refine ⟨{ N := 2 ^ M
              s := fun j => (j : ℝ) * 2 ^ (-(M : ℤ))
              t := fun j => ((L.take j).map fun e => (2 : ℝ) ^ e).sum * 2 ^ (-(M : ℤ))
              e := fun j => L.getD j 0
              hN := Nat.one_le_two_pow
              hs0 := by simp
              hsN := ?_
              ht0 := by simp
              htN := ?_
              hsmono := ?_
              hslope := ?_
              hsdy := fun j _ => isDyadic_natDiv j M
              htdy := fun j _ => isDyadic_scaled_sum _ M },
      rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    · show ((2 ^ M : ℕ) : ℝ) * 2 ^ (-(M : ℤ)) = 1
      rw [hzM]
      push_cast
      field_simp
    · show ((L.take (2 ^ M)).map fun e => (2 : ℝ) ^ e).sum * 2 ^ (-(M : ℤ)) = 1
      have h := hTval n le_rfl
      rw [hPn, hBn, hone] at h
      exact h
    · intro j _
      have hpos : (0 : ℝ) < 2 ^ (-(M : ℤ)) := by positivity
      have hjj : (j : ℝ) < ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact mul_lt_mul_of_pos_right hjj hpos
    · intro j hj
      have hjl : j < L.length := by rw [hLlen']; exact hj
      show ((L.take (j + 1)).map fun e => (2 : ℝ) ^ e).sum * 2 ^ (-(M : ℤ))
        - ((L.take j).map fun e => (2 : ℝ) ^ e).sum * 2 ^ (-(M : ℤ))
        = (2 : ℝ) ^ (L.getD j 0) * (((j + 1 : ℕ) : ℝ) * 2 ^ (-(M : ℤ))
          - (j : ℝ) * 2 ^ (-(M : ℤ)))
      rw [sum_take_succ L hjl]
      push_cast
      ring
  refine ⟨D, ?_, ?_⟩
  · -- values at the partition points
    intro i hi
    rw [← hPX i hi, ← hDs (P i), D.fn_s (by rw [hDN]; exact hPle i hi), hDt (P i)]
    exact hTval i hi
  · -- the identity on a shared part
    intro i hi hAB hAB1 z hz1 hz2
    have hKQ : K i = Q i := by rw [hK i, hQ i, hAB, hAB1]
    have hzero : ∀ j, P i ≤ j → j < P (i + 1) → D.e j = 0 := by
      intro j hj1 hj2
      rw [hDe j]
      refine hLzero i hi hKQ j ?_ ?_
      · rwa [← hP i]
      · rwa [← hP (i + 1)]
    have hstart : D.t (P i) = D.s (P i) := by
      rw [hDt (P i), hDs (P i), hTval i (by omega), ← hAB, ← hPX i (by omega)]
    have hle : P i ≤ P (i + 1) := by
      rw [hP i, hP (i + 1)]
      exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
    have hbN : P (i + 1) ≤ D.N := by rw [hDN]; exact hPle (i + 1) (by omega)
    have hts := D.t_eq_s_of_zero hbN hstart hzero
    refine D.fn_id_on hle hbN hts hzero z ?_ ?_
    · rw [hDs (P i), hPX i (by omega)]; exact hz1
    · rw [hDs (P (i + 1)), hPX (i + 1) (by omega)]; exact hz2

/-- Cannon–Floyd–Parry's Lemma 4.2, in terms of the underlying function: two dyadic partitions
of `[0,1]` with the same number of parts are carried onto one another, and the map may be taken
to be the identity on a part the two partitions share. -/
theorem exists_PLData_of_partitions (n : ℕ) (hn : 1 ≤ n) (X Y : ℕ → ℝ)
    (hXm : ∀ i, i < n → X i < X (i + 1)) (hYm : ∀ i, i < n → Y i < Y (i + 1))
    (hX0 : X 0 = 0) (hXn : X n = 1) (hY0 : Y 0 = 0) (hYn : Y n = 1)
    (hXd : ∀ i, i ≤ n → IsDyadic (X i)) (hYd : ∀ i, i ≤ n → IsDyadic (Y i)) :
    ∃ D : PLData, (∀ i, i ≤ n → D.fn (X i) = Y i) ∧
      (∀ i, i < n → X i = Y i → X (i + 1) = Y (i + 1) →
        ∀ z, X i ≤ z → z ≤ X (i + 1) → D.fn z = z) := by
  classical
  have hKX : ∀ i, i ≤ n → ∃ K : ℕ, ∀ M, K ≤ M → ∃ a : ℤ, X i = (a : ℝ) / 2 ^ M :=
    fun i hi => isDyadic_den (hXd i hi)
  have hKY : ∀ i, i ≤ n → ∃ K : ℕ, ∀ M, K ≤ M → ∃ a : ℤ, Y i = (a : ℝ) / 2 ^ M :=
    fun i hi => isDyadic_den (hYd i hi)
  choose! KX hKXs using hKX
  choose! KY hKYs using hKY
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, ∀ i, i ≤ n → KX i ≤ M₀ ∧ KY i ≤ M₀ := by
    refine ⟨(Finset.range (n + 1)).sup (fun i => max (KX i) (KY i)), fun i hi => ⟨?_, ?_⟩⟩
    · refine le_trans (le_max_left (KX i) (KY i)) ?_
      exact Finset.le_sup (f := fun i => max (KX i) (KY i))
        (Finset.mem_range.mpr (by omega : i < n + 1))
    · refine le_trans (le_max_right (KX i) (KY i)) ?_
      exact Finset.le_sup (f := fun i => max (KX i) (KY i))
        (Finset.mem_range.mpr (by omega : i < n + 1))
  have hA : ∀ i, i ≤ n → ∃ a : ℤ, X i = (a : ℝ) / 2 ^ M₀ :=
    fun i hi => hKXs i hi M₀ (hM₀ i hi).1
  have hB : ∀ i, i ≤ n → ∃ b : ℤ, Y i = (b : ℝ) / 2 ^ M₀ :=
    fun i hi => hKYs i hi M₀ (hM₀ i hi).2
  choose! A hAs using hA
  choose! B hBs using hB
  have hpos : (0 : ℝ) < 2 ^ (M₀ : ℕ) := by positivity
  have hne : ((2 : ℝ) ^ (M₀ : ℕ)) ≠ 0 := ne_of_gt hpos
  have hval : ∀ (C : ℕ → ℤ) (Z : ℕ → ℝ), (∀ i, i ≤ n → Z i = (C i : ℝ) / 2 ^ M₀) →
      ∀ i, i ≤ n → (C i : ℝ) = Z i * 2 ^ (M₀ : ℕ) := by
    intro C Z hZ i hi
    rw [hZ i hi]
    field_simp
  have hvA := hval A X hAs
  have hvB := hval B Y hBs
  have hA0 : A 0 = 0 := by
    have h : ((A 0 : ℤ) : ℝ) = 0 := by rw [hvA 0 (by omega), hX0]; ring
    exact_mod_cast h
  have hB0 : B 0 = 0 := by
    have h : ((B 0 : ℤ) : ℝ) = 0 := by rw [hvB 0 (by omega), hY0]; ring
    exact_mod_cast h
  have hAn : A n = 2 ^ M₀ := by
    have h : ((A n : ℤ) : ℝ) = ((2 ^ M₀ : ℤ) : ℝ) := by
      rw [hvA n le_rfl, hXn, one_mul]; push_cast; ring
    exact_mod_cast h
  have hBn : B n = 2 ^ M₀ := by
    have h : ((B n : ℤ) : ℝ) = ((2 ^ M₀ : ℤ) : ℝ) := by
      rw [hvB n le_rfl, hYn, one_mul]; push_cast; ring
    exact_mod_cast h
  have hAm : ∀ i, i < n → A i < A (i + 1) := by
    intro i hi
    have h : ((A i : ℤ) : ℝ) < ((A (i + 1) : ℤ) : ℝ) := by
      rw [hvA i (by omega), hvA (i + 1) (by omega)]
      exact mul_lt_mul_of_pos_right (hXm i hi) hpos
    exact_mod_cast h
  have hBm : ∀ i, i < n → B i < B (i + 1) := by
    intro i hi
    have h : ((B i : ℤ) : ℝ) < ((B (i + 1) : ℤ) : ℝ) := by
      rw [hvB i (by omega), hvB (i + 1) (by omega)]
      exact mul_lt_mul_of_pos_right (hYm i hi) hpos
    exact_mod_cast h
  obtain ⟨D, hD1, hD2⟩ := exists_PLData_of_int n hn M₀ A B hA0 hAn hB0 hBn hAm hBm
  refine ⟨D, ?_, ?_⟩
  · intro i hi
    rw [hAs i hi, hBs i hi]
    exact hD1 i hi
  · intro i hi hXY hXY1 z hz1 hz2
    have hAB : A i = B i := by
      have h : ((A i : ℤ) : ℝ) = ((B i : ℤ) : ℝ) := by
        rw [hvA i (by omega), hvB i (by omega), hXY]
      exact_mod_cast h
    have hAB1 : A (i + 1) = B (i + 1) := by
      have h : ((A (i + 1) : ℤ) : ℝ) = ((B (i + 1) : ℤ) : ℝ) := by
        rw [hvA (i + 1) (by omega), hvB (i + 1) (by omega), hXY1]
      exact_mod_cast h
    refine hD2 i hi hAB hAB1 z ?_ ?_
    · rw [← hAs i (by omega)]; exact hz1
    · rw [← hAs (i + 1) (by omega)]; exact hz2

end CFPLib
open CannonFloydParry CFPLib

namespace CFPCenter

/-! ### Dyadic rationals are order-dense

Cannon–Floyd–Parry's argument needs a supply of dyadic breakpoints strictly between two given
reals; that is all this section provides. -/

lemma isDyadic_one : IsDyadic (1 : ℝ) := ⟨1, 0, by norm_num⟩

lemma isDyadic_neg_c {x : ℝ} (h : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨m, k, rfl⟩ := h
  exact ⟨-m, k, by push_cast; ring⟩

lemma isDyadic_sub {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x - y) := by
  simpa [sub_eq_add_neg] using isDyadic_add_c hx (isDyadic_neg_c hy)

lemma isDyadic_half {x : ℝ} (h : IsDyadic x) : IsDyadic (x / 2) := by
  obtain ⟨m, k, rfl⟩ := h
  refine ⟨m, k + 1, ?_⟩
  rw [pow_succ]
  ring

/-- Between any two reals there is a dyadic rational. -/
lemma exists_isDyadic_Ioo {a b : ℝ} (hab : a < b) : ∃ c : ℝ, IsDyadic c ∧ a < c ∧ c < b := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 : ℝ) / 2 ^ k < b - a := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hab) (by norm_num : (1:ℝ)/2 < 1)
    exact ⟨k, by simpa [div_pow, one_div] using hk⟩
  have hP : (0 : ℝ) < 2 ^ k := by positivity
  have hwide : (1 : ℝ) < (b - a) * 2 ^ k := by
    rw [div_lt_iff₀ hP] at hk
    linarith
  have hfl : ((⌊a * 2 ^ k⌋ : ℤ) : ℝ) ≤ a * 2 ^ k := Int.floor_le _
  have hfu : a * 2 ^ k < ((⌊a * 2 ^ k⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  refine ⟨((⌊a * 2 ^ k⌋ + 1 : ℤ) : ℝ) / 2 ^ k, ⟨⌊a * 2 ^ k⌋ + 1, k, rfl⟩, ?_, ?_⟩
  · rw [lt_div_iff₀ hP]
    push_cast
    linarith
  · rw [div_lt_iff₀ hP]
    push_cast
    linarith

/-! ### A element of `F` whose fixed set is exactly `[0,c] ∪ {1}`

For a dyadic `c ∈ (0,1)`, rescale the shape of the generator `A` to `[c,1]`: the three pieces
have slopes `1/2`, `1`, `2`, so the map is the identity on `[0,c]` and strictly decreasing
away from the diagonal on `(c,1)`. -/

/-- Piecewise-linear data for that map. -/
noncomputable def push (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hcd : IsDyadic c) : PLData where
  N := 4
  s := fun j => match j with
    | 0 => 0
    | 1 => c
    | 2 => c + (1 - c) / 2
    | 3 => c + 3 * (1 - c) / 4
    | _ => 1
  t := fun j => match j with
    | 0 => 0
    | 1 => c
    | 2 => c + (1 - c) / 4
    | 3 => c + (1 - c) / 2
    | _ => 1
  e := fun j => match j with
    | 0 => 0
    | 1 => -1
    | 2 => 0
    | _ => 1
  hN := by norm_num
  hs0 := rfl
  hsN := rfl
  ht0 := rfl
  htN := rfl
  hsmono := by
    intro j hj
    interval_cases j <;> simp <;> linarith
  hslope := by
    intro j hj
    interval_cases j <;> norm_num <;> ring
  hsdy := by
    intro j hj
    have hd : IsDyadic (1 - c) := isDyadic_sub isDyadic_one hcd
    have hd2 : IsDyadic ((1 - c) / 2) := isDyadic_half hd
    have hd4 : IsDyadic ((1 - c) / 2 / 2) := isDyadic_half hd2
    interval_cases j
    · exact isDyadic_zero
    · exact hcd
    · exact isDyadic_add_c hcd hd2
    · have h3 : c + 3 * (1 - c) / 4
          = c + ((1 - c) / 2 / 2 + ((1 - c) / 2 / 2 + (1 - c) / 2 / 2)) := by ring
      show IsDyadic (c + 3 * (1 - c) / 4)
      rw [h3]
      exact isDyadic_add_c hcd (isDyadic_add_c hd4 (isDyadic_add_c hd4 hd4))
    · exact isDyadic_one
  htdy := by
    intro j hj
    have hd : IsDyadic (1 - c) := isDyadic_sub isDyadic_one hcd
    have hd2 : IsDyadic ((1 - c) / 2) := isDyadic_half hd
    have hd4 : IsDyadic ((1 - c) / 2 / 2) := isDyadic_half hd2
    interval_cases j
    · exact isDyadic_zero
    · exact hcd
    · show IsDyadic (c + (1 - c) / 4)
      have h2 : c + (1 - c) / 4 = c + (1 - c) / 2 / 2 := by ring
      rw [h2]
      exact isDyadic_add_c hcd hd4
    · exact isDyadic_add_c hcd hd2
    · exact isDyadic_one

variable {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hcd : IsDyadic c)

lemma push_fn_id {z : ℝ} (hz0 : 0 ≤ z) (hzc : z ≤ c) : (push c hc0 hc1 hcd).fn z = z := by
  have h := (push c hc0 hc1 hcd).fn_piece (k := 0) (by norm_num [push])
    (show (push c hc0 hc1 hcd).s 0 ≤ z by simpa [push] using hz0)
    (show z ≤ (push c hc0 hc1 hcd).s 1 by simpa [push] using hzc)
  simpa [push] using h

lemma push_fn_lt {z : ℝ} (hcz : c < z) (hz1 : z < 1) : (push c hc0 hc1 hcd).fn z < z := by
  obtain ⟨k, hk, hk1, hk2⟩ := (push c hc0 hc1 hcd).exists_piece_c (by linarith) (le_of_lt hz1)
  have hk' : k < 4 := hk
  rw [(push c hc0 hc1 hcd).fn_piece hk hk1 hk2]
  interval_cases k <;> simp only [push] at hk1 hk2 ⊢ <;> norm_num <;> linarith

end CFPCenter

namespace CannonFloydParry

open CFPCenter

/-- In the group of order isomorphisms, the inverse is the inverse map. -/
lemma inv_eq_symm_c (g : UI ≃o UI) : g⁻¹ = g.symm := rfl

/-- An order isomorphism of `[0,1]` fixes the right endpoint. -/
lemma orderIso_apply_top (f : UI ≃o UI) (hT : (1:ℝ) ∈ Set.Icc (0:ℝ) 1) :
    ((f ⟨1, hT⟩ : UI) : ℝ) = 1 := by
  have hle : ((f ⟨1, hT⟩ : UI) : ℝ) ≤ 1 := (f ⟨1, hT⟩).2.2
  have hsym : f.symm ⟨1, hT⟩ ≤ (⟨1, hT⟩ : UI) := (f.symm ⟨1, hT⟩).2.2
  have hmono : f (f.symm ⟨1, hT⟩) ≤ f ⟨1, hT⟩ := f.monotone hsym
  rw [f.apply_symm_apply] at hmono
  have : (1:ℝ) ≤ ((f ⟨1, hT⟩ : UI) : ℝ) := hmono
  linarith

/-- A central element of `F` fixes every dyadic point of `(0,1)`. -/
lemma center_fixes_dyadic {f : ↥F} (hf : f ∈ Subgroup.center F)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hcd : IsDyadic c)
    (hc : c ∈ Set.Icc (0:ℝ) 1) :
    (((f : UI ≃o UI) ⟨c, hc⟩ : UI) : ℝ) = c := by
  set D := push c hc0 hc1 hcd with hD
  set g : ↥F := ⟨D.uiMap, D.uiMap_mem_F⟩ with hg
  -- `f` commutes with `g`
  have hcomm : ∀ z : UI, D.uiMap ((f : UI ≃o UI) z) = (f : UI ≃o UI) (D.uiMap z) := by
    have h := Subgroup.mem_center_iff.mp hf g
    intro z
    have h' : ((g * f : ↥F) : UI ≃o UI) z = ((f * g : ↥F) : UI ≃o UI) z := by rw [h]
    simpa [hg] using h'
  set zc : UI := ⟨c, hc⟩ with hzc
  -- `g` fixes `c`
  have hgc : D.uiMap zc = zc := by
    apply Subtype.ext
    show D.fn c = c
    exact push_fn_id hc0 hc1 hcd hc.1 le_rfl
  -- hence `f c` is also fixed by `g`
  have hfix : D.uiMap ((f : UI ≃o UI) zc) = (f : UI ≃o UI) zc := by
    rw [hcomm zc, hgc]
  -- so `f c ≤ c`
  have hle : (((f : UI ≃o UI) zc : UI) : ℝ) ≤ c := by
    by_contra hgt
    push_neg at hgt
    set w : ℝ := (((f : UI ≃o UI) zc : UI) : ℝ) with hw
    rcases lt_or_eq_of_le ((f : UI ≃o UI) zc).2.2 with hlt1 | heq1
    · have := push_fn_lt hc0 hc1 hcd hgt hlt1
      have hfe : D.fn w = w := congrArg (fun u : UI => (u : ℝ)) hfix
      rw [hfe] at this
      exact absurd this (lt_irrefl w)
    · -- `f c = 1`, so `c = 1` by injectivity
      have hT : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
      have h1 : ((f : UI ≃o UI) ⟨1, hT⟩ : UI) = ((f : UI ≃o UI) zc : UI) := by
        apply Subtype.ext
        rw [orderIso_apply_top (f : UI ≃o UI) hT]
        exact heq1.symm
      have := (f : UI ≃o UI).injective h1
      have : (1:ℝ) = c := congrArg (fun u : UI => (u : ℝ)) this
      linarith
  -- and `c ≤ f c`, using that the inverse is central too
  have hge : c ≤ (((f : UI ≃o UI) zc : UI) : ℝ) := by
    have hfinv : f⁻¹ ∈ Subgroup.center F := Subgroup.inv_mem _ hf
    have hcomm' : ∀ z : UI, D.uiMap ((f : UI ≃o UI).symm z) = (f : UI ≃o UI).symm (D.uiMap z) := by
      have h := Subgroup.mem_center_iff.mp hfinv g
      intro z
      have h' : ((g * f⁻¹ : ↥F) : UI ≃o UI) z = ((f⁻¹ * g : ↥F) : UI ≃o UI) z := by rw [h]
      simpa [hg, inv_eq_symm_c] using h'
    have hfix' : D.uiMap ((f : UI ≃o UI).symm zc) = (f : UI ≃o UI).symm zc := by
      rw [hcomm' zc, hgc]
    have hle' : ((((f : UI ≃o UI).symm zc : UI)) : ℝ) ≤ c := by
      by_contra hgt
      push_neg at hgt
      set w : ℝ := ((((f : UI ≃o UI).symm zc : UI)) : ℝ) with hw
      rcases lt_or_eq_of_le ((f : UI ≃o UI).symm zc).2.2 with hlt1 | heq1
      · have := push_fn_lt hc0 hc1 hcd hgt hlt1
        have hfe : D.fn w = w := congrArg (fun u : UI => (u : ℝ)) hfix'
        rw [hfe] at this
        exact absurd this (lt_irrefl w)
      · have hT : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by norm_num
        have h1 : ((f : UI ≃o UI).symm ⟨1, hT⟩ : UI) = ((f : UI ≃o UI).symm zc : UI) := by
          apply Subtype.ext
          rw [orderIso_apply_top (f : UI ≃o UI).symm hT]
          exact heq1.symm
        have := (f : UI ≃o UI).symm.injective h1
        have : (1:ℝ) = c := congrArg (fun u : UI => (u : ℝ)) this
        linarith
    have hmono : (f : UI ≃o UI) ((f : UI ≃o UI).symm zc) ≤ (f : UI ≃o UI) zc :=
      (f : UI ≃o UI).monotone (by exact hle')
    rw [(f : UI ≃o UI).apply_symm_apply] at hmono
    exact hmono
  linarith [hle, hge]

end CannonFloydParry

namespace CannonFloydParry
open CFPCenter

theorem center_eq_bot' : Subgroup.center F = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro f hf
  apply Subtype.ext
  apply RelIso.ext
  intro z
  apply Subtype.ext
  show (((f : UI ≃o UI) z : UI) : ℝ) = (z : ℝ)
  refine le_antisymm ?_ ?_
  · by_contra hgt
    push_neg at hgt
    obtain ⟨d, hdd, hd1, hd2⟩ := exists_isDyadic_Ioo hgt
    have hd0 : 0 < d := lt_of_le_of_lt z.2.1 hd1
    have hdlt1 : d < 1 := lt_of_lt_of_le hd2 ((f : UI ≃o UI) z).2.2
    have hdmem : d ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hd0, le_of_lt hdlt1⟩
    have hfix := center_fixes_dyadic hf hd0 hdlt1 hdd hdmem
    have hzle : z ≤ (⟨d, hdmem⟩ : UI) := Subtype.coe_le_coe.mp (le_of_lt hd1)
    have hmono := (f : UI ≃o UI).monotone hzle
    have hcoe : (((f : UI ≃o UI) z : UI) : ℝ) ≤ (((f : UI ≃o UI) ⟨d, hdmem⟩ : UI) : ℝ) :=
      Subtype.coe_le_coe.mpr hmono
    rw [hfix] at hcoe
    linarith
  · by_contra hgt
    push_neg at hgt
    obtain ⟨d, hdd, hd1, hd2⟩ := exists_isDyadic_Ioo hgt
    have hd0 : 0 < d := lt_of_le_of_lt ((f : UI ≃o UI) z).2.1 hd1
    have hdlt1 : d < 1 := lt_of_lt_of_le hd2 z.2.2
    have hdmem : d ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hd0, le_of_lt hdlt1⟩
    have hfix := center_fixes_dyadic hf hd0 hdlt1 hdd hdmem
    have hzle : (⟨d, hdmem⟩ : UI) ≤ z := Subtype.coe_le_coe.mp (le_of_lt hd2)
    have hmono := (f : UI ≃o UI).monotone hzle
    have hcoe : (((f : UI ≃o UI) ⟨d, hdmem⟩ : UI) : ℝ) ≤ (((f : UI ≃o UI) z : UI) : ℝ) :=
      Subtype.coe_le_coe.mpr hmono
    rw [hfix] at hcoe
    linarith

end CannonFloydParry

namespace CannonFloydParry

/-! ### The generators, as elements of `F`, and the relations among them -/

noncomputable def XF (n : ℕ) : F :=
  ⟨X n, by rw [← closure_mapA_mapB_eq_F']; exact X_mem_closure n⟩

noncomputable def wordFromF (i : ℕ) (l : List ℕ) : F :=
  ⟨wordFrom i l, by rw [← closure_mapA_mapB_eq_F']; exact wordFrom_mem_closure l i⟩

@[simp] lemma coe_XF (n : ℕ) : ((XF n : F) : UI ≃o UI) = X n := rfl

@[simp] lemma coe_wordFromF (i : ℕ) (l : List ℕ) :
    ((wordFromF i l : F) : UI ≃o UI) = wordFrom i l := rfl

lemma XF_zero : XF 0 = genA := Subtype.ext (by simp [genA])

lemma XF_one : XF 1 = genB := Subtype.ext (by simp [genB])

lemma XF_two : XF 2 = genA⁻¹ * genB * genA := Subtype.ext (by
  show X 2 = mapA⁻¹ * mapB * mapA
  show (mapA ^ 1)⁻¹ * mapB * mapA ^ 1 = mapA⁻¹ * mapB * mapA
  rw [pow_one])

/-- `Xᵢ⁻¹ Xⱼ Xᵢ = Xⱼ₊₁` for `i < j`, in `F`. -/
lemma XF_conj_up {i j : ℕ} (h : i < j) : (XF i)⁻¹ * XF j * XF i = XF (j + 1) := by
  apply Subtype.ext
  show (X i)⁻¹ * X j * X i = X (j + 1)
  have hc := X_comm h
  calc (X i)⁻¹ * X j * X i = (X i)⁻¹ * (X j * X i) := by group
    _ = (X i)⁻¹ * (X i * X (j + 1)) := by rw [hc]
    _ = X (j + 1) := by group

lemma XF_conj_down {i j : ℕ} (h : i < j) : XF i * XF (j + 1) * (XF i)⁻¹ = XF j := by
  rw [← XF_conj_up h]; group

lemma XF_conj_up_pow {i j : ℕ} (h : i < j) (m : ℕ) :
    (XF i)⁻¹ * XF j ^ m * XF i = XF (j + 1) ^ m := by
  rw [← XF_conj_up h]
  rw [show (XF i)⁻¹ * XF j * XF i = (XF i)⁻¹ * XF j * ((XF i)⁻¹)⁻¹ by rw [inv_inv], conj_pow,
    inv_inv]

lemma wordFromF_nil (i : ℕ) : wordFromF i [] = 1 := Subtype.ext rfl

lemma wordFromF_cons (i c : ℕ) (l : List ℕ) :
    wordFromF i (c :: l) = XF i ^ c * wordFromF (i + 1) l := by
  apply Subtype.ext
  show wordFrom i (c :: l) = X i ^ c * wordFrom (i + 1) l
  rfl

lemma wordFromF_append (as bs : List ℕ) (i : ℕ) :
    wordFromF i (as ++ bs) = wordFromF i as * wordFromF (i + as.length) bs := by
  apply Subtype.ext
  show wordFrom i (as ++ bs) = wordFrom i as * wordFrom (i + as.length) bs
  exact wordFrom_append as bs i

/-- Conjugating a word in `X_j, X_{j+1}, …` by `X_i`, `i < j`, shifts every index up by one. -/
lemma wordFromF_conj_up {i : ℕ} : ∀ (l : List ℕ) (j : ℕ), i < j →
    (XF i)⁻¹ * wordFromF j l * XF i = wordFromF (j + 1) l := by
  intro l
  induction l with
  | nil => intro j _; rw [wordFromF_nil, wordFromF_nil]; group
  | cons c l ih =>
      intro j hij
      rw [wordFromF_cons, wordFromF_cons, ← XF_conj_up_pow hij, ← ih (j + 1) (by omega)]
      group

lemma wordFromF_conj_down {i : ℕ} (l : List ℕ) {j : ℕ} (h : i < j) :
    XF i * wordFromF (j + 1) l * (XF i)⁻¹ = wordFromF j l := by
  rw [← wordFromF_conj_up l j h]; group

/-- Conjugating by `A^m` shifts a word in `X_{j+m}, …` down to `X_j, …`, for `j ≥ 1`. -/
lemma wordFromF_conj_down_pow (l : List ℕ) : ∀ (m j : ℕ), 1 ≤ j →
    XF 0 ^ m * wordFromF (j + m) l * (XF 0 ^ m)⁻¹ = wordFromF j l := by
  intro m
  induction m with
  | zero => intro j _; simp
  | succ m ih =>
      intro j hj
      rw [pow_succ, show j + (m + 1) = (j + m) + 1 by omega]
      calc XF 0 ^ m * XF 0 * wordFromF (j + m + 1) l * (XF 0 ^ m * XF 0)⁻¹
          = XF 0 ^ m * (XF 0 * wordFromF (j + m + 1) l * (XF 0)⁻¹) * (XF 0 ^ m)⁻¹ := by group
        _ = XF 0 ^ m * wordFromF (j + m) l * (XF 0 ^ m)⁻¹ := by
            rw [wordFromF_conj_down l (by omega)]
        _ = wordFromF j l := ih j hj

lemma XF_conj_down_pow (l : List ℕ) : ∀ (m j : ℕ), 1 ≤ j →
    XF 0 ^ m * XF (j + m) * (XF 0 ^ m)⁻¹ = XF j := by
  intro m j hj
  have := wordFromF_conj_down_pow [1] m j hj
  rw [wordFromF_cons, wordFromF_cons, wordFromF_nil, wordFromF_nil, pow_one, pow_one,
    mul_one, mul_one] at this
  exact this

/-- `(Xᵢ^m)⁻¹ Xⱼ Xᵢ^m = X_{j+m}` for `i < j`. -/
lemma XF_conj_up_iter {i j : ℕ} (h : i < j) : ∀ m : ℕ,
    (XF i ^ m)⁻¹ * XF j * XF i ^ m = XF (j + m) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, show j + (m + 1) = (j + m) + 1 by omega, ← XF_conj_up (by omega : i < j + m),
        ← ih]
      group

/-- `Xᵢ^m X_{j+m} (Xᵢ^m)⁻¹ = Xⱼ` for `i < j`. -/
lemma XF_conj_down_iter {i j : ℕ} (h : i < j) (m : ℕ) :
    XF i ^ m * XF (j + m) * (XF i ^ m)⁻¹ = XF j := by
  rw [← XF_conj_up_iter h m]; group

/-! ### The slope at `0` of a word -/

lemma φ_XF_succ (n : ℕ) : φ (XF (n + 1)) = Multiplicative.ofAdd (0, 1) := by
  have : XF (n + 1) = (genA ^ n)⁻¹ * genB * genA ^ n := Subtype.ext (by
    show X (n + 1) = (mapA ^ n)⁻¹ * mapB * mapA ^ n
    rfl)
  rw [this, map_mul, map_mul, map_inv, map_pow, φ_genA, φ_genB]
  -- the target is commutative, so the conjugation is invisible
  rw [mul_comm ((Multiplicative.ofAdd ((-1 : ℤ), (1 : ℤ)) ^ n)⁻¹), mul_assoc, inv_mul_cancel,
    mul_one]

lemma φ_wordFromF_succ (l : List ℕ) : ∀ i,
    φ (wordFromF (i + 1) l) = Multiplicative.ofAdd (0, (l.sum : ℤ)) := by
  induction l with
  | nil => intro i; rw [wordFromF_nil, map_one]; rfl
  | cons c l ih =>
      intro i
      rw [wordFromF_cons, map_mul, map_pow, φ_XF_succ, ih (i + 1), ← ofAdd_nsmul, ← ofAdd_add]
      congr 1
      ext
      · simp
      · simp [List.sum_cons]

lemma slope0_wordFromF_zero (c : ℕ) (l : List ℕ) :
    slope0 (wordFromF 0 (c :: l)) = -(c : ℤ) := by
  rw [wordFromF_cons, XF_zero, zero_add]
  have h1 : φ (wordFromF 1 l) = Multiplicative.ofAdd (0, (l.sum : ℤ)) := φ_wordFromF_succ l 0
  have h := φ_apply (genA ^ c * wordFromF 1 l)
  rw [map_mul, map_pow, φ_genA, h1, ← ofAdd_nsmul, ← ofAdd_add] at h
  have h2 := congrArg (fun w => (Multiplicative.toAdd w).1) h
  simp at h2
  omega

lemma getD_ge_length' {l : List ℕ} {j : ℕ} (h : l.length ≤ j) : l.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-! ### The commutator `[B, A⁻¹]` lies in any normal subgroup containing a suitable word -/

lemma getD_eq_getElem' (l : List ℕ) {k : ℕ} (hk : k < l.length) : l.getD k 0 = l[k] :=
  List.getD_eq_getElem _ _ hk

lemma drop_eq_getD_cons (l : List ℕ) {k : ℕ} (hk : k < l.length) :
    l.drop k = l.getD k 0 :: l.drop (k + 1) := by
  rw [getD_eq_getElem' l hk]
  exact List.drop_eq_getElem_cons hk

lemma take_eq_of_getD (as bs : List ℕ) (k : ℕ) (hka : k ≤ as.length) (hkb : k ≤ bs.length)
    (h : ∀ i, i < k → as.getD i 0 = bs.getD i 0) : as.take k = bs.take k := by
  apply List.ext_getElem
  · simp [hka, hkb]
  · intro i h1 h2
    have hi : i < k := lt_of_lt_of_le h1 (List.length_take_le k as)
    rw [List.getElem_take, List.getElem_take]
    have := h i hi
    rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this

/-- The heart of Theorem 4.3: a normal subgroup containing `word bs · (word as)⁻¹`, where the two
lists first differ at an index `k ≥ 1` with `aₖ < bₖ`, contains `[B, A⁻¹]`. -/
lemma commutator_mem_of_words (N : Subgroup F) [hN : N.Normal] (as bs : List ℕ) (k : ℕ)
    (hk1 : 1 ≤ k) (hka : k < as.length) (hkb : k < bs.length)
    (hpre : ∀ i, i < k → as.getD i 0 = bs.getD i 0) (hlt : as.getD k 0 < bs.getD k 0)
    (hmem : wordFromF 0 bs * (wordFromF 0 as)⁻¹ ∈ N) :
    genB * genA⁻¹ * genB⁻¹ * genA ∈ N := by
  -- strip the common prefix
  set P := wordFromF 0 (as.take k) with hP
  have htake : as.take k = bs.take k := take_eq_of_getD as bs k (by omega) (by omega) hpre
  have hlenA : (as.take k).length = k := by simp; omega
  have hdecA : wordFromF 0 as = P * wordFromF k (as.drop k) := by
    conv_lhs => rw [← List.take_append_drop k as]
    rw [wordFromF_append, hlenA, zero_add]
  have hdecB : wordFromF 0 bs = P * wordFromF k (bs.drop k) := by
    conv_lhs => rw [← List.take_append_drop k bs]
    rw [wordFromF_append, ← htake, hlenA, zero_add]
  set a := as.getD k 0 with ha
  set b := bs.getD k 0 with hb
  set U' := wordFromF (k + 1) (bs.drop (k + 1)) with hU'
  set V' := wordFromF (k + 1) (as.drop (k + 1)) with hV'
  have hU : wordFromF k (bs.drop k) = XF k ^ b * U' := by
    rw [drop_eq_getD_cons bs hkb, wordFromF_cons]
  have hV : wordFromF k (as.drop k) = XF k ^ a * V' := by
    rw [drop_eq_getD_cons as hka, wordFromF_cons]
  obtain ⟨d, hd⟩ : ∃ d, b = a + (d + 1) := ⟨b - a - 1, by omega⟩
  -- `c₁ = X_k^{d+1} U' V'⁻¹`
  have h1 : (XF k ^ a)⁻¹ * (P⁻¹ * (wordFromF 0 bs * (wordFromF 0 as)⁻¹) * P) * XF k ^ a
      = XF k ^ (d + 1) * U' * V'⁻¹ := by
    rw [hdecA, hdecB, hU, hV, hd, pow_add]
    group
  have hc1 : XF k ^ (d + 1) * U' * V'⁻¹ ∈ N := by
    rw [← h1]
    have := hN.conj_mem _ hmem P⁻¹
    rw [inv_inv] at this
    have := hN.conj_mem _ this (XF k ^ a)⁻¹
    rwa [inv_inv] at this
  -- shift down by `A^(k-1)`: `c₂ = X_1^{d+1} U₁ V₁⁻¹` with `U₁, V₁` words in `X_2, X_3, …`
  obtain ⟨m, hm⟩ : ∃ m, k = 1 + m := ⟨k - 1, by omega⟩
  set U₁ := wordFromF 2 (bs.drop (k + 1)) with hU₁
  set V₁ := wordFromF 2 (as.drop (k + 1)) with hV₁
  have h2 : XF 0 ^ m * (XF k ^ (d + 1) * U' * V'⁻¹) * (XF 0 ^ m)⁻¹
      = XF 1 ^ (d + 1) * U₁ * V₁⁻¹ := by
    have e1 : XF 0 ^ m * XF k ^ (d + 1) * (XF 0 ^ m)⁻¹ = XF 1 ^ (d + 1) := by
      rw [← conj_pow, hm, XF_conj_down_iter (by omega : 0 < 1) m]
    have e2 : XF 0 ^ m * U' * (XF 0 ^ m)⁻¹ = U₁ := by
      rw [hU', hU₁, hm, show 1 + m + 1 = 2 + m by omega]
      exact wordFromF_conj_down_pow _ m 2 (by omega)
    have e3 : XF 0 ^ m * V' * (XF 0 ^ m)⁻¹ = V₁ := by
      rw [hV', hV₁, hm, show 1 + m + 1 = 2 + m by omega]
      exact wordFromF_conj_down_pow _ m 2 (by omega)
    calc XF 0 ^ m * (XF k ^ (d + 1) * U' * V'⁻¹) * (XF 0 ^ m)⁻¹
        = (XF 0 ^ m * XF k ^ (d + 1) * (XF 0 ^ m)⁻¹) * (XF 0 ^ m * U' * (XF 0 ^ m)⁻¹)
          * (XF 0 ^ m * V' * (XF 0 ^ m)⁻¹)⁻¹ := by group
      _ = XF 1 ^ (d + 1) * U₁ * V₁⁻¹ := by rw [e1, e2, e3]
  have hc2 : XF 1 ^ (d + 1) * U₁ * V₁⁻¹ ∈ N := by
    rw [← h2]; exact hN.conj_mem _ hc1 _
  -- `c₃ = (X₀⁻¹ c₂ X₀) (X₁⁻¹ c₂ X₁)⁻¹ = X_2^{d+1} X_1^{-(d+1)}`
  set U₂ := wordFromF 3 (bs.drop (k + 1)) with hU₂
  set V₂ := wordFromF 3 (as.drop (k + 1)) with hV₂
  have e4 : (XF 0)⁻¹ * (XF 1 ^ (d + 1) * U₁ * V₁⁻¹) * XF 0 = XF 2 ^ (d + 1) * U₂ * V₂⁻¹ := by
    have := XF_conj_up_pow (by omega : 0 < 1) (d + 1)
    have hu := wordFromF_conj_up (i := 0) (bs.drop (k + 1)) 2 (by omega)
    have hv := wordFromF_conj_up (i := 0) (as.drop (k + 1)) 2 (by omega)
    calc (XF 0)⁻¹ * (XF 1 ^ (d + 1) * U₁ * V₁⁻¹) * XF 0
        = ((XF 0)⁻¹ * XF 1 ^ (d + 1) * XF 0) * ((XF 0)⁻¹ * U₁ * XF 0)
          * ((XF 0)⁻¹ * V₁ * XF 0)⁻¹ := by group
      _ = XF 2 ^ (d + 1) * U₂ * V₂⁻¹ := by rw [this, hU₁, hV₁, hu, hv]
  have e5 : (XF 1)⁻¹ * (XF 1 ^ (d + 1) * U₁ * V₁⁻¹) * XF 1 = XF 1 ^ (d + 1) * U₂ * V₂⁻¹ := by
    have hu := wordFromF_conj_up (i := 1) (bs.drop (k + 1)) 2 (by omega)
    have hv := wordFromF_conj_up (i := 1) (as.drop (k + 1)) 2 (by omega)
    calc (XF 1)⁻¹ * (XF 1 ^ (d + 1) * U₁ * V₁⁻¹) * XF 1
        = XF 1 ^ (d + 1) * ((XF 1)⁻¹ * U₁ * XF 1) * ((XF 1)⁻¹ * V₁ * XF 1)⁻¹ := by group
      _ = XF 1 ^ (d + 1) * U₂ * V₂⁻¹ := by rw [hU₁, hV₁, hu, hv]
  have hc3 : XF 2 ^ (d + 1) * (XF 1 ^ (d + 1))⁻¹ ∈ N := by
    have hA := hN.conj_mem _ hc2 (XF 0)⁻¹
    rw [inv_inv, e4] at hA
    have hB := hN.conj_mem _ hc2 (XF 1)⁻¹
    rw [inv_inv, e5] at hB
    have := N.mul_mem hA (N.inv_mem hB)
    rwa [show XF 2 ^ (d + 1) * U₂ * V₂⁻¹ * (XF 1 ^ (d + 1) * U₂ * V₂⁻¹)⁻¹
        = XF 2 ^ (d + 1) * (XF 1 ^ (d + 1))⁻¹ by group] at this
  -- `c₄ = X_1^{-(d+1)} X_2^{d+1}`
  have hc4 : (XF 1 ^ (d + 1))⁻¹ * XF 2 ^ (d + 1) ∈ N := by
    have := hN.conj_mem _ hc3 (XF 1 ^ (d + 1))⁻¹
    rwa [inv_inv, show (XF 1 ^ (d + 1))⁻¹ * (XF 2 ^ (d + 1) * (XF 1 ^ (d + 1))⁻¹) * XF 1 ^ (d + 1)
        = (XF 1 ^ (d + 1))⁻¹ * XF 2 ^ (d + 1) by group] at this
  -- `c₅ = X_2 c₄ X_2⁻¹ c₄⁻¹ = X_2 X_{d+3}⁻¹`
  have hc5 : XF 2 * (XF (2 + (d + 1)))⁻¹ ∈ N := by
    have hconj := hN.conj_mem _ hc4 (XF 2)
    have := N.mul_mem hconj (N.inv_mem hc4)
    have key : (XF 1 ^ (d + 1))⁻¹ * (XF 2)⁻¹ * XF 1 ^ (d + 1) = (XF (2 + (d + 1)))⁻¹ := by
      rw [← XF_conj_up_iter (by omega : 1 < 2) (d + 1)]; group
    rwa [show XF 2 * ((XF 1 ^ (d + 1))⁻¹ * XF 2 ^ (d + 1)) * (XF 2)⁻¹
          * ((XF 1 ^ (d + 1))⁻¹ * XF 2 ^ (d + 1))⁻¹
        = XF 2 * ((XF 1 ^ (d + 1))⁻¹ * (XF 2)⁻¹ * XF 1 ^ (d + 1)) by group, key] at this
  -- `c₆ = X_2^{d} c₅ X_2^{-d} = X_2 X_3⁻¹`, then conjugate by `X_0`
  have hc6 : XF 2 * (XF 3)⁻¹ ∈ N := by
    have := hN.conj_mem _ hc5 (XF 2 ^ d)
    have key : XF 2 ^ d * (XF (2 + (d + 1)))⁻¹ * (XF 2 ^ d)⁻¹ = (XF 3)⁻¹ := by
      rw [show 2 + (d + 1) = 3 + d by omega, ← XF_conj_down_iter (by omega : 2 < 3) d]; group
    rwa [show XF 2 ^ d * (XF 2 * (XF (2 + (d + 1)))⁻¹) * (XF 2 ^ d)⁻¹
        = XF 2 * (XF 2 ^ d * (XF (2 + (d + 1)))⁻¹ * (XF 2 ^ d)⁻¹) by group, key] at this
  have hc7 : XF 1 * (XF 2)⁻¹ ∈ N := by
    have := hN.conj_mem _ hc6 (XF 0)
    have k1 : XF 0 * XF 2 * (XF 0)⁻¹ = XF 1 := XF_conj_down (by omega : 0 < 1)
    have k2 : XF 0 * XF 3 * (XF 0)⁻¹ = XF 2 := XF_conj_down (by omega : 0 < 2)
    rwa [show XF 0 * (XF 2 * (XF 3)⁻¹) * (XF 0)⁻¹
        = (XF 0 * XF 2 * (XF 0)⁻¹) * (XF 0 * XF 3 * (XF 0)⁻¹)⁻¹ by group, k1, k2] at this
  rw [XF_one, XF_two] at hc7
  rwa [show genB * (genA⁻¹ * genB * genA)⁻¹ = genB * genA⁻¹ * genB⁻¹ * genA by group] at hc7

/-! ### Theorem 4.3 -/

lemma exists_ne_index (as bs : List ℕ) (hlen : as.length = bs.length) (hne : as ≠ bs) :
    ∃ k, as.getD k 0 ≠ bs.getD k 0 := by
  by_contra h
  push_neg at h
  apply hne
  apply List.ext_getElem hlen
  intro i h1 h2
  rw [← List.getD_eq_getElem _ _ h1, ← List.getD_eq_getElem _ _ h2]
  exact h i

theorem mul_comm_quotient_of_ne_bot' (N : Subgroup F) [hN : N.Normal] (hne : N ≠ ⊥)
    (x y : F ⧸ N) : x * y = y * x := by
  classical
  -- a nontrivial element of `N`, and a nontrivial commutator in `N`
  obtain ⟨⟨f, hfN⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
  have hfc : f ∉ Subgroup.center F := by
    rw [center_eq_bot', Subgroup.mem_bot]; exact hf1'
  obtain ⟨g, hg⟩ : ∃ g : F, g * f ≠ f * g := by
    by_contra h
    push_neg at h
    exact hfc (Subgroup.mem_center_iff.mpr h)
  set c : F := f * g * f⁻¹ * g⁻¹ with hc
  have hcN : c ∈ N := by
    have := hN.conj_mem _ (N.inv_mem hfN) g
    have := N.mul_mem hfN this
    rwa [show f * (g * f⁻¹ * g⁻¹) = c by rw [hc]; group] at this
  have hc1 : c ≠ 1 := by
    intro h
    apply hg
    have : f * g = g * f := by
      have h' : f * g * f⁻¹ * g⁻¹ = 1 := h
      calc f * g = (f * g * f⁻¹ * g⁻¹) * (g * f) := by group
        _ = g * f := by rw [h', one_mul]
    exact this.symm
  have hccomm : c ∈ commutator F := by
    rw [hc]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top f) (Subgroup.mem_top g)
  -- its slope at `0` is `1`
  have hslope : slope0 c = 0 := by
    rw [← ker_φ, MonoidHom.mem_ker, φ_apply] at hccomm
    have := congrArg (fun w => (Multiplicative.toAdd w).1) hccomm
    simpa using this
  -- write it through a tree diagram
  obtain ⟨d, hd⟩ := exists_represents_of_isThompson (mem_F_iff_isThompson'.mp c.2)
  have hword : c = wordFromF 0 d.ran.exponents * (wordFromF 0 d.dom.exponents)⁻¹ :=
    Subtype.ext (represents_word_exponents hd)
  have hlen : d.dom.exponents.length = d.ran.exponents.length := by
    rw [exponents_length, exponents_length, d.leaves_eq]
  have hne0 := exponents_ne_nil d.dom
  have hne1 := exponents_ne_nil d.ran
  generalize d.dom.exponents = as at hword hlen hne0
  generalize d.ran.exponents = bs at hword hlen hne1
  obtain ⟨a0, as', hasc⟩ := List.exists_cons_of_ne_nil hne0
  obtain ⟨b0, bs', hbsc⟩ := List.exists_cons_of_ne_nil hne1
  have h00 : as.getD 0 0 = bs.getD 0 0 := by
    -- `slope0` is additive: read it off `φ`
    have hφ := congrArg (fun w => (Multiplicative.toAdd w).1)
      (map_mul φ (wordFromF 0 bs) (wordFromF 0 as)⁻¹)
    rw [map_inv, φ_apply, φ_apply, φ_apply] at hφ
    simp at hφ
    rw [← hword, hslope, hasc, hbsc, slope0_wordFromF_zero, slope0_wordFromF_zero] at hφ
    rw [hasc, hbsc]
    simp only [List.getD_cons_zero]
    omega
  have hne' : as ≠ bs := by
    intro h
    apply hc1
    rw [hword, h, mul_inv_cancel]
  have hex := exists_ne_index as bs hlen hne'
  set k := Nat.find hex with hkdef
  have hk : as.getD k 0 ≠ bs.getD k 0 := Nat.find_spec hex
  have hkmin : ∀ i, i < k → as.getD i 0 = bs.getD i 0 := fun i hi =>
    not_ne_iff.mp (Nat.find_min hex hi)
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd (by rw [h0]; exact h00) hk
    · exact h0
  have hkl : k < as.length := by
    by_contra hcon
    push_neg at hcon
    apply hk
    rw [getD_ge_length' hcon, getD_ge_length' (by omega)]
  -- the commutator `[B, A⁻¹]` lies in `N`
  have hBA : genB * genA⁻¹ * genB⁻¹ * genA ∈ N := by
    rcases Nat.lt_or_ge (as.getD k 0) (bs.getD k 0) with hlt | hge
    · exact commutator_mem_of_words N as bs k hk1 hkl (by omega) hkmin hlt (hword ▸ hcN)
    · have hlt' : bs.getD k 0 < as.getD k 0 := lt_of_le_of_ne hge (Ne.symm hk)
      have hinv : wordFromF 0 as * (wordFromF 0 bs)⁻¹ ∈ N := by
        have := N.inv_mem (hword ▸ hcN)
        rwa [mul_inv_rev, inv_inv] at this
      exact commutator_mem_of_words N bs as k hk1 (by omega) hkl
        (fun i hi => (hkmin i hi).symm) hlt' hinv
  -- hence the images of `A` and `B` commute, and they generate the quotient
  have hcommAB : Commute (QuotientGroup.mk genB : F ⧸ N) (QuotientGroup.mk genA) := by
    have h1 : (QuotientGroup.mk (genB * genA⁻¹ * genB⁻¹ * genA) : F ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hBA
    have h2 : Commute (QuotientGroup.mk genB : F ⧸ N) (QuotientGroup.mk genA)⁻¹ := by
      rw [← commutatorElement_eq_one_iff_commute, commutatorElement_def, inv_inv]
      first
        | exact h1
        | simpa using h1
    exact Commute.inv_right_iff.mp h2
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective y
  have hu : u ∈ Subgroup.closure ({genA, genB} : Set F) := by rw [closure_genA_genB]; trivial
  have hv : v ∈ Subgroup.closure ({genA, genB} : Set F) := by rw [closure_genA_genB]; trivial
  have key : ∀ u ∈ Subgroup.closure ({genA, genB} : Set F),
      ∀ v ∈ Subgroup.closure ({genA, genB} : Set F),
      Commute (QuotientGroup.mk u : F ⧸ N) (QuotientGroup.mk v) := by
    intro u hu v hv
    induction hu, hv using Subgroup.closure_induction₂ with
    | mem x y hx hy =>
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact Commute.refl _
        · exact hcommAB.symm
        · exact hcommAB
        · exact Commute.refl _
    | one_left y _ => exact Commute.one_left _
    | one_right x _ => exact Commute.one_right _
    | mul_left x y z _ _ _ h1 h2 => rw [QuotientGroup.mk_mul]; exact h1.mul_left h2
    | mul_right x y z _ _ _ h1 h2 => rw [QuotientGroup.mk_mul]; exact h1.mul_right h2
    | inv_left x y _ _ h => rw [QuotientGroup.mk_inv]; exact h.inv_left
    | inv_right x y _ _ h => rw [QuotientGroup.mk_inv]; exact h.inv_right
  exact (key u hu v hv).eq

end CannonFloydParry

open CannonFloydParry

theorem solution (N : Subgroup F) [N.Normal] (hN : N ≠ ⊥)
    (x y : F ⧸ N) : x * y = y * x :=
  mul_comm_quotient_of_ne_bot' N hN x y
