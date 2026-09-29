-- Prove2me | solution 1 for CannonFloydParry.closure_range_symV_eq_V_and_relations
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T13:43:53.33814+00:00
-- url     : https://prove2.me/submissions/20abf3b5-3cd5-4fc1-828a-782b56ee5de4

import Theorems.Thm_CannonFloydParry_represents_mul
import Theorems.Thm_CannonFloydParry_T_le_V_and_mapPi0_mem_V
import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib
import Definitions.Def_CannonFloydParry_T
import Definitions.Def_CannonFloydParry_V
import Theorems.Thm_CannonFloydParry_closure_mapA_mapB_eq_F
import Theorems.Thm_CannonFloydParry_closure_range_symT_eq_T_and_relations

/-! Tree-diagram infrastructure for F, reused unchanged from the CFP §2/§4 solutions. -/


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

lemma extend_coe (f : UI ≃o UI) (z : UI) : extend f (z : ℝ) = (f z : ℝ) := by
  rw [extend_apply, extendFun_of_mem f z.2]

@[simp] lemma extend_one : extend (1 : UI ≃o UI) = 1 := by
  ext x
  by_cases h : x ∈ Set.Icc (0:ℝ) 1
  · rw [extend_apply, extendFun_of_mem _ h]; rfl
  · rw [extend_apply, extendFun_of_notMem _ h]; rfl


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

end CannonFloydParry

namespace CannonFloydParry

/-! ### Small tools -/

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

/-! ### Every Thompson map has a tree diagram -/

end CannonFloydParry

/-! `toCircle` is an injective group homomorphism from the order isomorphisms of `[0,1]`. -/

namespace CannonFloydParry.S5

lemma icoPerm_mul (f g : UI ≃o UI) : icoPerm (f * g) = icoPerm f * icoPerm g := by
  ext x; rfl

lemma toCircle_mul (f g : UI ≃o UI) : toCircle (f * g) = toCircle f * toCircle g := by
  ext x
  simp only [toCircle, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, icoPerm_mul]

lemma toCircle_one : toCircle 1 = 1 := by
  ext x
  simp only [toCircle, Equiv.trans_apply, Equiv.Perm.coe_one, id]
  have : icoPerm (1 : UI ≃o UI) = 1 := by ext y; rfl
  rw [this, Equiv.Perm.coe_one, id, Equiv.symm_apply_apply]

/-- `toCircle` as a group homomorphism. -/
noncomputable def toCircleHom : (UI ≃o UI) →* Equiv.Perm UnitAddCircle where
  toFun := toCircle
  map_one' := toCircle_one
  map_mul' := toCircle_mul

@[simp] lemma toCircleHom_apply (f : UI ≃o UI) : toCircleHom f = toCircle f := rfl

end CannonFloydParry.S5

/-! Evaluating `A`, `B`, `C` and their inverses on `[0,1)` representatives of the circle. -/

namespace CannonFloydParry.S5

/-- The representative in `[0,1)` of a point of the circle. -/
noncomputable def ico (x : UnitAddCircle) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)

lemma ico_nonneg (x : UnitAddCircle) : 0 ≤ ico x := (AddCircle.equivIco (1 : ℝ) 0 x).2.1
lemma ico_lt_one (x : UnitAddCircle) : ico x < 1 := by
  have h := (AddCircle.equivIco (1 : ℝ) 0 x).2.2
  unfold ico
  linarith

lemma perm_ext {σ τ : Equiv.Perm UnitAddCircle} (h : ∀ x, ico (σ x) = ico (τ x)) : σ = τ := by
  ext x
  exact (AddCircle.equivIco (1 : ℝ) 0).injective (Subtype.ext (h x))

lemma ico_symm (y : Set.Ico (0 : ℝ) (0 + 1)) : ico ((AddCircle.equivIco (1 : ℝ) 0).symm y) = y := by
  simp [ico]

lemma ico_toCircle (f : UI ≃o UI) (x : UnitAddCircle) :
    ico (toCircle f x) = (f ⟨ico x, ico_nonneg x, (ico_lt_one x).le⟩ : ℝ) := by
  simp only [toCircle, Equiv.trans_apply, ico_symm]
  rfl

/-! Piecewise formulas. -/

lemma aInv_of_mem1 {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1/4) : aInv y = 2 * y := by
  unfold aInv; split_ifs <;> linarith
lemma aInv_of_mem2 {y : ℝ} (h0 : 1/4 ≤ y) (h1 : y ≤ 1/2) : aInv y = y + 1/4 := by
  unfold aInv; split_ifs <;> linarith
lemma aInv_of_mem3 {y : ℝ} (h0 : 1/2 ≤ y) (h1 : y ≤ 1) : aInv y = (y + 1) / 2 := by
  unfold aInv; split_ifs <;> linarith
lemma bInv_of_mem0 {y : ℝ} (h1 : y ≤ 1/2) : bInv y = y := by
  unfold bInv; split_ifs <;> linarith
lemma bInv_of_mem1 {y : ℝ} (h0 : 1/2 ≤ y) (h1 : y ≤ 5/8) : bInv y = 2 * y - 1/2 := by
  unfold bInv; split_ifs <;> linarith
lemma bInv_of_mem2 {y : ℝ} (h0 : 5/8 ≤ y) (h1 : y ≤ 3/4) : bInv y = y + 1/8 := by
  unfold bInv; split_ifs <;> linarith
lemma bInv_of_mem3 {y : ℝ} (h0 : 3/4 ≤ y) (h1 : y ≤ 1) : bInv y = (y + 1) / 2 := by
  unfold bInv; split_ifs <;> linarith
lemma cFun_of_mem1 {x : ℝ} (h1 : x < 1/2) : cFun x = x / 2 + 3/4 := by
  unfold cFun; split_ifs <;> linarith
lemma cFun_of_mem2 {x : ℝ} (h0 : 1/2 ≤ x) (h1 : x < 3/4) : cFun x = 2 * x - 1 := by
  unfold cFun; split_ifs <;> linarith
lemma cFun_of_mem3 {x : ℝ} (h0 : 3/4 ≤ x) : cFun x = x - 1/4 := by
  unfold cFun; split_ifs <;> linarith
lemma cInv_of_mem1 {y : ℝ} (h1 : y < 1/2) : cInv y = (y + 1) / 2 := by
  unfold cInv; split_ifs <;> linarith
lemma cInv_of_mem2 {y : ℝ} (h0 : 1/2 ≤ y) (h1 : y < 3/4) : cInv y = y + 1/4 := by
  unfold cInv; split_ifs <;> linarith
lemma cInv_of_mem3 {y : ℝ} (h0 : 3/4 ≤ y) : cInv y = 2 * y - 3/2 := by
  unfold cInv; split_ifs <;> linarith

lemma aInv_mem {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 ≤ aInv y ∧ aInv y ≤ 1 := by
  unfold aInv; split_ifs <;> constructor <;> linarith
lemma bInv_mem {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 ≤ bInv y ∧ bInv y ≤ 1 := by
  unfold bInv; split_ifs <;> constructor <;> linarith

/-! The generators and their inverses on representatives. -/

lemma ico_A (x : UnitAddCircle) : ico (symT FormalABC.A x) = aFun (ico x) := by
  simp only [symT, ico_toCircle, mapA, restrict_coe, lineA_apply]

lemma ico_B (x : UnitAddCircle) : ico (symT FormalABC.B x) = bFun (ico x) := by
  simp only [symT, ico_toCircle, mapB, restrict_coe, lineB_apply]

lemma ico_C (x : UnitAddCircle) : ico (symT FormalABC.C x) = cFun (ico x) := by
  simp only [symT, mapC, Equiv.trans_apply, ico_symm]
  rfl

lemma inv_apply_eq_of {σ : Equiv.Perm UnitAddCircle} {x z : UnitAddCircle} (h : σ z = x) :
    σ⁻¹ x = z := by
  rw [Equiv.Perm.inv_eq_iff_eq]; exact h.symm

lemma ico_Ainv (x : UnitAddCircle) : ico ((symT FormalABC.A)⁻¹ x) = aInv (ico x) := by
  obtain ⟨h0, h1⟩ := aInv_mem (ico_nonneg x) (ico_lt_one x).le
  have hlt : aInv (ico x) < 0 + 1 := by
    rcases lt_or_eq_of_le h1 with h | h
    · simpa using h
    · exfalso
      have := aFun_aInv (ico x); rw [h] at this
      rw [aFun_of_mem3 (by norm_num) le_rfl] at this
      linarith [ico_lt_one x]
  let z := (AddCircle.equivIco (1 : ℝ) 0).symm ⟨aInv (ico x), h0, hlt⟩
  have hz : symT FormalABC.A z = x := by
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    change ico (symT FormalABC.A z) = ico x
    rw [ico_A, ico_symm]
    exact aFun_aInv (ico x)
  rw [inv_apply_eq_of hz, ico_symm]

lemma ico_Binv (x : UnitAddCircle) : ico ((symT FormalABC.B)⁻¹ x) = bInv (ico x) := by
  obtain ⟨h0, h1⟩ := bInv_mem (ico_nonneg x) (ico_lt_one x).le
  have hlt : bInv (ico x) < 0 + 1 := by
    rcases lt_or_eq_of_le h1 with h | h
    · simpa using h
    · exfalso
      have := bFun_bInv (ico x); rw [h] at this
      rw [bFun_of_mem3 (by norm_num) le_rfl] at this
      linarith [ico_lt_one x]
  let z := (AddCircle.equivIco (1 : ℝ) 0).symm ⟨bInv (ico x), h0, hlt⟩
  have hz : symT FormalABC.B z = x := by
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    change ico (symT FormalABC.B z) = ico x
    rw [ico_B, ico_symm]
    exact bFun_bInv (ico x)
  rw [inv_apply_eq_of hz, ico_symm]

lemma ico_Cinv (x : UnitAddCircle) : ico ((symT FormalABC.C)⁻¹ x) = cInv (ico x) := by
  let z := (AddCircle.equivIco (1 : ℝ) 0).symm ⟨cInv (ico x), cInv_mem ⟨ico_nonneg x, by simpa using ico_lt_one x⟩⟩
  have hz : symT FormalABC.C z = x := by
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    change ico (symT FormalABC.C z) = ico x
    rw [ico_C, ico_symm]
    exact cFun_cInv ⟨ico_nonneg x, by simpa using ico_lt_one x⟩
  rw [inv_apply_eq_of hz, ico_symm]

end CannonFloydParry.S5

/-! Evaluating `A`, `B`, `C`, `π₀` and their inverses on `[0,1)` representatives. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

lemma piFun_of_mem1 {y : ℝ} (h1 : y < 1 / 2) : piFun y = y / 2 + 1 / 2 := by
  unfold piFun; rw [if_pos h1]

lemma piFun_of_mem2 {y : ℝ} (h0 : 1 / 2 ≤ y) (h1 : y < 3 / 4) : piFun y = 2 * y - 1 := by
  unfold piFun; rw [if_neg (by linarith), if_pos h1]

lemma piFun_of_mem3 {y : ℝ} (h0 : 3 / 4 ≤ y) : piFun y = y := by
  unfold piFun; rw [if_neg (by linarith), if_neg (by linarith)]

lemma ico_Av (x : UnitAddCircle) : ico (symV FormalV.A x) = aFun (ico x) := ico_A x
lemma ico_Bv (x : UnitAddCircle) : ico (symV FormalV.B x) = bFun (ico x) := ico_B x
lemma ico_Cv (x : UnitAddCircle) : ico (symV FormalV.C x) = cFun (ico x) := ico_C x
lemma ico_Avinv (x : UnitAddCircle) : ico ((symV FormalV.A)⁻¹ x) = aInv (ico x) := ico_Ainv x
lemma ico_Bvinv (x : UnitAddCircle) : ico ((symV FormalV.B)⁻¹ x) = bInv (ico x) := ico_Binv x
lemma ico_Cvinv (x : UnitAddCircle) : ico ((symV FormalV.C)⁻¹ x) = cInv (ico x) := ico_Cinv x

lemma ico_P (x : UnitAddCircle) : ico (symV FormalV.P x) = piFun (ico x) := by
  simp only [symV, mapPi0, Equiv.trans_apply, ico_symm]
  rfl

lemma mapPi0_mul_self : mapPi0 * mapPi0 = 1 := by
  apply perm_ext
  intro x
  have h := ico_P x
  simp only [symV] at h
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id]
  have h2 := ico_P (mapPi0 x)
  simp only [symV] at h2
  rw [h2, h, piFun_piFun ⟨ico_nonneg x, by simpa using ico_lt_one x⟩]

lemma mapPi0_inv : mapPi0⁻¹ = mapPi0 := inv_eq_of_mul_eq_one_right mapPi0_mul_self

lemma ico_Pinv (x : UnitAddCircle) : ico ((symV FormalV.P)⁻¹ x) = piFun (ico x) := by
  simp only [symV, mapPi0_inv]; exact ico_P x

end CannonFloydParry.S6

/-! Lifts of elements of `T` to the line, and the closure theorem (the first milestone): the
maps satisfying `IsThompsonCircle` form a group. -/

namespace CannonFloydParry.S5

/-! ### Dyadic arithmetic -/

lemma isDyadic_int (k : ℤ) : IsDyadic (k : ℝ) := ⟨k, 0, by simp⟩

lemma dy_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨n, l, rfl⟩ := hy
  refine ⟨m * 2 ^ l + n * 2 ^ k, k + l, ?_⟩
  push_cast
  field_simp
  ring

lemma dy_neg {x : ℝ} (hx : IsDyadic x) : IsDyadic (-x) := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨-m, k, by push_cast; ring⟩

lemma dy_sub {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x - y) := by
  simpa [sub_eq_add_neg] using dy_add hx (dy_neg hy)

lemma dy_zpow {x : ℝ} (hx : IsDyadic x) (n : ℤ) : IsDyadic ((2 : ℝ) ^ n * x) := by
  obtain ⟨m, k, rfl⟩ := hx
  rcases n with n | n
  · refine ⟨m * 2 ^ n, k, ?_⟩
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    push_cast
    ring
  · refine ⟨m, k + (n + 1), ?_⟩
    rw [zpow_negSucc, pow_add]
    field_simp
    ring

lemma dy_fract {x : ℝ} (hx : IsDyadic x) : IsDyadic (Int.fract x) := by
  rw [Int.fract]; exact dy_sub hx (isDyadic_int _)

/-! ### Good lifts -/

/-- `L` is affine with slope a power of `2` on every closed interval whose interior avoids the
integer translates of `B`. -/
def IsPL (L : ℝ ≃o ℝ) (B : Finset ℝ) : Prop :=
  ∀ x y : ℝ, x < y → (∀ t ∈ Set.Ioo x y, ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k) →
    ∃ (n : ℤ) (c : ℝ), ∀ z ∈ Set.Icc x y, L z = 2 ^ n * z + c

structure GoodLift (L : ℝ ≃o ℝ) : Prop where
  per : ∀ x, L (x + 1) = L x + 1
  dy : ∀ x, IsDyadic x → IsDyadic (L x)
  pl : ∃ B : Finset ℝ, (∀ b ∈ B, IsDyadic b) ∧ IsPL L B

namespace GoodLift
variable {L : ℝ ≃o ℝ}

lemma per_nat (hL : GoodLift L) (x : ℝ) (n : ℕ) : L (x + n) = L x + n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, ← add_assoc, hL.per, ih]; ring

lemma per_int (hL : GoodLift L) (x : ℝ) (k : ℤ) : L (x + k) = L x + k := by
  rcases k with n | n
  · simpa using hL.per_nat x n
  · have hc : ((Int.negSucc n : ℤ) : ℝ) = -((n : ℝ) + 1) := by rw [Int.cast_negSucc]; push_cast; ring
    have := hL.per_nat (x + ((Int.negSucc n : ℤ) : ℝ)) (n + 1)
    rw [hc] at this ⊢
    push_cast at this
    rw [show x + -((n : ℝ) + 1) + ((n : ℝ) + 1) = x by ring] at this
    linarith

lemma symm_per_int (hL : GoodLift L) (x : ℝ) (k : ℤ) : L.symm (x + k) = L.symm x + k := by
  apply L.injective
  rw [hL.per_int, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]

/-- The key fact: the inverse of a good lift maps dyadic rationals to dyadic rationals. -/
lemma symm_dy (hL : GoodLift L) (w : ℝ) (hw : IsDyadic w) : IsDyadic (L.symm w) := by
  obtain ⟨B, hB, hpl⟩ := hL.pl
  set z := L.symm w
  let S : Finset ℝ := insert ((⌊z⌋ : ℤ) : ℝ) (B.image fun b => b + ⌊z - b⌋)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  set x := S.max' hS
  have hxS : x ∈ S := S.max'_mem hS
  have hle : ∀ s ∈ S, s ≤ z := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact Int.floor_le z
    · obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hs
      linarith [Int.floor_le (z - b)]
  have hxz : x ≤ z := hle x hxS
  have hxdy : IsDyadic x := by
    rcases Finset.mem_insert.1 hxS with h | h
    · rw [h]; exact isDyadic_int _
    · obtain ⟨b, hb, h⟩ := Finset.mem_image.1 h
      rw [← h]; exact dy_add (hB b hb) (isDyadic_int _)
  rcases eq_or_lt_of_le hxz with h | h
  · rw [← h]; exact hxdy
  have havoid : ∀ t ∈ Set.Ioo x z, ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k := by
    rintro t ⟨ht1, ht2⟩ b hb k rfl
    have hk : k ≤ ⌊z - b⌋ := Int.le_floor.2 (by linarith)
    have : b + ⌊z - b⌋ ≤ x := S.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hb))
    have : (k : ℝ) ≤ ⌊z - b⌋ := by exact_mod_cast hk
    linarith
  obtain ⟨n, c, hc⟩ := hpl x z h havoid
  have hcx := hc x ⟨le_rfl, hxz⟩
  have hcz := hc z ⟨hxz, le_rfl⟩
  have hcdy : IsDyadic c := by
    have : c = L x - 2 ^ n * x := by linarith
    rw [this]; exact dy_sub (hL.dy x hxdy) (dy_zpow hxdy n)
  have hzw : L z = w := OrderIso.apply_symm_apply L w
  have : z = 2 ^ (-n) * (w - c) := by
    rw [← hzw, hcz, zpow_neg]
    field_simp
    ring
  rw [this]
  exact dy_zpow (dy_sub hw hcdy) _

lemma symm (hL : GoodLift L) : GoodLift L.symm := by
  obtain ⟨B, hB, hpl⟩ := hL.pl
  refine ⟨fun x => by simpa using hL.symm_per_int x 1, hL.symm_dy, B.image (fun b => Int.fract (L b)), ?_, ?_⟩
  · intro b' hb'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
    exact dy_fract (hL.dy b (hB b hb))
  · intro x y hxy havoid
    have hxy' : L.symm x < L.symm y := L.symm.strictMono hxy
    have havoid' : ∀ t ∈ Set.Ioo (L.symm x) (L.symm y), ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k := by
      rintro t ⟨ht1, ht2⟩ b hb k rfl
      refine havoid (L (b + k)) ⟨?_, ?_⟩ (Int.fract (L b)) (Finset.mem_image_of_mem _ hb) (⌊L b⌋ + k) ?_
      · have := L.strictMono ht1; rwa [OrderIso.apply_symm_apply] at this
      · have := L.strictMono ht2; rwa [OrderIso.apply_symm_apply] at this
      · rw [hL.per_int]; push_cast; rw [Int.fract]; ring
    obtain ⟨n, c, hc⟩ := hpl _ _ hxy' havoid'
    refine ⟨-n, -(2 ^ (-n) * c), fun z hz => ?_⟩
    have hs : L.symm z ∈ Set.Icc (L.symm x) (L.symm y) :=
      ⟨L.symm.monotone hz.1, L.symm.monotone hz.2⟩
    have := hc _ hs
    rw [OrderIso.apply_symm_apply] at this
    rw [zpow_neg]
    field_simp
    linarith

lemma trans {L₁ L₂ : ℝ ≃o ℝ} (h₁ : GoodLift L₁) (h₂ : GoodLift L₂) : GoodLift (L₁.trans L₂) := by
  obtain ⟨B₁, hB₁, hpl₁⟩ := h₁.pl
  obtain ⟨B₂, hB₂, hpl₂⟩ := h₂.pl
  refine ⟨fun x => by simp [h₁.per, h₂.per], fun x hx => h₂.dy _ (h₁.dy x hx),
    B₁ ∪ B₂.image (fun b => Int.fract (L₁.symm b)), ?_, ?_⟩
  · intro b hb
    rcases Finset.mem_union.1 hb with hb | hb
    · exact hB₁ b hb
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
      exact dy_fract (h₁.symm_dy b' (hB₂ b' hb'))
  · intro x y hxy havoid
    obtain ⟨m, c₁, hc₁⟩ := hpl₁ x y hxy (fun t ht b hb k => havoid t ht b (Finset.mem_union_left _ hb) k)
    have hxy' : L₁ x < L₁ y := L₁.strictMono hxy
    have havoid' : ∀ t ∈ Set.Ioo (L₁ x) (L₁ y), ∀ b ∈ B₂, ∀ k : ℤ, t ≠ b + k := by
      rintro t ⟨ht1, ht2⟩ b hb k rfl
      refine havoid (L₁.symm (b + k)) ⟨?_, ?_⟩ (Int.fract (L₁.symm b))
        (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb)) (⌊L₁.symm b⌋ + k) ?_
      · have := L₁.symm.strictMono ht1; rwa [OrderIso.symm_apply_apply] at this
      · have := L₁.symm.strictMono ht2; rwa [OrderIso.symm_apply_apply] at this
      · rw [h₁.symm_per_int]; push_cast; rw [Int.fract]; ring
    obtain ⟨n, c₂, hc₂⟩ := hpl₂ _ _ hxy' havoid'
    refine ⟨n + m, 2 ^ n * c₁ + c₂, fun z hz => ?_⟩
    have hz' : L₁ z ∈ Set.Icc (L₁ x) (L₁ y) := ⟨L₁.monotone hz.1, L₁.monotone hz.2⟩
    simp only [OrderIso.trans_apply]
    rw [hc₂ _ hz', hc₁ z hz, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring

end GoodLift

/-! ### The closure theorem -/


end CannonFloydParry.S5

/-! `T ≤ V` and `π₀ ∈ V` (CFP p. 240). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

lemma circ_ext {p q : UnitAddCircle} (h : ico p = ico q) : p = q :=
  (AddCircle.equivIco (1 : ℝ) 0).injective (Subtype.ext h)

lemma coe_fract (x : ℝ) : ((Int.fract x : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  rw [Int.fract, sub_eq_add_neg, AddCircle.coe_add]
  have : (((-⌊x⌋ : ℤ) : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]; exact ⟨-⌊x⌋, by simp⟩
  push_cast at this
  rw [this, add_zero]

lemma ico_coe (x : ℝ) : ico (x : UnitAddCircle) = Int.fract x := by
  rw [← coe_fract, ico, AddCircle.equivIco_coe_eq ⟨Int.fract_nonneg x, by
    simpa using Int.fract_lt_one x⟩]

lemma mapPi0_coe (z : ℝ) : mapPi0 (z : UnitAddCircle) = ((piFun (Int.fract z) : ℝ) : UnitAddCircle) := by
  apply circ_ext
  have h := ico_P (z : UnitAddCircle)
  simp only [symV] at h
  obtain ⟨m0, m1⟩ := piFun_mem (x := Int.fract z) ⟨Int.fract_nonneg z, by
    simpa using Int.fract_lt_one z⟩
  rw [h, ico_coe, ico_coe, Int.fract_eq_self.2 ⟨m0, by simpa using m1⟩]

theorem T_le_V_and_mapPi0_mem_V' : T ≤ V ∧ mapPi0 ∈ V :=
  by
  first
    | exact CannonFloydParry.T_le_V_and_mapPi0_mem_V
    | exact CannonFloydParry.T_le_V_and_mapPi0_mem_V ..
    | (apply CannonFloydParry.T_le_V_and_mapPi0_mem_V <;> first | assumption | infer_instance)
    | simpa using CannonFloydParry.T_le_V_and_mapPi0_mem_V


end CannonFloydParry.S6

/-! Generation, part 1: the subgroup `G = ⟨A, B, C, π₀⟩` contains `F` and `T`; any two standard
dyadic partitions with the same number of pieces are matched, affinely on pieces, by an
element of `F`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

/-- `G = ⟨A, B, C, π₀⟩`. -/
abbrev G : Subgroup (Equiv.Perm UnitAddCircle) := Subgroup.closure (Set.range symV)

lemma symV_mem_G (s : FormalV) : symV s ∈ G := Subgroup.subset_closure ⟨s, rfl⟩

lemma toCircle_mem_G {f : UI ≃o UI} (hf : f ∈ F) : toCircle f ∈ G := by
  rw [← closure_mapA_mapB_eq_F] at hf
  have : (Subgroup.closure ({mapA, mapB} : Set (UI ≃o UI))).map toCircleHom ≤ G := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rcases hg with rfl | rfl
    · exact symV_mem_G FormalV.A
    · exact symV_mem_G FormalV.B
  exact this ⟨f, hf, rfl⟩

lemma T_le_G : T ≤ G := by
  rw [← closure_range_symT_eq_T_and_relations.1, Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  cases s
  · exact symV_mem_G FormalV.A
  · exact symV_mem_G FormalV.B
  · exact symV_mem_G FormalV.C

/-- Two standard dyadic partitions with the same number of pieces are matched by an element of
`F` that is affine on every piece. -/
lemma exists_F_affine {xs ys : List ℝ} (hx : IsStandardDyadicPartition xs)
    (hy : IsStandardDyadicPartition ys) (hlen : xs.length = ys.length) :
    ∃ f ∈ F, AffineOnPieces (extend f) xs ∧ xs.map (extend f) = ys := by
  obtain ⟨R, rfl⟩ := exists_tree_marks hx
  obtain ⟨S, rfl⟩ := exists_tree_marks hy
  have hRS : R.leafCount = S.leafCount := by
    have := hlen; rw [marks_length_eq, marks_length_eq] at this; omega
  have hn : R.leafCount = (TTree.comb (R.leafCount - 1)).leafCount := by
    rw [leafCount_comb]; have := one_le_leafCount' R; omega
  have hnS : S.leafCount = (TTree.comb (R.leafCount - 1)).leafCount := hRS ▸ hn
  have h1 := represents_word_inv _ R _ hn le_rfl
  have h2 := represents_word_inv _ S _ hnS le_rfl
  have h3 := represents_inv _ h2
  have h4 := represents_mul hn hnS.symm h1 h3
  exact ⟨_, h4.1, h4.2.1, h4.2.2⟩

/-- Rotation of the circle by `1/2^L`. -/
noncomputable def rot (L : ℕ) : Equiv.Perm UnitAddCircle :=
  Equiv.addRight (((1 : ℝ) / 2 ^ L : ℝ) : UnitAddCircle)

lemma rot_coe (L : ℕ) (z : ℝ) : rot L (z : UnitAddCircle) = ((z + 1 / 2 ^ L : ℝ) : UnitAddCircle) := by
  simp [rot, AddCircle.coe_add]

lemma rot_mem_G (L : ℕ) : rot L ∈ G := by
  apply T_le_G
  apply Subgroup.subset_closure
  refine ⟨OrderIso.addRight ((1 : ℝ) / 2 ^ L), fun x => by simp; ring, fun x => rot_coe L x,
    fun x hx => ?_, ∅, by simp, fun x y _ _ => ⟨0, 1 / 2 ^ L, fun z _ => by simp⟩⟩
  simpa using dy_add hx (⟨1, L, by push_cast; ring⟩ : IsDyadic ((1 : ℝ) / 2 ^ L))

end CannonFloydParry.S6

/-! For `f` satisfying `IsThompsonV`: a uniform dyadic partition on whose pieces `f` is affine and
carries each piece onto a standard dyadic interval. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

/-- `x · 2ᵈ` is an integer. -/
def IntAt (x : ℝ) (d : ℕ) : Prop := ∃ z : ℤ, x * 2 ^ d = z

lemma IntAt.mono {x : ℝ} {d d' : ℕ} (h : IntAt x d) (hd : d ≤ d') : IntAt x d' := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨e, rfl⟩ : ∃ e, d' = d + e := ⟨d' - d, by omega⟩
  exact ⟨z * 2 ^ e, by rw [pow_add, ← mul_assoc, hz]; push_cast; ring⟩

lemma dy_intAt {x : ℝ} (hx : IsDyadic x) : ∃ d, IntAt x d := by
  obtain ⟨m, k, rfl⟩ := hx
  exact ⟨k, m, by field_simp⟩

lemma coe_eq_coe {a b : ℝ} (h : (a : UnitAddCircle) = b) : ∃ m : ℤ, b = a + m := by
  have := QuotientAddGroup.eq.1 h
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 this
  exact ⟨m, by simp at hm; linarith⟩

lemma coe_add_int (a : ℝ) (m : ℤ) : ((a + m : ℝ) : UnitAddCircle) = (a : UnitAddCircle) := by
  rw [AddCircle.coe_add]
  have : ((m : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]; exact ⟨m, by simp⟩
  rw [this, add_zero]

lemma dy_div_two_pow (j M : ℕ) : IsDyadic ((j : ℝ) / 2 ^ M) := ⟨j, M, by push_cast; ring⟩

/-- Level `M₀`: `f` is `z ↦ 2ᵏ z + c`, with `c` dyadic, on each `[j/2^M₀, (j+1)/2^M₀)`. -/
lemma uniform_affine {f : Equiv.Perm UnitAddCircle} (hf : IsThompsonV f) :
    ∃ M0 : ℕ, ∀ j : ℕ, j < 2 ^ M0 → ∃ (k : ℤ) (c : ℝ), IsDyadic c ∧
      ∀ z ∈ Set.Ico ((j : ℝ) / 2 ^ M0) ((j + 1) / 2 ^ M0),
        f (z : UnitAddCircle) = ((2 ^ k * z + c : ℝ) : UnitAddCircle) := by
  obtain ⟨hdy, B, hB, hpl⟩ := hf
  have hd : ∀ b ∈ B, ∃ d, IntAt b d := fun b hb => dy_intAt (hB b hb)
  choose! db hdb using hd
  refine ⟨B.sup db, fun j _ => ?_⟩
  set M0 := B.sup db
  have hpos : (0 : ℝ) < 2 ^ M0 := by positivity
  have hav : ∀ t ∈ Set.Ioo ((j : ℝ) / 2 ^ M0) ((j + 1) / 2 ^ M0), ∀ b ∈ B, ∀ k : ℤ, t ≠ b + k := by
    intro t ht b hb k htb
    obtain ⟨z, hz⟩ := (hdb b hb).mono (Finset.le_sup hb)
    have h1 : (j : ℝ) < t * 2 ^ M0 := by rw [← div_lt_iff₀ hpos]; exact ht.1
    have h2 : t * 2 ^ M0 < j + 1 := by rw [← lt_div_iff₀ hpos]; exact ht.2
    have e : t * 2 ^ M0 = ((z + k * 2 ^ M0 : ℤ) : ℝ) := by rw [htb, add_mul, hz]; push_cast; ring
    rw [e] at h1 h2
    have h1' : (j : ℤ) < z + k * 2 ^ M0 := by exact_mod_cast h1
    have h2' : z + k * 2 ^ M0 < (j : ℤ) + 1 := by exact_mod_cast h2
    omega
  have hlt : (j : ℝ) / 2 ^ M0 < (j + 1) / 2 ^ M0 := by
    rw [div_lt_div_iff_of_pos_right hpos]; linarith
  obtain ⟨n, c, hc⟩ := hpl _ _ hlt hav
  refine ⟨n, c, ?_, hc⟩
  obtain ⟨d, hd, hfx⟩ := hdy _ (dy_div_two_pow j M0)
  rw [hc _ ⟨le_rfl, hlt⟩] at hfx
  obtain ⟨m, hm⟩ := coe_eq_coe hfx
  have : c = d - m - 2 ^ n * ((j : ℝ) / 2 ^ M0) := by linarith
  rw [this]
  exact dy_sub (dy_sub hd (isDyadic_int m)) (dy_zpow (dy_div_two_pow j M0) n)

end CannonFloydParry.S6

namespace CannonFloydParry.S6

open CannonFloydParry.S5

/-- A finer uniform level at which every piece is carried onto a standard dyadic interval:
on `[j/2^M, (j+1)/2^M)`, `f` is `z ↦ A/2^m + 2ᵏ (z - j/2^M)` with `2ᵏ·2^m = 2^M`, `A < 2^m`. -/
lemma uniform_std {f : Equiv.Perm UnitAddCircle} (hf : IsThompsonV f) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ j : ℕ, j < 2 ^ M → ∃ (k : ℤ) (m A : ℕ), A + 1 ≤ 2 ^ m ∧
      (2 : ℝ) ^ k * 2 ^ m = 2 ^ M ∧
      ∀ z ∈ Set.Ico ((j : ℝ) / 2 ^ M) ((j + 1) / 2 ^ M),
        f (z : UnitAddCircle) = (((A : ℝ) / 2 ^ m + 2 ^ k * (z - j / 2 ^ M) : ℝ) : UnitAddCircle) := by
  obtain ⟨M0, h0⟩ := uniform_affine hf
  have h1 : ∀ j : Fin (2 ^ M0), ∃ (k : ℤ) (c : ℝ), IsDyadic c ∧
      ∀ z ∈ Set.Ico ((j : ℝ) / 2 ^ M0) ((j + 1) / 2 ^ M0),
        f (z : UnitAddCircle) = ((2 ^ k * z + c : ℝ) : UnitAddCircle) := fun j => h0 j j.2
  choose K C hC hK using h1
  have h2 : ∀ j : Fin (2 ^ M0), ∃ d, IntAt (C j) d := fun j => dy_intAt (hC j)
  choose D hD using h2
  obtain ⟨E, hE2, hkE_all⟩ : ∃ E : ℕ, 2 ≤ E ∧ ∀ j : Fin (2 ^ M0), (K j).toNat + D j ≤ E :=
    ⟨Finset.univ.sup (fun j : Fin (2 ^ M0) => (K j).toNat + D j) + 2, Nat.le_add_left _ _,
      fun j => le_trans (Finset.le_sup (f := fun j : Fin (2 ^ M0) => (K j).toNat + D j)
        (Finset.mem_univ j)) (Nat.le_add_right _ _)⟩
  refine ⟨M0 + E, by omega, fun j' hj' => ?_⟩
  have hE : (0 : ℕ) < 2 ^ E := by positivity
  set q := j' / 2 ^ E
  have hq : q < 2 ^ M0 := by
    rw [Nat.div_lt_iff_lt_mul hE, ← pow_add]; exact hj'
  set jq : Fin (2 ^ M0) := ⟨q, hq⟩
  set k := K jq
  set c := C jq
  have hkE : k.toNat + D jq ≤ E := hkE_all jq
  have hk_le : k ≤ k.toNat := Int.self_le_toNat k
  set m := ((M0 + E : ℕ) - k).toNat
  have hm : (m : ℤ) = (M0 + E : ℕ) - k := Int.toNat_of_nonneg (by push_cast; omega)
  have hDm : D jq ≤ m := by omega
  have hpow : (2 : ℝ) ^ k * 2 ^ m = 2 ^ (M0 + E) := by
    rw [← zpow_natCast (2 : ℝ) m, ← zpow_natCast (2 : ℝ) (M0 + E), ← zpow_add₀ two_ne_zero, hm]
    congr 1; ring
  -- the level-`M0` piece containing the level-`M0+E` piece `j'`
  have hdm : 2 ^ E * q + j' % 2 ^ E = j' := Nat.div_add_mod j' (2 ^ E)
  have hmod : j' % 2 ^ E < 2 ^ E := Nat.mod_lt j' hE
  have hsub : Set.Ico ((j' : ℝ) / 2 ^ (M0 + E)) ((j' + 1) / 2 ^ (M0 + E)) ⊆
      Set.Ico ((q : ℝ) / 2 ^ M0) ((q + 1) / 2 ^ M0) := by
    intro z ⟨hz1, hz2⟩
    have e1 : (q : ℝ) / 2 ^ M0 = (q * 2 ^ E : ℕ) / 2 ^ (M0 + E) := by
      push_cast; rw [pow_add]; field_simp
    have e2 : ((q : ℝ) + 1) / 2 ^ M0 = ((q + 1) * 2 ^ E : ℕ) / 2 ^ (M0 + E) := by
      push_cast; rw [pow_add]; field_simp
    have hpos : (0 : ℝ) < 2 ^ (M0 + E) := by positivity
    constructor
    · rw [e1]; refine le_trans ?_ hz1
      apply div_le_div_of_nonneg_right _ hpos.le
      have : q * 2 ^ E ≤ j' := Nat.div_mul_le_self j' (2 ^ E)
      exact_mod_cast this
    · rw [e2]; refine lt_of_lt_of_le hz2 ?_
      apply div_le_div_of_nonneg_right _ hpos.le
      have : j' + 1 ≤ (q + 1) * 2 ^ E := by nlinarith
      exact_mod_cast this
  -- the left endpoint of the image
  set x' : ℝ := (j' : ℝ) / 2 ^ (M0 + E)
  set u : ℝ := 2 ^ k * x' + c
  have hu : IntAt u m := by
    obtain ⟨z, hz⟩ := (hD jq).mono hDm
    refine ⟨j' + z, ?_⟩
    have : (2 : ℝ) ^ k * x' * 2 ^ m = j' := by
      calc (2 : ℝ) ^ k * x' * 2 ^ m = ((2 : ℝ) ^ k * 2 ^ m) * x' := by ring
        _ = j' := by rw [hpow]; simp only [x']; field_simp
    simp only [u]; rw [add_mul, this, hz]; push_cast; ring
  obtain ⟨zu, hzu⟩ := hu
  have hfr : ∃ A : ℕ, Int.fract u * 2 ^ m = A ∧ A + 1 ≤ 2 ^ m := by
    have e : Int.fract u * 2 ^ m = ((zu - ⌊u⌋ * 2 ^ m : ℤ) : ℝ) := by
      rw [Int.fract, sub_mul, hzu]; push_cast; ring
    have h0 : (0 : ℝ) ≤ Int.fract u * 2 ^ m := by positivity
    have h1 : Int.fract u * 2 ^ m < 2 ^ m := by
      have := Int.fract_lt_one u; nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) m]
    rw [e] at h0 h1
    have h0' : (0 : ℤ) ≤ zu - ⌊u⌋ * 2 ^ m := by exact_mod_cast h0
    have h1' : zu - ⌊u⌋ * 2 ^ m < 2 ^ m := by exact_mod_cast h1
    refine ⟨(zu - ⌊u⌋ * 2 ^ m).toNat, ?_, ?_⟩
    · rw [e, show (((zu - ⌊u⌋ * 2 ^ m).toNat : ℕ) : ℝ) = (((zu - ⌊u⌋ * 2 ^ m).toNat : ℤ) : ℝ) by
        norm_cast, Int.toNat_of_nonneg h0']
    · have : ((zu - ⌊u⌋ * 2 ^ m).toNat : ℤ) + 1 ≤ 2 ^ m := by rw [Int.toNat_of_nonneg h0']; omega
      exact_mod_cast this
  obtain ⟨A, hA, hA1⟩ := hfr
  refine ⟨k, m, A, hA1, hpow, fun z hz => ?_⟩
  rw [hK jq z (hsub hz)]
  have e : (2 : ℝ) ^ k * z + c = ((A : ℝ) / 2 ^ m + 2 ^ k * (z - x')) + ⌊u⌋ := by
    have : (A : ℝ) / 2 ^ m = Int.fract u := by rw [← hA]; field_simp
    rw [this, Int.fract]; simp only [u]; ring
  rw [e, coe_add_int]

end CannonFloydParry.S6

/-! Generation, part 2: permutations of the pieces of the uniform partition `[j/2^L, (j+1)/2^L)`
realised by translations inside `G`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

/-- `w` translates the `j`th piece of the level-`L` uniform partition onto the `τ j`th. -/
def Realizes (L : ℕ) (w : Equiv.Perm UnitAddCircle) (τ : Equiv.Perm (Fin (2 ^ L))) : Prop :=
  ∀ j : Fin (2 ^ L), ∀ z ∈ Set.Ico ((j : ℝ) / 2 ^ L) ((j + 1) / 2 ^ L),
    w (z : UnitAddCircle) = ((z + (((τ j : ℕ) : ℝ) - j) / 2 ^ L : ℝ) : UnitAddCircle)

lemma shift_mem {L : ℕ} {j i : ℕ} {z : ℝ} (hz : z ∈ Set.Ico ((j : ℝ) / 2 ^ L) ((j + 1) / 2 ^ L)) :
    z + ((i : ℝ) - j) / 2 ^ L ∈ Set.Ico ((i : ℝ) / 2 ^ L) ((i + 1) / 2 ^ L) := by
  have e1 : (i : ℝ) / 2 ^ L = j / 2 ^ L + ((i : ℝ) - j) / 2 ^ L := by ring
  have e2 : ((i : ℝ) + 1) / 2 ^ L = (j + 1) / 2 ^ L + ((i : ℝ) - j) / 2 ^ L := by ring
  exact ⟨by rw [e1]; linarith [hz.1], by rw [e2]; linarith [hz.2]⟩

/-- The permutations realised inside `G`. -/
def RS (L : ℕ) : Subgroup (Equiv.Perm (Fin (2 ^ L))) where
  carrier := {τ | ∃ w ∈ G, Realizes L w τ}
  one_mem' := ⟨1, one_mem _, fun j z _ => by simp⟩
  mul_mem' := by
    rintro τ₁ τ₂ ⟨w₁, h₁, r₁⟩ ⟨w₂, h₂, r₂⟩
    refine ⟨w₁ * w₂, mul_mem h₁ h₂, fun j z hz => ?_⟩
    rw [Equiv.Perm.mul_apply, r₂ j z hz, r₁ (τ₂ j) _ (shift_mem hz)]
    congr 1
    simp only [Equiv.Perm.mul_apply]
    ring
  inv_mem' := by
    rintro τ ⟨w, h, r⟩
    refine ⟨w⁻¹, inv_mem h, fun j z hz => ?_⟩
    set i := τ⁻¹ j
    have hi : τ i = j := by simp [i]
    have hz' := shift_mem (i := i) hz
    have := r i _ hz'
    rw [hi] at this
    rw [Equiv.Perm.inv_eq_iff_eq, this]
    congr 1
    ring

lemma rot_realizes (L : ℕ) (hL : 1 ≤ L) : Realizes L (rot L) (finRotate (2 ^ L)) := by
  have hN : 2 ≤ 2 ^ L := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  intro j z hz
  haveI : NeZero (2 ^ L) := ⟨by positivity⟩
  rw [rot_coe, finRotate_apply]
  have hval : (((j + 1 : Fin (2 ^ L)) : ℕ)) = ((j : ℕ) + 1) % 2 ^ L := by
    rw [Fin.val_add, Fin.val_one', Nat.one_mod_eq_one.2 (by omega)]
  rcases lt_or_ge ((j : ℕ) + 1) (2 ^ L) with h | h
  · rw [hval, Nat.mod_eq_of_lt h]; congr 1; push_cast; ring
  · have hj : (j : ℕ) + 1 = 2 ^ L := le_antisymm (by omega) h
    rw [hval, hj, Nat.mod_self]
    have : z + (((0 : ℕ) : ℝ) - j) / 2 ^ L = (z + 1 / 2 ^ L) + ((-1 : ℤ) : ℝ) := by
      have e : (j : ℝ) = 2 ^ L - 1 := by
        have : ((j : ℕ) : ℝ) + 1 = 2 ^ L := by exact_mod_cast hj
        linarith
      rw [e]; push_cast; field_simp; ring
    rw [this, coe_add_int]

end CannonFloydParry.S6

/-! Generation, part 3: the swap of the first two uniform pieces lies in `G`, so every
permutation of the pieces is realised in `G`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

lemma extend_lt_one (f : UI ≃o UI) {z : ℝ} (hz : z ∈ Set.Ico (0 : ℝ) 1) : extend f z < 1 := by
  have h1 : extend f 1 = 1 := by
    have := extend_coe f ⟨1, one_mem_UI⟩; rw [this, coe_apply_one]
  rw [← h1]; exact (extend f).strictMono hz.2

lemma extend_nonneg (f : UI ≃o UI) {z : ℝ} (hz : z ∈ Set.Ico (0 : ℝ) 1) : 0 ≤ extend f z := by
  have h0 : extend f 0 = 0 := by
    have := extend_coe f ⟨0, zero_mem_UI⟩; rw [this, coe_apply_zero]
  rw [← h0]; exact (extend f).monotone hz.1

lemma toCircle_coe (f : UI ≃o UI) {z : ℝ} (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    toCircle f (z : UnitAddCircle) = ((extend f z : ℝ) : UnitAddCircle) := by
  apply circ_ext
  have hico : ico (z : UnitAddCircle) = z := by rw [ico_coe, Int.fract_eq_self.2 hz]
  have hUI : (⟨ico (z : UnitAddCircle), ico_nonneg _, (ico_lt_one _).le⟩ : UI) = ⟨z, hz.1, hz.2.le⟩ :=
    Subtype.ext hico
  rw [ico_toCircle, hUI, ico_coe, Int.fract_eq_self.2 ⟨extend_nonneg f hz, extend_lt_one f hz⟩]
  exact (extend_coe f ⟨z, hz.1, hz.2.le⟩).symm

lemma two_pow_div_two_pow {a b : ℕ} (h : a ≤ b) : (2 : ℝ) ^ a / 2 ^ b = 1 / 2 ^ (b - a) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  rw [Nat.add_sub_cancel_left, pow_add]; field_simp

/-- `[0, 1/N, 2/N, 4/N, …, 1/2, 1]`, `N = 2^L`. -/
noncomputable def pDoub (L : ℕ) (i : Fin (L + 2)) : ℝ :=
  if (i : ℕ) = 0 then 0 else 2 ^ ((i : ℕ) - 1) / 2 ^ L

/-- The comb `[0, 1/2, 3/4, …, 1 - 2^{-L}, 1]`. -/
noncomputable def pComb (L : ℕ) (i : Fin (L + 2)) : ℝ :=
  if (i : ℕ) = L + 1 then 1 else 1 - 1 / 2 ^ (i : ℕ)

lemma pDoub_std (L : ℕ) : IsStandardDyadicPartition (List.ofFn (pDoub L)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.ofFn_succ, List.head?_cons]; simp [pDoub]
  · rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_append]
    simp [pDoub]
  · rw [List.isChain_ofFn]
    intro i hi
    simp only [pDoub]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨0, L, Nat.one_le_two_pow, by simp, by simp⟩
    · rw [if_neg (by omega), if_neg (by omega)]
      have h2 : 2 ≤ 2 ^ (L - i + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (L - i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine ⟨1, L - i + 1, by omega, ?_, ?_⟩
      · rw [two_pow_div_two_pow (by omega), show L - (i - 1) = L - i + 1 by omega]; simp
      · rw [show i + 1 - 1 = i by omega, two_pow_div_two_pow (by omega), pow_succ]
        push_cast; field_simp; norm_num

lemma pComb_std (L : ℕ) : IsStandardDyadicPartition (List.ofFn (pComb L)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.ofFn_succ, List.head?_cons]; simp [pComb]
  · rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_append]
    simp [pComb]
  · rw [List.isChain_ofFn]
    intro i hi
    simp only [pComb]
    rw [if_neg (by omega)]
    have hp : (0 : ℝ) < 2 ^ i := by positivity
    rcases lt_or_ge (i + 1) (L + 1) with h | h
    · rw [if_neg (by omega)]
      have h2 : (2 : ℕ) ≤ 2 ^ (i + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine ⟨2 ^ (i + 1) - 2, i + 1, by omega, ?_, ?_⟩
      · rw [Nat.cast_sub h2]; push_cast; rw [pow_succ]; field_simp; try ring
      · rw [Nat.cast_sub h2]; push_cast; field_simp; try ring
    · rw [if_pos (by omega)]
      obtain rfl : i = L := by omega
      refine ⟨2 ^ i - 1, i, by have := Nat.one_le_two_pow (n := i); omega, ?_, ?_⟩
      · rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; field_simp; try ring
      · rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; field_simp; try ring

end CannonFloydParry.S6

/-! Generation, part 4: every permutation of the uniform pieces is realised in `G`. -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

lemma mapPi0_coe_of_mem {v : ℝ} (hv : v ∈ Set.Ico (0 : ℝ) 1) :
    mapPi0 (v : UnitAddCircle) = ((piFun v : ℝ) : UnitAddCircle) := by
  rw [mapPi0_coe, Int.fract_eq_self.2 hv]

lemma affine_of_endpoints {g : ℝ → ℝ} {p q u v a b : ℝ} (hpq : p < q)
    (h : ∀ z ∈ Set.Icc p q, g z = a * z + b) (hu : g p = u) (hv : g q = v) :
    ∀ z ∈ Set.Icc p q, g z = u + (v - u) / (q - p) * (z - p) := by
  intro z hz
  have hp := h p ⟨le_rfl, hpq.le⟩
  have hq := h q ⟨hpq.le, le_rfl⟩
  have ha : a = (v - u) / (q - p) := by
    rw [eq_div_iff (by linarith)]; linarith
  rw [h z hz, ha]
  have hb : b = u - (v - u) / (q - p) * p := by rw [← ha]; linarith
  rw [hb]; ring

theorem swap_mem_RS (L : ℕ) (hL : 2 ≤ L) :
    Equiv.swap (⟨0, by positivity⟩ : Fin (2 ^ L)) ⟨1, Nat.one_lt_two_pow (by omega)⟩ ∈ RS L := by
  have hN4 : (4 : ℝ) ≤ 2 ^ L := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hL
  have hp : (0 : ℝ) < 2 ^ L := by positivity
  obtain ⟨t, htF, haff, hmap⟩ := exists_F_affine (pDoub_std L) (pComb_std L) (by simp)
  have hval : ∀ i, extend t (pDoub L i) = pComb L i := by
    rw [List.map_ofFn] at hmap
    exact congrFun (List.ofFn_injective hmap)
  -- the relevant partition points
  have v0 : pDoub L ⟨0, by omega⟩ = 0 := by unfold pDoub; rw [if_pos rfl]
  have v1 : pDoub L ⟨0 + 1, by omega⟩ = 1 / 2 ^ L := by
    unfold pDoub; rw [if_neg (by simp only [Fin.val_mk]; omega)]; norm_num
  have v1' : pDoub L ⟨1, by omega⟩ = 1 / 2 ^ L := v1
  have v2 : pDoub L ⟨1 + 1, by omega⟩ = 2 / 2 ^ L := by
    unfold pDoub; rw [if_neg (by simp only [Fin.val_mk]; omega)]; norm_num
  have c0 : pComb L ⟨0, by omega⟩ = 0 := by
    unfold pComb; rw [if_neg (by simp only [Fin.val_mk]; omega)]; norm_num
  have c1 : pComb L ⟨0 + 1, by omega⟩ = 1 / 2 := by
    unfold pComb; rw [if_neg (by simp only [Fin.val_mk]; omega)]; norm_num
  have c2 : pComb L ⟨1 + 1, by omega⟩ = 3 / 4 := by
    unfold pComb; rw [if_neg (by simp only [Fin.val_mk]; omega)]; norm_num
  unfold AffineOnPieces at haff
  rw [List.isChain_ofFn] at haff
  obtain ⟨a0, b0, h0⟩ := haff 0 (by omega)
  obtain ⟨a1, b1, h1⟩ := haff 1 (by omega)
  rw [v0, v1] at h0
  rw [v1', v2] at h1
  have e0 : extend t 0 = 0 := by have := hval ⟨0, by omega⟩; rwa [v0, c0] at this
  have e1 : extend t (1 / 2 ^ L) = 1 / 2 := by have := hval ⟨0 + 1, by omega⟩; rwa [v1, c1] at this
  have e2 : extend t (2 / 2 ^ L) = 3 / 4 := by have := hval ⟨1 + 1, by omega⟩; rwa [v2, c2] at this
  have hlt01 : (0 : ℝ) < 1 / 2 ^ L := by positivity
  have hlt12 : (1 : ℝ) / 2 ^ L < 2 / 2 ^ L := by
    rw [div_lt_div_iff_of_pos_right hp]; norm_num
  have hf0 : ∀ z ∈ Set.Icc (0 : ℝ) (1 / 2 ^ L), extend t z = 2 ^ L / 2 * z := by
    intro z hz
    rw [affine_of_endpoints hlt01 h0 e0 e1 z hz]
    field_simp; ring
  have hf1 : ∀ z ∈ Set.Icc (1 / 2 ^ L : ℝ) (2 / 2 ^ L), extend t z = 2 ^ L / 4 * z + 1 / 4 := by
    intro z hz
    rw [affine_of_endpoints hlt12 h1 e1 e2 z hz]
    field_simp; ring
  have hge : ∀ z, 2 / 2 ^ L ≤ z → 3 / 4 ≤ extend t z := fun z hz => by
    rw [← e2]; exact (extend t).monotone hz
  -- the element
  set s := (toCircle t)⁻¹ * mapPi0 * toCircle t
  have hs : s ∈ G := mul_mem (mul_mem (inv_mem (toCircle_mem_G htF)) (symV_mem_G FormalV.P))
    (toCircle_mem_G htF)
  refine ⟨s, hs, fun j z hz => ?_⟩
  have hz01 : z ∈ Set.Ico (0 : ℝ) 1 := by
    refine ⟨le_trans (by positivity) hz.1, lt_of_lt_of_le hz.2 ?_⟩
    rw [div_le_one hp]; have : (j : ℕ) + 1 ≤ 2 ^ L := j.2; exact_mod_cast this
  have hq : (1 : ℝ) / 2 ^ L ≤ 1 / 4 := by
    rw [div_le_div_iff_of_pos_left one_pos hp (by norm_num)]; exact hN4
  simp only [s, Equiv.Perm.mul_apply]
  rw [toCircle_coe t hz01]
  obtain ⟨hz1, hz2⟩ := hz
  rcases Nat.lt_or_ge (j : ℕ) 2 with hj | hj
  · interval_cases hj' : (j : ℕ)
    · -- piece 0 goes to piece 1
      have hj0 : j = ⟨0, by positivity⟩ := Fin.ext hj'
      simp only [Nat.cast_zero, zero_div, zero_add] at hz1 hz2
      rw [hf0 z ⟨hz1, hz2.le⟩]
      have hv : 2 ^ L / 2 * z < 1 / 2 := by
        rw [lt_div_iff₀ hp] at hz2
        have : 2 ^ L / 2 * z = (z * 2 ^ L) / 2 := by ring
        rw [this]; linarith
      rw [mapPi0_coe_of_mem ⟨by positivity, by linarith⟩, piFun_of_mem1 hv]
      apply inv_apply_eq_of
      rw [hj0, Equiv.swap_apply_left]
      simp only [Nat.cast_one, Nat.cast_zero, sub_zero]
      have hw1 : 1 / 2 ^ L ≤ z + 1 / 2 ^ L := by linarith
      have hw2 : z + 1 / 2 ^ L ≤ 2 / 2 ^ L := by
        have : (2 : ℝ) / 2 ^ L = 1 / 2 ^ L + 1 / 2 ^ L := by ring
        linarith
      rw [toCircle_coe t ⟨by linarith, by linarith⟩, hf1 _ ⟨hw1, hw2⟩]
      congr 1; field_simp; ring
    · -- piece 1 goes to piece 0
      have hj1 : j = ⟨1, Nat.one_lt_two_pow (by omega)⟩ := Fin.ext hj'
      simp only [Nat.cast_one] at hz1 hz2
      rw [show ((1 : ℝ) + 1) = 2 by norm_num] at hz2
      rw [hf1 z ⟨hz1, hz2.le⟩]
      have hv1 : 1 / 2 ≤ 2 ^ L / 4 * z + 1 / 4 := by
        rw [div_le_iff₀ hp] at hz1
        have : 2 ^ L / 4 * z = (z * 2 ^ L) / 4 := by ring
        rw [this]; linarith
      have hv2 : 2 ^ L / 4 * z + 1 / 4 < 3 / 4 := by
        rw [lt_div_iff₀ hp] at hz2
        have : 2 ^ L / 4 * z = (z * 2 ^ L) / 4 := by ring
        rw [this]; linarith
      rw [mapPi0_coe_of_mem ⟨by linarith, by linarith⟩, piFun_of_mem2 hv1 hv2]
      apply inv_apply_eq_of
      rw [hj1, Equiv.swap_apply_right]
      simp only [Nat.cast_one, Nat.cast_zero]
      have hw1 : 0 ≤ z + (0 - 1) / 2 ^ L := by
        have : z + (0 - 1) / 2 ^ L = z - 1 / 2 ^ L := by ring
        rw [this]; linarith
      have hw2 : z + (0 - 1) / 2 ^ L ≤ 1 / 2 ^ L := by
        have : z + (0 - 1) / 2 ^ L = z - 1 / 2 ^ L := by ring
        have e : (2 : ℝ) / 2 ^ L = 1 / 2 ^ L + 1 / 2 ^ L := by ring
        rw [this]; linarith
      rw [toCircle_coe t ⟨hw1, by linarith⟩, hf0 _ ⟨hw1, hw2⟩]
      congr 1; field_simp; ring
  · -- later pieces are fixed
    have hne0 : j ≠ ⟨0, by positivity⟩ := fun h => by rw [h] at hj; simp at hj
    have hne1 : j ≠ ⟨1, Nat.one_lt_two_pow (by omega)⟩ := fun h => by rw [h] at hj; simp at hj
    rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1, sub_self, zero_div, add_zero]
    have hz2' : 2 / 2 ^ L ≤ z := by
      refine le_trans ?_ hz1
      rw [div_le_div_iff_of_pos_right hp]; exact_mod_cast hj
    have h34 := hge z hz2'
    have hlt := extend_lt_one t hz01
    rw [mapPi0_coe_of_mem ⟨by linarith, hlt⟩, piFun_of_mem3 h34, ← toCircle_coe t hz01]
    simp

theorem RS_eq_top (L : ℕ) (hL : 2 ≤ L) : RS L = ⊤ := by
  have hN : 2 ≤ 2 ^ L := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI : NeZero (2 ^ L) := ⟨by positivity⟩
  have hrot : finRotate (2 ^ L) ∈ RS L := ⟨rot L, rot_mem_G L, rot_realizes L (by omega)⟩
  have h01 : finRotate (2 ^ L) ⟨0, by positivity⟩ = ⟨1, Nat.one_lt_two_pow (by omega)⟩ := by
    rw [finRotate_apply]; ext
    rw [Fin.val_add, Fin.val_one', Nat.one_mod_eq_one.2 (by omega)]
    simp only [zero_add]; exact Nat.mod_eq_of_lt (by omega)
  have htop := Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate_of_le hN)
    (support_finRotate_of_le hN) ⟨0, by positivity⟩
  rw [h01] at htop
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro τ (rfl | rfl)
  · exact hrot
  · exact swap_mem_RS L hL

end CannonFloydParry.S6

/-! Disjoint standard dyadic intervals covering `[0,1)`, sorted, form a standard dyadic partition. -/

namespace CannonFloydParry.S6

lemma sdi_bounds {x y : ℝ} (h : IsStandardDyadicInterval x y) : 0 ≤ x ∧ x < y ∧ y ≤ 1 := by
  obtain ⟨a, n, ha, rfl, rfl⟩ := h
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  refine ⟨by positivity, by rw [div_lt_div_iff_of_pos_right hp]; linarith, ?_⟩
  rw [div_le_one hp]; exact_mod_cast ha

theorem sort_partition {N : ℕ} (a ℓ : Fin N → ℝ)
    (hstd : ∀ j, IsStandardDyadicInterval (a j) (a j + ℓ j))
    (hdisj : ∀ j j' w, w ∈ Set.Ico (a j) (a j + ℓ j) → w ∈ Set.Ico (a j') (a j' + ℓ j') → j = j')
    (hcov : ∀ w ∈ Set.Ico (0 : ℝ) 1, ∃ j, w ∈ Set.Ico (a j) (a j + ℓ j)) :
    ∃ (y : Fin (N + 1) → ℝ) (σ : Equiv.Perm (Fin N)), IsStandardDyadicPartition (List.ofFn y) ∧
      ∀ j, y (σ j).castSucc = a j ∧ y (σ j).succ = a j + ℓ j := by
  have hb := fun j => sdi_bounds (hstd j)
  have hmem : ∀ j, a j ∈ Set.Ico (a j) (a j + ℓ j) := fun j => ⟨le_rfl, (hb j).2.1⟩
  have hinj : Function.Injective a := fun j j' h => hdisj j j' (a j) (hmem j) (h ▸ hmem j')
  set s := Finset.univ.image a
  have hcard : s.card = N := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  set e := s.orderIsoOfFin hcard
  have he_mem : ∀ j, a j ∈ s := fun j => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have he_surj : ∀ w ∈ s, ∃ r, (e r : ℝ) = w := fun w hw => ⟨e.symm ⟨w, hw⟩, by simp⟩
  have he_in : ∀ r, ∃ j, (e r : ℝ) = a j := fun r => by
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 (e r).2; exact ⟨j, hj.symm⟩
  let σf : Fin N → Fin N := fun j => e.symm ⟨a j, he_mem j⟩
  have hσf : ∀ j, (e (σf j) : ℝ) = a j := fun j => by simp [σf]
  have σinj : Function.Injective σf := fun j j' h => hinj (by rw [← hσf, h, hσf])
  let σ : Equiv.Perm (Fin N) := Equiv.ofBijective σf (Finite.injective_iff_bijective.1 σinj)
  let y : Fin (N + 1) → ℝ := fun r => if h : (r : ℕ) < N then (e ⟨r, h⟩ : ℝ) else 1
  have hy_lt : ∀ r : Fin N, y r.castSucc = e r := fun r => by simp [y]
  have hy_last : y (Fin.last N) = 1 := by simp [y]
  have emono : StrictMono (fun r => (e r : ℝ)) := fun r r' h => by
    simpa using e.strictMono h
  -- the successor of `a j` among the left endpoints is `a j + ℓ j`
  have succ : ∀ j, y (σ j).succ = a j + ℓ j := by
    intro j
    set r := σ j
    have hr : (e r : ℝ) = a j := hσf j
    by_cases hb1 : a j + ℓ j = 1
    · -- `r` is the last index
      have hlast : (r : ℕ) + 1 = N := by
        by_contra hne
        have hlt : (r : ℕ) + 1 < N := by omega
        obtain ⟨j'', hj''⟩ := he_in ⟨r + 1, hlt⟩
        have hgt : a j < a j'' := by
          rw [← hr, ← hj'']; exact emono (show r < ⟨r + 1, hlt⟩ from Fin.lt_def.2 (Nat.lt_succ_self _))
        have : j'' = j := hdisj j'' j (a j'') (hmem j'') ⟨hgt.le, by
          have := hb j''; linarith [(hb j'').2.1]⟩
        rw [this] at hgt; exact lt_irrefl _ hgt
      have : y r.succ = 1 := by
        rw [show r.succ = Fin.last N from Fin.ext (by rw [Fin.val_succ, Fin.val_last]; omega)]
        exact hy_last
      rw [this, hb1]
    · have hb1' : a j + ℓ j < 1 := lt_of_le_of_ne (hb j).2.2 hb1
      obtain ⟨j', hj'⟩ := hcov (a j + ℓ j) ⟨by linarith [(hb j).1, (hb j).2.1], hb1'⟩
      have hj'ne : j' ≠ j := fun h => by rw [h] at hj'; exact lt_irrefl _ hj'.2
      -- `a j' = a j + ℓ j`
      have haj' : a j' = a j + ℓ j := by
        rcases lt_trichotomy (a j') (a j + ℓ j) with h | h | h
        · exfalso
          rcases le_or_gt (a j) (a j') with h2 | h2
          · exact hj'ne (hdisj j' j (a j') (hmem j') ⟨h2, h⟩)
          · exact hj'ne (hdisj j' j (a j) ⟨h2.le, by linarith [hj'.2, (hb j).2.1]⟩ (hmem j))
        · exact h
        · exact absurd hj'.1 (not_le.2 h)
      obtain ⟨t, ht⟩ := he_surj (a j + ℓ j) (haj' ▸ he_mem j')
      have hrt : r < t := by
        by_contra h
        have h' : (e t : ℝ) ≤ e r := emono.monotone (not_lt.1 h)
        rw [ht, hr] at h'; linarith [(hb j).2.1]
      have hnext : (t : ℕ) = r + 1 := by
        by_contra hne
        have hlt : (r : ℕ) + 1 < t := by omega
        have hlt' : (r : ℕ) + 1 < N := lt_trans hlt t.2
        obtain ⟨j'', hj''⟩ := he_in ⟨r + 1, hlt'⟩
        have h1 : a j < a j'' := by
          rw [← hr, ← hj'']; exact emono (show r < ⟨r + 1, hlt'⟩ from Fin.lt_def.2 (Nat.lt_succ_self _))
        have h2 : a j'' < a j + ℓ j := by
          rw [← ht, ← hj'']; exact emono (show (⟨r + 1, hlt'⟩ : Fin N) < t from Fin.lt_def.2 hlt)
        have := hdisj j'' j (a j'') (hmem j'') ⟨h1.le, h2⟩
        rw [this] at h1; exact lt_irrefl _ h1
      have : r.succ = t.castSucc := Fin.ext (by rw [Fin.val_succ, Fin.coe_castSucc, hnext])
      rw [this, hy_lt, ht]
  refine ⟨y, σ, ⟨?_, ?_, ?_⟩, fun j => ⟨by rw [hy_lt]; exact hσf j, succ j⟩⟩
  · -- the first breakpoint is `0`
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exfalso; obtain ⟨j, -⟩ := hcov 0 ⟨le_rfl, one_pos⟩; exact j.elim0
    obtain ⟨j0, hj0⟩ := hcov 0 ⟨le_rfl, one_pos⟩
    have ha0 : a j0 = 0 := le_antisymm hj0.1 (hb j0).1
    have hy0 : y 0 = e ⟨0, hN⟩ := by simp [y, hN]
    rw [List.ofFn_succ, List.head?_cons, hy0]
    congr 1
    apply le_antisymm
    · rw [← ha0, ← hσf j0]; exact emono.monotone (Fin.le_def.2 (Nat.zero_le _))
    · obtain ⟨j1, hj1⟩ := he_in ⟨0, hN⟩; rw [hj1]; exact (hb j1).1
  · rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_append]; simp [hy_last]
  · rw [List.isChain_ofFn]
    intro i hi
    have hiN : i < N := by omega
    obtain ⟨j, hj⟩ : ∃ j, σ j = ⟨i, hiN⟩ := σ.surjective _
    have h1 := hy_lt (σ j)
    have h2 := succ j
    rw [hj] at h1 h2
    have ea : (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin (N + 1)) = (⟨i, hiN⟩ : Fin N).castSucc := rfl
    have eb : (⟨i + 1, hi⟩ : Fin (N + 1)) = (⟨i, hiN⟩ : Fin N).succ := rfl
    have h3 : (e ⟨i, hiN⟩ : ℝ) = a j := by rw [← hj]; exact hσf j
    rw [ea, eb, h1, h2, h3]
    exact hstd j

end CannonFloydParry.S6

/-! Tree diagrams for maps satisfying `IsThompsonV` (CFP p. 240). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

lemma coe_inj_Ico {z z' : ℝ} (hz : z ∈ Set.Ico (0 : ℝ) 1) (hz' : z' ∈ Set.Ico (0 : ℝ) 1)
    (h : (z : UnitAddCircle) = z') : z = z' := by
  have := congrArg ico h
  rw [ico_coe, ico_coe, Int.fract_eq_self.2 hz, Int.fract_eq_self.2 hz'] at this
  exact this

lemma uniform_partition (M : ℕ) :
    IsStandardDyadicPartition (List.ofFn (fun i : Fin (2 ^ M + 1) => ((i : ℕ) : ℝ) / 2 ^ M)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.ofFn_succ, List.head?_cons]; simp
  · rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_append]; simp
  · rw [List.isChain_ofFn]
    intro i hi
    exact ⟨i, M, by omega, rfl, by push_cast; ring⟩

lemma floor_piece {M : ℕ} {z : ℝ} (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    ∃ j : ℕ, j < 2 ^ M ∧ z ∈ Set.Ico ((j : ℝ) / 2 ^ M) ((j + 1) / 2 ^ M) := by
  have hp : (0 : ℝ) < 2 ^ M := by positivity
  set j := ⌊z * 2 ^ M⌋.toNat
  have h0 : (0 : ℤ) ≤ ⌊z * 2 ^ M⌋ := Int.floor_nonneg.2 (by nlinarith [hz.1])
  have hjz : (j : ℤ) = ⌊z * 2 ^ M⌋ := Int.toNat_of_nonneg h0
  have hj : (j : ℝ) = ⌊z * 2 ^ M⌋ := by exact_mod_cast hjz
  refine ⟨j, ?_, ?_, ?_⟩
  · have : z * 2 ^ M < 2 ^ M := by nlinarith [hz.2]
    have h1 : ⌊z * 2 ^ M⌋ < (2 : ℤ) ^ M := by
      rw [Int.floor_lt]; push_cast; exact this
    have : (j : ℤ) < 2 ^ M := by rw [Int.toNat_of_nonneg h0]; exact h1
    exact_mod_cast this
  · rw [div_le_iff₀ hp, hj]; exact Int.floor_le _
  · rw [lt_div_iff₀ hp, hj]; exact Int.lt_floor_add_one _

/-- Tree diagram with the uniform domain partition of level `M ≥ 2`. -/
theorem treeV_unif {f : Equiv.Perm UnitAddCircle} (hf : IsThompsonV f) :
    ∃ M : ℕ, 2 ≤ M ∧ ∃ (y : Fin (2 ^ M + 1) → ℝ) (σ : Equiv.Perm (Fin (2 ^ M))),
      IsStandardDyadicPartition (List.ofFn y) ∧
      ∀ i : Fin (2 ^ M), ∃ k : ℤ,
        y (σ i).succ - y (σ i).castSucc = 2 ^ k * (((i.succ : ℕ) : ℝ) / 2 ^ M - ((i.castSucc : ℕ) : ℝ) / 2 ^ M) ∧
        ∀ z ∈ Set.Ico (((i.castSucc : ℕ) : ℝ) / 2 ^ M) (((i.succ : ℕ) : ℝ) / 2 ^ M),
          f (z : UnitAddCircle) =
            ((y (σ i).castSucc + 2 ^ k * (z - ((i.castSucc : ℕ) : ℝ) / 2 ^ M) : ℝ) : UnitAddCircle) := by
  obtain ⟨M, hM2, hM⟩ := uniform_std hf
  have h1 : ∀ j : Fin (2 ^ M), ∃ (k : ℤ) (m A : ℕ), A + 1 ≤ 2 ^ m ∧ (2 : ℝ) ^ k * 2 ^ m = 2 ^ M ∧
      ∀ z ∈ Set.Ico ((j : ℝ) / 2 ^ M) ((j + 1) / 2 ^ M),
        f (z : UnitAddCircle) = (((A : ℝ) / 2 ^ m + 2 ^ k * (z - j / 2 ^ M) : ℝ) : UnitAddCircle) :=
    fun j => hM j j.2
  choose K m A hA hpow hK using h1
  have hp : (0 : ℝ) < 2 ^ M := by positivity
  set a : Fin (2 ^ M) → ℝ := fun j => (A j : ℝ) / 2 ^ m j
  set ℓ : Fin (2 ^ M) → ℝ := fun j => 1 / 2 ^ m j
  have hℓ : ∀ j, ℓ j = 2 ^ K j * (1 / 2 ^ M) := by
    intro j
    have := hpow j
    have hm : (0 : ℝ) < 2 ^ m j := by positivity
    simp only [ℓ]; field_simp; linarith
  have hkpos : ∀ j, (0 : ℝ) < 2 ^ K j := fun j => zpow_pos two_pos _
  have hstd : ∀ j, IsStandardDyadicInterval (a j) (a j + ℓ j) := fun j =>
    ⟨A j, m j, hA j, rfl, by simp only [a, ℓ]; ring⟩
  have hbd := fun j => sdi_bounds (hstd j)
  -- preimage of a point of `J_j` in `I_j`
  have pre : ∀ j w, w ∈ Set.Ico (a j) (a j + ℓ j) →
      ∃ z ∈ Set.Ico ((j : ℝ) / 2 ^ M) ((j + 1) / 2 ^ M), f (z : UnitAddCircle) = (w : UnitAddCircle) := by
    intro j w hw
    refine ⟨(j : ℝ) / 2 ^ M + (w - a j) / 2 ^ K j, ⟨?_, ?_⟩, ?_⟩
    · have : 0 ≤ (w - a j) / 2 ^ K j := div_nonneg (by linarith [hw.1]) (hkpos j).le
      linarith
    · have h2 : (w - a j) / 2 ^ K j < 1 / 2 ^ M := by
        rw [div_lt_iff₀ (hkpos j)]; have := hw.2; rw [hℓ j] at this; linarith
      have : ((j : ℝ) + 1) / 2 ^ M = j / 2 ^ M + 1 / 2 ^ M := by ring
      linarith
    · rw [hK j _ ⟨by
          have : 0 ≤ (w - a j) / 2 ^ K j := div_nonneg (by linarith [hw.1]) (hkpos j).le
          linarith, by
          have h2 : (w - a j) / 2 ^ K j < 1 / 2 ^ M := by
            rw [div_lt_iff₀ (hkpos j)]; have := hw.2; rw [hℓ j] at this; linarith
          have : ((j : ℝ) + 1) / 2 ^ M = j / 2 ^ M + 1 / 2 ^ M := by ring
          linarith⟩]
      congr 1
      have := (hkpos j).ne'
      simp only [a]
      field_simp
      ring
  have hI : ∀ (j : Fin (2 ^ M)) z, z ∈ Set.Ico ((j : ℝ) / 2 ^ M) ((j + 1) / 2 ^ M) →
      z ∈ Set.Ico (0 : ℝ) 1 := by
    intro j z hz
    constructor
    · exact le_trans (by positivity) hz.1
    · refine lt_of_lt_of_le hz.2 ?_
      rw [div_le_one hp]
      have : (j : ℕ) + 1 ≤ 2 ^ M := j.2
      exact_mod_cast this
  have hdisj : ∀ j j' w, w ∈ Set.Ico (a j) (a j + ℓ j) → w ∈ Set.Ico (a j') (a j' + ℓ j') → j = j' := by
    intro j j' w hw hw'
    obtain ⟨z, hz, hfz⟩ := pre j w hw
    obtain ⟨z', hz', hfz'⟩ := pre j' w hw'
    have hzz : z = z' := coe_inj_Ico (hI j z hz) (hI j' z' hz') (f.injective (hfz.trans hfz'.symm))
    subst hzz
    have e1 : ⌊z * 2 ^ M⌋ = (j : ℤ) := by
      rw [Int.floor_eq_iff]; constructor
      · have := hz.1; rw [div_le_iff₀ hp] at this; exact_mod_cast this
      · have := hz.2; rw [lt_div_iff₀ hp] at this; push_cast; linarith
    have e2 : ⌊z * 2 ^ M⌋ = (j' : ℤ) := by
      rw [Int.floor_eq_iff]; constructor
      · have := hz'.1; rw [div_le_iff₀ hp] at this; exact_mod_cast this
      · have := hz'.2; rw [lt_div_iff₀ hp] at this; push_cast; linarith
    exact Fin.ext (by exact_mod_cast e1.symm.trans e2)
  have hcov : ∀ w ∈ Set.Ico (0 : ℝ) 1, ∃ j, w ∈ Set.Ico (a j) (a j + ℓ j) := by
    intro w hw
    set z0 := ico (f⁻¹ (w : UnitAddCircle))
    have hz0 : z0 ∈ Set.Ico (0 : ℝ) 1 := ⟨ico_nonneg _, ico_lt_one _⟩
    have hz0c : ((z0 : ℝ) : UnitAddCircle) = f⁻¹ (w : UnitAddCircle) := by
      apply circ_ext; rw [ico_coe, Int.fract_eq_self.2 hz0]
    obtain ⟨j, hj, hzj⟩ := floor_piece (M := M) hz0
    set jf : Fin (2 ^ M) := ⟨j, hj⟩
    have hf0 := hK jf z0 hzj
    rw [hz0c, show f (f⁻¹ (w : UnitAddCircle)) = (w : UnitAddCircle) by simp] at hf0
    set v := a jf + 2 ^ K jf * (z0 - j / 2 ^ M)
    have hv : v ∈ Set.Ico (a jf) (a jf + ℓ jf) := by
      constructor
      · have : 0 ≤ 2 ^ K jf * (z0 - j / 2 ^ M) := mul_nonneg (hkpos jf).le (by linarith [hzj.1])
        simp only [v]; linarith
      · rw [hℓ jf]; simp only [v]
        have : z0 - j / 2 ^ M < 1 / 2 ^ M := by
          have := hzj.2; have e : ((j : ℝ) + 1) / 2 ^ M = j / 2 ^ M + 1 / 2 ^ M := by ring
          linarith
        have := mul_lt_mul_of_pos_left this (hkpos jf)
        linarith
    have hv01 : v ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨le_trans (hbd jf).1 hv.1, lt_of_lt_of_le hv.2 (hbd jf).2.2⟩
    have : w = v := coe_inj_Ico hw hv01 hf0
    exact ⟨jf, this ▸ hv⟩
  obtain ⟨y, σ, hy, hyσ⟩ := sort_partition a ℓ hstd hdisj hcov
  refine ⟨M, hM2, y, σ, hy, fun i => ⟨K i, ?_, ?_⟩⟩
  · rw [(hyσ i).1, (hyσ i).2, add_sub_cancel_left, hℓ i]
    simp only [Fin.val_succ, Fin.val_castSucc]; push_cast; ring
  · intro z hz
    rw [(hyσ i).1]
    simp only [Fin.val_succ, Fin.val_castSucc] at hz ⊢
    push_cast at hz
    exact hK i z hz

end CannonFloydParry.S6

/-! Generation, part 5: every map satisfying `IsThompsonV` lies in `⟨A, B, C, π₀⟩`, so
`A`, `B`, `C`, `π₀` generate `V` (Lemma 6.1). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

lemma realizes_unique {L : ℕ} {w w' : Equiv.Perm UnitAddCircle} {τ : Equiv.Perm (Fin (2 ^ L))}
    (h : Realizes L w τ) (h' : Realizes L w' τ) : w = w' := by
  ext p
  have hp : p = ((ico p : ℝ) : UnitAddCircle) :=
    circ_ext (by rw [ico_coe, Int.fract_eq_self.2 ⟨ico_nonneg p, ico_lt_one p⟩])
  obtain ⟨j, hj, hz⟩ := floor_piece (M := L) ⟨ico_nonneg p, ico_lt_one p⟩
  rw [hp, h ⟨j, hj⟩ _ hz, h' ⟨j, hj⟩ _ hz]

theorem isThompsonV_mem_G {f : Equiv.Perm UnitAddCircle} (hf : IsThompsonV f) : f ∈ G := by
  obtain ⟨M, hM2, y, σ, hy, hpc⟩ := treeV_unif hf
  obtain ⟨h, hF, haff, hmap⟩ := exists_F_affine hy (uniform_partition M) (by simp)
  have hval : ∀ r, extend h (y r) = ((r : ℕ) : ℝ) / 2 ^ M := by
    rw [List.map_ofFn] at hmap
    exact congrFun (List.ofFn_injective hmap)
  have hp : (0 : ℝ) < 2 ^ M := by positivity
  unfold AffineOnPieces at haff
  rw [List.isChain_ofFn] at haff
  have hchain := hy.2.2
  rw [List.isChain_ofFn] at hchain
  have hyb : ∀ r : Fin (2 ^ M), 0 ≤ y r.castSucc ∧ y r.castSucc < y r.succ ∧ y r.succ ≤ 1 :=
    fun r => sdi_bounds (hchain r (by omega))
  have hform : ∀ r : Fin (2 ^ M), ∀ w ∈ Set.Icc (y r.castSucc) (y r.succ),
      extend h w = ((r : ℕ) : ℝ) / 2 ^ M +
        ((((r : ℕ) + 1 : ℕ) : ℝ) / 2 ^ M - ((r : ℕ) : ℝ) / 2 ^ M) / (y r.succ - y r.castSucc) *
          (w - y r.castSucc) := by
    intro r w hw
    obtain ⟨a, c, hac⟩ := haff r (by omega)
    have := affine_of_endpoints (hyb r).2.1 hac (hval r.castSucc) (hval r.succ) w hw
    simpa [Fin.val_succ, Fin.val_castSucc] using this
  set g := toCircle h * f
  have hg : Realizes M g σ := by
    intro i z hz
    obtain ⟨k, hlen, hfz⟩ := hpc i
    simp only [Fin.val_succ, Fin.val_castSucc] at hlen hfz
    push_cast at hlen hfz
    have hkpos : (0 : ℝ) < 2 ^ k := zpow_pos two_pos _
    have hlen' : y (σ i).succ - y (σ i).castSucc = 2 ^ k / 2 ^ M := by
      rw [hlen]; field_simp; ring
    rw [Equiv.Perm.mul_apply, hfz z hz]
    have hd0 : 0 ≤ z - (i : ℝ) / 2 ^ M := by linarith [hz.1]
    have hd1 : z - (i : ℝ) / 2 ^ M < 1 / 2 ^ M := by
      have := hz.2; have e : ((i : ℝ) + 1) / 2 ^ M = i / 2 ^ M + 1 / 2 ^ M := by ring
      linarith
    set v := y (σ i).castSucc + 2 ^ k * (z - (i : ℝ) / 2 ^ M)
    have hv1 : y (σ i).castSucc ≤ v := by
      have := mul_nonneg hkpos.le hd0; simp only [v]; linarith
    have hv2 : v < y (σ i).succ := by
      have h2 := mul_lt_mul_of_pos_left hd1 hkpos
      have e : 2 ^ k * (1 / 2 ^ M) = (2 : ℝ) ^ k / 2 ^ M := by ring
      simp only [v]; linarith
    have hv01 : v ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨le_trans (hyb (σ i)).1 hv1, lt_of_lt_of_le hv2 (hyb (σ i)).2.2⟩
    rw [toCircle_coe h hv01, hform (σ i) v ⟨hv1, hv2.le⟩, hlen']
    congr 1
    simp only [v]
    push_cast
    field_simp
    ring
  have hσ : σ ∈ RS M := by rw [RS_eq_top M hM2]; trivial
  obtain ⟨w, hwG, hw⟩ := hσ
  have hgw : g = w := realizes_unique hg hw
  have hfg : f = (toCircle h)⁻¹ * g := by simp only [g]; group
  rw [hfg, hgw]
  exact mul_mem (inv_mem (toCircle_mem_G hF)) hwG

/-- Lemma 6.1, the generation half: `A`, `B`, `C`, `π₀` generate `V`. -/
theorem closure_range_symV_eq_V : Subgroup.closure (Set.range symV) = V := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨s, rfl⟩
    have hT : ∀ s', symT s' ∈ T := fun s' => by
      rw [← closure_range_symT_eq_T_and_relations.1]; exact Subgroup.subset_closure ⟨s', rfl⟩
    cases s
    · exact T_le_V_and_mapPi0_mem_V'.1 (hT FormalABC.A)
    · exact T_le_V_and_mapPi0_mem_V'.1 (hT FormalABC.B)
    · exact T_le_V_and_mapPi0_mem_V'.1 (hT FormalABC.C)
    · exact T_le_V_and_mapPi0_mem_V'.2
  · rw [V, Subgroup.closure_le]
    intro f hf
    exact isThompsonV_mem_G hf

end CannonFloydParry.S6

/-! Lemma 6.1, relations 1)–14). Relations 1)–6) are those of `T` (Lemma 5.2, published). For
7)–14), `π₁` is evaluated once on `[0,1)` representatives (`ico_piV_one`), and each relation is
then an identity between short compositions of explicit piecewise-affine real functions, checked
piece by piece (generated by gen_rel_short.py). -/

namespace CannonFloydParry.S6

open CannonFloydParry.S5

local notation "a" => symV FormalV.A
local notation "b" => symV FormalV.B
local notation "c" => symV FormalV.C
local notation "p" => symV FormalV.P

lemma lift_of (s : FormalV) : FreeGroup.lift symV (FreeGroup.of s) = symV s :=
  FreeGroup.lift_apply_of

lemma XV_two : XV 2 = a⁻¹ * b * a := by
  simp [XV, wordX, lift_of]
lemma XV_three : XV 3 = a⁻¹ ^ 2 * b * a ^ 2 := by
  simp [XV, wordX, lift_of, inv_pow]
lemma CV_one : CV 1 = c := by simp [CV, wordC, lift_of]
lemma CV_two : CV 2 = a⁻¹ * c * b := by simp [CV, wordC, lift_of]
lemma CV_three : CV 3 = a⁻¹ ^ 2 * c * b ^ 2 := by simp [CV, wordC, lift_of, inv_pow]
lemma piV_one : piV 1 = b⁻¹ * c⁻¹ * a * p * a⁻¹ * c * b := by
  simp [piV, wordPi, wordC, lift_of]; group
lemma piV_two' : piV 2 = a⁻¹ * piV 1 * a := by
  simp [piV, wordPi, lift_of]
lemma piV_three' : piV 3 = a⁻¹ ^ 2 * piV 1 * a ^ 2 := by
  simp [piV, wordPi, lift_of]

/-- `π₁` on `[0,1)`: the identity off `[1/2, 7/8)`, swapping `[1/2,3/4)` and `[3/4,7/8)`. -/
noncomputable def p1Fun (y : ℝ) : ℝ :=
  if y < 1 / 2 then y else if y < 3 / 4 then y / 2 + 1 / 2 else if y < 7 / 8 then 2 * y - 1 else y

lemma p1Fun_of_mem1 {y : ℝ} (h1 : y < 1 / 2) : p1Fun y = y := by
  unfold p1Fun; rw [if_pos h1]
lemma p1Fun_of_mem2 {y : ℝ} (h0 : 1 / 2 ≤ y) (h1 : y < 3 / 4) : p1Fun y = y / 2 + 1 / 2 := by
  unfold p1Fun; rw [if_neg (by linarith), if_pos h1]
lemma p1Fun_of_mem3 {y : ℝ} (h0 : 3 / 4 ≤ y) (h1 : y < 7 / 8) : p1Fun y = 2 * y - 1 := by
  unfold p1Fun; rw [if_neg (by linarith), if_neg (by linarith), if_pos h1]
lemma p1Fun_of_mem4 {y : ℝ} (h0 : 7 / 8 ≤ y) : p1Fun y = y := by
  unfold p1Fun; rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]

lemma relV7 : piV 1 ^ 2 = 1 := by
  have hp : p * p = 1 := mapPi0_mul_self
  rw [piV_one, sq]
  calc _ = (b⁻¹ * c⁻¹ * a) * (p * p) * (b⁻¹ * c⁻¹ * a)⁻¹ := by group
    _ = 1 := by rw [hp]; group

lemma ico_piV_one (x : UnitAddCircle) : ico (piV 1 x) = p1Fun (ico x) := by
  simp only [piV_one, mul_inv_rev, inv_inv, Equiv.Perm.coe_mul, Function.comp_apply, ico_Av, ico_Bv, ico_Cv, ico_Avinv, ico_Bvinv, ico_Cvinv, ico_P, ico_Pinv]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 2 : ℝ) with hq0 | hp0
  · have eL0 : bFun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [h0, hq0]
    have eL1 : cFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL2 : aInv ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 4 : ℝ) * y + (7 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [h0, hq0]
    have eL3 : piFun ((1 / 4 : ℝ) * y + (7 / 8 : ℝ)) = (1 / 4 : ℝ) * y + (7 / 8 : ℝ) := by rw [piFun_of_mem3] <;> first | ring1 | linarith only [h0, hq0]
    have eL4 : aFun ((1 / 4 : ℝ) * y + (7 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [h0, hq0]
    have eL5 : cInv ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [cInv_of_mem3] <;> first | ring1 | linarith only [h0, hq0]
    have eL6 : bInv ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bInv_of_mem0] <;> first | ring1 | linarith only [h0, hq0]
    have eR0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eR0] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq1 | hp1
  · have eL0 : bFun (y) = (1 / 2 : ℝ) * y + (1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL1 : cFun ((1 / 2 : ℝ) * y + (1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 2 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL2 : aInv ((1 : ℝ) * y + (-1 / 2 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL3 : piFun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [piFun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL4 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL5 : cInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 8 : ℝ) := by rw [cInv_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL6 : bInv ((1 / 2 : ℝ) * y + (3 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bInv_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR0 : p1Fun (y) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eR0] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq2 | hp2
  · have eL0 : bFun (y) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL1 : cFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL2 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL3 : piFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [piFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL4 : aFun ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-3 / 2 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eL5 : cInv ((2 : ℝ) * y + (-3 / 2 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [cInv_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eL6 : bInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bInv_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eR0 : p1Fun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eR0] <;> ring1
  have eL0 : bFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp2, h1]
  have eL1 : cFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith only [hp2, h1]
  have eL2 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, h1]
  have eL3 : piFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [piFun_of_mem3] <;> first | ring1 | linarith only [hp2, h1]
  have eL4 : aFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, h1]
  have eL5 : cInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [cInv_of_mem2] <;> first | ring1 | linarith only [hp2, h1]
  have eL6 : bInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bInv_of_mem3] <;> first | ring1 | linarith only [hp2, h1]
  have eR0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp2, h1]
  rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eR0] <;> ring1

lemma relV8 : (piV 1) * (a⁻¹ * a⁻¹ * piV 1 * a * a) = (a⁻¹ * a⁻¹ * piV 1 * a * a) * (piV 1) := by
  apply perm_ext
  intro x
  simp only [mul_inv_rev, inv_inv, inv_pow, pow_succ, pow_zero, one_mul, mul_one, inv_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id, ico_Av, ico_Bv, ico_Cv, ico_Avinv, ico_Bvinv, ico_Cvinv, ico_P, ico_Pinv, ico_piV_one]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 2 : ℝ) with hq0 | hp0
  · have eL0 : aFun (y) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL1 : aFun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL2 : p1Fun ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL3 : aInv ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL4 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL5 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR2 : aFun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR3 : p1Fun ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR4 : aInv ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR5 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq1 | hp1
  · have eL0 : aFun (y) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL1 : aFun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (-1 / 8 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL2 : p1Fun ((1 / 2 : ℝ) * y + (-1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (-1 / 8 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL3 : aInv ((1 / 2 : ℝ) * y + (-1 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL4 : aInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL5 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR0 : p1Fun (y) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR1 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eR2 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR3 : p1Fun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eR4 : aInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR5 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq2 | hp2
  · have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eL1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL2 : p1Fun ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eL3 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL4 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eL5 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eR0 : p1Fun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eR1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR2 : aFun ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (1 : ℝ) * y + (-5 / 8 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eR3 : p1Fun ((1 : ℝ) * y + (-5 / 8 : ℝ)) = (1 : ℝ) * y + (-5 / 8 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eR4 : aInv ((1 : ℝ) * y + (-5 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eR5 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (15 / 16 : ℝ) with hq3 | hp3
  · have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL2 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eL3 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL4 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL5 : p1Fun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp2, hq3]
    have eR0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp2, hq3]
    have eR1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR2 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR3 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eR4 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR5 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (31 / 32 : ℝ) with hq4 | hp4
  · have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eL1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eL2 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (8 : ℝ) * y + (-7 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eL3 : aInv ((8 : ℝ) * y + (-7 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eL4 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eL5 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, hq4]
    have eR0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, hq4]
    have eR1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR2 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR3 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (8 : ℝ) * y + (-7 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR4 : aInv ((8 : ℝ) * y + (-7 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR5 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eL1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eL2 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp4, h1]
  have eL3 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eL4 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eL5 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp4, h1]
  have eR0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp4, h1]
  have eR1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR2 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR3 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp4, h1]
  have eR4 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR5 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1

lemma relV9 : ((a⁻¹ * piV 1 * a) * (piV 1)) * ((a⁻¹ * piV 1 * a) * (piV 1)) * ((a⁻¹ * piV 1 * a) * (piV 1)) = 1 := by
  apply perm_ext
  intro x
  simp only [mul_inv_rev, inv_inv, inv_pow, pow_succ, pow_zero, one_mul, mul_one, inv_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id, ico_Av, ico_Bv, ico_Cv, ico_Avinv, ico_Bvinv, ico_Cvinv, ico_P, ico_Pinv, ico_piV_one]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 2 : ℝ) with hq0 | hp0
  · have eL0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL2 : p1Fun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL3 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL4 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL5 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL6 : p1Fun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL7 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL8 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL9 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL10 : p1Fun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL11 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq1 | hp1
  · have eL0 : p1Fun (y) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL1 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eL2 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL3 : aInv ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 / 4 : ℝ) * y + (3 / 4 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eL4 : p1Fun ((1 / 4 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 4 : ℝ) * y + (3 / 4 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp0, hq1]
    have eL5 : aFun ((1 / 4 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eL6 : p1Fun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eL7 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eL8 : p1Fun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eL9 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL10 : p1Fun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL11 : aInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq2 | hp2
  · have eL0 : p1Fun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eL1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL2 : p1Fun ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eL3 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL4 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL5 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eL6 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL7 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eL8 : p1Fun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp1, hq2]
    have eL9 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eL10 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eL11 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11] <;> ring1
  rcases lt_or_ge y (15 / 16 : ℝ) with hq3 | hp3
  · have eL0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp2, hq3]
    have eL1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL2 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL3 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL4 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL5 : aFun ((4 : ℝ) * y + (-3 : ℝ)) = (4 : ℝ) * y + (-13 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eL6 : p1Fun ((4 : ℝ) * y + (-13 / 4 : ℝ)) = (4 : ℝ) * y + (-13 / 4 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp2, hq3]
    have eL7 : aInv ((4 : ℝ) * y + (-13 / 4 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eL8 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eL9 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL10 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eL11 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11] <;> ring1
  have eL0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, h1]
  have eL1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eL2 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, h1]
  have eL3 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eL4 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, h1]
  have eL5 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eL6 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, h1]
  have eL7 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eL8 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, h1]
  have eL9 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eL10 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, h1]
  have eL11 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11] <;> ring1

lemma relV10 : (a⁻¹ * a⁻¹ * b * a * a) * (piV 1) = (piV 1) * (a⁻¹ * a⁻¹ * b * a * a) := by
  apply perm_ext
  intro x
  simp only [mul_inv_rev, inv_inv, inv_pow, pow_succ, pow_zero, one_mul, mul_one, inv_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id, ico_Av, ico_Bv, ico_Cv, ico_Avinv, ico_Bvinv, ico_Cvinv, ico_P, ico_Pinv, ico_piV_one]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 2 : ℝ) with hq0 | hp0
  · have eL0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL2 : aFun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL3 : bFun ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [h0, hq0]
    have eL4 : aInv ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL5 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR0 : aFun (y) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR1 : aFun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR2 : bFun ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [h0, hq0]
    have eR3 : aInv ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR4 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR5 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq1 | hp1
  · have eL0 : p1Fun (y) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL1 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eL2 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL3 : bFun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [hp0, hq1]
    have eL4 : aInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL5 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eR0 : aFun (y) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR1 : aFun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (-1 / 8 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eR2 : bFun ((1 / 2 : ℝ) * y + (-1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [hp0, hq1]
    have eR3 : aInv ((1 / 2 : ℝ) * y + (-1 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eR4 : aInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR5 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq2 | hp2
  · have eL0 : p1Fun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eL1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL2 : aFun ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (1 : ℝ) * y + (-5 / 8 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eL3 : bFun ((1 : ℝ) * y + (-5 / 8 : ℝ)) = (1 : ℝ) * y + (-5 / 8 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [hp1, hq2]
    have eL4 : aInv ((1 : ℝ) * y + (-5 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eL5 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eR1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR2 : bFun ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [hp1, hq2]
    have eR3 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR4 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eR5 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (15 / 16 : ℝ) with hq3 | hp3
  · have eL0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp2, hq3]
    have eL1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL2 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL3 : bFun ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp2, hq3]
    have eL4 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL5 : aInv ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (7 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR2 : bFun ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp2, hq3]
    have eR3 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR4 : aInv ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (7 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR5 : p1Fun ((1 / 2 : ℝ) * y + (7 / 16 : ℝ)) = (1 / 2 : ℝ) * y + (7 / 16 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp2, hq3]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (31 / 32 : ℝ) with hq4 | hp4
  · have eL0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, hq4]
    have eL1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eL2 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eL3 : bFun ((4 : ℝ) * y + (-3 : ℝ)) = (4 : ℝ) * y + (-25 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp3, hq4]
    have eL4 : aInv ((4 : ℝ) * y + (-25 / 8 : ℝ)) = (2 : ℝ) * y + (-17 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eL5 : aInv ((2 : ℝ) * y + (-17 / 16 : ℝ)) = (1 : ℝ) * y + (-1 / 32 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR2 : bFun ((4 : ℝ) * y + (-3 : ℝ)) = (4 : ℝ) * y + (-25 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp3, hq4]
    have eR3 : aInv ((4 : ℝ) * y + (-25 / 8 : ℝ)) = (2 : ℝ) * y + (-17 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR4 : aInv ((2 : ℝ) * y + (-17 / 16 : ℝ)) = (1 : ℝ) * y + (-1 / 32 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR5 : p1Fun ((1 : ℝ) * y + (-1 / 32 : ℝ)) = (1 : ℝ) * y + (-1 / 32 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, hq4]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  have eL0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp4, h1]
  have eL1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eL2 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eL3 : bFun ((4 : ℝ) * y + (-3 : ℝ)) = (8 : ℝ) * y + (-7 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eL4 : aInv ((8 : ℝ) * y + (-7 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eL5 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR2 : bFun ((4 : ℝ) * y + (-3 : ℝ)) = (8 : ℝ) * y + (-7 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR3 : aInv ((8 : ℝ) * y + (-7 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR4 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR5 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp4, h1]
  rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1

lemma relV11 : (piV 1) * (a⁻¹ * b * a) = b * (a⁻¹ * piV 1 * a) * (piV 1) := by
  apply perm_ext
  intro x
  simp only [mul_inv_rev, inv_inv, inv_pow, pow_succ, pow_zero, one_mul, mul_one, inv_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id, ico_Av, ico_Bv, ico_Cv, ico_Avinv, ico_Bvinv, ico_Cvinv, ico_P, ico_Pinv, ico_piV_one]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 2 : ℝ) with hq0 | hp0
  · have eL0 : aFun (y) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL1 : bFun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [h0, hq0]
    have eL2 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL3 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR2 : p1Fun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR3 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR4 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [h0, hq0]
    rw [eL0, eL1, eL2, eL3, eR0, eR1, eR2, eR3, eR4] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq1 | hp1
  · have eL0 : aFun (y) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL1 : bFun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [hp0, hq1]
    have eL2 : aInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL3 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR0 : p1Fun (y) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR1 : aFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eR2 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR3 : aInv ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 / 4 : ℝ) * y + (3 / 4 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eR4 : bFun ((1 / 4 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    rw [eL0, eL1, eL2, eL3, eR0, eR1, eR2, eR3, eR4] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq2 | hp2
  · have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eL1 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eL2 : aInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eL3 : p1Fun ((1 / 2 : ℝ) * y + (3 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eR0 : p1Fun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eR1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR2 : p1Fun ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eR3 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR4 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    rw [eL0, eL1, eL2, eL3, eR0, eR1, eR2, eR3, eR4] <;> ring1
  rcases lt_or_ge y (15 / 16 : ℝ) with hq3 | hp3
  · have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL1 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eL2 : aInv ((2 : ℝ) * y + (-9 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL3 : p1Fun ((1 : ℝ) * y + (-1 / 16 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp2, hq3]
    have eR1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR2 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR3 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR4 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    rw [eL0, eL1, eL2, eL3, eR0, eR1, eR2, eR3, eR4] <;> ring1
  have eL0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eL1 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eL2 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eL3 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, h1]
  have eR0 : p1Fun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, h1]
  have eR1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eR2 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, h1]
  have eR3 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eR4 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  rw [eL0, eL1, eL2, eL3, eR0, eR1, eR2, eR3, eR4] <;> ring1

lemma relV12 : (a⁻¹ * piV 1 * a) * b = b * (a⁻¹ * a⁻¹ * piV 1 * a * a) := by
  apply perm_ext
  intro x
  simp only [mul_inv_rev, inv_inv, inv_pow, pow_succ, pow_zero, one_mul, mul_one, inv_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id, ico_Av, ico_Bv, ico_Cv, ico_Avinv, ico_Bvinv, ico_Cvinv, ico_P, ico_Pinv, ico_piV_one]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 2 : ℝ) with hq0 | hp0
  · have eL0 : bFun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [h0, hq0]
    have eL1 : aFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL2 : p1Fun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL3 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR0 : aFun (y) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR1 : aFun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR2 : p1Fun ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 4 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR3 : aInv ((1 / 4 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR4 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR5 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [h0, hq0]
    rw [eL0, eL1, eL2, eL3, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq1 | hp1
  · have eL0 : bFun (y) = (1 / 2 : ℝ) * y + (1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL1 : aFun ((1 / 2 : ℝ) * y + (1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL2 : p1Fun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL3 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 4 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR0 : aFun (y) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR1 : aFun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (-1 / 8 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eR2 : p1Fun ((1 / 2 : ℝ) * y + (-1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (-1 / 8 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eR3 : aInv ((1 / 2 : ℝ) * y + (-1 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eR4 : aInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR5 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    rw [eL0, eL1, eL2, eL3, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq2 | hp2
  · have eL0 : bFun (y) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL1 : aFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (1 : ℝ) * y + (-3 / 8 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL2 : p1Fun ((1 : ℝ) * y + (-3 / 8 : ℝ)) = (1 : ℝ) * y + (-3 / 8 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eL3 : aInv ((1 : ℝ) * y + (-3 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eR1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR2 : p1Fun ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eR3 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR4 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eR5 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    rw [eL0, eL1, eL2, eL3, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (15 / 16 : ℝ) with hq3 | hp3
  · have eL0 : bFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL2 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eL3 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR2 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eR3 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR4 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR5 : bFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    rw [eL0, eL1, eL2, eL3, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  rcases lt_or_ge y (31 / 32 : ℝ) with hq4 | hp4
  · have eL0 : bFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eL1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eL2 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (8 : ℝ) * y + (-7 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eL3 : aInv ((8 : ℝ) * y + (-7 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR2 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (8 : ℝ) * y + (-7 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR3 : aInv ((8 : ℝ) * y + (-7 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR4 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    have eR5 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp3, hq4]
    rw [eL0, eL1, eL2, eL3, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1
  have eL0 : bFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eL1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eL2 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp4, h1]
  have eL3 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR1 : aFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR2 : p1Fun ((4 : ℝ) * y + (-3 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp4, h1]
  have eR3 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR4 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  have eR5 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp4, h1]
  rw [eL0, eL1, eL2, eL3, eR0, eR1, eR2, eR3, eR4, eR5] <;> ring1

lemma relV13 : (piV 1) * (a⁻¹ * a⁻¹ * c * b * b) = (a⁻¹ * a⁻¹ * c * b * b) * (a⁻¹ * piV 1 * a) := by
  apply perm_ext
  intro x
  simp only [mul_inv_rev, inv_inv, inv_pow, pow_succ, pow_zero, one_mul, mul_one, inv_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id, ico_Av, ico_Bv, ico_Cv, ico_Avinv, ico_Bvinv, ico_Cvinv, ico_P, ico_Pinv, ico_piV_one]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 2 : ℝ) with hq0 | hp0
  · have eL0 : bFun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [h0, hq0]
    have eL1 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [h0, hq0]
    have eL2 : cFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL3 : aInv ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 4 : ℝ) * y + (7 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [h0, hq0]
    have eL4 : aInv ((1 / 4 : ℝ) * y + (7 / 8 : ℝ)) = (1 / 8 : ℝ) * y + (15 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [h0, hq0]
    have eL5 : p1Fun ((1 / 8 : ℝ) * y + (15 / 16 : ℝ)) = (1 / 8 : ℝ) * y + (15 / 16 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [h0, hq0]
    have eR0 : aFun (y) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [aFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR1 : p1Fun ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR2 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR3 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [h0, hq0]
    have eR4 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [h0, hq0]
    have eR5 : cFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eR6 : aInv ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 4 : ℝ) * y + (7 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [h0, hq0]
    have eR7 : aInv ((1 / 4 : ℝ) * y + (7 / 8 : ℝ)) = (1 / 8 : ℝ) * y + (15 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [h0, hq0]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5, eR6, eR7] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq1 | hp1
  · have eL0 : bFun (y) = (1 / 2 : ℝ) * y + (1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL1 : bFun ((1 / 2 : ℝ) * y + (1 / 4 : ℝ)) = (1 / 4 : ℝ) * y + (3 / 8 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL2 : cFun ((1 / 4 : ℝ) * y + (3 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (-1 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL3 : aInv ((1 / 2 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 2 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL4 : aInv ((1 : ℝ) * y + (-1 / 2 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL5 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eR0 : aFun (y) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [aFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR1 : p1Fun ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 4 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eR2 : aInv ((1 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR3 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eR4 : bFun ((1 / 2 : ℝ) * y + (1 / 4 : ℝ)) = (1 / 4 : ℝ) * y + (3 / 8 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eR5 : cFun ((1 / 4 : ℝ) * y + (3 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (-1 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eR6 : aInv ((1 / 2 : ℝ) * y + (-1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 2 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eR7 : aInv ((1 : ℝ) * y + (-1 / 2 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5, eR6, eR7] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq2 | hp2
  · have eL0 : bFun (y) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL1 : bFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 16 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eL2 : cFun ((1 / 2 : ℝ) * y + (3 / 16 : ℝ)) = (1 : ℝ) * y + (-5 / 8 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL3 : aInv ((1 : ℝ) * y + (-5 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp1, hq2]
    have eL4 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL5 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eR1 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR2 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eR3 : bFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    have eR4 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR5 : cFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR6 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eR7 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp1, hq2]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5, eR6, eR7] <;> ring1
  rcases lt_or_ge y (15 / 16 : ℝ) with hq3 | hp3
  · have eL0 : bFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL1 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eL2 : cFun ((2 : ℝ) * y + (-9 / 8 : ℝ)) = (4 : ℝ) * y + (-13 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eL3 : aInv ((4 : ℝ) * y + (-13 / 4 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eL4 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eL5 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR1 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR2 : aInv ((4 : ℝ) * y + (-3 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, hq3]
    have eR3 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eR4 : bFun ((2 : ℝ) * y + (-9 / 8 : ℝ)) = (1 : ℝ) * y + (-5 / 16 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp2, hq3]
    have eR5 : cFun ((1 : ℝ) * y + (-5 / 16 : ℝ)) = (2 : ℝ) * y + (-13 / 8 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    have eR6 : aInv ((2 : ℝ) * y + (-13 / 8 : ℝ)) = (4 : ℝ) * y + (-13 / 4 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp2, hq3]
    have eR7 : aInv ((4 : ℝ) * y + (-13 / 4 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp2, hq3]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5, eR6, eR7] <;> ring1
  have eL0 : bFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eL1 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eL2 : cFun ((4 : ℝ) * y + (-3 : ℝ)) = (4 : ℝ) * y + (-13 / 4 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eL3 : aInv ((4 : ℝ) * y + (-13 / 4 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eL4 : aInv ((2 : ℝ) * y + (-9 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eL5 : p1Fun ((1 : ℝ) * y + (-1 / 16 : ℝ)) = (1 : ℝ) * y + (-1 / 16 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, h1]
  have eR0 : aFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eR1 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp3, h1]
  have eR2 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eR3 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eR4 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (4 : ℝ) * y + (-3 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eR5 : cFun ((4 : ℝ) * y + (-3 : ℝ)) = (4 : ℝ) * y + (-13 / 4 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eR6 : aInv ((4 : ℝ) * y + (-13 / 4 : ℝ)) = (2 : ℝ) * y + (-9 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  have eR7 : aInv ((2 : ℝ) * y + (-9 / 8 : ℝ)) = (1 : ℝ) * y + (-1 / 16 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp3, h1]
  rw [eL0, eL1, eL2, eL3, eL4, eL5, eR0, eR1, eR2, eR3, eR4, eR5, eR6, eR7] <;> ring1

lemma relV14 : ((piV 1) * (a⁻¹ * c * b)) * ((piV 1) * (a⁻¹ * c * b)) * ((piV 1) * (a⁻¹ * c * b)) = 1 := by
  apply perm_ext
  intro x
  simp only [mul_inv_rev, inv_inv, inv_pow, pow_succ, pow_zero, one_mul, mul_one, inv_one, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id, ico_Av, ico_Bv, ico_Cv, ico_Avinv, ico_Bvinv, ico_Cvinv, ico_P, ico_Pinv, ico_piV_one]
  have h0 := ico_nonneg x
  have h1 := ico_lt_one x
  generalize ico x = y at h0 h1 ⊢
  rcases lt_or_ge y (1 / 2 : ℝ) with hq0 | hp0
  · have eL0 : bFun (y) = (1 : ℝ) * y + (0 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [h0, hq0]
    have eL1 : cFun ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL2 : aInv ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 4 : ℝ) * y + (7 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [h0, hq0]
    have eL3 : p1Fun ((1 / 4 : ℝ) * y + (7 / 8 : ℝ)) = (1 / 4 : ℝ) * y + (7 / 8 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [h0, hq0]
    have eL4 : bFun ((1 / 4 : ℝ) * y + (7 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (3 / 4 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [h0, hq0]
    have eL5 : cFun ((1 / 2 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith only [h0, hq0]
    have eL6 : aInv ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 / 4 : ℝ) * y + (3 / 4 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [h0, hq0]
    have eL7 : p1Fun ((1 / 4 : ℝ) * y + (3 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [h0, hq0]
    have eL8 : bFun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 / 4 : ℝ) * y + (1 / 2 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL9 : cFun ((1 / 4 : ℝ) * y + (1 / 2 : ℝ)) = (1 / 2 : ℝ) * y + (0 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [h0, hq0]
    have eL10 : aInv ((1 / 2 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    have eL11 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [h0, hq0]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11] <;> ring1
  rcases lt_or_ge y (3 / 4 : ℝ) with hq1 | hp1
  · have eL0 : bFun (y) = (1 / 2 : ℝ) * y + (1 / 4 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL1 : cFun ((1 / 2 : ℝ) * y + (1 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 2 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [hp0, hq1]
    have eL2 : aInv ((1 : ℝ) * y + (-1 / 2 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL3 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL4 : bFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [hp0, hq1]
    have eL5 : cFun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (1 / 4 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith only [hp0, hq1]
    have eL6 : aInv ((1 : ℝ) * y + (1 / 4 : ℝ)) = (1 / 2 : ℝ) * y + (5 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eL7 : p1Fun ((1 / 2 : ℝ) * y + (5 / 8 : ℝ)) = (1 / 2 : ℝ) * y + (5 / 8 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp0, hq1]
    have eL8 : bFun ((1 / 2 : ℝ) * y + (5 / 8 : ℝ)) = (1 : ℝ) * y + (1 / 4 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eL9 : cFun ((1 : ℝ) * y + (1 / 4 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eL10 : aInv ((1 : ℝ) * y + (0 : ℝ)) = (1 / 2 : ℝ) * y + (1 / 2 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    have eL11 : p1Fun ((1 / 2 : ℝ) * y + (1 / 2 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp0, hq1]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11] <;> ring1
  rcases lt_or_ge y (7 / 8 : ℝ) with hq2 | hp2
  · have eL0 : bFun (y) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL1 : cFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL2 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL3 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL4 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL5 : cFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL6 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL7 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL8 : bFun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [bFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL9 : cFun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL10 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [aInv_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    have eL11 : p1Fun ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem2] <;> first | ring1 | linarith only [hp1, hq2]
    rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11] <;> ring1
  have eL0 : bFun (y) = (2 : ℝ) * y + (-1 : ℝ) := by rw [bFun_of_mem3] <;> first | ring1 | linarith only [hp2, h1]
  have eL1 : cFun ((2 : ℝ) * y + (-1 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [cFun_of_mem3] <;> first | ring1 | linarith only [hp2, h1]
  have eL2 : aInv ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (1 : ℝ) * y + (-1 / 8 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, h1]
  have eL3 : p1Fun ((1 : ℝ) * y + (-1 / 8 : ℝ)) = (2 : ℝ) * y + (-5 / 4 : ℝ) := by rw [p1Fun_of_mem3] <;> first | ring1 | linarith only [hp2, h1]
  have eL4 : bFun ((2 : ℝ) * y + (-5 / 4 : ℝ)) = (1 : ℝ) * y + (-3 / 8 : ℝ) := by rw [bFun_of_mem1] <;> first | ring1 | linarith only [hp2, h1]
  have eL5 : cFun ((1 : ℝ) * y + (-3 / 8 : ℝ)) = (2 : ℝ) * y + (-7 / 4 : ℝ) := by rw [cFun_of_mem2] <;> first | ring1 | linarith only [hp2, h1]
  have eL6 : aInv ((2 : ℝ) * y + (-7 / 4 : ℝ)) = (4 : ℝ) * y + (-7 / 2 : ℝ) := by rw [aInv_of_mem1] <;> first | ring1 | linarith only [hp2, h1]
  have eL7 : p1Fun ((4 : ℝ) * y + (-7 / 2 : ℝ)) = (4 : ℝ) * y + (-7 / 2 : ℝ) := by rw [p1Fun_of_mem1] <;> first | ring1 | linarith only [hp2, h1]
  have eL8 : bFun ((4 : ℝ) * y + (-7 / 2 : ℝ)) = (4 : ℝ) * y + (-7 / 2 : ℝ) := by rw [bFun_of_le_half] <;> first | ring1 | linarith only [hp2, h1]
  have eL9 : cFun ((4 : ℝ) * y + (-7 / 2 : ℝ)) = (2 : ℝ) * y + (-1 : ℝ) := by rw [cFun_of_mem1] <;> first | ring1 | linarith only [hp2, h1]
  have eL10 : aInv ((2 : ℝ) * y + (-1 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [aInv_of_mem3] <;> first | ring1 | linarith only [hp2, h1]
  have eL11 : p1Fun ((1 : ℝ) * y + (0 : ℝ)) = (1 : ℝ) * y + (0 : ℝ) := by rw [p1Fun_of_mem4] <;> first | ring1 | linarith only [hp2, h1]
  rw [eL0, eL1, eL2, eL3, eL4, eL5, eL6, eL7, eL8, eL9, eL10, eL11] <;> ring1


theorem relations_symV :
    (a * b⁻¹) * XV 2 * (a * b⁻¹)⁻¹ * (XV 2)⁻¹ = 1 ∧
      (a * b⁻¹) * XV 3 * (a * b⁻¹)⁻¹ * (XV 3)⁻¹ = 1 ∧
      CV 1 = b * CV 2 ∧
      CV 2 * XV 2 = b * CV 3 ∧
      CV 1 * a = CV 2 ^ 2 ∧
      CV 1 ^ 3 = 1 ∧
      piV 1 ^ 2 = 1 ∧
      piV 1 * piV 3 = piV 3 * piV 1 ∧
      (piV 2 * piV 1) ^ 3 = 1 ∧
      XV 3 * piV 1 = piV 1 * XV 3 ∧
      piV 1 * XV 2 = b * piV 2 * piV 1 ∧
      piV 2 * b = b * piV 3 ∧
      piV 1 * CV 3 = CV 3 * piV 2 ∧
      (piV 1 * CV 2) ^ 3 = 1 := by
  obtain ⟨-, t1, t2, t3, t4, t5, t6⟩ := closure_range_symT_eq_T_and_relations
  rw [XV_two, XV_three, CV_one, CV_two, CV_three, piV_two', piV_three']
  refine ⟨t1, t2, t3, t4, t5, t6, relV7, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := relV8; simp only [pow_succ, pow_zero, one_mul, mul_assoc] at this ⊢; exact this
  · have := relV9; simp only [pow_succ, pow_zero, one_mul, mul_assoc] at this ⊢; exact this
  · have := relV10; simp only [pow_succ, pow_zero, one_mul, mul_assoc] at this ⊢; exact this
  · have := relV11; simp only [pow_succ, pow_zero, one_mul, mul_assoc] at this ⊢; exact this
  · have := relV12; simp only [pow_succ, pow_zero, one_mul, mul_assoc] at this ⊢; exact this
  · have := relV13; simp only [pow_succ, pow_zero, one_mul, mul_assoc] at this ⊢; exact this
  · have := relV14; simp only [pow_succ, pow_zero, one_mul, mul_assoc] at this ⊢; exact this

end CannonFloydParry.S6

open CannonFloydParry in
theorem solution :
    Subgroup.closure (Set.range symV) = V ∧
      let a := symV FormalV.A
      let b := symV FormalV.B
      (a * b⁻¹) * XV 2 * (a * b⁻¹)⁻¹ * (XV 2)⁻¹ = 1 ∧
      (a * b⁻¹) * XV 3 * (a * b⁻¹)⁻¹ * (XV 3)⁻¹ = 1 ∧
      CV 1 = b * CV 2 ∧
      CV 2 * XV 2 = b * CV 3 ∧
      CV 1 * a = CV 2 ^ 2 ∧
      CV 1 ^ 3 = 1 ∧
      piV 1 ^ 2 = 1 ∧
      piV 1 * piV 3 = piV 3 * piV 1 ∧
      (piV 2 * piV 1) ^ 3 = 1 ∧
      XV 3 * piV 1 = piV 1 * XV 3 ∧
      piV 1 * XV 2 = b * piV 2 * piV 1 ∧
      piV 2 * b = b * piV 3 ∧
      piV 1 * CV 3 = CV 3 * piV 2 ∧
      (piV 1 * CV 2) ^ 3 = 1 := by
  exact ⟨S6.closure_range_symV_eq_V, S6.relations_symV⟩
