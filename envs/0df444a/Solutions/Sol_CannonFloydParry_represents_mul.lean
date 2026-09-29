-- Prove2me | solution 1 for CannonFloydParry.represents_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-16T21:52:13.640953+00:00
-- url     : https://prove2.me/submissions/e0dfa04f-e464-4f3f-a18e-d7e04b0b98e0

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

/-! ### Lengths of mark lists -/

lemma marksAux_length : ∀ (t : TTree) (a b : ℝ), (t.marksAux a b).length + 1 = t.leafCount := by
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

lemma marks_length (t : TTree) : t.marks.length = t.leafCount + 1 := by
  show ((0 : ℝ) :: (t.marksAux 0 1 ++ [1])).length = t.leafCount + 1
  have := marksAux_length t 0 1
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

/-! ### Chains versus indices -/

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

lemma getD_map {l : List ℝ} {g : ℝ → ℝ} {i : ℕ} (hi : i < l.length) :
    (l.map g).getD i 0 = g (l.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi,
    List.getElem_map]

/-! ### The extension of a product is the composite of the extensions -/

lemma extend_mul (f g : UI ≃o UI) (z : ℝ) : extend (g * f) z = extend g (extend f z) := by
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

end CannonFloydParry

open CannonFloydParry

theorem solution {Q R S : TTree} {f g : UI ≃o UI}
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
    rw [marks_length, marks_length, hQR]
  -- the marks of `Q` go to the marks of `R`, index by index
  have hmapj : ∀ i, i < Q.marks.length → extend f (Q.marks.getD i 0) = R.marks.getD i 0 := by
    intro i hi
    have h : (Q.marks.map (extend f)).getD i 0 = R.marks.getD i 0 := by rw [hfM']
    rw [getD_map hi] at h
    exact h
  refine ⟨mul_mem hgF hfF, ?_, ?_⟩
  · -- affine on each interval of the domain partition of `Q`
    show AffineOnPieces (extend (g * f)) Q.marks
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
    rw [extend_mul, hac' _ hfz, hac _ hz]
    ring
  · -- the marks of `Q` go to the marks of `S`
    show Q.marks.map (extend (g * f)) = S.marks
    calc Q.marks.map (extend (g * f))
        = Q.marks.map (fun z => extend g (extend f z)) := by
          refine List.map_congr_left ?_
          intro x _
          exact extend_mul f g x
      _ = (Q.marks.map (extend f)).map (extend g) := by rw [List.map_map]; rfl
      _ = R.marks.map (extend g) := by rw [hfM']
      _ = S.marks := hgM'
