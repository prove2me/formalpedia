-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsD.pos_homog_induces_distance
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:28:37.062465+00:00
-- url     : https://prove2.me/submissions/72caf2a5-4e50-44b2-9a7d-daec0cd16efd

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_ZeroMZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_TriangleInequality
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsIntegerValuedGamma
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_InducedGammaFromR
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_InducedGammaFromZ

open scoped Pointwise
open Classical

namespace DisPHI
open DiscreteConvex.MConvexFunctionsD

/-- Indicator (value 0) of `{x | ∑ x = 0, x i ≠ 0 for some i ∈ I}`. -/
noncomputable def F {W : Type} [Fintype W] (I : Set W) : (W → ℝ) → WithTop ℝ :=
  fun x => if ∑ w, x w = 0 ∧ ∃ i ∈ I, x i ≠ 0 then 0 else ⊤

lemma charvec_sum {W : Type} [Fintype W] [DecidableEq W] (u : W) :
    ∑ w, ((CharVec u w : ℤ) : ℝ) = 1 := by
  simp [CharVec]

lemma charvec_abs {W : Type} [DecidableEq W] (u v w : W) :
    |((CharVec u w : ℤ) : ℝ) - ((CharVec v w : ℤ) : ℝ)| ≤ 1 := by
  unfold CharVec; split_ifs <;> norm_num

lemma exch {W : Type} [Fintype W] [DecidableEq W] (I : Set W) : MExchangeAxiomR (F I) := by
  intro x hx y hy u hu
  have hx' : ∑ w, x w = 0 ∧ ∃ i ∈ I, x i ≠ 0 := by
    by_contra hc; exact hx (if_neg hc)
  have hy' : ∑ w, y w = 0 ∧ ∃ i ∈ I, y i ≠ 0 := by
    by_contra hc; exact hy (if_neg hc)
  have hfx : F I x = 0 := if_pos hx'
  have hfy : F I y = 0 := if_pos hy'
  obtain ⟨hxs, i, hiI, hxi⟩ := hx'
  obtain ⟨hys, j, hjI, hyj⟩ := hy'
  obtain ⟨v, hv⟩ : ∃ v, x v < y v := by
    by_contra hc
    push Not at hc
    have : ∑ w, y w < ∑ w, x w :=
      Finset.sum_lt_sum (fun w _ => hc w) ⟨u, Finset.mem_univ _, hu⟩
    linarith
  have hm : 0 < min |x i| |y j| := lt_min (abs_pos.2 hxi) (abs_pos.2 hyj)
  refine ⟨v, hv, min |x i| |y j| / 2, half_pos hm, fun α h0 h1 => ?_⟩
  have hlx : α < |x i| := by have := min_le_left |x i| |y j|; linarith
  have hly : α < |y j| := by have := min_le_right |x i| |y j|; linarith
  have key1 : F I (fun w => x w - α * (CharVec u w - CharVec v w : ℝ)) = 0 := by
    apply if_pos
    refine ⟨?_, i, hiI, ?_⟩
    · rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, charvec_sum,
        charvec_sum, hxs]; ring
    · intro h
      have hb := charvec_abs u v i
      have e : x i = α * (((CharVec u i : ℤ) : ℝ) - ((CharVec v i : ℤ) : ℝ)) := by linarith
      have : |x i| ≤ α := by
        rw [e, abs_mul, abs_of_nonneg h0]
        nlinarith
      linarith
  have key2 : F I (fun w => y w + α * (CharVec u w - CharVec v w : ℝ)) = 0 := by
    apply if_pos
    refine ⟨?_, j, hjI, ?_⟩
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, charvec_sum,
        charvec_sum, hys]; ring
    · intro h
      have hb := charvec_abs u v j
      have e : y j = -(α * (((CharVec u j : ℤ) : ℝ) - ((CharVec v j : ℤ) : ℝ))) := by linarith
      have : |y j| ≤ α := by
        rw [e, abs_neg, abs_mul, abs_of_nonneg h0]
        nlinarith
      linarith
  rw [key1, key2, hfx, hfy]

lemma poshom {W : Type} [Fintype W] [DecidableEq W] :
    PosHomogeneous (F (Set.univ : Set W)) := by
  intro x t ht
  simp only [F]
  have e : (∑ w, t * x w = 0 ∧ ∃ i ∈ (Set.univ : Set W), t * x i ≠ 0) ↔
      (∑ w, x w = 0 ∧ ∃ i ∈ (Set.univ : Set W), x i ≠ 0) := by
    rw [← Finset.mul_sum]; simp [ht.ne']
  by_cases h : ∑ w, x w = 0 ∧ ∃ i ∈ (Set.univ : Set W), x i ≠ 0
  · rw [if_pos h, if_pos (e.2 h)]; simp [PosScalarMul]
  · rw [if_neg h, if_neg (fun h' => h (e.1 h'))]; simp [PosScalarMul, ht.ne']

lemma zeroMR {W : Type} [Fintype W] [DecidableEq W] : ZeroMR (F (Set.univ : Set W)) :=
  ⟨exch _, poshom⟩

lemma ccv_top {W : Type} [Fintype W] [DecidableEq W] (x : W → ℝ) :
    ConvexClosureVal (fun _ : W → ℤ => (⊤ : WithTop ℝ)) x = ⊤ := by
  have hon : ∀ S, ConvexClosureValOn (fun _ : W → ℤ => (⊤ : WithTop ℝ)) S x = ⊤ := by
    intro S
    unfold ConvexClosureValOn
    convert WithTop.sInf_empty (α := ℝ)
    ext L
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨lam, -, hsum, hdom, -, -⟩
    rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
    · simp at hsum
    · exact hdom y hy rfl
  unfold ConvexClosureVal
  have hsub : {L : WithTop ℝ | ∃ (S : Finset (W → ℤ)),
      (∀ y ∈ S, y ∈ DomZ (fun _ : W → ℤ => (⊤ : WithTop ℝ))) ∧
      L = ConvexClosureValOn (fun _ : W → ℤ => (⊤ : WithTop ℝ)) S x} ⊆ {⊤} := by
    rintro L ⟨S, -, rfl⟩
    exact hon S
  rcases Set.subset_singleton_iff_eq.1 hsub with h | h <;> rw [h] <;> simp

lemma zeroMZ {W : Type} [Fintype W] [DecidableEq W] :
    ZeroMZ (fun _ : W → ℤ => (⊤ : WithTop ℝ)) := by
  refine ⟨fun x hx => absurd rfl hx, ?_⟩
  intro x t ht
  rw [ccv_top, ccv_top]
  simp [PosScalarMul, ht.ne']

lemma not_tri : ¬ TriangleInequality (InducedGammaFromR (F (Set.univ : Set (Fin 2)))) := by
  intro h
  have := h 0 1 0
  simp [InducedGammaFromR, F, CharVec] at this

end DisPHI

open DiscreteConvex.MConvexFunctionsD in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (fR : (V → ℝ) → WithTop ℝ) (_hfR : ZeroMR fR)
    (fZ : (V → ℤ) → WithTop ℝ) (_hfZ : ZeroMZ fZ) (_hfZint : IsIntegerValued fZ),
    TriangleInequality (InducedGammaFromR fR) ∧
    TriangleInequality (InducedGammaFromZ fZ) ∧ IsIntegerValuedGamma (InducedGammaFromZ fZ)) := by
  intro h
  exact DisPHI.not_tri (h (V := Fin 2) _ DisPHI.zeroMR _ DisPHI.zeroMZ (fun _ => Or.inl rfl)).1
