-- Prove2me | solution 1 for CauchyRiemannIndex.finiteDimensional_ker_isClosed_range_of_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T18:01:19.186987+00:00
-- url     : https://prove2.me/submissions/4c7b5f73-31a6-4ba1-8e6b-cfa76bf662b5

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.LocallyConvex.HahnBanach

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem fdker_closedRange_aux {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (T : X →L[ℝ] Y) (K : X →L[ℝ] Z) (hK : IsCompactOperator K) (c : ℝ)
    (hc : ∀ x, ‖x‖ ≤ c * ‖T x‖ + c * ‖K x‖) :
    FiniteDimensional ℝ (LinearMap.ker (T : X →ₗ[ℝ] Y)) ∧ IsClosed (Set.range T) := by
  -- the pair map `P x = (T x, K x)` is a closed embedding
  set P : X →L[ℝ] Y × Z := T.prod K with hPdef
  have hPx : ∀ x, P x = (T x, K x) := fun x => rfl
  let C : ℝ≥0 := ⟨2 * |c|, by positivity⟩
  have hPnorm : ∀ x, ‖x‖ ≤ C * ‖P x‖ := by
    intro x
    have h1 : ‖T x‖ ≤ ‖P x‖ := by rw [hPx]; exact norm_fst_le (T x, K x)
    have h2 : ‖K x‖ ≤ ‖P x‖ := by rw [hPx]; exact norm_snd_le (T x, K x)
    have e1 := mul_nonneg (sub_nonneg.2 (le_abs_self c)) (norm_nonneg (T x))
    have e2 := mul_nonneg (sub_nonneg.2 (le_abs_self c)) (norm_nonneg (K x))
    have e3 := mul_nonneg (abs_nonneg c) (sub_nonneg.2 h1)
    have e4 := mul_nonneg (abs_nonneg c) (sub_nonneg.2 h2)
    have := hc x
    show ‖x‖ ≤ 2 * |c| * ‖P x‖
    nlinarith
  have hPemb : IsClosedEmbedding P :=
    (P.antilipschitz_of_bound hPnorm).isClosedEmbedding P.uniformContinuous
  set L := closure (K '' Metric.closedBall 0 1) with hLdef
  have hL : IsCompact L := hK.isCompact_closure_image_closedBall 1
  set N := LinearMap.ker (T : X →ₗ[ℝ] Y) with hNdef
  have hNclosed : IsClosed (N : Set X) := T.isClosed_ker
  -- (1) the kernel is finite-dimensional
  have hfin : FiniteDimensional ℝ N := by
    refine FiniteDimensional.of_isCompact_closedBall₀ ℝ one_pos ?_
    have hS : IsCompact (P ⁻¹' ({(0 : Y)} ×ˢ L)) :=
      hPemb.isCompact_preimage (isCompact_singleton.prod hL)
    have hemb := hNclosed.isClosedEmbedding_subtypeVal
    rw [hemb.isInducing.isCompact_iff]
    refine hS.of_isClosed_subset (hemb.isClosedMap _ Metric.isClosed_closedBall) ?_
    rintro _ ⟨y, hy, rfl⟩
    have hyT : T (y : X) = 0 := y.2
    refine ⟨by simp [hPx, hyT], ?_⟩
    rw [hPx]
    refine subset_closure ⟨(y : X), ?_, rfl⟩
    simpa [mem_closedBall_zero_iff] using hy
  refine ⟨hfin, ?_⟩
  -- (2) closed range
  obtain ⟨V, hVclosed, hNV⟩ :=
    (Submodule.ClosedComplemented.of_finiteDimensional N).exists_isClosed_isCompl
  have hbound : ∃ D : ℝ, ∀ v ∈ V, ‖v‖ ≤ D * ‖T v‖ := by
    by_contra hcon
    push_neg at hcon
    have hu : ∀ n : ℕ, ∃ u : X, u ∈ V ∧ ‖u‖ = 1 ∧ ‖T u‖ < 1 / ((n : ℝ) + 1) := by
      intro n
      obtain ⟨v, hv, hlt⟩ := hcon ((n : ℝ) + 1)
      have hvpos : 0 < ‖v‖ := lt_of_le_of_lt (by positivity) hlt
      have hv0 : v ≠ 0 := norm_pos_iff.1 hvpos
      refine ⟨‖v‖⁻¹ • v, V.smul_mem _ hv, norm_smul_inv_norm hv0, ?_⟩
      rw [map_smul, norm_smul, norm_inv, norm_norm, inv_mul_lt_iff₀ hvpos,
        mul_one_div, lt_div_iff₀ (by positivity)]
      linarith
    choose u huV hu1 huT using hu
    have huL : ∀ n, K (u n) ∈ L := fun n =>
      subset_closure ⟨u n, by simp [hu1 n], rfl⟩
    obtain ⟨z, -, φ, hφ, hz⟩ := hL.tendsto_subseq huL
    have hT0 : Tendsto (fun n => T (u n)) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => (huT n).le) tendsto_one_div_add_atTop_nhds_zero_nat
    have hPlim : Tendsto (P ∘ (u ∘ φ)) atTop (𝓝 ((0 : Y), z)) := by
      have := (hT0.comp hφ.tendsto_atTop).prodMk_nhds hz
      exact this
    obtain ⟨x, hx⟩ : ((0 : Y), z) ∈ Set.range P :=
      hPemb.isClosed_range.mem_of_tendsto hPlim (Eventually.of_forall fun n => ⟨_, rfl⟩)
    have hux : Tendsto (u ∘ φ) atTop (𝓝 x) := by
      rw [hPemb.isInducing.tendsto_nhds_iff, hx]; exact hPlim
    have hxV : x ∈ V := hVclosed.mem_of_tendsto hux (Eventually.of_forall fun n => huV _)
    have hx1 : ‖x‖ = 1 := by
      have h1 : Tendsto (fun n => ‖(u ∘ φ) n‖) atTop (𝓝 ‖x‖) := hux.norm
      have h2 : Tendsto (fun n => ‖(u ∘ φ) n‖) atTop (𝓝 1) := by
        simp only [Function.comp, hu1]; exact tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2
    have hxN : x ∈ N := by
      have : (P x).1 = 0 := by rw [hx]
      exact this
    have : x ∈ N ⊓ V := ⟨hxN, hxV⟩
    rw [hNV.inf_eq_bot, Submodule.mem_bot] at this
    simp [this] at hx1
  obtain ⟨D, hD⟩ := hbound
  let D' : ℝ≥0 := ⟨max D 0, le_max_right _ _⟩
  haveI : CompleteSpace V := hVclosed.completeSpace_coe
  let TV : V →L[ℝ] Y := T.comp V.subtypeL
  have hTV : AntilipschitzWith D' TV := TV.antilipschitz_of_bound fun v => by
    show ‖(v : X)‖ ≤ max D 0 * ‖T v‖
    exact (hD v v.2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hrange : Set.range T = Set.range TV := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hx : x ∈ N ⊔ V := by rw [hNV.sup_eq_top]; trivial
      obtain ⟨n, hn, v, hv, rfl⟩ := Submodule.mem_sup.1 hx
      refine ⟨⟨v, hv⟩, ?_⟩
      have hTn : T n = 0 := hn
      simp [TV, hTn]
    · rintro ⟨v, rfl⟩
      exact ⟨v, rfl⟩
  rw [hrange]
  exact hTV.isClosed_range TV.uniformContinuous

end CauchyRiemannIndex

open Topology in
theorem solution {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (T : X →L[ℝ] Y) (K : X →L[ℝ] Z) (hK : IsCompactOperator K) (c : ℝ)
    (hc : ∀ x, ‖x‖ ≤ c * ‖T x‖ + c * ‖K x‖) :
    FiniteDimensional ℝ (LinearMap.ker (T : X →ₗ[ℝ] Y)) ∧ IsClosed (Set.range T) :=
  CauchyRiemannIndex.fdker_closedRange_aux T K hK c hc
