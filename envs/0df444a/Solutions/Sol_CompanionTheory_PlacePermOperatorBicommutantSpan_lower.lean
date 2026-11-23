-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:54.499961+00:00
-- url     : https://prove2.me/submissions/2aefe148-219d-43e9-a2b0-975982f4a638

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_Nuabs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (P : Subgroup G) (ν : Measure G) [SFinite ν], (∀ p ∈ P, ν.map (fun g => p * g) = ν) → (∀ U ∈ 𝓝 (1 : G), ν U ≠ 0) → ∀ C : Set G, IsCompact C → ∀ φ : G → ℝ≥0∞, Continuous φ → (∀ c ∈ C, φ c ≠ 0) → ∃ m : ℝ≥0∞, m ≠ 0 ∧ m ≠ ⊤ ∧ ∀ p ∈ P, ∀ c ∈ C, m ≤ ∫⁻ q, φ (q⁻¹ * (p * c)) ∂ν := by
  intro G _ _ _ _ _ _ _ _ P ν _ hν hU C hC φ hφ hφC
  have key : ∃ m : ℝ≥0∞, m ≠ 0 ∧ m ≠ ⊤ ∧ ∀ c ∈ C, m ≤ ∫⁻ q, φ (q⁻¹ * c) ∂ν := by
    refine hC.induction_on (p := fun s => ∃ m : ℝ≥0∞, m ≠ 0 ∧ m ≠ ⊤ ∧ ∀ c ∈ s, m ≤ ∫⁻ q, φ (q⁻¹ * c) ∂ν)
      ⟨1, one_ne_zero, ENNReal.one_ne_top, fun _ h => h.elim⟩
      (fun s t hst ⟨m, h1, h2, h3⟩ => ⟨m, h1, h2, fun c hc => h3 c (hst hc)⟩)
      (fun s t ⟨m, h1, h2, h3⟩ ⟨m', h1', _, h3'⟩ => ⟨min m m', (lt_min h1.bot_lt h1'.bot_lt).ne',
        ((min_le_left _ _).trans_lt h2.lt_top).ne, fun c hc => hc.elim (fun h => (min_le_left _ _).trans (h3 c h))
        fun h => (min_le_right _ _).trans (h3' c h)⟩) fun c₀ hc₀ => ?_
    obtain ⟨ε, h0, hε⟩ := exists_between (hφC c₀ hc₀).bot_lt
    have hO : {z : G × G | ε < φ (z.1⁻¹ * z.2)} ∈ 𝓝 ((1 : G), c₀) :=
      (isOpen_lt continuous_const (hφ.comp (continuous_fst.inv.mul continuous_snd))).mem_nhds (by simpa using hε)
    obtain ⟨U, hU1, W, hW, hsub⟩ := mem_nhds_prod_iff.1 hO
    refine ⟨W, mem_nhdsWithin_of_mem_nhds hW, min 1 (ε * ν (interior U)),
      (lt_min one_pos (ENNReal.mul_pos h0.ne' (hU _ (interior_mem_nhds.2 hU1)))).ne',
      ((min_le_left _ _).trans_lt ENNReal.one_lt_top).ne, fun c hc => (min_le_right _ _).trans ?_⟩
    rw [← lintegral_indicator_const isOpen_interior.measurableSet]
    refine lintegral_mono fun q => ?_
    by_cases hq : q ∈ interior U
    · rw [Set.indicator_of_mem hq]
      exact (hsub (Set.mk_mem_prod (interior_subset hq) hc)).le
    · rw [Set.indicator_of_notMem hq]
      exact zero_le
  obtain ⟨m, h1, h2, h3⟩ := key
  refine ⟨m, h1, h2, fun p hp c hc => (h3 c hc).trans (le_of_eq ?_)⟩
  conv_rhs => rw [← hν p hp]
  rw [lintegral_map (f := fun q => φ (q⁻¹ * (p * c))) (hφ.measurable.comp (measurable_inv.mul_const _)) (measurable_const_mul p)]
  simp [mul_assoc]
end CompanionTheory.PlacePermOperatorBicommutantSpan
