-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.restrict_le_smul_of_eq_tilted_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:15.050526+00:00
-- url     : https://prove2.me/submissions/4ea191ae-97c6-4bf6-ab57-44f32ee44075

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integrable_exp_neg_of_eq_tilted_readable

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
omit [InnerProductSpace ℝ V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- On a compact set Haar measure is dominated by a finite multiple of the tilted law, because
the density `e^{-U}/Z` is bounded below there. -/
theorem solution (hνU : (ν : Measure V) = m.tilted (-U)) (hU : Continuous U)
    {K : Set V} (hK : IsCompact K) :
    ∃ c : ENNReal, c ≠ ⊤ ∧ m.restrict K ≤ c • (ν : Measure V) := by
  have hInt : Integrable (fun x => Real.exp (-U x)) m :=
    FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_readable hνU
  let Z : ℝ := ∫ y, Real.exp (-U y) ∂m
  have hZ : 0 < Z := by
    dsimp [Z]
    rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hInt]
    simp [Function.support, (Real.exp_pos _).ne', Measure.measure_univ_pos, NeZero.ne m]
  have hZ0 : Z ≠ 0 := ne_of_gt hZ
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ K, U x ≤ M := by
    by_cases hKne : K.Nonempty
    · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hKne hU.continuousOn
      exact ⟨U x, fun y hy => hmax hy⟩
    · exact ⟨0, fun x hx => (hKne ⟨x, hx⟩).elim⟩
  refine ⟨ENNReal.ofReal (Z * Real.exp M), ENNReal.ofReal_ne_top, ?_⟩
  refine Measure.le_intro fun s hs _ => ?_
  rw [Measure.restrict_apply hs, Measure.smul_apply, hνU, Measure.tilted,
    withDensity_apply _ hs, smul_eq_mul]
  calc
    m (s ∩ K) = ∫⁻ x in s ∩ K, 1 ∂m := by simp
    _ ≤ ∫⁻ x in s ∩ K,
        ENNReal.ofReal (Z * Real.exp M) *
          ENNReal.ofReal (Real.exp ((-U) x) / Z) ∂m := by
      refine setLIntegral_mono' (hs.inter hK.measurableSet) ?_
      intro x hx
      have hprod :
          (Z * Real.exp M) * (Real.exp ((-U) x) / Z) =
            Real.exp (M - U x) := by
        change (Z * Real.exp M) * (Real.exp (-U x) / Z) =
          Real.exp (M - U x)
        calc
          (Z * Real.exp M) * (Real.exp (-U x) / Z) =
              Real.exp M * Real.exp (-U x) := by
                field_simp [hZ0]
          _ = Real.exp (M + (-U x)) := by
                rw [← Real.exp_add]
          _ = Real.exp (M - U x) := by ring_nf
      calc
        (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp (M - U x)) := by
          rw [ENNReal.one_le_ofReal]
          exact (Real.one_le_exp_iff).2 (sub_nonneg.mpr (hM x hx.2))
        _ = ENNReal.ofReal (Z * Real.exp M) *
              ENNReal.ofReal (Real.exp ((-U) x) / Z) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact congrArg ENNReal.ofReal hprod.symm
    _ ≤ ∫⁻ x in s,
        ENNReal.ofReal (Z * Real.exp M) *
          ENNReal.ofReal (Real.exp ((-U) x) / Z) ∂m :=
      lintegral_mono_set Set.inter_subset_left
    _ = ENNReal.ofReal (Z * Real.exp M) *
        (∫⁻ x in s, ENNReal.ofReal (Real.exp ((-U) x) / Z) ∂m) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
