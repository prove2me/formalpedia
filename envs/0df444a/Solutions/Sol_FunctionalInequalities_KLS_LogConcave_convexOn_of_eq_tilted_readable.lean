-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.convexOn_of_eq_tilted_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:42:07.303642+00:00
-- url     : https://prove2.me/submissions/137c0fad-9f83-4086-8dbb-3469ae8c6904

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integrable_exp_neg_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_exp_neg_pos_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_interior_support_nonempty_of_eq_tilted_readable

noncomputable section
open MeasureTheory Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
section Convexity
variable [SecondCountableTopology V] (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
/-- A log-concave law `ν = m.tilted (-U)` with a continuous potential has a convex potential: the
continuous density `e^{-U} / Z` agrees with the log-concave Borell representative of `ν`, which is
continuous because `ν` has full support. Converse of `isBorellDensity_of_eq_tilted`. -/
theorem solution (hν : FunctionalInequalities.KLS.LogConcave ν) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U) : ConvexOn ℝ Set.univ U := by
  have hint : Integrable (fun x => Real.exp (-U x)) m := FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_readable hνU
  have hZ : 0 < ∫ y, Real.exp (-U y) ∂m := FunctionalInequalities.KLS.LogConcave.integral_exp_neg_pos_of_eq_tilted_readable hνU
  set Z := ∫ y, Real.exp (-U y) ∂m with hZdef
  set q : V → ℝ := fun x => Real.exp (-U x) / Z with hqdef
  have hqpos : ∀ x, 0 < q x := fun x => div_pos (Real.exp_pos _) hZ
  have hqc : Continuous q := (Real.continuous_exp.comp hU.neg).div_const _
  have hmν : m ≪ (ν : Measure V) := by
    rw [hνU]; exact absolutelyContinuous_tilted (by simpa using hint)
  have hνm : (ν : Measure V) ≪ m := by rw [hνU]; exact tilted_absolutelyContinuous m (-U)
  have hsupp : (ν : Measure V).support = Set.univ := by
    refine Set.eq_univ_of_forall fun x => (Measure.mem_support_iff_forall x).2 fun s hs => ?_
    exact pos_iff_ne_zero.2 fun h0 =>
      (pos_iff_ne_zero.1 (Measure.measure_pos_of_mem_nhds m hs)) (hmν h0)
  obtain ⟨ρ, hρ⟩ := hν.exists_isBorellDensity_of_interior_support_nonempty m
    (FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_eq_tilted_readable m hνU) hνm
  have hρc : Continuous ρ := by
    have h := hρ.continuousOn_interior_support
    rw [hsupp, interior_univ] at h
    exact continuousOn_univ.mp h
  have hqd : m.withDensity (fun x => ENNReal.ofReal (q x)) = ν := by rw [hνU]; rfl
  have hae : (fun x => ENNReal.ofReal (ρ x)) =ᵐ[m] fun x => ENNReal.ofReal (q x) :=
    (withDensity_eq_iff_of_sigmaFinite hρc.measurable.ennreal_ofReal.aemeasurable
      hqc.measurable.ennreal_ofReal.aemeasurable).mp (hρ.withDensity_eq.trans hqd.symm)
  have hae' : ρ =ᵐ[m] q := by
    filter_upwards [hae] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff (hρ.nonneg x) (hqpos x).le).mp hx
  have heq : ρ = q := (hρc.ae_eq_iff_eq m hqc).mp hae'
  have hlog : ∀ x, Real.log (q x) = -U x - Real.log Z := fun x => by
    rw [hqdef, Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]
  rw [convexOn_iff_forall_pos]
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  have h := hρ.logConcave x y a ha (by linarith)
  rw [heq] at h
  have hx' := Real.rpow_pos_of_pos (hqpos x) a
  have hy' := Real.rpow_pos_of_pos (hqpos y) (1 - a)
  have h' := Real.log_le_log (mul_pos hx' hy') h
  rw [Real.log_mul hx'.ne' hy'.ne', Real.log_rpow (hqpos x), Real.log_rpow (hqpos y), hlog, hlog,
    hlog] at h'
  simp only [smul_eq_mul]
  nlinarith
