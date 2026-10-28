-- Prove2me | solution 1 for FunctionalInequalities.KLS.CEK.exists_limit_ge_normalized_supremum_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:14:55.065238+00:00
-- url     : https://prove2.me/submissions/cddd2e18-561f-483e-b1af-54ef50d73118

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_VariationalMaximum
import Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_normalized_maximizing_sequence_readable
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_integral_bound_of_eventual_functional_lower_readable
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_subseq_integral_bounds_of_convex_epigraph_readable
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_log_sub_ge_of_integral_limits_readable
import Theorems.Thm_FunctionalInequalities_Probability_zero_mem_interior_convexHull_support_of_integral_eq_zero_readable

section
noncomputable section
section
open FunctionalInequalities.Analysis
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
section Integral
variable {E : Type*} [MeasurableSpace E] {μ : MeasureTheory.Measure E}
/-- Source admissibility and nonnegativity identify the actual extended integral,
including its a.e. finite guard; infinity is never totalized before this step. -/
theorem FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential (φ : E → EReal) (hφ : PotentialIntegrable φ μ)
    (hnn : ∀ x, 0 ≤ φ x) :
    AEMeasurable (fun x => (φ x).toENNReal) μ ∧
      (∫⁻ x, (φ x).toENNReal ∂μ) = ENNReal.ofReal (∫ x, (φ x).toReal ∂μ) ∧
      0 ≤ ∫ x, (φ x).toReal ∂μ := by
  have heq : (fun x => (φ x).toENNReal) =ᵐ[μ] (fun x => ENNReal.ofReal (φ x).toReal) := by
    filter_upwards [hφ.2.1] with x hx
    exact EReal.toENNReal_of_ne_top hx
  have hm := hφ.2.2.aemeasurable.ennreal_ofReal
  refine ⟨hm.congr heq.symm, ?_, integral_nonneg (fun x => EReal.toReal_nonneg (hnn x))⟩
  rw [lintegral_congr_ae heq]
  exact (ofReal_integral_eq_lintegral_ofReal hφ.2.2
    (Eventually.of_forall fun x => EReal.toReal_nonneg (hnn x))).symm
end Integral
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]
/-- A normalized maximizing sequence whose extended functional limit lies
above a known finite level supplies (62). An infinite candidate limit is allowed. -/
theorem FunctionalInequalities.Probability.MomentMeasure.exists_integral_bound_of_tendsto_functional_above
    (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0)
    (φ : ℕ → E → EReal) (hnn : ∀ j x, 0 ≤ φ j x) (hφ0 : ∀ j, φ j 0 = 0)
    (hconv : ∀ j, ConvexPotential (φ j)) (hφ : ∀ j, PotentialIntegrable (φ j) μ)
    (L : EReal) (b : ℝ) (hb : (b : EReal) < L)
    (hlim : Tendsto (fun j => variationalFunctional dx μ (φ j)) atTop (𝓝 L)) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ j, (∫ x, (φ j x).toReal ∂μ) ≤ B) ∧
      (⨆ j, ∫⁻ x, (φ j x).toENNReal ∂μ) ≠ ⊤ := by
  apply exists_integral_bound_of_eventual_functional_lower_readable dx μ hsub hint hbar φ hnn hφ0 hconv hφ b
  exact (hlim.eventually (Ioi_mem_nhds hb)).mono fun _ h => h.le
end FiniteDimensional
end
end
end
end

noncomputable section
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- First extract an actual real-integral limit, then apply the actual full
Lemma17 to that same subsequence. Both limit inequalities and the composed
indices feed the independently rechecked actual extended-log limit helper. -/
theorem solution (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirstMoment : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ (S : ℝ) (ψ : E → EReal), FunctionalInequalities.Analysis.ConvexPotential ψ ∧ FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable ψ μ ∧
      (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧ 0 < FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre ψ) ∧ FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre ψ) ≠ ⊤ ∧
      (S : EReal) ≤ FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ ψ ∧
      ∀ η : E → EReal, FunctionalInequalities.Analysis.ConvexPotential η → FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable η μ →
        (∀ x, 0 ≤ η x) → η 0 = 0 → FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ η ≤ (S : EReal) := by
  obtain ⟨S, φ, hconv, hpot, hnn, hzero, hF, hsup⟩ :=
    FunctionalInequalities.KLS.CEK.exists_normalized_maximizing_sequence_readable dx μ hsub hfirstMoment hbar
  obtain ⟨B, _hB, hBphi, hbounded⟩ := FunctionalInequalities.Probability.MomentMeasure.exists_integral_bound_of_tendsto_functional_above
    dx μ hsub hfirstMoment hbar φ hnn hzero hconv hpot (S : EReal) (S - 1)
    (EReal.coe_lt_coe_iff.mpr (by linarith)) hF
  have hmnn : ∀ j, 0 ≤ ∫ x, (φ j x).toReal ∂μ :=
    fun j => (FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential (φ j) (hpot j) (hnn j)).2.2
  obtain ⟨M, _hM, t, ht, hmT⟩ := isCompact_Icc.tendsto_subseq
    (fun j => (show (∫ x, (φ j x).toReal ∂μ) ∈ Icc 0 B from ⟨hmnn j, hBphi j⟩))
  have hμ : μ ≠ 0 := by
    intro hz
    have hu : μ univ = 1 := measure_univ
    simp only [hz, Measure.coe_zero, Pi.zero_apply, zero_ne_one] at hu
  have h0 := FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero_readable
    μ hμ hsub hfirstMoment hbar
  have hboundedT : (⨆ j, ∫⁻ x, (φ (t j) x).toENNReal ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top hbounded (iSup_le fun j => le_iSup (fun k => ∫⁻ x, (φ k x).toENNReal ∂μ) (t j))
  obtain ⟨s, ψ, hs, hψnn, hψ0, hψconv, _hψmeas, _hpoint, _hrad, _hoff, hpψ, hZfin, hfirst, hsecond⟩ :=
    FunctionalInequalities.Probability.MomentMeasure.exists_subseq_integral_bounds_of_convex_epigraph_readable dx μ h0 (fun j => φ (t j))
      (fun j => hnn (t j)) (fun j => hzero (t j)) (fun j => (hconv (t j)).2)
      (fun j => (FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential (φ (t j)) (hpot (t j)) (hnn (t j))).1) hboundedT
  have hFts : Tendsto (fun j => FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ (φ (t (s j)))) atTop (𝓝 (S : EReal)) :=
    hF.comp (ht.tendsto_atTop.comp hs.tendsto_atTop)
  have hmts : Tendsto (fun j => ∫ x, (φ (t (s j)) x).toReal ∂μ) atTop (𝓝 M) :=
    hmT.comp hs.tendsto_atTop
  have hψlin := (FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential ψ hpψ hψnn).2.1
  have hseqlin (j : ℕ) :=
    (FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential (φ (t (s j))) (hpot (t (s j))) (hnn (t (s j)))).2.1
  have hfirstScalar : ENNReal.ofReal (∫ x, (ψ x).toReal ∂μ) ≤
      liminf (fun j => ENNReal.ofReal (∫ x, (φ (t (s j)) x).toReal ∂μ)) atTop := by
    simpa only [hψlin, hseqlin] using hfirst
  obtain ⟨hZpos, hvalue⟩ := FunctionalInequalities.Probability.MomentMeasure.log_sub_ge_of_integral_limits_readable
    (fun j => FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre (φ (t (s j)))))
    (fun j => ∫ x, (φ (t (s j)) x).toReal ∂μ) (FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre ψ))
    (∫ x, (ψ x).toReal ∂μ) S M (fun j => hmnn (t (s j))) hFts hmts hfirstScalar hsecond
  exact ⟨S, ψ, ⟨fun x => ne_of_gt (EReal.bot_lt_zero.trans_le (hψnn x)), hψconv⟩,
    hpψ, hψnn, hψ0, hZpos, hZfin, hvalue, hsup⟩
