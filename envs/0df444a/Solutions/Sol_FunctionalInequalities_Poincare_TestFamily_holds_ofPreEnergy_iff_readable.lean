-- Prove2me | solution 1 for FunctionalInequalities.Poincare.TestFamily.holds_ofPreEnergy_iff_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:40:10.271298+00:00
-- url     : https://prove2.me/submissions/21495bf9-fc21-4f98-a14d-6d6bf02972bb

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_Relaxation
import Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt_readable

section
noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
/-- The mean is continuous in the real `L²` topology. -/
theorem FunctionalInequalities.L2.continuous_mean (μ : ProbabilityMeasure α) : Continuous (mean μ) :=
  continuous_id.inner continuous_const
/-- Subtracting the mean is continuous in the real `L²` topology. -/
theorem FunctionalInequalities.L2.continuous_center (μ : ProbabilityMeasure α) : Continuous (center μ) := by
  apply (continuous_id.sub ((continuous_mean μ).smul continuous_const) :
    Continuous (fun f : Lp ℝ 2 (μ : Measure α) ↦ f - mean μ f • const μ 1)).congr
  intro f
  simp only [center, ← const_smul, mul_one]
  rfl
/-- Variance is continuous in `L²`, including at constant functions. -/
theorem FunctionalInequalities.L2.continuous_variance (μ : ProbabilityMeasure α) : Continuous (variance μ) :=
  (continuous_center μ).nnnorm.pow 2
end
end
end

section
section
variable {X : Type*}
/-- Coercing a finite energy back to `ENNReal` recovers the original value. -/
@[simp]
theorem FunctionalInequalities.Energy.Functional.coe_finiteValue (energy : Functional X) (x : energy.domain) :
    (energy.finiteValue x : ENNReal) = energy x.1 :=
  ENNReal.coe_toNNReal x.2
end
end

section
noncomputable section
open Filter Topology
section
universe u v
section
variable {X : Type u} [TopologicalSpace X] (P : FunctionalInequalities.Energy.PreEnergy X)
/-- Every particular approximating sequence gives an upper bound for the relaxed energy. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_sequenceEnergy {x : X} (f : P.ApproximatingSequence x) :
    P.sequentialRelaxation x ≤ P.sequenceEnergy f :=
  iInf_le _ f
/-- Relaxation never increases the energy of a concrete test. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_toAmbient_le (f : P.Test) :
    P.sequentialRelaxation (P.toAmbient f) ≤ (P.energy f : ENNReal) := by
  refine (P.sequentialRelaxation_le_sequenceEnergy (P.constantSequence f)).trans_eq ?_
  exact liminf_const (P.energy f : ENNReal)
/-- Every realized concrete test has finite relaxed energy. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_finiteAt_toAmbient (f : P.Test) :
    P.sequentialRelaxation.FiniteAt (P.toAmbient f) :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (P.sequentialRelaxation_toAmbient_le f)
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology
universe u
variable {α : Type u} [MeasurableSpace α] (μ : MeasureTheory.ProbabilityMeasure α)
  (P : FunctionalInequalities.Energy.PreEnergy (MeasureTheory.Lp ℝ 2 (μ : MeasureTheory.Measure α)))
/-- A finite constant works on concrete tests exactly when it works on the finite domain
of their sequential relaxation. Source: the local abstract Blueprint bridge described above. -/
theorem solution (C : NNReal) :
    (FunctionalInequalities.Poincare.TestFamily.ofPreEnergy μ P).Holds C ↔ FunctionalInequalities.Poincare.L2Energy.Holds μ P.sequentialRelaxation C := by
  constructor
  · intro h f
    obtain ⟨s, hs⟩ := P.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt_readable f.2
    have henergy : Tendsto (fun n ↦ P.energy (s.1 n)) atTop
        (𝓝 (P.sequentialRelaxation.finiteValue f)) := by
      simpa only [Function.comp_def, ENNReal.toNNReal_coe, FunctionalInequalities.Energy.Functional.finiteValue]
        using (ENNReal.tendsto_toNNReal f.2).comp hs
    exact le_of_tendsto_of_tendsto
      ((FunctionalInequalities.L2.continuous_variance μ).tendsto f.1 |>.comp s.2)
      (tendsto_const_nhds.mul henergy) (Eventually.of_forall fun n ↦ h (s.1 n))
  · intro h f
    let x : P.sequentialRelaxation.domain :=
      ⟨P.toAmbient f, P.sequentialRelaxation_finiteAt_toAmbient f⟩
    have henergy : P.sequentialRelaxation.finiteValue x ≤ P.energy f := by
      apply ENNReal.coe_le_coe.mp
      simpa only [FunctionalInequalities.Energy.Functional.coe_finiteValue] using
        P.sequentialRelaxation_toAmbient_le f
    exact (h x).trans (mul_le_mul le_rfl henergy zero_le zero_le)
