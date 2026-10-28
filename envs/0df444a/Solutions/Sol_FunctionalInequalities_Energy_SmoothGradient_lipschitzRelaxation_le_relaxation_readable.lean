-- Prove2me | solution 1 for FunctionalInequalities.Energy.SmoothGradient.lipschitzRelaxation_le_relaxation_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:04:58.953206+00:00
-- url     : https://prove2.me/submissions/595a88fb-9fdc-44c3-87f7-479fca4ac311

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LowerSemicontinuous
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Core
import Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_lowerSemicontinuous_sequentialRelaxation_readable
import Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_Test_exists_domain_sequence_tendsto_readable

section
noncomputable section
open MeasureTheory
section NormSquare
variable {V : Type*} [MeasurableSpace V]
/-- The `L²` norm squared of a square-integrable function is the integral of its squared norm. -/
theorem FunctionalInequalities.L2.norm_toLp_sq {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {μ : Measure V} {u : V → W} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]
end NormSquare
end
end

section
noncomputable section
open Filter Topology
section
universe u v
section
variable {X : Type u} [TopologicalSpace X] (P : FunctionalInequalities.Energy.PreEnergy X)
/-- The relaxed energy is the infimum of the `liminf` energies of all approximating sequences. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_apply (x : X) :
    P.sequentialRelaxation x = ⨅ f : P.ApproximatingSequence x, P.sequenceEnergy f :=
  rfl
/-- Every particular approximating sequence gives an upper bound for the relaxed energy. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_sequenceEnergy {x : X} (f : P.ApproximatingSequence x) :
    P.sequentialRelaxation x ≤ P.sequenceEnergy f :=
  iInf_le _ f
end
end
end
end

section
noncomputable section
open Filter Topology
section Maximality
variable {X : Type*} [TopologicalSpace X] (P : FunctionalInequalities.Energy.PreEnergy X)
/-- A lower-semicontinuous functional bounded by the concrete test energies is bounded by
their sequential relaxation. No density or finite-energy agreement is required. -/
theorem FunctionalInequalities.Energy.PreEnergy.le_sequentialRelaxation_of_lowerSemicontinuous
    (energy : Functional X) (hlsc : LowerSemicontinuous fun x ↦ energy x)
    (h : ∀ f : P.Test, energy (P.toAmbient f) ≤ (P.energy f : ENNReal)) (x : X) :
    energy x ≤ P.sequentialRelaxation x := by
  rw [P.sequentialRelaxation_apply]
  refine le_iInf fun s ↦ ?_
  have hlimit : energy x ≤ liminf (fun n ↦ energy (P.toAmbient (s.1 n))) atTop := by
    refine le_of_forall_lt fun c hc ↦ ?_
    obtain ⟨d, hcd, hd⟩ := exists_between hc
    have heventually := s.2.eventually (hlsc x d hd)
    exact hcd.trans_le (le_liminf_of_le (by isBoundedDefault)
      (heventually.mono fun _ hn ↦ hn.le))
  exact hlimit.trans (liminf_le_liminf (Eventually.of_forall fun n ↦ h (s.1 n)))
end Maximality
section Comparison
variable {X : Type*} [PseudoMetricSpace X] (P Q : FunctionalInequalities.Energy.PreEnergy X)
/-- Approximating each `P`-test by `Q`-tests at no greater limiting energy compares the two
relaxations. The hypothesis allows different test types and nonattained raw minima.

Both pre-energies use the same pseudometric ambient space, where the target relaxation is
lower semicontinuous. If each source test instead has a single exact target realization under
a continuous map, `PreEnergy.sequentialRelaxation_comp_le` applies even between different
topological spaces, without a pseudometric hypothesis.
-/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_of_recovery_sequences
    (h : ∀ f : P.Test, ∃ s : Q.ApproximatingSequence (P.toAmbient f),
      Q.sequenceEnergy s ≤ (P.energy f : ENNReal)) (x : X) :
    Q.sequentialRelaxation x ≤ P.sequentialRelaxation x := by
  apply P.le_sequentialRelaxation_of_lowerSemicontinuous Q.sequentialRelaxation
    Q.lowerSemicontinuous_sequentialRelaxation_readable
  intro f
  obtain ⟨s, hs⟩ := h f
  exact (Q.sequentialRelaxation_le_sequenceEnergy s).trans hs
end Comparison
end
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section Agreement
variable (ν : MeasureTheory.ProbabilityMeasure V) (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (D : FunctionalInequalities.Energy.SmoothGradient.LocalDensity ν m)
open FunctionalInequalities.Energy.WeightedGradient FunctionalInequalities.Energy.Euclidean
omit [FiniteDimensional ℝ V] in
/-- The raw energy of a smooth test is the squared `L²` norm of its gradient class. -/
theorem FunctionalInequalities.Energy.SmoothGradient.Test.coe_energy_eq_norm_toLp_sq (f : Test ν) :
    (f.energy : ℝ) = ‖(Test.memLp_gradient ν f).toLp (gradient f.toFun)‖ ^ 2 := by
  rw [Test.coe_energy, L2.norm_toLp_sq]
omit [FiniteDimensional ℝ V] in
/-- The raw energy of a smooth test, in `ENNReal`, is the squared `NNReal` norm of its gradient
class. -/
theorem FunctionalInequalities.Energy.SmoothGradient.Test.energy_eq_nnnorm_sq (f : Test ν) :
    (f.energy : ENNReal) =
      ((‖(Test.memLp_gradient ν f).toLp (gradient f.toFun)‖₊ ^ 2 : ℝ≥0) : ENNReal) := by
  apply ENNReal.coe_inj.mpr
  apply NNReal.eq
  push_cast
  exact Test.coe_energy_eq_norm_toLp_sq ν f
/-- The Lipschitz-gradient relaxation is at most the smooth-gradient relaxation: smooth cutoffs are
recovery sequences for smooth tests. -/
theorem solution (x : Lp ℝ 2 (ν : Measure V)) :
    (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap (FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D)).sequentialRelaxation x ≤ FunctionalInequalities.Energy.SmoothGradient.relaxation ν x := by
  refine FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_of_recovery_sequences (FunctionalInequalities.Energy.SmoothGradient.preEnergy ν)
    (FunctionalInequalities.Energy.PreEnergy.ofLinearPMap (FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D)) (fun f ↦ ?_) x
  obtain ⟨p, hp⟩ := FunctionalInequalities.Energy.SmoothGradient.Test.exists_domain_sequence_tendsto_readable ν m D f
  have h1 : Tendsto (fun j ↦ ((p j : (FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D).domain) : Lp ℝ 2 (ν : Measure V)))
      atTop (𝓝 f.toL2) := (continuous_fst.tendsto _).comp hp
  have h2 : Tendsto (fun j ↦ FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D (p j)) atTop
      (𝓝 ((FunctionalInequalities.Energy.SmoothGradient.Test.memLp_gradient ν f).toLp (gradient f.toFun))) := (continuous_snd.tendsto _).comp hp
  refine ⟨⟨p, h1⟩, le_of_eq ?_⟩
  change liminf (fun j ↦ (((‖FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D (p j)‖₊ ^ 2 : ℝ≥0)) : ENNReal)) atTop =
    (f.energy : ENNReal)
  have h3 : Tendsto (fun j ↦ (((‖FunctionalInequalities.Energy.SmoothGradient.lipschitzOperator ν m D (p j)‖₊ ^ 2 : ℝ≥0)) : ENNReal)) atTop
      (𝓝 (((‖(FunctionalInequalities.Energy.SmoothGradient.Test.memLp_gradient ν f).toLp (gradient f.toFun)‖₊ ^ 2 : ℝ≥0)) : ENNReal)) := by
    apply ENNReal.tendsto_coe.mpr
    exact ((continuous_nnnorm.tendsto _).comp h2).pow 2
  rw [h3.liminf_eq]
  exact (FunctionalInequalities.Energy.SmoothGradient.Test.energy_eq_nnnorm_sq ν f).symm
