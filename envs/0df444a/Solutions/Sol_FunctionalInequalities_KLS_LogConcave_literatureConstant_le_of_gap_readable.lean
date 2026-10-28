-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.literatureConstant_le_of_gap_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:43:21.180342+00:00
-- url     : https://prove2.me/submissions/a3f4fb00-108d-45ec-965a-644bd8f8b156

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_AbsoluteContinuity
import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LinearPMap
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_LocalSlope_Gradient
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_LowerSemicontinuous
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothGradient_Ambient
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothGradient_Comparison
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Comparison
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LocalSlope_SmoothTestComparison
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Poincare
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Cheeger_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Density
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Cheeger_Identification
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Energy
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Poincare
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_admissible_iff_memLp_gradient_readable
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_apply_eq_norm_gradient_readable
import Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_lowerSemicontinuous_sequentialRelaxation_readable
import Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_sequentialRelaxation_ofLinearPMap_of_mem_readable
import Theorems.Thm_FunctionalInequalities_Energy_PreEnergy_sequentialRelaxation_ofLinearPMap_of_notMem_readable
import Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_Test_exists_ambient_extension_readable
import Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_lipschitzRelaxation_le_relaxation_readable
import Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_relaxation_eq_intrinsic_energy_readable
import Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_relaxation_le_localSlope_of_admissible_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_smoothGradient_localDensity_readable
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_iff_localSlope_readable
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_iff_preEnergy_readable
import Theorems.Thm_FunctionalInequalities_Poincare_TestFamily_holds_ofPreEnergy_iff_readable
import Theorems.Thm_FunctionalInequalities_Probability_affineSupport_intrinsicMeasure_readable

section
noncomputable section
open MeasureTheory Set Topology
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
omit [CompleteSpace E] in
/-- Log-concavity is retained on the direction of the affine support, even for singular
ambient laws and a zero-dimensional carrier. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsicMeasure {μ : ProbabilityMeasure E} (hμ : LogConcave μ) :
    LogConcave (Probability.intrinsicMeasure μ) :=
  hμ.of_affineIsometry_map (Probability.intrinsicMeasure μ) (Probability.reconstruct μ)
    (Probability.measurePreserving_reconstruct μ).map_eq
omit [CompleteSpace E] in
/-- The intrinsic support has nonempty interior. This includes the singleton topology in
dimension zero and does not assert that the boundary has zero probability mass. -/
theorem FunctionalInequalities.KLS.LogConcave.interior_intrinsic_support_nonempty {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) :
    (interior (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support).Nonempty := by
  apply hμ.intrinsicMeasure.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr
  exact Probability.affineSupport_intrinsicMeasure_readable μ
end
end
end

section
noncomputable section
open MeasureTheory Filter Metric Set Topology
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
section Intrinsic
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [FiniteDimensional ℝ F]
omit [CompleteSpace F] in
/-- Every compact-set log-concave probability law is absolutely continuous in its own affine
support coordinates. Singular ambient measures and the zero-dimensional support are included. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsic_absolutelyContinuous {μ : ProbabilityMeasure F}
    (hμ : LogConcave μ) (m : Measure (Probability.affineSupport μ).direction)
    [m.IsAddHaarMeasure] :
    (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m :=
  hμ.intrinsicMeasure.absolutelyContinuous_of_interior_support_nonempty m
    hμ.interior_intrinsic_support_nonempty
end Intrinsic
end
end
end

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
section
variable {X : Type*}
/-- Extended energy functionals are equal when all of their values are equal. -/
@[ext]
theorem FunctionalInequalities.Energy.Functional.ext {left right : Functional X} (h : ∀ x, left x = right x) : left = right := by
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      congr
      funext x
      exact h x
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
/-- The relaxed energy is the infimum of the `liminf` energies of all approximating sequences. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_apply (x : X) :
    P.sequentialRelaxation x = ⨅ f : P.ApproximatingSequence x, P.sequenceEnergy f :=
  rfl
/-- Every particular approximating sequence gives an upper bound for the relaxed energy. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_le_sequenceEnergy {x : X} (f : P.ApproximatingSequence x) :
    P.sequentialRelaxation x ≤ P.sequenceEnergy f :=
  iInf_le _ f
/-- A continuous map with energy-nonincreasing lifts on concrete tests has the same bound
after relaxation. Neither test class needs to be nonempty or densely realized.

Each source test must have one target test realizing its image exactly. For comparison by
approximating sequences in a common pseudometric space, see
`PreEnergy.sequentialRelaxation_le_of_recovery_sequences` in
`FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous`. The present result only needs
topological ambient spaces and also allows a map between different spaces.
-/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_comp_le {Y : Type*} [TopologicalSpace Y]
    (Q : PreEnergy Y) (T : X → Y) (hT : Continuous T)
    (h : ∀ f : P.Test, ∃ g : Q.Test,
      Q.toAmbient g = T (P.toAmbient f) ∧ Q.energy g ≤ P.energy f) (x : X) :
    Q.sequentialRelaxation (T x) ≤ P.sequentialRelaxation x := by
  rw [P.sequentialRelaxation_apply]
  refine le_iInf fun s ↦ ?_
  choose g hreal henergy using fun n ↦ h (s.1 n)
  have hconv : Tendsto (fun n ↦ Q.toAmbient (g n)) atTop (𝓝 (T x)) := by
    simpa only [hreal, Function.comp_def] using (hT.tendsto x).comp s.2
  exact (Q.sequentialRelaxation_le_sequenceEnergy ⟨g, hconv⟩).trans
    (liminf_le_liminf (Eventually.of_forall fun n ↦ ENNReal.coe_le_coe.mpr (henergy n)))
end
end
end
end

section
noncomputable section
section
universe u
section
/-- The extended Rayleigh quotient is bounded by a finite `C` exactly when the defining
inequality holds. This includes zero-energy tests, whose quotient may be infinite. -/
theorem FunctionalInequalities.Poincare.TestFamily.rayleigh_le_iff (F : TestFamily) (f : F.Test) (C : NNReal) :
    rayleigh F f ≤ (C : ENNReal) ↔ F.variance f ≤ C * F.energy f := by
  rw [rayleigh, ENNReal.div_le_iff_le_mul
    (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top), ← ENNReal.coe_mul,
    ENNReal.coe_le_coe]
/-- A finite constant is valid exactly when it bounds the optimal extended constant. -/
theorem FunctionalInequalities.Poincare.TestFamily.holds_iff_constant_le (F : TestFamily) (C : NNReal) :
    Holds F C ↔ constant F ≤ (C : ENNReal) := by
  rw [constant, iSup_le_iff]
  exact forall_congr' fun f ↦ (rayleigh_le_iff F f C).symm
end
end
end
end

section
noncomputable section
open MeasureTheory
section
universe u
variable {α : Type u} [MeasurableSpace α]
section
/-- Unfolding validity gives the Poincaré inequality on the finite-energy domain. -/
theorem FunctionalInequalities.Poincare.L2Energy.holds_iff (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) :
    Holds μ energy C ↔
      ∀ f : energy.domain, L2.variance μ f.1 ≤ C * energy.finiteValue f :=
  Iff.rfl
/-- A finite `L²` Poincaré constant is valid exactly when it bounds the optimal one. -/
theorem FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le (μ : ProbabilityMeasure α)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α))) (C : NNReal) :
    Holds μ energy C ↔ constant μ energy ≤ (C : ENNReal) := by
  simpa [Holds, constant] using
    TestFamily.holds_iff_constant_le (TestFamily.ofL2Energy μ energy) C
end
end
end
end

section
noncomputable section
open Filter Topology Set
section PreEnergy
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
section
variable (T : X →ₗ.[ℝ] H)
section NormedSpace
variable {H' : Type*}
variable [NormedAddCommGroup H'] [NormedSpace ℝ H']
open Classical in
omit [CompleteSpace H] in
theorem FunctionalInequalities.Energy.PreEnergy.normSqEnergy_of_mem
    (S : X →ₗ.[ℝ] H') (x : S.domain) :
    normSqEnergy S x = ((‖S x‖₊ ^ 2 : NNReal) : ENNReal) := by
  change (if h : (x : X) ∈ S.domain then ((‖S ⟨x, h⟩‖₊ ^ 2 : NNReal) : ENNReal) else ⊤) = _
  rw [dif_pos x.2]
open Classical in
omit [CompleteSpace H] in
theorem FunctionalInequalities.Energy.PreEnergy.normSqEnergy_of_notMem
    (S : X →ₗ.[ℝ] H') {x : X} (hx : x ∉ S.domain) : normSqEnergy S x = ⊤ := by
  change (if h : x ∈ S.domain then ((‖S ⟨x, h⟩‖₊ ^ 2 : NNReal) : ENNReal) else ⊤) = _
  rw [dif_neg hx]
end NormedSpace
/-- The sequential relaxation of `‖T f‖²` is the squared-norm energy of the closure of `T`:
the graph-closed form, in the language of the pinned CMH source. -/
theorem FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_eq_normSqEnergy (hT : T.IsClosable) :
    (ofLinearPMap T).sequentialRelaxation = normSqEnergy T.closure := by
  ext x
  by_cases hx : x ∈ T.closure.domain
  · rw [sequentialRelaxation_ofLinearPMap_of_mem_readable T hT ⟨x, hx⟩, normSqEnergy_of_mem _ ⟨x, hx⟩]
  · rw [sequentialRelaxation_ofLinearPMap_of_notMem_readable T hT hx, normSqEnergy_of_notMem _ hx]
end
end PreEnergy
end
end

section
noncomputable section
open MeasureTheory Filter Topology
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [sct : SecondCountableTopology E]
  [FiniteDimensional ℝ E] (ν : MeasureTheory.ProbabilityMeasure E) (m : MeasureTheory.Measure E)
  [MeasureTheory.Measure.IsAddHaarMeasure m]
omit sct in
/-- Step 2: Rademacher and absolute continuity identify the two pointwise energies almost
everywhere for locally Lipschitz tests, with no integrability or density lower bound premise. -/
theorem FunctionalInequalities.Energy.LocalSlope.apply_ae_eq_norm_gradient (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    (fun x ↦ apply f x) =ᵐ[(ν : Measure E)]
      (fun x ↦ ENNReal.ofReal ‖gradient f x‖) := by
  filter_upwards [hν.ae_le
    (Energy.Euclidean.LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz hf m)]
    with x hx
  exact apply_eq_norm_gradient_readable f x hx
omit sct in
/-- Step 3: equality of the extended local-slope and gradient energies, also when infinite.
The lintegral keeps nonintegrable functions from acquiring a spurious zero energy. -/
theorem FunctionalInequalities.Energy.LocalSlope.energy_eq_lintegral_gradient (hν : (ν : Measure E) ≪ m)
    (f : E → ℝ) (hf : LocallyLipschitz f) :
    energy ν f = ∫⁻ x, (ENNReal.ofReal ‖gradient f x‖) ^ 2 ∂(ν : Measure E) := by
  unfold energy
  apply lintegral_congr_ae
  filter_upwards [apply_ae_eq_norm_gradient ν m hν f hf] with x hx
  rw [hx]
section RealIntegral
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  (ν : MeasureTheory.ProbabilityMeasure V) (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
/-- The literature energy of a locally Lipschitz function with square-integrable gradient is the
real integral of the squared gradient norm, under absolute continuity. -/
theorem FunctionalInequalities.Energy.LocalSlope.energy_eq_integral_gradient
    (hac : (ν : Measure V) ≪ m) (f : V → ℝ) (hf : LocallyLipschitz f)
    (hg : MemLp (gradient f) 2 (ν : Measure V)) :
    energy ν f = ENNReal.ofReal (∫ x, ‖gradient f x‖ ^ 2 ∂(ν : Measure V)) := by
  rw [energy_eq_lintegral_gradient ν m hac f hf,
    ofReal_integral_eq_lintegral_ofReal ((memLp_two_iff_integrable_sq_norm hg.1).mp hg)
      (ae_of_all _ fun x ↦ sq_nonneg ‖gradient f x‖)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
end RealIntegral
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E]
/-- Source: local order consequence of `constant` and Mathlib's `iInf_le_of_le`.
Every finite valid constant bounds the optimal constant from above. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_le {μ : Measure E} {C : NNReal}
    (hC : Holds μ (C : ℝ)) :
    constant μ ≤ (C : ENNReal) := by
  exact iInf_le_of_le ⟨C, hC⟩ le_rfl
/-- Source: local order consequence of `constant` and Mathlib's `le_iInf`.
A lower bound for every finite valid constant bounds the optimal constant from below. -/
theorem FunctionalInequalities.Poincare.SmoothTest.le_constant {μ : Measure E} {L : ENNReal}
    (hL : ∀ C : NNReal, Holds μ (C : ℝ) → L ≤ (C : ENNReal)) :
    L ≤ constant μ := by
  refine le_iInf fun C ↦ ?_
  exact hL C.1 C.2
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff
section
open FunctionalInequalities.Energy.Euclidean
universe u
private theorem FunctionalInequalities.Energy.SmoothGradient.pullbackTest_energy_le
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [MeasurableSpace Y]
    {μ : ProbabilityMeasure X} {ν : ProbabilityMeasure Y} (f : Test ν)
    (φ : X → Y) (hφ : ContDiff ℝ ∞ φ) (hlip : LipschitzWith 1 φ)
    (hmp : MeasurePreserving φ (μ : Measure X) (ν : Measure Y)) :
    (FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ hlip hmp).energy ≤ f.energy := by
  apply NNReal.coe_le_coe.mp
  calc
    _ ≤ ∫ x, ‖gradient f (φ x)‖ ^ 2 ∂(μ : Measure X) := by
      apply integral_mono (FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ hlip hmp).gradient_sq_integrable
        (hmp.integrable_comp_of_integrable f.gradient_sq_integrable)
      intro x
      exact pow_le_pow_left₀ (norm_nonneg _) (FunctionalInequalities.Energy.SmoothGradient.norm_gradient_comp_le f.contDiff hφ hlip x) 2
    _ = _ := by
      have h := integral_map hmp.measurable.aemeasurable
        (hmp.map_eq.symm ▸ f.gradient_sq_integrable.aestronglyMeasurable)
      simpa only [hmp.map_eq, Test.coe_energy] using h.symm
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : MeasureTheory.ProbabilityMeasure E)
section
/-- Restriction has the expected `L²` realization and does not increase raw energy.
Source: the tangential-gradient projection argument in the local Blueprint comparison. -/
theorem FunctionalInequalities.Energy.SmoothGradient.Test.exists_intrinsic_restriction (f : Energy.SmoothGradient.Test μ) :
    ∃ g : Energy.SmoothGradient.Test (Probability.intrinsicMeasure μ),
      (∀ v, g v = f (Probability.reconstruct μ v)) ∧
      g.toL2 = toIntrinsicL2 μ f.toL2 ∧ g.energy ≤ f.energy := by
  let φ := Probability.reconstruct μ
  have hφ : ContDiff ℝ ∞ φ := φ.toContinuousAffineMap.contDiff
  let g := FunctionalInequalities.Energy.SmoothGradient.pullbackTest f φ hφ φ.isometry.lipschitz
    (Probability.measurePreserving_reconstruct μ)
  exact ⟨g, fun _ ↦ rfl, rfl,
    pullbackTest_energy_le f φ hφ φ.isometry.lipschitz
      (Probability.measurePreserving_reconstruct μ)⟩
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
end
end

section
noncomputable section
open MeasureTheory
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]
/-- A finite constant is valid for the smooth-gradient relaxation exactly when it bounds its
optimal extended constant. -/
theorem FunctionalInequalities.Poincare.SmoothGradient.Ambient.holds_iff_constant_le (μ : ProbabilityMeasure E)
    [FiniteDimensional ℝ E] [BorelSpace E] [SecondCountableTopology E] (C : NNReal) :
    Holds μ C ↔
      constant μ ≤ (C : ENNReal) := by
  exact L2Energy.holds_iff_constant_le μ (Energy.SmoothGradient.relaxation μ) C
end
end
end

section
noncomputable section
open MeasureTheory
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : MeasureTheory.ProbabilityMeasure E)
/-- The ambient and selected optima agree in `ENNReal`, with no finiteness assumption.
Source: Blueprint `cor:ambient-intrinsic-constant-equality`. -/
theorem FunctionalInequalities.Poincare.SmoothGradient.Ambient.constant_eq_intrinsic :
    constant μ = Poincare.SmoothGradient.Intrinsic.constant μ := by
  unfold constant Poincare.SmoothGradient.Intrinsic.constant
  rw [Energy.SmoothGradient.relaxation_eq_intrinsic_energy_readable]
end
end
end

section
noncomputable section
open MeasureTheory
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : MeasureTheory.ProbabilityMeasure E)
/-- Smooth-test and ambient relaxed inequalities have the same valid finite constants.
Source: Blueprint `thm:legacy-relaxed-holds-equivalence` and the abstract pre-energy bridge. -/
theorem FunctionalInequalities.Poincare.SmoothTest.holds_iff_ambient (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔ Poincare.SmoothGradient.Ambient.Holds μ C := by
  exact (holds_iff_preEnergy_readable μ C).trans
    (TestFamily.holds_ofPreEnergy_iff_readable μ (Energy.SmoothGradient.preEnergy μ) C)
/-- The smooth-test infimum equals the ambient relaxed Rayleigh supremum, also at infinity.
Source: equality of the sets of valid finite constants; no attainment assumption is needed. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_eq_ambient :
    constant (μ : Measure E) = Poincare.SmoothGradient.Ambient.constant μ := by
  apply le_antisymm
  · by_cases h : Poincare.SmoothGradient.Ambient.constant μ = ⊤
    · simp [h]
    · have hcoe := ENNReal.coe_toNNReal h
      have hbound := (Poincare.SmoothGradient.Ambient.holds_iff_constant_le μ _).mpr hcoe.ge
      exact (constant_le ((holds_iff_ambient μ _).mpr hbound)).trans hcoe.le
  · apply le_constant
    intro C hC
    exact (Poincare.SmoothGradient.Ambient.holds_iff_constant_le μ C).mp
      ((holds_iff_ambient μ C).mp hC)
/-- The smooth-test and intrinsic smooth-gradient extended optima agree for every finite-dimensional law.
Source: Blueprint `thm:legacy-canonical-constant-comparison`; literature equivalence is separate. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsic :
    constant (μ : Measure E) = Poincare.SmoothGradient.Intrinsic.constant μ := by
  exact (constant_eq_ambient μ).trans
    (Poincare.SmoothGradient.Ambient.constant_eq_intrinsic μ)
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
/-- Step 6: equality of the infima of valid finite constants on this same coordinate space.
The subtype infimum is the existing Poincare.LocalSlope.Holds definition, without a second intrinsic map. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_eq_localSlope_infimum (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure E) ≪ m) :
    constant (ν : Measure E) =
      ⨅ C : {C : NNReal // Poincare.LocalSlope.Holds ν C}, (C.1 : ENNReal) := by
  apply le_antisymm
  · refine le_iInf fun C => ?_
    exact constant_le ((holds_iff_localSlope_readable ν m hν C.1).mpr C.2)
  · apply le_constant
    intro C hC
    exact iInf_le_of_le ⟨C, (holds_iff_localSlope_readable ν m hν C).mp hC⟩ le_rfl
/-- Smooth inequalities transport between the ambient law and its intrinsic law without
absolute continuity. Restriction decreases energy, while normal-constant extension preserves it. -/
private theorem FunctionalInequalities.Poincare.SmoothTest.holds_iff_intrinsicMeasure (μ : ProbabilityMeasure E) (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔
      Holds (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) (C : ℝ) := by
  let ν := Probability.intrinsicMeasure μ
  have hvar (f : Energy.SmoothGradient.Test μ)
      (g : Energy.SmoothGradient.Test ν)
      (heq : ∀ v, g v = f (Probability.reconstruct μ v)) :
      ProbabilityTheory.variance g.toFun (ν : Measure (Probability.affineSupport μ).direction) =
        ProbabilityTheory.variance f.toFun (μ : Measure E) := by
    calc
      _ = ProbabilityTheory.variance (fun v => f (Probability.reconstruct μ v))
          (ν : Measure (Probability.affineSupport μ).direction) :=
        congrArg (fun k => ProbabilityTheory.variance k (ν : Measure _)) (funext heq)
      _ = _ := (Probability.measurePreserving_reconstruct μ).variance_fun_comp
        f.contDiff.continuous.aemeasurable
  constructor
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro g hg
    let gt : Energy.SmoothGradient.Test ν :=
      ⟨g, hg.smooth', hg.memLp_two, hg.energy_integrable⟩
    obtain ⟨f, heq, _, henergy⟩ :=
      Energy.SmoothGradient.Test.exists_ambient_extension_readable μ gt
    have he : energy (μ : Measure E) f.toFun = energy (ν : Measure _) gt.toFun :=
      congrArg (fun c : NNReal => (c : ℝ)) henergy
    change ProbabilityTheory.variance gt.toFun (ν : Measure _) ≤ C * energy (ν : Measure _) gt.toFun
    rw [hvar f gt (fun v => (heq v).symm), ← he]
    exact h.variance_le ⟨f.contDiff, f.memLp_two, f.gradient_sq_integrable⟩
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro f hf
    let ft : Energy.SmoothGradient.Test μ :=
      ⟨f, hf.smooth', hf.memLp_two, hf.energy_integrable⟩
    obtain ⟨g, heq, _, henergy⟩ :=
      Energy.SmoothGradient.Test.exists_intrinsic_restriction μ ft
    have he : energy (ν : Measure _) g.toFun ≤ energy (μ : Measure E) ft.toFun :=
      NNReal.coe_le_coe.mpr henergy
    have hb := h.variance_le ⟨g.contDiff, g.memLp_two, g.gradient_sq_integrable⟩
    change ProbabilityTheory.variance ft.toFun (μ : Measure E) ≤ C * energy (μ : Measure E) ft.toFun
    rw [← hvar ft g heq]
    exact hb.trans (mul_le_mul_of_nonneg_left he C.2)
/-- Step 7: the exact ambient / intrinsic / literature chain from the Blueprint theorem.
Use the proved smooth-test restriction and normal-constant extension for the first equality.
The Haar reference lives on the direction of the affine support; zero dimension is included. -/
theorem FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope (μ : ProbabilityMeasure E)
    (m : Measure (Probability.affineSupport μ).direction) [Measure.IsAddHaarMeasure m]
    (hμ : (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m) :
    constant (μ : Measure E) =
        constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ∧
      constant (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) =
        Poincare.LocalSlope.Intrinsic.constant μ := by
  constructor
  · apply le_antisymm
    · apply le_constant
      intro C hC
      exact constant_le ((holds_iff_intrinsicMeasure μ C).mpr hC)
    · apply le_constant
      intro C hC
      exact constant_le ((holds_iff_intrinsicMeasure μ C).mp hC)
  · exact constant_eq_localSlope_infimum (Probability.intrinsicMeasure μ) m hμ
end
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
/-- Step 8: connect the selected constant to the literature frontend under the same explicit
intrinsic absolute-continuity premise. `KLS.LogConcave.Poincare` derives this premise for every
compact-set log-concave law. -/
theorem FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.constant_eq_localSlope
    (μ : ProbabilityMeasure E) (m : Measure (Probability.affineSupport μ).direction)
    [Measure.IsAddHaarMeasure m]
    (hμ : (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m) :
    constant μ = Poincare.LocalSlope.Intrinsic.constant μ := by
  rw [← Poincare.SmoothTest.constant_eq_intrinsic μ]
  exact (Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope μ m hμ).1.trans
    (Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope μ m hμ).2
end
end
end

section
noncomputable section
open MeasureTheory
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
/-- The selected intrinsic-affine relaxed constant agrees with the literature constant for
all finite-dimensional log-concave probability laws, including singular and Dirac laws. -/
theorem FunctionalInequalities.KLS.LogConcave.intrinsicSmooth_constant_eq_localSlope
    {μ : ProbabilityMeasure E} (hμ : KLS.LogConcave μ) :
    Poincare.SmoothGradient.Intrinsic.constant μ = Poincare.LocalSlope.Intrinsic.constant μ :=
  Poincare.SmoothGradient.Intrinsic.constant_eq_localSlope μ Measure.addHaar
    (hμ.intrinsic_absolutelyContinuous Measure.addHaar)
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
section
universe u
section
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The pre-energy of a local-slope test is its squared local-slope integral. -/
theorem FunctionalInequalities.Energy.LocalSlope.coe_preEnergy_energy (ν : ProbabilityMeasure V) (f : {f : V → ℝ // Admissible ν f}) :
    ((preEnergy ν).energy f : ℝ≥0∞) = energy ν f.1 :=
  ENNReal.coe_toNNReal f.2.finite_energy
omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The relaxation is the largest lower-semicontinuous functional below the raw slope energy
on admissible tests: together with `lowerSemicontinuous_relaxation` and `relaxation_toLp_le`
this characterizes it as the lower-semicontinuous envelope. -/
theorem FunctionalInequalities.Energy.LocalSlope.le_relaxation_of_lowerSemicontinuous (ν : ProbabilityMeasure V)
    (Q : Functional (Lp ℝ 2 (ν : Measure V)))
    (hlsc : LowerSemicontinuous (fun f ↦ Q f))
    (hQ : ∀ (f : V → ℝ) (hf : Admissible ν f), Q (hf.memLp_two.toLp f) ≤ energy ν f)
    (g : Lp ℝ 2 (ν : Measure V)) :
    Q g ≤ relaxation ν g := by
  apply (preEnergy ν).le_sequentialRelaxation_of_lowerSemicontinuous Q hlsc
  rintro ⟨f, hf⟩
  rw [coe_preEnergy_energy]
  exact hQ f hf
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
section
universe u
section
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section
variable {ν : MeasureTheory.ProbabilityMeasure V}
omit [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The pointwise local slope of a smooth test is the gradient norm, everywhere: no measure or
absolute-continuity hypothesis is needed since `ContDiff` gives differentiability at every
point. -/
private theorem FunctionalInequalities.Energy.SmoothGradient.Test.apply_toFun_eq_norm_gradient (f : Test ν) (x : V) :
    LocalSlope.apply f.toFun x = ENNReal.ofReal ‖gradient f.toFun x‖ :=
  LocalSlope.apply_eq_norm_gradient_readable f.toFun x (f.contDiff.differentiable (by simp) x)
omit [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The squared local-slope energy of a smooth test equals its smooth-gradient energy. -/
private theorem FunctionalInequalities.Energy.SmoothGradient.Test.localSlope_energy_eq_coe_energy (f : Test ν) :
    LocalSlope.energy ν f.toFun = (f.energy : ℝ≥0∞) := by
  have step1 : LocalSlope.energy ν f.toFun =
      ∫⁻ x, ENNReal.ofReal (‖gradient f.toFun x‖ ^ 2) ∂(ν : Measure V) := by
    unfold LocalSlope.energy
    refine lintegral_congr fun x ↦ ?_
    rw [apply_toFun_eq_norm_gradient f x, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [step1, ← ofReal_integral_eq_lintegral_ofReal f.gradient_sq_integrable
    (ae_of_all _ fun x ↦ sq_nonneg _), ← Test.coe_energy, ENNReal.ofReal_coe_nnreal]
omit [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- A smooth-gradient test is a local-slope test: it is locally Lipschitz, in `L²(ν)`, and its
local slope is the gradient norm at every point, with square-integrable gradient. -/
theorem FunctionalInequalities.Energy.SmoothGradient.Test.localSlope_admissible (f : Test ν) : LocalSlope.Admissible ν f :=
  ⟨(f.contDiff.of_le (by exact_mod_cast le_top)).locallyLipschitz, f.memLp_two, by
    rw [localSlope_energy_eq_coe_energy f]; exact ENNReal.coe_ne_top⟩
omit [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The squared local-slope energy of a smooth test is its smooth-gradient energy.  No
absolute-continuity hypothesis: the slope equals the gradient norm at every point. -/
theorem FunctionalInequalities.Energy.SmoothGradient.Test.localSlope_energy (f : Test ν) :
    LocalSlope.energy ν f = (f.energy : ℝ≥0∞) :=
  localSlope_energy_eq_coe_energy f
end
/-- Unconditional direction: relaxing over the larger local-slope test class gives at most the
smooth-gradient relaxation.  Holds for every law, singular laws included. -/
theorem FunctionalInequalities.Energy.SmoothGradient.localSlope_relaxation_le (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)) :
    LocalSlope.relaxation ν f ≤ relaxation ν f := by
  have h := (preEnergy ν).sequentialRelaxation_comp_le (LocalSlope.preEnergy ν) id continuous_id
    (fun g ↦ ⟨⟨g.toFun, Test.localSlope_admissible g⟩, rfl, by
      show (LocalSlope.energy ν g.toFun).toNNReal ≤ g.energy
      rw [Test.localSlope_energy g, ENNReal.toNNReal_coe]⟩) f
  exact h
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
section
universe u
section General
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section
/-- `C6`.  The reverse inequality between the two relaxations, for every law: smooth tests are
dense in the local-slope energy, so the smooth-gradient relaxation does not exceed the
local-slope relaxation. -/
theorem FunctionalInequalities.Energy.SmoothGradient.relaxation_le_localSlope (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)) :
    relaxation ν f ≤ LocalSlope.relaxation ν f :=
  LocalSlope.le_relaxation_of_lowerSemicontinuous ν (relaxation ν)
    (preEnergy ν).lowerSemicontinuous_sequentialRelaxation_readable
    (fun _g hgadm ↦ relaxation_le_localSlope_of_admissible_readable ν hgadm) f
end
end General
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
section
universe u
section
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- The smooth-gradient relaxation is the relaxed squared local slope, for every Borel
probability law on a finite-dimensional inner-product space: `≤` is the density of smooth tests in
the local-slope energy (`SlopeDensity`), `≥` is `localSlope_relaxation_le`. -/
theorem FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_localSlope (ν : ProbabilityMeasure V) :
    relaxation ν = LocalSlope.relaxation ν :=
  Functional.ext fun f => le_antisymm (relaxation_le_localSlope ν f) (localSlope_relaxation_le ν f)
end
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
section
open FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean FunctionalInequalities.Probability
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
section FullDimensional
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
/-- The local-slope relaxation is bounded by the unit-weight operator relaxation.  This is the
easy inclusion of globally Lipschitz operator tests into the literature local-slope test class. -/
private theorem FunctionalInequalities.KLS.LogConcave.localSlope_relaxation_le_weightedRelaxation (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty)
    (x : Lp ℝ 2 (ν : Measure V)) :
    Energy.LocalSlope.relaxation ν x ≤
      (PreEnergy.ofLinearPMap
        (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi)).sequentialRelaxation x := by
  let hac : (ν : Measure V) ≪ m := hν.absolutelyContinuous_haar m hi
  refine (PreEnergy.ofLinearPMap
      (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi)).sequentialRelaxation_comp_le
    (Energy.LocalSlope.preEnergy ν) id continuous_id ?_ x
  rintro ⟨f, hf⟩
  obtain ⟨g, hg, hfg⟩ :=
    (Energy.WeightedGradient.mem_domain_operator_iff ν
      (ContinuousLinearMap.id ℝ V) hac f).mp hf
  obtain ⟨K, hK⟩ := hg.1
  have hgrad : MemLp (gradient g) 2 (ν : Measure V) := by
    simpa only [Energy.WeightedGradient.apply_id] using hg.memLp_apply
  have hadm : Energy.LocalSlope.Admissible ν g :=
    (Energy.LocalSlope.admissible_iff_memLp_gradient_readable ν m hac g).mpr
      ⟨hK.locallyLipschitz, hg.memLp, hgrad⟩
  have hT : hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨f, hf⟩ =
      hgrad.toLp (gradient g) := by
    rw [Energy.WeightedGradient.operator_apply ν (ContinuousLinearMap.id ℝ V) hac
      (hν.frontier_support_eq_zero hi) hg hf hfg]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun y ↦ by
      rw [Energy.WeightedGradient.apply_id])
  refine ⟨⟨g, hadm⟩, hfg.symm, ?_⟩
  apply ENNReal.coe_le_coe.mp
  change ((Energy.LocalSlope.energy ν g).toNNReal : ENNReal) ≤
    ((‖hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨f, hf⟩‖₊ ^ 2 : NNReal) : ENNReal)
  rw [ENNReal.coe_toNNReal hadm.finite_energy, hT,
    Energy.LocalSlope.energy_eq_integral_gradient ν m hac g hK.locallyLipschitz hgrad,
    ← L2.norm_toLp_sq hgrad]
  rw [← ENNReal.ofReal_coe_nnreal]
  exact le_rfl
/-- The sequential relaxation of the unit-weight Lipschitz gradient operator is the canonical
smooth-gradient energy. -/
theorem FunctionalInequalities.KLS.LogConcave.weightedRelaxation_id_eq_smoothGradient (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    (PreEnergy.ofLinearPMap
      (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi)).sequentialRelaxation =
        Energy.SmoothGradient.relaxation ν := by
  obtain ⟨D⟩ := hν.exists_smoothGradient_localDensity_readable m hi
  apply Functional.ext
  intro x
  apply le_antisymm
  · simpa [Energy.SmoothGradient.lipschitzOperator, weightedOperator] using
      Energy.SmoothGradient.lipschitzRelaxation_le_relaxation_readable ν m D x
  · rw [Energy.SmoothGradient.relaxation_eq_localSlope ν]
    exact localSlope_relaxation_le_weightedRelaxation m hν hi x
/-- The squared norm form of the closed unit-weight gradient is the canonical energy. -/
theorem FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_id_energy_eq_smoothGradient (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    PreEnergy.normSqEnergy
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) =
        Energy.SmoothGradient.relaxation ν := by
  rw [← weightedRelaxation_id_eq_smoothGradient m hν hi]
  exact (PreEnergy.sequentialRelaxation_ofLinearPMap_eq_normSqEnergy
    (hν.weightedOperator m (ContinuousLinearMap.id ℝ V) hi)
    (hν.weightedOperator_isClosable m (ContinuousLinearMap.id ℝ V) hi)).symm
end FullDimensional
end
end
end

section
set_option autoImplicit false
noncomputable section
open MeasureTheory
section
open FunctionalInequalities.Energy
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
  (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)
/-- The optimal Poincare constant of the actual closed unit-gradient form is exactly the
intrinsic literature constant, including zero and infinity. -/
theorem FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_id_constant_eq_literature :
    Poincare.L2Energy.constant ν
      (PreEnergy.normSqEnergy
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) =
      Poincare.LocalSlope.Intrinsic.constant ν := by
  rw [hν.closedWeightedOperator_id_energy_eq_smoothGradient m hi]
  exact (Poincare.SmoothGradient.Ambient.constant_eq_intrinsic ν).trans
    hν.intrinsicSmooth_constant_eq_localSlope
end
end
end

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
/-- A form-domain gap `Var(u) ≤ C ‖T̄ u‖²` bounds the literature Poincaré constant by `C`
(the converse of `closedWeightedOperator_id_gap_of_literature_le`). -/
theorem solution (C : NNReal)
    (hgap : ∀ u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      ‖FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
        (C : ℝ) * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2) :
    FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) := by
  rw [← hν.closedWeightedOperator_id_constant_eq_literature m hi,
    ← FunctionalInequalities.Poincare.L2Energy.holds_iff_constant_le,
    FunctionalInequalities.Poincare.L2Energy.holds_iff]

  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  intro f

  have hfT : f.1 ∈ T.domain := by
    by_contra h
    have htop :
        FunctionalInequalities.Energy.PreEnergy.normSqEnergy T f.1 = ⊤ :=
      FunctionalInequalities.Energy.PreEnergy.normSqEnergy_of_notMem T h
    exact f.2 htop

  let u : T.domain := ⟨f.1, hfT⟩

  have hvalue :
      FunctionalInequalities.Energy.PreEnergy.normSqEnergy T f.1 =
        ((‖T u‖₊ ^ 2 : NNReal) : ENNReal) := by
    simpa [u] using
      (FunctionalInequalities.Energy.PreEnergy.normSqEnergy_of_mem T u)

  have hfinite :
      (FunctionalInequalities.Energy.PreEnergy.normSqEnergy T).finiteValue f =
        ‖T u‖₊ ^ 2 := by
    apply ENNReal.coe_injective
    calc
      ((FunctionalInequalities.Energy.PreEnergy.normSqEnergy T).finiteValue f : ENNReal) =
          (FunctionalInequalities.Energy.PreEnergy.normSqEnergy T).toFun f :=
        FunctionalInequalities.Energy.Functional.coe_finiteValue
          (FunctionalInequalities.Energy.PreEnergy.normSqEnergy T) f
      _ = FunctionalInequalities.Energy.PreEnergy.normSqEnergy T f.1 := rfl
      _ = ((‖T u‖₊ ^ 2 : NNReal) : ENNReal) := hvalue

  have hgap' :
      ‖FunctionalInequalities.L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖₊ ^ 2 ≤
        C * ‖T u‖₊ ^ 2 := by
    exact_mod_cast hgap u

  change
    FunctionalInequalities.L2.variance ν (f : Lp ℝ 2 (ν : Measure V)) ≤
      C * (FunctionalInequalities.Energy.PreEnergy.normSqEnergy T).finiteValue f

  rw [FunctionalInequalities.L2.variance, hfinite]
  simpa [u, T] using hgap'
