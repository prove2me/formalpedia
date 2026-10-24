-- Prove2me | solution 1 for FunctionalInequalities.Energy.LocalSlope.exists_partition_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:53:28.660871+00:00
-- url     : https://prove2.me/submissions/47d6ae48-e0cc-4721-b4bd-67d451c03639

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_lowerSemicontinuous_secant_408915f

section
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u
section
namespace FunctionalInequalities.Energy.AsymptoticLipschitz
end FunctionalInequalities.Energy.AsymptoticLipschitz
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.AsymptoticLipschitz
section Metric
variable {X : Type*} [MetricSpace X]
/-- A globally Lipschitz function has asymptotic Lipschitz constant at most its constant. -/
theorem FunctionalInequalities.Energy.AsymptoticLipschitz.apply_le_of_lipschitzWith {K : ℝ≥0} {f : X → ℝ} (hf : LipschitzWith K f) (x : X) :
    apply f x ≤ K := by
  unfold apply
  refine iInf_le_of_le 1 (iInf_le_of_le zero_lt_one ?_)
  refine iSup_le fun y ↦ iSup_le fun _ ↦ iSup_le fun z ↦ iSup_le fun _ ↦ ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  rcases eq_or_ne (dist y z) 0 with h0 | h0
  · rw [h0, div_zero]
    exact K.coe_nonneg
  · exact (div_le_iff₀ (dist_nonneg.lt_of_ne (Ne.symm h0))).2 (hf.dist_le_mul y z)
end Metric
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
end
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
section Metric
variable {X : Type*} [MetricSpace X]
/-- The one-moving-point local slope is dominated by the asymptotic Lipschitz constant. -/
theorem FunctionalInequalities.Energy.LocalSlope.apply_le_asymptoticLipschitz (f : X → ℝ) (x : X) :
    apply f x ≤ AsymptoticLipschitz.apply f x := by
  unfold apply AsymptoticLipschitz.apply
  refine iInf_mono fun r ↦ iInf_mono fun hr ↦ iSup_mono fun y ↦ iSup_mono fun hy ↦ ?_
  exact le_iSup₂_of_le x (by simpa using hr) le_rfl
end Metric
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
end
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
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
section Metric
variable {X : Type*} [MetricSpace X]
theorem FunctionalInequalities.Energy.LocalSlope.apply_eq_iInf_secant (f : X → ℝ) (x : X) :
    apply f x = ⨅ (r : ℝ) (_ : 0 < r), secant f r x :=
  rfl
/-- Every positive radius bounds the local slope from above. -/
theorem FunctionalInequalities.Energy.LocalSlope.apply_le_secant (f : X → ℝ) {r : ℝ} (hr : 0 < r) (x : X) :
    apply f x ≤ secant f r x :=
  iInf_le_of_le r (iInf_le _ hr)
/-- The secant supremum is monotone in the radius. -/
theorem FunctionalInequalities.Energy.LocalSlope.secant_mono (f : X → ℝ) {r r' : ℝ} (h : r ≤ r') (x : X) :
    secant f r x ≤ secant f r' x := by
  refine iSup_le fun y ↦ iSup_le fun hy ↦ ?_
  exact le_iSup₂_of_le y (hy.trans_le h) le_rfl
/-- A bound on the secant supremum is a Lipschitz-type bound on the ball. -/
theorem FunctionalInequalities.Energy.LocalSlope.dist_le_of_secant_le {f : X → ℝ} {r : ℝ} {x : X} {c : ℝ} (hc : 0 ≤ c)
    (h : secant f r x ≤ ENNReal.ofReal c) {y : X} (hy : dist y x < r) :
    dist (f y) (f x) ≤ c * dist y x := by
  rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := x)) with h0 | h0
  · have : y = x := by simpa [eq_comm] using h0.symm
    simp [this]
  · have hq : ENNReal.ofReal (dist (f y) (f x) / dist y x) ≤ ENNReal.ofReal c :=
      le_trans (le_iSup₂_of_le y hy le_rfl) h
    rw [ENNReal.ofReal_le_ofReal_iff hc, div_le_iff₀ h0] at hq
    exact hq
/-- Below any strict upper bound for the local slope there is a radius whose secant supremum
already respects it. -/
theorem FunctionalInequalities.Energy.LocalSlope.exists_secant_le {f : X → ℝ} {x : X} {c : ℝ≥0∞} (h : apply f x < c) :
    ∃ r : ℝ, 0 < r ∧ secant f r x ≤ c := by
  rw [apply_eq_iInf_secant, iInf_lt_iff] at h
  obtain ⟨r, hr⟩ := h
  rw [iInf_lt_iff] at hr
  obtain ⟨hr0, hlt⟩ := hr
  exact ⟨r, hr0, hlt.le⟩
end Metric
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
section Measurability
variable {X : Type*} [MetricSpace X]
/-- The local slope is the countable infimum of the secant suprema at the radii `1 / (m + 1)`. -/
theorem FunctionalInequalities.Energy.LocalSlope.apply_eq_iInf_nat (f : X → ℝ) (x : X) :
    apply f x = ⨅ m : ℕ, secant f (1 / ((m : ℝ) + 1)) x := by
  refine le_antisymm (le_iInf fun m ↦ apply_le_secant f (by positivity) x) ?_
  rw [apply_eq_iInf_secant]
  refine le_iInf fun r ↦ le_iInf fun hr ↦ ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr
  exact le_trans (iInf_le _ m) (secant_mono f hm.le x)
variable [MeasurableSpace X] [OpensMeasurableSpace X]
/-- `C1`.  The local slope of a continuous function is Borel measurable. -/
theorem FunctionalInequalities.Energy.LocalSlope.measurable_apply {f : X → ℝ} (hf : Continuous f) : Measurable (apply f) := by
  have h : apply f = fun x ↦ ⨅ m : ℕ, secant f (1 / ((m : ℝ) + 1)) x :=
    funext fun x ↦ apply_eq_iInf_nat f x
  rw [h]
  exact Measurable.iInf fun m ↦ (lowerSemicontinuous_secant_408915f hf _).measurable
end Measurability
end
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
section Patch
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities.Energy.LocalSlope in
omit [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V] in
/-- The Borel partition underlying the McShane patch: slope bands of width `α` cut by the balls
of a dense sequence, disjointed.  On each piece `f` is Lipschitz with a constant within `α` of
its local slope, and at most `L + α` overall. -/
theorem solution {f : V → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {α : ℝ≥0} (hα : 0 < α) :
    ∃ (D : ℕ → Set V) (c : ℕ → ℝ≥0),
      (∀ i, MeasurableSet (D i)) ∧ Pairwise (Function.onFun Disjoint D) ∧
      (⋃ i, D i) = Set.univ ∧ (∀ i, c i ≤ L + α) ∧
      (∀ i, LipschitzOnWith (c i) f (D i)) ∧
      (∀ i, ∀ x ∈ D i, ((c i : ℝ≥0∞)) ≤ FunctionalInequalities.Energy.LocalSlope.apply f x + (α : ℝ≥0∞)) := by
  classical
  have hcont : Continuous f := hf.continuous
  have hsL : ∀ x, FunctionalInequalities.Energy.LocalSlope.apply f x ≤ (L : ℝ≥0∞) := fun x ↦
    (FunctionalInequalities.Energy.LocalSlope.apply_le_asymptoticLipschitz f x).trans (FunctionalInequalities.Energy.AsymptoticLipschitz.apply_le_of_lipschitzWith hf x)
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq V
  set P : ℕ → ℕ → Set V := fun k m ↦
    {x | (((k : ℝ≥0) * α : ℝ≥0) : ℝ≥0∞) ≤ FunctionalInequalities.Energy.LocalSlope.apply f x} ∩
      {x | FunctionalInequalities.Energy.LocalSlope.apply f x < ((((k : ℝ≥0) + 1) * α : ℝ≥0) : ℝ≥0∞)} ∩
      {x | FunctionalInequalities.Energy.LocalSlope.secant f (1 / ((m : ℝ) + 1)) x ≤ ((((k : ℝ≥0) + 1) * α : ℝ≥0) : ℝ≥0∞)} with hPdef
  set A : ℕ → ℕ → ℕ → Set V := fun k m n ↦ P k m ∩ Metric.ball (v n) (1 / (4 * ((m : ℝ) + 1)))
    with hAdef
  set e : ℕ ≃ ℕ × ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ × ℕ)).symm with hedef
  set Aseq : ℕ → Set V := fun i ↦ A (e i).1 (e i).2.1 (e i).2.2 with hAseq
  have hmeasP : ∀ k m, MeasurableSet (P k m) := by
    intro k m
    refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
    · exact measurableSet_le measurable_const (FunctionalInequalities.Energy.LocalSlope.measurable_apply hcont)
    · exact measurableSet_lt (FunctionalInequalities.Energy.LocalSlope.measurable_apply hcont) measurable_const
    · exact (FunctionalInequalities.Energy.LocalSlope.lowerSemicontinuous_secant_408915f hcont _).measurable measurableSet_Iic
  have hmeasA : ∀ i, MeasurableSet (Aseq i) := fun i ↦
    (hmeasP _ _).inter Metric.isOpen_ball.measurableSet
  set D : ℕ → Set V := disjointed Aseq with hDdef
  set c : ℕ → ℝ≥0 := fun i ↦ min ((((e i).1 : ℝ≥0) + 1) * α) (L + α) with hcdef
  have hDsub : ∀ i, D i ⊆ Aseq i := fun i ↦ disjointed_subset Aseq i
  have hcover : (⋃ i, Aseq i) = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    have hfin : FunctionalInequalities.Energy.LocalSlope.apply f x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hsL x)
    set t : ℝ := (FunctionalInequalities.Energy.LocalSlope.apply f x).toReal with htdef
    have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
    have hteq : FunctionalInequalities.Energy.LocalSlope.apply f x = ENNReal.ofReal t := (ENNReal.ofReal_toReal hfin).symm
    set k : ℕ := ⌊t / (α : ℝ)⌋₊ with hkdef
    have hαpos : (0 : ℝ) < (α : ℝ) := hα
    have hk1 : (k : ℝ) * (α : ℝ) ≤ t := by
      have := Nat.floor_le (a := t / (α : ℝ)) (by positivity)
      rw [le_div_iff₀ hαpos] at this
      exact this
    have hk2 : t < ((k : ℝ) + 1) * (α : ℝ) := by
      have := Nat.lt_floor_add_one (t / (α : ℝ))
      rw [div_lt_iff₀ hαpos] at this
      exact this
    have hband1 : ((((k : ℝ≥0)) * α : ℝ≥0) : ℝ≥0∞) ≤ FunctionalInequalities.Energy.LocalSlope.apply f x := by
      rw [hteq, ← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal ?_
      push_cast
      exact hk1
    have hband2 : FunctionalInequalities.Energy.LocalSlope.apply f x < ((((k : ℝ≥0) + 1) * α : ℝ≥0) : ℝ≥0∞) := by
      rw [hteq, ← ENNReal.ofReal_coe_nnreal]
      refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht0).2 ?_
      push_cast
      exact hk2
    obtain ⟨r, hr0, hsec⟩ := FunctionalInequalities.Energy.LocalSlope.exists_secant_le hband2
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hr0
    have hPm : x ∈ P k m := ⟨⟨hband1, hband2⟩, (FunctionalInequalities.Energy.LocalSlope.secant_mono f hm.le x).trans hsec⟩
    obtain ⟨n, hn⟩ := hv.exists_dist_lt x (ε := 1 / (4 * ((m : ℝ) + 1))) (by positivity)
    refine Set.mem_iUnion.2 ⟨e.symm (k, m, n), ?_⟩
    rw [hAseq]
    simp only [Equiv.apply_symm_apply]
    exact ⟨hPm, by simpa [Metric.mem_ball] using hn⟩
  have hlipA : ∀ i, LipschitzOnWith (c i) f (Aseq i) := by
    intro i
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    obtain ⟨hxP, hxb⟩ := hx
    obtain ⟨hyP, hyb⟩ := hy
    set k : ℕ := (e i).1
    set m : ℕ := (e i).2.1
    have hci : c i = (((k : ℝ≥0)) + 1) * α := by
      refine min_eq_left ?_
      have hk : ((((k : ℝ≥0)) * α : ℝ≥0) : ℝ≥0∞) ≤ (L : ℝ≥0∞) := hxP.1.1.trans (hsL x)
      have hk' : ((k : ℝ≥0)) * α ≤ L := by exact_mod_cast hk
      have : ((((k : ℝ≥0)) + 1) * α : ℝ≥0) = (k : ℝ≥0) * α + α := by ring
      rw [this]
      exact add_le_add hk' le_rfl
    have hdist : dist y x < 1 / ((m : ℝ) + 1) := by
      have h1 : dist x (v (e i).2.2) < 1 / (4 * ((m : ℝ) + 1)) := by
        simpa [Metric.mem_ball] using hxb
      have h2 : dist y (v (e i).2.2) < 1 / (4 * ((m : ℝ) + 1)) := by
        simpa [Metric.mem_ball] using hyb
      have h3 : dist y x ≤ dist y (v (e i).2.2) + dist (v (e i).2.2) x :=
        dist_triangle _ _ _
      rw [dist_comm (v (e i).2.2) x] at h3
      have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have h4 : (0 : ℝ) < 4 * ((m : ℝ) + 1) := by linarith
      have hlt : (2 : ℝ) * (1 / (4 * ((m : ℝ) + 1))) < 1 / ((m : ℝ) + 1) := by
        rw [mul_one_div, div_lt_div_iff₀ h4 hm0]
        nlinarith
      linarith
    have hsecx : FunctionalInequalities.Energy.LocalSlope.secant f (1 / ((m : ℝ) + 1)) x ≤
        ENNReal.ofReal (((((k : ℝ≥0)) + 1) * α : ℝ≥0) : ℝ) := by
      rw [ENNReal.ofReal_coe_nnreal]
      exact hxP.2
    have := FunctionalInequalities.Energy.LocalSlope.dist_le_of_secant_le (NNReal.coe_nonneg _) hsecx hdist
    rw [dist_comm (f x) (f y), dist_comm x y, hci]
    exact this
  refine ⟨D, c, fun i ↦ MeasurableSet.disjointed hmeasA i, disjoint_disjointed Aseq, ?_,
    fun i ↦ min_le_right _ _, fun i ↦ (hlipA i).mono (hDsub i), ?_⟩
  · rw [hDdef, iUnion_disjointed, hcover]
  · intro i x hx
    have hxA : x ∈ Aseq i := hDsub i hx
    have hk : ((((e i).1 : ℝ≥0)) * α : ℝ≥0) ≤ FunctionalInequalities.Energy.LocalSlope.apply f x := by
      exact_mod_cast hxA.1.1.1
    calc ((c i : ℝ≥0) : ℝ≥0∞) ≤ ((((((e i).1 : ℝ≥0)) + 1) * α : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_le_coe.2 (min_le_left _ _)
      _ = (((((e i).1 : ℝ≥0)) * α : ℝ≥0) : ℝ≥0∞) + (α : ℝ≥0∞) := by
          rw [← ENNReal.coe_add]
          congr 1
          ring
      _ ≤ FunctionalInequalities.Energy.LocalSlope.apply f x + (α : ℝ≥0∞) := add_le_add hk le_rfl
