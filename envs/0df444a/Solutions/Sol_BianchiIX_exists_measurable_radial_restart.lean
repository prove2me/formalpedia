-- Prove2me | solution 1 for BianchiIX.exists_measurable_radial_restart
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:07:23.901921+00:00
-- url     : https://prove2.me/submissions/5e494687-6e3c-433d-8d0c-8c6e21779785

import Definitions.Def_BianchiIX_RadialFailureData
import Theorems.Thm_BianchiIX_exists_mem_physicalRadialPiece
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX
open MeasureTheory
open scoped Topology ENNReal

private theorem BianchiIX.dyadicScale_pos {d : ℝ} (hd : 0 < d) (j : ℕ) : 0 < dyadicScale d j := by
  exact mul_pos hd (pow_pos (by norm_num) _)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exists_measurable_countable_selection {ι X Y : Type*} [Countable ι] [Nonempty ι]
    [MeasurableSpace X] [MeasurableSpace Y] (S : ι → Set X) (f : ι → X → Y)
    (hS : ∀ i, MeasurableSet (S i)) (hf : ∀ i, Measurable (f i)) :
    ∃ g : X → Y, Measurable g ∧ ∀ x ∈ ⋃ i, S i, ∃ i, x ∈ S i ∧ g x = f i x := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  let U := ⋃ i, S i
  have hU : MeasurableSet U := MeasurableSet.iUnion hS
  have hcover (x : U) : ∃ n, x.val ∈ S (e n) := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    obtain ⟨n, rfl⟩ := he i
    exact ⟨n, hi⟩
  let g₀ : U → Y := fun x => f (e (Nat.find (hcover x))) x.val
  have hg₀ : Measurable g₀ := Measurable.find
    (fun n => (hf (e n)).comp measurable_subtype_coe)
    (fun n => (hS (e n)).preimage measurable_subtype_coe) hcover
  let g : X → Y := fun x => if hx : x ∈ U then g₀ ⟨x, hx⟩ else f (e 0) x
  refine ⟨g, hg₀.dite ((hf (e 0)).comp measurable_subtype_coe) hU, ?_⟩
  intro x hx
  change x ∈ U at hx
  refine ⟨e (Nat.find (hcover ⟨x, hx⟩)), Nat.find_spec (hcover ⟨x, hx⟩), ?_⟩
  simp only [g, dif_pos hx, g₀]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exists_measurable_chart_extension {X Y V : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace V] [Nonempty V] {D : Set X} {C : X → Y} {G : X → V}
    (hD : MeasurableSet D) (hC : ContinuousOn C D) (hinj : InjOn C D)
    (hG : Measurable (D.domRestrict G)) :
    ∃ g : Y → V, Measurable g ∧ ∀ x ∈ D, g (C x) = G x := by
  classical
  by_cases hne : D.Nonempty
  · let : Nonempty D := hne.to_subtype
    have H := hC.measurableEmbedding hD hinj
    refine ⟨fun y => G (H.invFun y).val, hG.comp H.measurable_invFun, ?_⟩
    intro x hx
    exact congrArg (fun z : D => G z.val) (H.leftInverse_invFun ⟨x, hx⟩)
  · exact ⟨fun _ => Classical.arbitrary V, measurable_const, fun x hx => (hne ⟨x, hx⟩).elim⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.two_mul_dyadicScale (d : ℝ) (j : ℕ) :
    2 * dyadicScale d j = d * (1 / 2 : ℝ) ^ j := by
  rw [dyadicScale, pow_succ]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_mem_dyadicScale_Ioc {d x : ℝ} (hd : 0 < d) (hx : x ∈ Ioc 0 d) :
    ∃ j : ℕ, x ∈ Ioc (dyadicScale d j) (2 * dyadicScale d j) := by
  obtain ⟨j, hj, hJ⟩ := exists_nat_pow_near_of_lt_one (div_pos hx.1 hd)
    ((div_le_one hd).mpr hx.2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨j, ?_, ?_⟩
  · change d * (1 / 2 : ℝ) ^ (j + 1) < x
    exact (mul_comm _ _).trans_lt ((lt_div_iff₀ hd).mp hj)
  · rw [two_mul_dyadicScale]
    exact ((div_le_iff₀ hd).mp hJ).trans_eq (mul_comm _ _)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.pairwise_disjoint_dyadicScale_Ioc {d : ℝ} (hd : 0 ≤ d) :
    Pairwise (fun j k : ℕ => Disjoint (Ioc (dyadicScale d j) (2 * dyadicScale d j))
      (Ioc (dyadicScale d k) (2 * dyadicScale d k))) := by
  have H {j k : ℕ} (hjk : j < k) : 2 * dyadicScale d k ≤ dyadicScale d j := by
    rw [two_mul_dyadicScale]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hjk) hd
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hjk with hj | hk
  · exact (not_lt_of_ge (hy.2.trans (H hj))) hx.1
  · exact (not_lt_of_ge (hx.2.trans (H hk))) hy.1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.hasFDerivAt_scaledAngularLogCoordinates {a : ℝ} {z : SectionCoordinates}
    (ha : 0 < a) (hρ : 0 < z 0) (ht : 0 < z 2) :
    HasFDerivAt (scaledAngularLogCoordinates a) (scaledAngularLogDifferential z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) z).mul
      (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) z) using 1
  · convert! ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) z).log hρ.ne').neg using 1
    ext v
    change -(z 0)⁻¹ * v 0 = -((z 0)⁻¹ * v 0)
    ring
  · have H := (((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) z).const_mul (2 * a)).log
      (mul_pos (mul_pos (by norm_num) ha) ht).ne').neg
    convert! H using 1
    ext v
    change -(z 2)⁻¹ * v 2 = -((2 * a * z 2)⁻¹ * (2 * a * v 2))
    field_simp

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.scaledAngularLogCoordinates_injOn {a : ℝ} (ha : 0 < a) :
    InjOn (scaledAngularLogCoordinates a) {z : SectionCoordinates | 0 < z 0 ∧ 0 < z 2} := by
  intro z hz w hw heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  change -Real.log (z 0) = -Real.log (w 0) at h1
  change -Real.log (2 * a * z 2) = -Real.log (2 * a * w 2) at h2
  have hρ := Real.log_injOn_pos hz.1 hw.1 (neg_injective h1)
  have ht := Real.log_injOn_pos (mul_pos (mul_pos (by norm_num) ha) hz.2)
    (mul_pos (mul_pos (by norm_num) ha) hw.2) (neg_injective h2)
  have htw : z 2 = w 2 := mul_left_cancel₀ (by positivity : 2 * a ≠ 0) ht
  change z 1 * z 0 = w 1 * w 0 at h0
  rw [hρ] at h0
  have hθ := mul_right_cancel₀ hw.1.ne' h0
  ext i
  fin_cases i
  · exact hρ
  · exact hθ
  · exact htw

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_mainWallReflection_image {A : Set SectionCoordinates} (hA : MeasurableSet A) :
    MeasurableSet (mainWallReflection '' A) :=
  hA.image_of_continuousOn_injOn mainWallReflectionEquiv.continuous.continuousOn
    mainWallReflectionEquiv.injective.injOn

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.hasFDerivAt_signedShearLogCoordinates {σ : ℝ} {z : SectionCoordinates}
    (h₁ : 0 < z 1) (h₂ : 0 < z 2) :
    HasFDerivAt (signedShearLogCoordinates σ) (signedShearLogDifferential σ z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) z).const_mul σ
  · convert! ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) z).log h₁.ne').neg using 1
    ext v
    change -(z 1)⁻¹ * v 1 = -((z 1)⁻¹ * v 1)
    ring
  · convert! ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) z).log h₂.ne').neg using 1
    ext v
    change -(z 2)⁻¹ * v 2 = -((z 2)⁻¹ * v 2)
    ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.signedShearLogCoordinates_injOn {σ : ℝ} (hσ : σ ≠ 0) :
    InjOn (signedShearLogCoordinates σ) {z : SectionCoordinates | 0 < z 1 ∧ 0 < z 2} := by
  intro z hz w hw heq
  have h0 : σ * z 0 = σ * w 0 := congrFun heq 0
  have h1 : -Real.log (z 1) = -Real.log (w 1) := congrFun heq 1
  have h2 : -Real.log (z 2) = -Real.log (w 2) := congrFun heq 2
  ext i
  fin_cases i
  · exact mul_left_cancel₀ hσ h0
  · exact Real.log_injOn_pos hz.1 hw.1 (neg_injective h1)
  · exact Real.log_injOn_pos hz.2 hw.2 (neg_injective h2)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_shearRadialDomain (a d ε : ℝ) : MeasurableSet (shearRadialDomain a d ε) := by
  have h₁ : MeasurableSet {z : SectionCoordinates | 0 < z 1} := measurableSet_lt (by fun_prop) (by fun_prop)
  have h₂ : MeasurableSet {z : SectionCoordinates | 0 < z 2} := measurableSet_lt (by fun_prop) (by fun_prop)
  have hr : MeasurableSet {z : SectionCoordinates | z 0 ∈ Ioo a (2 * a)} :=
    measurableSet_Ioo.preimage (by fun_prop)
  have hm : MeasurableSet {z : SectionCoordinates | max (z 1) (z 2) ≤ ε * z 0} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hd : MeasurableSet {z : SectionCoordinates | z 0 < d} := measurableSet_lt (by fun_prop) (by fun_prop)
  exact h₁.inter (h₂.inter (hr.inter (hm.inter hd)))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_angularRadialDomain (otherWall : Bool) (a d L : ℝ) :
    MeasurableSet (angularRadialDomain otherWall a d L) := by
  have horder : MeasurableSet {z : SectionCoordinates | if otherWall then z 2 < z 0 else z 2 ≤ z 0} := by
    cases otherWall
    · exact measurableSet_le (by fun_prop) (by fun_prop)
    · exact measurableSet_lt (by fun_prop) (by fun_prop)
  have hθ : MeasurableSet {z : SectionCoordinates | |z 1| < L} := measurableSet_lt (by fun_prop) (by fun_prop)
  have hζ : MeasurableSet {z : SectionCoordinates | 0 < z 2} := measurableSet_lt (by fun_prop) (by fun_prop)
  have hr : MeasurableSet {z : SectionCoordinates | z 0 ∈ Ioo a (2 * a)} :=
    measurableSet_Ioo.preimage (by fun_prop)
  have hd : MeasurableSet {z : SectionCoordinates | z 0 < d} := measurableSet_lt (by fun_prop) (by fun_prop)
  have hs : MeasurableSet {z : SectionCoordinates | |z 1| * z 0 < d} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  exact hθ.inter (hζ.inter (hr.inter (horder.inter (hd.inter hs))))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_shearRadialPiece {a d ε σ : ℝ} {F : Set SectionCoordinates}
    (hσ : σ ≠ 0) (hF : MeasurableSet F) :
    MeasurableSet (signedShearLogCoordinates σ '' (shearRadialDomain a d ε ∩ F)) := by
  have hpos : ∀ z ∈ shearRadialDomain a d ε ∩ F, 0 < z 1 ∧ 0 < z 2 :=
    fun _ hz => ⟨hz.1.1, hz.1.2.1⟩
  exact ((measurableSet_shearRadialDomain a d ε).inter hF).image_of_continuousOn_injOn
    (fun z hz => (hasFDerivAt_signedShearLogCoordinates (hpos z hz).1
      (hpos z hz).2).continuousAt.continuousWithinAt)
    ((signedShearLogCoordinates_injOn hσ).mono hpos)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_angularRadialPiece {a d L : ℝ} {F : Set SectionCoordinates}
    (otherWall : Bool) (ha : 0 < a) (hF : MeasurableSet F) :
    MeasurableSet (orderedAngularLogCoordinates otherWall '' (angularRadialDomain otherWall a d L ∩ F)) := by
  have hpos : ∀ z ∈ angularRadialDomain otherWall a d L ∩ F, 0 < z 0 ∧ 0 < z 2 :=
    fun _ hz => ⟨ha.trans hz.1.2.2.1.1, hz.1.2.1⟩
  have hbase : MeasurableSet (scaledAngularLogCoordinates (1 / 2) ''
      (angularRadialDomain otherWall a d L ∩ F)) :=
    ((measurableSet_angularRadialDomain otherWall a d L).inter hF).image_of_continuousOn_injOn
      (fun z hz => (hasFDerivAt_scaledAngularLogCoordinates (by norm_num) (hpos z hz).1
        (hpos z hz).2).continuousAt.continuousWithinAt)
      ((scaledAngularLogCoordinates_injOn (by norm_num : (0 : ℝ) < 1 / 2)).mono hpos)
  cases otherWall
  · exact hbase
  · change MeasurableSet ((mainWallReflection ∘ scaledAngularLogCoordinates (1 / 2)) '' _)
    rw [image_comp]
    exact measurableSet_mainWallReflection_image hbase

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.angularRadialPieces_disjoint {a b d e L M : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Disjoint (orderedAngularLogCoordinates false '' angularRadialDomain false a d L)
      (orderedAngularLogCoordinates true '' angularRadialDomain true b e M) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have hx0 : 0 < x 0 := ha.trans hx.2.2.1.1
  have hy0 : 0 < y 0 := hb.trans hy.2.2.1.1
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  simp only [orderedAngularLogCoordinates, Bool.false_eq_true, ↓reduceIte,
    mainWallReflection, scaledAngularLogCoordinates, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_zero] at h1 h2
  norm_num at h1 h2
  have h10 : y 2 = x 0 := Real.log_injOn_pos hy.2.1 hx0 h1
  have h20 : y 0 = x 2 := Real.log_injOn_pos hy0 hx.2.1 h2
  have hxy : x 2 ≤ x 0 := hx.2.2.2.1
  have hyx : y 2 < y 0 := hy.2.2.2.1
  linarith

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.signedShearRadialPieces_disjoint {a b d e ε δ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Disjoint (signedShearLogCoordinates 1 '' shearRadialDomain a d ε)
      (signedShearLogCoordinates (-1) '' shearRadialDomain b e δ) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have hx0 : 0 < x 0 := ha.trans hx.2.2.1.1
  have hy0 : 0 < y 0 := hb.trans hy.2.2.1.1
  have h0 : (-1 : ℝ) * y 0 = 1 * x 0 := congrFun heq 0
  linarith

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.radialPieceInverse_map {d ε : ℝ} (hd : 0 < d) {i : RadialPieceIndex}
    {z : SectionCoordinates} (hz : z ∈ radialPieceDomain d ε i) :
    radialPieceInverse i.1 (radialPieceMap i.1 z) = z := by
  rcases i with ⟨neg | other, j⟩
  · have h₁ : 0 < z 1 := hz.1
    have h₂ : 0 < z 2 := hz.2.1
    cases neg <;> ext n <;> fin_cases n <;>
      simp [radialPieceInverse, radialPieceMap, signedShearLogCoordinates, Real.exp_log h₁, Real.exp_log h₂]
  · have hr : 0 < z 0 := (dyadicScale_pos hd j).trans hz.2.2.1.1
    have hζ : 0 < z 2 := hz.2.1
    cases other <;> ext n <;> fin_cases n <;>
      simp [radialPieceInverse, radialPieceMap, orderedAngularLogCoordinates,
        scaledAngularLogCoordinates, mainWallReflection, Real.exp_log hr, Real.exp_log hζ, hr.ne']

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mainWallRadialRadius_pos {ε : ℝ} (hε : 0 < ε) (z : SectionCoordinates) :
    0 < mainWallRadialRadius ε z := by
  have hm : 0 < max (Real.exp (-z 1)) (Real.exp (-z 2)) :=
    (Real.exp_pos _).trans_le (le_max_left _ _)
  unfold mainWallRadialRadius
  split_ifs with hs
  · exact (mul_pos_iff_of_pos_left hε).mp (hm.trans_le hs)
  · exact hm

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mainWallRadialRadius_lt {d ε : ℝ} {z : SectionCoordinates}
    (hz : z ∈ mainWallOpenSection d) : mainWallRadialRadius ε z < d := by
  unfold mainWallRadialRadius
  split_ifs
  · exact hz.1
  · exact hz.2

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.signedShearLogCoordinates_radial_data {a d ε σ : ℝ} {z : SectionCoordinates}
    (ha : 0 < a) (hσ : |σ| = 1) (hz : z ∈ shearRadialDomain a d ε) :
    |signedShearLogCoordinates σ z 0| = z 0 ∧
    max (Real.exp (-(signedShearLogCoordinates σ z) 1))
      (Real.exp (-(signedShearLogCoordinates σ z) 2)) = max (z 1) (z 2) := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  simp [signedShearLogCoordinates, abs_mul, hσ, abs_of_pos hr,
    Real.exp_log hz.1, Real.exp_log hz.2.1]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.orderedAngularLogCoordinates_radial_data {a d L : ℝ} {z : SectionCoordinates}
    (other : Bool) (ha : 0 < a) (hz : z ∈ angularRadialDomain other a d L) :
    |orderedAngularLogCoordinates other z 0| = |z 1| * z 0 ∧
    max (Real.exp (-(orderedAngularLogCoordinates other z) 1))
      (Real.exp (-(orderedAngularLogCoordinates other z) 2)) = z 0 := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have ho := hz.2.2.2.1
  cases other with
  | false =>
    simp [orderedAngularLogCoordinates, scaledAngularLogCoordinates, abs_mul, abs_of_pos hr,
      Real.exp_log hr, Real.exp_log hz.2.1, max_eq_left ho]
  | true =>
    simp [orderedAngularLogCoordinates, mainWallReflection, scaledAngularLogCoordinates,
      abs_mul, abs_of_pos hr, Real.exp_log hr, Real.exp_log hz.2.1,
      max_eq_right (le_of_lt ho)]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.shearRadialPiece_region {a d ε σ : ℝ} {y : SectionCoordinates}
    (ha : 0 < a) (hσ : |σ| = 1) (hy : y ∈ signedShearLogCoordinates σ '' shearRadialDomain a d ε) :
    max (Real.exp (-y 1)) (Real.exp (-y 2)) ≤ ε * |y 0| ∧
      mainWallRadialRadius ε y ∈ Ioo a (2 * a) := by
  rcases hy with ⟨z, hz, rfl⟩
  obtain ⟨hs, hm⟩ := signedShearLogCoordinates_radial_data ha hσ hz
  have hreg : max (Real.exp (-(signedShearLogCoordinates σ z) 1))
      (Real.exp (-(signedShearLogCoordinates σ z) 2)) ≤ ε * |signedShearLogCoordinates σ z 0| := by
    rw [hs, hm]
    exact hz.2.2.2.1
  refine ⟨hreg, ?_⟩
  unfold mainWallRadialRadius
  rw [if_pos hreg, hs]
  exact hz.2.2.1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.angularRadialPiece_region {a d ε : ℝ} {y : SectionCoordinates}
    (other : Bool) (ha : 0 < a) (hε : 0 < ε)
    (hy : y ∈ orderedAngularLogCoordinates other '' angularRadialDomain other a d (1 / ε)) :
    ε * |y 0| < max (Real.exp (-y 1)) (Real.exp (-y 2)) ∧
      mainWallRadialRadius ε y ∈ Ioo a (2 * a) := by
  rcases hy with ⟨z, hz, rfl⟩
  obtain ⟨hs, hm⟩ := orderedAngularLogCoordinates_radial_data other ha hz
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have hθ : ε * |z 1| < 1 := by
    have H := (lt_div_iff₀ hε).mp hz.1
    nlinarith
  have hreg : ε * |orderedAngularLogCoordinates other z 0| <
      max (Real.exp (-(orderedAngularLogCoordinates other z) 1))
        (Real.exp (-(orderedAngularLogCoordinates other z) 2)) := by
    rw [hs, hm]
    nlinarith [mul_lt_mul_of_pos_right hθ hr]
  refine ⟨hreg, ?_⟩
  unfold mainWallRadialRadius
  rw [if_neg (not_le.mpr hreg), hm]
  exact hz.2.2.1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.physicalRadialPiece_radius {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    {i : RadialPieceIndex} {z : SectionCoordinates} (hz : z ∈ physicalRadialPiece d ε i) :
    mainWallRadialRadius ε z ∈ Ioo (dyadicScale d i.2) (2 * dyadicScale d i.2) := by
  rcases i with ⟨neg | other, j⟩
  · exact (shearRadialPiece_region (dyadicScale_pos hd j)
      (by cases neg <;> norm_num) hz).2
  · exact (angularRadialPiece_region other (dyadicScale_pos hd j) hε hz).2

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.physicalRadialPiece_subset_openSection {d ε : ℝ} (hd : 0 < d) (hε : ε ≤ 1)
    (i : RadialPieceIndex) : physicalRadialPiece d ε i ⊆ mainWallOpenSection d := by
  rcases i with ⟨neg | other, j⟩
  · rintro _ ⟨z, hz, rfl⟩
    have ha := dyadicScale_pos hd j
    obtain ⟨hs, hm⟩ := signedShearLogCoordinates_radial_data ha
      (show |(if neg then -1 else 1 : ℝ)| = 1 by cases neg <;> norm_num) hz
    change |signedShearLogCoordinates _ z 0| < d ∧
      max (Real.exp (-(signedShearLogCoordinates _ z) 1))
        (Real.exp (-(signedShearLogCoordinates _ z) 2)) < d
    rw [hs, hm]
    refine ⟨hz.2.2.2.2, (hz.2.2.2.1.trans ?_).trans_lt hz.2.2.2.2⟩
    have hr : 0 < z 0 := ha.trans hz.2.2.1.1
    nlinarith
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hs, hm⟩ := orderedAngularLogCoordinates_radial_data other (dyadicScale_pos hd j) hz
    change |orderedAngularLogCoordinates other z 0| < d ∧
      max (Real.exp (-(orderedAngularLogCoordinates other z) 1))
        (Real.exp (-(orderedAngularLogCoordinates other z) 2)) < d
    rw [hs, hm]
    exact ⟨hz.2.2.2.2.2, hz.2.2.2.2.1⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.shear_angular_radialPieces_disjoint {a b d e ε : ℝ} {σ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) (hσ : |σ| = 1) (other : Bool) :
    Disjoint (signedShearLogCoordinates σ '' shearRadialDomain a d ε)
      (orderedAngularLogCoordinates other '' angularRadialDomain other b e (1 / ε)) := by
  apply Set.disjoint_left.mpr
  intro z hs ha'
  exact (not_lt_of_ge (shearRadialPiece_region ha hσ hs).1)
    (angularRadialPiece_region other hb hε ha').1

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.physicalRadialPieces_pairwiseDisjoint {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    Pairwise (fun i j : RadialPieceIndex => Disjoint (physicalRadialPiece d ε i) (physicalRadialPiece d ε j)) := by
  rintro ⟨k, n⟩ ⟨l, m⟩ hij
  by_cases hnm : n = m
  · subst m
    have hkl : k ≠ l := by intro h; exact hij (by cases h; rfl)
    rcases k with neg | other <;> rcases l with neg' | other'
    · cases neg <;> cases neg'
      · exact False.elim (hkl rfl)
      · exact signedShearRadialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)
      · exact (signedShearRadialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)).symm
      · exact False.elim (hkl rfl)
    · exact shear_angular_radialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)
        hε (by cases neg <;> norm_num) other'
    · exact (shear_angular_radialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)
        hε (by cases neg' <;> norm_num) other).symm
    · cases other <;> cases other'
      · exact False.elim (hkl rfl)
      · exact angularRadialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)
      · exact (angularRadialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)).symm
      · exact False.elim (hkl rfl)
  · apply Set.disjoint_left.mpr
    intro z hz hw
    exact Set.disjoint_left.mp (pairwise_disjoint_dyadicScale_Ioc hd.le hnm)
      ⟨(physicalRadialPiece_radius hd hε hz).1, (physicalRadialPiece_radius hd hε hz).2.le⟩
      ⟨(physicalRadialPiece_radius hd hε hw).1, (physicalRadialPiece_radius hd hε hw).2.le⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.mainWallOpenSection_radial_partition {d ε : ℝ}
    (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    mainWallOpenSection d = mainWallRadialBoundary d ε ∪ ⋃ i : RadialPieceIndex, physicalRadialPiece d ε i := by
  ext z
  constructor
  · intro hz
    by_cases hb : z ∈ mainWallRadialBoundary d ε
    · exact Or.inl hb
    · obtain ⟨j, hj⟩ := exists_mem_dyadicScale_Ioc hd
        ⟨mainWallRadialRadius_pos hε z, (mainWallRadialRadius_lt hz).le⟩
      have hne : mainWallRadialRadius ε z ≠ 2 * dyadicScale d j := by
        intro heq
        exact hb ⟨hz, mem_iUnion_of_mem j heq⟩
      obtain ⟨k, hk⟩ := exists_mem_physicalRadialPiece hε hz ⟨hj.1, lt_of_le_of_ne hj.2 hne⟩
      exact Or.inr (mem_iUnion_of_mem (k, j) hk)
  · rintro (hb | hp)
    · exact hb.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact physicalRadialPiece_subset_openSection hd hε1 i hi

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_radialFailurePiece {d ε : ℝ} (hd : 0 < d)
    {F : RadialPieceIndex → Set SectionCoordinates} (hF : ∀ i, MeasurableSet (F i))
    (i : RadialPieceIndex) : MeasurableSet (radialFailurePiece d ε F i) := by
  rcases i with ⟨neg | other, j⟩
  · exact measurableSet_shearRadialPiece (by cases neg <;> norm_num) (hF _)
  · exact measurableSet_angularRadialPiece other (dyadicScale_pos hd j) (hF _)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.radialFailureSet_complement {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (F : RadialPieceIndex → Set SectionCoordinates) {z : SectionCoordinates}
    (hz : z ∈ mainWallOpenSection d \ radialFailureSet d ε F) :
    ∃! i : RadialPieceIndex, z ∈ physicalRadialPiece d ε i ∧ radialPieceInverse i.1 z ∉ F i := by
  have hb : z ∉ mainWallRadialBoundary d ε := fun hb => hz.2 (Or.inl hb)
  have hcover := hz.1
  rw [mainWallOpenSection_radial_partition hd hε hε1] at hcover
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.resolve_left hb)
  refine ⟨i, ⟨hi, ?_⟩, ?_⟩
  · rintro hf
    rcases hi with ⟨x, hx, rfl⟩
    rw [radialPieceInverse_map hd hx] at hf
    exact hz.2 (Or.inr (mem_iUnion_of_mem i ⟨x, ⟨hx, hf⟩, rfl⟩))
  · intro j hj
    by_contra hji
    exact Set.disjoint_left.mp (physicalRadialPieces_pairwiseDisjoint hd hε hji) hj.1 hi

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.measurableSet_restartLabelSet (L r P : ℝ) : MeasurableSet (restartLabelSet L r P) :=
  (measurableSet_le (continuous_abs.comp continuous_fst).measurable measurable_const).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const))

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.measurableSet_restartShearCommonLabelSet (ε a P : ℝ) :
    MeasurableSet (restartShearCommonLabelSet ε a P) :=
  ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)).inter
    (((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)).inter
      (measurableSet_le (measurable_fst.min measurable_snd) measurable_const))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_angularRestartParameterDomain (a L P : ℝ) :
    MeasurableSet (angularRestartParameterDomain a L P) :=
  (measurableSet_restartLabelSet L a P).prod measurableSet_Icc

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.continuousOn_angularRestartChart {a L P : ℝ} (ha : 0 < a) (o : Bool) :
    ContinuousOn (angularRestartChart o) (angularRestartParameterDomain a L P) := by
  have H : ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      (![p.1.1 * p.2, -Real.log p.2, -Real.log p.1.2] : SectionCoordinates))
      (angularRestartParameterDomain a L P) := by
    intro p hp
    have hr : p.2 ≠ 0 := (ha.trans_le hp.2.1).ne'
    have hz : p.1.2 ≠ 0 := hp.1.2.1.ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop
  cases o
  · exact H
  · exact mainWallReflectionEquiv.continuous.comp_continuousOn H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.injOn_angularRestartChart {a L P : ℝ} (ha : 0 < a) (o : Bool) :
    InjOn (angularRestartChart o) (angularRestartParameterDomain a L P) := by
  have H : InjOn (angularRestartChart false) (angularRestartParameterDomain a L P) := by
    intro p hp q hq heq
    have hpρ : 0 < p.2 := ha.trans_le hp.2.1
    have hqρ : 0 < q.2 := ha.trans_le hq.2.1
    have hρ := Real.log_injOn_pos hpρ hqρ (neg_injective (congrFun heq 1))
    have hζ := Real.log_injOn_pos hp.1.2.1 hq.1.2.1 (neg_injective (congrFun heq 2))
    have hθ := congrFun heq 0
    change p.1.1 * p.2 = q.1.1 * q.2 at hθ
    rw [hρ] at hθ
    exact Prod.ext (Prod.ext (mul_right_cancel₀ hqρ.ne' hθ) hζ) hρ
  cases o
  · exact H
  · intro p hp q hq heq
    exact H hp hq (mainWallReflectionEquiv.injective heq)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurableSet_shearRestartParameterDomain (ε a P : ℝ) :
    MeasurableSet (shearRestartParameterDomain ε a P) :=
  (measurableSet_restartShearCommonLabelSet ε a P).prod measurableSet_Icc

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.continuousOn_shearRestartChart (ε a P : ℝ) (o : Bool) :
    ContinuousOn (shearRestartChart o) (shearRestartParameterDomain ε a P) := by
  have H : ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      (![p.2, -Real.log p.1.1, -Real.log p.1.2] : SectionCoordinates))
      (shearRestartParameterDomain ε a P) := by
    intro p hp
    have h₂ : p.1.1 ≠ 0 := hp.1.1.1.ne'
    have h₃ : p.1.2 ≠ 0 := hp.1.2.1.1.ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop
  cases o
  · exact H
  · exact mainWallReflectionEquiv.continuous.comp_continuousOn H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.injOn_shearRestartChart (ε a P : ℝ) (o : Bool) :
    InjOn (shearRestartChart o) (shearRestartParameterDomain ε a P) := by
  have H : InjOn (shearRestartChart false) (shearRestartParameterDomain ε a P) := by
    intro p hp q hq heq
    have h₂ := Real.log_injOn_pos hp.1.1.1 hq.1.1.1 (neg_injective (congrFun heq 1))
    have h₃ := Real.log_injOn_pos hp.1.2.1.1 hq.1.2.1.1 (neg_injective (congrFun heq 2))
    exact Prod.ext (Prod.ext h₂ h₃) (congrFun heq 0)
  cases o
  · exact H
  · intro p hp q hq heq
    exact H hp hq (mainWallReflectionEquiv.injective heq)

end
end

private theorem BianchiIX.radialRestartChart_parameter (k : Bool ⊕ Bool) (z : SectionCoordinates) :
    radialRestartChart k (radialRestartParameter k z) = radialPieceMap k z := by
  rcases k with neg | other
  · cases neg <;> ext i <;> fin_cases i <;>
      simp [radialRestartChart, radialRestartParameter, shearRestartChart, radialPieceMap,
        signedShearLogCoordinates, mainWallReflection]
  · cases other <;> ext i <;> fin_cases i <;>
      simp [radialRestartChart, radialRestartParameter, angularRestartChart, radialPieceMap,
        orderedAngularLogCoordinates, scaledAngularLogCoordinates, mainWallReflection]

private theorem BianchiIX.radialRestartParameter_selected {h q d ε P η σ Bcap : ℝ} {J : ℕ}
    {i : RadialPieceIndex} {z : SectionCoordinates} (hz : z ∈ radialPieceDomain d ε i)
    (hn : z ∉ restartRadialFailureFamily h q d ε P η J σ Bcap i) :
    radialRestartParameter i.1 z ∈ radialRestartParameterDomain (dyadicScale d i.2) ε P i.1 := by
  have hr : z 0 ∈ Icc (dyadicScale d i.2) (2 * dyadicScale d i.2) := by
    rcases i with ⟨neg | other, j⟩ <;> exact ⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩
  rcases i with ⟨neg | other, j⟩
  · cases neg <;> exact ⟨by by_contra hl; exact hn ⟨hr, Or.inl hl⟩, hr⟩
  · exact ⟨by by_contra hl; exact hn ⟨hr, Or.inl hl⟩, hr⟩


/-- Selection only uses the successful parts of the prescribed disjoint radial pieces. -/
theorem solution {h q d ε P η σ Bcap : ℝ} {J : ℕ}
    (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hF : ∀ i, MeasurableSet (restartRadialFailureFamily h q d ε P η J σ Bcap i))
    (hG : ∀ i : RadialPieceIndex, Measurable
      ((radialRestartParameterDomain (dyadicScale d i.2) ε P i.1).domRestrict
        (radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1))) :
    ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
      ∀ y ∈ mainWallOpenSection d \ radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap),
        ∃ i : RadialPieceIndex, ∃ z ∈ radialPieceDomain d ε i,
          z ∉ restartRadialFailureFamily h q d ε P η J σ Bcap i ∧ radialPieceMap i.1 z = y ∧
          W y = radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1
            (radialRestartParameter i.1 z) := by
  have Hext (i : RadialPieceIndex) : ∃ f : SectionCoordinates → CoreRestartData, Measurable f ∧
      ∀ p ∈ radialRestartParameterDomain (dyadicScale d i.2) ε P i.1,
        f (radialRestartChart i.1 p) =
          radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1 p := by
    apply exists_measurable_chart_extension (hG := hG i)
    · rcases i with ⟨neg | other, j⟩
      · exact measurableSet_shearRestartParameterDomain _ _ _
      · exact measurableSet_angularRestartParameterDomain _ _ _
    · rcases i with ⟨neg | other, j⟩
      · exact continuousOn_shearRestartChart _ _ _ _
      · exact continuousOn_angularRestartChart (dyadicScale_pos hd j) _
    · rcases i with ⟨neg | other, j⟩
      · exact injOn_shearRestartChart _ _ _ _
      · exact injOn_angularRestartChart (dyadicScale_pos hd j) _
  choose f hfm hfeq using Hext
  let F := restartRadialFailureFamily h q d ε P η J σ Bcap
  let S := fun i => radialFailurePiece d ε (fun j => (F j)ᶜ) i
  obtain ⟨W, hW, HW⟩ := exists_measurable_countable_selection S f
    (fun i => measurableSet_radialFailurePiece hd (fun j => (hF j).compl) i) hfm
  refine ⟨W, hW, ?_⟩
  intro y hy
  have hcover : y ∈ ⋃ i, S i := by
    obtain ⟨i, ⟨⟨z, hz, heq⟩, hn⟩, _⟩ := radialFailureSet_complement hd hε hε1 F hy
    rw [← heq, radialPieceInverse_map hd hz] at hn
    exact mem_iUnion.mpr ⟨i, z, ⟨hz, hn⟩, heq⟩
  obtain ⟨i, ⟨z, ⟨hz, hn⟩, rfl⟩, hval⟩ := HW y hcover
  refine ⟨i, z, hz, hn, rfl, hval.trans ?_⟩
  rw [← radialRestartChart_parameter]
  exact hfeq i _ (radialRestartParameter_selected hz hn)
