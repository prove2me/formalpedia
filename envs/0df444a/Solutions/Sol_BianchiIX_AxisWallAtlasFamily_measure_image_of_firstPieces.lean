-- Prove2me | solution 1 for BianchiIX.AxisWallAtlasFamily.measure_image_of_firstPieces
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:32:51.654015+00:00
-- url     : https://prove2.me/submissions/789dd760-55c4-42c2-865f-b0097fa8ccca

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Flux
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisSectionMeasureData
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.MeasurableSpace.Prod

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiff_mainWallRadicand (h : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (mainWallRadicand h) := by
  unfold mainWallRadicand curvature
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_mainWallChart {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) (n : WithTop ℕ∞) : ContDiffAt ℝ n (mainWallChart h) y := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact ((contDiff_mainWallRadicand h n).contDiffAt.sqrt (ne_of_gt hy)).neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) y
  · exact contDiffAt_const
  · exact (contDiffAt_apply ℝ ℝ (1 : Fin 3) y).neg.exp
  · exact (contDiffAt_apply ℝ ℝ (2 : Fin 3) y).neg.exp

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.mainWallChart_negative {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) : mainWallChart h y 0 < 0 :=
  neg_neg_of_pos (Real.sqrt_pos.mpr hy)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.mainWallChartDensity_pos {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) : 0 < mainWallChartDensity h y := by
  have hp := mainWallChart_negative hy
  have hS : 0 ≤ shearSq (mainWallChart h y 0) (y 0) := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hH : 0 ≤ wallAmplitude h (Real.exp (-y 1)) (Real.exp (-y 2)) :=
    Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
  unfold mainWallChartDensity correctedSectionFluxDensity sectionFluxDensity
  exact div_pos (div_pos (by linarith) (mul_pos (by norm_num) (abs_pos.mpr (ne_of_lt hp))))
    (by linarith)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_axisWallChart (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) (n : WithTop ℕ∞) : ContDiffAt ℝ n (axisWallChart A h) y :=
  A.map.symm.contDiff.contDiffAt.comp y (contDiffAt_mainWallChart hy n)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.measurable_mainWallChartDensity (h : ℝ) : Measurable (mainWallChartDensity h) := by
  unfold mainWallChartDensity correctedSectionFluxDensity sectionFluxDensity shearSq
    mainWallChart mainWallRadicand curvature wallAmplitude
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.mainWallMeasure_apply {h : ℝ} {A : Set SectionCoordinates}
    (hA : MeasurableSet A) (hsub : A ⊆ mainWallChartDomain h) :
    mainWallMeasure h A = ∫⁻ y in A, ENNReal.ofReal (mainWallChartDensity h y) := by
  rw [mainWallMeasure, withDensity_apply _ hA, Measure.restrict_restrict_of_subset hsub]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.lintegral_mainWallMeasure {h : ℝ} {A : Set SectionCoordinates}
    (hA : MeasurableSet A) (hsub : A ⊆ mainWallChartDomain h) (f : SectionCoordinates → ℝ≥0∞) :
    (∫⁻ y in A, f y ∂mainWallMeasure h) =
      ∫⁻ y in A, ENNReal.ofReal (mainWallChartDensity h y) * f y := by
  rw [mainWallMeasure, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _
    (measurable_mainWallChartDensity h).ennreal_ofReal f hA (Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top)), Measure.restrict_restrict_of_subset hsub]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.continuousOn_coordinateTime : ContinuousOn P.coordinateTime P.source :=
  fun y hy => ((P.time_regular y hy).continuousAt.comp
    (contDiffAt_axisWallChart A (P.source_chart hy) 1).continuousAt).continuousWithinAt

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.measurableSet_image {E : Set SectionCoordinates} (hE : MeasurableSet E) (hsub : E ⊆ P.source) :
    MeasurableSet (P.map '' E) :=
  hE.image_of_continuousOn_injOn
    (fun y hy => (P.map_regular y (hsub hy)).continuousAt.continuousWithinAt) (P.injOn.mono hsub)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.measure_image (hh : 0 < h) {E : Set SectionCoordinates}
    (hE : MeasurableSet E) (hsub : E ⊆ P.source) :
    mainWallMeasure k (P.map '' E) = ∫⁻ y in E, ENNReal.ofReal (P.jacobian y) ∂mainWallMeasure h := by
  have hdiff : ∀ y ∈ E, HasFDerivWithinAt P.map (fderiv ℝ P.map y) E y :=
    fun y hy => ((P.map_regular y (hsub hy)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  rw [mainWallMeasure_apply (P.measurableSet_image hE hsub)
    (by rintro _ ⟨y, hy, rfl⟩; exact P.target_chart (hsub hy)),
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hE hdiff (P.injOn.mono hsub),
    lintegral_mainWallMeasure hE (hsub.trans P.source_chart)]
  apply lintegral_congr_ae
  apply ae_restrict_of_forall_mem hE
  intro y hy
  have hp := mainWallChartDensity_pos hh (P.source_chart (hsub hy))
  dsimp only
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul hp.le]
  congr 1
  unfold jacobian
  field_simp [ne_of_gt hp]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.axisFamilyMeasure_apply {ι : Type*} [MeasurableSpace ι] (k : ι → ℝ)
    {S : Set (ι × SectionCoordinates)} (hS : MeasurableSet S) :
    axisFamilyMeasure k S = ∑' i, mainWallMeasure (k i) (Prod.mk i ⁻¹' S) := by
  rw [axisFamilyMeasure, Measure.sum_apply _ hS]
  exact tsum_congr (fun _ => Measure.map_apply measurable_prodMk_left hS)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

private theorem BianchiIX.axisFamilyMeasure_image {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (k : ι → ℝ) (i : ι) {S : Set SectionCoordinates} (hS : MeasurableSet S) :
    axisFamilyMeasure k (Prod.mk i '' S) = mainWallMeasure (k i) S := by
  classical
  rw [axisFamilyMeasure_apply k ((measurableEmbedding_prodMk_left i).measurableSet_image.mpr hS)]
  have hpre (j : ι) : Prod.mk j ⁻¹' (Prod.mk i '' S) = if j = i then S else ∅ := by
    by_cases hji : j = i
    · subst j
      ext y
      simp
    · ext y
      simp [hji, Ne.symm hji]
  simp [hpre, apply_ite]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.measurableSet_eligible {E : Set SectionCoordinates} {I : Set ℝ}
    (hE : MeasurableSet E) (hI : MeasurableSet I) : MeasurableSet (P.eligible E I) := by
  have ht := P.continuousOn_coordinateTime.domRestrict.measurable
  have hm := (show ContinuousOn P.map P.source from
    fun y hy => (P.map_regular y hy).continuousAt.continuousWithinAt).domRestrict.measurable
  have H := P.isOpen_source.measurableSet.subtype_image ((hI.preimage ht).inter (hE.preimage hm))
  convert! H using 1
  ext y
  simp only [eligible, mem_ofPred_eq, mem_image, mem_inter_iff, mem_preimage, domRestrict_apply]
  aesop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallArrival
variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

private theorem BianchiIX.AxisWallArrival.measurable_delay {E : Set SectionCoordinates} {I : Set ℝ}
    (hE : MeasurableSet E) (hI : MeasurableSet I) : Measurable (P.delay E I) := by
  classical
  have hc : ContinuousOn (fun y => ENNReal.ofReal (P.coordinateTime y - t₀)) (P.eligible E I) :=
    ENNReal.continuous_ofReal.comp_continuousOn
      ((P.continuousOn_coordinateTime.mono (fun _ hy => hy.1)).sub continuousOn_const)
  exact hc.measurable_piecewise continuousOn_const (P.measurableSet_eligible hE hI)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.measurable_firstDelay [Countable ι] {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) : Measurable (C.firstDelay E I) :=
  Measurable.iInf (fun i => Measurable.iInf (fun n => ((C i).branch n).measurable_delay (hE i) hI))

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} [Encodable ι] {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.measurableSet_firstPiece {E : ι → Set SectionCoordinates} {I : Set ℝ}
    (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I) (q : ι × ℕ) :
    MeasurableSet (C.firstPiece E I q) := by
  have heq (r : ι × ℕ) : MeasurableSet {y |
      ((C r.1).branch r.2).delay (E r.1) I y = C.firstDelay E I y} :=
    measurableSet_eq_fun (((C r.1).branch r.2).measurable_delay (hE r.1) hI) (C.measurable_firstDelay hE hI)
  have hprev : MeasurableSet {y | ∀ r : ι × ℕ, Encodable.encode r < Encodable.encode q →
      ((C r.1).branch r.2).delay (E r.1) I y ≠ C.firstDelay E I y} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun r => MeasurableSet.iInter (fun _ => (heq r).compl))
  exact (((C q.1).branch q.2).measurableSet_eligible (hE q.1) hI).inter ((heq q).inter hprev)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} [Encodable ι] {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

private theorem BianchiIX.AxisWallAtlasFamily.firstPiece_pairwiseDisjoint (E : ι → Set SectionCoordinates) (I : Set ℝ) :
    Pairwise (fun q r => Disjoint (C.firstPiece E I q) (C.firstPiece E I r)) := by
  intro q r hqr
  rw [disjoint_left]
  intro y hyq hyr
  have hcode : Encodable.encode q ≠ Encodable.encode r := fun heq => hqr (Encodable.encode_injective heq)
  rcases lt_or_gt_of_ne hcode with hlt | hgt
  · exact hyr.2.2 q hlt hyq.2.1
  · exact hyq.2.2 r hgt hyr.2.1

end
end

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal
open BianchiIX.AxisWallAtlasFamily
variable {ι : Type*} [Encodable ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry} {h t₀ : ℝ} {k : ι → ℝ}
  (C : AxisWallAtlasFamily A B h k t₀)

omit [Nonempty ι]


theorem solution {E : ι → Set SectionCoordinates} {D S : Set SectionCoordinates}
    {I : Set ℝ} {R : SectionCoordinates → ι × SectionCoordinates} {j : SectionCoordinates → ℝ≥0∞}
    (hh : 0 < h) (hE : ∀ i, MeasurableSet (E i)) (hI : MeasurableSet I)
    (hcover : D ⊆ ⋃ q, C.firstPiece E I q) (hinj : InjOn R D)
    (hR : ∀ q : ι × ℕ, EqOn R (fun y => (q.1, ((C q.1).branch q.2).map y)) (C.firstPiece E I q))
    (hj : ∀ q : ι × ℕ, EqOn j (fun y => ENNReal.ofReal (((C q.1).branch q.2).jacobian y)) (C.firstPiece E I q))
    (hS : MeasurableSet S) (hSD : S ⊆ D) :
    MeasurableSet (R '' S) ∧ axisFamilyMeasure k (R '' S) = ∫⁻ y in S, j y ∂mainWallMeasure h := by
  let Q (q : ι × ℕ) := S ∩ C.firstPiece E I q
  have hQ (q : ι × ℕ) : MeasurableSet (Q q) := hS.inter (C.measurableSet_firstPiece hE hI q)
  have hQsource (q : ι × ℕ) : Q q ⊆ ((C q.1).branch q.2).source := fun _ hy => hy.2.1.1
  have hQD (q : ι × ℕ) : Q q ⊆ D := fun _ hy => hSD hy.1
  have hdisjoint : Pairwise (fun q r => Disjoint (Q q) (Q r)) :=
    fun _ _ hqr => (C.firstPiece_pairwiseDisjoint E I hqr).mono inter_subset_right inter_subset_right
  have hdecomp : S = ⋃ q, Q q := by
    ext y
    constructor
    · intro hy
      obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover (hSD hy))
      exact mem_iUnion.mpr ⟨q, hy, hq⟩
    · intro hy
      obtain ⟨q, hq⟩ := mem_iUnion.mp hy
      exact hq.1
  have himage (q : ι × ℕ) : R '' Q q = Prod.mk q.1 '' (((C q.1).branch q.2).map '' Q q) := by
    rw [← image_comp]
    exact ((hR q).mono inter_subset_right).image_eq
  have himageMeas (q : ι × ℕ) : MeasurableSet (R '' Q q) := by
    rw [himage q]
    exact (measurableEmbedding_prodMk_left q.1).measurableSet_image.mpr
      (((C q.1).branch q.2).measurableSet_image (hQ q) (hQsource q))
  have hRD : Pairwise (fun q r => Disjoint (R '' Q q) (R '' Q r)) := by
    intro q r hqr
    rw [disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hxy := hinj (hQD q hx) (hQD r hy) heq.symm
    exact disjoint_left.mp (hdisjoint hqr) hx (hxy ▸ hy)
  have hRdecomp : R '' S = ⋃ q, R '' Q q := by rw [hdecomp, image_iUnion]
  refine ⟨hRdecomp ▸ MeasurableSet.iUnion himageMeas, ?_⟩
  calc
    axisFamilyMeasure k (R '' S) = ∑' q, axisFamilyMeasure k (R '' Q q) := by
      rw [hRdecomp, measure_iUnion hRD himageMeas]
    _ = ∑' q, ∫⁻ y in Q q, j y ∂mainWallMeasure h := by
      apply tsum_congr
      intro q
      rw [himage q, axisFamilyMeasure_image k q.1
        (((C q.1).branch q.2).measurableSet_image (hQ q) (hQsource q)),
        ((C q.1).branch q.2).measure_image hh (hQ q) (hQsource q)]
      apply lintegral_congr_ae
      exact ae_restrict_of_forall_mem (hQ q) (fun y hy => (hj q hy.2).symm)
    _ = ∫⁻ y in S, j y ∂mainWallMeasure h := by
      rw [hdecomp, lintegral_iUnion hQ hdisjoint]
