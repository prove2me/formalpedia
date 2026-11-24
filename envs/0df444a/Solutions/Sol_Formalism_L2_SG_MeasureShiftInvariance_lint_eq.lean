-- Prove2me | solution 1 for Formalism.L2.SG.MeasureShiftInvariance.lint_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:24:33.320902+00:00
-- url     : https://prove2.me/submissions/af73a0b4-1b7a-4225-bbd2-7bccf9993901

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_ind_mul_right
import Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_ind_inv_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
namespace Formalism.L2.SG.MeasureShiftInvariance
section SF
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable (h : G)
end SF
section Unfold
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]
private theorem measurable_one_ennreal : Measurable (1 : G → ℝ≥0∞) := by
  first
  | exact measurable_one
  | exact measurable_const
end Unfold
section Boch
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]
end Boch
section Shift
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
end Shift
section ShiftG
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
end ShiftG
end Formalism.L2.SG.MeasureShiftInvariance
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.MeasureShiftInvariance
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]
namespace Formalism.L2.SG.MeasureShiftInvariance
theorem _root_.solution {A B : Set G} (hA : MeasurableSet A) (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hcB : ∀ x, ν {r | r * x ∈ B} = c) (hcA : ∀ y, ν {r | r⁻¹ * y ∈ A} = c)
    (g : G → ℝ≥0∞) (hg : AEMeasurable g μ) (hinv : ∀ᵐ r ∂ν, ∀ x, g (r⁻¹ * x) = g x) :
    c * ∫⁻ x in A, g x ∂μ = c * ∫⁻ x in B, g x ∂μ := by
  have h1m := (measurable_one_ennreal (G := G))
  have hL : c * ∫⁻ x in A, g x ∂μ = ∫⁻ x, ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) x * B.indicator (1 : G → ℝ≥0∞) (r * x) * g x ∂ν ∂μ := by
    first
    | rw [← lintegral_indicator hA]
    | rw [← lintegral_indicator _ hA]
    rw [← lintegral_const_mul'' c (hg.indicator hA)]
    refine lintegral_congr fun x => ?_
    have hm : Measurable fun r : G => B.indicator (1 : G → ℝ≥0∞) (r * x) :=
      (h1m.indicator hB).comp (measurable_mul_const x)
    have h2 : ∫⁻ r, B.indicator (1 : G → ℝ≥0∞) (r * x) ∂ν = c := by
      rw [← hcB x]
      first
      | exact lintegral_indicator_one (hB.preimage (measurable_mul_const x))
      | (rw [ind_mul_right x]; exact lintegral_indicator_one (hB.preimage (measurable_mul_const x)))
    calc c * A.indicator g x
        = (A.indicator (1 : G → ℝ≥0∞) x * g x) * ∫⁻ r, B.indicator (1 : G → ℝ≥0∞) (r * x) ∂ν := by
          rw [h2]
          by_cases hx : x ∈ A <;> simp [Set.indicator_apply, hx] <;> ring
      _ = ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) x * B.indicator (1 : G → ℝ≥0∞) (r * x) * g x ∂ν := by
          rw [← lintegral_const_mul _ hm]
          refine lintegral_congr fun r => ?_
          ring
  have hR : c * ∫⁻ y in B, g y ∂μ = ∫⁻ y, ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) * B.indicator (1 : G → ℝ≥0∞) y * g y ∂ν ∂μ := by
    first
    | rw [← lintegral_indicator hB]
    | rw [← lintegral_indicator _ hB]
    rw [← lintegral_const_mul'' c (hg.indicator hB)]
    refine lintegral_congr fun y => ?_
    have hm : Measurable fun r : G => A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) :=
      (h1m.indicator hA).comp (measurable_inv.mul_const y)
    have h2 : ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) ∂ν = c := by
      rw [← hcA y]
      first
      | exact lintegral_indicator_one (hA.preimage (measurable_inv.mul_const y))
      | (rw [ind_inv_mul y]; exact lintegral_indicator_one (hA.preimage (measurable_inv.mul_const y)))
    calc c * B.indicator g y
        = (B.indicator (1 : G → ℝ≥0∞) y * g y) * ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) ∂ν := by
          rw [h2]
          by_cases hy : y ∈ B <;> simp [Set.indicator_apply, hy] <;> ring
      _ = ∫⁻ r, A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) * B.indicator (1 : G → ℝ≥0∞) y * g y ∂ν := by
          rw [← lintegral_const_mul _ hm]
          refine lintegral_congr fun r => ?_
          ring
  have h3 : AEMeasurable (fun p : G × G => g p.1) (μ.prod ν) := by
    first
    | exact hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    | exact hg.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν))
    | exact hg.comp_fst
    | exact hg.fst_prod
    | exact hg.fst
  have hF : AEMeasurable (Function.uncurry fun (x r : G) =>
      A.indicator (1 : G → ℝ≥0∞) x * B.indicator (1 : G → ℝ≥0∞) (r * x) * g x) (μ.prod ν) := by
    have k1 : Measurable fun p : G × G => A.indicator (1 : G → ℝ≥0∞) p.1 :=
      (h1m.indicator hA).comp measurable_fst
    have k2 : Measurable fun p : G × G => B.indicator (1 : G → ℝ≥0∞) (p.2 * p.1) :=
      (h1m.indicator hB).comp (measurable_snd.mul measurable_fst)
    exact (k1.aemeasurable.mul k2.aemeasurable).mul h3
  have hG : AEMeasurable (Function.uncurry fun (y r : G) =>
      A.indicator (1 : G → ℝ≥0∞) (r⁻¹ * y) * B.indicator (1 : G → ℝ≥0∞) y * g y) (μ.prod ν) := by
    have k1 : Measurable fun p : G × G => A.indicator (1 : G → ℝ≥0∞) (p.2⁻¹ * p.1) :=
      (h1m.indicator hA).comp (measurable_snd.inv.mul measurable_fst)
    have k2 : Measurable fun p : G × G => B.indicator (1 : G → ℝ≥0∞) p.1 :=
      (h1m.indicator hB).comp measurable_fst
    exact (k1.aemeasurable.mul k2.aemeasurable).mul h3
  rw [hL, hR, lintegral_lintegral_swap hF, lintegral_lintegral_swap hG]
  refine lintegral_congr_ae ?_
  filter_upwards [hinv] with r hr
  try dsimp only
  rw [← lintegral_mul_left_eq_self
    (fun x => A.indicator (1 : G → ℝ≥0∞) x * B.indicator (1 : G → ℝ≥0∞) (r * x) * g x) r⁻¹]
  refine lintegral_congr fun y => ?_
  first
  | simp only [mul_inv_cancel_left, hr]
  | simp [hr]
end Formalism.L2.SG.MeasureShiftInvariance
