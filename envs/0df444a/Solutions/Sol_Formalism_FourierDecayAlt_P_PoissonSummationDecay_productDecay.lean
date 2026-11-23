-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PoissonSummationDecay.productDecay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:04.34849+00:00
-- url     : https://prove2.me/submissions/63f5cf53-fec3-4db2-a5db-fd369c429997

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_gP_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_gP_mul_le_gP_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_le_gP_of_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_gP_summable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal
section Summable
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]
end Summable
section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type} [Fintype ι]
end
private theorem nonneg_of_norm_le_mul_gP {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type} [Fintype ι] (π : ι → V →L[ℝ] ℂ) (φ : V → ℂ) (C : ℝ)
    (hφ' : ∀ c, ‖φ c‖ ≤ C * gP π c) : 0 ≤ C := by
  by_contra hneg
  have hneg' : C < 0 := lt_of_not_ge hneg
  have h1 : C * gP π 0 < 0 := mul_neg_of_neg_of_pos hneg' (gP_pos π 0)
  have h2 : ‖φ 0‖ ≤ C * gP π 0 := hφ' 0
  have h3 : 0 ≤ ‖φ 0‖ := norm_nonneg _
  linarith
private theorem gP_add_mul_prod_inv_le_gP_of_norm_le {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type} [Fintype ι] (π : ι → V →L[ℝ] ℂ) (R : ℝ) (y x : V)
    (hx : ‖-x‖ ≤ R) : gP π (y + x) * ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹ ≤ gP π y := by
  calc gP π (y + x) * ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹
      ≤ gP π (y + x) * gP π (-x) :=
        mul_le_mul_of_nonneg_left (le_gP_of_norm_le π R (-x) hx) (gP_pos _ _).le
    _ ≤ gP π (y + x + -x) := gP_mul_le_gP_add π _ _
    _ = gP π y := by rw [add_neg_cancel_right]
private theorem norm_add_le_mul_gP_div_prod_of_norm_le {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type} [Fintype ι] (π : ι → V →L[ℝ] ℂ) (φ : V → ℂ) (C R : ℝ)
    (hC : 0 ≤ C) (hR0 : 0 < R) (hφ' : ∀ c, ‖φ c‖ ≤ C * gP π c) (y x : V) (hx : ‖x‖ ≤ R) :
    ‖φ (y + x)‖ ≤ C * gP π y / ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹ := by
  have hm : 0 < ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹ := by
    refine Finset.prod_pos fun v _ => inv_pos.mpr (pow_pos ?_ 3)
    have := mul_nonneg (norm_nonneg (π v)) hR0.le
    linarith
  have hx' : ‖-x‖ ≤ R := by rw [norm_neg]; exact hx
  have h1 := gP_add_mul_prod_inv_le_gP_of_norm_le π R y x hx'
  have h3 : gP π (y + x) ≤ gP π y / ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹ := (le_div_iff₀ hm).mpr h1
  calc ‖φ (y + x)‖ ≤ C * gP π (y + x) := hφ' _
    _ ≤ C * (gP π y / ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹) := mul_le_mul_of_nonneg_left h3 hC
    _ = C * gP π y / ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹ := (mul_div_assoc _ _ _).symm
private theorem locSummable_of_norm_le_mul_gP {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι]
    (π : ι → V →L[ℝ] ℂ) (hπ : Function.Bijective fun (c : V) (v : ι) => π v c)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (φ : V → ℂ) (C : ℝ)
    (hφ' : ∀ c, ‖φ c‖ ≤ C * gP π c) : LocSummable Λ φ := by
  have hC : 0 ≤ C := nonneg_of_norm_le_mul_gP π φ C hφ'
  intro Kc hK
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.subset_closedBall_lt 0 0
  have hs : Summable (fun l : Λ => C * gP π (l : V) / ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹) :=
    ((gP_summable π hπ Λ).mul_left C).div_const _
  refine ⟨_, hs, fun l x hx => ?_⟩
  have hxR : ‖x‖ ≤ R := by
    have := hR hx
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  exact norm_add_le_mul_gP_div_prod_of_norm_le π φ C R hC hR0 hφ' (l : V) x hxR
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
theorem _root_.solution : ProductDecaySummable := by
  intro V _ _ _ ι _ π hπ Λ _ _ φ C hφ
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  exact locSummable_of_norm_le_mul_gP π hπ Λ φ C hφ
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
