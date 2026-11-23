-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PoissonSummationDecay.gP_summable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:40.39196+00:00
-- url     : https://prove2.me/submissions/dd9b3a83-1a4e-42a4-99ae-c59048ed53a6

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_gP_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_gP_mul_le_gP_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_le_gP_of_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_gP_integrable
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type} [Fintype ι]
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
theorem _root_.solution [MeasurableSpace V] [BorelSpace V] (π : ι → V →L[ℝ] ℂ)
    (hπ : Function.Bijective fun (c : V) (v : ι) => π v c)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Summable (fun l : Λ => gP π l) := by
  let b := Module.Free.chooseBasis ℤ Λ
  have hD := ZLattice.isAddFundamentalDomain b (volume : Measure V)
  have hDb := ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ Λ)
  have hDm := ZSpan.fundamentalDomain_measurableSet (b.ofZLatticeBasis ℝ Λ)
  obtain ⟨R, hR0, hR⟩ := hDb.subset_closedBall_lt 0 0
  have hm : 0 < ∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹ :=
    Finset.prod_pos fun v _ => inv_pos.mpr (pow_pos (by positivity) 3)
  have hvol : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ)) ≠ 0 := by
    intro h0
    have h1 := ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hD
    have h2 := ZLattice.covolume_pos Λ volume
    rw [h1, Measure.real, h0, ENNReal.toReal_zero] at h2
    exact lt_irrefl _ h2
  haveI : VAddInvariantMeasure Λ V (volume : Measure V) := ⟨fun c s _ => measure_preimage_add volume (c : V) s⟩
  have hint := (gP_integrable π hπ).lintegral_lt_top
  rw [hD.lintegral_eq_tsum''] at hint
  have hge : ∀ l : Λ, ENNReal.ofReal (gP π l) *
      (ENNReal.ofReal (∏ v, ((1 + ‖π v‖ * R) ^ 3)⁻¹) * volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ))) ≤
      ∫⁻ x in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ Λ), ENNReal.ofReal (gP π (l +ᵥ x)) := by
    intro l
    rw [← mul_assoc, ← ENNReal.ofReal_mul (gP_pos π l).le, ← setLIntegral_const]
    refine setLIntegral_mono' hDm fun x hx => ENNReal.ofReal_le_ofReal ?_
    have hx' : ‖x‖ ≤ R := by simpa using hR hx
    exact (mul_le_mul_of_nonneg_left (le_gP_of_norm_le π R x hx') (gP_pos π l).le).trans (gP_mul_le_gP_add π l x)
  have htop : ∑' l : Λ, ENNReal.ofReal (gP π l) ≠ ⊤ := by
    intro htop
    have hle := ENNReal.tsum_le_tsum hge
    rw [ENNReal.tsum_mul_right, htop, ENNReal.top_mul (mul_ne_zero (ENNReal.ofReal_pos.mpr hm).ne' hvol)] at hle
    exact absurd (lt_of_le_of_lt hle hint) (lt_irrefl _)
  have := ENNReal.summable_toReal htop
  refine this.congr fun l => ?_
  exact ENNReal.toReal_ofReal (gP_pos π l).le
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
