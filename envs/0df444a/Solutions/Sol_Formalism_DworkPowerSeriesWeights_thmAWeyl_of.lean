-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.thmAWeyl_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:05.431824+00:00
-- url     : https://prove2.me/submissions/51180154-5b69-4556-8d5c-12cbdcffd080

import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_coefficient_bound_membership

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (hG : ThmAGauss) : ThmAWeyl := by
  unfold ThmAWeyl
  unfold ThmAGauss at hG
  intro l _ d N0 N1 _ h3 h2 hE K0 hU ζ hζ be hB g hg0 hgs U hUi ε hε TT colN p hp hp1 I nu1 nu2 size
    h1 h2' h3' a ha hsa hlog hSB c hc
  have hbd := hG l d N0 N1 h3 h2 hE K0 hU ζ hζ be hB g hg0 hgs U hUi ε hε TT colN p hp hp1 I nu1
    nu2 size h1 h2' h3' a ha hsa hlog
  have hCB := coefficient_bound_membership
  unfold CBMem at hCB
  have hmem := hCB _ d N0 N1 colN p hp I (thetaZ g U ε be)
  unfold SBSat at hSB
  refine hSB _ (Submodule.smul_mem _ c⁻¹ hmem) fun n => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul, norm_inv]
  have hx := le_trans (hbd n) hc
  rcases (norm_nonneg c).eq_or_lt with h0 | hpos
  · rw [← h0, inv_zero, zero_mul]
    exact zero_le_one
  · calc _ ≤ ‖c‖⁻¹ * ‖c‖ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (norm_nonneg c))
      _ = 1 := inv_mul_cancel₀ hpos.ne'
end Formalism.DworkPowerSeriesWeights
