-- Prove2me | solution 1 for Formalism.ExtensionFiltration.covolume_assembly_of_slope_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:26:47.030882+00:00
-- url     : https://prove2.me/submissions/cb92efb8-bac1-48c6-9bd9-bbd58e7bbb76

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_Assembly
import Theorems.Thm_Formalism_ExtensionFiltration_covolume_from_slope_holds
import Theorems.Thm_Formalism_ExtensionFiltration_slope_lower_chain_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField
open Formalism Formalism.ExtensionFiltration
namespace Formalism.ExtensionFiltration
theorem _root_.solution (hLM : LcvMu) : CovolumeEstimateOfSlopeChain := by
  intro K _ _ _ _ d D hD hdD XW hXW M hM Pl _ w c1 ua muU muA muN muG mmax dA dB dN dg db
    C1 Cf Cc cfl ε δ Q P Λ G P9 pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η
    h41 hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hc1 hua hU1 hw hkS hkη hcard hm hf hq0 hqm hx heps hL hb hrd hrdL hchi0 hchiL hlx hll hLL0 hB0
    hC1 hCf hCc
  subst hdD
  have hL1 : 1 ≤ L := by rw [hL]; exact Real.one_le_rpow hx heps.le
  have hb0 : 0 < b := by rw [hb]; exact Real.exp_pos _
  have hrd0 : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogb : Real.log (b * rd) = L + Real.log rd := by
    rw [Real.log_mul (by positivity) (by positivity), hb, Real.log_exp]
  have hLLge : L + Real.log rd ≤ LL0 := by
    rw [hLL0, hlogb]
    have : L + Real.log rd ≤ (L + Real.log rd) * llx := le_mul_of_one_le_right (by linarith) hll
    linarith
  have hchain := slope_lower_chain_holds Pl w c1 ua muU muA muN muG
    (Formalism.HN.muDef (Pi.basisFun K (Fin d)) XW M) mmax dA dB dN dg db C1 Cf LL0 L b rd m q' cfl ε δ Q P Λ G P9
    h41 hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hC1 hCf hq0 hqm (fun τ => (hw τ).1) (fun τ => (hua τ).1) hrd0 (by linarith) (by linarith) hU1 hb0.le
  have hlcv : Formalism.DivisionValues.lcv XW M / (d : ℝ) = -Formalism.HN.muDef (Pi.basisFun K (Fin d)) XW M := by
    rw [hLM K d hD XW hXW M hM]
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp
  refine covolume_from_slope_holds Pl w c1 ua (Formalism.DivisionValues.lcv XW M / (d : ℝ)) (C1 + 3 * Cf) Cc pq q' logOm x eps L b rd
    Lchi llx LL0 B0 f m k S η ?_ hc1 ?_ hw hkS hkη hcard hm hf hq0 hqm hx heps hL hb hrd hrdL hchi0 hchiL
    hlx hll hLL0 hB0 (by positivity) hCc
  · rw [hlcv]; linarith
  · intro τ
    refine ⟨?_, (hua τ).2⟩
    have h1 := (hua τ).1
    have h2 : 0 ≤ m * w τ := mul_nonneg (by linarith) (hw τ).1
    linarith
end Formalism.ExtensionFiltration
