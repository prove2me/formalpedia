-- Prove2me | solution 1 for Formalism.ExtensionFiltration.covolume_full_assembly_weighted_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:07:27.048236+00:00
-- url     : https://prove2.me/submissions/ff2fdda1-70c8-41bc-b2ea-fd32d7a180da

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeEstimateAnchoredWeights
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeFullAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GlobalBoundRefinements
import Theorems.Thm_Formalism_ExtensionFiltration_weight_shift_constant
import Theorems.Thm_Formalism_ExtensionFiltration_la_le_three
import Theorems.Thm_Formalism_ExtensionFiltration_covolume_full_assembly_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ExtensionFiltration
open Finset Module NumberField
namespace Formalism.ExtensionFiltration
theorem _root_.solution : CovolumeEstimateOfAverageDegreeWeighted := by
  intro K _ _ _ _ d D hD hdD XW hXW M hM Pl _ w w0 c1 ua ι _ _ T DY A cs X cc z ρ R1 R2 Bn δ' h sl δc dc degc
    Ca Cb PPf e1 e2 muU muA muN muG mmax dA dB dN dg db Cf Cc cfl ε δ Q P Λ G P9
    pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η a La R CO
    a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hc1 hua hU1 hw hkS hkη hcard hm hf hq0 hqm hx heps hL hb hrd hrdL hchi0 hchiL hlx hll hLL0 hB0
    hCa hCb hCf hCc hww hS hR hkR hk hpq ha hLa hCO hOm
  have h0 := covolume_full_assembly_holds K d D hD hdD XW hXW M hM Pl w c1 ua ι T DY A cs X cc z ρ R1 R2 Bn δ' h sl δc dc degc
    Ca Cb PPf e1 e2 muU muA muN muG mmax dA dB dN dg db Cf Cc cfl ε δ Q P Λ G P9
    pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η
    a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hc1 hua hU1 hw hkS hkη hcard hm hf hq0 hqm hx heps hL hb hrd hrdL hchi0 hchiL hlx hll hLL0 hB0
    hCa hCb hCf hCc
  have h3 := la_le_three x eps L b a rd La hx hL hb ha hrd hrdL hlx hLa
  exact weight_shift_constant Pl w w0 _ pq logOm _ B0 llx La f m k (S + R) b (x ^ eps) CO h0 hww (by linarith) hpq hCO
    hOm h3 hcard hm hk (by linarith) hB0 hll
end Formalism.ExtensionFiltration
