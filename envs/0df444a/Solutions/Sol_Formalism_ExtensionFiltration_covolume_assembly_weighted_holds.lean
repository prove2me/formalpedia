-- Prove2me | solution 1 for Formalism.ExtensionFiltration.covolume_assembly_weighted_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:07:24.766286+00:00
-- url     : https://prove2.me/submissions/80b9c71c-921e-46ed-ad09-e274998e6cb7

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
import Theorems.Thm_Formalism_ExtensionFiltration_covolume_assembly_holds


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
theorem _root_.solution : CovolumeEstimateAnchoredWeights := by
  intro K _ _ _ _ d D hD hdD XW hXW M hM Pl _ w w0 c1 ua muU muA muN muG mmax dA dB dN dg db
    C1 Cf Cc cfl ε δ Q P Λ G P9 pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η a La R CO
    h41 hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hc1 hua hU1 hw hkS hkη hcard hm hf hq0 hqm hx heps hL hb hrd hrdL hchi0 hchiL hlx hll hLL0 hB0
    hC1 hCf hCc hww hS hR hkR hk hpq ha hLa hCO hOm
  have h := covolume_assembly_holds K d D hD hdD XW hXW M hM Pl w c1 ua muU muA muN muG mmax dA dB dN dg db
    C1 Cf Cc cfl ε δ Q P Λ G P9 pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η
    h41 hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hc1 hua hU1 hw hkS hkη hcard hm hf hq0 hqm hx heps hL hb hrd hrdL hchi0 hchiL hlx hll hLL0 hB0
    hC1 hCf hCc
  have h3 := la_le_three x eps L b a rd La hx hL hb ha hrd hrdL hlx hLa
  exact weight_shift_constant Pl w w0 _ pq logOm _ B0 llx La f m k (S + R) b (x ^ eps) CO h hww (by linarith) hpq hCO
    hOm h3 hcard hm hk (by linarith) hB0 hll
end Formalism.ExtensionFiltration
