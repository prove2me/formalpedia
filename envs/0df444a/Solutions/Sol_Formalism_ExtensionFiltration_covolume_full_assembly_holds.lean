-- Prove2me | solution 1 for Formalism.ExtensionFiltration.covolume_full_assembly_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:01:33.386032+00:00
-- url     : https://prove2.me/submissions/ba301fed-db0b-48e6-ad7d-5d3eec33ad93

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_StatementF
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SumComponents
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeFullAssemblyHolds
import Theorems.Thm_Formalism_ExtensionFiltration_mean_height_sum_bound_holds
import Theorems.Thm_Formalism_ExtensionFiltration_covolume_assembly_holds


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
theorem _root_.solution : CovolumeEstimateOfAverageDegree := by
  intro K _ _ _ _ d D hD hdD XW hXW M hM Pl _ w c1 ua ι _ _ T DY A cs X cc z ρ R1 R2 Bn δ' h sl δc dc degc
    Ca Cb PPf e1 e2 muU muA muN muG mmax dA dB dN dg db Cf Cc cfl ε δ Q P Λ G P9
    pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η
    a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
    hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hc1 hua hU1 hw hkS hkη hcard hm hf hq0 hqm hx heps hL hb hrd hrdL hchi0 hchiL hlx hll hLL0 hB0
    hCa hCb hCf hCc
  have h41 := mean_height_sum_bound_holds ι T DY A cs X cc z ρ R1 R2 Bn δ' h sl δc dc degc LL0 (∑ τ, ua τ) b Ca Cb PPf
    e1 e2 muU a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24
  exact covolume_assembly_holds K d D hD hdD XW hXW M hM Pl w c1 ua muU muA muN muG mmax dA dB dN dg db
    (Ca + Cb) Cf Cc cfl ε δ Q P Λ G P9 pq q' logOm x eps L b rd Lchi llx LL0 B0 f m k S η
    h41 hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hc1 hua hU1 hw hkS hkη hcard hm hf hq0 hqm hx heps hL hb hrd hrdL hchi0 hchiL hlx hll hLL0 hB0
    (by positivity) hCf hCc
end Formalism.ExtensionFiltration
