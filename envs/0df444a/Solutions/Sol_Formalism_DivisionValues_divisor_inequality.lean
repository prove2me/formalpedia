-- Prove2me | solution 1 for Formalism.DivisionValues.divisor_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:12.944599+00:00
-- url     : https://prove2.me/submissions/22989520-d0ff-4a0d-b6ab-a246b791fb4d

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementK
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivAssembly
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AbsorbE
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Theorems.Thm_Formalism_DivisionValues_divisor_inequality_assembly
import Theorems.Thm_Formalism_DivisionValues_error_absorption


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : TheoremDivIneq := by
  intro J Pl _ _ TT _ muC mu0 Fo hu hP mlam logT hK aT phν nν fa x eps L b a rd La B0 Nc xe m f k N S
    tt η w'' b' dC lam0 C0 Lpass Eb e6 eP logOm eK pq w eE δ
    h1 h2 h3 h4 h5 h6 h7 h8
    hx heps hL hb ha hrd1 hlogrd hlogx hLa hB0 hNc hxeb hJ hPl hm hf hk hN hS ht hη hdC
    hw hpq hOm hlam hNd hm3 hmηN hkN hkS hmt hNw hb'N hmkb' hC0 hLp hEb heK he6 heP heE hδ
  have hD := divisor_inequality_assembly J Pl TT muC mu0 Lpass 0 Fo Eb hu hP mlam e6 eP logOm logT k hK eK pq aT
    w phν nν fa eE δ h1 (by linarith) (by linarith) h4 h5 h6 h7 h8
  have hA := error_absorption J Pl TT x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' dC lam0 C0 Lpass
    Eb e6 eP logOm k eK pq w eE δ hx heps hL hb ha hrd1 hlogrd hlogx hLa hB0 hNc hxeb hJ hPl hm hf hk
    hN hS ht hη hdC hw hpq hOm hlam hNd hm3 hmηN hkN hkS hmt hNw hb'N hmkb' hC0 hLp hEb heK he6 heP
    heE hδ
  rw [hJ] at hD
  linarith
end Formalism.DivisionValues
