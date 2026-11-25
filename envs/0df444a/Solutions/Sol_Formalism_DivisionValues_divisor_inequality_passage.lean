-- Prove2me | solution 1 for Formalism.DivisionValues.divisor_inequality_passage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:27:26.371391+00:00
-- url     : https://prove2.me/submissions/107ee9bf-3909-43be-ae26-04647277aea4

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Theorems.Thm_Formalism_DivisionValues_passage_arithmetic
import Theorems.Thm_Formalism_DivisionValues_passage_size
import Theorems.Thm_Formalism_DivisionValues_divisor_inequality


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : DivIneqPassage := by
  intro J Pl _ _ TT _ muC mu0 Fo hu hP mlam logT hK aT phν nν fa x eps L b a rd La B0 Nc xe m f k N S
    tt η w'' b' dC lam0 C0 Eb e6 eP logOm eK pq w eE δ logκ HH0 de c1 c2 c3 Cd r g p2 pF pN hc1 hc2
    hc3 hCd hr hde hg hl0 hcmp hHH hpq hF hNc hA hB h1 hhu hK' hfa hP' hph hnν hx heps hL hb ha hrd
    hlrd hlx hLa hB0 hNc0 hxe hJ hPl hm hf hk hN hS htt hη hdC hw hpqk hlogOm hlb hN2 hm3 hmη hkN
    hkS hmt hNw hbN hmkb hC0 hEb heK he6 heP heE hδ
  have hL1 : 1 ≤ L := by
    rw [hL]
    exact Real.one_le_rpow hx heps.le
  have hb1 : 1 ≤ b := by
    rw [hb]
    exact Real.one_le_exp (by linarith)
  have hb0 : 0 ≤ b := by linarith
  have hxe0 : 0 ≤ xe := le_trans (Real.rpow_nonneg (by linarith) eps) hxe
  have hf0 : 0 ≤ f := by linarith
  have hmu : mu0 ≤ logκ + (2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) * b :=
    (passage_size J Pl mu0 logκ Fo Fo Eb logOm La (2 * b) b N m f C0 xe B0 Nc pF pN x eps pq w
      h1 hJ hPl hpq (by linarith) hw hlogOm le_rfl hC0 hEb).2 le_rfl hb0 hF hNc hB0 hxe hxe0
  obtain ⟨_, _, hmuC, _, hLp⟩ := passage_arithmetic muC mu0 HH0 lam0 logκ de c1 c2 c3 Cd f r g k b
    (2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) p2 C0 hc1 hc2 hCd hf0 hr hk hb1
    hde hg hl0 hlb hmu hHH hA hB hcmp hc3
  have key := divisor_inequality J Pl TT (muC - logκ) (mu0 - logκ) Fo (hP + ∑ j, hK j - mlam) hP
    mlam logT hK aT phν nν fa x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' dC lam0 C0
    (c1 * de * (mu0 + HH0 + c2 * lam0) + c3 * lam0) Eb e6 eP logOm eK pq w eE δ
    (by linarith) (by linarith) rfl hK' hfa hP' hph hnν hx heps hL hb ha hrd hlrd hlx hLa hB0 hNc0
    hxe hJ hPl hm hf hk hN hS htt hη hdC hw hpqk hlogOm hlb hN2 hm3 hmη hkN hkS hmt hNw hbN hmkb hC0
    hLp hEb heK he6 heP heE hδ
  linarith
end Formalism.DivisionValues
