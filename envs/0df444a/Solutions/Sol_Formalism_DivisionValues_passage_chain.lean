-- Prove2me | solution 1 for Formalism.DivisionValues.passage_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:30:14.119398+00:00
-- url     : https://prove2.me/submissions/413d555d-c976-42a4-88f9-35cffbbf765b

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Theorems.Thm_Formalism_DivisionValues_passage_arithmetic
import Theorems.Thm_Formalism_DivisionValues_passage_size

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
theorem _root_.solution : PassageChain := by
  intro J Pl _ _ muC mu0 HH0 lam0 logκ de Cd r g k p2 Fo Fabs Eb logOm La W b N m f C0 xe B0 Nc pF
    pN x eps pq w h1 hJ hPl hpq hW hw hLa hFo hC0 hEb hWb hF hNc hB0 hxe hxe0 hHH hCd hr hk hb hde
    hg hl0 hlb hA hB hcmp
  have hb0 : 0 ≤ b := by linarith
  have hf0 : 0 ≤ f := le_trans (Nat.cast_nonneg _) hPl
  have hsz := passage_size J Pl mu0 logκ Fo Fabs Eb logOm La W b N m f C0 xe B0 Nc pF pN x eps
    pq w h1 hJ hPl hpq hW hw hLa hFo hC0 hEb
  have hmu := hsz.2 hWb hb0 hF hNc hB0 hxe hxe0
  obtain ⟨_, _, hmuC, hd1, hLp⟩ := passage_arithmetic muC mu0 HH0 lam0 logκ de 3 28 28 Cd f r g k b
    (2 * m * f * N * La + 2 * pF + C0 * m * xe * (f * m * xe + pN)) p2 28 (by norm_num) (by norm_num)
    hCd hf0 hr hk hb hde hg hl0 hlb hmu hHH hA hB hcmp le_rfl
  exact ⟨hmuC, hLp, by linarith⟩
end Formalism.DivisionValues
