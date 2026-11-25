-- Prove2me | solution 1 for Formalism.LIFT.uClaim_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:20:59.247397+00:00
-- url     : https://prove2.me/submissions/02a21b2a-d386-46fb-a340-ec7494638726

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_main
import Theorems.Thm_Formalism_WindowSums_valuation_zpow_sub_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
namespace Formalism.LIFT
theorem _root_.solution (hU : UGraded) (_hG : GradedStep) : UClaim := by
  intro ℓ _ A _ _ B M D _ _ _ _ W s J hs hs2 hv hJ h1 h2 h3 h4
  have hcG : (∏ i ∈ Finset.Icc 1 M, ((B.u : ℤ_[ℓ]) ^ i - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    have hi0 : (i : ℤ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hi).1
      omega
    have := (Formalism.WindowSums.valuation_zpow_sub_one ℓ B.u s hs hs2 hv (i : ℤ) hi0).1
    simpa using this
  have hP : Polynomial.eval 1
      (∏ j ∈ J, (Polynomial.X - Polynomial.C (((B.u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) =
      ∏ j ∈ J, (1 - ((B.u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) := by
    simp [Polynomial.eval_prod]
  rw [← hP]
  exact CocyclePolynomialSubmodules.main W _ _ hcG (hU ℓ A B M D W M) h1 h2 h3 h4
end Formalism.LIFT
