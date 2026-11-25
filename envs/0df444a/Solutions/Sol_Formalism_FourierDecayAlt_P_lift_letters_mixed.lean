-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lift_letters_mixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:54:43.873812+00:00
-- url     : https://prove2.me/submissions/a16cf6bc-0c91-4e80-9b92-0de56b57b521

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdBelowOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx11_chebToThreshold
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx11_mix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx11
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : LiftLettersMix := by
  intro hLW hCS R M _ _ _ _ _ _ Ξ n s L f pl dat A₀ A₀v e t t' α β X X' κ len Mj ov be hs hκ hlen hbt
    h0 he ht hA hA0 hB hBv ho hF
  have hlt : ∀ a, α a < β a := fun a => by have := hbt a; linarith
  have hd : 1 ≤ 2 * n + s := by omega
  have hid := hLW R M Ξ n s L dat A₀ A₀v e t t' (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n + s)) X X'
    hs h0 he ht hA hA0 hB hBv (fun a => (hCS (α a) (β a) (2 * n + s) (hlt a) hd).1)
  obtain ⟨m1, m2, m3⟩ := mix (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n + s))
    (fun a => (1 / 2) * (4 / (β a - α a)) ^ (2 * n + s))
    (fun a => (hCS (α a) (β a) (2 * n + s) (hlt a) hd).2)
    (fun a => by have := hlt a; have h : 0 < β a - α a := by linarith
                 positivity)
    _ _ hid _ Mj hF
  refine ⟨m1, m2, ?_⟩
  have hn : ∀ a, ‖e a * (1 / t a - 1 / t' a)‖ = ‖1 / t a - 1 / t' a‖ := by
    intro a
    rw [norm_mul]
    rcases he a with h | h <;> rw [h] <;> simp
  rw [norm_mul, norm_prod, Finset.prod_congr rfl fun a _ => hn a] at m3
  exact chebToThreshold L f (2 * n + s) pl (fun a => ‖1 / t a - 1 / t' a‖) α β κ len ov be _ _ _
    hκ hlen hbt ho m3 le_rfl
end Formalism.FourierDecayAlt.P
