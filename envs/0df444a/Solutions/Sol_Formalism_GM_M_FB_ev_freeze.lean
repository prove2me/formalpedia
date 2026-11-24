-- Prove2me | solution 1 for Formalism.GM.M.FB.ev_freeze
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:09.023227+00:00
-- url     : https://prove2.me/submissions/0328464e-37be-4c18-bc9a-6a374e171124

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ev_freezeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.M.FB
theorem _root_.solution (LL : Letters N) (ρ : Fin r) (n : ℕ) (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ev p ρ (freeze p LL ρ n f) = f := by
  simp only [freeze, map_mul, map_pow]
  have h1 : ev p ρ (X (Fin.last N, ρ)) = 1 := by simp [ev]
  have h2 : ev p ρ (aeval (freezeSub p LL ρ) f) = f := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have : (fun i => (ev p ρ) (freezeSub p LL ρ i)) = X := funext (ev_freezeSub LL ρ)
    rw [this, MvPolynomial.aeval_X_left_apply]
  rw [h1, h2, one_pow, one_mul]
end Formalism.GM.M.FB
