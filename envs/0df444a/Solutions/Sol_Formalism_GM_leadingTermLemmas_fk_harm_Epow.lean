-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_harm_Epow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:21.377378+00:00
-- url     : https://prove2.me/submissions/325f6fc6-b916-49c2-a79d-6c53c5a8c2a1

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_symm
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_zero_right
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_E_pow
import Theorems.Thm_Formalism_GM_leadingTermLemmas_Fpow_harm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K σ : Type} [Field K] [CharZero K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
  (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution {g : MvPolynomial σ K} (hF : tieF w e g = 0) {t : ℕ} (ht : 1 ≤ t)
    (u : MvPolynomial σ K) : fk g ((tieE w e ^ t) u) = 0 := by
  rw [fk_symm, fk_E_pow, Fpow_harm hw he hwe hF ht, fk_zero_right]
end Formalism.GM.leadingTermLemmas
