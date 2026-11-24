-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.biHom_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:45.175989+00:00
-- url     : https://prove2.me/submissions/d5cc0762-5f2d-4714-8ea3-16062c25cea3

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_sum
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_X_w
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_X_e
import Theorems.Thm_P2M_Formalism_GM_tieE_apply__373a5b0b31bc


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
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
variable (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
include hw he hwe
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution {a b : ℕ} {u : MvPolynomial σ K} (hu : BiHom w e a b u) :
    BiHom w e (a + 1) (b + 1) (tieE w e u) := by
  rw [tieE_apply', Finset.sum_mul]
  apply biHom_sum
  intro c _
  rw [mul_assoc]
  exact biHom_X_w hw he hwe c (biHom_X_e hw he hwe c hu)
end Formalism.GM.leadingTermLemmas
