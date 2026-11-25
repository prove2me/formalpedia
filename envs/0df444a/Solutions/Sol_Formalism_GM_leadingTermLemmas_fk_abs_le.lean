-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.fk_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:26.882419+00:00
-- url     : https://prove2.me/submissions/02071d18-0abc-42a6-a341-5f0b207f5439

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_symm
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_add_left
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_sub_left
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_add_right
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_sub_right
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fk_self_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (F G : MvPolynomial σ ℝ) : 2 * |fk F G| ≤ fk F F + fk G G := by
  have h1 := fk_self_nonneg (F - G)
  have h2 := fk_self_nonneg (F + G)
  rw [fk_sub_left, fk_sub_right, fk_sub_right, fk_symm G F] at h1
  rw [fk_add_left, fk_add_right, fk_add_right, fk_symm G F] at h2
  have : 2 * |fk F G| = |2 * fk F G| := by rw [abs_mul, abs_two]
  rw [this, abs_le]
  constructor <;> linarith
end Formalism.GM.leadingTermLemmas
