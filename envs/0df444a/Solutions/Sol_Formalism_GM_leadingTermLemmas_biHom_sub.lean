-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.biHom_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:39.637704+00:00
-- url     : https://prove2.me/submissions/7a419fd8-f43e-48b7-a31d-fd7d2a838306

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_add
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_neg

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
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution {a b : ℕ} {u v : MvPolynomial σ K} (hu : BiHom w e a b u) (hv : BiHom w e a b v) :
    BiHom w e a b (u - v) := by
  rw [sub_eq_add_neg]; exact biHom_add hu (biHom_neg hv)
end Formalism.GM.leadingTermLemmas
