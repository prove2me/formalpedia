-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.E_pow_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:44.0382+00:00
-- url     : https://prove2.me/submissions/971d64e3-4d52-41c4-861c-09c9b95ef2be

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_tieE_pow_eq

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
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ)
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (j k : ℕ) (g : MvPolynomial (Fin (N + 1 + 1) × Fin r) K) :
    (tieE (wW (N := N)) eη ^ j) (X (Fin.last (N + 1), ρ) ^ k * g) =
      X (Fin.last (N + 1), ρ) ^ k * (tieE (wW (N := N)) eη ^ j) g := by
  rw [tieE_pow_eq, tieE_pow_eq]; ring
end Formalism.GM.leadingTermLemmas
