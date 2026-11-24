-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.tieGam_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:57.953862+00:00
-- url     : https://prove2.me/submissions/05c7ce42-71b0-4f06-9777-8d41ccf6e70c

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_fock_eq
import Theorems.Thm_Formalism_GM_leadingTermLemmas_freeze_eq

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
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r) (z n : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    M.tieGam p LL ρ z n f f' = gamK ℚ_[p] LL ρ z n f f' := by
  unfold M.tieGam gamK
  rw [fock_eq, freeze_eq, freeze_eq]
  rfl
end Formalism.GM.leadingTermLemmas
