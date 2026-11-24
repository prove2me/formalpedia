-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.freeze_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:34.035146+00:00
-- url     : https://prove2.me/submissions/7af911fb-81af-4668-b457-ae374aa9256d

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_mul
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_X
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_pow
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_aeval
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_freezeSub_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    {f : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hf : f ∈ M.IntPol p (Fin N × Fin r)) :
    M.freeze p LL ρ n f ∈ M.IntPol p (Fin (N + 1) × Fin r) :=
  intPol_mul p (intPol_pow p (intPol_X p _) _) (intPol_aeval p _ (freezeSub_int p LL ρ) hf)
end Formalism.GM.FrozenVariableLemmas
