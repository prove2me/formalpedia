-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.freezeSub_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:43.332875+00:00
-- url     : https://prove2.me/submissions/51ec909f-c60c-410a-8757-036a9323618f

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_mul
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_X

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
theorem _root_.solution (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r)
    (x : Fin N × Fin r) : M.freezeSub p LL ρ x ∈ M.IntPol p (Fin (N + 1) × Fin r) := by
  obtain ⟨i, c⟩ := x
  simp only [M.freezeSub]
  split_ifs
  · exact Submodule.sum_mem _ (fun c' _ => intPol_mul p (intPol_X p _) (intPol_X p _))
  · exact intPol_mul p (intPol_X p _) (intPol_X p _)
  · exact intPol_mul p (intPol_X p _) (intPol_X p _)
  · exact Submodule.sub_mem _ (intPol_mul p (intPol_X p _) (intPol_X p _))
      (intPol_mul p (intPol_X p _) (intPol_X p _))
end Formalism.GM.FrozenVariableLemmas
