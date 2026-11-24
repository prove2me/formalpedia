-- Prove2me | solution 1 for Formalism.UG.P.mem_Upq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:47:29.833896+00:00
-- url     : https://prove2.me/submissions/693e5b23-428f-474a-a0e0-64939c24c305

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
import Theorems.Thm_Formalism_UG_P_cT_conj_eq_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) :
    g ∈ Formalism.UG.Upq p q ↔
      star (g : Matrix _ _ ℂ) * Formalism.UG.Jpq p q * (g : Matrix _ _ ℂ) = Formalism.UG.Jpq p q := by
  unfold Formalism.UG.Upq UJ
  first
  | (simp [cT_conj_eq_star]; done)
  | done
end Formalism.UG.P
