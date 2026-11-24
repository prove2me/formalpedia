-- Prove2me | solution 1 for Formalism.GM.ProjS.eulL_pderiv_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:34.183847+00:00
-- url     : https://prove2.me/submissions/2f2219bb-3f2a-40a4-b5b3-b013d7069116

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_eulL_pderiv_notMem
import Theorems.Thm_Formalism_GM_ProjS_eulL_pderiv_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.GM.ProjS
theorem _root_.solution {s : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (a b : σ)
    (hab : ((∃ d, t d = a) ∧ ∀ d, t d ≠ b) ∨ ((∀ d, t d ≠ a) ∧ ∃ d, t d = b)) (g : MvPolynomial σ k) :
    eulL t (pderiv a (pderiv b g)) = pderiv a (pderiv b (eulL t g)) - pderiv a (pderiv b g) := by
  rcases hab with ⟨⟨d, hd⟩, hb⟩ | ⟨ha, ⟨d, hd⟩⟩
  · subst hd
    rw [eulL_pderiv_mem t ht d, eulL_pderiv_notMem t b hb]
  · subst hd
    rw [eulL_pderiv_notMem t a ha, eulL_pderiv_mem t ht d, map_sub]
end Formalism.GM.ProjS
