-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.lap_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:47:10.377451+00:00
-- url     : https://prove2.me/submissions/21bcb9c4-164e-4e98-a88e-9932f5fcd180

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
variable {Ty : Type} (r : Ty → ℕ) (n : ℕ)
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution {k k' : Type} [Field k] [Field k'] (φ : k →+* k') (τ τ' : Ty) (a0 : Fin (r τ)) (a1 : Fin (r τ'))
    (p : MvPolynomial (Letter Ty r n) k) :
    lap r n k' 1 τ τ' a0 a1 (map φ p) = map φ (lap r n k 1 τ τ' a0 a1 p) := by
  simp [lap, Matrix.one_apply, pderiv_map]
end Formalism.L2.FormalSeriesBounds.HaP
