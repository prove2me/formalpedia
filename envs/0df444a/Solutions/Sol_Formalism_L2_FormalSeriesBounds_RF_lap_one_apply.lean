-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.lap_one_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:14.764843+00:00
-- url     : https://prove2.me/submissions/a45dbc10-81d0-43fc-8c0d-f888b4e386e0

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {T : Type} (r : T → ℕ) (n : ℕ) (C : Type) [Field C] (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ'))
    (P : MvPolynomial (Letter T r n) C) :
    lap r n C 1 τ τ' a a' P = ∑ b, ∑ b', (1 : Matrix (Fin n) (Fin n) C) b b' •
      MvPolynomial.pderiv (⟨τ, a, b⟩ : Letter T r n) (MvPolynomial.pderiv (⟨τ', a', b'⟩ : Letter T r n) P) := by
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rfl
end Formalism.L2.FormalSeriesBounds.RF
