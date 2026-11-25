-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.letEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:58:29.81759+00:00
-- url     : https://prove2.me/submissions/219b69e7-6dc6-44d1-978e-0e4095a2c9d6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees

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
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
variable {T : Type} (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
theorem _root_.solution {τ1 τ2 : T} {c1 : Fin (r τ1)} {c2 : Fin (r τ2)} {b1 b2 : Fin n} :
    ((⟨τ1, (c1, b1)⟩ : Letter T r n) = ⟨τ2, (c2, b2)⟩) ↔ ((⟨τ1, c1⟩ : Σ σ, Fin (r σ)) = ⟨τ2, c2⟩ ∧ b1 = b2) := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, rfl⟩
    cases h1
    rfl
end Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
