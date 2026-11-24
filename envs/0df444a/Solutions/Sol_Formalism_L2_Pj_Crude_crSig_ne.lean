-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crSig_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:44.291912+00:00
-- url     : https://prove2.me/submissions/dc295672-ef35-4067-a88a-519a6091abcc

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin

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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution {τ σ : T} (h : τ ≠ σ) {x : Fin (r τ)} {y : Fin n} {i : Fin (r σ)} :
    ¬ ∃ b : Fin n, (⟨τ, x, y⟩ : Letter T r n) = ⟨σ, i, b⟩ := by
  rintro ⟨b, hb⟩
  exact h (Sigma.mk.inj hb).1
end Formalism.L2.Pj.Crude
