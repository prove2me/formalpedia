-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.MS_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:51:49.495119+00:00
-- url     : https://prove2.me/submissions/5b178a44-47f5-4757-8967-adb30a9f52fb

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.ClosureOperators
theorem _root_.solution {n : ℕ} (f : Fin n → Module.End ℂ V) (v : V) (ξ : Module.Dual ℂ V)
    (h : ∀ a : Fin n → ℕ, ξ (mono f a v) = 0) : MS f v ≤ LinearMap.ker ξ := by
  unfold MS
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact LinearMap.mem_ker.mpr (h a)
end Formalism.FourierDecayAlt.P.ClosureOperators
