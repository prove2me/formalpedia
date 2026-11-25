-- Prove2me | solution 1 for CompanionTheory.CapEig.inUJ_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:12:00.225822+00:00
-- url     : https://prove2.me/submissions/752cd5de-28c0-49b3-a73d-fa004f5358bb

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants PI.DSInfCharCap
noncomputable section
open CompanionTheory CompanionTheory.CapEig
variable {n : ℕ} {ε : Fin n → Bool} {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)}
namespace CompanionTheory.CapEig
theorem _root_.solution : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp [inUJ]
end CompanionTheory.CapEig
