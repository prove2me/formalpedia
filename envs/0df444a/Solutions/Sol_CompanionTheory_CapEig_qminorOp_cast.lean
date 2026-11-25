-- Prove2me | solution 1 for CompanionTheory.CapEig.qminorOp_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:13:52.634785+00:00
-- url     : https://prove2.me/submissions/81342047-9b77-4201-b0d7-931e77432682

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_CoefEig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep Formalism.FourierDecayAlt
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.CapEig
namespace CompanionTheory.CapEig
theorem _root_.solution {n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)) (h : m = n)
    (a : Fin m → Fin n) (ha : ∀ j, (a j).val = j.val) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.qminorOp Eop a a u f = Formalism.QuantumDeterminants.qminorOp Eop id id u f := by
  subst h
  have : a = id := funext fun j => Fin.ext (ha j)
  rw [this]
end CompanionTheory.CapEig
