-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.Th_pol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:12.914482+00:00
-- url     : https://prove2.me/submissions/de4c27bc-4dbb-4876-9000-9a72f84918e3

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_qminor_isPol
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_Th_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution : ∃ A : ℕ → (Fin (N + 1) → V) → (Fin (N + 1) → V), ∀ (u : ℂ) (X : Fin (N + 1) → V),
    Th E u X = ∑ s ∈ Finset.range (N + 1), u ^ s • A s X := by
  have hq : ∀ a x : Fin (N + 1), ∃ c : ℕ → Module.End ℂ V, ∀ u : ℂ,
      qminor E a.succAbove x.succAbove u = ∑ s ∈ Finset.range (N + 1), (u ^ s) • c s :=
    fun a x => qminor_isPol E _ _
  choose c hc using hq
  refine ⟨fun s X x => ∑ a : Fin (N + 1), ((-1 : ℂ) ^ ((a : ℕ) + (x : ℕ))) • c a x s (X a), fun u X => ?_⟩
  funext x
  rw [Th_apply]
  simp only [hc, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun a _ => smul_comm _ _ _))
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
