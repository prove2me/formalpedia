-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.EE_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:36:33.643028+00:00
-- url     : https://prove2.me/submissions/84c27ce6-98cf-4517-9530-6611bd087c3e

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_isCov_D
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_EE_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_mem_Gd

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
theorem _root_.solution (hE : GlRel E) {v : V} {X : Fin (N + 1) → V} (hX : X ∈ Gd E v) : EE E X ∈ Gd E v := by
  obtain ⟨η, hη, hXη⟩ := (mem_Gd E).mp hX
  refine (mem_Gd E).mpr ⟨fun j => ∑ l, E j l * η l, isCov_D hE hη, fun j => ?_⟩
  rw [EE_apply]
  first
    | (simp [hXη]; done)
    | (simp [hXη, Module.End.mul_apply]; done)
    | (simp [hXη, LinearMap.mul_apply]; done)
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
