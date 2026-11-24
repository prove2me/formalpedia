-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.IsPol.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:20:48.500309+00:00
-- url     : https://prove2.me/submissions/6f5bb5a0-22c3-4cf0-8a0b-29286c5f7fa0

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_IsPol_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_IsPol_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add


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
variable {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
namespace IsPol
theorem _root_.solution {ι : Type} (S : Finset ι) {d : ℕ} {f : ι → ℂ → X} (hf : ∀ i ∈ S, IsPol d (f i)) :
    IsPol d (fun u => ∑ i ∈ S, f i u) := by
  obtain ⟨c, hc⟩ := Finset.sum_induction f (IsPol d) (fun a b ha hb => IsPol.add ha hb) (IsPol.zero d) hf
  refine ⟨c, fun u => ?_⟩
  show ∑ i ∈ S, f i u = _
  rw [← Finset.sum_apply]
  exact hc u
end IsPol
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
