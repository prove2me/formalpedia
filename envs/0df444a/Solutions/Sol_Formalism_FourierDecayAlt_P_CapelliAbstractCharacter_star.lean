-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:56:25.748833+00:00
-- url     : https://prove2.me/submissions/240ec9da-3550-4250-86ef-0cf85290732f

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_comat
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_detCov
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_KK_apply

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
theorem _root_.solution (hE : GlRel E) {m : Fin (N + 1) → ℂ} {v : V} (hv : v ∈ CapSp E m) {X : Fin (N + 1) → V}
    (hX : X ∈ Gd E v) (u : ℂ) : u • Th E u X - Th E u (KK E X) = cpol m u • X := by
  funext x
  have h1 := comat E hE u X x
  have h2 := detCov E hE hv hX u x
  have lin : (u • Th E u X - Th E u (KK E X)) x = Th E u ((u - (N : ℂ)) • X + EE E X) x - Th E u X x := by
    rw [KK_apply]
    simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    first
      | module
      | (simp only [sub_smul, add_smul, one_smul]; abel)
  rw [lin, h1, h2, Pi.smul_apply, add_sub_cancel_right]
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
