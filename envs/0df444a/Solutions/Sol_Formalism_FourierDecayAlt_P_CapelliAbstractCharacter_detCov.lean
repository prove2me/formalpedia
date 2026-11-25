-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.detCov
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:36:38.759808+00:00
-- url     : https://prove2.me/submissions/529d598a-167e-4eef-9316-6401d2f2e610

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_sgn_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_Th_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_minorCov_gen
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_Qr_mem_CapSp


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
    (hX : X ∈ Gd E v) (u : ℂ) (x : Fin (N + 1)) :
    qdet E u (X x) = cpol m u • X x + Th E u X x := by
  obtain ⟨η, hη, hX⟩ := hX
  have h := congrArg (fun T : Module.End ℂ V => T v)
    (QuantumMinorCommutation.minorCov_gen E hE η hη id id x (fun k => Fin.succAbove_ne x k) u)
  simp only [id, Function.id_comp, sgn_mul, LinearMap.sum_apply, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply] at h
  have hq : qminor E id id u v = cpol m u • v := mem_CapSp.1 hv u
  rw [hq, map_smul, sub_eq_iff_eq_add'] at h
  rw [Th_apply, hX x]
  refine h.trans ?_
  congr 1
  exact Finset.sum_congr rfl (fun l _ => by rw [add_comm, hX l])
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
