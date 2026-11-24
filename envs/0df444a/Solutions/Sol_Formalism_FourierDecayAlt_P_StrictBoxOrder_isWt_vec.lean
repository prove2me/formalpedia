-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StrictBoxOrder.isWt_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:56:33.766264+00:00
-- url     : https://prove2.me/submissions/7dcc190e-7037-41a3-aad0-f1323862fc01

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StrictBoxOrder
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.StrictBoxOrder
theorem _root_.solution {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {y : Fin n → Module.End ℂ V} (hy : IsVec E y)
    (x : Fin n) (v : V) (h : IsWt E v) : IsWt E (y x v) := by
  intro c
  obtain ⟨t, ht⟩ := h c
  have e := congrArg (fun g : Module.End ℂ V => g v) (hy c c x)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, ht, map_smul] at e
  by_cases hcx : c = x
  · subst hcx
    rw [if_pos rfl, LinearMap.neg_apply, sub_eq_iff_eq_add] at e
    refine ⟨t - 1, ?_⟩
    rw [e, sub_smul, one_smul]
    abel
  · rw [if_neg hcx, LinearMap.zero_apply, sub_eq_zero] at e
    exact ⟨t, e⟩
end Formalism.FourierDecayAlt.P.StrictBoxOrder
