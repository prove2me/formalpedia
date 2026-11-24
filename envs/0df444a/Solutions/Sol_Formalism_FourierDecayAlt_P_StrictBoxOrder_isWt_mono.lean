-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StrictBoxOrder.isWt_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:24:50.054106+00:00
-- url     : https://prove2.me/submissions/05d62ef4-d30f-42b7-bb8d-ac0c5fe586a7

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder
import Theorems.Thm_Formalism_FourierDecayAlt_P_StrictBoxOrder_isWt_vec
import Theorems.Thm_Formalism_FourierDecayAlt_P_StrictBoxOrder_list_prod_pres
import Theorems.Thm_Formalism_FourierDecayAlt_P_StrictBoxOrder_pow_pres
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
    (a : Fin n → ℕ) (v : V) (h : IsWt E v) : IsWt E (mono y a v) := by
  unfold mono
  refine list_prod_pres (IsWt E) _ (fun f hf => ?_) v h
  simp only [List.mem_ofFn, Set.mem_range] at hf
  obtain ⟨x, rfl⟩ := hf
  exact pow_pres (IsWt E) (y x) (fun w hw => isWt_vec hy x w hw) (a x)
end Formalism.FourierDecayAlt.P.StrictBoxOrder
