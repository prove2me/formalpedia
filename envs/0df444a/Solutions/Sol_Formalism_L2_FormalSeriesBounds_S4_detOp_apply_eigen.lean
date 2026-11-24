-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.detOp_apply_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:12:20.667095+00:00
-- url     : https://prove2.me/submissions/2a2d2bfc-c0af-4220-89ec-655f5f95ea67

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_ofFn_prod_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution {F : Type*} [AddCommGroup F] [Module R F] {n : ℕ}
    (D : Fin n → Fin n → Module.End R F) (a : Matrix (Fin n) (Fin n) R) (g : F)
    (hD : ∀ ρ c, D ρ c g = a ρ c • g) : detOp D g = a.det • g := by
  unfold detOp
  rw [LinearMap.sum_apply, ← Matrix.det_transpose, Matrix.det_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [LinearMap.smul_apply, ofFn_prod_apply g (fun ρ => D ρ (σ ρ)) (fun ρ => a ρ (σ ρ)) (fun ρ => hD ρ (σ ρ)),
    smul_smul]
  simp [Matrix.transpose_apply, Units.smul_def]
end Formalism.L2.FormalSeriesBounds.S4
