-- Prove2me | solution 1 for Formalism.L2.SG.Pf.UkEmb.smat_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:21.233323+00:00
-- url     : https://prove2.me/submissions/021190f4-815b-40f9-9643-60c3f6413496

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SmatUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace Formalism.L2.SG.Pf.UkEmb
variable {n k : ℕ}
private theorem conjTranspose_Wm_mulVec_apply (wf : Fin k → Fin n → ℂ) (y : Fin n → ℂ) (a : Fin k) :
    ((Wm wf)ᴴ *ᵥ y) a = star (wf a) ⬝ᵥ y := by
  first
  | rfl
  | simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Wm]
variable (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ)
  (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0)
end Formalism.L2.SG.Pf.UkEmb
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.UkEmb
variable {n k : ℕ}
variable (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ)
  (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0)
include hon
namespace Formalism.L2.SG.Pf.UkEmb
theorem _root_.solution (G : Matrix (Fin k) (Fin k) ℂ) (x : Fin n → ℂ) (hx : ∀ a, star (wf a) ⬝ᵥ (J *ᵥ x) = 0) :
    smat J wf G *ᵥ x = x := by
  have hz : (Wm wf)ᴴ *ᵥ (J *ᵥ x) = 0 := by
    funext a
    rw [conjTranspose_Wm_mulVec_apply, hx a, Pi.zero_apply]
  unfold smat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz,
    Matrix.mulVec_zero, add_zero]
end Formalism.L2.SG.Pf.UkEmb
