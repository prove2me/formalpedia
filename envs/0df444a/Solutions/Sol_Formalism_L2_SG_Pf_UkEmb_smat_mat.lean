-- Prove2me | solution 1 for Formalism.L2.SG.Pf.UkEmb.smat_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:38.967831+00:00
-- url     : https://prove2.me/submissions/b2628b28-323d-475d-8dc2-10baba3d2ee8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SmatUnitary
import Theorems.Thm_Formalism_L2_SG_Pf_UkEmb_entry
import Theorems.Thm_Formalism_L2_SG_Pf_UkEmb_ortho
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
private theorem conjTranspose_mul_J_one_add_mul_eq_one_add (J : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin k) ℂ)
    (D : Matrix (Fin k) (Fin k) ℂ) (hF : Fᴴ * J * F = 1) :
    Fᴴ * (J * (1 + F * D * Fᴴ * J)) * F = 1 + D := by
  have key : ∀ {m : Type} [Fintype m] (X : Matrix (Fin k) m ℂ), Fᴴ * (J * (F * X)) = X := by
    intro m _ X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hF, Matrix.one_mul]
  have key2 : Fᴴ * (J * F) = 1 := by rw [← Matrix.mul_assoc, hF]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, key, key2]
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
theorem _root_.solution (G : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    star (wf a) ⬝ᵥ (J *ᵥ (smat J wf G *ᵥ wf b)) = G a b := by
  have hM : (Wm wf)ᴴ * (J * smat J wf G) * Wm wf = G := by
    unfold smat
    rw [conjTranspose_mul_J_one_add_mul_eq_one_add J (Wm wf) (G - 1) (ortho J wf hon)]
    abel
  rw [Matrix.mulVec_mulVec, ← entry, hM]
end Formalism.L2.SG.Pf.UkEmb
