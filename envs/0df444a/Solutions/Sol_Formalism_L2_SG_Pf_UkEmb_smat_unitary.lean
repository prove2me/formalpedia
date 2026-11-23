-- Prove2me | solution 1 for Formalism.L2.SG.Pf.UkEmb.smat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:28.461828+00:00
-- url     : https://prove2.me/submissions/7c9408e9-73cf-4ae3-aa9c-f37e0012d813

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SmatUnitary
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
private theorem conjTranspose_one_add_mul_J_mul_eq_J (J : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin k) ℂ)
    (D : Matrix (Fin k) (Fin k) ℂ) (hJh : Jᴴ = J) (hF : Fᴴ * J * F = 1) (hD : D + Dᴴ + Dᴴ * D = 0) :
    (1 + F * D * Fᴴ * J)ᴴ * J * (1 + F * D * Fᴴ * J) = J := by
  have key : ∀ {m : Type} [Fintype m] (X : Matrix (Fin k) m ℂ), Fᴴ * (J * (F * X)) = X := by
    intro m _ X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hF, Matrix.one_mul]
  have h0 : J * (F * ((D + Dᴴ + Dᴴ * D) * (Fᴴ * J))) = 0 := by
    rw [hD]; simp
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc] at h0
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJh]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, key]
  rw [← sub_eq_zero, ← h0]
  abel
private theorem sub_one_add_conjTranspose_defect_eq_zero_of_unitary (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1) :
    (G - 1) + (G - 1)ᴴ + (G - 1)ᴴ * (G - 1) = 0 := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  have e : (Gᴴ - 1) * (G - 1) = Gᴴ * G - Gᴴ - G + 1 := by
    first
    | noncomm_ring
    | (simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one]; abel)
  rw [e, hG]
  abel
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
theorem _root_.solution (hJh : Jᴴ = J) (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1) :
    (smat J wf G)ᴴ * J * smat J wf G = J := by
  unfold smat
  exact conjTranspose_one_add_mul_J_mul_eq_J J (Wm wf) (G - 1) hJh
    (ortho J wf hon) (sub_one_add_conjTranspose_defect_eq_zero_of_unitary G hG)
end Formalism.L2.SG.Pf.UkEmb
