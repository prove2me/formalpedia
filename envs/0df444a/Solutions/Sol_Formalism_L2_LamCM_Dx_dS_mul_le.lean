-- Prove2me | solution 1 for Formalism.L2.LamCM.Dx.dS_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:40:03.347889+00:00
-- url     : https://prove2.me/submissions/6e68b2d1-e6b4-4ceb-8747-02b605796bb7

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_castSucc
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_last
import Theorems.Thm_Formalism_L2_LamCM_Dx_lastL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.LamCM.Dx.snocL_castSucc
attribute [local simp] Formalism.L2.LamCM.Dx.snocL_last
attribute [local simp] Formalism.L2.LamCM.Dx.lastL_apply

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.Dx
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.Dx
theorem _root_.solution {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) :
    dS (M.comap (snocL K n)) * M.map (lastL K n) ≤ dS M := by
  rw [Submodule.mul_le]
  intro p hp q hq
  obtain ⟨v, hv, rfl⟩ := hq
  induction hp using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨y, hy, rfl⟩ := hd
    apply Submodule.subset_span
    let X : Fin (n+1) → Fin (n+1) → K := Fin.snoc (α := fun _ => Fin (n+1) → K) (fun i => snocL K n (y i)) v
    refine ⟨X, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [X] using hv
      · simpa [X] using hy j
    · have hsub : (Matrix.of X).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = Matrix.of y := by
        ext i j; simp [X, Fin.succAbove_last]
      rw [Matrix.det_succ_column _ (Fin.last n), Fin.sum_univ_castSucc, hsub]
      have h0 : ∀ i : Fin n, Matrix.of X (Fin.castSucc i) (Fin.last n) = 0 := fun i => by simp [X]
      simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
      have hl : Matrix.of X (Fin.last n) (Fin.last n) = v (Fin.last n) := by simp [X]
      rw [hl, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, lastL_apply, mul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx
end Formalism.L2.LamCM.Dx
