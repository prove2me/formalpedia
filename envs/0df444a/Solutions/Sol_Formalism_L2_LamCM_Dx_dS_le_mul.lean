-- Prove2me | solution 1 for Formalism.L2.LamCM.Dx.dS_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:40:01.162266+00:00
-- url     : https://prove2.me/submissions/ac599ebf-ec52-4c62-b2f3-3e39576f3def

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
theorem _root_.solution {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (z : Fin (n+1) → K) (hz1 : z (Fin.last n) = 1)
    (hz : ∀ q ∈ M.map (lastL K n), q • z ∈ M) :
    dS M ≤ dS (M.comap (snocL K n)) * M.map (lastL K n) := by
  rw [dS, Submodule.span_le]
  rintro d ⟨x, hx, rfl⟩
  set E : Matrix (Fin (n+1)) (Fin (n+1)) K := 1 + Matrix.replicateCol Unit (-(Pi.single (Fin.last n) (1 : K) : Fin (n+1) → K)) *
    Matrix.replicateRow Unit (z - (Pi.single (Fin.last n) (1 : K) : Fin (n+1) → K)) with hE
  have hEdet : E.det = 1 := by
    rw [hE, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct, Pi.single_apply, hz1]
  have hY : ∀ i k, (Matrix.of x * E) i k =
      if k = Fin.last n then x i (Fin.last n) else x i k - x i (Fin.last n) * z k := by
    intro i k
    simp [hE, Matrix.mul_apply, Pi.single_apply]
    rw [Finset.sum_congr rfl (fun j _ => mul_add _ _ _), Finset.sum_add_distrib]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_neg_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    split_ifs with hk
    · subst hk; simp [hz1]
    · ring
  have hdet : (Matrix.of x).det = (Matrix.of x * E).det := by rw [Matrix.det_mul, hEdet, mul_one]
  rw [SetLike.mem_coe, hdet, Matrix.det_succ_column _ (Fin.last n)]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hxl : x i (Fin.last n) ∈ M.map (lastL K n) := ⟨x i, hx i, rfl⟩
  let u : Fin (n+1) → Fin (n+1) → K := fun l => x l - x l (Fin.last n) • z
  have hu : ∀ l, (fun k : Fin n => u l (Fin.castSucc k)) ∈ M.comap (snocL K n) := by
    intro l
    show snocL K n _ ∈ M
    have : snocL K n (fun k : Fin n => u l (Fin.castSucc k)) = u l := by
      ext k; refine Fin.lastCases ?_ (fun j => ?_) k <;> simp [u, hz1]
    rw [this]
    exact M.sub_mem (hx l) (hz _ ⟨x l, hx l, rfl⟩)
  have hmin : ((Matrix.of x * E).submatrix i.succAbove (Fin.last n).succAbove).det ∈ dS (M.comap (snocL K n)) := by
    apply Submodule.subset_span
    refine ⟨fun j k => u (i.succAbove j) (Fin.castSucc k), fun j => hu _, ?_⟩
    congr 1; ext j k
    simp [hY, Fin.succAbove_last, u, (Fin.castSucc_lt_last k).ne]
  rw [hY, if_pos rfl]
  rcases neg_one_pow_eq_or K ((i : ℕ) + (Fin.last n : ℕ)) with h | h
  · convert Submodule.mul_mem_mul hmin hxl using 1; rw [h]; ring
  · convert Submodule.neg_mem _ (Submodule.mul_mem_mul hmin hxl) using 1; rw [h]; ring
end Formalism.L2.LamCM.Dx
