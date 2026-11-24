-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.sumA_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:31.846366+00:00
-- url     : https://prove2.me/submissions/f16d8601-037f-40de-b33f-10e3d75c1311

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_sum
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_trace_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_gauss_inert
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_add_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_add_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_conj
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
variable {n : ℕ} (Ph : Matrix (Fin n) (Fin n) L)
open scoped Classical
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (h2 : Module.finrank K L = 2) (hPh : IsUnit Ph.det)
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) {j : ℕ} (X : Fin j → Fin n → L)
    (g : Fin j → L) (bq : (Fin n → L) → K) (hbq : ∀ x, algebraMap K L (bq x) = hB K Ph x x)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 0) :
    ‖∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x)‖
      ≤ (Fintype.card K : ℝ) ^ n := by
  let ℓ : (Fin n → L) → (Fin j → L) := fun x b => hB K Ph x (X b)
  have hℓ : ∀ u d, ℓ (u + d) = ℓ u + ℓ d := fun u d => by
    funext b; exact hB_add_left Ph u d (X b)
  have hbqadd : ∀ u d, bq (u + d) = bq u + bq d + Algebra.trace K L (hB K Ph u d) := by
    intro u d
    apply (algebraMap K L).injective
    rw [map_add, map_add, hbq, hbq, hbq, trace_eq h2, hB_conj Ph h2 hherm, hB_add_left,
      hB_add_right, hB_add_right]
    ring
  have hfil : (univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b))
      = univ.filter (fun x : Fin n → L => ℓ x + (-g) = 0) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ℓ]
    rw [← sub_eq_add_neg, sub_eq_zero, funext_iff]
  have h0 := orth_sum (fun x : Fin n → L => ℓ x + (-g)) (fun x => ψ (bq x))
  rw [← hfil] at h0
  have hχ : ∀ χ : AddChar (Fin j → L) ℂ, ‖∑ x, χ (ℓ x + (-g)) * ψ (bq x)‖ ≤ (Fintype.card K : ℝ) ^ n := by
    intro χ
    have e1 : ∑ x, χ (ℓ x + (-g)) * ψ (bq x) = χ (-g) * ∑ x, χ (ℓ x) * ψ (bq x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [AddChar.map_add_eq_mul]; ring
    rw [e1, norm_mul, AddChar.norm_apply, one_mul]
    refine gauss_inert h2 n Ph hPh ψ hψ (fun x => χ (ℓ x) * ψ (bq x)) (fun u => ?_) (fun u d => ?_)
    · rw [norm_mul, AddChar.norm_apply, AddChar.norm_apply, one_mul]
    · change χ (ℓ (u + d)) * ψ (bq (u + d)) = χ (ℓ u) * ψ (bq u) * (χ (ℓ d) * ψ (bq d)) *
        ψ (Algebra.trace K L (hB K Ph u d))
      rw [hℓ, hbqadd, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
      ring
  have hT : (0 : ℝ) < (Fintype.card (Fin j → L) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h1 : ‖∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x)‖
      * (Fintype.card (Fin j → L) : ℝ) ≤ (Fintype.card K : ℝ) ^ n * (Fintype.card (Fin j → L) : ℝ) := by
    calc _ = ‖(∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x))
          * (Fintype.card (Fin j → L) : ℂ)‖ := by rw [norm_mul]; simp
      _ ≤ ∑ χ : AddChar (Fin j → L) ℂ, ‖∑ x, χ (ℓ x + (-g)) * ψ (bq x)‖ := by
          rw [h0]; exact norm_sum_le _ _
      _ ≤ ∑ χ : AddChar (Fin j → L) ℂ, (Fintype.card K : ℝ) ^ n := Finset.sum_le_sum fun χ _ => hχ χ
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, AddChar.card_eq, nsmul_eq_mul, mul_comm]
  exact le_of_mul_le_mul_right h1 hT
end Formalism.HermitianLatticeCounting.P.S4aux
