-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.step_Z
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:46.972267+00:00
-- url     : https://prove2.me/submissions/f5cc6abd-a493-4f30-88ea-ccd686238618

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_sum
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_fiber_card
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_trace_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_trace_surj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_conj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hB_mulVec
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hMat_li
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_sumA_bound
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
    (hX : LinearIndependent L X) (g : Fin j → L) (a : L) (ha : a ^ Fintype.card K = a) (c : ℕ)
    (hc : c * (Fintype.card K ^ 2) ^ j = (Fintype.card K ^ 2) ^ n) :
    |(Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L =>
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) - c|
      ≤ (Fintype.card K : ℝ) * (Fintype.card K : ℝ) ^ n := by
  obtain ⟨θ, hθ⟩ := trace_surj (K := K) (L := L) 1
  have hθ' : θ + θ ^ Fintype.card K = 1 := by
    rw [← trace_eq h2, hθ, map_one]
  have hfix : ∀ z : L, z ^ Fintype.card K = z → algebraMap K L (Algebra.trace K L (θ * z)) = z := by
    intro z hz
    rw [trace_eq h2, mul_pow, hz]
    linear_combination z * hθ'
  let bq : (Fin n → L) → K := fun x => Algebra.trace K L (θ * hB K Ph x x)
  have hbq : ∀ x, algebraMap K L (bq x) = hB K Ph x x := fun x => hfix _ (hB_conj Ph h2 hherm x x)
  let a0 : K := Algebra.trace K L (θ * a)
  have ha0 : algebraMap K L a0 = a := hfix a ha
  have hQ : ∀ x, bq x + (-a0) = 0 ↔ hB K Ph x x = a := by
    intro x
    rw [← sub_eq_add_neg, sub_eq_zero, ← hbq, ← ha0]
    exact (algebraMap K L).injective.eq_iff.symm
  have hA : (univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b)).card = c := by
    have h1 := fiber_card (hMat K Ph X) (hMat_li Ph h2 hPh X hX) g
    rw [card_L h2, ← hc] at h1
    have h3 := Nat.eq_of_mul_eq_mul_right (by positivity) h1
    rw [← h3]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hB_mulVec, funext_iff]
  have h0 := orth_sum (fun x : Fin n → L => bq x + (-a0))
    (fun x => if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0)
  have hL : ∑ x ∈ univ.filter (fun x : Fin n → L => bq x + (-a0) = 0),
      (if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0)
      = ((univ.filter (fun x : Fin n → L => (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℂ) := by
    rw [Finset.sum_boole, Finset.filter_filter]
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hQ]
    exact and_comm
  rw [hL, ← Finset.add_sum_erase univ _ (Finset.mem_univ (0 : AddChar K ℂ))] at h0
  simp only [AddChar.zero_apply, one_mul] at h0
  rw [Finset.sum_boole, hA] at h0
  have hψb : ∀ ψ ∈ univ.erase (0 : AddChar K ℂ),
      ‖∑ x, ψ (bq x + (-a0)) * (if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0)‖
        ≤ (Fintype.card K : ℝ) ^ n := by
    intro ψ hψ
    have e1 : ∑ x, ψ (bq x + (-a0)) * (if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0)
        = ψ (-a0) * ∑ x ∈ univ.filter (fun x : Fin n → L => ∀ b, hB K Ph x (X b) = g b), ψ (bq x) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [AddChar.map_add_eq_mul]
      split_ifs <;> ring
    rw [e1, norm_mul, AddChar.norm_apply, one_mul]
    exact sumA_bound Ph h2 hPh hherm X g bq hbq ψ (Finset.ne_of_mem_erase hψ)
  have e2 : (((Fintype.card K : ℝ) * ((univ.filter (fun x : Fin n → L =>
        (∀ b, hB K Ph x (X b) = g b) ∧ hB K Ph x x = a)).card : ℝ) - c : ℝ) : ℂ)
      = ∑ ψ ∈ univ.erase (0 : AddChar K ℂ),
        ∑ x, ψ (bq x + (-a0)) * (if (∀ b, hB K Ph x (X b) = g b) then (1 : ℂ) else 0) := by
    push_cast
    linear_combination h0
  rw [← Real.norm_eq_abs, ← Complex.norm_real, e2]
  calc _ ≤ ∑ ψ ∈ univ.erase (0 : AddChar K ℂ), _ := norm_sum_le _ _
    _ ≤ ∑ ψ ∈ univ.erase (0 : AddChar K ℂ), (Fintype.card K : ℝ) ^ n := Finset.sum_le_sum hψb
    _ = ((univ.erase (0 : AddChar K ℂ)).card : ℝ) * (Fintype.card K : ℝ) ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
        gcongr
        have : (univ.erase (0 : AddChar K ℂ)).card ≤ Fintype.card K := by
          calc _ ≤ (univ : Finset (AddChar K ℂ)).card := Finset.card_le_card (Finset.erase_subset _ _)
            _ = _ := by rw [Finset.card_univ, AddChar.card_eq]
        exact_mod_cast this
end Formalism.HermitianLatticeCounting.P.S4aux
