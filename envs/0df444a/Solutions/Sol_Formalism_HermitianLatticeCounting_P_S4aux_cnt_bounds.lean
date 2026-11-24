-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.cnt_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:10.500187+00:00
-- url     : https://prove2.me/submissions/59428dd1-3da9-45b5-a3b5-cd0a5090e8d7

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_step_alt
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_step_arith
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_cnt_succ
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
    (hherm : ∀ k l, Ph l k = Ph k l ^ Fintype.card K) (j : ℕ) : 2 * j + 3 ≤ n →
    ∀ G : Matrix (Fin j) (Fin j) L, (∀ a b, G b a = G a b ^ Fintype.card K) →
    (1 - ((Fintype.card K : ℝ) ^ 2) ^ j / (Fintype.card K : ℝ) ^ n) *
        ((Fintype.card K : ℝ) ^ (2 * n * j) / (Fintype.card K : ℝ) ^ (j ^ 2))
      ≤ ((univ.filter fun X : Fin j → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b).card : ℝ) ∧
    ((univ.filter fun X : Fin j → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b).card : ℝ)
      ≤ (1 + ((Fintype.card K : ℝ) ^ 2) ^ j / (Fintype.card K : ℝ) ^ n) *
        ((Fintype.card K : ℝ) ^ (2 * n * j) / (Fintype.card K : ℝ) ^ (j ^ 2)) := by
  have hq2 : (2 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hq0 : (0 : ℝ) < (Fintype.card K : ℝ) := by linarith
  induction j with
  | zero =>
    intro _ G _
    have : (univ.filter fun X : Fin 0 → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = G a b) = univ := by
      ext X
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact ⟨linearIndependent_empty_type, fun a => a.elim0⟩
    rw [this]
    have hd : 0 ≤ 1 / (Fintype.card K : ℝ) ^ n := by positivity
    simp only [Finset.card_univ, Fintype.card_unique, Nat.cast_one, pow_zero, mul_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_one, mul_one]
    constructor <;> linarith
  | succ j ih =>
    intro hn G hG
    obtain ⟨t, rfl⟩ : ∃ t, n = j + t := ⟨n - j, by omega⟩
    have ih' := ih (by omega) (G.submatrix Fin.succ Fin.succ) (fun a b => hG _ _)
    simp only [Matrix.submatrix_apply] at ih'
    rw [cnt_succ Ph h2 hherm j G hG]
    set valid := univ.filter (fun X' : Fin j → Fin (j + t) → L => LinearIndependent L X' ∧
          ∀ a b, hB K Ph (X' a) (X' b) = G a.succ b.succ) with hvalid
    have hc : (Fintype.card K ^ 2) ^ t * (Fintype.card K ^ 2) ^ j = (Fintype.card K ^ 2) ^ (j + t) := by
      rw [← pow_add, add_comm]
    have hstep : ∀ X' ∈ valid, _ := fun X' hX' =>
      step_alt Ph h2 hPh hherm X' (Finset.mem_filter.1 hX').2.1 (fun b => G 0 b.succ) (G 0 0)
        (hG 0 0).symm ((Fintype.card K ^ 2) ^ t) hc
    push_cast
    push_cast at hstep
    set q : ℝ := (Fintype.card K : ℝ) with hq
    have hres := step_arith q (q ^ (j + t)) ((q ^ 2) ^ j) ((q ^ 2) ^ t)
      (q ^ (2 * (j + t) * j) / q ^ (j ^ 2)) (valid.card : ℝ)
      (∑ X' ∈ valid, ((univ.filter fun x : Fin (j + t) → L => x ∉ Submodule.span L (Set.range X') ∧
          (∀ b, hB K Ph x (X' b) = G 0 b.succ) ∧ hB K Ph x x = G 0 0).card : ℝ))
      (((q ^ 2) ^ t - q * q ^ (j + t) - q * (q ^ 2) ^ j) / q) (((q ^ 2) ^ t + q * q ^ (j + t)) / q)
      hq2 (by positivity) (by positivity)
      (by rw [← pow_add, ← pow_mul, ← pow_mul]; congr 1; ring)
      (by
        have h8 : (8 : ℝ) ≤ q ^ 3 := by
          calc (8 : ℝ) = 2 ^ 3 := by norm_num
            _ ≤ q ^ 3 := by gcongr
        have e : q ^ (j + t) = q ^ 2 * (q ^ 2) ^ j * q ^ (t - j - 2) := by
          rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
        have h3 : q ^ 3 ≤ q ^ (t - j - 2) := pow_le_pow_right₀ (by linarith) (by omega)
        rw [e]
        have : 0 < q ^ 2 * (q ^ 2) ^ j := by positivity
        nlinarith)
      (by positivity) ih'.1 ih'.2 rfl rfl
      (by
        rw [← nsmul_eq_mul]
        refine Finset.card_nsmul_le_sum _ _ _ fun X' hX' => ?_
        rw [div_le_iff₀ hq0]
        linarith [(hstep X' hX').2])
      (by
        rw [← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ fun X' hX' => ?_
        rw [le_div_iff₀ hq0]
        linarith [(hstep X' hX').1])
    have eQ : q ^ (2 * (j + t) * (j + 1)) / q ^ ((j + 1) ^ 2)
        = q ^ (2 * (j + t) * j) / q ^ (j ^ 2) * (q ^ 2) ^ t / q := by
      rw [div_mul_eq_mul_div, div_div, div_eq_div_iff (by positivity) (by positivity), ← pow_mul,
        ← pow_succ, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      ring
    have ed : (q ^ 2) ^ (j + 1) / q ^ (j + t) = q ^ 2 * (q ^ 2) ^ j / q ^ (j + t) := by
      rw [pow_succ]; ring
    rw [eQ, ed]
    exact hres
end Formalism.HermitianLatticeCounting.P.S4aux
