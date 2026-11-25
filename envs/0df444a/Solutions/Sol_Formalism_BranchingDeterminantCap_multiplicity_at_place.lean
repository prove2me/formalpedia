-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.multiplicity_at_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:16:45.944746+00:00
-- url     : https://prove2.me/submissions/0fa30273-fd0b-4c79-9058-3f7ed3dfd4b1

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
import Theorems.Thm_Formalism_BranchingDeterminantCap_choose_succ_mul_two_pow_le
import Theorems.Thm_Formalism_BranchingDeterminantCap_geom_half_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : MultPlace := by
  unfold MultPlace
  intro q k r Nn hq hk hkr hrq hN0 hNn gam hg0 hgs
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  have hqne : (q:ℝ) ≠ 0 := hq0.ne'
  have hrq' : (r:ℝ) ≤ (q:ℝ) := by exact_mod_cast hrq
  have hg : ∀ l, 0 ≤ gam l ∧ gam l ≤ (q:ℝ) ^ l := by
    intro l
    cases l with
    | zero => simp [hg0]
    | succ l =>
      rw [hgs l]
      have h1 : (0:ℝ) ≤ (q:ℝ) ^ l := pow_nonneg hq0.le l
      constructor
      · rw [pow_succ]; nlinarith
      · linarith
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ', hN0]
  simp only [Nat.cast_one, one_mul, Nat.sub_zero]
  have hterm : ∀ i ∈ range (m + 1), (Nn (i + 1) : ℝ) * gam (m + 1 - (i + 1)) ≤
      (r:ℝ) * (q:ℝ) ^ m * ((1:ℝ) / 2) ^ i := by
    intro i hi
    have him : i ≤ m := by have := Finset.mem_range.mp hi; omega
    have e : m + 1 - (i + 1) = m - i := by omega
    rw [e]
    have hN : (Nn (i + 1) : ℝ) ≤ (r.choose (i + 1) : ℝ) := by exact_mod_cast hNn (i + 1)
    have key : (r.choose (i + 1) : ℝ) * 2 ^ i ≤ (r:ℝ) ^ (i + 1) := by
      exact_mod_cast choose_succ_mul_two_pow_le r i
    have hqs : (q:ℝ) ^ m = (q:ℝ) ^ i * (q:ℝ) ^ (m - i) := by
      rw [← pow_add]; congr 1; omega
    have h2 : ((2:ℝ)) ^ i * ((1:ℝ) / 2) ^ i = 1 := by rw [← mul_pow]; norm_num
    have hpos : (0:ℝ) ≤ ((1:ℝ) / 2) ^ i := by positivity
    have hqm : (0:ℝ) ≤ (q:ℝ) ^ (m - i) := pow_nonneg hq0.le _
    calc (Nn (i + 1) : ℝ) * gam (m - i) ≤ (r.choose (i + 1) : ℝ) * (q:ℝ) ^ (m - i) :=
          mul_le_mul hN (hg _).2 (hg _).1 (Nat.cast_nonneg _)
      _ = (r.choose (i + 1) : ℝ) * 2 ^ i * (q:ℝ) ^ (m - i) * ((1:ℝ) / 2) ^ i := by
          linear_combination (-((r.choose (i + 1) : ℝ) * (q:ℝ) ^ (m - i))) * h2
      _ ≤ (r:ℝ) * (q:ℝ) ^ m * ((1:ℝ) / 2) ^ i := by
          apply mul_le_mul_of_nonneg_right _ hpos
          calc (r.choose (i + 1) : ℝ) * 2 ^ i * (q:ℝ) ^ (m - i)
              ≤ (r:ℝ) ^ (i + 1) * (q:ℝ) ^ (m - i) := mul_le_mul_of_nonneg_right key hqm
            _ = (r:ℝ) * (r:ℝ) ^ i * (q:ℝ) ^ (m - i) := by ring
            _ ≤ (r:ℝ) * (q:ℝ) ^ i * (q:ℝ) ^ (m - i) := by gcongr
            _ = (r:ℝ) * (q:ℝ) ^ m := by rw [hqs]; ring
  have hsum_nonneg : 0 ≤ ∑ i ∈ range (m + 1), (Nn (i + 1) : ℝ) * gam (m + 1 - (i + 1)) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hg _).1)
  have hsum_le : ∑ i ∈ range (m + 1), (Nn (i + 1) : ℝ) * gam (m + 1 - (i + 1)) ≤
      2 * (r:ℝ) * (q:ℝ) ^ m := by
    calc _ ≤ ∑ i ∈ range (m + 1), (r:ℝ) * (q:ℝ) ^ m * ((1:ℝ) / 2) ^ i := Finset.sum_le_sum hterm
      _ = (r:ℝ) * (q:ℝ) ^ m * ∑ i ∈ range (m + 1), ((1:ℝ) / 2) ^ i := by rw [Finset.mul_sum]
      _ ≤ (r:ℝ) * (q:ℝ) ^ m * 2 := by
          apply mul_le_mul_of_nonneg_left (geom_half_le (m + 1)); positivity
      _ = 2 * (r:ℝ) * (q:ℝ) ^ m := by ring
  have hgm : gam (m + 1) = (q:ℝ) ^ (m + 1) - (q:ℝ) ^ m := hgs m
  have hA : (q:ℝ) ^ (m + 1) * (1 - 1 / (q:ℝ)) = (q:ℝ) ^ (m + 1) - (q:ℝ) ^ m := by
    field_simp; ring
  have hB : (q:ℝ) ^ (m + 1) * (1 + (2 * (r:ℝ) - 1) / (q:ℝ)) =
      (q:ℝ) ^ (m + 1) + (2 * (r:ℝ) - 1) * (q:ℝ) ^ m := by
    field_simp; ring
  rw [hA, hB, hgm]
  constructor <;> linarith [hsum_nonneg, hsum_le]
end Formalism.BranchingDeterminantCap
