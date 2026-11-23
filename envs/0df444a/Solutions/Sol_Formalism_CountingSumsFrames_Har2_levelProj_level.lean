-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.levelProj_level
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:59.351151+00:00
-- url     : https://prove2.me/submissions/e6ba04ce-ade0-4157-8eb7-8d92828c7f5c

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_h_pow_mul_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctr_pow_h_pow_har
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_har
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_kill
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_levelProj_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.CountingSumsFrames
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
private theorem mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero {A B : ℕ} {f : PolXY K k} :
    f ∈ HarAB K k A B ↔ f ∈ PolAB K k A B ∧ ctrF K k f = 0 := Iff.rfl
end Har2
open Har2
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
end Har2
end Formalism.CountingSumsFrames
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution [CharZero K] (hk : 1 ≤ k) {A B i j : ℕ} (hi : i ≤ min A B) (hj : j ≤ min A B)
    {w : PolXY K k} (hw : w ∈ HarAB K k (A - i) (B - i)) :
    levelProj K k A B j (hXY K k ^ i * w) = if i = j then hXY K k ^ i * w else 0 := by
  rw [levelProj_apply]
  obtain ⟨hw1, hw2⟩ := mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 hw
  have hA := min_le_left A B
  have hB := min_le_right A B
  have hc : ctrDiv K k j (hXY K k ^ i * w) = (((j.factorial : ℕ) : K)⁻¹ *
      ((i.descFactorial j * (A - i + (B - i) + k + i - 1).descFactorial j : ℕ) : K)) •
        (hXY K k ^ (i - j) * w) := by
    simp only [ctrDiv, LinearMap.smul_apply]
    rw [ctr_pow_h_pow_har hk hw j i, smul_smul]
  rw [hc]
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 hij, zero_mul, Nat.cast_zero, mul_zero, zero_smul, map_zero,
      smul_zero, mul_zero, if_neg hij.ne]
  · subst hij
    rw [if_pos rfl, Nat.sub_self, pow_zero, one_mul, map_smul, harProj_har hw, smul_smul]
    congr 1
    convert one_smul K w using 2
    have hN : A - i + (B - i) + k + i - 1 = A + B + k - 2 * i + i - 1 := by omega
    have h1 : ((i.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
    have h2 : (((A + B + k - 2 * i + i - 1).choose i : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.choose_pos (by omega)).ne'
    rw [hN, Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.cast_mul]
    field_simp
    all_goals ring
  · rw [if_neg hij.ne', map_smul]
    have hpow : hXY K k ^ (i - j) * w = hXY K k * (hXY K k ^ (i - j - 1) * w) := by
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]
    have hg : hXY K k ^ (i - j - 1) * w ∈ PolAB K k (A - j - 1) (B - j - 1) := by
      have := h_pow_mul_mem (i - j - 1) hw1
      rwa [show A - i + (i - j - 1) = A - j - 1 by omega, show B - i + (i - j - 1) = B - j - 1 by omega] at this
    rw [hpow, harProj_kill hk (by omega) (by omega) hg, smul_zero, smul_zero, mul_zero]
end Formalism.CountingSumsFrames.Har2
