-- Prove2me | solution 1 for ErschlerZheng.tsum_f_mul_mass_upsilon_and_upsilonCheck_not_mem_letterGerms_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T15:40:53.697322+00:00
-- url     : https://prove2.me/submissions/6dca150e-b386-4fb2-aeaa-0d40fe4fba60

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Germs
import Theorems.Thm_ErschlerZheng_germEq_mul_and_germ_mul
import Theorems.Thm_ErschlerZheng_isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms
import Theorems.Thm_ErschlerZheng_exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem
import Theorems.Thm_ErschlerZheng_setOf_not_mem_letterGerms_seqG_eq
import Theorems.Thm_ErschlerZheng_setOf_not_mem_letterGerms_gTilde_eq_and_ncard_and_schreierDist
import Definitions.Def_ErschlerZheng_Walks
import Theorems.Thm_ErschlerZheng_schreierDist_eq_abs_sub_grayCode_of_isCofinal
import Theorems.Thm_ErschlerZheng_card_rayPrefix_smul_div_card_eq
import Theorems.Thm_ErschlerZheng_tsum_f_schreierDist_div_card_le_sixteen

section
/-!
# The doubling sums of p. 56 (Proposition 7.12, last step) — prover 7

For `f ⩾ 0` on `[0, ∞)` with `f(2s)/f(s) ⩾ 2^{-1/D'}` for `s ⩾ 1` (Proposition 7.12's hypotheses):
* `f(s) > 0` for `s ⩾ 1`;
* `f(2^a) ⩽ 2^{(b-a)/D'} f(2^b)` for `a ⩽ b`;
* `Σ_{j ⩽ n} 2^j f(2^{j+c}) ⩽ C 2^n f(2^{n+c})` with `C = (1 - 2^{-(1-1/D')})⁻¹`, for `D' > 1`
  (Lemma 7.21's first term, `c = 2k_n`; also the `j ⩽ n - k_n` pieces with `c = 0`);
* `Σ_{j ⩽ n} 2^j f(2^{n+e₀}) k^{1+2/D} 2^{-(j+2k-n)/D} ⩽ C 2^n f(2^{n+2k})` for `1 < D < D'`,
  `e₀ ⩽ 2k`, `C = C(D, D')` (Lemma 7.21's second term, `e₀ ∈ {D, 0}`).
No stubs.
-/

namespace ErschlerZheng

namespace P7Dev

section Doubling

variable {f : ℝ → ℝ} {D' : ℝ} (hD' : 1 < D') (hf0 : ∀ s, 0 ≤ s → 0 ≤ f s)
  (hfr : ∀ s, 1 ≤ s → (2 : ℝ) ^ (-1 / D') ≤ f (2 * s) / f s)

include hf0 hfr in
theorem pos_of_ratio (s : ℝ) (hs : 1 ≤ s) : 0 < f s := by
  rcases (hf0 s (by linarith)).lt_or_eq with h | h
  · exact h
  · have := hfr s hs
    rw [← h, div_zero] at this
    exact absurd this (not_le.mpr (by positivity))

include hf0 hfr in
theorem step_le (s : ℝ) (hs : 1 ≤ s) : f s ≤ (2 : ℝ) ^ (1 / D') * f (2 * s) := by
  have hpos := pos_of_ratio hf0 hfr s hs
  have h := hfr s hs
  rw [le_div_iff₀ hpos] at h
  have e : (2 : ℝ) ^ (1 / D') * (2 : ℝ) ^ (-1 / D') = 1 := by
    rw [← Real.rpow_add (by norm_num)]; ring_nf; simp
  calc f s = (2 : ℝ) ^ (1 / D') * ((2 : ℝ) ^ (-1 / D') * f s) := by
        rw [← mul_assoc, e, one_mul]
    _ ≤ (2 : ℝ) ^ (1 / D') * f (2 * s) := mul_le_mul_of_nonneg_left h (by positivity)

include hf0 hfr in
/-- `f(2^a) ⩽ 2^{m/D'} f(2^{a+m})`. -/
theorem pow_le (a : ℕ) : ∀ m : ℕ, f (2 ^ a) ≤ (2 : ℝ) ^ ((m : ℝ) / D') * f (2 ^ (a + m))
  | 0 => by simp
  | m + 1 => by
    have ih := pow_le a m
    have hs : (1 : ℝ) ≤ 2 ^ (a + m) := one_le_pow₀ (by norm_num)
    have := step_le hf0 hfr _ hs
    rw [← pow_succ'] at this
    calc f (2 ^ a) ≤ (2 : ℝ) ^ ((m : ℝ) / D') * f (2 ^ (a + m)) := ih
      _ ≤ (2 : ℝ) ^ ((m : ℝ) / D') * ((2 : ℝ) ^ (1 / D') * f (2 ^ (a + m + 1))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (2 : ℝ) ^ (((m + 1 : ℕ) : ℝ) / D') * f (2 ^ (a + (m + 1))) := by
          rw [← mul_assoc, ← Real.rpow_add (by norm_num), ← add_assoc]
          congr 2
          push_cast; ring

include hD' hf0 hfr in
/-- `Σ_{j ⩽ n} 2^j f(2^{j+c}) ⩽ (1 - 2^{-(1-1/D')})⁻¹ 2^n f(2^{n+c})`. -/
theorem sum_two_pow_mul_le (c n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j * f (2 ^ (j + c)) ≤
      (1 - (2 : ℝ) ^ (-(1 - 1 / D')))⁻¹ * (2 ^ n * f (2 ^ (n + c))) := by
  set q : ℝ := (2 : ℝ) ^ (-(1 - 1 / D')) with hq
  have hD'0 : 0 < D' := by linarith
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by have : 1 / D' < 1 := (div_lt_one hD'0).mpr hD'; linarith)
  have hq0 : 0 ≤ q := by positivity
  have hF : 0 ≤ f (2 ^ (n + c)) := hf0 _ (by positivity)
  have hterm : ∀ j ∈ Finset.range (n + 1),
      (2 : ℝ) ^ j * f (2 ^ (j + c)) ≤ q ^ (n - j) * (2 ^ n * f (2 ^ (n + c))) := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h := pow_le hf0 hfr (j + c) (n - j)
    rw [show j + c + (n - j) = n + c by omega] at h
    have e : (2 : ℝ) ^ j * (2 : ℝ) ^ (((n - j : ℕ) : ℝ) / D') = q ^ (n - j) * 2 ^ n := by
      rw [hq, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num),
        ← Real.rpow_add (by norm_num)]
      congr 1
      push_cast [Nat.cast_sub hjn]
      field_simp
      ring
    calc (2 : ℝ) ^ j * f (2 ^ (j + c)) ≤
          (2 : ℝ) ^ j * ((2 : ℝ) ^ (((n - j : ℕ) : ℝ) / D') * f (2 ^ (n + c))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = q ^ (n - j) * (2 ^ n * f (2 ^ (n + c))) := by rw [← mul_assoc, e, mul_assoc]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by positivity) hF)
  calc ∑ j ∈ Finset.range (n + 1), q ^ (n - j) = ∑ i ∈ Finset.range (n + 1), q ^ i :=
        Finset.sum_range_reflect (fun i => q ^ i) (n + 1)
    _ ≤ ∑' i, q ^ i :=
        (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun i _ => pow_nonneg hq0 i)
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1

/-- `x^a ⩽ (a/b)^a e^{bx}` for `x ⩾ 0`, `a, b > 0` (from `e^y ⩾ y`). -/
theorem rpow_le_exp (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) :
    x ^ a ≤ (a / b) ^ a * Real.exp (b * x) := by
  have h1 : x ≤ a / b * Real.exp (b * x / a) := by
    have := Real.add_one_le_exp (b * x / a)
    have hy : b * x / a ≤ Real.exp (b * x / a) := by linarith
    calc x = a / b * (b * x / a) := by field_simp
      _ ≤ a / b * Real.exp (b * x / a) := mul_le_mul_of_nonneg_left hy (by positivity)
  calc x ^ a ≤ (a / b * Real.exp (b * x / a)) ^ a := Real.rpow_le_rpow hx h1 ha.le
    _ = (a / b) ^ a * Real.exp (b * x) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.exp_mul]
        congr 2; field_simp

/-- `k^a 2^{-ck}` is bounded on `ℕ` for `c > 0`. -/
theorem exists_bound_rpow_mul_two_rpow (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∃ M, ∀ k : ℕ, (k : ℝ) ^ a * (2 : ℝ) ^ (-(c * k)) ≤ M := by
  set b := c * Real.log 2
  have hb : 0 < b := mul_pos hc (Real.log_pos one_lt_two)
  refine ⟨(a / b) ^ a, fun k => ?_⟩
  have h := rpow_le_exp a b k ha hb (Nat.cast_nonneg k)
  have e : (2 : ℝ) ^ (-(c * k)) = Real.exp (-(b * k)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]; congr 1; ring
  rw [e]
  calc (k : ℝ) ^ a * Real.exp (-(b * k)) ≤ (a / b) ^ a * Real.exp (b * k) * Real.exp (-(b * k)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = (a / b) ^ a := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

end Doubling

end P7Dev

end ErschlerZheng
end

section
/-!
# Proposition 7.12 (corrected): the real sums of the assembly (OpI2)

For `f ⩾ 0` on `[0, ∞)` with `f(2s)/f(s) ⩾ 2^{-1/D'}` (`s ⩾ 1`), `3 ⩽ D < D'`, and
`K = (1 - 2^{-(1-1/D')})⁻¹` (`kK`), the sums over the levels `j ⩽ n` of the per-level bounds of
the `υ_n` half (`sumU_le`) and of the `υ̌_n` half (`sumV_le`) are at most `C 2^n f(2^{n+2k})`, with
constants that do not depend on `f`, `n` or `k`. The second term of Lemma 7.21 carries a factor
`C₁ ⩾ 0` (the constant of `OpI1.I1Bound`). No stubs.
-/

namespace ErschlerZheng

namespace OpI2

open P7Dev

/-- `K = (1 - 2^{-(1-1/D')})⁻¹`, the constant of `P7Dev.sum_two_pow_mul_le`. -/
noncomputable def kK (D' : ℝ) : ℝ := (1 - (2 : ℝ) ^ (-(1 - 1 / D')))⁻¹

theorem kK_pos {D' : ℝ} (hD' : 1 < D') : 0 < kK D' := by
  unfold kK
  have hD'0 : 0 < D' := by linarith
  have hq1 : (2 : ℝ) ^ (-(1 - 1 / D')) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by have : 1 / D' < 1 := (div_lt_one hD'0).mpr hD'; linarith)
  have : 0 < 1 - (2 : ℝ) ^ (-(1 - 1 / D')) := by linarith
  positivity

/-- The `f`-independent constant of the second-term sum: `(1 - 2^{-(1-1/D)})⁻¹ M`. -/
noncomputable def kS (D : ℕ) (M : ℝ) : ℝ := (1 - (2 : ℝ) ^ (-(1 - 1 / (D : ℝ))))⁻¹ * M

theorem kS_nonneg (D : ℕ) (hD : 1 < D) (M : ℝ) (hM : 0 ≤ M) : 0 ≤ kS D M := by
  unfold kS
  have hD0 : (1 : ℝ) < D := by exact_mod_cast hD
  have hq1 : (2 : ℝ) ^ (-(1 - 1 / (D : ℝ))) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by have : 1 / (D : ℝ) < 1 := (div_lt_one (by linarith)).mpr hD0; linarith)
  have : 0 < 1 - (2 : ℝ) ^ (-(1 - 1 / (D : ℝ))) := by linarith
  positivity

/-- The bound `M` of `k^{1+2/D} 2^{-2(1/D - 1/D')k}`, chosen before `f`. -/
theorem exists_M (D : ℕ) (hD : 1 < D) {D' : ℝ} (hDD' : (D : ℝ) < D') :
    ∃ M, 0 ≤ M ∧ ∀ k : ℕ, (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
      (2 : ℝ) ^ (-(2 * (1 / (D : ℝ) - 1 / D') * k)) ≤ M := by
  have hD0 : (1 : ℝ) < D := by exact_mod_cast hD
  have hc : 0 < 2 * (1 / (D : ℝ) - 1 / D') := by
    have : 1 / D' < 1 / (D : ℝ) := one_div_lt_one_div_of_lt (by linarith) hDD'
    linarith
  obtain ⟨M, hM⟩ := exists_bound_rpow_mul_two_rpow (1 + 2 / (D : ℝ)) _ (by positivity) hc
  exact ⟨M, le_trans (by positivity) (hM 0), hM⟩

theorem sum_ite_le_range (n k : ℕ) (h : ℕ → ℝ) (h0 : ∀ j, 0 ≤ h j) :
    ∑ j ∈ Finset.range (n + 1), (if j + k ≤ n then h j else 0) ≤
      ∑ j ∈ Finset.range (n - k + 1), h j := by
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    omega
  · intro j _ _; exact h0 j

theorem sum_ite_two_pow_le (n k : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (if j + k ≤ n then (2 : ℝ) ^ j else 0) ≤ 2 * 2 ^ n / 2 ^ k := by
  by_cases hk : k ≤ n
  · refine (sum_ite_le_range n k _ (fun j => by positivity)).trans ?_
    rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
    have e : (2 : ℝ) ^ (n - k + 1) = 2 * 2 ^ n / 2 ^ k := by
      rw [eq_div_iff (by positivity), ← pow_add, show n - k + 1 + k = n + 1 by omega, pow_succ]
      ring
    rw [← e]
    norm_num
  · rw [Finset.sum_eq_zero (fun j hj => by rw [if_neg (by omega)])]
    positivity

section

variable {f : ℝ → ℝ} {D' : ℝ} (hf0 : ∀ s, 0 ≤ s → 0 ≤ f s)
  (hfr : ∀ s, 1 ≤ s → (2 : ℝ) ^ (-1 / D') ≤ f (2 * s) / f s)

include hf0 hfr in
/-- `P7Dev.exists_sum_second_term_le` with its constant made explicit (it does not depend on `f`). -/
theorem sum_second_le (D : ℕ) (hD : 1 < D) (hDD' : (D : ℝ) < D') (M : ℝ)
    (hM : ∀ k : ℕ, (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
      (2 : ℝ) ^ (-(2 * (1 / (D : ℝ) - 1 / D') * k)) ≤ M)
    (n k e₀ : ℕ) (he₀ : e₀ ≤ 2 * k) :
    ∑ j ∈ Finset.range (n + 1), (2 : ℝ) ^ j * (f (2 ^ (n + e₀)) * (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
        (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k - n))) ≤
      kS D M * (2 ^ n * f (2 ^ (n + 2 * k))) := by
  unfold kS
  have hD0 : (1 : ℝ) < D := by exact_mod_cast hD
  set q : ℝ := (2 : ℝ) ^ (-(1 - 1 / (D : ℝ))) with hq
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by have : 1 / (D : ℝ) < 1 := (div_lt_one (by linarith)).mpr hD0; linarith)
  have hq0 : 0 ≤ q := by positivity
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0)
  have hF : 0 ≤ f (2 ^ (n + 2 * k)) := hf0 _ (by positivity)
  have hfe : f (2 ^ (n + e₀)) ≤ (2 : ℝ) ^ ((2 * k : ℕ) / D') * f (2 ^ (n + 2 * k)) := by
    have h := pow_le hf0 hfr (n + e₀) (2 * k - e₀)
    rw [show n + e₀ + (2 * k - e₀) = n + 2 * k by omega] at h
    refine h.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (by linarith))) hF)
  have hterm : ∀ j ∈ Finset.range (n + 1),
      (2 : ℝ) ^ j * (f (2 ^ (n + e₀)) * (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
        (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k - n))) ≤
      q ^ (n - j) * (M * (2 ^ n * f (2 ^ (n + 2 * k)))) := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hk := hM k
    have e : (2 : ℝ) ^ j * (2 : ℝ) ^ ((2 * k : ℕ) / D') *
        (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k - n)) =
        q ^ (n - j) * 2 ^ n * (2 : ℝ) ^ (-(2 * (1 / (D : ℝ) - 1 / D') * k)) := by
      rw [hq, ← Real.rpow_natCast, ← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_natCast _ (n - j),
        ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num),
        ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
        ← Real.rpow_add (by norm_num)]
      congr 1
      push_cast [Nat.cast_sub hjn]
      ring
    calc (2 : ℝ) ^ j * (f (2 ^ (n + e₀)) * (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
          (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k - n))) ≤
        (2 : ℝ) ^ j * (((2 : ℝ) ^ ((2 * k : ℕ) / D') * f (2 ^ (n + 2 * k))) *
          (k : ℝ) ^ (1 + 2 / (D : ℝ)) * (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k - n))) := by
          gcongr
      _ = q ^ (n - j) * 2 ^ n * f (2 ^ (n + 2 * k)) * ((k : ℝ) ^ (1 + 2 / (D : ℝ)) *
            (2 : ℝ) ^ (-(2 * (1 / (D : ℝ) - 1 / D') * k))) := by
          linear_combination (f (2 ^ (n + 2 * k)) * (k : ℝ) ^ (1 + 2 / (D : ℝ))) * e
      _ ≤ q ^ (n - j) * 2 ^ n * f (2 ^ (n + 2 * k)) * M :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hM0 (mul_nonneg (by positivity) hF))
  calc ∑ j ∈ Finset.range (n + 1), q ^ (n - j) = ∑ i ∈ Finset.range (n + 1), q ^ i :=
        Finset.sum_range_reflect (fun i => q ^ i) (n + 1)
    _ ≤ ∑' i, q ^ i :=
        (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun i _ => pow_nonneg hq0 i)
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1

include hf0 hfr in
/-- The fixed factor `g_j⁻¹` (`υ̌_n`): `Σ_{m<j-1} 2^m f(2^m) + f(1) ⩽ 2K 2^j f(2^j)`. -/
theorem lowInv_real (hD' : 1 < D') (j : ℕ) (hj : 1 ≤ j) :
    ∑ m ∈ Finset.range (j - 1), (2 : ℝ) ^ m * f (2 ^ m) + f 1 ≤
      2 * kK D' * ((2 : ℝ) ^ j * f (2 ^ j)) := by
  have hnn : ∀ m : ℕ, 0 ≤ (2 : ℝ) ^ m * f (2 ^ m) := fun m =>
    mul_nonneg (by positivity) (hf0 _ (by positivity))
  set A := ∑ m ∈ Finset.range (j - 1 + 1), (2 : ℝ) ^ m * f (2 ^ m) with hA
  have h1 : ∑ m ∈ Finset.range (j - 1), (2 : ℝ) ^ m * f (2 ^ m) ≤ A :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun m _ _ => hnn m)
  have h2 : f 1 ≤ A := by
    have := Finset.single_le_sum (f := fun m : ℕ => (2 : ℝ) ^ m * f (2 ^ m)) (fun m _ => hnn m)
      (Finset.mem_range.mpr (Nat.succ_pos (j - 1)))
    simpa using this
  have h3 : A ≤ kK D' * (2 ^ (j - 1) * f (2 ^ (j - 1))) := by
    have := sum_two_pow_mul_le hD' hf0 hfr 0 (j - 1)
    simp only [add_zero] at this
    exact this
  have h4 : f (2 ^ (j - 1)) ≤ 2 * f (2 ^ j) := by
    have h := pow_le hf0 hfr (j - 1) 1
    rw [show j - 1 + 1 = j by omega] at h
    have hD'0 : 0 < D' := by linarith
    have hr : (2 : ℝ) ^ (((1 : ℕ) : ℝ) / D') ≤ 2 := by
      have : (2 : ℝ) ^ (((1 : ℕ) : ℝ) / D') ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by rw [Nat.cast_one, div_le_one hD'0]; linarith)
      rwa [Real.rpow_one] at this
    exact h.trans (mul_le_mul_of_nonneg_right hr (hf0 _ (by positivity)))
  have hK := (kK_pos hD').le
  have e : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
    rw [← pow_succ', show j - 1 + 1 = j by omega]
  calc ∑ m ∈ Finset.range (j - 1), (2 : ℝ) ^ m * f (2 ^ m) + f 1 ≤ 2 * A := by linarith
    _ ≤ 2 * (kK D' * (2 ^ (j - 1) * f (2 ^ (j - 1)))) := by linarith
    _ ≤ 2 * (kK D' * (2 ^ (j - 1) * (2 * f (2 ^ j)))) := by gcongr
    _ = 2 * kK D' * ((2 : ℝ) ^ j * f (2 ^ j)) := by rw [e]; ring

include hf0 hfr in
/-- The `υ_n` half summed over the levels: the fixed factors (`j + k ⩽ n`, by `term_low_le`) and
the levels of Lemma 7.21 (with its constant `C₁`). -/
theorem sumU_le (D : ℕ) (hD : 1 < D) (hDD' : (D : ℝ) < D') (M : ℝ)
    (hM : ∀ k : ℕ, (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
      (2 : ℝ) ^ (-(2 * (1 / (D : ℝ) - 1 / D') * k)) ≤ M)
    (C₁ : ℝ) (hC₁ : 0 ≤ C₁) (n k : ℕ) (hDk : D ≤ k) :
    ∑ j ∈ Finset.range (n + 1), ((if j + k ≤ n then (2 : ℝ) ^ j * (2 / 2 ^ n) *
        ∑ m ∈ Finset.range n, (2 : ℝ) ^ m * f (2 ^ m) else 0) +
      (2 : ℝ) ^ j * (f (2 ^ (j + 2 * k)) + C₁ * (f (2 ^ (n + D)) * (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
        (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k - n))))) ≤
      (4 * kK D' + kK D' + C₁ * kS D M) * (2 ^ n * f (2 ^ (n + 2 * k))) := by
  have hD0 : (1 : ℝ) < D := by exact_mod_cast hD
  have hD'1 : 1 < D' := by linarith
  have hD'2 : (2 : ℝ) ≤ D' := by
    have : (2 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  have hK := (kK_pos hD'1).le
  set F₀ := f (2 ^ (n + 2 * k)) with hF₀
  have hF0 : 0 ≤ F₀ := hf0 _ (by positivity)
  set S := ∑ m ∈ Finset.range n, (2 : ℝ) ^ m * f (2 ^ m) with hS
  have hnn : ∀ m : ℕ, 0 ≤ (2 : ℝ) ^ m * f (2 ^ m) := fun m =>
    mul_nonneg (by positivity) (hf0 _ (by positivity))
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun m _ => hnn m
  -- `S ⩽ K 2^n f(2^n) ⩽ K 2^n 2^{2k/D'} F₀`
  have hS1 : S ≤ kK D' * (2 ^ n * f (2 ^ n)) := by
    have h1 : S ≤ ∑ m ∈ Finset.range (n + 1), (2 : ℝ) ^ m * f (2 ^ m) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        (fun m _ _ => hnn m)
    have h2 := sum_two_pow_mul_le hD'1 hf0 hfr 0 n
    simp only [add_zero] at h2
    exact h1.trans h2
  have hfn : f (2 ^ n) ≤ 2 ^ k * F₀ := by
    have h := pow_le hf0 hfr n (2 * k)
    have hr : (2 : ℝ) ^ (((2 * k : ℕ) : ℝ) / D') ≤ 2 ^ k := by
      rw [← Real.rpow_natCast (2 : ℝ) k]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      rw [div_le_iff₀ (by linarith)]
      push_cast
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    exact h.trans (mul_le_mul_of_nonneg_right hr hF0)
  -- the low part
  have hlow : ∑ j ∈ Finset.range (n + 1), (if j + k ≤ n then (2 : ℝ) ^ j * (2 / 2 ^ n) * S
      else 0) ≤ 4 * kK D' * (2 ^ n * F₀) := by
    have e : ∀ j, (if j + k ≤ n then (2 : ℝ) ^ j * (2 / 2 ^ n) * S else 0) =
        (if j + k ≤ n then (2 : ℝ) ^ j else 0) * ((2 / 2 ^ n) * S) := by
      intro j; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun j _ => e j), ← Finset.sum_mul]
    have hX : 0 ≤ (2 / 2 ^ n) * S := by positivity
    calc (∑ j ∈ Finset.range (n + 1), (if j + k ≤ n then (2 : ℝ) ^ j else 0)) * ((2 / 2 ^ n) * S)
        ≤ (2 * 2 ^ n / 2 ^ k) * ((2 / 2 ^ n) * (kK D' * (2 ^ n * (2 ^ k * F₀)))) := by
          gcongr
          · exact sum_ite_two_pow_le n k
          · exact hS1.trans (by gcongr)
      _ = 4 * kK D' * (2 ^ n * F₀) := by
          field_simp
          ring
  -- the levels of Lemma 7.21
  have hhigh1 := sum_two_pow_mul_le hD'1 hf0 hfr (2 * k) n
  have hhigh2 := sum_second_le hf0 hfr D hD hDD' M hM n k D (by omega)
  have e : ∀ j : ℕ, ((if j + k ≤ n then (2 : ℝ) ^ j * (2 / 2 ^ n) * S else 0) +
      (2 : ℝ) ^ j * (f (2 ^ (j + 2 * k)) + C₁ * (f (2 ^ (n + D)) * (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
        (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k - n))))) =
      (if j + k ≤ n then (2 : ℝ) ^ j * (2 / 2 ^ n) * S else 0) +
        (2 : ℝ) ^ j * f (2 ^ (j + 2 * k)) +
        C₁ * ((2 : ℝ) ^ j * (f (2 ^ (n + D)) * (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
          (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k - n)))) := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hC2 := mul_le_mul_of_nonneg_left hhigh2 hC₁
  have hk1 : kK D' * (2 ^ n * F₀) = (1 - (2 : ℝ) ^ (-(1 - 1 / D')))⁻¹ * (2 ^ n * F₀) := rfl
  calc _ ≤ 4 * kK D' * (2 ^ n * F₀) + kK D' * (2 ^ n * F₀) + C₁ * (kS D M * (2 ^ n * F₀)) := by
        gcongr
        rw [hk1]; exact hhigh1
    _ = _ := by ring

include hf0 hfr in
/-- The `υ̌_n` half summed over the levels: the fixed factors (`j + k ⩽ n`, by `term_lowInv_le`
and `lowInv_real`) and the levels of Lemma 7.21 (with its constant `C₁`). -/
theorem sumV_le (D : ℕ) (hD : 3 ≤ D) (hDD' : (D : ℝ) < D') (M : ℝ)
    (hM : ∀ k : ℕ, (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
      (2 : ℝ) ^ (-(2 * (1 / (D : ℝ) - 1 / D') * k)) ≤ M)
    (C₁ : ℝ) (hC₁ : 0 ≤ C₁) (n k : ℕ) :
    ∑ j ∈ Finset.range (n + 1), ((if j + k ≤ n then 4 * kK D' * ((2 : ℝ) ^ j * f (2 ^ j)) else 0) +
      (2 : ℝ) ^ j * (f (2 ^ (j + 2 * k)) + C₁ * (f (2 ^ n) * (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
        (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k - n))))) ≤
      (4 * kK D' ^ 2 + kK D' + C₁ * kS D M) * (2 ^ n * f (2 ^ (n + 2 * k))) := by
  have hD0 : (3 : ℝ) ≤ D := by exact_mod_cast hD
  have hD'1 : 1 < D' := by linarith
  have hD'3 : (3 : ℝ) ≤ D' := by linarith
  have hK := (kK_pos hD'1).le
  set F₀ := f (2 ^ (n + 2 * k)) with hF₀
  have hF0 : 0 ≤ F₀ := hf0 _ (by positivity)
  have hnn : ∀ m : ℕ, 0 ≤ (2 : ℝ) ^ m * f (2 ^ m) := fun m =>
    mul_nonneg (by positivity) (hf0 _ (by positivity))
  -- the low part
  have hlow : ∑ j ∈ Finset.range (n + 1),
      (if j + k ≤ n then 4 * kK D' * ((2 : ℝ) ^ j * f (2 ^ j)) else 0) ≤
      4 * kK D' ^ 2 * (2 ^ n * F₀) := by
    by_cases hkn : k ≤ n
    · refine (sum_ite_le_range n k _ (fun j => mul_nonneg (by positivity) (hnn j))).trans ?_
      rw [← Finset.mul_sum]
      have h1 := sum_two_pow_mul_le hD'1 hf0 hfr 0 (n - k)
      simp only [add_zero] at h1
      have h2 : f (2 ^ (n - k)) ≤ 2 ^ k * F₀ := by
        have h := pow_le hf0 hfr (n - k) (3 * k)
        rw [show n - k + 3 * k = n + 2 * k by omega] at h
        have hr : (2 : ℝ) ^ (((3 * k : ℕ) : ℝ) / D') ≤ 2 ^ k := by
          rw [← Real.rpow_natCast (2 : ℝ) k]
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          rw [div_le_iff₀ (by linarith)]
          push_cast
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          nlinarith
        exact h.trans (mul_le_mul_of_nonneg_right hr hF0)
      have e2 : (2 : ℝ) ^ (n - k) * 2 ^ k = 2 ^ n := by
        rw [← pow_add, Nat.sub_add_cancel hkn]
      have hk1 : kK D' * (2 ^ (n - k) * f (2 ^ (n - k))) =
          (1 - (2 : ℝ) ^ (-(1 - 1 / D')))⁻¹ * (2 ^ (n - k) * f (2 ^ (n - k))) := rfl
      calc 4 * kK D' * ∑ j ∈ Finset.range (n - k + 1), (2 : ℝ) ^ j * f (2 ^ j)
          ≤ 4 * kK D' * (kK D' * (2 ^ (n - k) * f (2 ^ (n - k)))) := by
            gcongr
            rw [hk1]; exact h1
        _ ≤ 4 * kK D' * (kK D' * (2 ^ (n - k) * (2 ^ k * F₀))) := by gcongr
        _ = 4 * kK D' ^ 2 * (2 ^ n * F₀) := by rw [← e2]; ring
    · rw [Finset.sum_eq_zero (fun j hj => by rw [if_neg (by omega)])]
      positivity
  have hhigh1 := sum_two_pow_mul_le hD'1 hf0 hfr (2 * k) n
  have hhigh2 := sum_second_le hf0 hfr D (by omega) hDD' M hM n k 0 (by omega)
  simp only [add_zero] at hhigh2
  have e : ∀ j : ℕ, ((if j + k ≤ n then 4 * kK D' * ((2 : ℝ) ^ j * f (2 ^ j)) else 0) +
      (2 : ℝ) ^ j * (f (2 ^ (j + 2 * k)) + C₁ * (f (2 ^ n) * (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
        (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k - n))))) =
      (if j + k ≤ n then 4 * kK D' * ((2 : ℝ) ^ j * f (2 ^ j)) else 0) +
        (2 : ℝ) ^ j * f (2 ^ (j + 2 * k)) +
        C₁ * ((2 : ℝ) ^ j * (f (2 ^ n) * (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
          (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k - n)))) := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => e j), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hC2 := mul_le_mul_of_nonneg_left hhigh2 hC₁
  have hk1 : kK D' * (2 ^ n * F₀) = (1 - (2 : ℝ) ^ (-(1 - 1 / D')))⁻¹ * (2 ^ n * F₀) := rfl
  calc _ ≤ 4 * kK D' ^ 2 * (2 ^ n * F₀) + kK D' * (2 ^ n * F₀) +
        C₁ * (kS D M * (2 ^ n * F₀)) := by
        gcongr
        rw [hk1]; exact hhigh1
    _ = _ := by ring

end

end OpI2

end ErschlerZheng
end

section
/-!
# Basic facts about sections, `a`, and the generators `b_ω, c_ω, d_ω`

Development helpers for the Grigorchuk part of the Erschler–Zheng mission (not published).
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace GrigBasic

/-! ### Sections -/

theorem nil_smul (g : BinaryTreeAut) : ([] : List Bool) <• g = [] :=
  List.eq_nil_of_length_eq_zero (length_vertex_smul g [])

theorem sec_unique {g h : BinaryTreeAut} {v : List Bool}
    (H : ∀ w : List Bool, (v ++ w) <• g = (v <• g) ++ (w <• h)) : sec g v = h := by
  have key : ∀ w : List Bool, w <• sec g v = w <• h := by
    intro w
    have h1 := append_vertex_smul g v w
    rw [H w] at h1
    exact (List.append_cancel_left h1).symm
  have : (sec g v)⁻¹ = h⁻¹ := Subtype.ext (Equiv.ext fun w => key w)
  exact inv_injective this

theorem sec_mul (g h : BinaryTreeAut) (v : List Bool) :
    sec (g * h) v = sec g v * sec h (v <• g) := by
  apply sec_unique
  intro w
  rw [vertex_smul_mul, vertex_smul_mul, append_vertex_smul, append_vertex_smul,
    vertex_smul_mul]

theorem sec_nil (g : BinaryTreeAut) : sec g [] = g := by
  apply sec_unique
  intro w
  rw [nil_smul]
  rfl

theorem sec_append (g : BinaryTreeAut) (v u : List Bool) :
    sec g (v ++ u) = sec (sec g v) u := by
  apply sec_unique
  intro w
  rw [List.append_assoc, append_vertex_smul, append_vertex_smul, append_vertex_smul]
  simp only [List.append_assoc]

theorem sec_one (v : List Bool) : sec 1 v = 1 := by
  apply sec_unique
  intro w
  rfl

theorem sec_cons (g : BinaryTreeAut) (x : Bool) (u : List Bool) :
    sec g (x :: u) = sec (sec g [x]) u := by
  rw [← sec_append]
  rfl

/-! ### The root swap -/

theorem sec_inv (g : BinaryTreeAut) (v : List Bool) : sec g⁻¹ v = (sec g (v <• g⁻¹))⁻¹ := by
  have h1 := sec_mul g⁻¹ g v
  rw [inv_mul_cancel, sec_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

/-! ### `a` and the generators -/

theorem grigA_mul_self : grigA * grigA = 1 :=
  Subtype.ext (Equiv.ext fun w => grigAFun_involutive w)

theorem grigA_inv : grigA⁻¹ = grigA := inv_eq_of_mul_eq_one_right grigA_mul_self

theorem vertex_smul_grigA (v : List Bool) : v <• grigA = grigAFun v := by
  rw [vertex_smul_def, grigA_inv]
  rfl

theorem sec_grigA (x : Bool) : sec grigA [x] = 1 := by
  apply sec_unique
  intro w
  rw [vertex_smul_grigA, vertex_smul_grigA]
  rfl

theorem sec_grigA_cons (x : Bool) (u : List Bool) : sec grigA (x :: u) = 1 := by
  rw [sec_cons, sec_grigA, sec_one]

theorem gen_mul_self (ω : ℕ → Fin 3) (γ : BCD) : gen ω γ * gen ω γ = 1 :=
  Subtype.ext (Equiv.ext fun w => genFun_involutive ω γ w)

theorem gen_inv (ω : ℕ → Fin 3) (γ : BCD) : (gen ω γ)⁻¹ = gen ω γ :=
  inv_eq_of_mul_eq_one_right (gen_mul_self ω γ)

theorem vertex_smul_gen (ω : ℕ → Fin 3) (γ : BCD) (v : List Bool) :
    v <• gen ω γ = genFun ω γ v := by
  rw [vertex_smul_def, gen_inv]
  rfl

/-- The element `ω_0(γ) ∈ {a, id}`. -/
def letterElt (i : Fin 3) (γ : BCD) : BinaryTreeAut := if letterValue i γ then grigA else 1

theorem sec_gen_false (ω : ℕ → Fin 3) (γ : BCD) :
    sec (gen ω γ) [false] = letterElt (ω 0) γ := by
  apply sec_unique
  intro w
  rw [vertex_smul_gen, vertex_smul_gen]
  unfold letterElt
  by_cases h : letterValue (ω 0) γ
  · simp only [List.cons_append, List.nil_append, genFun, h, if_true]
    rw [vertex_smul_grigA]
    rfl
  · simp only [List.cons_append, List.nil_append, genFun, h]
    rfl

theorem sec_gen_true (ω : ℕ → Fin 3) (γ : BCD) :
    sec (gen ω γ) [true] = gen (shiftSeq ω 1) γ := by
  apply sec_unique
  intro w
  rw [vertex_smul_gen, vertex_smul_gen, vertex_smul_gen]
  simp [genFun]

theorem shiftSeq_shiftSeq (ω : ℕ → Fin 3) (m k : ℕ) :
    shiftSeq (shiftSeq ω m) k = shiftSeq ω (k + m) := by
  funext j
  simp only [shiftSeq]
  congr 1
  omega

theorem shiftSeq_zero (ω : ℕ → Fin 3) : shiftSeq ω 0 = ω := by
  funext j; simp [shiftSeq]

/-! ### Words -/

end GrigBasic

end ErschlerZheng
end

section
/-!
# Rays: prefixes, shifts, and the action of sections
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace RayBasic

open GrigBasic

theorem ray_ext {x y : Ray} (h : ∀ n, rayPrefix x n = rayPrefix y n) : x = y := by
  funext i
  have hx : i < (rayPrefix x (i + 1)).length := by simp [length_rayPrefix]
  rw [← getElem_rayPrefix x (i + 1) i hx, List.getElem_of_eq (h (i + 1)), getElem_rayPrefix]

theorem rayPrefix_add (x : Ray) (n m : ℕ) :
    rayPrefix x (n + m) = rayPrefix x n ++ rayPrefix (shiftRay x n) m := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    by_cases hi : i < n
    · rw [List.getElem_append_left (by rw [length_rayPrefix]; exact hi), getElem_rayPrefix]
    · rw [List.getElem_append_right (by rw [length_rayPrefix]; omega), getElem_rayPrefix]
      simp only [shiftRay, length_rayPrefix]
      congr 1
      omega

theorem shiftRay_smul (g : BinaryTreeAut) (x : Ray) (n : ℕ) :
    shiftRay (x <• g) n = shiftRay x n <• sec g (rayPrefix x n) := by
  apply ray_ext
  intro m
  have h1 : rayPrefix (x <• g) (n + m) =
      (rayPrefix x n <• g) ++ (rayPrefix (shiftRay x n) m <• sec g (rayPrefix x n)) := by
    rw [rayPrefix_smul, rayPrefix_add, append_vertex_smul]
  have h2 : rayPrefix (x <• g) (n + m) =
      rayPrefix (x <• g) n ++ rayPrefix (shiftRay (x <• g) n) m := rayPrefix_add _ _ _
  rw [h2, rayPrefix_smul] at h1
  rw [rayPrefix_smul]
  exact List.append_cancel_left h1

/-- `x = x_1 … x_n (𝔰ⁿ x)`. -/
theorem prepend_rayPrefix_shiftRay (x : Ray) (n : ℕ) : prepend (rayPrefix x n) (shiftRay x n) = x := by
  funext i
  unfold prepend
  split_ifs with h
  · rw [getElem_rayPrefix]
  · simp only [shiftRay, length_rayPrefix] at h ⊢
    congr 1; omega

theorem rayPrefix_prepend (u : List Bool) (x : Ray) :
    rayPrefix (prepend u x) u.length = u := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    simp [prepend, h2]

theorem shiftRay_prepend (u : List Bool) (x : Ray) : shiftRay (prepend u x) u.length = x := by
  funext i
  simp [shiftRay, prepend]

/-- `(v x')·g = (v·g)(x'·g_v)`. -/
theorem prepend_smul (g : BinaryTreeAut) (v : List Bool) (x : Ray) :
    prepend v x <• g = prepend (v <• g) (x <• sec g v) := by
  conv_lhs => rw [← prepend_rayPrefix_shiftRay (prepend v x <• g) v.length]
  rw [rayPrefix_smul, shiftRay_smul, rayPrefix_prepend, shiftRay_prepend]

theorem one_smul_ray (x : Ray) : x <• (1 : BinaryTreeAut) = x := one_smul _ x

end RayBasic

end ErschlerZheng
end

section
/-!
# The Gray code on finite words, and how the generators move it

For a word `w` of length `N`, `grayList w < 2^N`. The generator `a` changes it by `+1` when `w`
has an even number of zeros and by `-1` otherwise; a generator `γ_ω` either fixes `w` or changes
it by `-1` (even) or `+1` (odd). From every word there is a generator step up (below the top
value `2^N - 1`) and down (above `0`) whose section at `w` is trivial.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace GrayDev

open GrigBasic

theorem grayList_cons (b : Bool) (v : List Bool) :
    grayList (b :: v) = (b :: v).count false % 2 + 2 * grayList v := rfl

theorem grayList_append_true (w : List Bool) : grayList (w ++ [true]) = grayList w := by
  induction w with
  | nil => simp [grayList]
  | cons b v ih =>
    rw [List.cons_append, grayList_cons, grayList_cons, ih]
    simp [List.count_cons, List.count_append]

theorem grayList_append_replicate (w : List Bool) (m : ℕ) :
    grayList (w ++ List.replicate m true) = grayList w := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ', ← List.append_assoc, grayList_append_true, ih]

theorem sec_gen_cons_true (ω : ℕ → Fin 3) (γ : BCD) (u : List Bool) :
    sec (gen ω γ) (true :: u) = sec (gen (shiftSeq ω 1) γ) u := by
  rw [sec_cons, sec_gen_true]

theorem sec_gen_replicate (ω : ℕ → Fin 3) (γ : BCD) (k : ℕ) (z : List Bool) (hz : z ≠ []) :
    sec (gen ω γ) (List.replicate k true ++ false :: z) = 1 := by
  induction k generalizing ω with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    rw [sec_cons, sec_gen_false]
    obtain ⟨c, z', rfl⟩ := List.exists_cons_of_ne_nil hz
    unfold letterElt
    split_ifs
    · exact sec_grigA_cons c z'
    · exact sec_one _
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, sec_gen_cons_true, ih]

end GrayDev

end ErschlerZheng
end

section
/-!
# The Schreier graph of `1^∞` through the Gray code

Rays that are all ones from position `N` on are `prepend w 1^∞` with `|w| = N`; their Gray code
is `grayList w`. A generator moves the Gray code of such a ray by at most one, and from `w` to
`w'` of the same length there is a path of `|ḡ(w) - ḡ(w')|` generators with trivial sections at
the intermediate words, so it carries any tail along unchanged.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace SchreierDev

open GrigBasic RayBasic GrayDev

/-- `x_k = 1` for every `k ⩾ N`. -/
def AllOnesFrom (N : ℕ) (x : Ray) : Prop := ∀ k ≥ N, x k = true

theorem isCofinal_iff (x : Ray) : IsCofinal x ↔ ∃ N, AllOnesFrom N x :=
  Filter.eventually_atTop

theorem AllOnesFrom.mono {N M : ℕ} {x : Ray} (h : AllOnesFrom N x) (hNM : N ≤ M) :
    AllOnesFrom M x := fun k hk => h k (le_trans hNM hk)

theorem rayPrefix_oneRay (n : ℕ) : rayPrefix oneRay n = List.replicate n true := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2; rw [getElem_rayPrefix]; simp [oneRay]

theorem shiftRay_eq_oneRay {N : ℕ} {x : Ray} (h : AllOnesFrom N x) : shiftRay x N = oneRay := by
  funext i; simp only [shiftRay, oneRay]; exact h _ (by omega)

theorem grayCode_eq {N : ℕ} {x : Ray} (h : AllOnesFrom N x) :
    grayCode x = grayList (rayPrefix x N) := by
  unfold grayCode
  set M := maxZeroIndex x with hM
  have hMdef : M = sSup {k | 1 ≤ k ∧ x (k - 1) = false} := rfl
  have hbdd : ∀ k ∈ {k | 1 ≤ k ∧ x (k - 1) = false}, k ≤ N := by
    rintro k ⟨hk1, hk⟩
    by_contra hc
    have := h (k - 1) (by omega)
    rw [this] at hk
    exact Bool.noConfusion hk
  have hMN : M ≤ N := csSup_le' hbdd
  have hones : AllOnesFrom M x := by
    intro k hk
    by_contra hc
    have hmem : k + 1 ∈ {k | 1 ≤ k ∧ x (k - 1) = false} := by
      refine ⟨by omega, ?_⟩
      simpa using hc
    have := le_csSup ⟨N, hbdd⟩ hmem
    rw [← hMdef] at this
    omega
  have hsplit : rayPrefix x N = rayPrefix x M ++ List.replicate (N - M) true := by
    rw [show N = M + (N - M) by omega, rayPrefix_add, shiftRay_eq_oneRay hones,
      rayPrefix_oneRay]
    simp
  rw [hsplit, grayList_append_replicate]

theorem grayCode_oneRay : grayCode oneRay = 0 := by
  rw [grayCode_eq (N := 0) (x := oneRay) (fun k _ => rfl)]
  rfl

/-! ### Generators on rays that are eventually all ones -/

theorem genFun_replicate_true (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    genFun ω γ (List.replicate n true) = List.replicate n true := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, genFun, ih]

theorem oneRay_smul_gen (ω : ℕ → Fin 3) (γ : BCD) : oneRay <• gen ω γ = oneRay := by
  apply ray_ext
  intro n
  rw [rayPrefix_smul, rayPrefix_oneRay, vertex_smul_gen, genFun_replicate_true]

end SchreierDev

end ErschlerZheng
end

section
/-!
# Germ calculus (helpers for B2, B5, B6)

Composition of germ equalities and multiplicativity of germs come from B1 (imported).
-/

open scoped RightActions

namespace ErschlerZheng

namespace GermBase

set_option linter.unusedSectionVars false

variable {H : Type*} [Group H] {X : Type*} [TopologicalSpace X] [MulAction Hᵐᵒᵖ X]
  [ContinuousConstSMul Hᵐᵒᵖ X]

theorem rsmul_mul (y : X) (g h : H) : y <• (g * h) = (y <• g) <• h := by
  rw [MulOpposite.op_mul, mul_smul]

theorem rsmul_one (y : X) : y <• (1 : H) = y := by rw [MulOpposite.op_one, one_smul]

theorem rsmul_inv_eq {x : X} {h : H} (hh : x <• h = x) : x <• h⁻¹ = x := by
  conv_lhs => rw [← hh]
  rw [← rsmul_mul, mul_inv_cancel, rsmul_one]

theorem rsmul_inv_smul (y : X) (h : H) : (y <• h) <• h⁻¹ = y := by
  rw [← rsmul_mul, mul_inv_cancel, rsmul_one]

theorem germEq_refl (x : X) (g : H) : GermEq x g g := Filter.Eventually.of_forall fun _ => rfl

theorem GermEq.symm' {x : X} {g h : H} (e : GermEq x g h) : GermEq x h g := e.mono fun _ h => h.symm

theorem germEq_comp {x : X} {g₁ g₂ h₁ h₂ : H} (hg : GermEq x g₁ g₂) (hh : GermEq (x <• g₁) h₁ h₂) :
    GermEq x (g₁ * h₁) (g₂ * h₂) :=
  (germEq_mul_and_germ_mul x).1 g₁ g₂ h₁ h₂ hg hh

theorem germ_mul {x : X} {g h : H} (hg : x <• g = x) (hh : x <• h = x) :
    germ x (g * h) = germ x g * germ x h :=
  (germEq_mul_and_germ_mul x).2 g h hg hh

theorem germ_def {x : X} {h : H} (hh : x <• h = x) :
    germ x h = QuotientGroup.mk ⟨h, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top h, hh⟩⟩ := by
  unfold germ; rw [dif_pos hh]

theorem germ_one (x : X) : germ x (1 : H) = 1 := by
  rw [germ_def (rsmul_one x)]
  rfl

theorem germ_eq_iff {x : X} {h h' : H} (hh : x <• h = x) (hh' : x <• h' = x) :
    germ x h = germ x h' ↔ GermEq x h h' := by
  rw [germ_def hh, germ_def hh', QuotientGroup.eq]
  change GermEq x (h⁻¹ * h') 1 ↔ GermEq x h h'
  constructor
  · intro e
    have := germEq_comp (germEq_refl x h) (by rw [hh]; exact e)
    rw [mul_inv_cancel_left, mul_one] at this
    exact GermEq.symm' this
  · intro e
    have := germEq_comp (germEq_refl x h⁻¹) (by rw [rsmul_inv_eq hh]; exact e)
    rw [inv_mul_cancel] at this
    exact GermEq.symm' this

theorem conj_fix {o x : X} {σ h : H} (hσ : o <• σ = x) (hh : x <• h = x) :
    o <• (σ * h * σ⁻¹) = o := by
  rw [rsmul_mul, rsmul_mul, hσ, hh, ← hσ, rsmul_inv_smul]

theorem transport_spec {L : Subgroup H} {x y : X} (h : ∃ σ ∈ L, x <• σ = y) :
    transport L x y ∈ L ∧ x <• transport L x y = y := by
  unfold transport
  exact Classical.epsilon_spec (p := fun σ => σ ∈ L ∧ x <• σ = y) (by
    obtain ⟨σ, h1, h2⟩ := h; exact ⟨σ, h1, h2⟩)

theorem exists_L_of_mem {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) (x : X) {g : H}
    (hg : g ∈ G) : ∃ σ ∈ L, x <• σ = x <• g := by
  have : x <• g ∈ rightOrbit L x := by
    rw [hL.1 x]; exact ⟨g, hg, rfl⟩
  obtain ⟨σ, hσ, e⟩ := this
  exact ⟨σ, hσ, e.symm⟩

theorem exists_L_of_orbit {G L : Subgroup H} (hL : IsAuxiliary (X := X) G L) {o x : X}
    (hx : x ∈ rightOrbit G o) : ∃ σ ∈ L, o <• σ = x := by
  have : x ∈ rightOrbit L o := by rw [hL.1 o]; exact hx
  obtain ⟨σ, hσ, e⟩ := this
  exact ⟨σ, hσ, e.symm⟩

theorem orbit_smul {G : Subgroup H} {o x : X} (hx : x ∈ rightOrbit G o) {g : H} (hg : g ∈ G) :
    x <• g ∈ rightOrbit G o := by
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k * g, G.mul_mem hk hg, (rsmul_mul o k g).symm⟩

end GermBase

end ErschlerZheng
end

section
/-!
# Germs of `G_ω` read from sections along the ray (helpers for B3, B4)

For `k ∈ G_ω ⊔ L` and a ray `x` cofinal with `1^∞`, the sections of `k` along `x` are eventually
the sections along `1^∞` of an element `c ∈ {1, b_ω, c_ω, d_ω}`, i.e. `1` or `γ_{𝔰ⁿω}`; along a ray
not cofinal with `1^∞` they are eventually trivial. Two elements fixing `x` have the same germ at
`x` iff their sections along `x` eventually agree. Orbits and the finitary group come from A2.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ErschlerZheng

namespace GrigGermsDev

open GrigBasic RayBasic GrayDev SchreierDev GermBase

/-! ### Cylinders -/

theorem eventually_rayPrefix_eq (x : Ray) (n : ℕ) :
    ∀ᶠ y in nhds x, rayPrefix y n = rayPrefix x n := by
  have : ∀ᶠ y in nhds x, ∀ i : Fin n, y i = x i := by
    rw [Filter.eventually_all]
    intro i
    exact (continuous_apply (i : ℕ)).continuousAt (x := x)
      ((isOpen_discrete {x i}).mem_nhds rfl)
  filter_upwards [this] with y hy
  simp only [rayPrefix]
  congr 1
  funext i
  exact hy i

theorem exists_cylinder_subset (x : Ray) {U : Set Ray} (hU : U ∈ nhds x) :
    ∃ n, ∀ y : Ray, rayPrefix y n = rayPrefix x n → y ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hsub⟩ := hU
  obtain ⟨M, hM⟩ := hI.bddAbove
  refine ⟨M + 1, fun y hy => hsub fun i hi => ?_⟩
  have hiM : i < M + 1 := Nat.lt_succ_of_le (hM hi)
  have : y i = x i := by
    have h1 : i < (rayPrefix y (M + 1)).length := by rw [length_rayPrefix]; exact hiM
    rw [← getElem_rayPrefix y (M + 1) i h1, List.getElem_of_eq hy, getElem_rayPrefix]
  rw [this]
  exact mem_of_mem_nhds (ht i)

theorem cyl_smul (k : BinaryTreeAut) (x y : Ray) (n : ℕ) (hy : rayPrefix y n = rayPrefix x n) :
    y <• k = prepend (rayPrefix x n <• k) (shiftRay y n <• sec k (rayPrefix x n)) := by
  conv_lhs => rw [← prepend_rayPrefix_shiftRay y n]
  rw [hy, prepend_smul]

theorem germEq_of_sec {x : Ray} {k k' : BinaryTreeAut} {n : ℕ}
    (hv : rayPrefix x n <• k = rayPrefix x n <• k')
    (hs : sec k (rayPrefix x n) = sec k' (rayPrefix x n)) : GermEq x k k' := by
  filter_upwards [eventually_rayPrefix_eq x n] with y hy
  rw [cyl_smul k x y n hy, cyl_smul k' x y n hy, hv, hs]

theorem sec_eq_of_vertex_eq {u : List Bool} {k k' : BinaryTreeAut}
    (H : ∀ w : List Bool, (u ++ w) <• k = (u ++ w) <• k') : sec k u = sec k' u := by
  apply sec_unique
  intro w
  rw [H w, append_vertex_smul, ← (show u <• k = u <• k' by simpa using H [])]

theorem sec_eq_of_germEq {x : Ray} {k k' : BinaryTreeAut} (h : GermEq x k k') :
    ∃ N, ∀ n ≥ N, rayPrefix x n <• k = rayPrefix x n <• k' ∧
      sec k (rayPrefix x n) = sec k' (rayPrefix x n) := by
  obtain ⟨N, hN⟩ := exists_cylinder_subset x h
  refine ⟨N, fun n hn => ?_⟩
  have key : ∀ w : List Bool, (rayPrefix x n ++ w) <• k = (rayPrefix x n ++ w) <• k' := by
    intro w
    set y := prepend (rayPrefix x n ++ w) oneRay
    have hyN : rayPrefix y N = rayPrefix x N := by
      have h1 : rayPrefix y (n + w.length) = rayPrefix x n ++ w := by
        have := rayPrefix_prepend (rayPrefix x n ++ w) oneRay
        simpa [length_rayPrefix] using this
      have h2 : rayPrefix y N = (rayPrefix y (n + w.length)).take N := by
        rw [List.prefix_iff_eq_take.mp (rayPrefix_prefix y (show N ≤ n + w.length by omega))]
        simp [length_rayPrefix]
      rw [h2, h1, List.take_append_of_le_length (by rw [length_rayPrefix]; exact hn)]
      have := List.prefix_iff_eq_take.mp (rayPrefix_prefix x hn)
      rw [length_rayPrefix] at this
      exact this.symm
    have hy := hN y hyN
    have := congrArg (fun z => rayPrefix z (n + w.length)) hy
    simp only [rayPrefix_smul] at this
    have h1 : rayPrefix y (n + w.length) = rayPrefix x n ++ w := by
      have := rayPrefix_prepend (rayPrefix x n ++ w) oneRay
      simpa [length_rayPrefix] using this
    rwa [h1] at this
  exact ⟨by simpa using key [], sec_eq_of_vertex_eq key⟩

/-! ### The set `V = {1, b_ω, c_ω, d_ω}` -/

theorem sec_gen_replicate_true (ω : ℕ → Fin 3) (γ : BCD) (n : ℕ) :
    sec (gen ω γ) (List.replicate n true) = gen (shiftSeq ω n) γ := by
  induction n generalizing ω with
  | zero => rw [List.replicate_zero, sec_nil, shiftSeq_zero]
  | succ n ih =>
    rw [List.replicate_succ, sec_cons, sec_gen_true, ih, shiftSeq_shiftSeq]

/-! ### Cofinality classes are preserved (A2) -/

theorem mem_GL_of_G {ω : ℕ → Fin 3} {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) :
    g ∈ grigorchuk ω ⊔ finitary := (le_sup_left : grigorchuk ω ≤ _) hg

theorem mem_GL_of_L {ω : ℕ → Fin 3} {g : BinaryTreeAut} (hg : g ∈ finitary) :
    g ∈ grigorchuk ω ⊔ finitary := (le_sup_right : finitary ≤ _) hg

/-! ### Eventual sections -/

theorem first_zero (x : Ray) (hx : ∃ k, x k = false) :
    ∃ k, x k = false ∧ ∀ j < k, x j = true := by
  classical
  exact ⟨Nat.find hx, Nat.find_spec hx, fun j hj => by simpa using Nat.find_min hx hj⟩

theorem rayPrefix_first_zero' (x : Ray) (k : ℕ) (hk : x k = false) (hmin : ∀ j < k, x j = true) :
    rayPrefix x (k + 1) = List.replicate k true ++ [false] := by
  apply List.ext_getElem
  · simp [length_rayPrefix]
  · intro i h1 h2
    rw [getElem_rayPrefix]
    simp only [length_rayPrefix] at h1
    by_cases hi : i < k
    · rw [List.getElem_append_left (by simpa using hi)]; simp [hmin i hi]
    · rw [List.getElem_append_right (by simpa using hi)]
      have : i = k := by omega
      subst this; simp [hk]

theorem rayPrefix_first_zero (x : Ray) (k : ℕ) (hk : x k = false) (hmin : ∀ j < k, x j = true)
    (n : ℕ) (hn : k + 2 ≤ n) :
    ∃ z : List Bool, z ≠ [] ∧ rayPrefix x n = List.replicate k true ++ false :: z := by
  refine ⟨rayPrefix (shiftRay x (k + 1)) (n - (k + 1)), ?_, ?_⟩
  · intro h
    have := congrArg List.length h
    simp [length_rayPrefix] at this
    omega
  · rw [show n = (k + 1) + (n - (k + 1)) by omega, rayPrefix_add, rayPrefix_first_zero' x k hk hmin]
    simp [show k + 1 + (n - (k + 1)) - (k + 1) = n - (k + 1) by omega]

end GrigGermsDev

end ErschlerZheng
end

section
/-!
# B3: Example 3.2 (p. 18)

Germs of `G_ω` at a ray `x` are read from the sections along `x`: two elements fixing `x` have the
same germ iff their sections along `x` eventually agree (`GrigGermsDev`). Along a ray not cofinal
with `1^∞` the sections are eventually trivial; along a cofinal ray they are eventually `1` or
`γ_{𝔰ⁿω}`. Orbits and level transitivity come from A2 and the Gray-code path.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace B3Dev

open GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev

theorem germ_eq_of_sec' {x : Ray} {k k' : BinaryTreeAut} (hk : x <• k = x) (hk' : x <• k' = x)
    {N : ℕ} (h : ∀ n ≥ N, sec k (rayPrefix x n) = sec k' (rayPrefix x n)) :
    germ x k = germ x k' := by
  rw [germ_eq_iff hk hk']
  refine germEq_of_sec (n := N) ?_ (h N le_rfl)
  rw [← rayPrefix_smul, ← rayPrefix_smul, hk, hk']

theorem sec_eq_of_germ {x : Ray} {k k' : BinaryTreeAut} (hk : x <• k = x) (hk' : x <• k' = x)
    (h : germ x k = germ x k') : ∃ N, ∀ n ≥ N, sec k (rayPrefix x n) = sec k' (rayPrefix x n) := by
  obtain ⟨N, hN⟩ := sec_eq_of_germEq ((germ_eq_iff hk hk').mp h)
  exact ⟨N, fun n hn => (hN n hn).2⟩

theorem one_fix (x : Ray) : x <• (1 : BinaryTreeAut) = x := one_smul_ray x

end B3Dev

end ErschlerZheng
end

section
/-!
# B4: germs read from sections (p. 42, the general-`ω` Fact 4.1)

`(g, x) ∈ ℋ^b` iff the sections of `g` along `x` are eventually `1` or `b_{𝔰ⁿω}` (conjugating by
the finitary transports changes no deep section). If every level-`n` section is in
`{1, a, b_{𝔰ⁿω}}`, that holds along every cofinal ray. Conversely the "bad" vertices (section not
in `{1, a, b_{𝔰^{|v|}ω}}`) form a subtree; if it were infinite, compactness of `∂T` would give a ray
along which every section is bad, while along every ray the sections are eventually good.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace B4Dev

open GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev B3Dev

theorem sec_gen_along (ω' : ℕ → Fin 3) (γ : BCD) (y : Ray) :
    (∃ N, ∀ m ≥ N, sec (gen ω' γ) (rayPrefix y m) = 1) ∨ y = oneRay := by
  by_cases hz : ∃ k, y k = false
  · left
    obtain ⟨k, hk, hmin⟩ := first_zero y hz
    refine ⟨k + 2, fun m hm => ?_⟩
    obtain ⟨z, hz, e⟩ := rayPrefix_first_zero y k hk hmin m hm
    rw [e, sec_gen_replicate ω' γ k z hz]
  · right
    push Not at hz
    exact funext fun k => by simpa [oneRay] using hz k

/-- Conjugating by a finitary transport does not change deep sections. -/
theorem sec_conj_L {σ k : BinaryTreeAut} (hσ : σ ∈ finitary) {x : Ray} (hσx : oneRay <• σ = x)
    (hk : x <• k = x) :
    ∃ N, ∀ n ≥ N, sec (σ * k * σ⁻¹) (List.replicate n true) = sec k (rayPrefix x n) := by
  obtain ⟨m, hm⟩ := hσ
  refine ⟨m, fun n hn => ?_⟩
  have h1 : sec σ (List.replicate n true) = 1 :=
    sec_eq_one_of_le σ hn hm _ (List.length_replicate)
  have hp : List.replicate n true <• σ = rayPrefix x n := by
    rw [← rayPrefix_oneRay, ← rayPrefix_smul, hσx]
  have hpk : rayPrefix x n <• k = rayPrefix x n := by rw [← rayPrefix_smul, hk]
  have hpσ : rayPrefix x n <• σ⁻¹ = List.replicate n true := by
    rw [← hp, vertex_smul_smul_inv]
  rw [sec_mul, sec_mul, hp, vertex_smul_mul, hp, hpk, sec_inv, hpσ, h1, inv_one, one_mul, mul_one]

theorem sec_mul_L {σ : BinaryTreeAut} (hσ : σ ∈ finitary) (g : BinaryTreeAut) (x : Ray) :
    ∃ N, ∀ n ≥ N, sec (g * σ⁻¹) (rayPrefix x n) = sec g (rayPrefix x n) := by
  obtain ⟨m, hm⟩ := finitary.inv_mem hσ
  refine ⟨m, fun n hn => ?_⟩
  rw [sec_mul, sec_eq_one_of_le σ⁻¹ hn hm _ (by rw [length_vertex_smul, length_rayPrefix]),
    mul_one]

theorem mem_zpowers_sq {G : Type*} [Group G] {θ y : G} (hsq : θ ^ (2 : ℤ) = 1)
    (hy : y ∈ Subgroup.zpowers θ) : y = 1 ∨ y = θ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [zpow_eq_zpow_emod k hsq]
  rcases Int.emod_two_eq k with h | h <;> rw [h]
  · left; exact zpow_zero θ
  · right; exact zpow_one θ

end B4Dev

end ErschlerZheng
end

section
/-!
# Proposition 7.12 as stated fails for `υ̌_n` (prover 3, item 3)

The bound of Proposition 7.12 is uniform in `f`, and `f(0)` is free (only `f ⩾ 0`, `f`
non-increasing on `[0, ∞)` and the ratio condition on `[1, ∞)` are asked). The term `x = o = 1^∞`
of the sum is `f(0) · υ̌_n{g : (g, o) ∉ ℋ^b}`. For `υ_n` that mass is `0` (every factor `γ_j` acts at a
point whose first `j + 1` digits are `1`, where its germ is good). For `υ̌_n` it is not: with
`D = 3`, `ω = (201)^∞`, `k ≡ 3`, `n = 6`, the element `g_1 = a c a c` is `θ_6(e_1, γ)` for every `γ`, so
`υ̌_6(g_1⁻¹) = υ_6(g_1) ⩾ 2⁻⁶`, and the sections of `g_1⁻¹ = c a c a` along `1^∞` are `c_{𝔰ⁿω}`
(`n ⩾ 2`), so `(g_1⁻¹, o) ∉ ℋ^b`. Taking `f = 1` on `(0, ∞)` and `f(0) = M` large contradicts the
`υ̌` inequality.

The sum is a genuine (summable) sum: every `g ∈ G_ω` has only finitely many points where its
sections are not eventually `1` or `b_{𝔰ⁿω}` (closure induction: generators have at most `1^∞`), and
`υ̌_6` has finite support.
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErschlerZheng

namespace P3P712Dev

open GrigBasic RayBasic GrayDev SchreierDev GermBase GrigGermsDev B3Dev B4Dev

/-! ### Germs read from sections, point by point -/

/-- The sections of `g` along `x` are eventually `1`, or eventually `b_{𝔰ⁿω}`. -/
def GoodAt (ω : ℕ → Fin 3) (g : BinaryTreeAut) (x : Ray) : Prop :=
  ∃ N, (∀ n ≥ N, sec g (rayPrefix x n) = 1) ∨
    (∀ n ≥ N, sec g (rayPrefix x n) = gen (shiftSeq ω n) .b)

theorem goodAt_mul (ω : ℕ → Fin 3) {g h : BinaryTreeAut} {x : Ray} (hg : GoodAt ω g x)
    (hh : GoodAt ω h (x <• g)) : GoodAt ω (g * h) x := by
  obtain ⟨N, hN⟩ := hg
  obtain ⟨M, hM⟩ := hh
  have e : ∀ n, sec (g * h) (rayPrefix x n) =
      sec g (rayPrefix x n) * sec h (rayPrefix (x <• g) n) := fun n => by
    rw [sec_mul, rayPrefix_smul]
  refine ⟨max N M, ?_⟩
  rcases hN with hN | hN <;> rcases hM with hM | hM
  · exact Or.inl fun n hn => by rw [e, hN n (by omega), hM n (by omega), one_mul]
  · exact Or.inr fun n hn => by rw [e, hN n (by omega), hM n (by omega), one_mul]
  · exact Or.inr fun n hn => by rw [e, hN n (by omega), hM n (by omega), mul_one]
  · exact Or.inl fun n hn => by rw [e, hN n (by omega), hM n (by omega), gen_mul_self]

theorem goodAt_inv (ω : ℕ → Fin 3) {g : BinaryTreeAut} {x : Ray} (hg : GoodAt ω g x) :
    GoodAt ω g⁻¹ (x <• g) := by
  obtain ⟨N, hN⟩ := hg
  have e : ∀ n, sec g⁻¹ (rayPrefix (x <• g) n) = (sec g (rayPrefix x n))⁻¹ := fun n => by
    rw [sec_inv, rayPrefix_smul, vertex_smul_smul_inv]
  refine ⟨N, ?_⟩
  rcases hN with hN | hN
  · exact Or.inl fun n hn => by rw [e, hN n hn, inv_one]
  · exact Or.inr fun n hn => by rw [e, hN n hn, gen_inv]

theorem goodAt_one (ω : ℕ → Fin 3) (x : Ray) : GoodAt ω 1 x :=
  ⟨0, Or.inl fun n _ => sec_one _⟩

theorem goodAt_grigA (ω : ℕ → Fin 3) (x : Ray) : GoodAt ω grigA x := by
  refine ⟨1, Or.inl fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : rayPrefix x (m + 1) = x 0 :: rayPrefix (shiftRay x 1) m := by
    simp [rayPrefix, List.ofFn_succ, shiftRay]
  rw [this, sec_grigA_cons]

theorem goodAt_gen (ω : ℕ → Fin 3) (γ : BCD) {x : Ray} (hx : x ≠ oneRay) :
    GoodAt ω (gen ω γ) x := by
  rcases sec_gen_along ω γ x with ⟨N, hN⟩ | h
  · exact ⟨N, Or.inl hN⟩
  · exact absurd h hx

theorem goodAt_gen_b (ω : ℕ → Fin 3) (x : Ray) : GoodAt ω (gen ω .b) x := by
  by_cases hx : x = oneRay
  · subst hx
    exact ⟨0, Or.inr fun n _ => by rw [rayPrefix_oneRay, sec_gen_replicate_true]⟩
  · exact goodAt_gen ω .b hx

/-- Every element of `G_ω` has sections eventually `1` or `b` along all but finitely many rays. -/
theorem finite_not_goodAt (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) :
    {x | ¬ GoodAt ω g x}.Finite := by
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · simp [goodAt_grigA]
    · simp [goodAt_gen_b]
    · refine (Set.finite_singleton oneRay).subset fun x hx => ?_
      by_contra h
      exact hx (goodAt_gen ω .c h)
    · refine (Set.finite_singleton oneRay).subset fun x hx => ?_
      by_contra h
      exact hx (goodAt_gen ω .d h)
  | one => simp [goodAt_one]
  | mul g h _ _ ihg ihh =>
    refine (ihg.union (ihh.image fun y => y <• g⁻¹)).subset fun x hx => ?_
    by_cases h1 : GoodAt ω g x
    · right
      refine ⟨x <• g, fun h2 => hx (goodAt_mul ω h1 h2), ?_⟩
      exact rsmul_inv_smul x g
    · exact Or.inl h1
  | inv g _ ihg =>
    refine (ihg.image fun y => y <• g).subset fun x hx => ?_
    refine ⟨x <• g⁻¹, fun h2 => hx ?_, ?_⟩
    · have := goodAt_inv ω h2
      rwa [← rsmul_mul, inv_mul_cancel, rsmul_one] at this
    · show (x <• g⁻¹) <• g = x
      rw [← rsmul_mul, inv_mul_cancel, rsmul_one]

/-- Good sections give a germ in `ℋ^b` (as in B4). -/
theorem mem_of_goodAt (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) {x : Ray}
    (hx : x ∈ orbitOne ω) (hG : GoodAt ω g x) : (g, x) ∈ letterGerms ω .b := by
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
  have hL : IsAuxiliary (X := Ray) (grigorchuk ω) finitary := hA2.2.2 ω
  have hbo := oneRay_smul_gen ω .b
  have hgGL : g ∈ grigorchuk ω ⊔ finitary := mem_GL_of_G hg
  obtain ⟨hσL, hσ⟩ := transport_spec (exists_L_of_mem hL x hg)
  set σ := transport finitary x (x <• g)
  obtain ⟨hρL, hρ⟩ := transport_spec (exists_L_of_orbit hL hx)
  set ρ := transport finitary oneRay x
  have hk : x <• (g * σ⁻¹) = x := by rw [rsmul_mul, ← hσ, rsmul_inv_smul]
  have hkGL : g * σ⁻¹ ∈ grigorchuk ω ⊔ finitary :=
    Subgroup.mul_mem _ hgGL (mem_GL_of_L (finitary.inv_mem hσL))
  refine ⟨hg, hx, g * σ⁻¹, hkGL, hk, rfl, ?_⟩
  have hK : oneRay <• (ρ * (g * σ⁻¹) * ρ⁻¹) = oneRay := conj_fix hρ hk
  obtain ⟨N1, hN1⟩ := sec_conj_L hρL hρ hk
  obtain ⟨N3, hN3⟩ := sec_mul_L hσL g x
  obtain ⟨N, hN⟩ := hG
  rcases hN with hN | hN
  · have : germ oneRay (ρ * (g * σ⁻¹) * ρ⁻¹) = 1 := by
      rw [← germ_one oneRay]
      exact germ_eq_of_sec' hK (one_fix oneRay) (N := max N (max N1 N3)) fun n hn => by
        rw [rayPrefix_oneRay, hN1 n (by omega), hN3 n (by omega), hN n (by omega), sec_one]
    rw [this]; exact Subgroup.one_mem _
  · have : germ oneRay (ρ * (g * σ⁻¹) * ρ⁻¹) = germ oneRay (gen ω .b) :=
      germ_eq_of_sec' hK hbo (N := max N (max N1 N3)) fun n hn => by
        rw [rayPrefix_oneRay, hN1 n (by omega), hN3 n (by omega), hN n (by omega),
          sec_gen_replicate_true]
    rw [this]; exact Subgroup.mem_zpowers _

/-- A germ in `ℋ^b` has good sections (as in B4). -/
theorem goodAt_of_mem (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) {x : Ray}
    (hx : x ∈ orbitOne ω) (hmem : (g, x) ∈ letterGerms ω .b) : GoodAt ω g x := by
  have hA2 := isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary
  have hL : IsAuxiliary (X := Ray) (grigorchuk ω) finitary := hA2.2.2 ω
  have hbo := oneRay_smul_gen ω .b
  have hsq : germ oneRay (gen ω .b) ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← germ_mul hbo hbo, gen_mul_self, germ_one]
  obtain ⟨-, -, hmem⟩ := hmem
  dsimp only at hmem
  obtain ⟨hσL, hσ⟩ := transport_spec (exists_L_of_mem hL x hg)
  set σ := transport finitary x (x <• g)
  obtain ⟨h, hhGL, hhx, hhe, hho⟩ := hmem
  obtain ⟨hρL, hρ⟩ := transport_spec (exists_L_of_orbit hL hx)
  set ρ := transport finitary oneRay x
  have hk : x <• (g * σ⁻¹) = x := by rw [rsmul_mul, ← hσ, rsmul_inv_smul]
  have hK : oneRay <• (ρ * h * ρ⁻¹) = oneRay := conj_fix hρ hhx
  obtain ⟨N1, hN1⟩ := sec_conj_L hρL hρ hhx
  obtain ⟨N2, hN2⟩ := sec_eq_of_germ hhx hk hhe
  obtain ⟨N3, hN3⟩ := sec_mul_L hσL g x
  rcases mem_zpowers_sq hsq hho with e | e
  · obtain ⟨N4, hN4⟩ := sec_eq_of_germ hK (one_fix oneRay) (e.trans (germ_one _).symm)
    refine ⟨max (max N1 N2) (max N3 N4), Or.inl fun n hn => ?_⟩
    rw [← hN3 _ (by omega), ← hN2 _ (by omega), ← hN1 _ (by omega), ← rayPrefix_oneRay,
      hN4 _ (by omega), sec_one]
  · obtain ⟨N4, hN4⟩ := sec_eq_of_germ hK hbo e
    refine ⟨max (max N1 N2) (max N3 N4), Or.inr fun n hn => ?_⟩
    rw [← hN3 _ (by omega), ← hN2 _ (by omega), ← hN1 _ (by omega), ← rayPrefix_oneRay,
      hN4 _ (by omega), rayPrefix_oneRay, sec_gen_replicate_true]

/-! ### The witness: `D = 3`, `ω = (201)^∞`, `k ≡ 3`, `n = 6` -/

/-- `ω = (201)^∞`. -/
def ω₁ : ℕ → Fin 3 := fun i => if i % 3 = 0 then 2 else if i % 3 = 1 then 0 else 1

/-- `k_n = 3`. -/
def k₁ : ℕ → ℕ := fun _ => 3

/-! ### `Λ_n` is finite; `Λ_6` is non-empty -/

theorem finite_vSet (D : ℕ) (ω : ℕ → Fin 3) (j k : ℕ) : (vSet D ω j k).Finite := by
  apply Set.Finite.subset ((List.finite_length_eq Bool k).image fun u =>
    List.replicate (D - j % D) true ++ u ++ List.replicate (frM D ω (ellIndex D k j) + 2) true ++
      [false])
  rintro v ⟨u, hu, rfl⟩
  exact ⟨u, hu.1, rfl⟩

theorem finite_fSet (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (j n : ℕ) : (fSet D ω k j n).Finite := by
  unfold fSet
  split_ifs
  · apply Set.Finite.subset ((finite_vSet D ω j (2 * k n)).image (gTilde ω j))
    rintro g ⟨v, hv, -, rfl⟩
    exact ⟨v, hv, rfl⟩
  · exact Set.finite_singleton _

theorem cpl_cons_true (u : List Bool) :
    commonPrefixLength (true :: u) oneRay = commonPrefixLength u oneRay + 1 := by
  simp [commonPrefixLength, rayPrefix_oneRay, List.replicate_succ, List.takeWhile_cons]

theorem cpl_replicate_append (N : ℕ) (w : List Bool) :
    N ≤ commonPrefixLength (List.replicate N true ++ w) oneRay := by
  induction N with
  | zero => exact Nat.zero_le _
  | succ N ih =>
    rw [List.replicate_succ, List.cons_append, cpl_cons_true]
    omega

theorem nonempty_fSet (i : Fin 6) : (fSet 3 ω₁ k₁ (i + 1) 6).Nonempty := by
  unfold fSet
  split_ifs with h
  · set m := frM 3 ω₁ (ellIndex 3 (2 * k₁ 6) (i + 1))
    set v := List.replicate (3 - (i + 1) % 3) true ++ List.replicate (2 * k₁ 6) true ++
      List.replicate (m + 2) true ++ [false]
    refine ⟨gTilde ω₁ (i + 1) v, v, ⟨List.replicate (2 * k₁ 6) true, ⟨by simp, ?_⟩, rfl⟩, ?_, rfl⟩
    · intro j hj _; simp
    · have : v = List.replicate (3 - (i + 1) % 3 + 2 * k₁ 6) true ++
          (List.replicate (m + 2) true ++ [false]) := by
        simp only [v, List.replicate_add, List.append_assoc]
      rw [this]
      refine le_trans ?_ (cpl_replicate_append _ _)
      have := i.2
      simp only [k₁]
      omega
  · exact Set.singleton_nonempty _

instance (i : Fin 6) : Finite (fSet 3 ω₁ k₁ (i + 1) 6) := (finite_fSet _ _ _ _ _).to_subtype

instance : Finite (LambdaN 3 ω₁ k₁ 6) := inferInstance

instance : Nonempty (fProd 3 ω₁ k₁ 6) :=
  ⟨fun i => ⟨(nonempty_fSet i).some, (nonempty_fSet i).some_mem⟩⟩

/-! ### `υ_6(g_1) ⩾ 2⁻⁶` -/

/-! ### Finite support and summability -/

end P3P712Dev

end ErschlerZheng
end

section
/-!
# Proposition 7.12, `υ_n` half: no mass at `x = 1^∞` (prover 3, item 3)

For every `p ∈ Λ_n`, `(θ_n(p), 1^∞) ∈ ℋ^b`, so `υ_n{g : (g, 1^∞) ∉ ℋ^b} = 0`. In
`θ = γ_n^{ε_n} ⋯ γ_1^{ε_1}` the factor `γ_j` acts at `1^∞·γ_n^{ε_n}⋯γ_{j+1}^{ε_{j+1}}`, which begins with
`1^{j+1}` because every `γ_i ∈ St(L_i)`; points beginning with `1^{j+1}` are not bad for `γ_j` (the
bad points have `j + 1 + Σ_{i ⩽ j+1} x_i` odd); and good germs compose (sections eventually `1` or
`b`). A reduction to the Construction milestones (7.1)/Lemma 5.6 (`seqG`), Lemma 7.9 (`gTilde`),
`B_j` and (7.16).
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ErschlerZheng

namespace P3U0Dev

open GrigBasic RayBasic SchreierDev GermBase GrigGermsDev P3P712Dev

/-- Products of factors with good sections at the successive points have good sections. -/
theorem goodAt_list_prod (ω : ℕ → Fin 3) :
    ∀ (L : List BinaryTreeAut) (y : Ray),
      (∀ t (ht : t < L.length), GoodAt ω L[t] (y <• (L.take t).prod)) → GoodAt ω L.prod y
  | [], y, _ => goodAt_one ω y
  | h :: L, y, H => by
    rw [List.prod_cons]
    refine goodAt_mul ω ?_ ?_
    · have := H 0 (by simp)
      simpa using this
    · refine goodAt_list_prod ω L (y <• h) fun t ht => ?_
      have := H (t + 1) (by simp; omega)
      rw [List.getElem_cons_succ, List.take_succ_cons, List.prod_cons, rsmul_mul] at this
      exact this

section

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k)
  (n : ℕ) (hn : D ∣ n)

include hω hk hn

/-- Every factor `γ_{i+1}` lies in `St(L_{i+1})`. -/
theorem levelStab_factor (p : LambdaN D ω k n) (i : Fin n) :
    (p.2 i : BinaryTreeAut) ∈ levelStab (grigorchuk ω) (i + 1) := by
  have h := (p.2 i).2
  unfold fSet at h
  split_ifs at h with hc
  · obtain ⟨v, hv, -, e⟩ := h
    rw [e]
    have hDk : D ∣ 2 * k n := Dvd.dvd.mul_left ((hk.2 n (by omega) hn).2) 2
    exact ((exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem D ω hω (i + 1) (by omega)
      (2 * k n) hDk v hv).2.2 (by rw [hc.1]; decide)).1
  · rw [Set.mem_singleton_iff.mp h]
    exact ((seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω).1 (i + 1)
      (by omega)).1

theorem mem_G_factor (p : LambdaN D ω k n) (i : Fin n) :
    (p.2 i : BinaryTreeAut) ∈ grigorchuk ω :=
  (Subgroup.mem_inf.mp (levelStab_factor D ω hω k hk n hn p i)).1

end

end P3U0Dev

end ErschlerZheng
end

section
/-!
# The orbit chain `P_μ` and its step probabilities in `[0, ∞]` (helpers for B8)

`ofReal (P^{n+1}(y, x)) = Σ_g μ(g) ofReal (P^n(y·g, x))`, so `green` counts the expected visits of
`o·W_n`.
-/

open scoped RightActions ENNReal

namespace ErschlerZheng

namespace B8MarkovDev

open scoped Classical

variable {H : Type*} [Group H] {X : Type*} [MulAction Hᵐᵒᵖ X]

theorem orbit_smul' {G : Subgroup H} {o x : X} (hx : x ∈ rightOrbit G o) {g : H} (hg : g ∈ G) :
    x <• g ∈ rightOrbit G o := by
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k * g, G.mul_mem hk hg, by rw [MulOpposite.op_mul, mul_smul]⟩

variable [DecidableEq X]

end B8MarkovDev

end ErschlerZheng
end

section
/-!
# Proposition 7.12, first step of §7.6 (p. 53): the sub-groupoid union bound (prover 7)

If `θ_n(ε, γ) = γ_n^{ε_n} ⋯ γ_1^{ε_1}` has a germ outside `ℋ^b` at `x`, then some factor with
`ε_j = 1` has a germ outside `ℋ^b` at the point where it acts, `x·γ_n^{ε_n} ⋯ γ_{j+1}^{ε_{j+1}}`;
likewise for `θ_n(ε, γ)⁻¹ = γ_1^{-ε_1} ⋯ γ_n^{-ε_n}`, whose factor `γ_j^{-1}` acts at
`x·γ_1^{-ε_1} ⋯ γ_{j-1}^{-ε_{j-1}}`. Germs in `ℋ^b` are exactly the good germs (sections eventually
`1` or `b`, prover 3's `GoodAt`), and good germs compose.

Rests on what `P3U0` rests on (the membership `γ_j ∈ G_ω`: F1, F7 via the §7.2 stubs; B1, A2).
-/

open scoped RightActions
open Garrido

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ErschlerZheng

namespace P7Dev

open GrigBasic P3P712Dev P3U0Dev

section

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k)
  (n : ℕ) (hn : D ∣ n)

include hω hk hn

theorem orbit_list_prod {x : Ray} (hx : x ∈ orbitOne ω) (L : List BinaryTreeAut)
    (hL : ∀ h ∈ L, h ∈ grigorchuk ω) : x <• L.prod ∈ orbitOne ω :=
  B8MarkovDev.orbit_smul' hx ((grigorchuk ω).list_prod_mem hL)

/-- The union bound for `θ_n`: a bad germ of the product comes from a bad germ of a factor
`γ_j` (`ε_j = 1`) at the point `x·γ_n^{ε_n} ⋯ γ_{j+1}^{ε_{j+1}}` (Lean: position `t` of the list,
`j - 1 = t.rev`). -/
theorem exists_bad_factor (p : LambdaN D ω k n) {x : Ray} (hx : x ∈ orbitOne ω)
    (hbad : (theta D ω k n p, x) ∉ letterGerms ω .b) :
    ∃ t : Fin n, p.1 t.rev = true ∧
      ((p.2 t.rev : BinaryTreeAut), x <• ((List.ofFn fun i : Fin n =>
        (p.2 i.rev : BinaryTreeAut) ^ (p.1 i.rev).toNat).take t).prod) ∉ letterGerms ω .b := by
  set F : Fin n → BinaryTreeAut := fun i => (p.2 i.rev : BinaryTreeAut) ^ (p.1 i.rev).toNat
    with hFdef
  have hF : ∀ i : Fin n, F i ∈ grigorchuk ω := fun i =>
    Subgroup.pow_mem _ (mem_G_factor D ω hω k hk n hn p i.rev) _
  have hFL : ∀ L : List BinaryTreeAut, L <+: List.ofFn F → ∀ h ∈ L, h ∈ grigorchuk ω :=
    fun L hL h hh => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (hL.subset hh)
      exact hF i
  have hθG : theta D ω k n p ∈ grigorchuk ω :=
    (grigorchuk ω).list_prod_mem (hFL _ List.prefix_rfl)
  have hng : ¬ GoodAt ω (theta D ω k n p) x := fun hg => hbad (mem_of_goodAt ω hθG hx hg)
  by_contra hall
  push Not at hall
  apply hng
  unfold theta
  apply goodAt_list_prod ω
  intro t ht
  have htn : t < n := by simpa using ht
  rw [List.getElem_ofFn]
  have hy : x <• ((List.ofFn F).take t).prod ∈ orbitOne ω :=
    orbit_list_prod D ω hω k hk n hn hx _ (hFL _ (List.take_prefix _ _))
  show GoodAt ω (F ⟨t, htn⟩) _
  simp only [hFdef]
  cases hb : p.1 (Fin.rev ⟨t, htn⟩)
  · simp only [Bool.toNat_false, pow_zero]; exact goodAt_one ω _
  · simp only [Bool.toNat_true, pow_one]
    exact goodAt_of_mem ω (mem_G_factor D ω hω k hk n hn p _) hy (hall ⟨t, htn⟩ hb)

theorem theta_inv (p : LambdaN D ω k n) :
    (theta D ω k n p)⁻¹ =
      (List.ofFn fun i : Fin n => ((p.2 i : BinaryTreeAut) ^ (p.1 i).toNat)⁻¹).prod := by
  unfold theta
  rw [List.prod_inv_reverse]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < n := by simpa using h2
  simp only [List.getElem_reverse, List.getElem_map, List.getElem_ofFn, List.length_map,
    List.length_ofFn]
  have e : (⟨n - 1 - i, by omega⟩ : Fin n).rev = ⟨i, hi⟩ := by
    ext; simp only [Fin.val_rev]; omega
  rw [e]

/-- The union bound for `θ_n⁻¹`: a bad germ of `θ_n⁻¹` comes from a bad germ of some `γ_j⁻¹`
(`ε_j = 1`) at the point `x·γ_1^{-ε_1} ⋯ γ_{j-1}^{-ε_{j-1}}` (Lean: `j - 1 = t`). -/
theorem exists_bad_factor_inv (p : LambdaN D ω k n) {x : Ray} (hx : x ∈ orbitOne ω)
    (hbad : ((theta D ω k n p)⁻¹, x) ∉ letterGerms ω .b) :
    ∃ t : Fin n, p.1 t = true ∧
      (((p.2 t : BinaryTreeAut))⁻¹, x <• ((List.ofFn fun i : Fin n =>
        ((p.2 i : BinaryTreeAut) ^ (p.1 i).toNat)⁻¹).take t).prod) ∉ letterGerms ω .b := by
  set F : Fin n → BinaryTreeAut := fun i => ((p.2 i : BinaryTreeAut) ^ (p.1 i).toNat)⁻¹
    with hFdef
  have hF : ∀ i : Fin n, F i ∈ grigorchuk ω := fun i =>
    (grigorchuk ω).inv_mem (Subgroup.pow_mem _ (mem_G_factor D ω hω k hk n hn p i) _)
  have hFL : ∀ L : List BinaryTreeAut, L <+: List.ofFn F → ∀ h ∈ L, h ∈ grigorchuk ω :=
    fun L hL h hh => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (hL.subset hh)
      exact hF i
  have hθG : (theta D ω k n p)⁻¹ ∈ grigorchuk ω := by
    rw [theta_inv D ω hω k hk n hn]
    exact (grigorchuk ω).list_prod_mem (hFL _ List.prefix_rfl)
  have hng : ¬ GoodAt ω (theta D ω k n p)⁻¹ x := fun hg => hbad (mem_of_goodAt ω hθG hx hg)
  by_contra hall
  push Not at hall
  apply hng
  rw [theta_inv D ω hω k hk n hn]
  apply goodAt_list_prod ω
  intro t ht
  have htn : t < n := by simpa using ht
  rw [List.getElem_ofFn]
  have hy : x <• ((List.ofFn F).take t).prod ∈ orbitOne ω :=
    orbit_list_prod D ω hω k hk n hn hx _ (hFL _ (List.take_prefix _ _))
  show GoodAt ω (F ⟨t, htn⟩) _
  simp only [hFdef]
  cases hb : p.1 ⟨t, htn⟩
  · simp only [Bool.toNat_false, pow_zero, inv_one]; exact goodAt_one ω _
  · simp only [Bool.toNat_true, pow_one]
    exact goodAt_of_mem ω ((grigorchuk ω).inv_mem (mem_G_factor D ω hω k hk n hn p _)) hy
      (hall ⟨t, htn⟩ hb)

end

end P7Dev

end ErschlerZheng
end

section
/-!
# Root swap and level-1 sections of products (helpers for A5, A7)
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ZetaDev

open GrigBasic

end ZetaDev

end ErschlerZheng
end

section
/-!
# A7: the substitutions act on group elements (p. 15), under the tail hypothesis

Route. By (2.3) (A5, imported), `g = ζ_{ω_n}(w)` evaluated in `G_{𝔰^n ω}` is determined by its
root swap `β(w)` and by `W = w` evaluated in `G_{𝔰^{n+1} ω}`: its level-1 sections are
`(aWa, W)` or `(aW, Wa)`. It remains to see that `β(w)` is a function of `W`. For every level
`k`, `σ_k(g) = Σ_{|v| = k} [g_v swaps level 1] mod 2` is a homomorphism `Aut(T) → ℤ/2`, with
`σ_0(a) = 1`, `σ_{k+1}(a) = 0`, `σ_0(γ_ω) = 0`, `σ_{k+1}(γ_ω) = ω_k(γ)`. The parity `β` counts
the pairs `a κ` with `κ` the generator killed by `ω_n`; under the tail hypothesis it is
`σ_0 + Σ_{j ∈ J} σ_{j+1}` of `W` for a set `J` of one level (where `ω_n` recurs) or two levels
(where the two other letters occur).
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false

namespace ErschlerZheng

namespace ZetaHatDev

open GrigBasic ZetaDev

/-! ### Level parities -/

/-! ### The free-group words -/

/-! ### The parity is a function of the element -/

end ZetaHatDev

open GrigBasic ZetaDev ZetaHatDev

end ErschlerZheng
end

section
/-!
# The index sets `W^n_k` and `V^j_k` (Erschler–Zheng p. 37)

`|W^n_k| = 2^{k/D}` for `D ∣ n`, `D ∣ k`; `|V^j_k| = 2^{k/D}` and every `v ∈ V^j_k` ends with `0`.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrW

theorem frM_spec (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (ℓ : ℕ) :
    frM D ω ℓ + 3 ≤ D ∧ ω (ℓ * D + frM D ω ℓ) = 2 ∧ ω (ℓ * D + frM D ω ℓ + 2) = 1 ∧
      (ω (ℓ * D + frM D ω ℓ + 1) = 0 ∨ ω (ℓ * D + frM D ω ℓ + 1) = 1) := by
  have hne : {m | m + 3 ≤ D ∧ ω (ℓ * D + m) = 2 ∧ ω (ℓ * D + m + 2) = 1 ∧
      (ω (ℓ * D + m + 1) = 0 ∨ ω (ℓ * D + m + 1) = 1)}.Nonempty := hω ℓ
  exact Nat.sInf_mem hne

end ConstrW

end ErschlerZheng
end

section
/-!
# Fact 7.6: `ι([γ_{𝔰ⁿω}, a], v)` lies in `G_ω`, with word length at most `2^{n+2}`

The words of the paper's proof (p. 37), built from the bottom: a word `w` read in `G_{𝔰^{ℓ+1}ω}`
is lifted to `G_{𝔰^ℓ ω}` letter by letter, by `a ↦ a y a`, `γ ↦ γ` (to act below `1`) or by
`a ↦ y`, `γ ↦ a γ a` (to act below `0`), where `ω_ℓ(y) = a`. The lift acts as `w` below the chosen
vertex and as `π(w)` below the other one, where `π` sends `a ↦ y_{𝔰^{ℓ+1}ω}`, `γ ↦ ω_ℓ(γ)`.
The invariant that makes `π(w) = 1` is `Kill`: `w` evaluates to `1` under every letter map
`a ↦ z`, `γ ↦ (A if ω_ℓ(γ) = a, else 1)` with `z, A` involutions.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrIota

open GrigBasic ZetaDev

/-! ### `ι` -/

/-! ### Words and letter maps -/

/-- The letter `γ` as a letter of `{a, b, c, d}`. -/
def bcdGen : BCD → Gen4
  | .b => .b
  | .c => .c
  | .d => .d

/-- The letter map `a ↦ fa`, `γ ↦ fγ γ`. -/
def lm (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : Gen4 → BinaryTreeAut
  | .a => fa
  | .b => fγ .b
  | .c => fγ .c
  | .d => fγ .d

@[simp] theorem lm_a (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : lm fa fγ .a = fa := rfl
@[simp] theorem lm_b (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : lm fa fγ .b = fγ .b := rfl
@[simp] theorem lm_c (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : lm fa fγ .c = fγ .c := rfl
@[simp] theorem lm_d (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) : lm fa fγ .d = fγ .d := rfl

@[simp] theorem lm_bcdGen (fa : BinaryTreeAut) (fγ : BCD → BinaryTreeAut) (γ : BCD) :
    lm fa fγ (bcdGen γ) = fγ γ := by
  cases γ <;> rfl

/-! ### The lift -/


/-! ### The invariant `Kill` under lifts -/

/-! ### The words of Fact 7.6 -/

end ConstrIota

end ErschlerZheng
end

section
/-!
# The elements `h^v_i` (7.4) (Erschler–Zheng p. 38)

For `v ∈ V^j_k`: its length, the `201`/`211` window at each digit `0`, `h^v_i` in the rigid
stabilizer of `v_1 … v_{i-2}` (Fact 7.6 for the string `𝔰^j ω`), `[b, a]` below `1`, and
`1^∞ · h^v_1 ⋯ h^v_{k'} = v 1^∞`.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrH

open GrigBasic ZetaDev ConstrW ConstrIota RayBasic SchreierDev

/-! ### The positions of the digits `0` of `v ∈ V^j_k` -/

theorem length_of_mem_vSet (D : ℕ) (ω : ℕ → Fin 3) (j k : ℕ) (v : List Bool)
    (hv : v ∈ vSet D ω j k) :
    v.length = D - j % D + k + frM D ω (ellIndex D k j) + 3 := by
  obtain ⟨u, ⟨hu, -⟩, rfl⟩ := hv
  simp [hu]
  omega

/-! ### `[b, a]` below `1` -/

/-! ### The milestone -/

end ConstrH

end ErschlerZheng
end

section
/-!
# Lemma 7.9 (corrected) and its printed failure (Erschler–Zheng p. 39)

`a𝔠^v_j = a H⁻¹ c H` is the value of the explicit even-length word `a U^R c U` (`U` a word for
`H = h^v_1 ⋯ h^v_{k'}`, from Fact 7.6), hence of a free-group word `w` over `{ab, ac, ad}`
(pair the letters: `x y = (a x)⁻¹ (a y)`). The parity character `χ_κ` (number of `aκ` letters
mod 2) satisfies `χ_κ ∘ ζ_i = χ_{κ_i}` (`κ_i` the letter killed by `i`), and the root swap of
`ζ_i(u)` evaluated is `χ_{κ_i}(u)` (A5). So every stage of `ζ_{ω_0} ∘ ⋯ ∘ ζ_{ω_{j-1}}(w)`
has root swap `χ_{κ_{j-1}}(w)`: `0` when `ω_{j-1} ≠ 1` (even numbers of `b` and `d`), `1` when
`ω_{j-1} = 1` (odd number of `c`). With (2.3) this gives Lemma 7.9 and its failure.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrG

open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH

/-! ### Words for `hProd` and `a𝔠` -/

/-! ### Free-group words from even-length words -/

/-! ### The parity character and the substitutions -/

/-! ### The structure of `g̃` -/

/-! ### The free word for `a𝔠` and the tail condition -/

/-! ### The printed claim fails at `ω = (201)^∞`, `D = 3`, `j = 3`, `k = 3` -/

end ConstrG

end ErschlerZheng
end

section
/-!
# The sequence `g_n` of (7.1) (Erschler–Zheng p. 35)

`g_n = ζ_{ω_0} ∘ ⋯ ∘ ζ_{ω_{n-1}}(aγ)` with `γ = c` if `ω_{n-1} = 2`, else `b`: the letter `aγ`
has `χ_{κ_{n-1}} = 0`, so every substitution stage fixes level 1 (`ConstrG`), `g_n ∈ St(L_n)` with
sections `aγ` or `γa` at level `n`; cube independence is Lemma 5.6 (A13b); the germs are read from
the sections at level `n + 1`, which lie in `{1, a, γ_{𝔰^{n+1}ω}}`, with B4 (for `⟨c⟩`, B4 applied to
the string with the letters `1` and `2` exchanged, whose `b` is `c_ω`).
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrSeq

open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG

/-! ### `g_n` as a substituted free-group word -/

/-! ### Exchanging the letters `1` and `2` -/

/-! ### Generators that differ -/

/-! ### The milestone -/

end ConstrSeq

end ErschlerZheng
end

section
/-!
# Lemma 7.7: the sections of `𝔠^v_j` along the path `v` (Erschler–Zheng p. 38)

For a string `ω` and a word `v`, `kProd ω v = k_1 ⋯ k_{|v|}` with `k_i = 1` if `v_i = 1`,
`k_1 = a` if `v_1 = 0`, and `k_i = ι([b_{𝔰^{i-2}ω}, a], v_1 … v_{i-2})` if `v_i = 0`, `i ⩾ 2`;
`qElt ω v = kProd⁻¹ c_ω kProd`. When `v_1 = 1`, `hProd ω j v = kProd (𝔰^j ω) v` and
`cElt ω j v = qElt (𝔰^j ω) v`. One level down:
`qElt ω (1 :: v') = (s, qElt (𝔰ω) v')` and `qElt ω (0 :: v') = (qElt (𝔰ω) v', ω_0(c))`, where
`s = b a ω_0(c) a b` (`b = b_{𝔰ω}`) if `v'` starts with `0`, and `s = ω_0(c)` otherwise.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrC

open GrigBasic ZetaDev ConstrW ConstrIota ConstrH

/-! ### The milestone -/

end ConstrC

end ErschlerZheng
end

section
/-!
# Fact 7.14: on level `n + D + 1`, every element of `𝔉_{j,n}` acts as `g_j` (p. 44)

`g̃^v_j` and `g_j` are `ζ_{ω_0} ∘ ⋯ ∘ ζ_{ω_{j-1}}` of `a𝔠^v_j` and `ac_{𝔰^jω}`; both fix level `j`, and
at each vertex of level `j` their sections are `(a𝔠, ac)` or `(𝔠a, ca)` (`goodPair_zfold`). If `v`
begins with `1^p`, then `𝔠^v_j = qElt (𝔰^jω) v` and `c = qElt (𝔰^jω) 1^{|v|}` agree on level `p + 1`
(`qElt_agree`, one level at a time with `qElt_cons`); here `p = n - j + D`.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrFact714

open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG ConstrSeq ConstrC

/-! ### `|1^∞ ∧ v|` -/

theorem take_of_le_commonPrefixLength (v : List Bool) (p : ℕ)
    (h : p ≤ commonPrefixLength v oneRay) : p ≤ v.length ∧ v.take p = List.replicate p true := by
  unfold commonPrefixLength at h
  have hro : rayPrefix oneRay v.length = List.replicate v.length true := by
    apply List.ext_getElem <;> simp [rayPrefix, oneRay]
  rw [hro] at h
  set l := (v.zip (List.replicate v.length true)).takeWhile fun p => p.1 = p.2
  have hpre : l <+: v.zip (List.replicate v.length true) := List.takeWhile_prefix _
  have hl : l.length ≤ v.length := by
    have := hpre.length_le; simpa using this
  refine ⟨by omega, ?_⟩
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_replicate]
    have hi : i < l.length := by simp at h2; omega
    have hmem : l[i] ∈ l := List.getElem_mem hi
    have hP := List.mem_takeWhile_imp hmem
    have heq : l[i] = (v.zip (List.replicate v.length true))[i]'(by
        have := hpre.length_le; omega) := hpre.getElem hi
    rw [heq] at hP
    simpa using hP

/-! ### Two substitution stacks side by side -/

/-! ### The milestone -/

end ConstrFact714

end ErschlerZheng
end

section
/-!
# (7.7): the index set of `𝔉_{j,n}`, injectivity of `v ↦ g̃^v_j`, and `|𝔉_{j,n}|` (p. 40)

Injectivity: the section of `g̃^v_j` at `1^j` is `a𝔠^v_j`, and `v ↦ 𝔠^v_j` is injective: where two
words first differ, one element has the path section `qElt` (no root swap, `≠ 1`) and the other a
sibling section (`1`, or one that swaps level 1). The count: the prefix `1^{n-j+D}` fixes the first
`n - j + j̄` digits of `u ∈ W^{j+D-j̄}_{2k_n}`, a multiple of `D`.
-/

open scoped RightActions commutatorElement
open Garrido

namespace ErschlerZheng

namespace ConstrF8

open GrigBasic ZetaDev ZetaHatDev ConstrW ConstrIota ConstrH ConstrG ConstrSeq ConstrC
  ConstrFact714

/-! ### Clause 1 -/

theorem le_length_takeWhile {α : Type*} (P : α → Bool) :
    ∀ (p : ℕ) (l : List α) (hl : p ≤ l.length), (∀ i (h : i < p), P (l[i]'(by omega)) = true) →
      p ≤ (l.takeWhile P).length := by
  intro p
  induction p with
  | zero => intros; exact Nat.zero_le _
  | succ p ih =>
    intro l hl h
    cases l with
    | nil => simp at hl
    | cons a l =>
      have h0 : P a = true := h 0 (by omega)
      rw [List.takeWhile_cons, if_pos h0]
      simp only [List.length_cons, Nat.add_le_add_iff_right]
      exact ih l (by simpa using hl) (fun i hi => h (i + 1) (by omega))

theorem le_commonPrefixLength_iff (v : List Bool) (p : ℕ) :
    p ≤ commonPrefixLength v oneRay ↔ List.replicate p true <+: v := by
  constructor
  · intro h
    obtain ⟨hl, ht⟩ := take_of_le_commonPrefixLength v p h
    rw [List.prefix_iff_eq_take, List.length_replicate, ht]
  · intro h
    have hl : p ≤ v.length := by simpa using h.length_le
    have ht : v.take p = List.replicate p true := by
      rw [List.prefix_iff_eq_take, List.length_replicate] at h; exact h.symm
    unfold commonPrefixLength
    apply le_length_takeWhile _ p _ (by simp [length_rayPrefix]; omega)
    intro i hi
    simp only [List.getElem_zip, decide_eq_true_eq]
    have h1 : v[i]'(by omega) = true := by
      have := congrArg (fun l : List Bool => l[i]?) ht
      simp only [List.getElem?_take, show i < p from hi, if_true,
        List.getElem?_replicate, if_true] at this
      rw [List.getElem?_eq_getElem (by omega)] at this
      simpa using this
    rw [h1, getElem_rayPrefix]
    rfl

/-! ### Injectivity of `v ↦ 𝔠^v_j` -/

/-! ### The section of `g̃^v_j` at `1^j` -/

/-! ### The count -/

end ConstrF8

end ErschlerZheng
end

section
/-!
# Lemma 7.15: on level `n + D + 1`, `x·θ_n(ε, γ)` determines `ε` (Erschler–Zheng p. 44)

By Fact 7.14 every `γ_i ∈ 𝔉_{i,n}` acts on level `n + D + 1` as `g_i`, so `x·θ_n(ε, γ) =
x·g_n^{ε_n} ⋯ g_1^{ε_1}` there. Each `g_k` fixes the first `k` digits and flips digit `k + 1`
(it fixes level `k` and its sections there swap level 1, (7.1)); so digit `2` of the result is
`x_2 + ε_1`, and peeling off `g_1^{ε_1}` the argument repeats.
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrLemma715

open GrigBasic

end ConstrLemma715

end ErschlerZheng
end

section
/-!
# The kernels of `υ_n` on `L_n` and the isoperimetric bound (Erschler–Zheng p. 48)
-/

open scoped RightActions
open Garrido

namespace ErschlerZheng

namespace ConstrG9

open GrigBasic ConstrW ConstrH ConstrF8 ConstrLemma715

/-! ### `𝔉_{j,n}` and `Λ_n` are finite and non-empty -/

theorem vSet_finite (D : ℕ) (ω : ℕ → Fin 3) (j k : ℕ) : (vSet D ω j k).Finite :=
  (List.finite_length_eq Bool (D - j % D + k + frM D ω (ellIndex D k j) + 3)).subset
    fun v hv => length_of_mem_vSet D ω j k v hv

theorem fSet_finite (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (j n : ℕ) : (fSet D ω k j n).Finite := by
  unfold fSet
  split_ifs
  · apply ((vSet_finite D ω j (2 * k n)).image (gTilde ω j)).subset
    rintro g ⟨v, hv, -, rfl⟩
    exact ⟨v, hv, rfl⟩
  · exact Set.finite_singleton _

theorem fSet_nonempty (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j) :
    (fSet D ω k j n).Nonempty := by
  have hD : 3 ≤ D := (frM_spec D ω hω 0).1.trans' (by omega)
  unfold fSet
  split_ifs with hc
  · obtain ⟨-, hjn, hjn'⟩ := hc
    have hkn := hk.2 n (by omega) hn
    have hkD : D ≤ k n := Nat.le_of_dvd hkn.1 hkn.2
    set m := frM D ω (ellIndex D (2 * k n) j)
    set v0 := List.replicate (D - j % D) true ++ List.replicate (2 * k n) true ++
      List.replicate (m + 2) true ++ [false]
    have hv0 : v0 ∈ vSet D ω j (2 * k n) :=
      ⟨List.replicate (2 * k n) true, ⟨by simp, fun i hi _ => by simp⟩, rfl⟩
    have hjD : j % D < D := Nat.mod_lt _ (by omega)
    have hpre : List.replicate (n - j + D) true <+: v0 := by
      have e : v0 = List.replicate (n - j + D) true ++
          (List.replicate (D - j % D + 2 * k n + (m + 2) - (n - j + D)) true ++ [false]) := by
        simp only [v0, ← List.append_assoc, ← List.replicate_add]
        congr 2
        omega
      rw [e]; exact List.prefix_append _ _
    exact ⟨_, v0, hv0, (le_commonPrefixLength_iff v0 _).2 hpre, rfl⟩
  · exact Set.singleton_nonempty _

theorem fSet_subset (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j) :
    fSet D ω k j n ⊆ grigorchuk ω := by
  intro γ hγ
  unfold fSet at hγ
  split_ifs at hγ with hc
  · obtain ⟨v, hv, -, rfl⟩ := hγ
    have hkn := hk.2 n (by omega) hn
    exact (exists_evalFree_eq_and_gTilde_mem_levelStab_and_sec_mem D ω hω j hj1 (2 * k n)
      (Dvd.dvd.mul_left hkn.2 2) v hv).2.1
  · rw [Set.mem_singleton_iff.mp hγ]
    exact ((seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω).1 j hj1).1.1

theorem finite_fProd (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) : Finite (fProd D ω k n) := by
  have : ∀ i : Fin n, Finite ↥(fSet D ω k (i + 1) n) := fun i => (fSet_finite D ω k _ n).to_subtype
  exact Pi.finite

theorem nonempty_fProd (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) : Nonempty (fProd D ω k n) :=
  ⟨fun i => ⟨_, (fSet_nonempty D ω hω k hk n hn (i + 1) (by omega)).some_mem⟩⟩

theorem theta_mem (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (p : LambdaN D ω k n) :
    theta D ω k n p ∈ grigorchuk ω := by
  unfold theta
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
  exact Subgroup.pow_mem _ (fSet_subset D ω hω k hk n hn _ (by omega) (p.2 i.rev).2) _

/-! ### Injectivity in `ε` on rays (Lemma 7.15) -/


/-! ### Clause 2 -/

open Classical in
theorem upsilon_eq_sum (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) [Fintype (LambdaN D ω k n)]
    (g : BinaryTreeAut) :
    upsilon D ω k n g = ∑ p : LambdaN D ω k n,
      if theta D ω k n p = g then (1 / (Nat.card (LambdaN D ω k n) : ℝ)) else 0 := by
  unfold upsilon
  rw [Nat.card_eq_fintype_card (α := {p // theta D ω k n p = g}), Fintype.card_subtype,
    Finset.card_filter]
  push_cast
  rw [Finset.sum_div]
  congr 1; funext p; split_ifs <;> simp


/-! ### Clause 1 -/

end ConstrG9

end ErschlerZheng
end

section
/-!
# Proposition 7.12, steps 1–2 of §7.6 (p. 53) for `υ_n` — prover 7

`Σ_x F(x) υ_n{g : (g, x) ∉ ℋ^b} ⩽ Σ_t |Λ_n|⁻¹ Σ_p [ε_j = 1] Σ_{y : (γ_j, y) ∉ ℋ^b} F(y·P_t(p)⁻¹)`, in
`[0, ∞]`, where `j - 1 = t.rev` and `P_t(p) = γ_n^{ε_n} ⋯ γ_{j+1}^{ε_{j+1}}`: the mass as a count over
`Λ_n`, the union bound (`P7P712.exists_bad_factor`), and the change of variables `x ↦ x·P_t(p)` of the
orbit (`sum_mass_upsilon_le`). Likewise for `υ̌_n` (`sum_mass_upsilonCheck_le`, factors `γ_j⁻¹`,
`j - 1 = t`, `Q_t(p) = γ_1^{-ε_1} ⋯ γ_{j-1}^{-ε_{j-1}}`). `prodTake_inv_eq` and `prodTakeInv_inv_eq`
rewrite `P_t(p)⁻¹`, `Q_t(p)⁻¹` in the exact list forms of G8 (clauses 1, 3) and I1 (clauses 1, 2).
-/

open scoped RightActions ENNReal
open Garrido

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ErschlerZheng

namespace P7Dev

open GrigBasic P3P712Dev P3U0Dev

/-- `P_t(p)`: the first `t` factors of `θ_n(p)`. -/
def prodTake (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (p : LambdaN D ω k n) (t : ℕ) :
    BinaryTreeAut :=
  ((List.ofFn fun i : Fin n => (p.2 i.rev : BinaryTreeAut) ^ (p.1 i.rev).toNat).take t).prod

/-- `Q_t(p)`: the first `t` factors of `θ_n(p)⁻¹ = γ_1^{-ε_1} ⋯ γ_n^{-ε_n}`. -/
def prodTakeInv (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (p : LambdaN D ω k n) (t : ℕ) :
    BinaryTreeAut :=
  ((List.ofFn fun i : Fin n => ((p.2 i : BinaryTreeAut) ^ (p.1 i).toNat)⁻¹).take t).prod

/-! ### The products in the forms of G8 and I1 -/

theorem take_ofFn_eq {α : Type*} {n : ℕ} (F : Fin n → α) (t : ℕ) (ht : t ≤ n) :
    (List.ofFn F).take t = (List.finRange t).map fun m : Fin t => F ⟨m.val, by have := m.2; omega⟩ := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp [List.getElem_take, List.getElem_ofFn, List.getElem_map, List.getElem_finRange]

theorem filter_range' (j n : ℕ) (h : j ≤ n) :
    (List.range n).filter (fun i => decide (j ≤ i)) = (List.range (n - j)).map (j + ·) := by
  conv_lhs => rw [show n = j + (n - j) by omega, List.range_add]
  rw [List.filter_append, List.filter_eq_nil_iff.mpr, List.filter_eq_self.mpr]
  · rfl
  · intro a ha; simp at ha; obtain ⟨b, -, rfl⟩ := ha; simp
  · intro a ha; simp at ha; simp; omega

theorem filter_finRange_ge (n s : ℕ) (hs : s ≤ n) :
    (List.finRange n).filter (fun i : Fin n => s ≤ i.val) =
      (List.finRange (n - s)).map fun m : Fin (n - s) => (⟨s + m.val, by have := m.2; omega⟩ : Fin n) := by
  apply List.ext_getElem
  · have h := congrArg List.length (congrArg (List.map Fin.val)
      (show (List.finRange n).filter (fun i : Fin n => s ≤ i.val) =
        (List.finRange n).filter (fun i : Fin n => s ≤ i.val) from rfl))
    rw [List.length_map] at h
    have h2 : (List.map Fin.val (List.filter (fun i : Fin n => decide (s ≤ i.val))
        (List.finRange n))) = (List.range n).filter (fun i => decide (s ≤ i)) := by
      rw [← List.map_coe_finRange_eq_range, List.filter_map]; rfl
    rw [← List.length_map (f := Fin.val), h2, filter_range' s n hs]
    simp
  · intro i h1 h2
    have h3 : (List.map Fin.val (List.filter (fun i : Fin n => decide (s ≤ i.val))
        (List.finRange n))) = (List.range n).filter (fun i => decide (s ≤ i)) := by
      rw [← List.map_coe_finRange_eq_range, List.filter_map]; rfl
    rw [filter_range' s n hs] at h3
    have h4 := congrArg (fun l => l[i]?) h3
    simp only [List.getElem?_map] at h4
    apply Fin.ext
    simp only [List.getElem_map, List.getElem_finRange]
    have h5 : (List.filter (fun i : Fin n => decide (s ≤ i.val)) (List.finRange n))[i]? =
        some (List.filter (fun i : Fin n => decide (s ≤ i.val)) (List.finRange n))[i] :=
      List.getElem?_eq_getElem h1
    rw [h5] at h4
    have hi : i < n - s := by simpa using h2
    simp [hi] at h4
    simp [h4]


/-! ### The Gray-code lower bound: a digit `0` at (0-based) position `i` means `d(o, x) ⩾ 2^i` -/

theorem two_pow_le_grayList : ∀ (w : List Bool) (i : ℕ) (hi : i < w.length), w[i] = false →
    2 ^ i ≤ grayList w
  | [], i, hi, _ => absurd hi (by simp)
  | b :: v, 0, _, h => by
    simp only [List.getElem_cons_zero] at h
    subst h
    rw [grayList]
    by_cases hv : false ∈ v
    · obtain ⟨i', hi', e⟩ := List.mem_iff_getElem.mp hv
      have := two_pow_le_grayList v i' hi' e
      have : 1 ≤ 2 ^ i' := Nat.one_le_two_pow
      omega
    · have hc : (false :: v).count false = 1 := by
        rw [List.count_cons_self, List.count_eq_zero.mpr hv]
      rw [hc]; simp
  | b :: v, i' + 1, hi, h => by
    simp only [List.getElem_cons_succ] at h
    have := two_pow_le_grayList v i' (by simpa using hi) h
    rw [grayList, pow_succ]
    omega

theorem two_pow_le_schreierDist (ω : ℕ → Fin 3) {x : Ray} (hx : IsCofinal x) {i : ℕ}
    (hi : x i = false) : 2 ^ i ≤ schreierDist ω oneRay x := by
  have hd := schreierDist_eq_abs_sub_grayCode_of_isCofinal ω oneRay x (Filter.Eventually.of_forall fun _ => rfl) hx
  rw [SchreierDev.grayCode_oneRay] at hd
  simp only [Nat.cast_zero, zero_sub, abs_neg, Nat.abs_cast] at hd
  have hd' : schreierDist ω oneRay x = grayCode x := by exact_mod_cast hd
  obtain ⟨N, hN⟩ := (SchreierDev.isCofinal_iff x).mp hx
  have hN' := hN.mono (le_max_left N (i + 1))
  rw [hd', SchreierDev.grayCode_eq hN']
  refine two_pow_le_grayList _ i (by rw [length_rayPrefix]; omega) ?_
  rw [getElem_rayPrefix]
  exact hi


/-! ### Bad points of an inverse: `{x : (g⁻¹, x) ∉ ℋ^b} = {y : (g, y) ∉ ℋ^b}·g` -/

theorem goodAt_inv_iff (ω : ℕ → Fin 3) (g : BinaryTreeAut) (x : Ray) :
    GoodAt ω g⁻¹ x ↔ GoodAt ω g (x <• g⁻¹) := by
  constructor
  · intro h
    have := goodAt_inv ω h
    rwa [inv_inv] at this
  · intro h
    have := goodAt_inv ω h
    rwa [op_smul_op_smul, inv_mul_cancel, MulOpposite.op_one, one_smul] at this

theorem bad_inv_eq_image (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) :
    {x | x ∈ orbitOne ω ∧ (g⁻¹, x) ∉ letterGerms ω .b} =
      (fun y => y <• g) '' {y | y ∈ orbitOne ω ∧ (g, y) ∉ letterGerms ω .b} := by
  ext x
  constructor
  · rintro ⟨hx, hbad⟩
    have hx' : x <• g⁻¹ ∈ orbitOne ω := B8MarkovDev.orbit_smul' hx ((grigorchuk ω).inv_mem hg)
    refine ⟨x <• g⁻¹, ⟨hx', fun hmem => hbad ?_⟩, ?_⟩
    · exact mem_of_goodAt ω ((grigorchuk ω).inv_mem hg) hx
        ((goodAt_inv_iff ω g x).mpr (goodAt_of_mem ω hg hx' hmem))
    · show (x <• g⁻¹) <• g = x
      rw [op_smul_op_smul, inv_mul_cancel, MulOpposite.op_one, one_smul]
  · rintro ⟨y, ⟨hy, hbad⟩, rfl⟩
    have hyg : y <• g ∈ orbitOne ω := B8MarkovDev.orbit_smul' hy hg
    refine ⟨hyg, fun hmem => hbad ?_⟩
    have h1 := (goodAt_inv_iff ω g (y <• g)).mp
      (goodAt_of_mem ω ((grigorchuk ω).inv_mem hg) hyg hmem)
    rw [op_smul_op_smul, mul_inv_cancel, MulOpposite.op_one, one_smul] at h1
    exact mem_of_goodAt ω hg hy h1

theorem ncard_bad_inv (ω : ℕ → Fin 3) {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) :
    {x | x ∈ orbitOne ω ∧ (g⁻¹, x) ∉ letterGerms ω .b}.ncard =
      {y | y ∈ orbitOne ω ∧ (g, y) ∉ letterGerms ω .b}.ncard := by
  rw [bad_inv_eq_image ω hg]
  refine Set.ncard_image_of_injective _ fun a b h => ?_
  have := congrArg (fun z => z <• g⁻¹) h
  simpa only [op_smul_op_smul, mul_inv_cancel, MulOpposite.op_one, one_smul] using this

section

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k)
  (n : ℕ) (hn : D ∣ n)

include hω hk hn

theorem prodTake_mem (p : LambdaN D ω k n) (t : ℕ) : prodTake D ω k n p t ∈ grigorchuk ω := by
  unfold prodTake
  refine (grigorchuk ω).list_prod_mem fun h hh => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hh)
  exact Subgroup.pow_mem _ (mem_G_factor D ω hω k hk n hn p i.rev) _

theorem prodTakeInv_mem (p : LambdaN D ω k n) (t : ℕ) :
    prodTakeInv D ω k n p t ∈ grigorchuk ω := by
  unfold prodTakeInv
  refine (grigorchuk ω).list_prod_mem fun h hh => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hh)
  exact (grigorchuk ω).inv_mem (Subgroup.pow_mem _ (mem_G_factor D ω hω k hk n hn p i) _)

/-- `x ↦ x·g` as a permutation of the orbit, for `g ∈ G_ω`. -/
def orbitPerm {g : BinaryTreeAut} (hg : g ∈ grigorchuk ω) : orbitOne ω ≃ orbitOne ω where
  toFun x := ⟨(x : Ray) <• g, B8MarkovDev.orbit_smul' x.2 hg⟩
  invFun y := ⟨(y : Ray) <• g⁻¹, B8MarkovDev.orbit_smul' y.2 ((grigorchuk ω).inv_mem hg)⟩
  left_inv x := by
    apply Subtype.ext
    show ((x : Ray) <• g) <• g⁻¹ = x
    rw [op_smul_op_smul, mul_inv_cancel, MulOpposite.op_one, one_smul]
  right_inv y := by
    apply Subtype.ext
    show ((y : Ray) <• g⁻¹) <• g = y
    rw [op_smul_op_smul, inv_mul_cancel, MulOpposite.op_one, one_smul]


/-- `P_t(p)⁻¹` in the form of G8 clause 1 and I1 clause 1, with `j = n - t`. -/
theorem prodTake_inv_eq (p : LambdaN D ω k n) (t : ℕ) (ht : t ≤ n) :
    (prodTake D ω k n p t)⁻¹ = (((List.finRange n).filter fun i : Fin n => n - t ≤ i.val).map
      fun i => ((p.2 i : BinaryTreeAut) ^ (p.1 i).toNat)⁻¹).prod := by
  set G : Fin n → BinaryTreeAut := fun i => (p.2 i : BinaryTreeAut) ^ (p.1 i).toNat with hG
  show ((List.ofFn fun i : Fin n => G i.rev).take t).prod⁻¹ =
    (((List.finRange n).filter fun i : Fin n => n - t ≤ i.val).map fun i => (G i)⁻¹).prod
  rw [List.prod_inv_reverse, take_ofFn_eq _ t ht, filter_finRange_ge n (n - t) (by omega)]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  have hi : i < t := by simpa using h1
  simp only [List.getElem_reverse, List.getElem_map, List.getElem_finRange, List.length_map,
    List.length_finRange]
  congr 2
  ext
  simp [Fin.val_rev]
  omega

/-- `Q_t(p)⁻¹` in the form of I1 clause 2 and G8 clause 3, with `j = t + 1`. -/
theorem prodTakeInv_inv_eq (p : LambdaN D ω k n) (t : ℕ) (ht : t ≤ n) :
    (prodTakeInv D ω k n p t)⁻¹ = ((((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ t + 1).map
      fun i => (p.2 i : BinaryTreeAut) ^ (p.1 i).toNat).reverse).prod := by
  unfold prodTakeInv
  rw [List.prod_inv_reverse, take_ofFn_eq _ t ht, List.map_map]
  congr 2
  have hf : (List.finRange n).filter (fun i : Fin n => i.val + 2 ≤ t + 1) =
      (List.finRange t).map fun m : Fin t => (⟨m.val, by have := m.2; omega⟩ : Fin n) := by
    apply List.ext_getElem
    · have h2 : (List.map Fin.val (List.filter (fun i : Fin n => decide (i.val + 2 ≤ t + 1))
          (List.finRange n))) = (List.range n).filter (fun i => decide (i + 2 ≤ t + 1)) := by
        rw [← List.map_coe_finRange_eq_range, List.filter_map]; rfl
      have h3 : (List.range n).filter (fun i => decide (i + 2 ≤ t + 1)) = List.range t := by
        conv_lhs => rw [show n = t + (n - t) by omega, List.range_add]
        rw [List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr]
        · simp
        · intro a ha; simp at ha; obtain ⟨b, -, rfl⟩ := ha; simp
        · intro a ha; simp at ha; simp; omega
      rw [← List.length_map (f := Fin.val), h2, h3]
      simp
    · intro i h1 h2
      have h2' : (List.map Fin.val (List.filter (fun i : Fin n => decide (i.val + 2 ≤ t + 1))
          (List.finRange n))) = (List.range n).filter (fun i => decide (i + 2 ≤ t + 1)) := by
        rw [← List.map_coe_finRange_eq_range, List.filter_map]; rfl
      have h3 : (List.range n).filter (fun i => decide (i + 2 ≤ t + 1)) = List.range t := by
        conv_lhs => rw [show n = t + (n - t) by omega, List.range_add]
        rw [List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr]
        · simp
        · intro a ha; simp at ha; obtain ⟨b, -, rfl⟩ := ha; simp
        · intro a ha; simp at ha; simp; omega
      rw [h3] at h2'
      have h4 := congrArg (fun l => l[i]?) h2'
      simp only [List.getElem?_map] at h4
      rw [List.getElem?_eq_getElem h1] at h4
      have hi : i < t := by simpa using h2
      simp [hi] at h4
      apply Fin.ext
      simp [h4]
  rw [hf, List.map_map]
  simp only [Function.comp_def, inv_inv]

open Classical in
/-- The mass of a measure `ν = Σ_p δ_{φ(p)}/|Λ_n|` (with `φ(p) ∈ G_ω`) on the germs bad at `x`, as a
count over `Λ_n`. -/
theorem ofReal_mass_eq_of [Fintype (LambdaN D ω k n)] (φ : LambdaN D ω k n → BinaryTreeAut)
    (hφ : ∀ p, φ p ∈ grigorchuk ω) (ν : BinaryTreeAut → ℝ)
    (hν : ∀ h, ν h = ∑ p : LambdaN D ω k n,
      if φ p = h then (1 / (Nat.card (LambdaN D ω k n) : ℝ)) else 0) (x : Ray) :
    ENNReal.ofReal (mass (fun g : grigorchuk ω => ν g)
        {g | ((g : BinaryTreeAut), x) ∉ letterGerms ω .b}) =
      ∑ p : LambdaN D ω k n, if (φ p, x) ∉ letterGerms ω .b then
        ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ)) else 0 := by
  set c : ℝ := 1 / (Nat.card (LambdaN D ω k n) : ℝ)
  have hc : 0 ≤ c := by positivity
  set S := {g : grigorchuk ω | ((g : BinaryTreeAut), x) ∉ letterGerms ω .b}
  have hu : ∀ g : grigorchuk ω, ν g = ∑ p : LambdaN D ω k n, if φ p = g then c else 0 :=
    fun g => hν g
  have hsum : Summable fun g : grigorchuk ω => ν g := by
    simp_rw [hu]
    refine summable_sum fun p _ => ?_
    refine summable_of_ne_finset_zero (s := {⟨_, hφ p⟩}) fun g hg => ?_
    simp only [Finset.mem_singleton] at hg
    rw [if_neg]; intro h; exact hg (Subtype.ext h.symm)
  unfold mass
  have hnn : ∀ g : grigorchuk ω, (0 : ℝ) ≤ ν g := fun g => by
    rw [hu]; exact Finset.sum_nonneg fun p _ => by split_ifs <;> simp [hc]
  rw [ENNReal.ofReal_tsum_of_nonneg (f := S.indicator fun g : grigorchuk ω => ν g)
    (fun g => Set.indicator_nonneg (fun g _ => hnn g) g) (hsum.indicator S)]
  have hpt : ∀ g : grigorchuk ω, ENNReal.ofReal (S.indicator
      (fun g : grigorchuk ω => ν g) g) =
      ∑ p : LambdaN D ω k n, if (g : BinaryTreeAut) = φ p ∧ g ∈ S then
        ENNReal.ofReal c else 0 := by
    intro g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg, hu, ENNReal.ofReal_sum_of_nonneg (fun p _ => by
        split_ifs <;> simp [hc])]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases h : φ p = g
      · simp [h, hg]
      · rw [if_neg h, if_neg (fun h' => h h'.1.symm), ENNReal.ofReal_zero]
    · rw [Set.indicator_of_notMem hg, ENNReal.ofReal_zero]
      exact (Finset.sum_eq_zero fun p _ => by rw [if_neg (fun h => hg h.2)]).symm
  simp_rw [hpt]
  rw [Summable.tsum_finsetSum (fun p _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [tsum_eq_single (⟨φ p, hφ p⟩ : grigorchuk ω)]
  · by_cases h : (φ p, x) ∉ letterGerms ω .b
    · rw [if_pos ⟨rfl, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]
  · intro g hg
    rw [if_neg]
    rintro ⟨h1, -⟩
    exact hg (Subtype.ext h1)

open Classical in
theorem ofReal_mass_upsilon_eq [Fintype (LambdaN D ω k n)] (x : Ray) :
    ENNReal.ofReal (mass (fun g : grigorchuk ω => upsilon D ω k n g)
        {g | ((g : BinaryTreeAut), x) ∉ letterGerms ω .b}) =
      ∑ p : LambdaN D ω k n, if (theta D ω k n p, x) ∉ letterGerms ω .b then
        ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ)) else 0 := by
  classical
  convert ofReal_mass_eq_of D ω hω k hk n hn (theta D ω k n)
    (ConstrG9.theta_mem D ω hω k hk n hn) (upsilon D ω k n)
    (fun h => ConstrG9.upsilon_eq_sum D ω k n h) x

open Classical in
theorem ofReal_mass_upsilonCheck_eq [Fintype (LambdaN D ω k n)] (x : Ray) :
    ENNReal.ofReal (mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
        {g | ((g : BinaryTreeAut), x) ∉ letterGerms ω .b}) =
      ∑ p : LambdaN D ω k n, if ((theta D ω k n p)⁻¹, x) ∉ letterGerms ω .b then
        ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ)) else 0 := by
  classical
  convert ofReal_mass_eq_of D ω hω k hk n hn (fun p => (theta D ω k n p)⁻¹)
    (fun p => (grigorchuk ω).inv_mem (ConstrG9.theta_mem D ω hω k hk n hn p))
    (upsilonCheck D ω k n) (fun h => by
      unfold upsilonCheck
      rw [ConstrG9.upsilon_eq_sum D ω k n h⁻¹]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [inv_eq_iff_eq_inv]) x

open Classical in
/-- Steps 1–2 of p. 53 for `υ_n`: the orbit sum is at most the sum over the factors `t` and
`p ∈ Λ_n` (with `ε_j = 1`) of the sum over the bad points `y` of `γ_j` of `F(y·P_t(p)⁻¹)`. -/
theorem sum_mass_upsilon_le [Fintype (LambdaN D ω k n)] (F : Ray → ℝ) (hF : ∀ r, 0 ≤ F r) :
    ∑' x : orbitOne ω, ENNReal.ofReal (F x * mass (fun g : grigorchuk ω => upsilon D ω k n g)
        {g | ((g : BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) ≤
      ∑ t : Fin n, ∑ p : LambdaN D ω k n, if p.1 t.rev = true then
        ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ)) *
          ∑' y : orbitOne ω, (if ((p.2 t.rev : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b then
            ENNReal.ofReal (F ((y : Ray) <• (prodTake D ω k n p t)⁻¹)) else 0) else 0 := by
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ))
  set B : Fin n → LambdaN D ω k n → orbitOne ω → ℝ≥0∞ := fun t p x =>
    if p.1 t.rev = true ∧ ((p.2 t.rev : BinaryTreeAut), (x : Ray) <• prodTake D ω k n p t) ∉
      letterGerms ω .b then c * ENNReal.ofReal (F x) else 0 with hB
  have hstep1 : ∀ x : orbitOne ω, ENNReal.ofReal (F x * mass (fun g : grigorchuk ω =>
      upsilon D ω k n g) {g | ((g : BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) ≤
      ∑ t : Fin n, ∑ p : LambdaN D ω k n, B t p x := by
    intro x
    rw [ENNReal.ofReal_mul (hF x), ofReal_mass_upsilon_eq D ω hω k hk n hn, Finset.mul_sum,
      Finset.sum_comm]
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases hbad : (theta D ω k n p, (x : Ray)) ∉ letterGerms ω .b
    · rw [if_pos hbad]
      obtain ⟨t, ht1, ht2⟩ := exists_bad_factor D ω hω k hk n hn p x.2 hbad
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun t => B t p x)
        (fun _ _ => zero_le) (Finset.mem_univ t))
      simp only [hB]
      rw [if_pos ⟨ht1, ht2⟩, mul_comm]
    · rw [if_neg hbad, mul_zero]; exact zero_le
  calc _ ≤ ∑' x : orbitOne ω, ∑ t : Fin n, ∑ p : LambdaN D ω k n, B t p x :=
        ENNReal.tsum_le_tsum hstep1
    _ = ∑ t : Fin n, ∑ p : LambdaN D ω k n, ∑' x : orbitOne ω, B t p x := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = _ := by
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun p _ => ?_
        by_cases h1 : p.1 t.rev = true
        · rw [if_pos h1, ← ENNReal.tsum_mul_left]
          have hP := prodTake_mem D ω hω k hk n hn p t
          conv_rhs => rw [← (orbitPerm ω hP).tsum_eq]
          refine tsum_congr fun x => ?_
          simp only [hB, orbitPerm, Equiv.coe_fn_mk, h1, true_and]
          have e : ((x : Ray) <• prodTake D ω k n p t) <• (prodTake D ω k n p t)⁻¹ = x := by
            rw [op_smul_op_smul, mul_inv_cancel, MulOpposite.op_one, one_smul]
          rw [e]
          by_cases h2 : ((p.2 t.rev : BinaryTreeAut), (x : Ray) <• prodTake D ω k n p t) ∉
              letterGerms ω .b
          · simp only [h2, not_false_eq_true, if_true]
          · simp only [h2, if_false, mul_zero]
        · rw [if_neg h1]
          refine ENNReal.tsum_eq_zero.mpr fun x => ?_
          simp only [hB]
          rw [if_neg (fun h => h1 h.1)]

open Classical in
/-- Steps 1–2 of p. 53 for `υ̌_n`: as `sum_mass_upsilon_le`, with the factors `γ_j⁻¹` (`j - 1 = t`)
and `Q_t(p) = γ_1^{-ε_1} ⋯ γ_{j-1}^{-ε_{j-1}}`. -/
theorem sum_mass_upsilonCheck_le [Fintype (LambdaN D ω k n)] (F : Ray → ℝ) (hF : ∀ r, 0 ≤ F r) :
    ∑' x : orbitOne ω, ENNReal.ofReal (F x * mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
        {g | ((g : BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) ≤
      ∑ t : Fin n, ∑ p : LambdaN D ω k n, if p.1 t = true then
        ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ)) *
          ∑' y : orbitOne ω, (if (((p.2 t : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b then
            ENNReal.ofReal (F ((y : Ray) <• (prodTakeInv D ω k n p t)⁻¹)) else 0) else 0 := by
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ))
  set B : Fin n → LambdaN D ω k n → orbitOne ω → ℝ≥0∞ := fun t p x =>
    if p.1 t = true ∧ (((p.2 t : BinaryTreeAut))⁻¹, (x : Ray) <• prodTakeInv D ω k n p t) ∉
      letterGerms ω .b then c * ENNReal.ofReal (F x) else 0 with hB
  have hstep1 : ∀ x : orbitOne ω, ENNReal.ofReal (F x * mass (fun g : grigorchuk ω =>
      upsilonCheck D ω k n g) {g | ((g : BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) ≤
      ∑ t : Fin n, ∑ p : LambdaN D ω k n, B t p x := by
    intro x
    rw [ENNReal.ofReal_mul (hF x), ofReal_mass_upsilonCheck_eq D ω hω k hk n hn, Finset.mul_sum,
      Finset.sum_comm]
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases hbad : ((theta D ω k n p)⁻¹, (x : Ray)) ∉ letterGerms ω .b
    · rw [if_pos hbad]
      obtain ⟨t, ht1, ht2⟩ := exists_bad_factor_inv D ω hω k hk n hn p x.2 hbad
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun t => B t p x)
        (fun _ _ => zero_le) (Finset.mem_univ t))
      simp only [hB]
      rw [if_pos ⟨ht1, ht2⟩, mul_comm]
    · rw [if_neg hbad, mul_zero]; exact zero_le
  calc _ ≤ ∑' x : orbitOne ω, ∑ t : Fin n, ∑ p : LambdaN D ω k n, B t p x :=
        ENNReal.tsum_le_tsum hstep1
    _ = ∑ t : Fin n, ∑ p : LambdaN D ω k n, ∑' x : orbitOne ω, B t p x := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = _ := by
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun p _ => ?_
        by_cases h1 : p.1 t = true
        · rw [if_pos h1, ← ENNReal.tsum_mul_left]
          have hP := prodTakeInv_mem D ω hω k hk n hn p t
          conv_rhs => rw [← (orbitPerm ω hP).tsum_eq]
          refine tsum_congr fun x => ?_
          simp only [hB, orbitPerm, Equiv.coe_fn_mk, h1, true_and]
          have e : ((x : Ray) <• prodTakeInv D ω k n p t) <• (prodTakeInv D ω k n p t)⁻¹ = x := by
            rw [op_smul_op_smul, mul_inv_cancel, MulOpposite.op_one, one_smul]
          rw [e]
          by_cases h2 : (((p.2 t : BinaryTreeAut))⁻¹, (x : Ray) <• prodTakeInv D ω k n p t) ∉
              letterGerms ω .b
          · simp only [h2, not_false_eq_true, if_true]
          · simp only [h2, if_false, mul_zero]
        · rw [if_neg h1]
          refine ENNReal.tsum_eq_zero.mpr fun x => ?_
          simp only [hB]
          rw [if_neg (fun h => h1 h.1)]

end

end P7Dev

end ErschlerZheng
end

section
/-!
# Words by the position of their last `0` (prover 7, toward Proposition 7.12)

`lastZero w` is the (0-based) index of the last `false` in `w` (`none` if there is none).
Among the `2^n` words of length `n`, exactly `2^m` have their last `0` at `m < n`, so
`Σ_{|w| = n} g(lastZero w) = Σ_{m < n} 2^m g(m)` (with `g(none) = 0`), and exactly one word (`1^n`)
has no `0`. No stubs.
-/

namespace ErschlerZheng

namespace P7Dev

/-- The index of the last `false` in a word. -/
def lastZero : List Bool → Option ℕ
  | [] => none
  | b :: v => match lastZero v with
    | some m => some (m + 1)
    | none => if b = false then some 0 else none

theorem lastZero_cons (b : Bool) (v : List Bool) : lastZero (b :: v) =
    (match lastZero v with
      | some m => some (m + 1)
      | none => if b = false then some 0 else none) := rfl

theorem lastZero_spec : ∀ (w : List Bool) (m : ℕ), lastZero w = some m →
    ∃ h : m < w.length, w[m] = false
  | [], m, h => by simp [lastZero] at h
  | b :: v, m, h => by
    unfold lastZero at h
    rcases hv : lastZero v with _ | m'
    · rw [hv] at h
      simp only at h
      split_ifs at h with hb
      · cases h
        exact ⟨by simp, by simpa using hb⟩
    · rw [hv] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hlt, he⟩ := lastZero_spec v m' hv
      exact ⟨by simp; omega, by simpa using he⟩

theorem lastZero_isSome : ∀ (w : List Bool) (i : ℕ) (hi : i < w.length), w[i] = false →
    (lastZero w).isSome
  | [], i, hi, _ => absurd hi (by simp)
  | b :: v, i, hi, h => by
    rw [lastZero_cons]
    rcases hv : lastZero v with _ | m'
    · cases i with
      | zero => simp at h; simp [h]
      | succ i' =>
        have := lastZero_isSome v i' (by simpa using hi) (by simpa using h)
        rw [hv] at this; simp at this
    · simp

/-- The words of length `n`. -/
def words : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (words n).image (List.cons false) ∪ (words n).image (List.cons true)

theorem mem_words : ∀ (n : ℕ) (w : List Bool), w ∈ words n ↔ w.length = n
  | 0, w => by simp [words, List.length_eq_zero_iff]
  | n + 1, w => by
    simp only [words, Finset.mem_union, Finset.mem_image, mem_words n]
    constructor
    · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩) <;> simp [hv]
    · intro h
      obtain ⟨b, v, rfl⟩ : ∃ b v, w = b :: v := by
        cases w with
        | nil => simp at h
        | cons b v => exact ⟨b, v, rfl⟩
      simp only [List.length_cons, add_left_inj] at h
      cases b
      · exact Or.inl ⟨v, h, rfl⟩
      · exact Or.inr ⟨v, h, rfl⟩

theorem sum_words_succ {M : Type*} [AddCommMonoid M] (n : ℕ) (F : List Bool → M) :
    ∑ w ∈ words (n + 1), F w = ∑ v ∈ words n, F (false :: v) + ∑ v ∈ words n, F (true :: v) := by
  rw [words, Finset.sum_union, Finset.sum_image (fun _ _ _ _ h => List.cons_injective h),
    Finset.sum_image (fun _ _ _ _ h => List.cons_injective h)]
  rw [Finset.disjoint_left]
  rintro w h1 h2
  simp only [Finset.mem_image] at h1 h2
  obtain ⟨v, -, rfl⟩ := h1
  obtain ⟨v', -, h⟩ := h2
  simp at h

/-- Exactly one word of each length has no `0`. -/
theorem sum_words_none (c : ENNReal) : ∀ n : ℕ,
    ∑ v ∈ words n, (match lastZero v with | some _ => (0 : ENNReal) | none => c) = c
  | 0 => by simp [words, lastZero]
  | n + 1 => by
    rw [sum_words_succ]
    have h1 : ∀ v ∈ words n, (match lastZero (false :: v) with
        | some _ => (0 : ENNReal) | none => c) = 0 := by
      intro v _; rw [lastZero_cons]; rcases lastZero v with _ | m <;> simp
    have h2 : ∀ v ∈ words n, (match lastZero (true :: v) with
        | some _ => (0 : ENNReal) | none => c) =
        (match lastZero v with | some _ => (0 : ENNReal) | none => c) := by
      intro v _; rw [lastZero_cons]; rcases lastZero v with _ | m <;> simp
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero, zero_add]
    exact sum_words_none c n

/-- `Σ_{|w| = n} g(lastZero w) = Σ_{m < n} 2^m g(m)`, for `g` extended by `0` at `none`. -/
theorem sum_words_lastZero : ∀ (n : ℕ) (g : ℕ → ENNReal),
    ∑ w ∈ words n, (match lastZero w with | some m => g m | none => 0) =
      ∑ m ∈ Finset.range n, 2 ^ m * g m
  | 0, g => by simp [words, lastZero]
  | n + 1, g => by
    rw [sum_words_succ]
    have hone : ∀ v ∈ words n, ∀ b : Bool,
        (match lastZero (b :: v) with | some m => g m | none => 0) =
          (match lastZero v with | some m => g (m + 1) | none => 0) +
            (match lastZero v with
              | some _ => (0 : ENNReal)
              | none => if b = false then g 0 else 0) := by
      intro v _ b
      rw [lastZero_cons]
      rcases lastZero v with _ | m
      · simp only [zero_add]; split_ifs <;> simp
      · simp
    rw [Finset.sum_congr rfl fun v hv => hone v hv false,
      Finset.sum_congr rfl fun v hv => hone v hv true, Finset.sum_add_distrib,
      Finset.sum_add_distrib, sum_words_lastZero n (fun m => g (m + 1))]
    simp only [Bool.true_eq_false, if_false, if_true]
    rw [sum_words_none (g 0) n, sum_words_none 0 n, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, add_zero, pow_succ]
    rw [add_right_comm, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    ring

end P7Dev

end ErschlerZheng
end

section
/-!
# Word balls: word length is subadditive, balls are finite, `v(K r) ⩽ ((2|S|+1) v(r))^K`
-/

namespace ErschlerZheng

namespace WordBallDev

open Pointwise

variable {G : Type*} [Group G]

theorem wordBall_mul_subset (S : Set G) (m n : ℕ) :
    Chou.wordBall S m * Chou.wordBall S n ⊆ Chou.wordBall S (m + n) := by
  rintro _ ⟨_, ⟨l, hl, hls, rfl⟩, _, ⟨l', hl', hls', rfl⟩, rfl⟩
  refine ⟨l ++ l', by simp; omega, ?_, by simp⟩
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hls x h
  · exact hls' x h

theorem one_mem_wordBall (S : Set G) (n : ℕ) : (1 : G) ∈ Chou.wordBall S n :=
  ⟨[], by simp, by simp, rfl⟩

theorem exists_mem_wordBall (S : Set G) (g : G) (hg : g ∈ Subgroup.closure S) :
    ∃ n, g ∈ Chou.wordBall S n := by
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact ⟨1, [s], by simp, by simp [hs], by simp⟩
  | one => exact ⟨0, one_mem_wordBall S 0⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨m, hm⟩ := ihg
    obtain ⟨n, hn⟩ := ihh
    exact ⟨m + n, wordBall_mul_subset S m n ⟨g, hm, h, hn, rfl⟩⟩
  | inv g _ ihg =>
    obtain ⟨m, l, hl, hls, rfl⟩ := ihg
    refine ⟨m, (l.map (·⁻¹)).reverse, by simp; omega, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_reverse, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rcases hls y hy with h | h
      · right; simpa using h
      · left; exact h
    · rw [List.prod_inv_reverse]

end WordBallDev

end ErschlerZheng
end

section
/-!
# Proposition 7.12, the fixed factors `g_j` (`j + k_n ⩽ n`, `ω_{j-1} = 2`) for `υ_n` — prover 7

For `(y, p)` in `B_j × Λ_n`, the first `n` digits of `x = y·(γ_{j+1}^{ε}⋯γ_n^{ε})⁻¹` have law
`[odd]·2/2^n` (G8, clause 1). With `d(o, x) ⩾ 2^m` when the last `0` of `prefix_n(x)` is at `m`
(Gray code) and the count of words by their last `0` (`P7Count`):
`Σ_{(y, p)} f(d(o, x)) ⩽ |B_j × Λ_n|·(2/2^n)·Σ_{m<n} 2^m f(2^m)`.
-/

open scoped RightActions ENNReal
open Garrido

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ErschlerZheng

namespace P7Dev

open GrigBasic P3P712Dev P3U0Dev

theorem sum_low_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j + k n ≤ n)
    (hj : ω (j - 1) = 2) (f : ℝ → ℝ) (hf0 : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hfa : AntitoneOn f (Set.Ici 0))
    [Fintype ↥{x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b}]
    [Fintype (LambdaN D ω k n)] :
    ∑ q : ↥{x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} × LambdaN D ω k n,
        ENNReal.ofReal (f (schreierDist ω oneRay ((q.1 : Ray) <•
          (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
            fun i => ((q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat)⁻¹).prod))) ≤
      ENNReal.ofReal ((Nat.card (↥{x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b} ×
          LambdaN D ω k n) : ℝ) * (2 / 2 ^ n)) *
        ∑ m ∈ Finset.range n, 2 ^ m * ENNReal.ofReal (f (2 ^ m)) := by
  classical
  set S := {x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b}
  set Q := ↥S × LambdaN D ω k n
  set X : Q → Ray := fun q => (q.1 : Ray) <•
    (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
      fun i => ((q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat)⁻¹).prod with hX
  set π : Q → List Bool := fun q => rayPrefix (X q) n with hπ
  set h : List Bool → ℝ≥0∞ := fun w => match lastZero w with
    | some m => ENNReal.ofReal (f (2 ^ m))
    | none => ⊤ with hh
  set h' : List Bool → ℝ≥0∞ := fun w => match lastZero w with
    | some m => ENNReal.ofReal (f (2 ^ m))
    | none => 0 with hh'
  have hG8 := (card_rayPrefix_smul_div_card_eq D ω hω k hk n hn j hj1 hjn hj).2.1
  -- (3) pointwise bound through the last zero of the prefix
  have hpt : ∀ q : Q, ENNReal.ofReal (f (schreierDist ω oneRay (X q))) ≤ h (π q) := by
    intro q
    simp only [hh]
    rcases hz : lastZero (π q) with _ | m
    · exact le_top
    · obtain ⟨hlt, hm⟩ := lastZero_spec _ m hz
      have hxm : X q m = false := by
        simp only [hπ] at hlt hm
        rw [getElem_rayPrefix] at hm
        exact hm
      have hXo : X q ∈ orbitOne ω := by
        refine B8MarkovDev.orbit_smul' q.1.2.1 ((grigorchuk ω).list_prod_mem fun g hg => ?_)
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
        exact (grigorchuk ω).inv_mem (Subgroup.pow_mem _ (mem_G_factor D ω hω k hk n hn _ i) _)
      have hcof : IsCofinal (X q) := by
        have := ((isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary).2.1 ω oneRay).1
        have hx : X q ∈ rightOrbit (grigorchuk ω) oneRay := hXo
        rw [this] at hx
        exact hx
      have hd := two_pow_le_schreierDist ω hcof hxm
      refine ENNReal.ofReal_le_ofReal (hfa (Set.mem_Ici.mpr (by positivity))
        (Set.mem_Ici.mpr (by positivity)) ?_)
      exact_mod_cast hd
  -- (4) fibres over the words of length `n`
  have hmaps : ∀ q ∈ (Finset.univ : Finset Q), π q ∈ words n := fun q _ =>
    (mem_words n _).mpr (length_rayPrefix _ _)
  have hfib : ∑ q : Q, h (π q) =
      ∑ w ∈ words n, ((Finset.univ.filter fun q : Q => π q = w).card : ℝ≥0∞) * h w := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (fun q hq => by rw [(Finset.mem_filter.mp hq).2]),
      Finset.sum_const, nsmul_eq_mul]
  -- (5) the fibre sizes from G8
  have hcard : ∀ w ∈ words n, ((Finset.univ.filter fun q : Q => π q = w).card : ℝ≥0∞) * h w ≤
      ENNReal.ofReal ((Nat.card Q : ℝ) * (2 / 2 ^ n)) * h' w := by
    intro w hw
    have hwl := (mem_words n w).mp hw
    have hG := hG8 w hwl
    have hc : ((Finset.univ.filter fun q : Q => π q = w).card : ℝ) =
        (Nat.card {q : Q // π q = w} : ℝ) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rcases hz : lastZero w with _ | m
    · -- no zero: the parity condition fails, the fibre is empty
      have hall : ∀ i (hi : i < w.length), w[i] = true := by
        intro i hi
        by_contra hne
        have hfalse : w[i] = false := by simpa using hne
        have := lastZero_isSome w i hi hfalse
        rw [hz] at this; simp at this
      have hnotodd : ¬ Odd (j + 1 + (w.take (j + 1)).count true) := by
        have ht : (w.take (j + 1)).count true = (w.take (j + 1)).length := by
          rw [List.count_eq_length]
          intro b hb
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
          rw [List.getElem_take]
          exact (hall i (lt_of_lt_of_le hi (by rw [List.length_take]; exact min_le_right _ _))).symm
        have hkpos := (hk.2 n (by omega) hn).1
        rw [ht, List.length_take, min_eq_left (by omega)]
        rw [Nat.not_odd_iff_even]; exact ⟨j + 1, rfl⟩
      rw [if_neg hnotodd] at hG
      have h0 : (Nat.card {q : Q // π q = w} : ℝ) = 0 := by
        rcases div_eq_zero_iff.mp hG with h0 | h0
        · exact h0
        · have : Nat.card Q = 0 := by exact_mod_cast h0
          have hle : Nat.card {q : Q // π q = w} ≤ Nat.card Q :=
            Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
          rw [this] at hle
          exact_mod_cast Nat.le_zero.mp hle
      have : ((Finset.univ.filter fun q : Q => π q = w).card : ℝ≥0∞) = 0 := by
        have h1 : ((Finset.univ.filter fun q : Q => π q = w).card : ℝ) = 0 := by rw [hc, h0]
        exact_mod_cast h1
      rw [this, zero_mul]; exact zero_le
    · simp only [hh, hh', hz]
      refine mul_le_mul_of_nonneg_right ?_ zero_le
      have hQ : (0 : ℝ) ≤ Nat.card Q := Nat.cast_nonneg _
      have hle : ((Finset.univ.filter fun q : Q => π q = w).card : ℝ) ≤
          (Nat.card Q : ℝ) * (2 / 2 ^ n) := by
        rw [hc]
        rcases (Nat.cast_nonneg (Nat.card Q) : (0 : ℝ) ≤ _).lt_or_eq with hpos | hzero
        · have h2 := hG
          rw [div_eq_iff hpos.ne'] at h2
          have hb : (if Odd (j + 1 + (w.take (j + 1)).count true) then (2 : ℝ) / 2 ^ n else 0) ≤
              2 / 2 ^ n := by
            split_ifs
            · exact le_rfl
            · positivity
          calc (Nat.card {q : Q // π q = w} : ℝ) =
                (if Odd (j + 1 + (w.take (j + 1)).count true) then (2 : ℝ) / 2 ^ n else 0) *
                  (Nat.card Q : ℝ) := h2
            _ ≤ 2 / 2 ^ n * (Nat.card Q : ℝ) := mul_le_mul_of_nonneg_right hb hQ
            _ = (Nat.card Q : ℝ) * (2 / 2 ^ n) := mul_comm _ _
        · have h0 : Nat.card Q = 0 := by exact_mod_cast hzero.symm
          have hle : Nat.card {q : Q // π q = w} ≤ Nat.card Q :=
            Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
          rw [h0] at hle
          rw [Nat.le_zero.mp hle, h0]
          simp
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hle
  have key : ∑ q : Q, ENNReal.ofReal (f (schreierDist ω oneRay (X q))) ≤
      ENNReal.ofReal ((Nat.card Q : ℝ) * (2 / 2 ^ n)) *
        ∑ m ∈ Finset.range n, 2 ^ m * ENNReal.ofReal (f (2 ^ m)) := by
    calc ∑ q : Q, ENNReal.ofReal (f (schreierDist ω oneRay (X q))) ≤ ∑ q : Q, h (π q) :=
          Finset.sum_le_sum fun q _ => hpt q
      _ = _ := hfib
      _ ≤ ∑ w ∈ words n, ENNReal.ofReal ((Nat.card Q : ℝ) * (2 / 2 ^ n)) * h' w :=
          Finset.sum_le_sum hcard
      _ = _ := by
          rw [← Finset.mul_sum]
          exact congrArg (fun z => ENNReal.ofReal ((Nat.card Q : ℝ) * (2 / 2 ^ n)) * z)
            (sum_words_lastZero n (fun m => ENNReal.ofReal (f (2 ^ m))))
  convert key using 2
  exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

open Classical in
/-- The `t`-term of `sum_mass_upsilon_le` for a fixed factor `g_j`, `j = n - t`, `j + k_n ⩽ n`,
`ω_{j-1} = 2`: at most `|B_j|·(2/2^n)·Σ_{m<n} 2^m f(2^m)`. -/
theorem term_low_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (t : Fin n) (hjn : n - t + k n ≤ n)
    (hj : ω (n - t - 1) = 2) (f : ℝ → ℝ) (hf0 : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hfa : AntitoneOn f (Set.Ici 0))
    [Fintype ↥{x | x ∈ orbitOne ω ∧ (seqG ω (n - t), x) ∉ letterGerms ω .b}]
    [Fintype (LambdaN D ω k n)] :
    ∑ p : LambdaN D ω k n, (if p.1 t.rev = true then
        ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ)) *
          ∑' y : orbitOne ω, (if ((p.2 t.rev : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b then
            ENNReal.ofReal (f (schreierDist ω oneRay ((y : Ray) <• (prodTake D ω k n p t)⁻¹)))
            else 0) else 0) ≤
      ENNReal.ofReal ((Nat.card ↥{x | x ∈ orbitOne ω ∧ (seqG ω (n - t), x) ∉ letterGerms ω .b} : ℝ)
        * (2 / 2 ^ n)) * ∑ m ∈ Finset.range n, 2 ^ m * ENNReal.ofReal (f (2 ^ m)) := by
  classical
  have ht : (t : ℕ) < n := t.2
  set j := n - (t : ℕ) with hjdef
  have hj1 : 1 ≤ j := by omega
  set S := {x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b}
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ))
  set Pr : LambdaN D ω k n → BinaryTreeAut := fun p =>
    (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
      fun i => ((p.2 i : Garrido.BinaryTreeAut) ^ (p.1 i).toNat)⁻¹).prod with hPr
  set G : Ray → ℝ≥0∞ := fun r => ENNReal.ofReal (f (schreierDist ω oneRay r)) with hG
  -- the factor at `t.rev` is `g_j`
  have hγ : ∀ p : LambdaN D ω k n, (p.2 t.rev : BinaryTreeAut) = seqG ω j := by
    intro p
    have hmem := (p.2 t.rev).2
    have hidx : ((t.rev : Fin n) : ℕ) + 1 = j := by simp [Fin.val_rev]; omega
    obtain ⟨a, ha⟩ : ∃ a, a = (p.2 t.rev : BinaryTreeAut) := ⟨_, rfl⟩
    rw [← ha] at hmem ⊢
    rw [hidx] at hmem
    unfold fSet at hmem
    rw [if_neg (by omega)] at hmem
    exact hmem
  have hP : ∀ p : LambdaN D ω k n, (prodTake D ω k n p t)⁻¹ = Pr p := fun p =>
    prodTake_inv_eq D ω hω k hk n hn p t ht.le
  have hinner : ∀ p : LambdaN D ω k n,
      ∑' y : orbitOne ω, (if ((p.2 t.rev : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b then
        ENNReal.ofReal (f (schreierDist ω oneRay ((y : Ray) <• (prodTake D ω k n p t)⁻¹)))
        else 0) = ∑ y : ↥S, G ((y : Ray) <• Pr p) := by
    intro p
    rw [tsum_subtype (orbitOne ω) (fun r => if ((p.2 t.rev : BinaryTreeAut), r) ∉
      letterGerms ω .b then ENNReal.ofReal (f (schreierDist ω oneRay (r <• (prodTake D ω k n p t)⁻¹)))
      else 0)]
    rw [show (∑ y : ↥S, G ((y : Ray) <• Pr p)) = ∑' y : ↥S, G ((y : Ray) <• Pr p) from
      (tsum_fintype (L := SummationFilter.unconditional _) _).symm,
      tsum_subtype S (fun r => G (r <• Pr p))]
    congr 1; funext r
    simp only [Set.indicator, hγ p, hP p, S, Set.mem_ofPred_eq, hG]
    by_cases h1 : r ∈ orbitOne ω <;> by_cases h2 : (seqG ω j, r) ∈ letterGerms ω .b <;>
      simp [h1, h2]
  have hlow := sum_low_le D ω hω k hk n hn j hj1 (by omega) (by simpa [hjdef] using hj) f hf0 hfa
  have hne : Nonempty (LambdaN D ω k n) :=
    ⟨⟨fun _ => false, (ConstrG9.nonempty_fProd D ω hω k hk n hn).some⟩⟩
  have hΛ : (0 : ℝ) < Nat.card (LambdaN D ω k n) := by
    exact_mod_cast Nat.card_pos
  calc _ ≤ ∑ p : LambdaN D ω k n, c * ∑ y : ↥S, G ((y : Ray) <• Pr p) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [← hinner p]
        split_ifs
        · exact le_rfl
        · exact zero_le
    _ = c * ∑ q : ↥S × LambdaN D ω k n, G ((q.1 : Ray) <• Pr q.2) := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type_right]
    _ ≤ c * (ENNReal.ofReal ((Nat.card (↥S × LambdaN D ω k n) : ℝ) * (2 / 2 ^ n)) *
          ∑ m ∈ Finset.range n, 2 ^ m * ENNReal.ofReal (f (2 ^ m))) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), Nat.card_prod ↥S (LambdaN D ω k n)]
        congr 2
        push_cast
        field_simp

theorem eq_oneRay_of_schreierDist_eq_zero (ω : ℕ → Fin 3) {x : Ray} (hx : x ∈ orbitOne ω)
    (h : schreierDist ω oneRay x = 0) : x = oneRay := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨m, hm⟩ := WordBallDev.exists_mem_wordBall (gens ω) g hg
  have hne : {n | ∃ g' ∈ Chou.wordBall (gens ω) n, oneRay <• g = oneRay <• g'}.Nonempty :=
    ⟨m, g, hm, rfl⟩
  have hmem := Nat.sInf_mem hne
  have h0 : sInf {n | ∃ g' ∈ Chou.wordBall (gens ω) n, oneRay <• g = oneRay <• g'} = 0 := h
  rw [h0] at hmem
  obtain ⟨g', ⟨l, hl, -, rfl⟩, he⟩ := hmem
  rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)] at he
  rw [he]; simp

open Classical in
/-- For `υ̌_n`, fixed factor `g_j⁻¹` (`j + k_n ⩽ n`, `ω_{j-1} = 2`): with `F(r) = [r ≠ o] f(d(o, r))`,
`Σ_{(y,p) ∈ B'_j × Λ_n} F(y·Q⁻¹) ⩽ |B'_j × Λ_n|/2^{j-1}·(Σ_{m<j-1} 2^m f(2^m) + f(1))` (G8 clause 3). -/
theorem sum_lowInv_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j + k n ≤ n)
    (hj : ω (j - 1) = 2) (f : ℝ → ℝ) (hf0 : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hfa : AntitoneOn f (Set.Ici 0))
    [Fintype ↥{x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b}]
    [Fintype (LambdaN D ω k n)] :
    ∑ q : ↥{x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} × LambdaN D ω k n,
        (if (q.1 : Ray) <• ((((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).map
            fun i => (q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat).reverse).prod ≠ oneRay then
          ENNReal.ofReal (f (schreierDist ω oneRay ((q.1 : Ray) <•
            ((((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).map
              fun i => (q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat).reverse).prod))) else 0) ≤
      ENNReal.ofReal ((Nat.card (↥{x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b} ×
          LambdaN D ω k n) : ℝ) * (1 / 2 ^ (j - 1))) *
        (∑ m ∈ Finset.range (j - 1), 2 ^ m * ENNReal.ofReal (f (2 ^ m)) +
          ENNReal.ofReal (f 1)) := by
  classical
  set S := {x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b}
  set Q := ↥S × LambdaN D ω k n
  set X : Q → Ray := fun q => (q.1 : Ray) <•
    ((((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).map
      fun i => (q.2.2 i : Garrido.BinaryTreeAut) ^ (q.2.1 i).toNat).reverse).prod with hX
  set π : Q → List Bool := fun q => rayPrefix (X q) (j - 1) with hπ
  set h : List Bool → ℝ≥0∞ := fun w => match lastZero w with
    | some m => ENNReal.ofReal (f (2 ^ m))
    | none => ENNReal.ofReal (f 1) with hh
  have hG8 := (card_rayPrefix_smul_div_card_eq D ω hω k hk n hn j hj1 hjn hj).2.2.2
  have hXo : ∀ q : Q, X q ∈ orbitOne ω := by
    intro q
    refine B8MarkovDev.orbit_smul' q.1.2.1 ((grigorchuk ω).list_prod_mem fun g hg => ?_)
    rw [List.mem_reverse] at hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
    exact Subgroup.pow_mem _ (mem_G_factor D ω hω k hk n hn _ i) _
  have hpt : ∀ q : Q, (if X q ≠ oneRay then ENNReal.ofReal (f (schreierDist ω oneRay (X q)))
      else 0) ≤ h (π q) := by
    intro q
    split_ifs with hne
    · simp only [hh]
      have hcof : IsCofinal (X q) := by
        have := ((isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary).2.1 ω oneRay).1
        have hx : X q ∈ rightOrbit (grigorchuk ω) oneRay := hXo q
        rw [this] at hx
        exact hx
      rcases hz : lastZero (π q) with _ | m
      · have hd : 1 ≤ schreierDist ω oneRay (X q) := by
          rcases Nat.eq_zero_or_pos (schreierDist ω oneRay (X q)) with h0 | h0
          · exact absurd (eq_oneRay_of_schreierDist_eq_zero ω (hXo q) h0) hne
          · exact h0
        refine ENNReal.ofReal_le_ofReal (hfa (Set.mem_Ici.mpr (by norm_num))
          (Set.mem_Ici.mpr (by positivity)) ?_)
        exact_mod_cast hd
      · obtain ⟨hlt, hm⟩ := lastZero_spec _ m hz
        have hxm : X q m = false := by
          simp only [hπ] at hlt hm
          rw [getElem_rayPrefix] at hm
          exact hm
        have hd := two_pow_le_schreierDist ω hcof hxm
        refine ENNReal.ofReal_le_ofReal (hfa (Set.mem_Ici.mpr (by positivity))
          (Set.mem_Ici.mpr (by positivity)) ?_)
        exact_mod_cast hd
    · exact zero_le
  have hmaps : ∀ q ∈ (Finset.univ : Finset Q), π q ∈ words (j - 1) := fun q _ =>
    (mem_words (j - 1) _).mpr (length_rayPrefix _ _)
  have hfib : ∑ q : Q, h (π q) =
      ∑ w ∈ words (j - 1), ((Finset.univ.filter fun q : Q => π q = w).card : ℝ≥0∞) * h w := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (fun q hq => by rw [(Finset.mem_filter.mp hq).2]),
      Finset.sum_const, nsmul_eq_mul]
  have hcard : ∀ w ∈ words (j - 1),
      ((Finset.univ.filter fun q : Q => π q = w).card : ℝ≥0∞) * h w ≤
      ENNReal.ofReal ((Nat.card Q : ℝ) * (1 / 2 ^ (j - 1))) * h w := by
    intro w hw
    have hwl := (mem_words (j - 1) w).mp hw
    have hG := hG8 w hwl
    have hc : ((Finset.univ.filter fun q : Q => π q = w).card : ℝ) =
        (Nat.card {q : Q // π q = w} : ℝ) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    have hQ : (0 : ℝ) ≤ Nat.card Q := Nat.cast_nonneg _
    have hle : ((Finset.univ.filter fun q : Q => π q = w).card : ℝ) ≤
        (Nat.card Q : ℝ) * (1 / 2 ^ (j - 1)) := by
      rw [hc]
      rcases (Nat.cast_nonneg (Nat.card Q) : (0 : ℝ) ≤ _).lt_or_eq with hpos | hzero
      · have h2 := hG
        rw [div_eq_iff hpos.ne'] at h2
        rw [h2, mul_comm]
      · have h0 : Nat.card Q = 0 := by exact_mod_cast hzero.symm
        have hle : Nat.card {q : Q // π q = w} ≤ Nat.card Q :=
          Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
        rw [h0] at hle
        rw [Nat.le_zero.mp hle, h0]
        simp
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hle
  have key : ∑ q : Q, (if X q ≠ oneRay then ENNReal.ofReal (f (schreierDist ω oneRay (X q)))
      else 0) ≤ ENNReal.ofReal ((Nat.card Q : ℝ) * (1 / 2 ^ (j - 1))) *
        (∑ m ∈ Finset.range (j - 1), 2 ^ m * ENNReal.ofReal (f (2 ^ m)) +
          ENNReal.ofReal (f 1)) := by
    calc _ ≤ ∑ q : Q, h (π q) := Finset.sum_le_sum fun q _ => hpt q
      _ = _ := hfib
      _ ≤ ∑ w ∈ words (j - 1), ENNReal.ofReal ((Nat.card Q : ℝ) * (1 / 2 ^ (j - 1))) * h w :=
          Finset.sum_le_sum hcard
      _ = _ := by
          rw [← Finset.mul_sum]
          congr 1
          have hsplit : ∀ w, h w = (match lastZero w with
              | some m => ENNReal.ofReal (f (2 ^ m)) | none => 0) +
              (match lastZero w with | some _ => (0 : ENNReal) | none => ENNReal.ofReal (f 1)) := by
            intro w; simp only [hh]; rcases lastZero w with _ | m <;> simp
          rw [Finset.sum_congr rfl fun w _ => hsplit w, Finset.sum_add_distrib]
          congr 1
          · exact sum_words_lastZero (j - 1) (fun m => ENNReal.ofReal (f (2 ^ m)))
          · exact sum_words_none (ENNReal.ofReal (f 1)) (j - 1)
  convert key using 2
  exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

open Classical in
/-- The `t`-term of `sum_mass_upsilonCheck_le` for a fixed factor `g_j⁻¹`, `j = t + 1`,
`j + k_n ⩽ n`, `ω_{j-1} = 2`, with `F(r) = [r ≠ o] f(d(o, r))`:
at most `|B'_j|/2^{j-1}·(Σ_{m<j-1} 2^m f(2^m) + f(1))`. -/
theorem term_lowInv_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n) (t : Fin n) (hjn : (t : ℕ) + 1 + k n ≤ n)
    (hj : ω t = 2) (f : ℝ → ℝ) (hf0 : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hfa : AntitoneOn f (Set.Ici 0))
    [Fintype ↥{x | x ∈ orbitOne ω ∧ ((seqG ω ((t : ℕ) + 1))⁻¹, x) ∉ letterGerms ω .b}]
    [Fintype (LambdaN D ω k n)] :
    ∑ p : LambdaN D ω k n, (if p.1 t = true then
        ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ)) *
          ∑' y : orbitOne ω, (if (((p.2 t : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b then
            ENNReal.ofReal (if (y : Ray) <• (prodTakeInv D ω k n p t)⁻¹ ≠ oneRay then
              f (schreierDist ω oneRay ((y : Ray) <• (prodTakeInv D ω k n p t)⁻¹)) else 0)
            else 0) else 0) ≤
      ENNReal.ofReal ((Nat.card ↥{x | x ∈ orbitOne ω ∧
          ((seqG ω ((t : ℕ) + 1))⁻¹, x) ∉ letterGerms ω .b} : ℝ) * (1 / 2 ^ ((t : ℕ) + 1 - 1))) *
        (∑ m ∈ Finset.range ((t : ℕ) + 1 - 1), 2 ^ m * ENNReal.ofReal (f (2 ^ m)) +
          ENNReal.ofReal (f 1)) := by
  classical
  have ht : (t : ℕ) < n := t.2
  set j := (t : ℕ) + 1 with hjdef
  have hj1 : 1 ≤ j := by omega
  set S := {x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b}
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ))
  set Pr : LambdaN D ω k n → BinaryTreeAut := fun p =>
    ((((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).map
      fun i => (p.2 i : Garrido.BinaryTreeAut) ^ (p.1 i).toNat).reverse).prod with hPr
  set G : Ray → ℝ≥0∞ := fun r => if r ≠ oneRay then ENNReal.ofReal (f (schreierDist ω oneRay r))
    else 0 with hG
  have hγ : ∀ p : LambdaN D ω k n, (p.2 t : BinaryTreeAut) = seqG ω j := by
    intro p
    have hmem := (p.2 t).2
    obtain ⟨a, ha⟩ : ∃ a, a = (p.2 t : BinaryTreeAut) := ⟨_, rfl⟩
    rw [← ha] at hmem ⊢
    unfold fSet at hmem
    rw [if_neg (by omega)] at hmem
    exact hmem
  have hP : ∀ p : LambdaN D ω k n, (prodTakeInv D ω k n p t)⁻¹ = Pr p := fun p =>
    prodTakeInv_inv_eq D ω hω k hk n hn p t ht.le
  have hinner : ∀ p : LambdaN D ω k n,
      ∑' y : orbitOne ω, (if (((p.2 t : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b then
        ENNReal.ofReal (if (y : Ray) <• (prodTakeInv D ω k n p t)⁻¹ ≠ oneRay then
          f (schreierDist ω oneRay ((y : Ray) <• (prodTakeInv D ω k n p t)⁻¹)) else 0)
        else 0) = ∑ y : ↥S, G ((y : Ray) <• Pr p) := by
    intro p
    rw [tsum_subtype (orbitOne ω) (fun r => if (((p.2 t : BinaryTreeAut))⁻¹, r) ∉
      letterGerms ω .b then ENNReal.ofReal (if r <• (prodTakeInv D ω k n p t)⁻¹ ≠ oneRay then
        f (schreierDist ω oneRay (r <• (prodTakeInv D ω k n p t)⁻¹)) else 0) else 0)]
    rw [show (∑ y : ↥S, G ((y : Ray) <• Pr p)) = ∑' y : ↥S, G ((y : Ray) <• Pr p) from
      (tsum_fintype (L := SummationFilter.unconditional _) _).symm,
      tsum_subtype S (fun r => G (r <• Pr p))]
    congr 1; funext r
    simp only [Set.indicator, hγ p, hP p, S, Set.mem_ofPred_eq, hG]
    by_cases h1 : r ∈ orbitOne ω <;> by_cases h2 : ((seqG ω j)⁻¹, r) ∈ letterGerms ω .b <;>
      by_cases h3 : r <• Pr p = oneRay <;> simp [h1, h2, h3]
  have hlow := sum_lowInv_le D ω hω k hk n hn j hj1 (by omega) (by simpa [hjdef] using hj) f hf0 hfa
  have hne : Nonempty (LambdaN D ω k n) :=
    ⟨⟨fun _ => false, (ConstrG9.nonempty_fProd D ω hω k hk n hn).some⟩⟩
  have hΛ : (0 : ℝ) < Nat.card (LambdaN D ω k n) := by
    exact_mod_cast Nat.card_pos
  calc _ ≤ ∑ p : LambdaN D ω k n, c * ∑ y : ↥S, G ((y : Ray) <• Pr p) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [← hinner p]
        split_ifs
        · exact le_rfl
        · exact zero_le
    _ = c * ∑ q : ↥S × LambdaN D ω k n, G ((q.1 : Ray) <• Pr q.2) := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type_right]
    _ ≤ c * (ENNReal.ofReal ((Nat.card (↥S × LambdaN D ω k n) : ℝ) * (1 / 2 ^ (j - 1))) *
          (∑ m ∈ Finset.range (j - 1), 2 ^ m * ENNReal.ofReal (f (2 ^ m)) +
            ENNReal.ofReal (f 1))) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), Nat.card_prod ↥S (LambdaN D ω k n)]
        congr 2
        push_cast
        field_simp
        rw [show j - 1 = (t : ℕ) by omega]

end P7Dev

end ErschlerZheng
end

section
/-!
# Conditioning on one coordinate of a product (prover 7, toward Proposition 7.12, item 6)

For a finite product `Π_i β_i` and a function `G` that does not depend on coordinate `i₀`,
`Σ_p G(p) = |β_{i₀}| · Σ_{p : p_{i₀} = a} G(p)` for every `a`. (`Λ_n = {0,1}ⁿ × Π_i 𝔉_{i,n}`; the
products `P_t(p)` of the union bound do not involve the coordinate of `γ_j`.) No stubs.
-/

namespace ErschlerZheng

namespace P7Dev

theorem sum_eq_card_mul_sum_fiber {ι : Type*} [DecidableEq ι] [Fintype ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)] (i₀ : ι) (a : β i₀)
    (G : ((i : ι) → β i) → ENNReal) (hG : ∀ p b, G (Function.update p i₀ b) = G p) :
    ∑ p, G p = (Fintype.card (β i₀) : ENNReal) *
      ∑ p ∈ Finset.univ.filter (fun p : (i : ι) → β i => p i₀ = a), G p := by
  rw [← Finset.sum_fiberwise Finset.univ (fun p : (i : ι) → β i => p i₀) G]
  have key : ∀ b : β i₀, ∑ p ∈ Finset.univ.filter (fun p : (i : ι) → β i => p i₀ = b), G p =
      ∑ p ∈ Finset.univ.filter (fun p : (i : ι) → β i => p i₀ = a), G p := by
    intro b
    refine Finset.sum_nbij' (fun p => Function.update p i₀ a) (fun p => Function.update p i₀ b)
      ?_ ?_ ?_ ?_ ?_
    · intro p _; simp
    · intro p _; simp
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Function.update_idem]
      rw [← hp, Function.update_eq_self]
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Function.update_idem]
      rw [← hp, Function.update_eq_self]
    · intro p _; rw [hG]
  rw [Finset.sum_congr rfl fun b _ => key b, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

open Classical in
/-- Conditioning on coordinate `i₀` of the second factor of `A × Π_i β_i`: if `F` does not depend on
that coordinate, `Σ_p [P(p₂ i₀)] F(p) = Σ_a [P a] |β_{i₀}|⁻¹ Σ_p F(p)`. -/
theorem sum_indicator_coord {A ι : Type*} [Fintype A] [DecidableEq ι] [Fintype ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)] [∀ i, Nonempty (β i)] (i₀ : ι)
    (P : β i₀ → Prop) (F : A × ((i : ι) → β i) → ENNReal)
    (hF : ∀ e γ b, F (e, Function.update γ i₀ b) = F (e, γ)) :
    ∑ p : A × ((i : ι) → β i), (if P (p.2 i₀) then F p else 0) =
      ∑ a : β i₀, if P a then (Fintype.card (β i₀) : ENNReal)⁻¹ *
        ∑ p : A × ((i : ι) → β i), F p else 0 := by
  have hc0 : (Fintype.card (β i₀) : ENNReal) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hcT : (Fintype.card (β i₀) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hfib : ∀ (e : A) (a : β i₀),
      ∑ γ ∈ Finset.univ.filter (fun γ : (i : ι) → β i => γ i₀ = a), F (e, γ) =
        (Fintype.card (β i₀) : ENNReal)⁻¹ * ∑ γ, F (e, γ) := by
    intro e a
    rw [sum_eq_card_mul_sum_fiber i₀ a (fun γ => F (e, γ)) (fun γ b => hF e γ b), ← mul_assoc,
      ENNReal.inv_mul_cancel hc0 hcT, one_mul]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ e : A, ∑ γ : (i : ι) → β i, (if P (γ i₀) then F (e, γ) else 0) =
      ∑ a : β i₀, if P a then (Fintype.card (β i₀) : ENNReal)⁻¹ * ∑ γ, F (e, γ) else 0 := by
    intro e
    rw [← Finset.sum_fiberwise Finset.univ (fun γ : (i : ι) → β i => γ i₀)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_congr rfl (fun γ hγ => by
      rw [(Finset.mem_filter.mp hγ).2])]
    split_ifs with hP
    · exact hfib e a
    · simp
  simp only [hinner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [← Finset.mul_sum, Fintype.sum_prod_type]
  · simp

end P7Dev

end ErschlerZheng
end

section
/-!
# The shape of Lemma 7.21 with a constant

`I1Bound D ω k C` is the conclusion of the milestone `ErschlerZheng.tsum_f_schreierDist_div_card_le`
(Lemma 7.21, both parts) for every admissible level, with the factor `C` on the second term. The
milestone as published is the case `C = 1`. Shared by the open-milestone provers: the Lemma 7.21
prover settles which `C` holds, the Proposition 7.12 prover assembles from `∃ C, I1Bound D ω k C`.
-/

open scoped RightActions

namespace ErschlerZheng

namespace OpI1

/-- Lemma 7.21's two bounds, with the constant `C` on the second term. -/
def I1Bound (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (C : ℝ) : Prop :=
  ∀ (n : ℕ), D ∣ n → ∀ (j : ℕ), 1 ≤ j → ω (j - 1) = 2 → n < j + k n → j ≤ n →
    ∀ (v : List Bool), v ∈ vSet D ω j (2 * k n) → n - j + D ≤ commonPrefixLength v oneRay →
    ∀ (f : ℝ → ℝ), Antitone f → (∀ s, 0 ≤ f s) →
    (∀ x ∈ orbitOne ω, (gTilde ω j v, x) ∉ letterGerms ω .b →
      (∑' p : LambdaN D ω k n, f (schreierDist ω oneRay
          (x <• (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map fun i =>
            ((p.2 i : Garrido.BinaryTreeAut) ^ (p.1 i).toNat)⁻¹).prod))) /
          Nat.card (LambdaN D ω k n) ≤
        f (2 ^ (j + 2 * k n)) +
          C * (f (2 ^ (n + D)) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
            (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n)))) ∧
    ∀ x ∈ orbitOne ω, ((gTilde ω j v)⁻¹, x) ∉ letterGerms ω .b →
      (∑' p : LambdaN D ω k n, f (schreierDist ω oneRay
          (x <• (((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).reverse.map fun i =>
            (p.2 i : Garrido.BinaryTreeAut) ^ (p.1 i).toNat).prod))) /
          Nat.card (LambdaN D ω k n) ≤
        f (2 ^ (j + 2 * k n)) +
          C * (f (2 ^ n) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
            (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n)))

end OpI1

end ErschlerZheng
end

section
/-!
# Proposition 7.12 (corrected), the levels `n - k_n < j ⩽ n` of Lemma 7.21, with its constant (OpI2)

Copies of prover 7's `P7I2High.term_high_le`, `term_highInv_le` (and their helpers), with Lemma 7.21
taken from the hypothesis `OpI1.I1Bound D ω k C` (its second term multiplied by `C ⩾ 0`) instead of
the I1 stub: conditioning on `γ_j` (`P7Cond`), Lemma 7.21 per bad point, and `|bad(g̃^v_j)| = 2^j`
(G6). This module does not import the I1 stub.
-/

open scoped RightActions ENNReal
open Garrido

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ErschlerZheng

namespace OpI2

open P7Dev GrigBasic P3P712Dev P3U0Dev

/-- `I1Bound` is monotone in its constant. -/
theorem I1Bound_mono {D : ℕ} {ω : ℕ → Fin 3} {k : ℕ → ℕ} {C C' : ℝ} (h : OpI1.I1Bound D ω k C)
    (hCC' : C ≤ C') : OpI1.I1Bound D ω k C' := by
  intro n hn j hj1 hj hjn hjn' v hv hv' f hf hf0
  obtain ⟨h1, h2⟩ := h n hn j hj1 hj hjn hjn' v hv hv' f hf hf0
  refine ⟨fun x hx hb => (h1 x hx hb).trans ?_, fun x hx hb => (h2 x hx hb).trans ?_⟩
  · gcongr
    have := hf0 (2 ^ (n + D))
    positivity
  · gcongr
    have := hf0 (2 ^ n)
    positivity

/-- The products `Pr` of the union bound do not involve the coordinate `j - 1` of `γ`. -/
theorem prod_update_eqC (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n j : ℕ) (e : Fin n → Bool)
    (γ : fProd D ω k n) (i₀ : Fin n) (hi₀ : (i₀ : ℕ) < j) (b : ↥(fSet D ω k (i₀ + 1) n)) :
    (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
      fun i => (((Function.update γ i₀ b) i : Garrido.BinaryTreeAut) ^ (e i).toNat)⁻¹).prod =
    (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
      fun i => ((γ i : Garrido.BinaryTreeAut) ^ (e i).toNat)⁻¹).prod := by
  congr 1
  apply List.map_congr_left
  intro i hi
  have hne : i ≠ i₀ := by
    intro h; subst h
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hi
    omega
  rw [Function.update_of_ne hne]

/-- Lemma 7.21 clause 1 (from `I1Bound … C`) in `[0, ∞]`, for an `f` given on `[0, ∞)` only. -/
theorem sum_I1C_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (C : ℝ) (hC : 0 ≤ C) (hI1 : OpI1.I1Bound D ω k C) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : ω (j - 1) = 2) (hjn : n < j + k n) (hjn' : j ≤ n) (f : ℝ → ℝ)
    (hf0 : ∀ s, 0 ≤ s → 0 ≤ f s) (hfa : AntitoneOn f (Set.Ici 0)) [Fintype (LambdaN D ω k n)]
    (g : BinaryTreeAut) (hg : g ∈ fSet D ω k j n) (y : Ray) (hy : y ∈ orbitOne ω)
    (hbad : (g, y) ∉ letterGerms ω .b) :
    ∑ p : LambdaN D ω k n, ENNReal.ofReal (f (schreierDist ω oneRay (y <•
      (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
        fun i => ((p.2 i : Garrido.BinaryTreeAut) ^ (p.1 i).toNat)⁻¹).prod))) ≤
      ENNReal.ofReal ((Nat.card (LambdaN D ω k n) : ℝ) * (f (2 ^ (j + 2 * k n)) +
          C * (f (2 ^ (n + D)) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
            (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n))))) := by
  unfold fSet at hg
  rw [if_pos ⟨hj, hjn, hjn'⟩] at hg
  obtain ⟨v, hv, hv', rfl⟩ := hg
  set fh : ℝ → ℝ := fun s => f (max s 0) with hfh
  have hfh_anti : Antitone fh := fun a b hab =>
    hfa (Set.mem_Ici.mpr (le_max_right _ _)) (Set.mem_Ici.mpr (le_max_right _ _))
      (max_le_max hab le_rfl)
  have hfh0 : ∀ s, 0 ≤ fh s := fun s => hf0 _ (le_max_right _ _)
  have hfe : ∀ s, 0 ≤ s → fh s = f s := fun s hs => by simp only [hfh, max_eq_left hs]
  have h1 := (hI1 n hn j hj1 hj hjn hjn' v hv hv' fh hfh_anti hfh0).1 y hy hbad
  rw [tsum_fintype] at h1
  simp only [hfe _ (Nat.cast_nonneg _), hfe _ (by positivity : (0 : ℝ) ≤ 2 ^ (j + 2 * k n)),
    hfe _ (by positivity : (0 : ℝ) ≤ 2 ^ (n + D))] at h1
  have hne : Nonempty (LambdaN D ω k n) :=
    ⟨⟨fun _ => false, (ConstrG9.nonempty_fProd D ω hω k hk n hn).some⟩⟩
  have hΛ : (0 : ℝ) < Nat.card (LambdaN D ω k n) := by exact_mod_cast Nat.card_pos
  rw [div_le_iff₀ hΛ] at h1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => hf0 _ (Nat.cast_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (by linarith)

open Classical in
/-- A constant summed over the bad points of `g` in the orbit. -/
theorem tsum_bad_constC (ω : ℕ → Fin 3) (g : BinaryTreeAut) (N : ℕ)
    (hN : {x | x ∈ orbitOne ω ∧ (g, x) ∉ letterGerms ω .b}.ncard = N) (hN0 : 0 < N)
    (K : ℝ≥0∞) :
    ∑' y : orbitOne ω, (if (g, (y : Ray)) ∉ letterGerms ω .b then K else 0) = N * K := by
  set Sb := {x | x ∈ orbitOne ω ∧ (g, x) ∉ letterGerms ω .b}
  have hfin : Sb.Finite := Set.finite_of_ncard_pos (by omega)
  have : Fintype ↥Sb := hfin.fintype
  rw [tsum_subtype (orbitOne ω) (fun r => if (g, r) ∉ letterGerms ω .b then K else 0)]
  have e : (orbitOne ω).indicator (fun r => if (g, r) ∉ letterGerms ω .b then K else 0) =
      Sb.indicator (fun _ => K) := by
    funext r
    by_cases h1 : r ∈ orbitOne ω <;> by_cases h2 : (g, r) ∈ letterGerms ω .b <;>
      simp [Set.indicator, Sb, h1, h2]
  rw [e, ← tsum_subtype Sb (fun _ => K), tsum_fintype (L := SummationFilter.unconditional _),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hN]

open Classical in
/-- Item 6 for `υ_n`: the `t`-term of `sum_mass_upsilon_le` for `j = n - t`, `n < j + k_n`,
`ω_{j-1} = 2` is at most `2^j (f(2^{j+2k_n}) + C f(2^{n+D}) k_n^{1+2/D} 2^{-(j+2k_n-n)/D})`. -/
theorem term_highC_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (C : ℝ) (hC : 0 ≤ C) (hI1 : OpI1.I1Bound D ω k C) (n : ℕ) (hn : D ∣ n) (t : Fin n) (hjn : n < n - t + k n)
    (hj : ω (n - t - 1) = 2) (f : ℝ → ℝ) (hf0 : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hfa : AntitoneOn f (Set.Ici 0)) [Fintype (LambdaN D ω k n)] :
    ∑ p : LambdaN D ω k n, (if p.1 t.rev = true then
        ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ)) *
          ∑' y : orbitOne ω, (if ((p.2 t.rev : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b then
            ENNReal.ofReal (f (schreierDist ω oneRay ((y : Ray) <• (prodTake D ω k n p t)⁻¹)))
            else 0) else 0) ≤
      2 ^ (n - (t : ℕ)) * ENNReal.ofReal (f (2 ^ (n - (t : ℕ) + 2 * k n)) +
          C * (f (2 ^ (n + D)) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
            (2 : ℝ) ^ (-(1 / (D : ℝ)) * (((n - (t : ℕ) : ℕ) : ℝ) + 2 * k n - n)))) := by
  classical
  have ht : (t : ℕ) < n := t.2
  set j := n - (t : ℕ) with hjdef
  have hj1 : 1 ≤ j := by omega
  have hjn' : j ≤ n := by omega
  have hidx : ((t.rev : Fin n) : ℕ) + 1 = j := by simp [Fin.val_rev]; omega
  set B : ℝ := f (2 ^ (j + 2 * k n)) + C * (f (2 ^ (n + D)) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
    (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n))) with hB
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ))
  set Pr : LambdaN D ω k n → BinaryTreeAut := fun p =>
    (((List.finRange n).filter fun i : Fin n => j ≤ i.val).map
      fun i => ((p.2 i : Garrido.BinaryTreeAut) ^ (p.1 i).toNat)⁻¹).prod with hPr
  have hP : ∀ p, (prodTake D ω k n p t)⁻¹ = Pr p := fun p =>
    prodTake_inv_eq D ω hω k hk n hn p t ht.le
  set F : LambdaN D ω k n → orbitOne ω → ℝ≥0∞ := fun p y =>
    ENNReal.ofReal (f (schreierDist ω oneRay ((y : Ray) <• Pr p))) with hFdef
  obtain ⟨c6, hc6, C6, hC6, H6⟩ := setOf_not_mem_letterGerms_gTilde_eq_and_ncard_and_schreierDist D ω hω k hk
  have hne : Nonempty (LambdaN D ω k n) :=
    ⟨⟨fun _ => false, (ConstrG9.nonempty_fProd D ω hω k hk n hn).some⟩⟩
  have hΛ : (0 : ℝ) < Nat.card (LambdaN D ω k n) := by exact_mod_cast Nat.card_pos
  -- the bad points of every element of `𝔉_{j,n}` number `2^j`, and I1 bounds each
  have hmemj : ∀ a : ↥(fSet D ω k ((t.rev : ℕ) + 1) n), (a : BinaryTreeAut) ∈ fSet D ω k j n := by
    intro a
    have hm := a.2
    obtain ⟨g, hg⟩ : ∃ g, g = (a : BinaryTreeAut) := ⟨_, rfl⟩
    rw [← hg] at hm ⊢
    rw [hidx] at hm
    exact hm
  have hcount : ∀ a : ↥(fSet D ω k ((t.rev : ℕ) + 1) n),
      {x | x ∈ orbitOne ω ∧ ((a : BinaryTreeAut), x) ∉ letterGerms ω .b}.ncard = 2 ^ j := by
    intro a
    have hm := hmemj a
    unfold fSet at hm
    rw [if_pos ⟨by simpa [hjdef] using hj, by omega, hjn'⟩] at hm
    obtain ⟨v, hv, hv', he⟩ := hm
    rw [he]
    exact (H6 n hn j hj1 (by simpa [hjdef] using hj) (by omega) hjn' v hv hv').2.1
  have hbound : ∀ a : ↥(fSet D ω k ((t.rev : ℕ) + 1) n), ∀ y : orbitOne ω,
      ((a : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b →
      ∑ p : LambdaN D ω k n, F p y ≤ ENNReal.ofReal ((Nat.card (LambdaN D ω k n) : ℝ) * B) :=
    fun a y hbad => sum_I1C_le D ω hω k hk C hC hI1 n hn j hj1 (by simpa [hjdef] using hj) (by omega) hjn' f
      hf0 hfa _ (hmemj a) y y.2 hbad
  have hfin : ∀ i : Fin n, Fintype ↥(fSet D ω k ((i : ℕ) + 1) n) := fun i =>
    (ConstrG9.fSet_finite D ω k _ n).fintype
  have hnei : ∀ i : Fin n, Nonempty ↥(fSet D ω k ((i : ℕ) + 1) n) := fun i =>
    (ConstrG9.fSet_nonempty D ω hω k hk n hn ((i : ℕ) + 1) (by omega)).to_subtype
  have htr : ((t.rev : Fin n) : ℕ) < j := by simp [Fin.val_rev]; omega
  set M : ℝ≥0∞ := (Fintype.card ↥(fSet D ω k ((t.rev : ℕ) + 1) n) : ℝ≥0∞) with hM
  have hcond : ∀ y : orbitOne ω,
      ∑ p : LambdaN D ω k n, (if ((p.2 t.rev : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b then
        F p y else 0) =
      ∑ a : ↥(fSet D ω k ((t.rev : ℕ) + 1) n),
        (if ((a : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b then
          M⁻¹ * ∑ p : LambdaN D ω k n, F p y else 0) := by
    intro y
    have h3 := sum_indicator_coord (A := Fin n → Bool)
      (β := fun i : Fin n => ↥(fSet D ω k ((i : ℕ) + 1) n)) t.rev
      (fun a => ((a : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b) (fun p => F p y)
      (fun e γ b => by
        simp only [hFdef, hPr]
        rw [prod_update_eqC D ω k n j e γ t.rev htr b])
    convert h3 using 3
    all_goals first
      | exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)
      | (simp only [hM, Fintype.card_eq_nat_card]
         congr 1
         exact congrArg (fun u => Finset.sum u fun p => F p y) (by ext; simp))
  have hM0 : M ≠ 0 := by
    simp only [hM, ne_eq, Nat.cast_eq_zero]
    exact Fintype.card_ne_zero
  have hMT : M ≠ ⊤ := ENNReal.natCast_ne_top _
  have hB0 : 0 ≤ B := by
    have := hf0 (2 ^ (j + 2 * k n)) (by positivity)
    have := hf0 (2 ^ (n + D)) (by positivity)
    positivity
  have hcB : c * ENNReal.ofReal ((Nat.card (LambdaN D ω k n) : ℝ) * B) = ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc _ ≤ ∑ p : LambdaN D ω k n, c * ∑' y : orbitOne ω,
        (if ((p.2 t.rev : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b then F p y else 0) := by
        refine Finset.sum_le_sum fun p _ => ?_
        split_ifs
        · simp only [hP p, hFdef, le_refl]
        · exact zero_le
    _ = c * ∑' y : orbitOne ω, ∑ p : LambdaN D ω k n,
        (if ((p.2 t.rev : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b then F p y else 0) := by
        rw [← Finset.mul_sum, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = c * ∑' y : orbitOne ω, ∑ a : ↥(fSet D ω k ((t.rev : ℕ) + 1) n),
        (if ((a : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b then
          M⁻¹ * ∑ p : LambdaN D ω k n, F p y else 0) := by
        congr 1; exact tsum_congr hcond
    _ = c * ∑ a : ↥(fSet D ω k ((t.rev : ℕ) + 1) n), M⁻¹ * ∑' y : orbitOne ω,
        (if ((a : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b then
          ∑ p : LambdaN D ω k n, F p y else 0) := by
        congr 1
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun y => ?_
        split_ifs <;> simp
    _ ≤ c * ∑ a : ↥(fSet D ω k ((t.rev : ℕ) + 1) n), M⁻¹ * ∑' y : orbitOne ω,
        (if ((a : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b then
          ENNReal.ofReal ((Nat.card (LambdaN D ω k n) : ℝ) * B) else 0) := by
        gcongr with a _ y
        split_ifs with h
        · exact le_rfl
        · exact hbound a y h
    _ = c * ∑ a : ↥(fSet D ω k ((t.rev : ℕ) + 1) n), M⁻¹ *
        ((2 ^ j : ℕ) * ENNReal.ofReal ((Nat.card (LambdaN D ω k n) : ℝ) * B)) := by
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [tsum_bad_constC ω _ (2 ^ j) (hcount a) (by positivity)]
    _ = (2 : ℝ≥0∞) ^ j * ENNReal.ofReal B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcard : ((Fintype.card ↥(fSet D ω k ((t.rev : ℕ) + 1) n) : ℕ) : ℝ≥0∞) = M := by
          simp only [hM, Fintype.card_eq_nat_card]
        rw [hcard, ← mul_assoc M, ENNReal.mul_inv_cancel hM0 hMT, one_mul, ← mul_assoc,
          mul_comm c, mul_assoc, hcB]
        push_cast
        rfl


/-- The products of I1 clause 2 do not involve the coordinate `j - 1` of `γ`. -/
theorem prod_update_eq_invC (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n j : ℕ) (e : Fin n → Bool)
    (γ : fProd D ω k n) (i₀ : Fin n) (hi₀ : j ≤ (i₀ : ℕ) + 1) (b : ↥(fSet D ω k (i₀ + 1) n)) :
    ((((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).reverse.map
      fun i => ((Function.update γ i₀ b) i : Garrido.BinaryTreeAut) ^ (e i).toNat)).prod =
    ((((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).reverse.map
      fun i => (γ i : Garrido.BinaryTreeAut) ^ (e i).toNat)).prod := by
  congr 1
  apply List.map_congr_left
  intro i hi
  have hne : i ≠ i₀ := by
    intro h; subst h
    simp only [List.mem_reverse, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq] at hi
    omega
  rw [Function.update_of_ne hne]

/-- Lemma 7.21 clause 2 (from `I1Bound … C`) in `[0, ∞]`. -/
theorem sum_I1C_inv_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (C : ℝ) (hC : 0 ≤ C) (hI1 : OpI1.I1Bound D ω k C) (n : ℕ) (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : ω (j - 1) = 2) (hjn : n < j + k n) (hjn' : j ≤ n) (f : ℝ → ℝ)
    (hf0 : ∀ s, 0 ≤ s → 0 ≤ f s) (hfa : AntitoneOn f (Set.Ici 0)) [Fintype (LambdaN D ω k n)]
    (g : BinaryTreeAut) (hg : g ∈ fSet D ω k j n) (y : Ray) (hy : y ∈ orbitOne ω)
    (hbad : (g⁻¹, y) ∉ letterGerms ω .b) :
    ∑ p : LambdaN D ω k n, ENNReal.ofReal (f (schreierDist ω oneRay (y <•
      ((((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).reverse.map
        fun i => (p.2 i : Garrido.BinaryTreeAut) ^ (p.1 i).toNat)).prod))) ≤
      ENNReal.ofReal ((Nat.card (LambdaN D ω k n) : ℝ) * (f (2 ^ (j + 2 * k n)) +
          C * (f (2 ^ n) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
            (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n))))) := by
  unfold fSet at hg
  rw [if_pos ⟨hj, hjn, hjn'⟩] at hg
  obtain ⟨v, hv, hv', rfl⟩ := hg
  set fh : ℝ → ℝ := fun s => f (max s 0) with hfh
  have hfh_anti : Antitone fh := fun a b hab =>
    hfa (Set.mem_Ici.mpr (le_max_right _ _)) (Set.mem_Ici.mpr (le_max_right _ _))
      (max_le_max hab le_rfl)
  have hfh0 : ∀ s, 0 ≤ fh s := fun s => hf0 _ (le_max_right _ _)
  have hfe : ∀ s, 0 ≤ s → fh s = f s := fun s hs => by simp only [hfh, max_eq_left hs]
  have h1 := (hI1 n hn j hj1 hj hjn hjn' v hv hv' fh hfh_anti hfh0).2 y hy hbad
  rw [tsum_fintype] at h1
  simp only [hfe _ (Nat.cast_nonneg _), hfe _ (by positivity : (0 : ℝ) ≤ 2 ^ (j + 2 * k n)),
    hfe _ (by positivity : (0 : ℝ) ≤ 2 ^ n)] at h1
  have hne : Nonempty (LambdaN D ω k n) :=
    ⟨⟨fun _ => false, (ConstrG9.nonempty_fProd D ω hω k hk n hn).some⟩⟩
  have hΛ : (0 : ℝ) < Nat.card (LambdaN D ω k n) := by exact_mod_cast Nat.card_pos
  rw [div_le_iff₀ hΛ] at h1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => hf0 _ (Nat.cast_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (by linarith)

open Classical in
/-- Item 6 for `υ̌_n`: the `t`-term of `sum_mass_upsilonCheck_le` for `j = t + 1`, `n < j + k_n`,
`ω_{j-1} = 2`, with `F(r) = [r ≠ o] f(d(o, r))`, is at most
`2^j (f(2^{j+2k_n}) + C f(2^n) k_n^{1+2/D} 2^{-(j+2k_n-n)/D})`. -/
theorem term_highInvC_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (C : ℝ) (hC : 0 ≤ C) (hI1 : OpI1.I1Bound D ω k C) (n : ℕ) (hn : D ∣ n) (t : Fin n) (hjn : n < (t : ℕ) + 1 + k n)
    (hj : ω t = 2) (f : ℝ → ℝ) (hf0 : ∀ s, 0 ≤ s → 0 ≤ f s)
    (hfa : AntitoneOn f (Set.Ici 0)) [Fintype (LambdaN D ω k n)] :
    ∑ p : LambdaN D ω k n, (if p.1 t = true then
        ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ)) *
          ∑' y : orbitOne ω, (if (((p.2 t : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b then
            ENNReal.ofReal (if (y : Ray) <• (prodTakeInv D ω k n p t)⁻¹ ≠ oneRay then
              f (schreierDist ω oneRay ((y : Ray) <• (prodTakeInv D ω k n p t)⁻¹)) else 0)
            else 0) else 0) ≤
      2 ^ ((t : ℕ) + 1) * ENNReal.ofReal (f (2 ^ ((t : ℕ) + 1 + 2 * k n)) +
          C * (f (2 ^ n) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
            (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((((t : ℕ) + 1 : ℕ) : ℝ) + 2 * k n - n)))) := by
  classical
  have ht : (t : ℕ) < n := t.2
  set j := (t : ℕ) + 1 with hjdef
  have hj1 : 1 ≤ j := by omega
  have hjn' : j ≤ n := by omega
  set B : ℝ := f (2 ^ (j + 2 * k n)) + C * (f (2 ^ n) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
    (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n))) with hB
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (Nat.card (LambdaN D ω k n) : ℝ))
  set Pr : LambdaN D ω k n → BinaryTreeAut := fun p =>
    ((((List.finRange n).filter fun i : Fin n => i.val + 2 ≤ j).reverse.map
      fun i => (p.2 i : Garrido.BinaryTreeAut) ^ (p.1 i).toNat)).prod with hPr
  have hP : ∀ p, (prodTakeInv D ω k n p t)⁻¹ = Pr p := fun p => by
    rw [prodTakeInv_inv_eq D ω hω k hk n hn p t ht.le, ← List.map_reverse]
  set F : LambdaN D ω k n → orbitOne ω → ℝ≥0∞ := fun p y =>
    ENNReal.ofReal (if (y : Ray) <• Pr p ≠ oneRay then
      f (schreierDist ω oneRay ((y : Ray) <• Pr p)) else 0) with hFdef
  obtain ⟨c6, hc6, C6, hC6, H6⟩ :=
    setOf_not_mem_letterGerms_gTilde_eq_and_ncard_and_schreierDist D ω hω k hk
  have hne : Nonempty (LambdaN D ω k n) :=
    ⟨⟨fun _ => false, (ConstrG9.nonempty_fProd D ω hω k hk n hn).some⟩⟩
  have hΛ : (0 : ℝ) < Nat.card (LambdaN D ω k n) := by exact_mod_cast Nat.card_pos
  have hcount : ∀ a : ↥(fSet D ω k j n),
      {x | x ∈ orbitOne ω ∧ (((a : BinaryTreeAut))⁻¹, x) ∉ letterGerms ω .b}.ncard = 2 ^ j := by
    intro a
    have hG : (a : BinaryTreeAut) ∈ grigorchuk ω :=
      ConstrG9.fSet_subset D ω hω k hk n hn j hj1 a.2
    rw [ncard_bad_inv ω hG]
    obtain ⟨g, hg⟩ : ∃ g, g = (a : BinaryTreeAut) := ⟨_, rfl⟩
    have hm : g ∈ fSet D ω k j n := hg ▸ a.2
    rw [← hg]
    unfold fSet at hm
    rw [if_pos ⟨by simpa [hjdef] using hj, by omega, hjn'⟩] at hm
    obtain ⟨v, hv, hv', he⟩ := hm
    rw [he]
    exact (H6 n hn j hj1 (by simpa [hjdef] using hj) (by omega) hjn' v hv hv').2.1
  have hbound : ∀ a : ↥(fSet D ω k j n), ∀ y : orbitOne ω,
      (((a : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b →
      ∑ p : LambdaN D ω k n, F p y ≤ ENNReal.ofReal ((Nat.card (LambdaN D ω k n) : ℝ) * B) := by
    intro a y hbad
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) (sum_I1C_inv_le D ω hω k hk C hC hI1 n hn j hj1
      (by simpa [hjdef] using hj) (by omega) hjn' f hf0 hfa _ a.2 y y.2 hbad)
    simp only [hFdef]
    refine ENNReal.ofReal_le_ofReal ?_
    split_ifs
    · exact le_rfl
    · exact hf0 _ (Nat.cast_nonneg _)
  have hfin : ∀ i : Fin n, Fintype ↥(fSet D ω k ((i : ℕ) + 1) n) := fun i =>
    (ConstrG9.fSet_finite D ω k _ n).fintype
  have hnei : ∀ i : Fin n, Nonempty ↥(fSet D ω k ((i : ℕ) + 1) n) := fun i =>
    (ConstrG9.fSet_nonempty D ω hω k hk n hn ((i : ℕ) + 1) (by omega)).to_subtype
  set M : ℝ≥0∞ := (Fintype.card ↥(fSet D ω k j n) : ℝ≥0∞) with hM
  have hcond : ∀ y : orbitOne ω,
      ∑ p : LambdaN D ω k n, (if (((p.2 t : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b then
        F p y else 0) =
      ∑ a : ↥(fSet D ω k j n),
        (if (((a : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b then
          M⁻¹ * ∑ p : LambdaN D ω k n, F p y else 0) := by
    intro y
    have h3 := sum_indicator_coord (A := Fin n → Bool)
      (β := fun i : Fin n => ↥(fSet D ω k ((i : ℕ) + 1) n)) t
      (fun a => (((a : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b) (fun p => F p y)
      (fun e γ b => by
        simp only [hFdef, hPr]
        rw [prod_update_eq_invC D ω k n j e γ t (by omega) b])
    convert h3 using 3
    all_goals first
      | exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)
      | (simp only [hM, Fintype.card_eq_nat_card]
         congr 1
         exact congrArg (fun u => Finset.sum u fun p => F p y) (by ext; simp))
  have hM0 : M ≠ 0 := by
    simp only [hM, ne_eq, Nat.cast_eq_zero]
    exact Fintype.card_ne_zero
  have hMT : M ≠ ⊤ := ENNReal.natCast_ne_top _
  have hB0 : 0 ≤ B := by
    have := hf0 (2 ^ (j + 2 * k n)) (by positivity)
    have := hf0 (2 ^ n) (by positivity)
    positivity
  have hcB : c * ENNReal.ofReal ((Nat.card (LambdaN D ω k n) : ℝ) * B) = ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc _ ≤ ∑ p : LambdaN D ω k n, c * ∑' y : orbitOne ω,
        (if (((p.2 t : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b then F p y else 0) := by
        refine Finset.sum_le_sum fun p _ => ?_
        split_ifs
        · simp only [hP p, hFdef, le_refl]
        · exact zero_le
    _ = c * ∑' y : orbitOne ω, ∑ p : LambdaN D ω k n,
        (if (((p.2 t : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b then F p y else 0) := by
        rw [← Finset.mul_sum, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = c * ∑' y : orbitOne ω, ∑ a : ↥(fSet D ω k j n),
        (if (((a : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b then
          M⁻¹ * ∑ p : LambdaN D ω k n, F p y else 0) := by
        congr 1; exact tsum_congr hcond
    _ = c * ∑ a : ↥(fSet D ω k j n), M⁻¹ * ∑' y : orbitOne ω,
        (if (((a : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b then
          ∑ p : LambdaN D ω k n, F p y else 0) := by
        congr 1
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun y => ?_
        split_ifs <;> simp
    _ ≤ c * ∑ a : ↥(fSet D ω k j n), M⁻¹ * ∑' y : orbitOne ω,
        (if (((a : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b then
          ENNReal.ofReal ((Nat.card (LambdaN D ω k n) : ℝ) * B) else 0) := by
        gcongr with a _ y
        split_ifs with h
        · exact le_rfl
        · exact hbound a y h
    _ = c * ∑ a : ↥(fSet D ω k j n), M⁻¹ *
        ((2 ^ j : ℕ) * ENNReal.ofReal ((Nat.card (LambdaN D ω k n) : ℝ) * B)) := by
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [tsum_bad_constC ω _ (2 ^ j) (hcount a) (by positivity)]
    _ = (2 : ℝ≥0∞) ^ j * ENNReal.ofReal B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hcard : ((Fintype.card ↥(fSet D ω k j n) : ℕ) : ℝ≥0∞) = M := by
          simp only [hM, Fintype.card_eq_nat_card]
        rw [hcard, ← mul_assoc M, ENNReal.mul_inv_cancel hM0 hMT, one_mul, ← mul_assoc,
          mul_comm c, mul_assoc, hcB]
        push_cast
        rfl


end OpI2

end ErschlerZheng
end

section
/-!
# G8 (pp. 55–56, corrected): uniform digits — counting tools (prover 3, in progress)

Each factor `F_i` keeps the first `i + 1` digits and flips digit `i + 1` exactly when its exponent
bit is set. Then the first digits of `x·F_s(e_s)⋯F_{s+L-1}(e_{s+L-1})` beyond position `s` are a
bijective function of the bits `e_s, …, e_{s+L-1}`: flipping the last bit toggles the last digit and
changes nothing before it (`card_forward`).
-/

open scoped RightActions
open Garrido

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ErschlerZheng

namespace P3G8Dev

open RayBasic

/-- Half of a set is cut out by a predicate that an involution toggles. -/
theorem two_mul_card {α : Type*} [Fintype α] (σ : α ≃ α) (A B : α → Prop) [DecidablePred A]
    [DecidablePred B] (hA : ∀ a, A (σ a) ↔ A a) (hB : ∀ a, B (σ a) ↔ ¬ B a) :
    2 * Fintype.card {a // A a ∧ B a} = Fintype.card {a // A a} := by
  have h1 : Fintype.card {a // A a ∧ B a} = Fintype.card {a // A a ∧ ¬ B a} :=
    Fintype.card_congr (σ.subtypeEquiv fun a => by
      constructor
      · rintro ⟨ha, hb⟩; exact ⟨(hA a).mpr ha, (hB a).not.mpr (not_not.mpr hb)⟩
      · rintro ⟨ha, hb⟩; exact ⟨(hA a).mp ha, by simpa using (hB a).not.mp hb⟩)
  have h2 : Fintype.card {a // A a} =
      Fintype.card {a // A a ∧ B a} + Fintype.card {a // A a ∧ ¬ B a} := by
    simp only [Fintype.card_subtype]
    rw [← Finset.filter_filter, ← Finset.filter_filter,
      Finset.card_filter_add_card_filter_not]
  omega

/-! ### One factor flips one digit -/

open GrigBasic

section Inst

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k)
  (n : ℕ) (hn : D ∣ n)

include hω hk hn

end Inst

/-! ### Clause 1, for fixed `x` and `γ` -/

section Clause1

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k)
  (n : ℕ) (hn : D ∣ n)

include hω hk hn

end Clause1

/-! ### Counting `B_j` -/

theorem card_odd (m c : ℕ) :
    2 * Fintype.card {f : Fin (m + 1) → Bool // Odd (c + (List.ofFn f).count true)} = 2 ^ (m + 1) := by
  classical
  let σ : (Fin (m + 1) → Bool) ≃ (Fin (m + 1) → Bool) :=
    { toFun := fun f => Function.update f 0 (!f 0)
      invFun := fun f => Function.update f 0 (!f 0)
      left_inv := fun f => by funext i; by_cases hi : i = 0 <;> simp [hi]
      right_inv := fun f => by funext i; by_cases hi : i = 0 <;> simp [hi] }
  have hcount : ∀ f : Fin (m + 1) → Bool, (List.ofFn (σ f)).count true =
      (List.ofFn fun i : Fin m => f i.succ).count true + (if f 0 then 0 else 1) ∧
      (List.ofFn f).count true =
      (List.ofFn fun i : Fin m => f i.succ).count true + (if f 0 then 1 else 0) := by
    intro f
    have hs : ∀ i : Fin m, σ f i.succ = f i.succ := fun i => by
      simp [σ, Function.update, Fin.succ_ne_zero]
    constructor
    · rw [List.ofFn_succ, List.count_cons]
      simp only [hs]
      cases h : f 0 <;> simp [σ, h]
    · rw [List.ofFn_succ, List.count_cons]
      cases h : f 0 <;> simp [h]
  have := two_mul_card σ (fun _ => True) (fun f => Odd (c + (List.ofFn f).count true))
    (fun _ => Iff.rfl) (fun f => by
      obtain ⟨h1, h2⟩ := hcount f
      rw [h1, h2]
      cases f 0 <;> simp [← add_assoc, Nat.odd_add_one])
  simp only [true_and] at this
  rw [this, Fintype.card_subtype_true, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem rayPrefix_prepend' (p : List Bool) : rayPrefix (prepend p oneRay) p.length = p :=
  rayPrefix_prepend p oneRay

section Bj

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j : ℕ) (hj1 : 1 ≤ j) (hj : ω (j - 1) = 2)

/-- `B_j`. -/
abbrev Bset : Set Ray := {x | x ∈ orbitOne ω ∧ (seqG ω j, x) ∉ letterGerms ω .b}

include hω hj1 hj

theorem mem_Bset_iff (x : Ray) : x ∈ Bset ω j ↔
    ∃ p : List Bool, p.length = j + 1 ∧ Odd (j + 1 + p.count true) ∧ x = prepend p oneRay := by
  rw [show Bset ω j = _ from setOf_not_mem_letterGerms_seqG_eq D ω hω j hj1 hj]
  rfl

/-- `B_j ≃ {f : {0,1}^{j+1} odd}`. -/
noncomputable def eB : Bset ω j ≃ {f : Fin (j + 1) → Bool // Odd (j + 1 + (List.ofFn f).count true)} where
  toFun x := ⟨fun i => x.1 i, by
    obtain ⟨p, hp, hodd, hx⟩ := (mem_Bset_iff D ω hω j hj1 hj x.1).mp x.2
    have : (List.ofFn fun i : Fin (j + 1) => x.1 i) = p := by
      rw [show (List.ofFn fun i : Fin (j + 1) => x.1 i) = rayPrefix x.1 (j + 1) from rfl, hx,
        ← hp, rayPrefix_prepend']
    rw [this]; exact hodd⟩
  invFun f := ⟨prepend (List.ofFn f.1) oneRay, (mem_Bset_iff D ω hω j hj1 hj _).mpr
    ⟨List.ofFn f.1, by simp, f.2, rfl⟩⟩
  left_inv x := by
    obtain ⟨p, hp, hodd, hx⟩ := (mem_Bset_iff D ω hω j hj1 hj x.1).mp x.2
    apply Subtype.ext
    simp only
    have : (List.ofFn fun i : Fin (j + 1) => x.1 i) = p := by
      rw [show (List.ofFn fun i : Fin (j + 1) => x.1 i) = rayPrefix x.1 (j + 1) from rfl, hx,
        ← hp, rayPrefix_prepend']
    rw [this, hx]
  right_inv f := by
    apply Subtype.ext
    funext i
    show prepend (List.ofFn f.1) oneRay i = f.1 i
    unfold prepend
    rw [dif_pos (by simp [i.2])]
    simp only [List.getElem_ofFn]

theorem card_Bset [Fintype (Bset ω j)] : Fintype.card (Bset ω j) = 2 ^ j := by
  classical
  have h := card_odd j (j + 1)
  rw [Fintype.card_congr (eB D ω hω j hj1 hj)]
  rw [pow_succ] at h
  omega

end Bj

/-! ### `Λ_n` is finite and non-empty -/

/-! ### Clause 1 -/

/-! ### Backward products -/

/-! ### `B'_j = B_j · g_j` -/

theorem ray_inv_smul (y : Ray) (h : BinaryTreeAut) : (y <• h⁻¹) <• h = y := by
  simpa using GermBase.rsmul_inv_smul y h⁻¹

section Bj'

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j : ℕ) (hj1 : 1 ≤ j) (hj : ω (j - 1) = 2)

/-- `B'_j`. -/
abbrev Bset' : Set Ray := {x | x ∈ orbitOne ω ∧ ((seqG ω j)⁻¹, x) ∉ letterGerms ω .b}

include hω hj1 hj

theorem seqG_mem : seqG ω j ∈ grigorchuk ω :=
  (Subgroup.mem_inf.mp ((seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω).1 j
    hj1).1).1

/-- `B'_j ≃ B_j`, `y ↦ y·g_j⁻¹`. -/
noncomputable def eB' : Bset' ω j ≃ Bset ω j where
  toFun y := ⟨y.1 <• (seqG ω j)⁻¹, by
    refine ⟨GermBase.orbit_smul y.2.1 (inv_mem (seqG_mem D ω hω j hj1 hj)), fun h => y.2.2 ?_⟩
    have hG := P3P712Dev.goodAt_of_mem ω (seqG_mem D ω hω j hj1 hj)
      (GermBase.orbit_smul y.2.1 (inv_mem (seqG_mem D ω hω j hj1 hj))) h
    have := P3P712Dev.goodAt_inv ω hG
    rw [ray_inv_smul] at this
    exact P3P712Dev.mem_of_goodAt ω (inv_mem (seqG_mem D ω hω j hj1 hj)) y.2.1 this⟩
  invFun x := ⟨x.1 <• seqG ω j, by
    refine ⟨GermBase.orbit_smul x.2.1 (seqG_mem D ω hω j hj1 hj), fun h => x.2.2 ?_⟩
    have hG := P3P712Dev.goodAt_of_mem ω (inv_mem (seqG_mem D ω hω j hj1 hj))
      (GermBase.orbit_smul x.2.1 (seqG_mem D ω hω j hj1 hj)) h
    have := P3P712Dev.goodAt_inv ω hG
    rw [inv_inv, GermBase.rsmul_inv_smul] at this
    exact P3P712Dev.mem_of_goodAt ω (seqG_mem D ω hω j hj1 hj) x.2.1 this⟩
  left_inv y := by apply Subtype.ext; exact ray_inv_smul _ _
  right_inv x := by apply Subtype.ext; exact GermBase.rsmul_inv_smul _ _

end Bj'

/-! ### Clauses 2 and 3, for fixed `y` and `γ` -/


section Clause23

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k)
  (n : ℕ) (hn : D ∣ n)

include hω hk hn

end Clause23

/-! ### Assembly -/

end P3G8Dev

end ErschlerZheng
end

section
/-!
# `|B_j| = |B'_j| = 2^j` in the fixed-factor bounds (prover 7)

Prover 3's `P3G8.card_Bset`, `card_Bset'` (via the G7 stub) turn `term_low_le` and `term_lowInv_le`
into `2^j·(2/2ⁿ)·Σ_{m<n} 2^m f(2^m)` and `2^j/2^{j-1}·(Σ_{m<j-1} 2^m f(2^m) + f(1))`.
-/

namespace ErschlerZheng

namespace P7Dev

theorem finite_Bset (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : ω (j - 1) = 2) : Finite ↥(P3G8Dev.Bset ω j) :=
  Finite.of_equiv _ (P3G8Dev.eB D ω hω j hj1 hj).symm

theorem natCard_Bset (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : ω (j - 1) = 2) : Nat.card ↥(P3G8Dev.Bset ω j) = 2 ^ j := by
  have := finite_Bset D ω hω j hj1 hj
  have : Fintype ↥(P3G8Dev.Bset ω j) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, P3G8Dev.card_Bset D ω hω j hj1 hj]

theorem natCard_Bset' (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : ω (j - 1) = 2) : Nat.card ↥(P3G8Dev.Bset' ω j) = 2 ^ j := by
  rw [Nat.card_congr (P3G8Dev.eB' D ω hω j hj1 hj), natCard_Bset D ω hω j hj1 hj]

end P7Dev

end ErschlerZheng
end

section
/-!
# Proposition 7.12 (corrected) from Lemma 7.21 with a constant (OpI2)

`prop712_of_I1Bound`: if `OpI1.I1Bound D ω k C` holds for some `C` (Lemma 7.21 with the factor `C`
on its second term), then the milestone `tsum_f_mul_mass_upsilon_and_upsilonCheck_not_mem_letterGerms_le`
holds (its statement, verbatim, after the extra hypothesis).

The route (p. 53–56, prover 7's pieces): the union bound and the change of variables
(`P7Dev.sum_mass_upsilon_le`, `sum_mass_upsilonCheck_le`), then per level `j`:
* `ω_{j-1} ≠ 2`: no bad point (`term_zeroC`, `term_zero_invC`);
* `j + k_n ⩽ n`: the fixed factor `g_j^{±1}` (`P7Dev.term_low_le`, `term_lowInv_le`, `|B_j| = 2^j`);
* `n < j + k_n`: Lemma 7.21 with its constant (`OpI2.term_highC_le`, `term_highInvC_le`);
and the sums over `j` (`OpI2.sumU_le`, `sumV_le`). The `υ̌_n` half uses `F(r) = [r ≠ o] f(d(o, r))`.
Summability: finite supports (`summable_orbit_sumC`, a copy of prover 7's `summable_orbit_sum`).
-/

open scoped RightActions ENNReal
open Garrido

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ErschlerZheng

namespace OpI2

open P7Dev GrigBasic P3P712Dev P3U0Dev

/-! ### Finite supports (copies of `P7Dev.finite_support_upsilon`, `summable_orbit_sum`) -/

theorem finite_support_upsilonC (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) :
    {h | upsilon D ω k n h ≠ 0}.Finite := by
  by_cases hfin : Finite (LambdaN D ω k n)
  · refine (Set.finite_range (theta D ω k n)).subset fun h hh => ?_
    by_contra hr
    apply hh
    unfold upsilon
    have : IsEmpty {p // theta D ω k n p = h} := ⟨fun ⟨p, hp⟩ => hr ⟨p, hp⟩⟩
    rw [Nat.card_of_isEmpty]; simp
  · have : Infinite (LambdaN D ω k n) := not_finite_iff_infinite.mp hfin
    have h0 : Nat.card (LambdaN D ω k n) = 0 := Nat.card_eq_zero_of_infinite
    refine Set.finite_empty.subset fun h hh => hh ?_
    simp [upsilon]

theorem finite_support_upsilonCheckC (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) :
    {h | upsilonCheck D ω k n h ≠ 0}.Finite := by
  refine ((finite_support_upsilonC D ω k n).image fun h => h⁻¹).subset fun h hh => ?_
  exact ⟨h⁻¹, hh, inv_inv h⟩

theorem summable_orbit_sumC (ω : ℕ → Fin 3) (ν : BinaryTreeAut → ℝ)
    (hν : {h | ν h ≠ 0}.Finite) (F : ℝ → ℝ) (Y : Set Ray) (hY : Y ⊆ orbitOne ω) :
    Summable fun x : Y => F (schreierDist ω oneRay x) *
      mass (fun g : grigorchuk ω => ν g)
        {g | ((g : BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b} := by
  set T : Set BinaryTreeAut := {h | ν h ≠ 0} ∩ grigorchuk ω
  have hT : T.Finite := hν.subset Set.inter_subset_left
  set Bad : Set Ray := ⋃ h ∈ T, {x | ¬ GoodAt ω h x}
  have hBad : Bad.Finite := hT.biUnion fun h hh => finite_not_goodAt ω hh.2
  refine summable_of_hasFiniteSupport ((hBad.preimage Subtype.val_injective.injOn).subset ?_)
  intro x hx
  by_contra hxB
  apply hx
  show _ * _ = 0
  rw [mul_eq_zero]; right
  unfold mass
  convert tsum_zero with g
  by_cases hg : ν (g : BinaryTreeAut) = 0
  · simp [Set.indicator, hg]
  · have hgood : GoodAt ω g x := by
      by_contra hng
      exact hxB (Set.mem_biUnion (x := (g : BinaryTreeAut)) ⟨hg, g.2⟩ hng)
    have hmem := mem_of_goodAt ω g.2 (hY x.2) hgood
    simp [Set.indicator, hmem]

theorem mass_nonneg_of (ω : ℕ → Fin 3) (ν : BinaryTreeAut → ℝ) (hν : ∀ h, 0 ≤ ν h)
    (A : Set (grigorchuk ω)) : 0 ≤ mass (fun g : grigorchuk ω => ν g) A :=
  tsum_nonneg fun g => Set.indicator_nonneg (s := A) (f := fun g : grigorchuk ω => ν g)
    (fun g _ => hν g) g

theorem upsilon_nonnegC (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (n : ℕ) (g : BinaryTreeAut) :
    0 ≤ upsilon D ω k n g :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ### Levels with `ω_{j-1} ≠ 2` (prover 7's `term_zero`, with a summand depending on `p`) -/

open Classical in
theorem term_zeroC (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (n : ℕ) (t : Fin n) (hj : ω t.rev ≠ 2) (F : LambdaN D ω k n → Ray → ℝ≥0∞) (c : ℝ≥0∞)
    [Fintype (LambdaN D ω k n)] :
    ∑ p : LambdaN D ω k n, (if p.1 t.rev = true then c *
        ∑' y : orbitOne ω, (if ((p.2 t.rev : BinaryTreeAut), (y : Ray)) ∉ letterGerms ω .b then
          F p y else 0) else 0) = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  have hγ : (p.2 t.rev : BinaryTreeAut) = seqG ω ((t.rev : ℕ) + 1) := by
    have hmem := (p.2 t.rev).2
    obtain ⟨a, ha⟩ : ∃ a, a = (p.2 t.rev : BinaryTreeAut) := ⟨_, rfl⟩
    rw [← ha] at hmem ⊢
    unfold fSet at hmem
    rw [if_neg (by simp only [Nat.add_sub_cancel]; exact fun h => hj h.1)] at hmem
    exact hmem
  have hgood := ((seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω).2.2
    ((t.rev : ℕ) + 1) (by omega)).1 (by simpa using hj)
  split_ifs
  · rw [ENNReal.tsum_eq_zero.mpr fun y => by
      rw [if_neg (by rw [hγ]; exact not_not.mpr (hgood y y.2))], mul_zero]
  · rfl

open Classical in
theorem term_zero_invC (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (n : ℕ) (t : Fin n) (hj : ω t ≠ 2) (F : LambdaN D ω k n → Ray → ℝ≥0∞) (c : ℝ≥0∞)
    [Fintype (LambdaN D ω k n)] :
    ∑ p : LambdaN D ω k n, (if p.1 t = true then c *
        ∑' y : orbitOne ω, (if (((p.2 t : BinaryTreeAut))⁻¹, (y : Ray)) ∉ letterGerms ω .b then
          F p y else 0) else 0) = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  have hγ : (p.2 t : BinaryTreeAut) = seqG ω ((t : ℕ) + 1) := by
    have hmem := (p.2 t).2
    obtain ⟨a, ha⟩ : ∃ a, a = (p.2 t : BinaryTreeAut) := ⟨_, rfl⟩
    rw [← ha] at hmem ⊢
    unfold fSet at hmem
    rw [if_neg (by simp only [Nat.add_sub_cancel]; exact fun h => hj h.1)] at hmem
    exact hmem
  have hgood := ((seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω hω).2.2
    ((t : ℕ) + 1) (by omega)).1 (by simpa using hj)
  have hG : seqG ω ((t : ℕ) + 1) ∈ grigorchuk ω :=
    (Subgroup.mem_inf.mp (((seqG_mem_levelStab_and_isCubeIndependent_and_mem_letterGerms D ω
      hω).1 ((t : ℕ) + 1) (by omega)).1)).1
  have hempty : ∀ y : orbitOne ω, ((seqG ω ((t : ℕ) + 1))⁻¹, (y : Ray)) ∈ letterGerms ω .b := by
    intro y
    by_contra hbad
    have hmem : (y : Ray) ∈ {x | x ∈ orbitOne ω ∧ ((seqG ω ((t : ℕ) + 1))⁻¹, x) ∉
        letterGerms ω .b} := ⟨y.2, hbad⟩
    rw [bad_inv_eq_image ω hG] at hmem
    obtain ⟨z, ⟨hz, hzbad⟩, -⟩ := hmem
    exact hzbad (hgood z hz)
  split_ifs
  · rw [ENNReal.tsum_eq_zero.mpr fun y => by
      rw [if_neg (by rw [hγ]; exact not_not.mpr (hempty y))], mul_zero]
  · rfl

/-! ### Reindexing the levels -/

theorem sum_fin_rev_le (n : ℕ) (G : ℕ → ℝ) (hG : ∀ j, 0 ≤ G j) :
    ∑ t : Fin n, G (n - t) ≤ ∑ j ∈ Finset.range (n + 1), G j := by
  rw [Fin.sum_univ_eq_sum_range (fun i => G (n - i)) n, Finset.sum_range_succ']
  have e : ∑ i ∈ Finset.range n, G (n - i) = ∑ i ∈ Finset.range n, G (i + 1) := by
    rw [← Finset.sum_range_reflect (fun i => G (i + 1)) n]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.mp hi
    show G (n - i) = G (n - 1 - i + 1)
    congr 1; omega
  rw [e]; linarith [hG 0]

theorem sum_fin_succ_le (n : ℕ) (G : ℕ → ℝ) (hG : ∀ j, 0 ≤ G j) :
    ∑ t : Fin n, G (t + 1) ≤ ∑ j ∈ Finset.range (n + 1), G j := by
  rw [Fin.sum_univ_eq_sum_range (fun i => G (i + 1)) n, Finset.sum_range_succ']
  linarith [hG 0]

theorem ofReal_sum_two_pow (f : ℝ → ℝ) (hf0 : ∀ s, 0 ≤ s → 0 ≤ f s) (N : ℕ) :
    ∑ m ∈ Finset.range N, (2 : ℝ≥0∞) ^ m * ENNReal.ofReal (f (2 ^ m)) =
      ENNReal.ofReal (∑ m ∈ Finset.range N, (2 : ℝ) ^ m * f (2 ^ m)) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => mul_nonneg (by positivity) (hf0 _ (by positivity)))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

theorem two_pow_eq_ofReal (m : ℕ) : (2 : ℝ≥0∞) ^ m = ENNReal.ofReal ((2 : ℝ) ^ m) := by
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-! ### The two halves in `[0, ∞]` -/

section

variable (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k)
  (D' : ℝ) (hD' : (D : ℝ) < D') (C₁ : ℝ) (hC₁ : 0 ≤ C₁) (hI1 : OpI1.I1Bound D ω k C₁) (M : ℝ)
  (hM : ∀ k : ℕ, (k : ℝ) ^ (1 + 2 / (D : ℝ)) *
      (2 : ℝ) ^ (-(2 * (1 / (D : ℝ) - 1 / D') * k)) ≤ M)
  (f : ℝ → ℝ) (hf0 : ∀ s, 0 ≤ s → 0 ≤ f s) (hfa : AntitoneOn f (Set.Ici 0))
  (hfr : ∀ s, 1 ≤ s → (2 : ℝ) ^ (-1 / D') ≤ f (2 * s) / f s) (n : ℕ) (hn : D ∣ n)

include hω hk hD' hC₁ hI1 hM hf0 hfa hfr hn

open Classical in
/-- The `υ_n` half: `Σ_x f(d(o, x)) υ_n{bad at x} ⩽ (5K + C₁ K_S) 2^n f(2^{n+2k_n})` in `[0, ∞]`. -/
theorem upsilon_ennreal_le [Fintype (LambdaN D ω k n)] :
    ∑' x : orbitOne ω, ENNReal.ofReal (f (schreierDist ω oneRay x) *
        mass (fun g : grigorchuk ω => upsilon D ω k n g)
          {g | ((g : BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) ≤
      ENNReal.ofReal ((4 * kK D' + kK D' + C₁ * kS D M) * (2 ^ n * f (2 ^ (n + 2 * k n)))) := by
  have hD3 : 3 ≤ D := by obtain ⟨m, hm, -⟩ := hω 0; omega
  have hsum := sum_mass_upsilon_le D ω hω k hk n hn (fun r => f (schreierDist ω oneRay r))
    (fun r => hf0 _ (Nat.cast_nonneg _))
  refine hsum.trans ?_
  rcases Nat.eq_zero_or_pos n with h0 | hn1
  · subst h0
    simp
  have hDk : D ≤ k n := Nat.le_of_dvd (hk.2 n hn1 hn).1 (hk.2 n hn1 hn).2
  set Gu : ℕ → ℝ := fun j => (if j + k n ≤ n then (2 : ℝ) ^ j * (2 / 2 ^ n) *
        ∑ m ∈ Finset.range n, (2 : ℝ) ^ m * f (2 ^ m) else 0) +
      (2 : ℝ) ^ j * (f (2 ^ (j + 2 * k n)) + C₁ * (f (2 ^ (n + D)) *
        (k n : ℝ) ^ (1 + 2 / (D : ℝ)) * (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n))))
    with hGu
  have hnn : ∀ m : ℕ, 0 ≤ (2 : ℝ) ^ m * f (2 ^ m) := fun m =>
    mul_nonneg (by positivity) (hf0 _ (by positivity))
  have hhigh0 : ∀ j : ℕ, 0 ≤ (2 : ℝ) ^ j * (f (2 ^ (j + 2 * k n)) + C₁ * (f (2 ^ (n + D)) *
        (k n : ℝ) ^ (1 + 2 / (D : ℝ)) * (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n)))) := by
    intro j
    have := hf0 (2 ^ (j + 2 * k n)) (by positivity)
    have := hf0 (2 ^ (n + D)) (by positivity)
    positivity
  have hGu0 : ∀ j, 0 ≤ Gu j := by
    intro j
    simp only [hGu]
    have h1 : 0 ≤ (if j + k n ≤ n then (2 : ℝ) ^ j * (2 / 2 ^ n) *
        ∑ m ∈ Finset.range n, (2 : ℝ) ^ m * f (2 ^ m) else 0) := by
      split_ifs
      · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => hnn m)
      · exact le_rfl
    exact add_nonneg h1 (hhigh0 j)
  refine (Finset.sum_le_sum (g := fun t : Fin n => ENNReal.ofReal (Gu (n - t)))
    fun t _ => ?_).trans ?_
  · have ht := t.2
    have hrev : ((t.rev : Fin n) : ℕ) = n - t - 1 := by simp [Fin.val_rev]; omega
    by_cases hω2 : ω t.rev = 2
    · have hj : ω (n - t - 1) = 2 := by rw [← hrev]; exact hω2
      by_cases hlow : n - t + k n ≤ n
      · have hfinB := finite_Bset D ω hω (n - t) (by omega) hj
        let _ : Fintype ↥{x | x ∈ orbitOne ω ∧ (seqG ω (n - t), x) ∉ letterGerms ω .b} :=
          Fintype.ofFinite _
        refine (term_low_le D ω hω k hk n hn t hlow hj f hf0 hfa).trans ?_
        have hc : (Nat.card ↥{x | x ∈ orbitOne ω ∧ (seqG ω (n - t), x) ∉ letterGerms ω .b} : ℝ) =
            2 ^ (n - t) := by
          exact_mod_cast natCard_Bset D ω hω (n - t) (by omega) hj
        rw [ofReal_sum_two_pow f hf0 n, ← ENNReal.ofReal_mul (by rw [hc]; positivity), hc]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [hGu, if_pos hlow]
        linarith [hhigh0 (n - t)]
      · have hjn : n < n - t + k n := by omega
        refine (term_highC_le D ω hω k hk C₁ hC₁ hI1 n hn t hjn hj f hf0 hfa).trans ?_
        rw [two_pow_eq_ofReal, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [hGu, if_neg hlow, zero_add]
        exact le_rfl
    · exact (term_zeroC D ω hω k n t hω2 (fun p (y : Ray) =>
        ENNReal.ofReal (f (schreierDist ω oneRay (y <• (prodTake D ω k n p t)⁻¹)))) _).le.trans
        zero_le
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => hGu0 _)]
    refine ENNReal.ofReal_le_ofReal ((sum_fin_rev_le n Gu hGu0).trans ?_)
    exact sumU_le hf0 hfr D (by omega) hD' M hM C₁ hC₁ n (k n) hDk

open Classical in
/-- The `υ̌_n` half, with `F(r) = [r ≠ o] f(d(o, r))`:
`Σ_x F(x) υ̌_n{bad at x} ⩽ (4K² + K + C₁ K_S) 2^n f(2^{n+2k_n})` in `[0, ∞]`. -/
theorem upsilonCheck_ennreal_le [Fintype (LambdaN D ω k n)] :
    ∑' x : orbitOne ω, ENNReal.ofReal ((if (x : Ray) ≠ oneRay then
        f (schreierDist ω oneRay x) else 0) *
        mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
          {g | ((g : BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) ≤
      ENNReal.ofReal ((4 * kK D' ^ 2 + kK D' + C₁ * kS D M) *
        (2 ^ n * f (2 ^ (n + 2 * k n)))) := by
  have hD3 : 3 ≤ D := by obtain ⟨m, hm, -⟩ := hω 0; omega
  have hD'1 : 1 < D' := by
    have : (3 : ℝ) ≤ D := by exact_mod_cast hD3
    linarith
  have hsum := sum_mass_upsilonCheck_le D ω hω k hk n hn
    (fun r => if r ≠ oneRay then f (schreierDist ω oneRay r) else 0)
    (fun r => by split_ifs; exacts [hf0 _ (Nat.cast_nonneg _), le_rfl])
  refine hsum.trans ?_
  set Gv : ℕ → ℝ := fun j => (if j + k n ≤ n then 4 * kK D' * ((2 : ℝ) ^ j * f (2 ^ j)) else 0) +
      (2 : ℝ) ^ j * (f (2 ^ (j + 2 * k n)) + C₁ * (f (2 ^ n) * (k n : ℝ) ^ (1 + 2 / (D : ℝ)) *
        (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n)))) with hGv
  have hK := (kK_pos hD'1).le
  have hhigh0 : ∀ j : ℕ, 0 ≤ (2 : ℝ) ^ j * (f (2 ^ (j + 2 * k n)) + C₁ * (f (2 ^ n) *
        (k n : ℝ) ^ (1 + 2 / (D : ℝ)) * (2 : ℝ) ^ (-(1 / (D : ℝ)) * ((j : ℝ) + 2 * k n - n)))) := by
    intro j
    have := hf0 (2 ^ (j + 2 * k n)) (by positivity)
    have := hf0 (2 ^ n) (by positivity)
    positivity
  have hGv0 : ∀ j, 0 ≤ Gv j := by
    intro j
    simp only [hGv]
    have h1 : 0 ≤ (if j + k n ≤ n then 4 * kK D' * ((2 : ℝ) ^ j * f (2 ^ j)) else 0) := by
      split_ifs
      · have := hf0 (2 ^ j) (by positivity)
        positivity
      · exact le_rfl
    exact add_nonneg h1 (hhigh0 j)
  refine (Finset.sum_le_sum (g := fun t : Fin n => ENNReal.ofReal (Gv (t + 1)))
    fun t _ => ?_).trans ?_
  · have ht := t.2
    by_cases hω2 : ω t = 2
    · by_cases hlow : (t : ℕ) + 1 + k n ≤ n
      · have hj : ω ((t : ℕ) + 1 - 1) = 2 := by simpa using hω2
        have hfinB : Finite ↥(P3G8Dev.Bset' ω ((t : ℕ) + 1)) :=
          Finite.of_equiv _ (P3G8Dev.eB' D ω hω ((t : ℕ) + 1) (by omega) hj).symm
            (h := finite_Bset D ω hω ((t : ℕ) + 1) (by omega) hj)
        let _ : Fintype ↥{x | x ∈ orbitOne ω ∧
            ((seqG ω ((t : ℕ) + 1))⁻¹, x) ∉ letterGerms ω .b} := Fintype.ofFinite _
        refine (term_lowInv_le D ω hω k hk n hn t hlow hω2 f hf0 hfa).trans ?_
        have hc : (Nat.card ↥{x | x ∈ orbitOne ω ∧
            ((seqG ω ((t : ℕ) + 1))⁻¹, x) ∉ letterGerms ω .b} : ℝ) = 2 ^ ((t : ℕ) + 1) := by
          exact_mod_cast natCard_Bset' D ω hω ((t : ℕ) + 1) (by omega) hj
        have hS0 : 0 ≤ ∑ m ∈ Finset.range ((t : ℕ) + 1 - 1), (2 : ℝ) ^ m * f (2 ^ m) :=
          Finset.sum_nonneg fun m _ => mul_nonneg (by positivity) (hf0 _ (by positivity))
        have hf1 := hf0 1 zero_le_one
        rw [ofReal_sum_two_pow f hf0, ← ENNReal.ofReal_add hS0 hf1,
          ← ENNReal.ofReal_mul (by rw [hc]; positivity), hc]
        refine ENNReal.ofReal_le_ofReal ?_
        have hr := lowInv_real hf0 hfr hD'1 ((t : ℕ) + 1) (by omega)
        have e : (2 : ℝ) ^ ((t : ℕ) + 1) * (1 / 2 ^ ((t : ℕ) + 1 - 1)) = 2 := by
          rw [Nat.add_sub_cancel, pow_succ]
          field_simp
        rw [e]
        simp only [hGv, if_pos hlow]
        linarith [hhigh0 ((t : ℕ) + 1)]
      · have hjn : n < (t : ℕ) + 1 + k n := by omega
        refine (term_highInvC_le D ω hω k hk C₁ hC₁ hI1 n hn t hjn hω2 f hf0 hfa).trans ?_
        rw [two_pow_eq_ofReal, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [hGv, if_neg hlow, zero_add]
        exact le_rfl
    · exact (term_zero_invC D ω hω k n t hω2 (fun p (y : Ray) =>
        ENNReal.ofReal (if y <• (prodTakeInv D ω k n p t)⁻¹ ≠ oneRay then
          f (schreierDist ω oneRay (y <• (prodTakeInv D ω k n p t)⁻¹)) else 0)) _).le.trans
        zero_le
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => hGv0 _)]
    refine ENNReal.ofReal_le_ofReal ((sum_fin_succ_le n Gv hGv0).trans ?_)
    exact sumV_le hf0 hfr D hD3 hD' M hM C₁ hC₁ n (k n)

end

/-! ### Proposition 7.12 (corrected) from `∃ C, I1Bound D ω k C` -/

/-- **Proposition 7.12 (corrected)**, assuming Lemma 7.21 with some constant on its second term. -/
theorem prop712_of_I1Bound (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) (D' : ℝ) (hD' : (D : ℝ) < D')
    (hI1 : ∃ C, OpI1.I1Bound D ω k C) :
    ∃ C : ℝ, ∀ f : ℝ → ℝ, (∀ s, 0 ≤ s → 0 ≤ f s) → AntitoneOn f (Set.Ici 0) →
      (∀ s, 1 ≤ s → (2 : ℝ) ^ (-1 / D') ≤ f (2 * s) / f s) → ∀ n, D ∣ n →
        Summable (fun x : orbitOne ω => f (schreierDist ω oneRay x) *
            mass (fun g : grigorchuk ω => upsilon D ω k n g)
              {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) ∧
        ∑' x : orbitOne ω, f (schreierDist ω oneRay x) *
            mass (fun g : grigorchuk ω => upsilon D ω k n g)
              {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b} ≤
          C * 2 ^ n * f (2 ^ (n + 2 * k n)) ∧
        Summable (fun x : ↥(orbitOne ω \ {oneRay}) => f (schreierDist ω oneRay x) *
            mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
              {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) ∧
        ∑' x : ↥(orbitOne ω \ {oneRay}), f (schreierDist ω oneRay x) *
            mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
              {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b} ≤
          C * 2 ^ n * f (2 ^ (n + 2 * k n)) := by
  classical
  obtain ⟨C₀, hC₀⟩ := hI1
  set C₁ := max C₀ 0 with hC₁def
  have hC₁ : 0 ≤ C₁ := le_max_right _ _
  have hI1 : OpI1.I1Bound D ω k C₁ := I1Bound_mono hC₀ (le_max_left _ _)
  have hD3 : 3 ≤ D := by obtain ⟨m, hm, -⟩ := hω 0; omega
  have hD1 : 1 < D := by omega
  have hD'1 : 1 < D' := by
    have : (3 : ℝ) ≤ D := by exact_mod_cast hD3
    linarith
  obtain ⟨M, hM0, hM⟩ := exists_M D hD1 hD'
  have hK := (kK_pos hD'1).le
  have hS := kS_nonneg D hD1 M hM0
  refine ⟨4 * kK D' ^ 2 + 4 * kK D' + kK D' + C₁ * kS D M, ?_⟩
  intro f hf0 hfa hfr n hn
  have : Finite (fProd D ω k n) := ConstrG9.finite_fProd D ω k n
  let _ : Fintype (LambdaN D ω k n) := Fintype.ofFinite _
  have hF0 : 0 ≤ f (2 ^ (n + 2 * k n)) := hf0 _ (by positivity)
  have hCU : (4 * kK D' + kK D' + C₁ * kS D M) * (2 ^ n * f (2 ^ (n + 2 * k n))) ≤
      (4 * kK D' ^ 2 + 4 * kK D' + kK D' + C₁ * kS D M) * 2 ^ n * f (2 ^ (n + 2 * k n)) := by
    rw [mul_assoc]
    gcongr
    nlinarith
  have hCV : (4 * kK D' ^ 2 + kK D' + C₁ * kS D M) * (2 ^ n * f (2 ^ (n + 2 * k n))) ≤
      (4 * kK D' ^ 2 + 4 * kK D' + kK D' + C₁ * kS D M) * 2 ^ n * f (2 ^ (n + 2 * k n)) := by
    rw [mul_assoc]
    gcongr
    nlinarith
  have hRU : 0 ≤ (4 * kK D' + kK D' + C₁ * kS D M) * (2 ^ n * f (2 ^ (n + 2 * k n))) := by
    positivity
  have hRV : 0 ≤ (4 * kK D' ^ 2 + kK D' + C₁ * kS D M) * (2 ^ n * f (2 ^ (n + 2 * k n))) := by
    positivity
  -- the `υ_n` half
  have hsU := summable_orbit_sumC ω (upsilon D ω k n) (finite_support_upsilonC D ω k n) f
    (orbitOne ω) le_rfl
  have hnU : ∀ x : orbitOne ω, 0 ≤ f (schreierDist ω oneRay x) *
      mass (fun g : grigorchuk ω => upsilon D ω k n g)
        {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b} := fun x =>
    mul_nonneg (hf0 _ (Nat.cast_nonneg _))
      (mass_nonneg_of ω _ (upsilon_nonnegC D ω k n) _)
  have hU := upsilon_ennreal_le D ω hω k hk D' hD' C₁ hC₁ hI1 M hM f hf0 hfa hfr n hn
  rw [← ENNReal.ofReal_tsum_of_nonneg hnU hsU, ENNReal.ofReal_le_ofReal_iff hRU] at hU
  -- the `υ̌_n` half
  have hsV := summable_orbit_sumC ω (upsilonCheck D ω k n) (finite_support_upsilonCheckC D ω k n)
    f (orbitOne ω \ {oneRay}) Set.sdiff_subset
  have hnV : ∀ x : ↥(orbitOne ω \ {oneRay}), 0 ≤ f (schreierDist ω oneRay x) *
      mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
        {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b} := fun x =>
    mul_nonneg (hf0 _ (Nat.cast_nonneg _))
      (mass_nonneg_of ω _ (fun h => upsilon_nonnegC D ω k n h⁻¹) _)
  have hV := upsilonCheck_ennreal_le D ω hω k hk D' hD' C₁ hC₁ hI1 M hM f hf0 hfa hfr n hn
  have hincl : ∑' x : ↥(orbitOne ω \ {oneRay}), ENNReal.ofReal (f (schreierDist ω oneRay x) *
      mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
        {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) ≤
      ∑' x : orbitOne ω, ENNReal.ofReal ((if (x : Ray) ≠ oneRay then
        f (schreierDist ω oneRay x) else 0) *
        mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
          {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) := by
    set ι : ↥(orbitOne ω \ {oneRay}) → orbitOne ω := fun x => ⟨x.1, x.2.1⟩ with hι
    have hinj : Function.Injective ι := fun a b h =>
      Subtype.ext (show (a : Ray) = b from congrArg (fun z : orbitOne ω => (z : Ray)) h)
    refine le_trans (le_of_eq ?_) (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun x : orbitOne ω => ENNReal.ofReal ((if (x : Ray) ≠ oneRay then
        f (schreierDist ω oneRay x) else 0) *
        mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
          {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b})))
    refine tsum_congr fun x => ?_
    have hx : (x : Ray) ≠ oneRay := x.2.2
    simp only [hι, if_pos hx]
  have hV' := hincl.trans hV
  rw [← ENNReal.ofReal_tsum_of_nonneg hnV hsV, ENNReal.ofReal_le_ofReal_iff hRV] at hV'
  exact ⟨hsU, hU.trans hCU, hsV, hV'.trans hCV⟩

end OpI2

end ErschlerZheng
end

section
/-!
# Proposition 7.12 (corrected), through Lemma 7.21 with the constant 16

The standalone `ErschlerZheng.tsum_f_schreierDist_div_card_le_sixteen` (Lemma 7.21 with the factor
16 on its second term, through its stub) is the case `C = 16` of `OpI1.I1Bound`;
`OpI2.prop712_of_I1Bound` then gives the milestone. Lemma 7.21 as printed (`C = 1`) is not needed.
-/

open scoped RightActions

namespace ErschlerZheng

/-- Lemma 7.21 with the constant 16 is `I1Bound D ω k 16`. -/
theorem OpI2.I1Bound_sixteen_of_stub (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω) (k : ℕ → ℕ)
    (hk : IsAdmissibleSeq D k) : OpI1.I1Bound D ω k 16 :=
  fun n hn j hj1 hj hjn hjn' v hv hv' f hf hf0 =>
    tsum_f_schreierDist_div_card_le_sixteen D ω hω k hk n hn j hj1 hj hjn hjn' v hv hv' f hf hf0

end ErschlerZheng
end

section
open scoped RightActions
open ErschlerZheng
theorem solution (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (D' : ℝ) (hD' : (D : ℝ) < D') :
    ∃ C : ℝ, ∀ f : ℝ → ℝ, (∀ s, 0 ≤ s → 0 ≤ f s) → AntitoneOn f (Set.Ici 0) →
      (∀ s, 1 ≤ s → (2 : ℝ) ^ (-1 / D') ≤ f (2 * s) / f s) → ∀ n, D ∣ n →
        Summable (fun x : orbitOne ω => f (schreierDist ω oneRay x) *
            mass (fun g : grigorchuk ω => upsilon D ω k n g)
              {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) ∧
        ∑' x : orbitOne ω, f (schreierDist ω oneRay x) *
            mass (fun g : grigorchuk ω => upsilon D ω k n g)
              {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b} ≤
          C * 2 ^ n * f (2 ^ (n + 2 * k n)) ∧
        Summable (fun x : ↥(orbitOne ω \ {oneRay}) => f (schreierDist ω oneRay x) *
            mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
              {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) ∧
        ∑' x : ↥(orbitOne ω \ {oneRay}), f (schreierDist ω oneRay x) *
            mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
              {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b} ≤
          C * 2 ^ n * f (2 ^ (n + 2 * k n)) :=
  OpI2.prop712_of_I1Bound D ω hω k hk D' hD' ⟨16, OpI2.I1Bound_sixteen_of_stub D ω hω k hk⟩
end
