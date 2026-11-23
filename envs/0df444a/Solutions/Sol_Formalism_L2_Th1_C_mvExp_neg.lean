-- Prove2me | solution 1 for Formalism.L2.Th1.C.mvExp_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:24.768502+00:00
-- url     : https://prove2.me/submissions/8f717a4b-ed48-412f-bdb0-5bf95234ce0a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Theorems.Thm_Formalism_L2_Th1_C_coeff_pow_eq_zero_of_cc
import Theorems.Thm_Formalism_L2_Th1_C_coeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_zero
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
open Finset
namespace Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] {σ : Type}
private theorem finsupp_degree_add (a b : σ →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  first
  | exact map_add Finsupp.degree a b
  | exact Finsupp.degree_add a b
  | simp [Finsupp.degree_add]
private theorem coeff_mul_eq_zero_of_degree_lt_add' {A B : MvPowerSeries σ K} {a b : ℕ}
    (hA : ∀ m : σ →₀ ℕ, m.degree < a → MvPowerSeries.coeff m A = 0)
    (hB : ∀ m : σ →₀ ℕ, m.degree < b → MvPowerSeries.coeff m B = 0)
    (n : σ →₀ ℕ) (hn : n.degree < a + b) : MvPowerSeries.coeff n (A * B) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  first
  | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  | simp only [Finset.mem_antidiagonal] at hp
  | simp at hp
  have hd : p.1.degree + p.2.degree = n.degree := by rw [← finsupp_degree_add, hp]
  by_cases h1 : p.1.degree < a
  · rw [hA _ h1, zero_mul]
  · rw [hB _ (by omega), mul_zero]
private theorem coeff_mvExp_eq_coeff_trunc_sum {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (N : ℕ) (m : σ →₀ ℕ) (hm : m.degree < N) :
    MvPowerSeries.coeff m (mvExp f) =
      MvPowerSeries.coeff m (∑ k ∈ Finset.range N, ((k.factorial : K))⁻¹ • f ^ k) := by
  rw [coeff_mvExp hf hm, map_sum]
  simp only [map_smul, smul_eq_mul]
private theorem coeff_mul_congr_of_degree_lt {A A' B B' : MvPowerSeries σ K} {N : ℕ}
    (hA : ∀ m : σ →₀ ℕ, m.degree < N → MvPowerSeries.coeff m A = MvPowerSeries.coeff m A')
    (hB : ∀ m : σ →₀ ℕ, m.degree < N → MvPowerSeries.coeff m B = MvPowerSeries.coeff m B')
    (n : σ →₀ ℕ) (hn : n.degree < N) :
    MvPowerSeries.coeff n (A * B) = MvPowerSeries.coeff n (A' * B') := by
  classical
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  first
  | rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  | simp only [Finset.mem_antidiagonal] at hp
  | simp at hp
  have hd : p.1.degree + p.2.degree = n.degree := by rw [← finsupp_degree_add, hp]
  rw [hA _ (by omega), hB _ (by omega)]
private theorem inv_factorial_mul_choose_eq {k m : ℕ} (h : m ≤ k) :
    ((k.factorial : K))⁻¹ * (k.choose m : K) =
      ((m.factorial : K))⁻¹ * (((k - m).factorial : K))⁻¹ := by
  have e := Nat.choose_mul_factorial_mul_factorial h
  have h1 : (m.factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have h2 : ((k - m).factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : (k.choose m : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos h).ne'
  rw [← e]
  push_cast
  first
  | (field_simp; done)
  | (field_simp; ring)
private theorem mvExp_add_binomial_series_coefficients {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) : mvExp (f + g) = mvExp f * mvExp g := by
  classical
  have hfg : MvPowerSeries.constantCoeff (f + g) = 0 := by simp [hf, hg]
  ext n
  rw [coeff_mvExp hfg (Nat.lt_succ_self n.degree),
    coeff_mul_congr_of_degree_lt (coeff_mvExp_eq_coeff_trunc_sum hf (n.degree + 1)) (coeff_mvExp_eq_coeff_trunc_sum hg (n.degree + 1)) n
      (Nat.lt_succ_self _),
    Finset.sum_mul_sum, map_sum]
  simp only [map_sum, smul_mul_smul_comm, map_smul, smul_eq_mul]
  have hL : ∀ k ∈ Finset.range (n.degree + 1),
      ((k.factorial : K))⁻¹ * MvPowerSeries.coeff n ((f + g) ^ k) =
        ∑ m ∈ Finset.range (k + 1), ((m.factorial : K))⁻¹ * (((k - m).factorial : K))⁻¹ *
          MvPowerSeries.coeff n (f ^ m * g ^ (k - m)) := by
    intro k _
    rw [add_pow, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := K)) (k.choose m),
      mul_comm _ (MvPowerSeries.C _), MvPowerSeries.coeff_C_mul, ← mul_assoc, inv_factorial_mul_choose_eq hmk]
  rw [Finset.sum_congr rfl hL]
  have hflip := Finset.sum_range_diag_flip (n.degree + 1) (fun a b =>
    ((a.factorial : K))⁻¹ * ((b.factorial : K))⁻¹ * MvPowerSeries.coeff n (f ^ a * g ^ b))
  try simp only at hflip
  rw [hflip]
  refine Finset.sum_congr rfl fun i hi => ?_
  refine Finset.sum_subset (fun j hj => Finset.mem_range.2
    (lt_of_lt_of_le (Finset.mem_range.1 hj) (Nat.sub_le _ _))) ?_
  intro j hj hj'
  simp only [Finset.mem_range, not_lt] at hi hj hj'
  rw [coeff_mul_eq_zero_of_degree_lt_add' (fun m hm => coeff_pow_eq_zero_of_cc hf hm)
    (fun m hm => coeff_pow_eq_zero_of_cc hg hm) n (by omega), mul_zero]
end Formalism.L2.Th1.C
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.Th1.C
theorem _root_.solution {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    mvExp (-f) * mvExp f = 1 := by
  have h := mvExp_add_binomial_series_coefficients (f := -f) (g := f) (by simp [hf]) hf
  rw [neg_add_cancel, mvExp_zero] at h
  exact h.symm
end Formalism.L2.Th1.C
