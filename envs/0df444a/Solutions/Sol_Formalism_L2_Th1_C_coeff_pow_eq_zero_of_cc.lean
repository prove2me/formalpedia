-- Prove2me | solution 1 for Formalism.L2.Th1.C.coeff_pow_eq_zero_of_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:02.899813+00:00
-- url     : https://prove2.me/submissions/204ef340-7c3e-4b93-a698-f721fe8fe703

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
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
private theorem coeff_pow_eq_zero_of_degree_lt_mul {A : MvPowerSeries σ K} {a : ℕ}
    (hA : ∀ m : σ →₀ ℕ, m.degree < a → MvPowerSeries.coeff m A = 0) (k : ℕ) :
    ∀ n : σ →₀ ℕ, n.degree < k * a → MvPowerSeries.coeff n (A ^ k) = 0 := by
  induction k with
  | zero => intro n hn; simp at hn
  | succ k ih =>
    intro n hn
    rw [pow_succ']
    have e : (k + 1) * a = a + k * a := by ring
    exact coeff_mul_eq_zero_of_degree_lt_add' hA ih n (by rw [e] at hn; exact hn)
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
theorem _root_.solution {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    {n : σ →₀ ℕ} {k : ℕ} (h : n.degree < k) : MvPowerSeries.coeff n (f ^ k) = 0 := by
  have h1 : ∀ m : σ →₀ ℕ, m.degree < 1 → MvPowerSeries.coeff m f = 0 := by
    intro m hm
    have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 (by omega)
    subst hm0
    simpa using hf
  exact coeff_pow_eq_zero_of_degree_lt_mul h1 k n (by simpa using h)
end Formalism.L2.Th1.C
