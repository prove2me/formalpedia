-- Prove2me | solution 1 for Formalism.L2.Th1.C.mvExp_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:36:40.879645+00:00
-- url     : https://prove2.me/submissions/718c8c76-50e7-4ab5-9193-f39771d71f13

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Theorems.Thm_Formalism_L2_Th1_C_coeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_mul_neg
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_sub_mul
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
private theorem eq_zero_of_mvExp_eq_one {h : MvPowerSeries σ K} (hh : MvPowerSeries.constantCoeff h = 0)
    (he : mvExp h = 1) : h = 0 := by
  classical
  by_contra hne
  have hex : ∃ d : ℕ, ∃ m : σ →₀ ℕ, m.degree = d ∧ MvPowerSeries.coeff m h ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (MvPowerSeries.ext fun m => by simpa using hall _ m rfl)
  obtain ⟨m, hmd, hm⟩ := Nat.find_spec hex
  have hmin : ∀ m' : σ →₀ ℕ, m'.degree < Nat.find hex → MvPowerSeries.coeff m' h = 0 := by
    intro m' hm'
    by_contra hc
    exact Nat.find_min hex hm' ⟨m', rfl, hc⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hm
    simpa using hh
  have hd1 : 1 ≤ Nat.find hex := by
    rw [← hmd]
    by_contra h0
    exact hm0 ((Finsupp.degree_eq_zero_iff m).1 (by omega))
  have he' := congrArg (MvPowerSeries.coeff m) he
  rw [coeff_mvExp hh (show m.degree < Nat.find hex + 1 by omega), Finset.sum_eq_single 1] at he'
  · simp [hm0, MvPowerSeries.coeff_one] at he'
    exact hm he'
  · intro k _ hk1
    rcases Nat.lt_or_gt_of_ne hk1 with hk0 | hk2
    · have hk : k = 0 := by omega
      subst hk
      simp [hm0, MvPowerSeries.coeff_one]
    · rw [coeff_pow_eq_zero_of_degree_lt_mul hmin k m (by rw [hmd]; nlinarith), mul_zero]
  · intro h1
    exact absurd (Finset.mem_range.2 (by omega)) h1
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
theorem _root_.solution {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) (h : mvExp f = mvExp g) : f = g := by
  have h1 := mvExp_sub_mul hf hg
  rw [h] at h1
  have h2 : mvExp (f - g) = 1 := by
    calc mvExp (f - g) = mvExp (f - g) * mvExp g * mvExp (-g) := by
          rw [mul_assoc, mvExp_mul_neg hg, mul_one]
      _ = 1 := by rw [h1, mvExp_mul_neg hg]
  exact sub_eq_zero.1 (eq_zero_of_mvExp_eq_one (by simp [hf, hg]) h2)
end Formalism.L2.Th1.C
