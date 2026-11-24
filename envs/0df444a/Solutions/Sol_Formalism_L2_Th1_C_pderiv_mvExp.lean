-- Prove2me | solution 1 for Formalism.L2.Th1.C.pderiv_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:23:09.426401+00:00
-- url     : https://prove2.me/submissions/d77674ef-df81-42a5-9a37-57ae7dc93a86

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Theorems.Thm_Formalism_L2_Th1_C_coeff_mvExp
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
theorem _root_.solution {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) (i : σ) :
    MvPowerSeries.pderiv K i (mvExp f) = MvPowerSeries.pderiv K i f * mvExp f := by
  classical
  ext n
  have hE : MvPowerSeries.pderiv K i
      (∑ k ∈ Finset.range (n.degree + 1 + 1), ((k.factorial : K))⁻¹ • f ^ k) =
      MvPowerSeries.pderiv K i f *
        ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : K))⁻¹ • f ^ k := by
    rw [map_sum, Finset.mul_sum, Finset.sum_range_succ' _ (n.degree + 1)]
    have h0 : MvPowerSeries.pderiv K i (((Nat.factorial 0 : K))⁻¹ • f ^ 0) = 0 := by simp
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : (((k + 1).factorial : K))⁻¹ * ((k + 1 : ℕ) : K) = ((k.factorial : K))⁻¹ := by
      rw [Nat.factorial_succ]
      push_cast
      have : (k.factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
      field_simp
    rw [Derivation.map_smul, Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, ← Nat.cast_smul_eq_nsmul K,
      smul_smul, hc, mul_smul_comm, mul_comm (MvPowerSeries.pderiv K i f)]
  rw [MvPowerSeries.coeff_pderiv, coeff_mvExp_eq_coeff_trunc_sum hf (n.degree + 1 + 1) _ ?_,
    ← MvPowerSeries.coeff_pderiv, hE]
  · exact coeff_mul_congr_of_degree_lt (fun _ _ => rfl) (fun m hm => (coeff_mvExp_eq_coeff_trunc_sum hf _ m hm).symm) n
      (Nat.lt_succ_self _)
  · rw [finsupp_degree_add, Finsupp.degree_single]
    omega
end Formalism.L2.Th1.C
