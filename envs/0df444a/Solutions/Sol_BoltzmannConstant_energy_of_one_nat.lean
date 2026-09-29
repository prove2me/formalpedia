-- Prove2me | solution 1 for BoltzmannConstant.energy_of_one_nat
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:21:35.84119+00:00
-- url     : https://prove2.me/submissions/437dcda3-2646-434d-a7c9-b6ad3dd060d9

import Mathlib
import Definitions.Def_boltzmann_si_basics

open BoltzmannConstant

theorem W2p_BoltzmannConstant_kB_pos : (0 : ℝ) < BoltzmannConstant.kB := by
  unfold BoltzmannConstant.kB; norm_num

theorem W2p_BoltzmannConstant_kB_in_eV_per_kelvin :
    |kB / elemCharge - 8.617333262e-5| < 1e-13 := by
  unfold kB elemCharge
  rw [abs_lt]; constructor <;> norm_num

theorem W2p_BoltzmannConstant_thermal_voltage_at_300K :
    |thermalVoltage 300 - 0.02585| < 1e-5 := by
  unfold thermalVoltage kB elemCharge
  rw [abs_lt]; constructor <;> norm_num

theorem W2p_BoltzmannConstant_energy_of_one_nat (T S₁ S₂ : ℝ) (h : S₂ / kB = S₁ / kB + 1) :
    T * (S₂ - S₁) = kB * T := by
  have hk : kB ≠ 0 := W2p_BoltzmannConstant_kB_pos.ne'
  have e : S₂ - S₁ = (S₂ / kB - S₁ / kB) * kB := by
    rw [sub_mul, div_mul_cancel₀ _ hk, div_mul_cancel₀ _ hk]
  rw [e, h]; ring

theorem W2p_BoltzmannConstant_rescaled_entropy_eq_shannon {ι : Type*} (s : Finset ι)
    (p : ι → ℝ) :
    gibbsEntropy s p / kB = shannonEntropy s p := by
  have hk : kB ≠ 0 := W2p_BoltzmannConstant_kB_pos.ne'
  unfold gibbsEntropy shannonEntropy
  rw [neg_mul, neg_div, mul_div_cancel_left₀ _ hk]

theorem W2p_BoltzmannConstant_gibbs_entropy_uniform_eq_boltzmann_entropy {ι : Type*}
    (s : Finset ι) (W : ℕ)
    (hW : s.card = W) (hW0 : 0 < W) :
    gibbsEntropy s (fun _ => 1 / (W : ℝ)) = boltzmannEntropy W := by
  unfold gibbsEntropy boltzmannEntropy
  have hW' : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hW0.ne'
  rw [Finset.sum_const, nsmul_eq_mul, hW, one_div, Real.log_inv, ← mul_assoc (W : ℝ),
    mul_inv_cancel₀ hW']
  ring

theorem W2p_BoltzmannConstant_boltzmann_prob_sum_eq_one {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty)
    (T : ℝ) (hT : 0 < T) (E : ι → ℝ) :
    ∑ i ∈ s, boltzmannProb s T E i = 1 := by
  unfold boltzmannProb
  rw [← Finset.sum_div]
  have hZ : 0 < partitionFunction s T E := by
    unfold partitionFunction
    exact Finset.sum_pos (fun i _ => by unfold boltzmannWeight; exact Real.exp_pos _) hs
  rw [show (∑ i ∈ s, boltzmannWeight T (E i)) = partitionFunction s T E from rfl]
  exact div_self hZ.ne'

theorem W2p_BoltzmannConstant_rms_speed_ratio (T m₁ m₂ : ℝ) (hT : 0 < T) (hm₁ : 0 < m₁)
    (hm₂ : 0 < m₂) :
    Real.sqrt (3 * kB * T / m₁) / Real.sqrt (3 * kB * T / m₂) = Real.sqrt (m₂ / m₁) := by
  have hk := W2p_BoltzmannConstant_kB_pos
  rw [← Real.sqrt_div (by positivity)]
  congr 1
  field_simp <;> ring

theorem W2p_BoltzmannConstant_equipartition_per_degree_of_freedom
    (m T vx2 vy2 vz2 msq : ℝ) (hsum : msq = vx2 + vy2 + vz2)
    (hxy : vx2 = vy2) (hyz : vy2 = vz2)
    (hmean : m * msq / 2 = 3 / 2 * (kB * T)) :
    m * vx2 / 2 = kB * T / 2 := by
  rw [hsum, ← hyz, ← hxy] at hmean
  linear_combination hmean / 3

theorem W2p_BoltzmannConstant_ideal_gas_law_per_molecule (n N p V T : ℝ) (hN : N = n * NA) :
    p * V = n * R * T ↔ p * V = N * kB * T := by
  have e : n * R * T = N * kB * T := by rw [hN]; unfold R; ring
  rw [e]

theorem W2p_BoltzmannConstant_mean_kinetic_energy_eq_three_halves_kT
    (N m V p T msq : ℝ) (hN : 0 < N) (hV : 0 < V) (hm : 0 < m) (hT : 0 < T)
    (hkinetic : p * V = N * m * msq / 3)
    (hgas : p * V = N * kB * T) :
    m * msq / 2 = 3 / 2 * (kB * T) ∧ Real.sqrt msq = Real.sqrt (3 * kB * T / m) := by
  have h1 : N * (m * msq) = N * (3 * kB * T) := by linear_combination 3 * hgas - 3 * hkinetic
  have h2 : m * msq = 3 * kB * T := mul_left_cancel₀ hN.ne' h1
  refine ⟨by linear_combination h2 / 2, ?_⟩
  congr 1
  rw [eq_div_iff hm.ne']
  linear_combination h2

theorem solution (T S₁ S₂ : ℝ) (h : S₂ / kB = S₁ / kB + 1) :
    T * (S₂ - S₁) = kB * T := by
  apply W2p_BoltzmannConstant_energy_of_one_nat <;> assumption
