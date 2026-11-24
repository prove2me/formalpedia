-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.c_add_sigma_c_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:46:36.406256+00:00
-- url     : https://prove2.me/submissions/baa90cd4-4aac-4289-8236-3d6bb5ea2437

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_norm_add_le_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_eq_zero_of_div
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_of_not_dvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_product_single_variables

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
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace CoboundarySeries
open MvPowerSeries
section Cob
variable {K : Type} [Field K]
end Cob
section Supp
variable {K : Type} [Field K]
end Supp
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Norm
section MapG
variable {K : Type} [Field K]
end MapG
end CoboundarySeries
open CoboundarySeries
private theorem coeff_lgF_one_lemma {K : Type} [Field K] {p : ℕ} (hp : 2 ≤ p) :
    PowerSeries.coeff 1 (lgF K p) = 1 := by
  have h4 : 1 < p ^ 2 := by
    have := Nat.pow_le_pow_left hp 2
    norm_num at this
    omega
  rw [lgF, PowerSeries.coeff_mk, Finset.sum_range_succ, Finset.sum_range_one]
  simp [h4.ne]
private theorem coeff_g0F_at_lemma_2 {K : Type} [Field K] {p : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    PowerSeries.coeff (p * (p ^ 2) ^ i) (g0F K p) = ((p : K) ^ (i + 1))⁻¹ := by
  have hp2 : 2 ≤ p ^ 2 := by nlinarith
  have hinj : ∀ j, (p * (p ^ 2) ^ i = p * (p ^ 2) ^ j) ↔ j = i := by
    intro j
    constructor
    · intro h
      have h' : (p ^ 2) ^ i = (p ^ 2) ^ j := Nat.eq_of_mul_eq_mul_left (by omega) h
      exact (Nat.pow_right_injective hp2 h').symm
    · rintro rfl
      rfl
  have hlt : i < (p ^ 2) ^ i := Nat.lt_pow_self (by omega)
  have hi : i ∈ Finset.range (p * (p ^ 2) ^ i + 1) := by
    rw [Finset.mem_range]
    nlinarith
  rw [g0F, PowerSeries.coeff_mk]
  simp_rw [hinj]
  simp [hi]
private theorem coeff_g0F_one_lemma_3 {K : Type} [Field K] {p : ℕ} (hp : 2 ≤ p) :
    PowerSeries.coeff 1 (g0F K p) = 0 := by
  rw [g0F, PowerSeries.coeff_mk]
  refine Finset.sum_eq_zero fun j _ => if_neg ?_
  intro h
  have h1 : 1 ≤ (p ^ 2) ^ j := Nat.one_le_pow _ _ (pow_pos (by omega : 0 < p) 2)
  nlinarith
end Formalism.InvariantFactorPaths.G7
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open CoboundarySeries
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : StepIII := by
  intro K _ _ _ p σ hU G c c' hc hc' hD hI
  obtain ⟨hpr, hp2, hnp, -, -⟩ := hU
  have hp : 2 ≤ p := hp2.le
  have hp0 : p ≠ 0 := by omega
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp0
  have hnd1 : ¬ p ∣ 1 := fun h => by
    have := Nat.le_of_dvd one_pos h
    omega
  have hall : ∀ z : Fin 2, z = 0 ∨ z = 1 := fun z => by fin_cases z <;> simp
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hlg1 : PowerSeries.coeff 1 (lgF K p) = 1 := coeff_lgF_one_lemma hp
  have hg01 : PowerSeries.coeff 1 (g0F K p) = 0 := coeff_g0F_one_lemma_3 hp
  apply eq_zero_of_div hp hnp
  intro i
  obtain ⟨m, hm⟩ : ∃ m, m = p * (p ^ 2) ^ i := ⟨_, rfl⟩
  have hg0m : PowerSeries.coeff m (g0F K p) = ((p : K) ^ (i + 1))⁻¹ := hm ▸ coeff_g0F_at_lemma_2 hp i
  obtain ⟨n, hn⟩ : ∃ n : Fin 2 →₀ ℕ, n = Finsupp.single 1 m + Finsupp.single 0 1 := ⟨_, rfl⟩

  have hcoefD : MvPowerSeries.coeff (Finsupp.single 1 m) (MvPowerSeries.pderiv (R := K) 0 G -
      MvPowerSeries.C c * (at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (g0F K p))) =
      MvPowerSeries.coeff n G - c * ((p : K) ^ (i + 1))⁻¹ := by
    have hs0 : (Finsupp.single (1 : Fin 2) m) 0 = 0 := by simp
    have hs1 : (Finsupp.single (1 : Fin 2) m) 1 = m := by simp
    rw [map_sub, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C_mul, coeff_product_single_variables h01 hall, hs0, hs1,
      PowerSeries.coeff_derivative, hg0m, ← hn]
    simp [hlg1]

  have hcoefH : MvPowerSeries.coeff n (Hser p σ G (σ c) (σ c')) =
      -(MvPowerSeries.coeff n G) - σ c' * ((p : K) ^ (i + 1))⁻¹ := by
    have hn0 : n 0 = 1 := by simp [hn]
    have hn1 : n 1 = m := by simp [hn]
    have hfr : MvPowerSeries.coeff n (frobVar p (MvPowerSeries.map σ G)) = 0 :=
      coeff_frobVar_of_not_dvd hp0 _ (i := 0) (by rw [hn0]; exact hnd1)
    unfold Hser DeS
    simp only [map_sub, MvPowerSeries.coeff_C_mul]
    rw [hfr, coeff_product_single_variables h01 hall, coeff_product_single_variables h01 hall, hn0, hn1, hg01, hlg1, hg0m]
    field_simp
    ring
  have hA : ‖MvPowerSeries.coeff n G - c * ((p : K) ^ (i + 1))⁻¹‖ ≤ 1 := by
    rw [← hcoefD]
    exact hD _
  have hB : ‖-(MvPowerSeries.coeff n G) - σ c' * ((p : K) ^ (i + 1))⁻¹‖ ≤ 1 := by
    rw [← hcoefH]
    exact hI n
  have key : (c + σ c') * ((p : K) ^ (i + 1))⁻¹ =
      -((MvPowerSeries.coeff n G - c * ((p : K) ^ (i + 1))⁻¹) +
        (-(MvPowerSeries.coeff n G) - σ c' * ((p : K) ^ (i + 1))⁻¹)) := by ring
  rw [key, norm_neg]
  exact norm_add_le_one hA hB
end Formalism.InvariantFactorPaths.G7
