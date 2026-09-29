-- Prove2me | solution 1 for CerednikDrinfeld.Omega.pow_le_v_phi_of_mem_affinoid_of_v_det_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6cdf622e-f142-5119-9db7-e0d5f50c6222

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_pow_le_v_phi_of_mem_affinoid_of_v_det_lt

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace T2A

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "ι" => algebraMap K₀ K

theorem pow_two_mul_le_v_mul_sub (ϖ : PseudoUniformizer K₀ K) (n : ℕ) {z : K} (hz : z ∈ affinoid ϖ n)
    (u₁ u₂ : K₀) (h₂ : Valued.v (ι u₂) ≤ 1)
    (hunit : Valued.v (ι u₁) = 1 ∨ Valued.v (ι u₂) = 1) :
    Valued.v (ι ϖ.ϖ) ^ (2 * n) ≤ Valued.v (z * ι u₂ - ι u₁) := by
  set p := Valued.v (ι ϖ.ϖ) with hp
  have hp0 : 0 < p := ϖ.pos
  have hp1 : p ≤ 1 := ϖ.lt_one.le
  have hpn1 : p ^ n ≤ 1 := pow_le_one₀ zero_le' hp1
  have hpn0 : 0 < p ^ n := pow_pos hp0 n
  have h2n : p ^ (2 * n) = p ^ n * p ^ n := by rw [two_mul, pow_add]
  rw [mem_affinoid_iff'] at hz
  obtain ⟨hz₁, hz₂⟩ := hz

  have hfac : ∀ (hu₂ : u₂ ≠ 0), z * ι u₂ - ι u₁ = ι u₂ * (z - ι (u₁ / u₂)) := by
    intro hu₂
    have : ι u₂ ≠ 0 := (map_ne_zero _).mpr hu₂
    rw [map_div₀]
    field_simp
  rcases hunit with hu1 | hu2
  ·
    by_cases hlt : Valued.v (z * ι u₂) < 1
    ·
      have : Valued.v (z * ι u₂ - ι u₁) = 1 := by
        rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ (by rwa [Valuation.map_neg, hu1]), Valuation.map_neg,
          hu1]
      rw [this, h2n]
      exact mul_le_one' hpn1 hpn1
    · push Not at hlt

      have hu₂0 : u₂ ≠ 0 := by
        rintro rfl
        rw [map_zero, mul_zero, Valuation.map_zero] at hlt
        exact not_lt_of_ge hlt zero_lt_one
      have hvu₂ : 0 < Valued.v (ι u₂) := by
        rw [Valuation.pos_iff]; exact (map_ne_zero _).mpr hu₂0
      rw [hfac hu₂0, Valuation.map_mul]

      have hza := hz₂ (u₁ / u₂)

      have hu₂n : p ^ n ≤ Valued.v (ι u₂) := by
        rw [Valuation.map_mul] at hlt
        have hz0 : 0 < Valued.v z := by
          rw [Valuation.pos_iff]; rintro rfl; rw [Valuation.map_zero, zero_mul] at hlt
          exact not_lt_of_ge hlt zero_lt_one
        calc p ^ n = p ^ n * 1 := (mul_one _).symm
          _ ≤ p ^ n * (Valued.v z * Valued.v (ι u₂)) := by gcongr
          _ = (p ^ n * Valued.v z) * Valued.v (ι u₂) := by rw [mul_assoc]
          _ ≤ 1 * Valued.v (ι u₂) := by
            gcongr
            calc p ^ n * Valued.v z ≤ p ^ n * (p⁻¹ ^ n) := by gcongr
              _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hp0.ne', one_pow]
          _ = Valued.v (ι u₂) := one_mul _
      rw [h2n]
      exact mul_le_mul' hu₂n hza
  ·
    have hu₂0 : u₂ ≠ 0 := by
      rintro rfl; rw [map_zero, Valuation.map_zero] at hu2; exact zero_ne_one hu2
    rw [hfac hu₂0, Valuation.map_mul, hu2, one_mul, h2n]
    calc p ^ n * p ^ n ≤ p ^ n * 1 := by gcongr
      _ = p ^ n := mul_one _
      _ ≤ _ := hz₂ (u₁ / u₂)

theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp

def Phi (z b : K) (g : Matrix (Fin 2) (Fin 2) K₀) : K :=
  z * (ι (g 1 0) * b + ι (g 1 1)) - (ι (g 0 0) * b + ι (g 0 1))

theorem Phi_add (z b : K) (g h : Matrix (Fin 2) (Fin 2) K₀) : Phi z b (g + h) = Phi z b g + Phi z b h := by
  simp only [Phi, Matrix.add_apply, map_add]; ring

theorem Phi_sub (z b : K) (g h : Matrix (Fin 2) (Fin 2) K₀) : Phi z b (g - h) = Phi z b g - Phi z b h := by
  simp only [Phi, Matrix.sub_apply, map_sub]; ring

theorem Phi_vecMulVec (z b : K) (u w : Fin 2 → K₀) :
    Phi z b (Matrix.vecMulVec u w) = (ι (w 0) * b + ι (w 1)) * (z * ι (u 1) - ι (u 0)) := by
  simp only [Phi, Matrix.vecMulVec_apply, map_mul]; ring

theorem v_Phi_single_le (z b : K) (i j : Fin 2) (e : K₀) (M : Γ₀) (hzb : Valued.v (z * b) ≤ M) (hz : Valued.v z ≤ M)
    (hb : Valued.v b ≤ M) (h1 : (1 : Γ₀) ≤ M) :
    Valued.v (Phi z b (Matrix.single i j e)) ≤ M * Valued.v (ι e) := by
  rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl
  ·
    have : Phi z b (Matrix.single 0 0 e) = -(ι e * b) := by
      simp [Phi]
    rw [this, Valuation.map_neg, Valuation.map_mul, mul_comm]
    gcongr
  · have : Phi z b (Matrix.single 0 1 e) = -(ι e) := by
      simp [Phi]
    rw [this, Valuation.map_neg]
    calc Valued.v (ι e) = 1 * Valued.v (ι e) := (one_mul _).symm
      _ ≤ M * Valued.v (ι e) := by gcongr
  · have : Phi z b (Matrix.single 1 0 e) = z * b * ι e := by
      simp [Phi]; ring
    rw [this, Valuation.map_mul]
    gcongr
  · have : Phi z b (Matrix.single 1 1 e) = z * ι e := by
      simp [Phi]
    rw [this, Valuation.map_mul]
    gcongr

theorem exists_sub_vecMulVec_eq_single (g : Matrix (Fin 2) (Fin 2) K₀) (i₀ j₀ : Fin 2) (h0 : g i₀ j₀ ≠ 0) :
    ∃ (i₁ j₁ : Fin 2) (s : K₀), (s = 1 ∨ s = -1) ∧
      g - Matrix.vecMulVec (fun i => g i j₀ / g i₀ j₀) (fun j => g i₀ j) = Matrix.single i₁ j₁ (s * g.det / g i₀ j₀) := by
  rcases fin_two_cases i₀ with rfl | rfl <;> rcases fin_two_cases j₀ with rfl | rfl
  · refine ⟨1, 1, 1, Or.inl rfl, ?_⟩
    ext i j
    rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl <;>
      simp [Matrix.vecMulVec_apply, Matrix.det_fin_two] <;> field_simp <;> ring
  · refine ⟨1, 0, -1, Or.inr rfl, ?_⟩
    ext i j
    rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl <;>
      simp [Matrix.vecMulVec_apply, Matrix.det_fin_two] <;> field_simp <;> ring
  · refine ⟨0, 1, -1, Or.inr rfl, ?_⟩
    ext i j
    rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl <;>
      simp [Matrix.vecMulVec_apply, Matrix.det_fin_two] <;> field_simp <;> ring
  · refine ⟨0, 0, 1, Or.inl rfl, ?_⟩
    ext i j
    rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl <;>
      simp [Matrix.vecMulVec_apply, Matrix.det_fin_two] <;> field_simp <;> ring

theorem pow_four_mul_le_v_Phi (ϖ : PseudoUniformizer K₀ K) (n : ℕ) {b z : K} (hb : b ∈ affinoid ϖ n)
    (hz : z ∈ affinoid ϖ n) (g : Matrix (Fin 2) (Fin 2) K₀) (hle : ∀ i j, Valued.v (ι (g i j)) ≤ 1)
    (hone : ∃ i j, Valued.v (ι (g i j)) = 1)
    (hdet : Valued.v (ι g.det) < Valued.v (ι ϖ.ϖ) ^ (6 * n)) :
    Valued.v (ι ϖ.ϖ) ^ (4 * n) ≤ Valued.v (Phi z b g) := by
  set p := Valued.v (ι ϖ.ϖ) with hp
  have hp0 : 0 < p := ϖ.pos
  have hp1 : p ≤ 1 := ϖ.lt_one.le
  obtain ⟨i₀, j₀, hunit⟩ := hone
  have h0 : g i₀ j₀ ≠ 0 := by
    intro h; rw [h, map_zero, Valuation.map_zero] at hunit; exact zero_ne_one hunit
  have h0' : ι (g i₀ j₀) ≠ 0 := (map_ne_zero _).mpr h0
  obtain ⟨i₁, j₁, s, hs, hdiff⟩ := exists_sub_vecMulVec_eq_single g i₀ j₀ h0
  set u : Fin 2 → K₀ := fun i => g i j₀ / g i₀ j₀ with hu
  set w : Fin 2 → K₀ := fun j => g i₀ j with hw

  have hule : ∀ i, Valued.v (ι (u i)) ≤ 1 := by
    intro i
    simp only [hu, map_div₀, hunit, div_one]
    exact hle i j₀
  have hui₀ : Valued.v (ι (u i₀)) = 1 := by
    simp only [hu, div_self h0, map_one]
  have hwle : ∀ j, Valued.v (ι (w j)) ≤ 1 := fun j => hle i₀ j
  have hwj₀ : Valued.v (ι (w j₀)) = 1 := hunit
  have huunit : Valued.v (ι (u 0)) = 1 ∨ Valued.v (ι (u 1)) = 1 := by
    rcases fin_two_cases i₀ with h | h <;> [left; right] <;> rw [← h] <;> exact hui₀
  have hwunit : Valued.v (ι (-(w 1))) = 1 ∨ Valued.v (ι (w 0)) = 1 := by
    rcases fin_two_cases j₀ with h | h <;> [right; left]
    · rw [← h]; exact hwj₀
    · rw [map_neg, Valuation.map_neg, ← h]; exact hwj₀

  have hA : p ^ (4 * n) ≤ Valued.v (Phi z b (Matrix.vecMulVec u w)) := by
    rw [Phi_vecMulVec, Valuation.map_mul, show 4 * n = 2 * n + 2 * n by ring, pow_add]
    refine mul_le_mul' ?_ ?_
    · have := pow_two_mul_le_v_mul_sub ϖ n hb (-(w 1)) (w 0) (hwle 0) hwunit
      rwa [map_neg, sub_neg_eq_add, mul_comm b] at this
    · exact pow_two_mul_le_v_mul_sub ϖ n hz (u 0) (u 1) (hule 1) huunit

  have hM : Valued.v (Phi z b (g - Matrix.vecMulVec u w)) < p ^ (4 * n) := by
    rw [hdiff]
    have hzle : Valued.v z ≤ p⁻¹ ^ n := ((mem_affinoid_iff' ϖ n z).mp hz).1
    have hble : Valued.v b ≤ p⁻¹ ^ n := ((mem_affinoid_iff' ϖ n b).mp hb).1
    have hpinv : 1 ≤ p⁻¹ := (one_le_inv₀ hp0).2 hp1
    have hn2n : p⁻¹ ^ n ≤ p⁻¹ ^ (2 * n) := pow_le_pow_right₀ hpinv (by omega)
    have hMzb : Valued.v (z * b) ≤ p⁻¹ ^ (2 * n) := by
      rw [Valuation.map_mul, two_mul, pow_add]; exact mul_le_mul' hzle hble
    have h1M : (1 : Γ₀) ≤ p⁻¹ ^ (2 * n) := one_le_pow₀ hpinv
    have hB := v_Phi_single_le z b i₁ j₁ (s * g.det / g i₀ j₀) (p⁻¹ ^ (2 * n)) hMzb (hzle.trans hn2n)
      (hble.trans hn2n) h1M
    have hve : Valued.v (ι (s * g.det / g i₀ j₀)) = Valued.v (ι g.det) := by
      have hvs : Valued.v (ι s) = 1 := by
        rcases hs with rfl | rfl
        · rw [map_one, Valuation.map_one]
        · rw [map_neg, map_one, Valuation.map_neg, Valuation.map_one]
      rw [map_div₀, map_mul, Valuation.map_div, Valuation.map_mul, hvs, one_mul, hunit, div_one]
    rw [hve] at hB
    refine hB.trans_lt ?_
    calc p⁻¹ ^ (2 * n) * Valued.v (ι g.det) < p⁻¹ ^ (2 * n) * p ^ (6 * n) :=
          mul_lt_mul_of_pos_left hdet (pow_pos (zero_lt_iff.mpr (inv_ne_zero hp0.ne')) _)
      _ = p ^ (4 * n) := by
          rw [show 6 * n = 2 * n + 4 * n by ring, pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0.ne', one_pow,
            one_mul]

  have hsplit : Phi z b g = Phi z b (Matrix.vecMulVec u w) + Phi z b (g - Matrix.vecMulVec u w) := by
    rw [Phi_sub]; ring
  rw [hsplit, Valuation.map_add_eq_of_lt_left _ (hM.trans_le hA)]
  exact hA

end T2A

theorem solution
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) (n : ℕ) {b z : K} (hb : b ∈ affinoid ϖ n) (hz : z ∈ affinoid ϖ n)
    (g : Matrix (Fin 2) (Fin 2) K₀)
    (hle : ∀ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) ≤ 1)
    (hone : ∃ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) = 1)
    (hdet : Valued.v (algebraMap K₀ K g.det) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (6 * n)) :
    Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (4 * n) ≤
      Valued.v (z * (algebraMap K₀ K (g 1 0) * b + algebraMap K₀ K (g 1 1)) -
        (algebraMap K₀ K (g 0 0) * b + algebraMap K₀ K (g 0 1))) :=
  T2A.pow_four_mul_le_v_Phi ϖ n hb hz g hle hone hdet

end S_CerednikDrinfeld_Omega_pow_le_v_phi_of_mem_affinoid_of_v_det_lt
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_pow_le_v_phi_of_mem_affinoid_of_v_det_lt (solution)
