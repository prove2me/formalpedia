-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:31.375716+00:00
-- url     : https://prove2.me/submissions/0568b7d4-464a-4137-af09-d0e831b7f4d3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_u_disc
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_u_sum_re
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_final_contra
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_near_far


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
set_option maxHeartbeats 1000000
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
theorem _root_.solution (c' C : ℝ) (A B : ℕ) (hc'0 : 0 < c') (hc'2 : c' ≤ 1 / 2) (hA1 : 1 ≤ A) (hB1 : 1 ≤ B)
    (hC : 0 < C)
    (hT : ∀ (n K : ℕ) (z : Fin n → ℂ), 1 ≤ n → B * n ≤ K →
      (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) → (∀ i, ‖z i‖ ^ 2 ≤ 2 * (z i).re) →
      ∃ k : ℕ, K ≤ k ∧ k ≤ A * K ∧ c' ^ K ≤ (∑ i, z i ^ k).re)
    (q ε l b c₂ : ℝ) (hq : q = c' / 2 ^ A) (hε : ε = q / 4) (hl : l = -Real.log q)
    (hb : b = 2 * B / ε ^ 2 + 4) (hc₂0 : 0 < c₂) (hc₂ : c₂ ≤ ε ^ 2 / (25 * B * C * (2 * l + 2)))
    (large₂ lam η K0 : ℝ) (hK0 : b + 64 * A * Real.exp (l * b) < K0)
    (hη0 : 0 < η) (hηc : η ≤ q ^ 2 / 200) (hlam0 : 0 < lam) (hlamη : lam / η ≤ Real.exp (-K0))
    (hηL : η * large₂ < c₂ * K0) (hLg0 : 0 < large₂)
    (N : ℕ) (w : Fin N → ℂ) (hw : ∀ i, η ≤ (w i).re) (hi0 : ∃ i, w i = ((η + η : ℝ) : ℂ))
    (hpow : ∀ j : ℕ, 1 ≤ j → (∑ i, 1 / (w i) ^ j).re ≤ 2 * j * lam / η ^ (j + 1) + C * large₂ * 25 ^ j) :
    False := by
  have h2A : (2 : ℝ) ≤ 2 ^ A := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ A := pow_le_pow_right₀ (by norm_num) hA1
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq4 : q ≤ 1 / 4 := by
    rw [hq, div_le_iff₀ (by positivity)]; nlinarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε1 : ε ≤ 1 / 16 := by rw [hε]; linarith
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hl0 : 0 ≤ l := by
    rw [hl]; have := Real.log_nonpos hq0.le (by linarith); linarith
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA1
  have hK0pos : 0 < K0 := by
    have : 0 ≤ 64 * A * Real.exp (l * b) := by positivity
    linarith
  set u : Fin N → ℂ := fun i => (η : ℂ) / w i with hu_def
  have hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re := fun i => u_disc η hη0 (w i) (hw i)
  have hi : ∃ i, 1 / 2 ≤ ‖u i‖ := by
    obtain ⟨i, hi⟩ := hi0
    refine ⟨i, ?_⟩
    simp only [hu_def, hi, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0,
      abs_of_pos (by linarith : (0 : ℝ) < η + η)]
    rw [le_div_iff₀ (by linarith)]; linarith
  set S : ℝ := ∑ i, (u i).re with hS_def
  have hS_eq : S = η * (∑ i, 1 / (w i) ^ 1).re := by
    have := u_sum_re η w 1
    simp only [pow_one] at this ⊢
    rw [hS_def, ← this, Complex.re_sum]
  have hlam1 : lam / η ≤ 1 := le_trans hlamη (by rw [Real.exp_le_one_iff]; linarith)
  have hS : S ≤ 2 * (lam / η) + 25 * C * (η * large₂) := by
    have h1 := hpow 1 le_rfl
    rw [hS_eq]
    have h2 := mul_le_mul_of_nonneg_left h1 hη0.le
    have h3 : η * (2 * ((1 : ℕ) : ℝ) * lam / η ^ (1 + 1) + C * large₂ * 25 ^ 1) = 2 * (lam / η) + 25 * C * (η * large₂) := by
      field_simp; ring
    linarith
  set Sb : ℝ := 2 + 25 * C * c₂ * K0 with hSb_def
  have hSb0 : 0 ≤ Sb := by positivity
  have hηL' : 25 * C * (η * large₂) ≤ 25 * C * (c₂ * K0) :=
    mul_le_mul_of_nonneg_left hηL.le (by positivity)
  have hSSb : S ≤ Sb := by rw [hSb_def]; linarith only [hηL', hS, hlam1]
  set x : ℝ := B * Sb / ε ^ 2 with hx_def
  have hx0 : 0 ≤ x := by positivity
  set K : ℕ := ⌈x⌉₊ + 3 with hK_def
  have hK3 : 3 ≤ K := by omega
  have hKr : (K : ℝ) = ⌈x⌉₊ + 3 := by rw [hK_def]; push_cast; ring
  have hxK : x ≤ ⌈x⌉₊ := Nat.le_ceil x
  have hxK' : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le (by linarith)
  have hSbx : Sb ≤ x := by
    rw [hx_def, le_div_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hε2 hSb0
    have h2 := mul_le_mul_of_nonneg_right hBr hSb0
    linarith only [h1, h2]
  have hBS : (B : ℝ) * S ≤ ε ^ 2 * K := by
    have h1 : (B : ℝ) * S ≤ B * Sb := mul_le_mul_of_nonneg_left hSSb (by positivity)
    have h2 : (B : ℝ) * Sb = ε ^ 2 * x := by rw [hx_def]; field_simp
    have h3 : ε ^ 2 * x ≤ ε ^ 2 * K := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  obtain ⟨j, hKj, hjA, hj⟩ := near_far c' A B hc'0 hT ε hε0 (by linarith) N u hu hi K (by omega) hBS
  have hj1 : 1 ≤ j := by omega
  have hpj := hpow j hj1
  have hsumj : (∑ i, u i ^ j).re = η ^ j * (∑ i, 1 / (w i) ^ j).re := u_sum_re η w j
  have hηj : 0 < η ^ j := pow_pos hη0 j
  have hRe : (∑ i, u i ^ j).re ≤ 2 * j * (lam / η) + C * (η * large₂) * 25 * (25 * η) ^ (j - 1) := by
    rw [hsumj]
    have h2 := mul_le_mul_of_nonneg_left hpj hηj.le
    have h3 : η ^ j * (2 * (j : ℝ) * lam / η ^ (j + 1) + C * large₂ * 25 ^ j) =
        2 * j * (lam / η) + C * (η * large₂) * 25 * (25 * η) ^ (j - 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [mul_pow, pow_succ, pow_succ]
      field_simp
      ring
    linarith

  have hjAK : (j : ℝ) ≤ A * K := by exact_mod_cast hjA
  have hB1' : 2 * j * (lam / η) ≤ 2 * A * K * Real.exp (-K0) := by
    have h0 : 0 ≤ lam / η := by positivity
    have : (j : ℝ) * (lam / η) ≤ (A * K) * Real.exp (-K0) :=
      mul_le_mul hjAK hlamη h0 (by positivity)
    linarith only [this]
  have h25 : 25 * η ≤ q ^ 2 / 8 := by linarith
  have h25' : q ^ 2 / 8 ≤ 1 := by
    have : q ^ 2 ≤ 1 := pow_le_one₀ hq0.le (by linarith)
    linarith only [this]
  have hB2 : C * (η * large₂) * 25 * (25 * η) ^ (j - 1) ≤ K * (q ^ 2 / 8) ^ (K - 1) := by
    have ha : C * (η * large₂) * 25 ≤ K := by
      have : C * (η * large₂) * 25 ≤ 25 * C * c₂ * K0 := by linarith only [hηL']
      linarith only [this, hSbx, hxK, hKr, hSb_def]
    have hp1 : (25 * η) ^ (j - 1) ≤ (25 * η) ^ (K - 1) :=
      pow_le_pow_of_le_one (by positivity) (by linarith) (by omega)
    have hp2 : (25 * η) ^ (K - 1) ≤ (q ^ 2 / 8) ^ (K - 1) := pow_le_pow_left₀ (by positivity) h25 _
    have hp0 : 0 ≤ (25 * η) ^ (j - 1) := by positivity
    have hC0 : 0 ≤ C * (η * large₂) * 25 := by positivity
    calc C * (η * large₂) * 25 * (25 * η) ^ (j - 1) ≤ K * (25 * η) ^ (j - 1) := mul_le_mul_of_nonneg_right ha hp0
      _ ≤ K * (q ^ 2 / 8) ^ (K - 1) := mul_le_mul_of_nonneg_left (le_trans hp1 hp2) (by positivity)
  have hB3 : ε ^ (j - 2) * S ≤ K * (q / 4) ^ K := by
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => le_trans (by positivity) (hu i))
    have hSK : S ≤ ε ^ 2 * K := by
      have := mul_le_mul_of_nonneg_right hBr hS0
      linarith only [this, hBS]
    have hp1 : ε ^ (j - 2) ≤ ε ^ (K - 2) := pow_le_pow_of_le_one hε0.le (by linarith) (by omega)
    have hp2 : ε ^ (K - 2) * ε ^ 2 = ε ^ K := by rw [← pow_add, Nat.sub_add_cancel (by omega : 2 ≤ K)]
    calc ε ^ (j - 2) * S ≤ ε ^ (K - 2) * S := mul_le_mul_of_nonneg_right hp1 hS0
      _ ≤ ε ^ (K - 2) * (ε ^ 2 * K) := mul_le_mul_of_nonneg_left hSK (by positivity)
      _ = K * ε ^ K := by rw [← hp2]; ring
      _ = K * (q / 4) ^ K := by rw [hε]
  have hLHS : q ^ K ≤ c' ^ K * (1 / 2) ^ j := by
    have h1 : q ^ K = c' ^ K * (1 / 2) ^ (A * K) := by
      rw [hq, div_pow, ← pow_mul, one_div_pow]; ring
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hjA
  have hmain : q ^ K ≤ 2 * A * K * Real.exp (-K0) + K * (q ^ 2 / 8) ^ (K - 1) + K * (q / 4) ^ K := by
    linarith
  set a : ℝ := 25 * B * C * c₂ / ε ^ 2 with ha_def
  have ha0 : 0 ≤ a := by positivity
  have ha : a * (2 * l + 2) ≤ 1 := by
    have h1 : c₂ * (25 * B * C * (2 * l + 2)) ≤ ε ^ 2 := by
      rwa [le_div_iff₀ (by positivity)] at hc₂
    rw [ha_def, div_mul_eq_mul_div, div_le_one (by positivity)]
    have : 25 * (B : ℝ) * C * c₂ * (2 * l + 2) = c₂ * (25 * B * C * (2 * l + 2)) := by ring
    linarith only [this, h1]
  have hKab : (K : ℝ) ≤ a * K0 + b := by
    have : x = a * K0 + (b - 4) := by
      rw [hx_def, ha_def, hb, hSb_def]; field_simp; ring
    linarith
  exact final_contra q A K0 a b l K hq0 hq4 hl hAr hK3 hK0pos ha0 ha hb0 hKab hK0 hmain
end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
