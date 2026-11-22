-- Prove2me | solution 1 for Egrs75.SeedWindow.seed_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:38.566178+00:00
-- url     : https://prove2.me/submissions/31de4c75-cbdc-4f40-886e-33cf6e968d47

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_Egrs75_LogIrrationality
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Definitions.Def_LeanPool_Egrs75_SeedWindow
public import Theorems.Thm_Egrs75_SeedWindow_lt_of_log_lt
public import Theorems.Thm_Egrs75_SeedWindow_walk_hits
public import Theorems.Thm_Egrs75_SeedWindow_exists_small_step

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.SeedWindow
open Nat
open Egrs75
namespace Egrs75.SeedWindow
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq3 : 3 ≤ q)
    (hpq : p ≠ q) (F : ℕ) :
    ∃ α e : ℕ, 1 ≤ α ∧ F < q ^ (e + 3) ∧
      (q - 1) / 2 * q ^ (e + 3) < p ^ α ∧
      4 * p ^ α < 4 * ((q - 1) / 2 * q ^ (e + 3)) + q ^ (e + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hL : 0 < Real.log p := Real.log_pos hp1
  have hM : 0 < Real.log q := Real.log_pos hq1
  have hqR0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hBq1 : 1 ≤ (q - 1) / 2 := by omega
  have hBqR : (1 : ℝ) ≤ (((q - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hBq1
  set c₁ : ℝ := (((q - 1) / 2 : ℕ) : ℝ) with hc₁def
  set c₂ : ℝ := c₁ + 1 / (4 * (q : ℝ) ^ 2) with hc₂def
  have hc₁pos : 0 < c₁ := by rw [hc₁def]; linarith
  have hquad : (0 : ℝ) < 1 / (4 * (q : ℝ) ^ 2) := by positivity
  have hc₂pos : 0 < c₂ := by rw [hc₂def]; linarith
  have hc₁₂ : c₁ < c₂ := by rw [hc₂def]; linarith
  set w₁ : ℝ := Real.log c₁ with hw₁def
  set w₂ : ℝ := Real.log c₂ with hw₂def
  have hw₁0 : 0 ≤ w₁ := Real.log_nonneg hBqR
  have hw₁₂ : w₁ < w₂ := Real.log_lt_log hc₁pos hc₁₂
  set β₀ : ℕ := max (F + 1) 3 with hβ₀def
  have hβ₀3 : 3 ≤ β₀ := le_max_right _ _
  have hβ₀F : F + 1 ≤ β₀ := le_max_left _ _
  -- the small step
  obtain ⟨a, b, ha1, hδne, hδabs, hδbneg⟩ :=
    exists_small_step hp hq hpq (sub_pos.mpr hw₁₂)
  -- main: α, βe with γ := α·log p − βe·log q ∈ (w₁, w₂), 1 ≤ α, β₀ ≤ βe
  have hmain : ∃ α βe : ℕ, 1 ≤ α ∧ β₀ ≤ βe ∧
      w₁ < (α : ℝ) * Real.log p - (βe : ℝ) * Real.log q ∧
      (α : ℝ) * Real.log p - (βe : ℝ) * Real.log q < w₂ := by
    set δ : ℝ := (a : ℝ) * Real.log p - (b : ℝ) * Real.log q with hδdef
    have habs2 := abs_lt.mp hδabs
    rcases lt_trichotomy δ 0 with hneg | h0 | hpos
    · -- δ < 0: walk γ DOWN from a tall pure power α₀·log p
      have hb1 : 1 ≤ b := hδbneg hneg
      have hδ'0 : 0 < -δ := by linarith
      have hδ'w : -δ < w₂ - w₁ := by linarith [habs2.1]
      obtain ⟨α₀, hα₀⟩ := exists_nat_gt ((w₂ + (β₀ : ℝ) * (w₂ - w₁)) / Real.log p)
      have hα₀L : w₂ + (β₀ : ℝ) * (w₂ - w₁) < (α₀ : ℝ) * Real.log p := by
        have := (div_lt_iff₀ hL).mp hα₀
        linarith
      have hβ₀R0 : (0 : ℝ) ≤ (β₀ : ℝ) * (w₂ - w₁) := by
        have h1 : (0 : ℝ) ≤ (β₀ : ℝ) := by positivity
        have h2 : (0 : ℝ) ≤ w₂ - w₁ := by linarith
        exact mul_nonneg h1 h2
      have hstart : -((α₀ : ℝ) * Real.log p) < -w₂ := by linarith
      obtain ⟨t, ht1, hlo, hhi⟩ :=
        walk_hits hδ'0 (by linarith : -δ < (-w₁) - (-w₂)) hstart
      -- height: t > β₀
      have htβ : β₀ < t := by
        have hwpos : 0 < w₂ - w₁ := by linarith
        have h1 : (β₀ : ℝ) * (w₂ - w₁) < (t : ℝ) * (-δ) := by linarith
        have htδ : (t : ℝ) * (-δ) ≤ (t : ℝ) * (w₂ - w₁) :=
          mul_le_mul_of_nonneg_left (le_of_lt hδ'w) (by positivity)
        have h2 : (β₀ : ℝ) * (w₂ - w₁) < (t : ℝ) * (w₂ - w₁) := lt_of_lt_of_le h1 htδ
        have hβ₀t : (β₀ : ℝ) < (t : ℝ) := lt_of_mul_lt_mul_right h2 (le_of_lt hwpos)
        exact_mod_cast hβ₀t
      have hta : 1 ≤ t * a := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))
      have htb : t ≤ t * b := Nat.le_mul_of_pos_right t (by omega)
      have hid : ((α₀ + t * a : ℕ) : ℝ) * Real.log p - ((t * b : ℕ) : ℝ) * Real.log q
          = -(-((α₀ : ℝ) * Real.log p) + (t : ℝ) * (-δ)) := by
        push_cast
        rw [hδdef]
        ring
      refine ⟨α₀ + t * a, t * b, by omega, by omega, ?_, ?_⟩
      · rw [hid]; linarith
      · rw [hid]; linarith
    · exact absurd h0 hδne
    · -- δ > 0: walk γ UP from −β₀·log q
      have hδw : δ < w₂ - w₁ := habs2.2
      have hstart : -((β₀ : ℝ) * Real.log q) < w₁ := by
        have h1 : (0 : ℝ) < (β₀ : ℝ) := by
          simp_all
        have h2 : 0 < (β₀ : ℝ) * Real.log q := mul_pos h1 hM
        linarith
      obtain ⟨t, ht1, hlo, hhi⟩ := walk_hits hpos hδw hstart
      have hta : 1 ≤ t * a := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by omega) (by omega))
      have hid : ((t * a : ℕ) : ℝ) * Real.log p - ((t * b + β₀ : ℕ) : ℝ) * Real.log q
          = -((β₀ : ℝ) * Real.log q) + (t : ℝ) * δ := by
        push_cast
        rw [hδdef]
        ring
      refine ⟨t * a, t * b + β₀, by omega, by omega, ?_, ?_⟩
      · rw [hid]; exact hlo
      · rw [hid]; exact hhi
  -- transfer back to ℕ
  obtain ⟨α, βe, hα1, hβe, hγlo, hγhi⟩ := hmain
  have hβe3 : 3 ≤ βe := le_trans hβ₀3 hβe
  refine ⟨α, βe - 3, hα1, ?_, ?_, ?_⟩
  all_goals have hee : βe - 3 + 3 = βe := by omega
  · -- F < q^(βe)
    rw [hee]
    have h2 : F < 2 ^ F := Nat.lt_two_pow_self
    have h3 : (2 : ℕ) ^ F ≤ q ^ F := Nat.pow_le_pow_left (by omega) F
    have h4 : q ^ F ≤ q ^ βe := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · -- left bound
    rw [hee]
    have h1 : Real.log (c₁ * (q : ℝ) ^ βe) < Real.log ((p : ℝ) ^ α) := by
      rw [Real.log_mul (ne_of_gt hc₁pos) (by positivity), Real.log_pow, Real.log_pow]
      have hlogq : Real.log ((q : ℝ) ^ βe) = (βe : ℝ) * Real.log q := Real.log_pow _ _
      linarith [hγlo]
    have h2 : c₁ * (q : ℝ) ^ βe < (p : ℝ) ^ α :=
      lt_of_log_lt (by positivity) (by positivity) h1
    have h3 : (((q - 1) / 2 * q ^ βe : ℕ) : ℝ) < ((p ^ α : ℕ) : ℝ) := by
      simp_all
    exact_mod_cast h3
  · -- right bound
    rw [hee]
    have h1 : Real.log ((p : ℝ) ^ α) < Real.log (c₂ * (q : ℝ) ^ βe) := by
      rw [Real.log_mul (ne_of_gt hc₂pos) (by positivity), Real.log_pow, Real.log_pow]
      linarith [hγhi]
    have h2 : (p : ℝ) ^ α < c₂ * (q : ℝ) ^ βe :=
      lt_of_log_lt (by positivity) (by positivity) h1
    have hsplit : (q : ℝ) ^ βe = (q : ℝ) ^ (βe - 3 + 1) * (q : ℝ) ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    have h3 : c₂ * (q : ℝ) ^ βe
        = c₁ * (q : ℝ) ^ βe + (q : ℝ) ^ (βe - 3 + 1) / 4 := by
      rw [hc₂def, hsplit]
      have hq2 : (q : ℝ) ^ 2 ≠ 0 := by positivity
      field_simp
    have h4 : 4 * ((p ^ α : ℕ) : ℝ)
        < 4 * (((q - 1) / 2 * q ^ βe : ℕ) : ℝ) + ((q ^ (βe - 3 + 1) : ℕ) : ℝ) := by
      push_cast
      rw [hc₁def] at h3
      nlinarith [h2, h3]
    exact_mod_cast h4
end Egrs75.SeedWindow
