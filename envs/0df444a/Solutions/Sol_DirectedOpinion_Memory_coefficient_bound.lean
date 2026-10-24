-- Prove2me | solution 1 for DirectedOpinion.Memory.coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T03:26:10.023966+00:00
-- url     : https://prove2.me/submissions/bb75d4f1-21d4-4346-84bf-b4117047ad14

import Mathlib
import Definitions.Def_DirectedOpinion_Memory_Setting

open DirectedOpinion.Memory
open MeasureTheory ProbabilityTheory

theorem solution (c d ρ₂ : ℝ) (hc : 0 < c) (hd : 0 < d) (hcd : c + d < 1)
    (hρ₂ : 0 ≤ ρ₂) (hρ₂c : ρ₂ ≤ c ^ 2) :
    (∀ m : ℕ, pT c d m ∈ Set.Ioo (0 : ℝ) 1) ∧
    geomExp ρ₂ (fun k => ((c + d) ^ (2 * (k + 2)))⁻¹)
      = (1 - ρ₂) / ((c + d) ^ 2 * ((c + d) ^ 2 - ρ₂)) ∧
    1 / (1 - ρ₂) * geomExp ρ₂ (fun k => ((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1))
      - 1 / ((c + d) ^ 2 * ((c + d) ^ 2 - ρ₂)) ≤ 0 := by
  set b := c + d with hb
  have hb0 : 0 < b := by linarith
  have hb1 : b < 1 := hcd
  have ha0 : 0 ≤ 1 - c - d := by linarith
  have ha1 : 1 - c - d < 1 := by linarith
  -- part 1: p_m ∈ (0,1)
  have hp : ∀ m : ℕ, pT c d m ∈ Set.Ioo (0 : ℝ) 1 := by
    intro m
    set x : ℕ → ℝ := fun s => ((s + m).choose m : ℝ) * (1 - c - d) ^ s * b ^ (m + 1) with hx
    have hxsum : HasSum x 1 := by
      have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) m (r := 1 - c - d)
        (by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith)
      have h2 := h.mul_right (b ^ (m + 1))
      have e : 1 - (1 - c - d) = b := by rw [hb]; ring
      rw [e, one_div, inv_mul_cancel₀ (pow_ne_zero _ hb0.ne')] at h2
      exact h2
    have hx0 : ∀ s, 0 ≤ x s := fun s => by
      simp only [hx]; positivity
    have hx1 : ∀ s, x s ≤ 1 := fun s => by
      have := le_hasSum hxsum s (fun j _ => hx0 j); exact this
    have hterm : ∀ s, ((s + m).choose s : ℝ) ^ 2 * (1 - c - d) ^ (2 * s) * (c + d) ^ (2 * (m + 1))
        = x s ^ 2 := by
      intro s
      simp only [hx]
      rw [Nat.choose_symm_add, ← hb]; ring
    have hsq : Summable (fun s => x s ^ 2) :=
      Summable.of_nonneg_of_le (fun s => sq_nonneg _)
        (fun s => by nlinarith [hx0 s, hx1 s]) hxsum.summable
    have hpT : pT c d m = ∑' s, x s ^ 2 := by
      unfold pT; exact tsum_congr hterm
    have hx00 : x 0 = b ^ (m + 1) := by simp [hx]
    have hbm0 : 0 < b ^ (m + 1) := pow_pos hb0 _
    have hbm1 : b ^ (m + 1) < 1 := pow_lt_one₀ hb0.le hb1 (by omega)
    refine ⟨?_, ?_⟩
    · rw [hpT]
      exact hsq.tsum_pos (fun s => sq_nonneg _) 0 (by rw [hx00]; positivity)
    · rw [hpT]
      have : ∑' s, x s ^ 2 < 1 :=
        hasSum_lt (f := fun s => x s ^ 2) (g := x) (i := 0)
          (fun s => by nlinarith [hx0 s, hx1 s])
          (by show x 0 ^ 2 < x 0; rw [hx00]; nlinarith) hsq.hasSum hxsum
      exact this
  -- part 2: geometric expectation
  have hb2 : ρ₂ < b ^ 2 := by
    calc ρ₂ ≤ c ^ 2 := hρ₂c
      _ < b ^ 2 := by rw [hb]; nlinarith
  have hr0 : 0 ≤ ρ₂ / b ^ 2 := by positivity
  have hr1 : ρ₂ / b ^ 2 < 1 := by rw [div_lt_one (by positivity)]; exact hb2
  have hgterm : ∀ k : ℕ, ρ₂ ^ k * (1 - ρ₂) * ((c + d) ^ (2 * (k + 2)))⁻¹
      = (1 - ρ₂) * (b ^ 4)⁻¹ * (ρ₂ / b ^ 2) ^ k := by
    intro k
    have e : (c + d) ^ (2 * (k + 2)) = b ^ 4 * (b ^ 2) ^ k := by
      rw [← hb, ← pow_mul, ← pow_add]; ring_nf
    rw [e, div_pow]
    have : (b ^ 2) ^ k ≠ 0 := by positivity
    have : b ^ 4 ≠ 0 := by positivity
    field_simp
  have hgsum : HasSum (fun k : ℕ => ρ₂ ^ k * (1 - ρ₂) * ((c + d) ^ (2 * (k + 2)))⁻¹)
      ((1 - ρ₂) / (b ^ 2 * (b ^ 2 - ρ₂))) := by
    have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ((1 - ρ₂) * (b ^ 4)⁻¹)
    have hne : b ^ 2 - ρ₂ ≠ 0 := by linarith
    have hb2' : b ^ 2 ≠ 0 := by positivity
    have e2 : (1 - ρ₂) / (b ^ 2 * (b ^ 2 - ρ₂)) = (1 - ρ₂) * (b ^ 4)⁻¹ * (1 - ρ₂ / b ^ 2)⁻¹ := by
      rw [one_sub_div hb2']
      field_simp
    rw [e2, show (fun k : ℕ => ρ₂ ^ k * (1 - ρ₂) * ((c + d) ^ (2 * (k + 2)))⁻¹)
      = fun k : ℕ => (1 - ρ₂) * (b ^ 4)⁻¹ * (ρ₂ / b ^ 2) ^ k from funext hgterm]
    exact h
  have hρ1 : ρ₂ < 1 := by nlinarith
  refine ⟨hp, ?_, ?_⟩
  · unfold geomExp; exact hgsum.tsum_eq
  · have hle : geomExp ρ₂ (fun k => ((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1))
        ≤ (1 - ρ₂) / (b ^ 2 * (b ^ 2 - ρ₂)) := by
      unfold geomExp
      have hnn : ∀ k : ℕ, 0 ≤ ρ₂ ^ k * (1 - ρ₂) * (((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1)) :=
        fun k => by
          have := (hp (k + 1)).1
          have : 0 ≤ 1 - ρ₂ := by linarith
          positivity
      have hle' : ∀ k : ℕ, ρ₂ ^ k * (1 - ρ₂) * (((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1))
          ≤ ρ₂ ^ k * (1 - ρ₂) * ((c + d) ^ (2 * (k + 2)))⁻¹ := by
        intro k
        have h1 := (hp (k + 1)).2
        have : 0 ≤ ρ₂ ^ k * (1 - ρ₂) * ((c + d) ^ (2 * (k + 2)))⁻¹ := by
          have : 0 ≤ 1 - ρ₂ := by linarith
          positivity
        calc ρ₂ ^ k * (1 - ρ₂) * (((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1))
            = (ρ₂ ^ k * (1 - ρ₂) * ((c + d) ^ (2 * (k + 2)))⁻¹) * pT c d (k + 1) := by ring
          _ ≤ (ρ₂ ^ k * (1 - ρ₂) * ((c + d) ^ (2 * (k + 2)))⁻¹) * 1 :=
            mul_le_mul_of_nonneg_left h1.le this
          _ = _ := by ring
      have hs := Summable.of_nonneg_of_le hnn hle' hgsum.summable
      exact hasSum_le hle' hs.hasSum hgsum
    have h1 : 0 < 1 - ρ₂ := by linarith
    have h2 : 0 < b ^ 2 - ρ₂ := by linarith
    have key : 1 / (1 - ρ₂) * geomExp ρ₂ (fun k => ((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1))
        ≤ 1 / (1 - ρ₂) * ((1 - ρ₂) / (b ^ 2 * (b ^ 2 - ρ₂))) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have e : 1 / (1 - ρ₂) * ((1 - ρ₂) / (b ^ 2 * (b ^ 2 - ρ₂))) = 1 / (b ^ 2 * (b ^ 2 - ρ₂)) := by
      field_simp
    linarith
