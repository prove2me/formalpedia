-- Prove2me | solution 1 for CloudMWU.Bicriteria.claim_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:29:54.633479+00:00
-- url     : https://prove2.me/submissions/15477f02-3123-4ce0-b582-674fff6be492

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model
import Theorems.Thm_CloudMWU_Bicriteria_lemma_1

open Finset CloudMWU.Bicriteria

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3) (β : Fin N → ℝ)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h)
    (r m : ℕ) (hm : sTilde N ε η ≤ (m : ℝ))
    (i₀ : Fin N) (hbusy : ∀ τ ∈ Icc r (r + m), 0 < runQueue h L τ i₀) :
    (((Ico r (r + m)).filter (fun τ => ∑ j ∈ active h L τ, h τ j ≤ 1 - ε)).card : ℝ)
      ≤ 4 * ε * (m : ℝ) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hεN : 0 < ε / (N : ℝ) := by positivity
  have hsimp : ∀ τ, h τ ∈ truncSimplex N ε := by
    intro τ
    cases τ with
    | zero => exact hrun.1
    | succ τ => exact (hrun.2 τ).2.1
  have hpos : ∀ τ i, 0 < h τ i := fun τ i => lt_of_lt_of_le hεN ((hsimp τ).2 i)
  have hle1 : ∀ τ i, h τ i ≤ 1 := by
    intro τ i
    have := Finset.single_le_sum (f := h τ) (fun j _ => (hpos τ j).le) (Finset.mem_univ i)
    rw [(hsimp τ).1] at this; exact this
  set c := cLem1 N ε η with hc_def
  have hc : c = ε * η / (4 * (N : ℝ)) := rfl
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 / 100 := by
    rw [hc, div_le_iff₀ (by positivity)]; nlinarith
  have hεc0 : 0 < ε * c := by positivity
  have hεc1 : ε * c ≤ 1 / 100 := by nlinarith
  set α := Real.log (1 + c) with hα
  set γ := - Real.log (1 - ε * c) with hγ
  have hαlow : c / (1 + c) ≤ α := by
    have h1' := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 / (1 + c))
    rw [one_div, Real.log_inv] at h1'
    have : (1 + c)⁻¹ - 1 = -(c / (1 + c)) := by field_simp; ring
    rw [hα]; linarith
  have hγup : γ ≤ ε * c / (1 - ε * c) := by
    have hpos' : (0:ℝ) < 1 - ε * c := by linarith
    have h1' := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 / (1 - ε * c))
    rw [one_div, Real.log_inv] at h1'
    have : (1 - ε * c)⁻¹ - 1 = ε * c / (1 - ε * c) := by
      have hne : (1 - ε * c) ≠ 0 := hpos'.ne'
      field_simp; ring
    rw [hγ]; linarith
  have hγ0 : 0 ≤ γ := by
    rw [hγ]; have := Real.log_nonpos (by linarith : (0:ℝ) ≤ 1 - ε * c) (by linarith)
    linarith
  -- low steps
  set low : ℕ → Prop := fun τ => ∑ j ∈ active h L τ, h τ j ≤ 1 - ε with hlow
  set g : ℕ → ℝ := fun τ => if low τ then α else -γ with hg
  have hstep : ∀ τ ∈ Icc r (r + m), h τ i₀ * Real.exp (g τ) ≤ h (τ + 1) i₀ := by
    intro τ hτ
    have hi : i₀ ∈ active h L τ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbusy τ hτ⟩
    have hl := lemma_1 N hN ε η hε hε' hη hη' β L hL h hrun τ
    by_cases hlo : low τ
    · have : g τ = α := by simp only [hg, if_pos hlo]
      rw [this, hα, Real.exp_log (by linarith)]
      exact hl.1 hlo i₀ hi
    · have : g τ = -γ := by simp only [hg, if_neg hlo]
      rw [this, hγ, neg_neg, Real.exp_log (by linarith)]
      by_cases hb : h τ i₀ < β i₀
      · have := hl.2.1 i₀ hi hb
        have := hpos τ i₀
        nlinarith
      · push_neg at hb
        exact hl.2.2 i₀ hi hb
  have hiter : ∀ n, n ≤ m → h r i₀ * Real.exp (∑ j ∈ range n, g (r + j)) ≤ h (r + n) i₀ := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have hs := hstep (r + n) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [Finset.sum_range_succ, Real.exp_add]
      have e : r + (n + 1) = r + n + 1 := by omega
      rw [e]
      calc h r i₀ * (Real.exp (∑ j ∈ range n, g (r + j)) * Real.exp (g (r + n)))
          = (h r i₀ * Real.exp (∑ j ∈ range n, g (r + j))) * Real.exp (g (r + n)) := by ring
        _ ≤ h (r + n) i₀ * Real.exp (g (r + n)) :=
            mul_le_mul_of_nonneg_right ih' (Real.exp_pos _).le
        _ ≤ h (r + n + 1) i₀ := hs
  -- sum of g
  set K := ((Ico r (r + m)).filter low).card with hK
  have hsumg : ∑ j ∈ range m, g (r + j) = (K : ℝ) * α - ((m : ℝ) - K) * γ := by
    have e1 : ∑ j ∈ range m, g (r + j) = ∑ τ ∈ Ico r (r + m), g τ := by
      rw [Finset.sum_Ico_eq_sum_range]; simp
    rw [e1, hg, Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hcard := Finset.card_filter_add_card_filter_not (s := Ico r (r + m)) low
    rw [Nat.card_Ico] at hcard
    have : (((Ico r (r + m)).filter (fun τ => ¬ low τ)).card : ℝ) = (m : ℝ) - K := by
      rw [hK]
      have : ((Ico r (r + m)).filter (fun τ => ¬ low τ)).card = m - ((Ico r (r + m)).filter low).card := by
        omega
      rw [this, Nat.cast_sub (by omega)]
    rw [this, ← hK]; ring
  -- log bound
  have hlogb : (K : ℝ) * α - ((m : ℝ) - K) * γ ≤ Real.log ((N : ℝ) / ε) := by
    have h1 := hiter m le_rfl
    rw [hsumg] at h1
    have h2 : ε / (N : ℝ) * Real.exp ((K : ℝ) * α - ((m : ℝ) - K) * γ) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right ((hsimp r).2 i₀) (Real.exp_pos ((K : ℝ) * α - ((m : ℝ) - K) * γ)).le
      linarith [hle1 (r + m) i₀]
    have h3 : Real.exp ((K : ℝ) * α - ((m : ℝ) - K) * γ) ≤ (N : ℝ) / ε := by
      rw [le_div_iff₀ hε]
      have e : ε / (N : ℝ) * Real.exp ((K : ℝ) * α - ((m : ℝ) - K) * γ)
          = Real.exp ((K : ℝ) * α - ((m : ℝ) - K) * γ) * ε / N := by ring
      rw [e, div_le_one hNpos] at h2; linarith
    calc (K : ℝ) * α - ((m : ℝ) - K) * γ
        = Real.log (Real.exp ((K : ℝ) * α - ((m : ℝ) - K) * γ)) := (Real.log_exp _).symm
      _ ≤ Real.log ((N : ℝ) / ε) := Real.log_le_log (Real.exp_pos _) h3
  have hst : sTilde N ε η = Real.log ((N : ℝ) / ε) / (ε * c) := rfl
  have hℓ : Real.log ((N : ℝ) / ε) ≤ ε * c * (m : ℝ) := by
    rw [hst, div_le_iff₀ hεc0] at hm; linarith
  have hKm : (K : ℝ) ≤ m := by
    have : K ≤ m := by
      have := Finset.card_filter_le (Ico r (r + m)) low
      rw [Nat.card_Ico] at this; omega
    exact_mod_cast this
  have hK0 : (0 : ℝ) ≤ K := by positivity
  -- K * α ≤ log + m γ
  have h1 : (K : ℝ) * α ≤ ε * c * m + m * (ε * c / (1 - ε * c)) := by
    have : ((m : ℝ) - K) * γ ≤ m * γ := by nlinarith
    have : (m : ℝ) * γ ≤ m * (ε * c / (1 - ε * c)) := mul_le_mul_of_nonneg_left hγup (by positivity)
    linarith
  have h2 : ε * c / (1 - ε * c) ≤ 102 / 100 * (ε * c) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h3 : (K : ℝ) * (c / (1 + c)) ≤ (K : ℝ) * α := mul_le_mul_of_nonneg_left hαlow hK0
  have h4 : (K : ℝ) * (c / (1 + c)) ≤ 202 / 100 * (ε * c) * m := by
    have : (m : ℝ) * (ε * c / (1 - ε * c)) ≤ m * (102 / 100 * (ε * c)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith
  have h5 : (K : ℝ) * c ≤ 202 / 100 * (ε * c) * m * (1 + c) := by
    have e : (K : ℝ) * (c / (1 + c)) = (K : ℝ) * c / (1 + c) := by ring
    rw [e, div_le_iff₀ (by linarith)] at h4; exact h4
  have h6 : (K : ℝ) ≤ 202 / 100 * ε * m * (1 + c) := by
    have e : 202 / 100 * (ε * c) * m * (1 + c) = (202 / 100 * ε * m * (1 + c)) * c := by ring
    rw [e] at h5
    exact le_of_mul_le_mul_right h5 hc0
  have hm0 : (0 : ℝ) ≤ m := by positivity
  show (K : ℝ) ≤ 4 * ε * m
  nlinarith
