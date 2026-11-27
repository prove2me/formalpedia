-- Prove2me | solution 1 for FracRiccati.Radius.Supplement.prop_C_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:32.293822+00:00
-- url     : https://prove2.me/submissions/8585dc9d-6b86-40dd-ad76-29d5de341ce6

import Mathlib
import Definitions.Def_FracRiccati_Radius_Supplement_DoubleSeries

open FracRiccati
open FracRiccati.Radius
open FracRiccati.Radius.Supplement

theorem solution (α : ℝ) (lam mu nu u : ℂ)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hlam : lam ≠ 0) :
    ∀ ℓ : ℕ, 1 ≤ ℓ →
      doubleCoeff α lam mu nu u 0 (2 * ℓ - 1) ℓ =
        lam ^ (ℓ - 1) * (u / (Real.Gamma α : ℂ)) ^ ℓ * (startingValues α ℓ : ℂ) := by
          set a := doubleCoeff α lam mu nu u 0 with ha
          have hrec : ∀ j ℓ : ℕ, a (j + 2) ℓ =
              (mu * a (j + 1) ℓ + lam * ∑ i ∈ Finset.Ico 1 (j + 1), ∑ r ∈ Finset.range (ℓ + 1),
                a i r * a (j + 1 - i) (ℓ - r)) *
              ((Real.Gamma (α * ((j + 1 : ℕ) : ℝ) - (ℓ : ℝ) + 1) /
                Real.Gamma (α * ((j + 2 : ℕ) : ℝ) - (ℓ : ℝ) + 1) : ℝ) : ℂ) := by
            intro j ℓ
            rw [ha, doubleCoeff.eq_6]
            congr 3
            exact Finset.sum_attach (Finset.Ico 1 (j + 1))
              (fun i => ∑ r ∈ Finset.range (ℓ + 1),
                doubleCoeff α lam mu nu u 0 i r * doubleCoeff α lam mu nu u 0 (j + 1 - i) (ℓ - r))
          have hsrec : ∀ j : ℕ, startingValues α (j + 2) =
              Real.Gamma ((2 * α - 1) * ((j + 1 : ℕ) : ℝ)) /
                Real.Gamma ((2 * α - 1) * ((j + 2 : ℕ) : ℝ) + 1 - α) *
              ∑ i ∈ Finset.Ico 1 (j + 2), startingValues α i * startingValues α (j + 2 - i) := by
            intro j
            rw [startingValues.eq_3]
            congr 1
            exact Finset.sum_attach (Finset.Ico 1 (j + 2))
              (fun i => startingValues α i * startingValues α (j + 2 - i))
          have hvan : ∀ n k ℓ : ℕ, k ≤ n → k + 1 < 2 * ℓ → a k ℓ = 0 := by
            intro n
            induction n with
            | zero =>
              intro k ℓ hk _
              have : k = 0 := by omega
              subst this
              rw [ha, doubleCoeff.eq_1]
            | succ n ih =>
              intro k ℓ hk hkl
              rcases Nat.lt_or_ge k (n + 1) with h | h
              · exact ih k ℓ (by omega) hkl
              have hk' : k = n + 1 := by omega
              subst hk'
              rcases n with _ | j
              · -- k = 1
                obtain ⟨t, rfl⟩ : ∃ t, ℓ = t + 2 := ⟨ℓ - 2, by omega⟩
                rcases t with _ | t
                · rw [ha, doubleCoeff.eq_4]; simp
                · rw [ha, doubleCoeff.eq_5]
              · rw [hrec]
                have h1 : a (j + 1) ℓ = 0 := ih _ _ le_rfl (by omega)
                rw [h1]
                have h2 : ∑ i ∈ Finset.Ico 1 (j + 1), ∑ r ∈ Finset.range (ℓ + 1),
                    a i r * a (j + 1 - i) (ℓ - r) = 0 := by
                  apply Finset.sum_eq_zero
                  intro i hi
                  apply Finset.sum_eq_zero
                  intro r hr
                  rw [Finset.mem_Ico] at hi
                  rw [Finset.mem_range] at hr
                  rcases Nat.lt_or_ge (i + 1) (2 * r) with h3 | h3
                  · rw [ih i r (by omega) h3, zero_mul]
                  · rw [ih (j + 1 - i) (ℓ - r) (by omega) (by omega), mul_zero]
                rw [h2]; simp
          intro ℓ
          induction ℓ using Nat.strong_induction_on with
          | _ ℓ IH =>
          intro hℓ
          rcases ℓ with _ | ℓ
          · omega
          rcases ℓ with _ | m
          · simp [ha, doubleCoeff.eq_3, startingValues]
          -- ℓ = m + 2
          have e : 2 * (m + 1 + 1) - 1 = (2 * m + 1) + 2 := by omega
          rw [e, hrec]
          have h1 : a (2 * m + 1 + 1) (m + 1 + 1) = 0 := hvan _ _ _ le_rfl (by omega)
          rw [h1, mul_zero, zero_add]
          have hsum : ∑ i ∈ Finset.Ico 1 (2 * m + 1 + 1), ∑ r ∈ Finset.range (m + 1 + 1 + 1),
              a i r * a (2 * m + 1 + 1 - i) (m + 1 + 1 - r) =
              ∑ r ∈ Finset.Ico 1 (m + 2), a (2 * r - 1) r * a (2 * (m + 2 - r) - 1) (m + 2 - r) := by
            rw [Finset.sum_comm]
            have hsub : Finset.Ico 1 (m + 2) ⊆ Finset.range (m + 1 + 1 + 1) := by
              intro r hr
              rw [Finset.mem_Ico] at hr
              rw [Finset.mem_range]; omega
            rw [← Finset.sum_subset hsub ?_]
            · apply Finset.sum_congr rfl
              intro r hr
              rw [Finset.mem_Ico] at hr
              rw [Finset.sum_eq_single (2 * r - 1)]
              · have e1 : 2 * m + 1 + 1 - (2 * r - 1) = 2 * (m + 2 - r) - 1 := by omega
                have e1' : m + 1 + 1 - r = m + 2 - r := by omega
                rw [e1, e1']
              · intro i hi hne
                rw [Finset.mem_Ico] at hi
                rcases Nat.lt_or_ge (i + 1) (2 * r) with h3 | h3
                · rw [hvan i i r le_rfl h3, zero_mul]
                · rw [hvan _ _ (m + 1 + 1 - r) le_rfl (by omega), mul_zero]
              · intro hn
                exfalso; apply hn
                rw [Finset.mem_Ico]; omega
            · intro r hr hr'
              rw [Finset.mem_range] at hr
              rw [Finset.mem_Ico] at hr'
              apply Finset.sum_eq_zero
              intro i hi
              rw [Finset.mem_Ico] at hi
              rcases Nat.lt_or_ge (i + 1) (2 * r) with h3 | h3
              · rw [hvan i i r le_rfl h3, zero_mul]
              · rw [hvan _ _ (m + 1 + 1 - r) le_rfl (by omega), mul_zero]
          rw [hsum, hsrec m]
          have hsum2 : ∑ r ∈ Finset.Ico 1 (m + 2), a (2 * r - 1) r * a (2 * (m + 2 - r) - 1) (m + 2 - r)
              = ∑ r ∈ Finset.Ico 1 (m + 2), lam ^ m * (u / (Real.Gamma α : ℂ)) ^ (m + 2) *
                  ((startingValues α r : ℂ) * (startingValues α (m + 2 - r) : ℂ)) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [Finset.mem_Ico] at hr
            rw [IH r (by omega) (by omega), IH (m + 2 - r) (by omega) (by omega)]
            obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
            obtain ⟨q, rfl⟩ : ∃ q, m = p + q := ⟨m - p, by omega⟩
            have e2 : p + q + 2 - (p + 1) = q + 1 := by omega
            rw [e2]
            simp only [Nat.add_sub_cancel]
            ring
          rw [hsum2, ← Finset.mul_sum]
          have g1 : α * ((2 * m + 1 + 1 : ℕ) : ℝ) - ((m + 1 + 1 : ℕ) : ℝ) + 1 =
              (2 * α - 1) * ((m + 1 : ℕ) : ℝ) := by push_cast; ring
          have g2 : α * ((2 * m + 1 + 2 : ℕ) : ℝ) - ((m + 1 + 1 : ℕ) : ℝ) + 1 =
              (2 * α - 1) * ((m + 2 : ℕ) : ℝ) + 1 - α := by push_cast; ring
          rw [g1, g2]
          push_cast
          ring
