-- Prove2me | solution 1 for CongestionTaxes.display_14_line_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:29:55.347994+00:00
-- url     : https://prove2.me/submissions/36dfc3d8-5a12-43be-96ec-fbb07cf1072e

import Mathlib
import Definitions.Def_CongestionTaxes_Assumption1
import Definitions.Def_CongestionTaxes_poissonValue
import Definitions.Def_CongestionTaxes_rhoSup

open scoped ENNReal

open CongestionTaxes in
theorem solution (L : Set (ℕ → ℝ)) (hL : ∀ ℓ ∈ L, Assumption1 ℓ) (hρ : rhoSup L < ⊤)
    (ℓ : ℕ → ℝ) (hmem : ℓ ∈ L) (x : ℕ) :
    poissonValue ℓ (x : ℝ) ≤ (rhoSup L).toReal * ((x : ℝ) * ℓ x) := by
  obtain ⟨h0, hpos, _, _⟩ := hL ℓ hmem
  have hnn : ∀ k, 0 ≤ ℓ k := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · rw [hk, h0]
    · exact (hpos k hk).le
  have hRnn : 0 ≤ (rhoSup L).toReal * ((x : ℝ) * ℓ x) :=
    mul_nonneg ENNReal.toReal_nonneg (mul_nonneg (Nat.cast_nonneg _) (hnn x))
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    unfold poissonValue
    have : ∀ i : ℕ, (i : ℝ) * ℓ i * ((0 : ℕ) : ℝ) ^ i / (i.factorial : ℝ) = 0 := by
      intro i
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi; simp
      · simp [zero_pow (Nat.pos_iff_ne_zero.1 hi)]
    simp only [this, tsum_zero, zero_mul]
    exact hRnn
  · set t : ℕ → ℝ := fun k => (k : ℝ) * ℓ k * (x : ℝ) ^ k * Real.exp (-(x : ℝ)) /
      (k.factorial : ℝ) with ht
    have htnn : ∀ k, 0 ≤ t k := fun k => by
      simp only [ht]; have := hnn k; positivity
    have hpv : poissonValue ℓ (x : ℝ) = ∑' k, t k := by
      unfold poissonValue
      rw [← tsum_mul_right]
      congr 1; funext k; simp only [ht]; ring
    rw [hpv]
    by_cases hs : Summable t
    · have hxl : 0 < (x : ℝ) * ℓ x := mul_pos (by exact_mod_cast hx) (hpos x hx)
      have hrho : (∑' k, ENNReal.ofReal (t k)) / ENNReal.ofReal ((x : ℝ) * ℓ x) ≤ rhoSup L := by
        unfold rhoSup
        refine le_trans ?_ (le_iSup₂ (f := fun ℓ (_ : ℓ ∈ L) => rho ℓ) ℓ hmem)
        unfold rho
        exact le_iSup₂ (f := fun (x : ℕ) (_ : 1 ≤ x) =>
          (∑' k : ℕ, ENNReal.ofReal ((k : ℝ) * ℓ k * (x : ℝ) ^ k * Real.exp (-(x : ℝ)) /
            (k.factorial : ℝ))) / ENNReal.ofReal ((x : ℝ) * ℓ x)) x hx
      rw [← ENNReal.ofReal_tsum_of_nonneg htnn hs] at hrho
      have hne : ENNReal.ofReal ((x : ℝ) * ℓ x) ≠ 0 := (ENNReal.ofReal_pos.2 hxl).ne'
      have h2 : ENNReal.ofReal (∑' k, t k) ≤ rhoSup L * ENNReal.ofReal ((x : ℝ) * ℓ x) := by
        rw [ENNReal.div_le_iff hne ENNReal.ofReal_ne_top] at hrho
        exact hrho
      have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hρ.ne ENNReal.ofReal_ne_top) h2
      rw [ENNReal.toReal_ofReal (tsum_nonneg htnn), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hxl.le] at h3
      exact h3
    · rw [tsum_eq_zero_of_not_summable hs]
      exact hRnn
