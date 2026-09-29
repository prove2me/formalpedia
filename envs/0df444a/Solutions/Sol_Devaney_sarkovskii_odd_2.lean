-- Prove2me | solution 2 for Devaney.sarkovskii_odd
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T15:01:56.711561+00:00
-- url     : https://prove2.me/submissions/89a42cbe-d7fb-4abe-a018-b99395febcbe

import Mathlib
import Definitions.Def_Devaney_sarkovskii
import Theorems.Thm_Devaney_odd_period_all_even_and_above
import Theorems.Thm_Devaney_exists_hasPrimePeriod_two

open Set Function

namespace Conn

open Devaney

theorem twoAdicVal_odd {n : ℕ} (h : Odd n) : Devaney.twoAdicVal n = 0 := by
  have hnd : ¬ (2 ∣ n) := by
    intro hdvd; rw [Nat.odd_iff] at h; omega
  exact padicValNat.eq_zero_of_not_dvd hnd

theorem oddPart_odd {n : ℕ} (h : Odd n) : Devaney.oddPart n = n := by
  have h0 := twoAdicVal_odd h
  unfold Devaney.twoAdicVal at h0
  unfold Devaney.oddPart
  rw [h0]; simp

theorem two_dvd_of_twoAdicVal_pos {l : ℕ} (h : 0 < Devaney.twoAdicVal l) : 2 ∣ l := by
  by_contra hcon
  have h0 := padicValNat.eq_zero_of_not_dvd (p := 2) hcon
  unfold Devaney.twoAdicVal at h
  omega

theorem odd_of_twoAdicVal_zero {l : ℕ} (hl : l ≠ 0) (h : Devaney.twoAdicVal l = 0) : Odd l := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff]
  by_contra hcon
  have hdvd : 2 ∣ l := by omega
  have h1 := one_le_padicValNat_of_dvd hl hdvd
  unfold Devaney.twoAdicVal at h
  omega

theorem eq_pow_of_oddPart_one {l : ℕ} (hl : l ≠ 0) (h : Devaney.oddPart l = 1) :
    l = 2 ^ Devaney.twoAdicVal l := by
  have hdvd : 2 ^ padicValNat 2 l ∣ l := pow_padicValNat_dvd
  unfold Devaney.oddPart at h
  unfold Devaney.twoAdicVal
  have hc := Nat.div_mul_cancel hdvd
  rw [h, one_mul] at hc
  exact hc.symm

/-- A fixed point, obtained from a two-cycle by the intermediate value theorem. -/
theorem exists_fixed_of_two {f : ℝ → ℝ} (hf : Continuous f) {y : ℝ}
    (h2 : HasPrimePeriod f y 2) : ∃ z, HasPrimePeriod f z 1 := by
  have hff : f (f y) = y := by have := h2.2.1; simpa using this
  have hne : f y ≠ y := by have := h2.2.2 1 one_pos (by omega); simpa using this
  have hcont : Continuous (fun t : ℝ => f t - t) := hf.sub continuous_id
  have h0 : (0:ℝ) ∈ uIcc ((fun t : ℝ => f t - t) y) ((fun t : ℝ => f t - t) (f y)) := by
    simp only [hff]
    rw [mem_uIcc]
    rcases lt_or_gt_of_ne hne with h | h <;>
      first
        | (left; constructor <;> linarith)
        | (right; constructor <;> linarith)
  obtain ⟨z, hz, hz0⟩ :=
    intermediate_value_uIcc (f := fun t : ℝ => f t - t) hcont.continuousOn h0
  have hz1 : f z - z = 0 := hz0
  exact ⟨z, one_pos, by simpa using (by linarith : f z = z),
    fun k hk hk1 => absurd hk1 (by omega)⟩

end Conn

theorem solution (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ) (hodd : Odd n) (hn : 1 < n)
    (h : ∃ x, Devaney.HasPrimePeriod f x n) (l : ℕ) (hl : Devaney.SarkovskiiPrecedes n l) :
    ∃ x, Devaney.HasPrimePeriod f x l := by
  have hpar : n % 2 = 1 := Nat.odd_iff.1 hodd
  have hn3 : 3 ≤ n := by omega
  obtain ⟨heven, hbig⟩ := Devaney.odd_period_all_even_and_above f hf n hn3 hodd h
  have hop : Devaney.oddPart n = n := Conn.oddPart_odd hodd
  have htv : Devaney.twoAdicVal n = 0 := Conn.twoAdicVal_odd hodd
  rcases hl with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
  · have hl0 : l ≠ 0 := by
      rintro rfl
      simp [Devaney.oddPart] at h2
    rcases h3 with hlt | ⟨heq, hlt⟩
    · have hdvd : 2 ∣ l := Conn.two_dvd_of_twoAdicVal_pos (by omega)
      exact heven l (by omega) (by omega)
    · have hlodd : Odd l := Conn.odd_of_twoAdicVal_zero hl0 (by omega)
      have hll : Devaney.oddPart l = l := Conn.oddPart_odd hlodd
      exact hbig l (by omega)
  · by_cases hl1 : l = 1
    · subst hl1
      obtain ⟨y, hy⟩ := Devaney.exists_hasPrimePeriod_two f hf n (by omega) h
      exact Conn.exists_fixed_of_two hf hy
    · have hl0 : l ≠ 0 := by omega
      have hlpow : l = 2 ^ Devaney.twoAdicVal l := Conn.eq_pow_of_oddPart_one hl0 h2
      have hv1 : 0 < Devaney.twoAdicVal l := by
        by_contra hcon
        have hz : Devaney.twoAdicVal l = 0 := by omega
        rw [hz, pow_zero] at hlpow
        exact hl1 hlpow
      have hdvd : 2 ∣ l := Conn.two_dvd_of_twoAdicVal_pos hv1
      exact heven l (by omega) (by omega)
  · exact absurd h1 (by omega)
