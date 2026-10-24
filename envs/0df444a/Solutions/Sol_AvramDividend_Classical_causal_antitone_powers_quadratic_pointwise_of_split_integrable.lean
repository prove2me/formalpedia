-- Prove2me | solution 1 for AvramDividend.Classical.causal_antitone_powers_quadratic_pointwise_of_split_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:53:39.340358+00:00
-- url     : https://prove2.me/submissions/daafde7f-e346-4928-9526-bf0274c6e27d

import Mathlib.Analysis.Convolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_causal_neumann_quadratic_convolution_successor_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set

/-- Under split-interval integrability, the quadratic causal-power estimate propagates by induction. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hKpoint : ∀ x : ℝ, 0 < x → κ x ≤ ρ / x)
    (hKnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ κ t)
    (hKint : ∀ y : ℝ, 0 < y → IntervalIntegrable κ volume 0 y)
    (hKmass : ∀ y : ℝ, 0 < y → (∫ t in (0 : ℝ)..y, κ t) ≤ ρ)
    (hzero : F 0 = κ)
    (hsucc : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      F (n + 1) x = ∫ s in Ioc (0 : ℝ) x, κ (x - s) * F n s ∂volume)
    (hFnonneg : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ F n t)
    (hFint : ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u → IntervalIntegrable (F n) volume 0 u)
    (hFmass : ∀ n : ℕ, ∀ u : ℝ, 0 ≤ u →
      (∫ s in (0 : ℝ)..u, F n s) ≤ ρ ^ (n + 1))
    (hKrightInt : ∀ x u : ℝ, 0 < u → u < x →
      IntervalIntegrable (fun s : ℝ => κ (x - s)) volume u x)
    (hProdInt : ∀ n : ℕ, ∀ x u : ℝ, 0 < u → u < x →
      IntervalIntegrable (fun s : ℝ => κ (x - s) * F n s) volume 0 u ∧
      IntervalIntegrable (fun s : ℝ => κ (x - s) * F n s) volume u x) :
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x := by
  intro n
  induction n with
  | zero =>
      intro x hx
      rw [hzero]
      simpa using hKpoint x hx
  | succ n ih =>
      intro x hx
      let u : ℝ := ((n + 1 : ℝ) / (n + 2 : ℝ)) * x
      have hn1 : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      have hn2 : (0 : ℝ) < (n + 2 : ℝ) := by positivity
      have hu : 0 < u := mul_pos (div_pos hn1 hn2) hx
      have hsep : x - u = x / (n + 2 : ℝ) := by
        dsimp [u]
        field_simp
        ring
      have hxu : 0 < x - u := by
        rw [hsep]
        exact div_pos hx hn2
      have hux : u < x := by linarith
      have hFright : ∀ s ∈ Ioo u x,
          F n s ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / s := by
        intro s hs
        exact ih s (lt_trans hu hs.1)
      have hκright : ∀ s ∈ Ioo u x, 0 ≤ κ (x - s) := by
        intro s hs
        exact hKnonneg (x - s) (by linarith [hs.2])
      have hbound :=
        AvramDividend.Classical.causal_neumann_quadratic_convolution_successor_bound
          n κ (F n) ρ x u hx hρ rfl hanti
          (hKint (x - u) hxu) (hKmass (x - u) hxu)
          (hProdInt n x u hu hux).1 (hProdInt n x u hu hux).2
          (hFint n u hu.le) (hKrightInt x u hu hux)
          (fun s hs => hFnonneg n s hs.1.le)
          hFright hκright (hFmass n u hu.le)
      have hrec : F (n + 1) x =
          ∫ s in (0 : ℝ)..x, κ (x - s) * F n s := by
        rw [hsucc n x hx.le]
        rw [intervalIntegral.integral_of_le hx.le]
      rw [hrec]
      have hnat : Nat.succ n + 1 = n + 2 := by
        rw [Nat.succ_eq_add_one]
      have hreal : ((Nat.succ n : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by
        rw [Nat.cast_succ]
        ring
      simpa only [hnat, hreal] using hbound
