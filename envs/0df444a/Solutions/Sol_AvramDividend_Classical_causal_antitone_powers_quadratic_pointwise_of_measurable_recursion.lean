-- Prove2me | solution 1 for AvramDividend.Classical.causal_antitone_powers_quadratic_pointwise_of_measurable_recursion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:04:17.968978+00:00
-- url     : https://prove2.me/submissions/cf002d0b-fcbe-4b93-988f-5751be6e0be5

import Mathlib.Analysis.Convolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_causal_neumann_quadratic_convolution_successor_bound
import Theorems.Thm_AvramDividend_Classical_causal_reflected_kernel_right_interval_integrable
import Theorems.Thm_AvramDividend_Classical_causal_antitone_split_product_integrable_of_pointwise_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Causal power bounds propagate with their own split-integrability witnesses. -/
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
    (hKleftMeas : ∀ x u : ℝ, 0 < u → u < x →
      AEStronglyMeasurable (fun s : ℝ => κ (x - s))
        (volume.restrict (Ioc (0 : ℝ) u)))
    (hFrightMeas : ∀ n : ℕ, ∀ x u : ℝ, 0 < u → u < x →
      AEStronglyMeasurable (F n) (volume.restrict (Ioc u x))) :
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
      have hκInt : IntervalIntegrable (fun s : ℝ => κ (x - s)) volume u x :=
        AvramDividend.Classical.causal_reflected_kernel_right_interval_integrable
          κ x u (hKint (x - u) hxu)
      have hProd :=
        AvramDividend.Classical.causal_antitone_split_product_integrable_of_pointwise_bound
          κ (F n) x u ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1))
          hu hux (by positivity) hanti
          (fun t ht => hKnonneg t ht.le)
          (fun t ht => hFnonneg n t ht.le)
          (fun t ht => ih t ht)
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hu.le).1 (hFint n u hu.le))
          (hKleftMeas x u hu hux)
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hux.le).1 hκInt)
          (hFrightMeas n x u hu hux)
      have hbound :=
        AvramDividend.Classical.causal_neumann_quadratic_convolution_successor_bound
          n κ (F n) ρ x u hx hρ rfl hanti
          (hKint (x - u) hxu) (hKmass (x - u) hxu)
          hProd.1 hProd.2 (hFint n u hu.le) hκInt
          (fun s hs => hFnonneg n s hs.1.le)
          (fun s hs => ih s (lt_trans hu hs.1))
          (fun s hs => hKnonneg (x - s) (by linarith [hs.2]))
          (hFmass n u hu.le)
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
