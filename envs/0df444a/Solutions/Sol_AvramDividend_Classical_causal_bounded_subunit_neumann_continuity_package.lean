-- Prove2me | solution 1 for AvramDividend.Classical.causal_bounded_subunit_neumann_continuity_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:13:06.302334+00:00
-- url     : https://prove2.me/submissions/7893afe9-98d6-4211-8ac0-aa7dbca25720

import Theorems.Thm_AvramDividend_Classical_causal_positive_convolution_powers_geometric_truncated_mass
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_continuous_of_bounded_kernel
import Theorems.Thm_AvramDividend_Classical_causal_continuous_product_integrable_full
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_comm_all_real
import Theorems.Thm_AvramDividend_Classical_causal_power_sup_geometric_from_truncated_mass
import Theorems.Thm_AvramDividend_Classical_causal_neumann_series_continuous_of_uniform_geometric_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- A bounded subunit positive kernel has continuous convergent renewal powers. -/
theorem solution
    (κ : ℝ → ℝ) (ρ : ℝ)
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκcont : Continuous κ)
    (hκbounded : BddAbove (Set.range (fun x : ℝ => ‖κ x‖)))
    (hκi : IntegrableOn κ (Ioi (0 : ℝ)) volume)
    (hκpos : ∀ x : ℝ, 0 ≤ κ x)
    (hκmass : (∫ x in Ioi (0 : ℝ), κ x ∂volume) = ρ)
    (hρpos : 0 < ρ) (hρlt : ρ < 1) :
    ∃ F : ℕ → ℝ → ℝ,
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
          κ s * F n (x - s) ∂volume) ∧
      (∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) ∧
      (∀ n : ℕ, Continuous (F n)) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → F n x = 0) ∧
      (∀ x : ℝ, Summable (fun n : ℕ => F n x)) ∧
      ContinuousOn (fun x : ℝ => ∑' n : ℕ, F n x) (Ici 0) := by
  obtain ⟨F, hF0, hFsucc, hFi, hFnonneg, hFmass⟩ :=
    causal_positive_convolution_powers_geometric_truncated_mass
      κ hκi (fun x _ => hκpos x)
  have hFzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → F n x = 0 := by
    intro n
    induction n with
    | zero =>
        intro x hx
        rw [hF0]
        exact hκzero x hx
    | succ n _ =>
        intro x hx
        rw [hFsucc]
        have hempty : Ioc (0 : ℝ) x = ∅ := Ioc_eq_empty_of_le hx
        simp [hempty]
  have hFpos (n : ℕ) (x : ℝ) : 0 ≤ F n x := by
    by_cases hx : 0 ≤ x
    · exact hFnonneg n x hx
    · simp [hFzero n x (le_of_lt (lt_of_not_ge hx))]
  have hFcont : ∀ n : ℕ, Continuous (F n) :=
    causal_Ioc_convolution_powers_continuous_of_bounded_kernel
      κ F hκzero hκcont hκbounded hF0 hFsucc hFi
  rcases hκbounded with ⟨B₀, hB₀⟩
  let B : ℝ := max B₀ 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hκabs (x : ℝ) : |κ x| ≤ B := by
    calc
      |κ x| = ‖κ x‖ := (Real.norm_eq_abs _).symm
      _ ≤ B₀ := hB₀ ⟨x, rfl⟩
      _ ≤ B := le_max_left _ _
  have hκle (x : ℝ) : κ x ≤ B :=
    (le_abs_self _).trans (hκabs x)
  have hFrev (n : ℕ) (x : ℝ) :
      F (n + 1) x =
        ∫ s in Ioc (0 : ℝ) x, κ (x - s) * F n s ∂volume := by
    calc
      F (n + 1) x =
          ∫ s in Ioc (0 : ℝ) x, κ s * F n (x - s) ∂volume :=
        congrFun (hFsucc n) x
      _ = ∫ s in Ioc (0 : ℝ) x, F n s * κ (x - s) ∂volume :=
        causal_Ioc_convolution_comm_all_real κ (F n) x
      _ = ∫ s in Ioc (0 : ℝ) x, κ (x - s) * F n s ∂volume := by
        congr 1
        funext s
        ring
  have hFprod (n : ℕ) (x : ℝ) :
      IntegrableOn (fun s : ℝ => κ (x - s) * F n s)
        (Ioc (0 : ℝ) x) volume := by
    have hi := causal_continuous_product_integrable_full
      (F n) κ (hFcont n) hκcont
      (fun y hy => hFzero n y (le_of_lt hy))
      (fun y hy => hκzero y (le_of_lt hy)) x
    have hi' : Integrable (fun s : ℝ => κ (x - s) * F n s) volume := by
      simpa only [mul_comm] using hi
    exact hi'.integrableOn
  have hFIoc (n : ℕ) (x : ℝ) :
      IntegrableOn (F n) (Ioc (0 : ℝ) x) volume :=
    (hFi n).mono_set (by intro y hy; exact hy.1)
  have hFmass' (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
      (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) ≤ ρ ^ (n + 1) := by
    simpa only [hκmass] using hFmass n x hx
  have hFsup :=
    causal_power_sup_geometric_from_truncated_mass
      κ F B ρ (le_of_lt hBpos) hκle hFnonneg hFrev
      hFprod hFIoc hFmass'
  have hFbound (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
      |F n x| ≤ B * ρ ^ n := by
    cases n with
    | zero =>
        simpa [hF0] using hκabs x
    | succ n =>
        rw [abs_of_nonneg (hFnonneg (n + 1) x hx)]
        exact hFsup n x hx
  have hFseries :=
    causal_neumann_series_continuous_of_uniform_geometric_bound
      F B ρ hBpos hρpos hρlt
      (fun n => (hFcont n).continuousOn) hFbound
  have hFsum (x : ℝ) : Summable (fun n : ℕ => F n x) := by
    by_cases hx : 0 ≤ x
    · exact hFseries.2 x hx
    · have hz (n : ℕ) : F n x = 0 :=
        hFzero n x (le_of_lt (lt_of_not_ge hx))
      simpa only [hz] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  exact ⟨F, hF0, hFsucc, hFi, hFcont, hFpos, hFzero,
    hFsum, hFseries.1⟩