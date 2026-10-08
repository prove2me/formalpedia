-- Prove2me | solution 1 for ChenBullwhip.Centralized.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T12:35:58.069894+00:00
-- url     : https://prove2.me/submissions/9ba55fbb-2b2d-41fe-9910-e662b79637ff

import Mathlib
import Definitions.Def_ChenBullwhip_Centralized_AR1Demand
import Definitions.Def_ChenBullwhip_Centralized_Policy

set_option autoImplicit false

namespace ChenBullwhipEq4Aux

theorem tele (f : ℕ → ℝ) : ∀ p : ℕ,
    ∑ i ∈ Finset.Icc 1 p, (f i - f (i + 1)) = f 1 - f (p + 1) := by
  intro p
  induction p with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

end ChenBullwhipEq4Aux

open ChenBullwhip.Centralized in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    (X : AR1Demand P) (C z : ℝ) (L p : ℕ) (hp : 1 ≤ p) (t : ℤ) (ω : Ω) :
    X.order C z L p t ω
        = (L : ℝ) * ((X.D (t - 1) ω - X.D (t - p - 1) ω) / p) + X.D (t - 1) ω
          + z * (X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω)
      ∧ X.order C z L p t ω
        = (1 + (L : ℝ) / p) * X.D (t - 1) ω - ((L : ℝ) / p) * X.D (t - p - 1) ω
          + z * (X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω) := by
  have hsum : (∑ i ∈ Finset.Icc 1 p, X.D (t - i) ω)
      - (∑ i ∈ Finset.Icc 1 p, X.D (t - 1 - i) ω) = X.D (t - 1) ω - X.D (t - p - 1) ω := by
    rw [← Finset.sum_sub_distrib]
    have h := ChenBullwhipEq4Aux.tele (fun i : ℕ => X.D (t - i) ω) p
    try simp only at h
    have e1 : ∀ i ∈ Finset.Icc 1 p, X.D (t - i) ω - X.D (t - 1 - i) ω
        = X.D (t - (i : ℕ)) ω - X.D (t - ((i + 1 : ℕ) : ℤ)) ω := by
      intro i _
      congr 2
      push_cast; ring
    rw [Finset.sum_congr rfl e1, h]
    congr 2
    all_goals (push_cast; ring)
  have hp' : (p : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have key : X.order C z L p t ω
      = (L : ℝ) * ((X.D (t - 1) ω - X.D (t - p - 1) ω) / p) + X.D (t - 1) ω
          + z * (X.sigmaHat C p t ω - X.sigmaHat C p (t - 1) ω) := by
    unfold AR1Demand.order AR1Demand.orderUpTo AR1Demand.Dhat
    rw [← hsum]
    field_simp
    ring
  refine ⟨key, ?_⟩
  rw [key]
  field_simp
  ring
