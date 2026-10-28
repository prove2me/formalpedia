-- Prove2me | solution 1 for CountingMatroid.Bridge.finite_good_card_of_bad_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:20:06.040704+00:00
-- url     : https://prove2.me/submissions/f00a0a1e-e6c3-498d-a573-6d2f06ce2f01

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Bridge_list_tape_event_card

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid.Bridge

/-- Convert the source's ENNReal bad-event bound into the mission's rational
lower bound on the number of successful finite tapes. -/
theorem solution (K : ℕ) (δ : ℚ) (hδ : 0 ≤ δ)
    (good : List Bool → Prop)
    (hbad : (Set.ncard {xs : List Bool | xs.length = K ∧ ¬good xs} : ENNReal) *
      (1/2 : ENNReal)^K ≤ ENNReal.ofReal (δ : ℝ)) :
    (1-δ) * (2:ℚ)^K ≤ Nat.card {bits : Fin K → Bool // good (List.ofFn bits)} := by
  classical
  rw [list_tape_event_card] at hbad
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (show (0:ℝ) ≤ δ by exact_mod_cast hδ)] at hr
  have hq : (Nat.card {bits : Fin K → Bool // ¬good (List.ofFn bits)} : ℚ) *
      (1/2:ℚ)^K ≤ δ := by
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    exact hr
  have hb : (Nat.card {bits : Fin K → Bool // ¬good (List.ofFn bits)} : ℚ) ≤
      δ * (2:ℚ)^K := by
    apply (div_le_iff₀ (by positivity : (0:ℚ) < 2^K)).mp
    simpa [div_pow, div_eq_mul_inv] using hq
  have hc : Nat.card {bits : Fin K → Bool // good (List.ofFn bits)} +
      Nat.card {bits : Fin K → Bool // ¬good (List.ofFn bits)} = 2^K := by
    have hh := Set.ncard_add_ncard_compl {bits : Fin K → Bool | good (List.ofFn bits)}
    change Nat.card {bits : Fin K → Bool // good (List.ofFn bits)} +
      Nat.card {bits : Fin K → Bool // ¬good (List.ofFn bits)} = Nat.card (Fin K → Bool) at hh
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin] using hh
  have hcq : (Nat.card {bits : Fin K → Bool // good (List.ofFn bits)} : ℚ) +
      Nat.card {bits : Fin K → Bool // ¬good (List.ofFn bits)} = (2:ℚ)^K := by
    exact_mod_cast hc
  nlinarith
