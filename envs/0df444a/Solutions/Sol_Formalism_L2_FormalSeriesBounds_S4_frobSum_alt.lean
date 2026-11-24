-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.frobSum_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:11:00.024063+00:00
-- url     : https://prove2.me/submissions/ea16e6ae-f97d-4484-ae6d-a61652d6a0a6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_parity_of_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (big : ZMod d → Prop)
    (halt : ∀ b, big (b + 1) ↔ ¬ big b) (p : ZMod d → ℕ)
    (hpb : ∀ b, big b → p b = n + j) (hps : ∀ b, ¬ big b → p b = j')
    (a : ZMod d) (ha : big a) :
    frobSum l p a = (j' : ℝ) * gam l + ((n : ℝ) + j) * rho l := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl
  have hlne : (l : ℝ) ≠ 0 := by positivity
  have h3 : (l : ℝ) ^ 2 - 1 ≠ 0 := by
    intro h
    nlinarith
  have hq0 : (0 : ℝ) ≤ ((l : ℝ)⁻¹) ^ 2 := by positivity
  have hq1 : ((l : ℝ)⁻¹) ^ 2 < 1 := pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl1) two_ne_zero
  have hpar := parity_of_alt big halt a ha
  have hval : ∀ k : ℕ, (p (a + ((k + 1 : ℕ) : ZMod d)) : ℝ) = if Even k then (j' : ℝ) else (n : ℝ) + j := by
    intro k
    by_cases hk : Even k
    · have hb : ¬ big (a + ((k + 1 : ℕ) : ZMod d)) := by
        rw [hpar, Nat.even_add_one]
        exact not_not.mpr hk
      rw [hps _ hb, if_pos hk]
    · have hb : big (a + ((k + 1 : ℕ) : ZMod d)) := by
        rw [hpar, Nat.even_add_one]
        exact hk
      rw [hpb _ hb, if_neg hk]
      push_cast
      ring
  have hF : (fun k : ℕ => ((l : ℝ) ^ (k + 1))⁻¹ * (p (a + ((k + 1 : ℕ) : ZMod d)) : ℝ)) =
      fun k => ((l : ℝ) ^ (k + 1))⁻¹ * (if Even k then (j' : ℝ) else (n : ℝ) + j) :=
    funext fun k => by rw [hval]
  have hev : ∀ m : ℕ, ((l : ℝ) ^ (2 * m + 1))⁻¹ * (if Even (2 * m) then (j' : ℝ) else (n : ℝ) + j) =
      ((j' : ℝ) * (l : ℝ)⁻¹) * (((l : ℝ)⁻¹) ^ 2) ^ m := by
    intro m
    rw [if_pos (even_two_mul m), ← inv_pow, pow_succ, pow_mul]
    ring
  have hod : ∀ m : ℕ, ((l : ℝ) ^ (2 * m + 1 + 1))⁻¹ * (if Even (2 * m + 1) then (j' : ℝ) else (n : ℝ) + j) =
      (((n : ℝ) + j) * ((l : ℝ)⁻¹) ^ 2) * (((l : ℝ)⁻¹) ^ 2) ^ m := by
    intro m
    rw [if_neg (Nat.not_even_two_mul_add_one m), ← inv_pow, pow_succ, pow_succ, pow_mul]
    ring
  have hs := summable_geometric_of_lt_one hq0 hq1
  unfold frobSum
  rw [hF, ← tsum_even_add_odd (f := fun k : ℕ => ((l : ℝ) ^ (k + 1))⁻¹ * (if Even k then (j' : ℝ) else (n : ℝ) + j))
    (by simp only [hev]; exact hs.mul_left _) (by simp only [hod]; exact hs.mul_left _)]
  simp only [hev, hod, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  unfold gam rho
  field_simp
  try ring
end Formalism.L2.FormalSeriesBounds.S4
