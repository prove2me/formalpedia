-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FrobP.coeff_pow_char_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:08:34.250365+00:00
-- url     : https://prove2.me/submissions/c1d49514-7fa3-455d-a211-8be8a323940d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffPowCharFrobenius
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_frob_ser
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open ValuationNonnegativity
open Formalism.L2.FormalSeriesBounds.FrobP
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.FrobP
theorem _root_.solution : ∀ (m : ℕ) (f : PowerSeries C), (∀ n, V.Ge 0 (PowerSeries.coeff n f)) →
    V.MM (PowerSeries.coeff m (f ^ V.l) - if V.l ∣ m then PowerSeries.coeff (m / V.l) f ^ V.l else 0) := by
  have hl := V.l_prime
  have hl0 : 0 < V.l := hl.pos
  have mm_add : ∀ x y : C, V.MM x → V.MM y → V.MM (x + y) := fun x y hx hy => by
    unfold VF.MM at *
    exact lt_of_lt_of_le (lt_min hx hy) (AddValuation.map_add _ _ _)
  have mm_zero : V.MM (0 : C) := by
    unfold VF.MM
    rw [AddValuation.map_zero]
    exact WithTop.coe_lt_top 0
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro f hf
  set a := PowerSeries.constantCoeff f with ha
  set g := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) f with hgdef
  have hfg : f = PowerSeries.C a + PowerSeries.X * g := by
    ext n
    cases n with
    | zero => simp [a, g]
    | succ k => simp [g, PowerSeries.coeff_succ_X_mul]
  have hCa : ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.C a)) := by
    intro n
    rw [PowerSeries.coeff_C]
    split_ifs
    · have := hf 0
      simpa [a] using this
    · unfold VF.Ge
      rw [AddValuation.map_zero]
      exact le_top
  have hg : ∀ n, V.Ge 0 (PowerSeries.coeff n g) := fun n => by simpa [g] using hf (n + 1)
  have hXg : ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.X * g)) := by
    intro n
    cases n with
    | zero =>
      unfold VF.Ge
      simp [AddValuation.map_zero]
    | succ k =>
      rw [PowerSeries.coeff_succ_X_mul]
      exact hg k
  have hfr := frob_ser hCa hXg m
  rw [← hfg, map_sub, map_sub] at hfr
  have e1 : PowerSeries.coeff m (PowerSeries.C a ^ V.l) = if m = 0 then a ^ V.l else 0 := by
    rw [← map_pow, PowerSeries.coeff_C]
  have e2 : PowerSeries.coeff m ((PowerSeries.X * g) ^ V.l) =
      if V.l ≤ m then PowerSeries.coeff (m - V.l) (g ^ V.l) else 0 := by
    rw [mul_pow, PowerSeries.coeff_X_pow_mul']
  have hsec : V.MM (PowerSeries.coeff m (PowerSeries.C a ^ V.l) + PowerSeries.coeff m ((PowerSeries.X * g) ^ V.l) -
      if V.l ∣ m then PowerSeries.coeff (m / V.l) f ^ V.l else 0) := by
    rw [e1, e2]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      have hnl : ¬ V.l ≤ 0 := by omega
      simp only [if_true, hnl, if_false, add_zero, dvd_zero, Nat.zero_div]
      rw [show PowerSeries.coeff 0 f = a by simp [a], sub_self]
      exact mm_zero
    · by_cases hlm : V.l ≤ m
      · have hm0 : m ≠ 0 := by omega
        have hdiv : (V.l ∣ m) ↔ (V.l ∣ m - V.l) := by
          constructor
          · intro h; exact Nat.dvd_sub h (dvd_refl _)
          · intro h
            have := Nat.dvd_add h (dvd_refl V.l)
            rwa [Nat.sub_add_cancel hlm] at this
        have hq : m / V.l = (m - V.l) / V.l + 1 := Nat.div_eq_sub_div hl0 hlm
        have hih := ih (m - V.l) (by omega) g hg
        simp only [hm0, if_false, hlm, if_true, zero_add]
        have e3 : (if V.l ∣ m then PowerSeries.coeff (m / V.l) f ^ V.l else 0) =
            if V.l ∣ m - V.l then PowerSeries.coeff ((m - V.l) / V.l) g ^ V.l else 0 := by
          by_cases h : V.l ∣ m
          · rw [if_pos h, if_pos (hdiv.1 h), hq]
            simp [g]
          · rw [if_neg h, if_neg (fun h' => h (hdiv.2 h'))]
        rw [e3]
        exact hih
      · have hm0 : m ≠ 0 := by omega
        have hnd : ¬ V.l ∣ m := fun h => hlm (Nat.le_of_dvd hpos h)
        simp only [hm0, if_false, hlm, hnd, add_zero, sub_self]
        exact mm_zero
  have h := mm_add _ _ hfr hsec
  convert h using 1
  ring
end Formalism.L2.FormalSeriesBounds.FrobP
