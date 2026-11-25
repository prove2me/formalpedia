-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FrobP.not_mm_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:12.059743+00:00
-- url     : https://prove2.me/submissions/e58ed55f-2a02-4acb-bf1a-fb2a3b897cb8

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffPowCharFrobenius
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_ge_intCast

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
theorem _root_.solution {m : ℕ} (hm : ¬ V.l ∣ m) : ¬ V.MM (m : C) := by
  intro h
  have hcop : Nat.Coprime V.l m := (Nat.Prime.coprime_iff_not_dvd V.l_prime).mpr hm
  have hA := ge_intCast (V := V) (Nat.gcdA V.l m)
  have hB := ge_intCast (V := V) (Nat.gcdB V.l m)
  unfold VF.Ge at hA hB
  rw [WithTop.coe_zero] at hA hB
  unfold VF.MM at h
  have h0 := Nat.gcd_eq_gcd_ab V.l m
  rw [Nat.Coprime.gcd_eq_one hcop] at h0
  have hsum := congrArg (fun z : ℤ => (z : C)) h0
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_one, Int.cast_one] at hsum
  have h1 : (0 : WithTop ℝ) < V.v ((V.l : C) * ((Nat.gcdA V.l m : ℤ) : C)) := by
    rw [AddValuation.map_mul, V.v_l]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right hA)
  have h2 : (0 : WithTop ℝ) < V.v ((m : C) * ((Nat.gcdB V.l m : ℤ) : C)) := by
    rw [AddValuation.map_mul]
    exact lt_of_lt_of_le h (le_add_of_nonneg_right hB)
  have hmin := AddValuation.map_add V.v ((V.l : C) * ((Nat.gcdA V.l m : ℤ) : C)) ((m : C) * ((Nat.gcdB V.l m : ℤ) : C))
  rw [← hsum, AddValuation.map_one] at hmin
  exact absurd hmin (not_le.mpr (lt_min h1 h2))
end Formalism.L2.FormalSeriesBounds.FrobP
