-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_dual_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:17.118808+00:00
-- url     : https://prove2.me/submissions/24cb64a6-4292-41b1-8bfa-5b3456994f17

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_UnramifiedTrace_CardFilterSubtype
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_UnramifiedTrace_card_fib_mul
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_UnramifiedTrace_exists_dual_one
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_UnramifiedTrace_card_dual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
private theorem eq_pow_sub_of_mul_pow_eq_pow {c q k n : ℕ} (hq : 1 < q) (hc : 1 ≤ c) (h : c * q ^ k = q ^ n) :
    c = q ^ (n - k) := by
  have hkn : k ≤ n := by
    by_contra hlt
    push_neg at hlt
    have h1 : q ^ n < q ^ k := Nat.pow_lt_pow_right hq hlt
    have h2 : q ^ k ≤ c * q ^ k := Nat.le_mul_of_pos_left _ hc
    omega
  have hpos : 0 < q ^ k := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h, ← pow_add, Nat.sub_add_cancel hkn]
variable {K X : Type*} [Field K] [Fintype K] [DecidableEq K] [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [Fintype (Module.Dual K X)]
end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
end

set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
variable {K X : Type*} [Field K] [Fintype K] [DecidableEq K] [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [Fintype (Module.Dual K X)]
namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
theorem _root_.solution (x : X) (hx : x ≠ 0) :
    (Finset.univ.filter (fun g : Module.Dual K X => g x = 1)).card = Fintype.card K ^ (Module.finrank K X - 1) := by
  obtain ⟨g1, hg1⟩ := exists_dual_one (K := K) x hx
  let f : Module.Dual K X →+ K :=
    { toFun := fun g => g x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hsurj : Function.Surjective f := fun c => ⟨c • g1, by simp [f, hg1]⟩
  have h : (Finset.univ.filter (fun g : Module.Dual K X => g x = 1)).card * Fintype.card K ^ 1 =
      Fintype.card K ^ Module.finrank K X := by
    rw [pow_one, ← card_dual]
    exact card_fib_mul f hsurj 1
  have hc : 1 ≤ (Finset.univ.filter (fun g : Module.Dual K X => g x = 1)).card :=
    Finset.card_pos.2 ⟨g1, by simp [hg1]⟩
  exact eq_pow_sub_of_mul_pow_eq_pow Fintype.one_lt_card hc h
end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
