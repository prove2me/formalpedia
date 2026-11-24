-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_dual_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:18.394515+00:00
-- url     : https://prove2.me/submissions/a4f7eb35-9ebd-4a60-8a66-0cc2ece6fccc

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
theorem _root_.solution (te x : X) (hte : te ≠ 0) (hx : x ∉ Submodule.span K {te}) :
    (Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1)).card =
      Fintype.card K ^ (Module.finrank K X - 2) := by
  have hte' : te ∉ Submodule.span K {x} := by
    intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hte (by rw [← hc, zero_smul])
    apply hx
    rw [← hc]
    exact Submodule.mem_span_singleton.2 ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
  have hq1 : Submodule.Quotient.mk (p := Submodule.span K {te}) x ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hq2 : Submodule.Quotient.mk (p := Submodule.span K {x}) te ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  obtain ⟨h2, hh2⟩ := exists_dual_one (K := K) _ hq1
  obtain ⟨h1, hh1⟩ := exists_dual_one (K := K) _ hq2
  let g2 : Module.Dual K X := h2.comp (Submodule.span K {te}).mkQ
  let g1 : Module.Dual K X := h1.comp (Submodule.span K {x}).mkQ
  have g2te : g2 te = 0 := by
    simp only [g2, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self te), map_zero]
  have g2x : g2 x = 1 := hh2
  have g1x : g1 x = 0 := by
    simp only [g1, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self x), map_zero]
  have g1te : g1 te = 1 := hh1
  let f : Module.Dual K X →+ K × K :=
    { toFun := fun g => (g te, g x), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hsurj : Function.Surjective f := by
    rintro ⟨a, b⟩
    refine ⟨a • g1 + b • g2, ?_⟩
    simp [f, g1te, g1x, g2te, g2x]
  have h : (Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1)).card *
      Fintype.card K ^ 2 = Fintype.card K ^ Module.finrank K X := by
    rw [← card_dual, sq, ← Fintype.card_prod]
    have h3 := card_fib_mul f hsurj (1, 1)
    have h4 : (Finset.univ.filter (fun g : Module.Dual K X => f g = (1, 1))) =
        Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1) := by
      ext g
      simp [f, Prod.ext_iff]
    rw [h4] at h3
    exact h3
  have hc : 1 ≤ (Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1)).card :=
    Finset.card_pos.2 ⟨g1 + g2, by simp [g1te, g1x, g2te, g2x]⟩
  exact eq_pow_sub_of_mul_pow_eq_pow Fintype.one_lt_card hc h
end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
