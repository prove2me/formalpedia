-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.comb_du
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:58.259528+00:00
-- url     : https://prove2.me/submissions/e1d67b59-e858-4c4a-94f9-a96a2a1114f8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_UnramifiedTrace_SumFib
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_UnramifiedTrace_sum_fib

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
theorem _root_.solution {K X PD PE : Type*} [Field K] [Fintype K] [DecidableEq K] [AddCommGroup X] [Module K X] [Fintype X]
    [DecidableEq X] {iPD : Fintype PD} {iPE : Fintype PE} (te : X) (hte0 : te ≠ 0) (Tn n1 n2 : ℕ) (hTn : Tn ≠ 0)
    (πD : PD → X) (πE : PE → X) (VD : PD → ℂ) (VE : PE → ℂ) (Φ : ℂ) (Dl : Kˣ → ℂ) (τ : Kˣ ≃ Kˣ)
    (hcE : ∀ x, (Finset.univ.filter (fun q => πE q = x)).card = if x = 0 then 0 else Tn ^ n1)
    (hcD : ∀ x, (Finset.univ.filter (fun p => πD p = x)).card =
      if x = te then Tn ^ n1 else if x ∈ Submodule.span K {te} then 0 else Tn ^ n2)
    (hself : ∀ p, πD p = te → VD p = Φ)
    (hDE : ∀ p q, πD p = πE q → VD p = VE q)
    (hEE : ∀ p q, πE p = πE q → VE p = VE q)
    (hline : ∀ (a : Kˣ) q, πE q = (a : K) • te → VE q = Dl (τ a)) :
    ∑ p, VD p = (Tn : ℂ) ^ n1 * Φ - (Tn : ℂ) ^ n2 * ∑ a, Dl a + (Tn : ℂ) ^ n2 * (((Tn : ℂ) ^ n1)⁻¹ * ∑ p, VE p) := by
  have hTn' : (0 : ℕ) < Tn ^ n1 := pow_pos (Nat.pos_of_ne_zero hTn) _
  have hA : ((Tn : ℂ) ^ n1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hTn)
  have hfibE : ∀ x : X, x ≠ 0 → ∃ q, πE q = x := by
    intro x hx
    have hc : 0 < (Finset.univ.filter (fun q => πE q = x)).card := by rw [hcE x, if_neg hx]; exact hTn'
    obtain ⟨q, hq⟩ := Finset.card_pos.1 hc
    exact ⟨q, (Finset.mem_filter.1 hq).2⟩
  obtain ⟨wE, hwE⟩ : ∃ wE : X → ℂ, ∀ q, VE q = wE (πE q) :=
    ⟨fun x => if h : ∃ q, πE q = x then VE h.choose else 0, fun q => by
      have h : ∃ q', πE q' = πE q := ⟨q, rfl⟩
      simp only [dif_pos h]
      exact hEE _ _ h.choose_spec.symm⟩
  have hVD : ∀ p, VD p = (if πD p = te then Φ else wE (πD p)) := by
    intro p
    split_ifs with h
    · exact hself p h
    · have h0 : πD p ≠ 0 := by
        intro h0
        have hc := hcD 0
        rw [if_neg (Ne.symm hte0), if_pos (Submodule.zero_mem _)] at hc
        have hm : p ∈ Finset.univ.filter (fun p => πD p = 0) := Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩
        rw [Finset.card_eq_zero.1 hc] at hm
        simp at hm
      obtain ⟨q, hq⟩ := hfibE _ h0
      rw [hDE p q hq.symm, hwE q, hq]
  have hD0 : ∑ p, VD p = ∑ x, ((Finset.univ.filter (fun p => πD p = x)).card : ℂ) *
      (if x = te then Φ else wE x) := sum_fib πD VD _ hVD
  have hE0 : ∑ q, VE q = ∑ x, ((Finset.univ.filter (fun q => πE q = x)).card : ℂ) * wE x :=
    sum_fib πE VE wE hwE
  have e1 : ∀ x : X, ((Finset.univ.filter (fun p => πD p = x)).card : ℂ) * (if x = te then Φ else wE x) =
      (if x = te then (Tn : ℂ) ^ n1 * Φ else 0) +
        (Tn : ℂ) ^ n2 * (if x ∈ Submodule.span K {te} then 0 else wE x) := by
    intro x
    rw [hcD x]
    by_cases h1 : x = te
    · subst h1; simp [Submodule.mem_span_singleton_self]
    · by_cases h2 : x ∈ Submodule.span K {te} <;> simp [h1, h2]
  have e2 : ∀ x : X, ((Finset.univ.filter (fun q => πE q = x)).card : ℂ) * wE x =
      (Tn : ℂ) ^ n1 * ((if x ∈ Submodule.span K {te} then 0 else wE x) +
        (if x ∈ Submodule.span K {te} ∧ x ≠ 0 then wE x else 0)) := by
    intro x
    rw [hcE x]
    by_cases h1 : x = 0
    · subst h1; simp
    · by_cases h2 : x ∈ Submodule.span K {te} <;> simp [h1, h2]
  have hD1 : ∑ x, ((Finset.univ.filter (fun p => πD p = x)).card : ℂ) * (if x = te then Φ else wE x) =
      (Tn : ℂ) ^ n1 * Φ + (Tn : ℂ) ^ n2 * ∑ x : X, (if x ∈ Submodule.span K {te} then 0 else wE x) := by
    rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hE1 : ∑ x, ((Finset.univ.filter (fun q => πE q = x)).card : ℂ) * wE x =
      (Tn : ℂ) ^ n1 * (∑ x : X, (if x ∈ Submodule.span K {te} then 0 else wE x) +
        ∑ x : X, (if x ∈ Submodule.span K {te} ∧ x ≠ 0 then wE x else 0)) := by
    rw [Finset.sum_congr rfl (fun x _ => e2 x), ← Finset.mul_sum, Finset.sum_add_distrib]
  have hS2 : ∑ x : X, (if x ∈ Submodule.span K {te} ∧ x ≠ 0 then wE x else 0) = ∑ a, Dl a := by
    rw [← Finset.sum_filter, ← Equiv.sum_comp τ Dl]
    symm
    refine Finset.sum_bij (fun a _ => (a : K) • te) ?_ ?_ ?_ ?_
    · intro a _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self te), smul_ne_zero a.ne_zero hte0⟩
    · intro a _ b _ h
      exact Units.ext (smul_left_injective K hte0 h)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx.1
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hx.2 (by rw [← hc, zero_smul])
      exact ⟨Units.mk0 c hc0, Finset.mem_univ _, by simp [hc]⟩
    · intro a _
      obtain ⟨q, hq⟩ := hfibE _ (smul_ne_zero a.ne_zero hte0)
      rw [← hq, ← hwE q, hline a q hq]
  rw [hD0, hD1, hE0, hE1, hS2, inv_mul_cancel_left₀ hA]
  ring
end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
