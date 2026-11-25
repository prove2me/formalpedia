-- Prove2me | solution 1 for ErdosGirth.exists_girth_not_colorable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:38:55.530271+00:00
-- url     : https://prove2.me/submissions/6eaaf705-cda0-40fb-9250-67124a0c9910

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Definitions.Def_GirthLib_ErdosGirth
public import Theorems.Thm_ErdosGirth_exists_girth_indep

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution (g k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n), (g : ℕ∞) < G.egirth ∧ ¬ G.Colorable k := by
  obtain ⟨N, hN⟩ := exists_girth_indep g (ε := 1 / (k + 1)) (by positivity)
  refine ⟨max N 1, fun n hn => ?_⟩
  obtain ⟨G, hG, hind⟩ := hN n (le_of_max_le_left hn)
  refine ⟨G, hG, fun ⟨C⟩ => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hcls : ∀ c : Fin k,
      ((univ.filter (fun v => C v = c)).card : ℝ) < 1 / (k + 1) * n := by
    intro c
    refine hind _ ?_
    intro x hx y hy _ hadj
    simp only [coe_filter, mem_univ, true_and] at hx hy
    exact C.valid hadj (hx.trans hy.symm)
  have hsum : (n : ℝ) = ∑ c : Fin k, ((univ.filter (fun v => C v = c)).card : ℝ) := by
    have := card_eq_sum_card_fiberwise (f := C) (s := univ) (t := univ) (fun _ _ => mem_univ _)
    rw [card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have hle : (n : ℝ) ≤ k * (1 / (k + 1) * n) := by
    calc (n : ℝ) = _ := hsum
      _ ≤ ∑ _c : Fin k, 1 / ((k : ℝ) + 1) * n := sum_le_sum fun c _ => (hcls c).le
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hk : (k : ℝ) * (1 / (k + 1) * n) < n := by
    rw [← mul_assoc, mul_one_div]
    have hk0 : (0 : ℝ) < k + 1 := by positivity
    have : (k : ℝ) / (k + 1) < 1 := by rw [div_lt_one hk0]; linarith
    nlinarith
  linarith
end ErdosGirth
