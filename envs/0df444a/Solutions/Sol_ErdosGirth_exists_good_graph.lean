-- Prove2me | solution 1 for ErdosGirth.exists_good_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:35:54.315148+00:00
-- url     : https://prove2.me/submissions/1d9569fa-1c33-442a-bb13-d3127e6f0f51

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Theorems.Thm_ErdosGirth_wt_nonneg
public import Theorems.Thm_ErdosGirth_sum_wt
public import Theorems.Thm_ErdosGirth_expected_cyc_le
public import Theorems.Thm_ErdosGirth_expected_indep
public import Theorems.Thm_ErdosGirth_disjoint_of_isIndepSet
public import Theorems.Thm_ErdosGirth_cyc_nonneg
public import Theorems.Thm_ErdosGirth_indep_nonneg
public import Theorems.Thm_ErdosGirth_one_le_cyc

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
open Classical
namespace ErdosGirth
theorem _root_.solution (m g t : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hm : 0 < m)
    (h : 2 / m * ∑ ℓ ∈ range (g + 1), ((m : ℝ) * p) ^ ℓ + m.choose t * (1 - p) ^ t.choose 2 < 1) :
    ∃ G : SimpleGraph (Fin m), ∃ D : Finset (Fin m), 2 * D.card < m ∧
      (∀ u (c : G.Walk u u), c.IsCycle → c.length ≤ g → u ∈ D) ∧
      ∀ T : Finset (Fin m), T.card = t → ¬ G.IsIndepSet (T : Set (Fin m)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set Z : Finset (Sym2 (Fin m)) → ℝ := fun S => 2 / m * ∑ u, cyc m g S u + indep m t S with hZ
  have hEZ : ∑ S ∈ (pairs m).powerset, wt m p S * Z S < 1 := by
    calc ∑ S ∈ (pairs m).powerset, wt m p S * Z S
        = 2 / m * ∑ S ∈ (pairs m).powerset, wt m p S * ∑ u, cyc m g S u
          + ∑ S ∈ (pairs m).powerset, wt m p S * indep m t S := by
          rw [mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun S _ => ?_
          rw [hZ]; ring
      _ ≤ 2 / m * ∑ ℓ ∈ range (g + 1), ((m : ℝ) * p) ^ ℓ + m.choose t * (1 - p) ^ t.choose 2 := by
          rw [expected_indep]
          gcongr
          exact expected_cyc_le g hp0
      _ < 1 := h
  obtain ⟨S, -, hS⟩ : ∃ S ∈ (pairs m).powerset, Z S < 1 := by
    by_contra hcon
    push Not at hcon
    have : ∑ S ∈ (pairs m).powerset, wt m p S * 1 ≤ ∑ S ∈ (pairs m).powerset, wt m p S * Z S :=
      sum_le_sum fun S hS => mul_le_mul_of_nonneg_left (hcon S hS) (wt_nonneg hp0 hp1 S)
    simp only [mul_one, sum_wt] at this
    linarith
  have hcyc0 : 0 ≤ ∑ u, cyc m g S u := sum_nonneg fun u _ => cyc_nonneg S u
  have hind0 := indep_nonneg (t := t) S
  have h2 : 0 ≤ 2 / (m : ℝ) * ∑ u, cyc m g S u := by positivity
  simp only [hZ] at hS
  refine ⟨gr S, univ.filter (fun u => ∃ c : (gr S).Walk u u, c.IsCycle ∧ c.length ≤ g), ?_,
    fun u c hc hl => mem_filter.mpr ⟨mem_univ _, c, hc, hl⟩, fun T hT hTi => ?_⟩
  · have hD : ((univ.filter (fun u => ∃ c : (gr S).Walk u u, c.IsCycle ∧ c.length ≤ g)).card : ℝ)
        ≤ ∑ u, cyc m g S u := by
      rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      calc _ ≤ ∑ u ∈ univ.filter (fun u => ∃ c : (gr S).Walk u u, c.IsCycle ∧ c.length ≤ g),
            cyc m g S u := by
            refine sum_le_sum fun u hu => ?_
            obtain ⟨c, hc, hl⟩ := (mem_filter.mp hu).2
            exact one_le_cyc c hc hl
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun u _ _ => cyc_nonneg S u
    have : 2 / (m : ℝ) * ∑ u, cyc m g S u < 1 := by linarith
    rw [div_mul_eq_mul_div, div_lt_one hm'] at this
    have h3 : (2 : ℝ) * ((univ.filter
        (fun u => ∃ c : (gr S).Walk u u, c.IsCycle ∧ c.length ≤ g)).card : ℝ) < m := by linarith
    exact_mod_cast h3
  · have : (1 : ℝ) ≤ indep m t S := by
      refine le_trans ?_ (single_le_sum (f := fun T : Finset (Fin m) =>
        if Disjoint (edgesIn T) S then (1 : ℝ) else 0) (fun _ _ => by split_ifs <;> norm_num)
        (mem_powersetCard.mpr ⟨subset_univ T, hT⟩))
      simp [disjoint_of_isIndepSet hTi]
    linarith
end ErdosGirth
