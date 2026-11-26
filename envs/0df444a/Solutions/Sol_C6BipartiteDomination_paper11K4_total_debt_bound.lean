-- Prove2me | solution 1 for C6BipartiteDomination.paper11K4_total_debt_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:59.519534+00:00
-- url     : https://prove2.me/submissions/4feb41c6-1e2c-40b8-b999-719369f2dafe

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11K4Edges_subset_product
import Theorems.Thm_C6BipartiteDomination_paper11K4_left_degree_eq_two
import Theorems.Thm_C6BipartiteDomination_paper11K4_right_degree_eq_one
import Theorems.Thm_C6BipartiteDomination_paper11K4_right_resource_bound
import Theorems.Thm_C6BipartiteDomination_lemma_7_2_charge_values
import Theorems.Thm_C6BipartiteDomination_mem_paper11K4Supports
import Theorems.Thm_C6BipartiteDomination_paper11_incidence_degree_sum


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ w ∈ paper11K4Supports G D, -externalCharge G D w) ≤
      ∑ u ∈ paper11K4RightVertices G D hCan hmax,
        paper11K4Resource G D hCan hmax u := by
  classical
  let L := paper11K4Supports G D
  let R := paper11K4RightVertices G D hCan hmax
  let E := paper11K4Edges G D hCan hmax
  have hE : E ⊆ L.product R := by
    simpa [L, R, E] using paper11K4Edges_subset_product G hCan hmax
  obtain ⟨hLsum, hRsum⟩ := paper11_incidence_degree_sum L R E hE
  have hLdeg : ∀ w ∈ L, paper11LeftDegree E R w = 2 := by
    intro w hw
    simpa [L, E, R] using paper11K4_left_degree_eq_two G hCan hmax hw
  have hRdeg : ∀ u ∈ R, paper11RightDegree E L u = 1 := by
    intro u hu
    simpa [L, E, R] using paper11K4_right_degree_eq_one G hCan hmax hu
  have hLsum' : (2 * L.card : ℕ) = E.card := by
    calc
      2 * L.card = ∑ w ∈ L, (2 : ℕ) := by simp; ring
      _ = ∑ w ∈ L, paper11LeftDegree E R w := by
        apply Finset.sum_congr rfl
        intro w hw
        exact (hLdeg w hw).symm
      _ = E.card := hLsum
  have hRsum' : R.card = E.card := by
    calc
      R.card = ∑ u ∈ R, (1 : ℕ) := by simp
      _ = ∑ u ∈ R, paper11RightDegree E L u := by
        apply Finset.sum_congr rfl
        intro u hu
        exact (hRdeg u hu).symm
      _ = E.card := hRsum
  have hRcard : R.card = 2 * L.card := by omega
  have hDebt :
      (∑ w ∈ L, -externalCharge G D w) = 14 * (L.card : ℤ) := by
    calc
      _ = ∑ w ∈ L, (14 : ℤ) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hinfo := mem_paper11K4Supports G hw
        have hvalues := lemma_7_2_charge_values G hCan hmax
          hinfo.1 hinfo.2.1
        rcases hvalues with h | h | h
        · omega
        · omega
        · omega
      _ = 14 * (L.card : ℤ) := by simp; ring
  have hRes : (8 * (R.card : ℤ)) ≤
      ∑ u ∈ R, paper11K4Resource G D hCan hmax u := by
    have hpoint : ∀ u ∈ R, (8 : ℤ) ≤ paper11K4Resource G D hCan hmax u := by
      intro u hu
      simpa [R] using paper11K4_right_resource_bound G hCan hmax hu
    have hsum := Finset.sum_le_sum hpoint
    calc
      8 * (R.card : ℤ) = ∑ u ∈ R, (8 : ℤ) := by simp; ring
      _ ≤ ∑ u ∈ R, paper11K4Resource G D hCan hmax u := hsum
  have hcalc : (14 * (L.card : ℤ)) ≤ 8 * (R.card : ℤ) := by
    rw [hRcard]
    norm_num
    nlinarith [show (0 : ℤ) ≤ (L.card : ℤ) by positivity]
  calc
    (∑ w ∈ paper11K4Supports G D, -externalCharge G D w) =
        14 * (L.card : ℤ) := by simpa [L] using hDebt
    _ ≤ 8 * (R.card : ℤ) := hcalc
    _ ≤ ∑ u ∈ paper11K4RightVertices G D hCan hmax,
        paper11K4Resource G D hCan hmax u := by simpa [R] using hRes
end C6BipartiteDomination
