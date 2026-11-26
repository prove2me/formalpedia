-- Prove2me | solution 1 for C6BipartiteDomination.paper11_pure_k3_charge_balance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:03:58.29914+00:00
-- url     : https://prove2.me/submissions/3553942c-0197-45ba-a100-c1f24f687708

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_paper11_incidence_degree_sum

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace C6BipartiteDomination
theorem _root_.solution
    (L R : Finset V) (E : Finset (V × V))
    (hE : E ⊆ L.product R)
    (debt : V → ℤ) (resource : V → ℤ)
    (hLdegree : ∀ w ∈ L,
      paper11LeftDegree E R w = 1 ∨ paper11LeftDegree E R w = 2)
    (hRdegree : ∀ u ∈ R,
      paper11RightDegree E L u = 1 ∨ paper11RightDegree E L u = 2)
    (hDebt : ∀ w ∈ L,
      debt w ≤ if paper11LeftDegree E R w = 1 then 4 else 7)
    (hResource : ∀ u ∈ R,
      (if paper11RightDegree E L u = 1 then 4 else 11) ≤ resource u) :
    (∑ w ∈ L, debt w) ≤ ∑ u ∈ R, resource u := by
  classical
  obtain ⟨hLsum, hRsum⟩ := paper11_incidence_degree_sum L R E hE
  have hLpositive : ∀ w ∈ L, 1 ≤ paper11LeftDegree E R w := by
    intro w hw
    rcases hLdegree w hw with h | h <;> omega
  have hRpositive : ∀ u ∈ R, 1 ≤ paper11RightDegree E L u := by
    intro u hu
    rcases hRdegree u hu with h | h <;> omega
  have hLcard : (L.card : ℤ) ≤ (E.card : ℤ) := by
    have hsum := Finset.sum_le_sum hLpositive
    have hsum' : (L.card : ℤ) ≤
        (∑ w ∈ L, (paper11LeftDegree E R w : ℤ)) := by
      exact_mod_cast (by simpa using hsum)
    calc
      (L.card : ℤ) ≤ ∑ w ∈ L, (paper11LeftDegree E R w : ℤ) := hsum'
      _ = (E.card : ℤ) := by exact_mod_cast hLsum
  have hRcard : (R.card : ℤ) ≤ (E.card : ℤ) := by
    have hsum := Finset.sum_le_sum hRpositive
    have hsum' : (R.card : ℤ) ≤
        (∑ u ∈ R, (paper11RightDegree E L u : ℤ)) := by
      exact_mod_cast (by simpa using hsum)
    calc
      (R.card : ℤ) ≤ ∑ u ∈ R, (paper11RightDegree E L u : ℤ) := hsum'
      _ = (E.card : ℤ) := by exact_mod_cast hRsum
  have hDebtAffine : (∑ w ∈ L, debt w) ≤
      3 * (E.card : ℤ) + L.card := by
    have hpoint : ∀ w ∈ L,
        debt w ≤ 3 * (paper11LeftDegree E R w : ℤ) + 1 := by
      intro w hw
      rcases hLdegree w hw with h | h
      · rw [h]
        have hdebt := hDebt w hw
        simp [h] at hdebt
        norm_num at hdebt ⊢
        exact hdebt
      · rw [h]
        have hdebt := hDebt w hw
        have hne : paper11LeftDegree E R w ≠ 1 := by omega
        simp [hne] at hdebt
        norm_num at hdebt ⊢
        exact hdebt
    have hsum := Finset.sum_le_sum hpoint
    calc
      _ ≤ ∑ w ∈ L, (3 * (paper11LeftDegree E R w : ℤ) + 1) := hsum
      _ = 3 * (∑ w ∈ L, (paper11LeftDegree E R w : ℤ)) + L.card := by
        simp [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 3 * (E.card : ℤ) + L.card := by
        rw [show (∑ w ∈ L, (paper11LeftDegree E R w : ℤ)) =
          (E.card : ℤ) by exact_mod_cast hLsum]
  have hResourceAffine : 7 * (E.card : ℤ) - 3 * R.card ≤
      ∑ u ∈ R, resource u := by
    have hpoint : ∀ u ∈ R,
        7 * (paper11RightDegree E L u : ℤ) - 3 ≤ resource u := by
      intro u hu
      rcases hRdegree u hu with h | h
      · rw [h]
        have hres := hResource u hu
        simp [h] at hres
        norm_num at hres ⊢
        exact hres
      · rw [h]
        have hres := hResource u hu
        have hne : paper11RightDegree E L u ≠ 1 := by omega
        simp [hne] at hres
        norm_num at hres ⊢
        exact hres
    have hsum := Finset.sum_le_sum hpoint
    have hsumEq :
        (∑ u ∈ R, (7 * (paper11RightDegree E L u : ℤ) - 3)) =
          7 * (E.card : ℤ) - 3 * R.card := by
      calc
        _ = (∑ u ∈ R, (7 * (paper11RightDegree E L u : ℤ))) -
            ∑ u ∈ R, (3 : ℤ) := by rw [Finset.sum_sub_distrib]
        _ = 7 * (∑ u ∈ R, (paper11RightDegree E L u : ℤ)) - 3 * R.card := by
            simp [← Finset.mul_sum]
            ring
        _ = 7 * (E.card : ℤ) - 3 * R.card := by
            rw [show (∑ u ∈ R, (paper11RightDegree E L u : ℤ)) =
              (E.card : ℤ) by exact_mod_cast hRsum]
    rw [← hsumEq]
    exact hsum
  have harithmetic :
      3 * (E.card : ℤ) + L.card ≤ 7 * (E.card : ℤ) - 3 * R.card := by
    nlinarith
  exact le_trans (le_trans hDebtAffine harithmetic) hResourceAffine
end C6BipartiteDomination
