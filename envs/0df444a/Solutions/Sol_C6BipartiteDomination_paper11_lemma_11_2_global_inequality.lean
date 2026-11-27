-- Prove2me | solution 1 for C6BipartiteDomination.paper11_lemma_11_2_global_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:13:47.984996+00:00
-- url     : https://prove2.me/submissions/26d5eb8e-a7de-4a41-a8b7-906860435327

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11_external_charge_sum_split
import Theorems.Thm_C6BipartiteDomination_paper11_nonnegative_residual_charge
import Theorems.Thm_C6BipartiteDomination_paper11_base_charge_sum_bound
import Theorems.Thm_C6BipartiteDomination_paper11_negative_debt_paid
import Theorems.Thm_C6BipartiteDomination_paper11_Z0_card_le_incidence
import Theorems.Thm_C6BipartiteDomination_lemma_6_1_charge_identity
import Theorems.Thm_C6BipartiteDomination_paper11K3SpecialBudget_cost_bound


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G) :
    8 * (WBPart G D).card ≥
      7 * ((BPart G D).card + (Z0Part G D).card) := by
  classical
  let N := paper11NegativeSupports G D
  let C := paper11AllCompensation G D hCan hmax
  let O := paper11AllRepairOwners G D hCan hmax
  let Pspec := paper11K3SpecialBudgetVertices G D hCan hmax
  let surplus := incidenceTotal G D - (Z0Part G D).card
  have hDebt := paper11_negative_debt_paid G hCan hmax hNoIso
  have hBase := paper11_base_charge_sum_bound G hCan hmax
  have hResidual := paper11_nonnegative_residual_charge G hCan hmax
  have hSplit := paper11_external_charge_sum_split G hCan hmax
  have hSpecial := paper11K3SpecialBudget_cost_bound G hCan hmax hNoIso
  have hNegCast :
      (∑ w ∈ N, externalCharge G D w) =
        - (∑ w ∈ N, -externalCharge G D w) := by
    rw [← Finset.sum_neg_distrib]
    simp
  have hAlloc :
      0 ≤ (∑ w ∈ N, externalCharge G D w) +
        (∑ u ∈ BPart G D, vertexCharge G D u) +
        (∑ q ∈ C, externalCharge G D q) +
        7 * (surplus : ℤ) := by
    have hDebt' :
        (∑ w ∈ N, -externalCharge G D w) ≤
          (∑ u ∈ O, vertexCharge G D u) +
            (∑ q ∈ C, externalCharge G D q) + 7 * (surplus : ℤ) := by
      simpa [N, O, C, surplus] using hDebt
    have hBase' :
        (∑ u ∈ O, vertexCharge G D u) ≤
          ∑ u ∈ BPart G D, vertexCharge G D u := by
      simpa [O] using hBase
    have hSpecial' : 7 * (Pspec.card : ℤ) ≤ 7 * (surplus : ℤ) := by
      simpa [Pspec, surplus] using hSpecial
    rw [hNegCast]
    linarith
  have hCharges :
      0 ≤ (∑ u ∈ BPart G D, vertexCharge G D u) +
        (∑ w ∈ SPart G D, externalCharge G D w) +
        7 * ((incidenceTotal G D - (Z0Part G D).card : ℕ) : ℤ) := by
    rw [hSplit]
    have hResidual' :
        0 ≤ ∑ q ∈ paper11NonnegativeSupports G D \ C,
          externalCharge G D q := by
      simpa [C] using hResidual
    have hAlloc' := hAlloc
    dsimp [surplus] at hAlloc'
    dsimp [N, C] at hAlloc'
    linarith
  have hIdentity := lemma_6_1_charge_identity G hCan
  have hDifferenceAdd :
      0 ≤ (8 : ℤ) * ((WBPart G D).card : ℤ) -
        7 * (((BPart G D).card : ℤ) + ((Z0Part G D).card : ℤ)) := by
    rw [hIdentity]
    have hZ0le := paper11_Z0_card_le_incidence G (D := D) hNoIso
    simpa only [Nat.cast_sub hZ0le] using hCharges
  have hDifference :
      0 ≤ (8 : ℤ) * ((WBPart G D).card : ℤ) -
        7 * (((BPart G D).card + (Z0Part G D).card : ℕ) : ℤ) := by
    simpa only [Nat.cast_add] using hDifferenceAdd
  have hInt :
      (7 * ((BPart G D).card + (Z0Part G D).card) : ℤ) ≤
        8 * ((WBPart G D).card : ℤ) := by linarith
  exact_mod_cast hInt
end C6BipartiteDomination
