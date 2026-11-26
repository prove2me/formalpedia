-- Prove2me | solution 1 for C6BipartiteDomination.paper11AllCompensation_sum_eq_owner_sums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:17.450575+00:00
-- url     : https://prove2.me/submissions/08e40cd5-f7c3-4042-b784-dc04e35af538

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11OwnerCompensation_charge_four
import Theorems.Thm_C6BipartiteDomination_paper11AllRepairOwners_subset_B
import Theorems.Thm_C6BipartiteDomination_paper11OwnerCompensation_family_disjoint
import Theorems.Thm_C6BipartiteDomination_paper11AllCompensation_charge_four

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
    (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
      ∑ q ∈ paper11OwnerCompensation G D hCan hmax u,
        externalCharge G D q) =
      ∑ q ∈ paper11AllCompensation G D hCan hmax,
        externalCharge G D q := by
  classical
  let O := paper11AllRepairOwners G D hCan hmax
  let C := paper11OwnerCompensation G D hCan hmax
  let U := paper11AllCompensation G D hCan hmax
  have hpair : (O : Set V).PairwiseDisjoint C := by
    simpa [O, C] using paper11OwnerCompensation_family_disjoint G hCan hmax
  have hcard : U.card = ∑ u ∈ O, (C u).card := by
    simpa [O, C, U, paper11AllCompensation] using Finset.card_biUnion hpair
  have hinner : ∀ u ∈ O,
      (∑ q ∈ C u, externalCharge G D q) = 4 * ((C u).card : ℤ) := by
    intro u hu
    calc
      _ = ∑ q ∈ C u, (4 : ℤ) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact paper11OwnerCompensation_charge_four G hCan hmax
          (paper11AllRepairOwners_subset_B G hCan hmax hu) hq
      _ = 4 * ((C u).card : ℤ) := by simp; ring
  have hsumOwner :
      (∑ u ∈ O, ∑ q ∈ C u, externalCharge G D q) =
        4 * (∑ u ∈ O, ((C u).card : ℤ)) := by
    calc
      _ = ∑ u ∈ O, 4 * ((C u).card : ℤ) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hinner u hu
      _ = 4 * (∑ u ∈ O, ((C u).card : ℤ)) := by
        calc
          _ = ∑ u ∈ O, ((C u).card : ℤ) * 4 := by
            apply Finset.sum_congr rfl
            intro u hu
            ring
          _ = (∑ u ∈ O, ((C u).card : ℤ)) * 4 := by rw [Finset.sum_mul]
          _ = 4 * (∑ u ∈ O, ((C u).card : ℤ)) := by ring
  have hcardZ : (U.card : ℤ) =
      ∑ u ∈ O, ((C u).card : ℤ) := by exact_mod_cast hcard
  calc
    _ = 4 * (∑ u ∈ O, ((C u).card : ℤ)) := hsumOwner
    _ = 4 * (U.card : ℤ) := by rw [← hcardZ]
    _ = ∑ q ∈ U, externalCharge G D q := by
      symm
      calc
        _ = ∑ q ∈ U, (4 : ℤ) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact paper11AllCompensation_charge_four G hCan hmax hq
        _ = 4 * (U.card : ℤ) := by simp; ring
end C6BipartiteDomination
