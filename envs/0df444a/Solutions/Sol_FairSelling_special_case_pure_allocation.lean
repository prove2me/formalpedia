-- Prove2me | solution 1 for FairSelling.special_case_pure_allocation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:02:44.30015+00:00
-- url     : https://prove2.me/submissions/cc5a841b-593f-49db-97ff-12d159c9a06a

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_outcome_of_bundles
import Theorems.Thm_FairSelling_disjoint_compl_of_subset
import Theorems.Thm_FairSelling_reject_all_counting
import Theorems.Thm_FairSelling_reject_one_counting
import Theorems.Thm_FairSelling_vbarSum_sold_le
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_fin3_cover
import Theorems.Thm_FairSelling_fin3_sum
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_vbarSum_union
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (a b d : Fin 3) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hnobig : ∀ i g, vbar (v i) p g < (3 / 4 : ℝ) * MMS 3 (v i) p)
    (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (lo : Fin 3)
    (hcan : IsCanonical (v a) p ((3 / 4 : ℝ) * MMS 3 (v a) p) kept sold money lo)
    (hcard : sold.card ≤ 2)
    (kA kB : Fin 3) (hkA : kA ≠ lo) (hkB : kB ≠ lo) (hkAB : kA ≠ kB)
    (hpure : money kA = 0)
    (hbacc : (3 / 4 : ℝ) * MMS 3 (v b) p ≤ vbarSum (v b) p (kept kA) + money kA)
    (hdrej : ∀ k, vbarSum (v d) p (kept k) + money k ≤ (3 / 4 : ℝ) * MMS 3 (v d) p) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  classical
  obtain ⟨hdisj, hsold, hm0, hmsum, hacc, -⟩ := hcan
  have hdA : Disjoint (kept kA) (kept kB) := hdisj _ _ hkAB
  have hdAlo : Disjoint (kept kA) (kept lo) := hdisj _ _ hkA
  have hdBlo : Disjoint (kept kB) (kept lo) := hdisj _ _ hkB
  have hbval : (3 / 4 : ℝ) * MMS 3 (v b) p ≤ vbarSum (v b) p (kept kA) := by
    rw [hpure] at hbacc; linarith
  by_cases hcase : (3 / 4 : ℝ) * MMS 3 (v a) p ≤
      vbarSum (v a) p (kept kB) + vbarSum (v a) p (kept lo)
  · -- `a` takes the two other bundles, `b` the pure bundle, `d` everything else (which
    -- contains the force-sold goods).
    set X : Fin 3 → Finset G := fun i =>
      if i = a then kept kB ∪ kept lo else if i = b then kept kA
      else Finset.univ \ (kept kA ∪ kept kB ∪ kept lo) with hX
    have hXa : X a = kept kB ∪ kept lo := by simp [hX]
    have hXb : X b = kept kA := by simp [hX, (Ne.symm hab)]
    have hXd : X d = Finset.univ \ (kept kA ∪ kept kB ∪ kept lo) := by
      simp [hX, (Ne.symm had), (Ne.symm hbd)]
    have hsubunion : ∀ i, i ≠ d → X i ⊆ kept kA ∪ kept kB ∪ kept lo := by
      intro i hi
      rcases fin3_cover hab had hbd i with h | h | h
      · subst h; rw [hXa]; intro x hx
        rcases Finset.mem_union.mp hx with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h')
        · exact Finset.mem_union_right _ h'
      · subst h; rw [hXb]; intro x hx
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
      · exact absurd h hi
    refine outcome_of_bundles v p hp X ∅ 0 ?_ (fun i => by simp) (fun i => le_refl 0)
      (by simp) ?_
    · intro i j hij
      have hda : Disjoint (X a) (X b) := by
        rw [hXa, hXb]
        exact Finset.disjoint_union_left.mpr ⟨hdA.symm, hdAlo.symm⟩
      have hdad : Disjoint (X a) (X d) := by
        rw [hXd]; exact disjoint_compl_of_subset (hsubunion a had)
      have hdbd : Disjoint (X b) (X d) := by
        rw [hXd]; exact disjoint_compl_of_subset (hsubunion b hbd)
      rcases fin3_cover hab had hbd i with hi | hi | hi <;>
        rcases fin3_cover hab had hbd j with hj | hj | hj <;> rw [hi, hj] <;>
        first
          | exact absurd (hi.trans hj.symm) hij
          | exact hda
          | exact hda.symm
          | exact hdad
          | exact hdad.symm
          | exact hdbd
          | exact hdbd.symm
    · intro i
      rcases fin3_cover hab had hbd i with hi | hi | hi <;> rw [hi]
      · rw [hXa, Pi.zero_apply, add_zero, vbarSum_union (v a) p hdBlo]; exact hcase
      · rw [hXb, Pi.zero_apply, add_zero]; exact hbval
      · rw [hXd, Pi.zero_apply, add_zero]
        have := reject_all_counting (v d) p (hv d) hp kept money hdisj kA kB lo hkAB hkA hkB hdrej
        have hmsum0 : (0 : ℝ) ≤ ∑ k, money k := Finset.sum_nonneg (fun k _ => hm0 k)
        linarith
  · -- The sale proceeds alone already satisfy `a`; `d` takes everything except the pure bundle
    -- and the sold goods.
    push_neg at hcase
    have hkBacc := hacc kB
    have hloacc := hacc lo
    have hmoney : (3 / 4 : ℝ) * MMS 3 (v a) p < money kB + money lo := by linarith
    have hmsum3 : money kA + money kB + money lo = ∑ k, money k :=
      (fin3_sum hkAB hkA hkB money).symm
    have hpsold : (3 / 4 : ℝ) * MMS 3 (v a) p ≤ ∑ g ∈ sold, p g := by
      rw [hpure] at hmsum3; linarith [hmsum]
    have hvsold : (3 / 4 : ℝ) * MMS 3 (v a) p ≤ vbarSum (v a) p sold := by
      refine le_trans hpsold ?_
      exact Finset.sum_le_sum (fun g _ => le_max_left _ _)
    set X : Fin 3 → Finset G := fun i =>
      if i = a then sold else if i = b then kept kA
      else Finset.univ \ (kept kA ∪ sold) with hX
    have hXa : X a = sold := by simp [hX]
    have hXb : X b = kept kA := by simp [hX, (Ne.symm hab)]
    have hXd : X d = Finset.univ \ (kept kA ∪ sold) := by
      simp [hX, (Ne.symm had), (Ne.symm hbd)]
    have hsubunion : ∀ i, i ≠ d → X i ⊆ kept kA ∪ sold := by
      intro i hi
      rcases fin3_cover hab had hbd i with h | h | h
      · subst h; rw [hXa]; exact Finset.subset_union_right
      · subst h; rw [hXb]; exact Finset.subset_union_left
      · exact absurd h hi
    refine outcome_of_bundles v p hp X ∅ 0 ?_ (fun i => by simp) (fun i => le_refl 0)
      (by simp) ?_
    · intro i j hij
      have hda : Disjoint (X a) (X b) := by rw [hXa, hXb]; exact hsold kA
      have hdad : Disjoint (X a) (X d) := by
        rw [hXd]; exact disjoint_compl_of_subset (hsubunion a had)
      have hdbd : Disjoint (X b) (X d) := by
        rw [hXd]; exact disjoint_compl_of_subset (hsubunion b hbd)
      rcases fin3_cover hab had hbd i with hi | hi | hi <;>
        rcases fin3_cover hab had hbd j with hj | hj | hj <;> rw [hi, hj] <;>
        first
          | exact absurd (hi.trans hj.symm) hij
          | exact hda
          | exact hda.symm
          | exact hdad
          | exact hdad.symm
          | exact hdbd
          | exact hdbd.symm
    · intro i
      rcases fin3_cover hab had hbd i with hi | hi | hi <;> rw [hi]
      · rw [hXa, Pi.zero_apply, add_zero]; exact hvsold
      · rw [hXb, Pi.zero_apply, add_zero]; exact hbval
      · rw [hXd, Pi.zero_apply, add_zero]
        have hsoldsmall := vbarSum_sold_le (v d) p (hv d) hp sold hcard (hnobig d)
        have := reject_one_counting (v d) p (hv d) hp (kept kA) sold (money kA)
          hsoldsmall (hdrej kA)
        linarith [hm0 kA]
end FairSelling
