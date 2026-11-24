-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathProductDegrees
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:11:23.613824+00:00
-- url     : https://prove2.me/submissions/561299e0-54a1-491b-a9ca-7baf2972bbd1

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_colHeight_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_path_ncard
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_path_finite
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_pathWord_unchanged
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_pathWord_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Paths
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : PsiDegrees := by
  intro R _ n N isVec B μ I hp hI
  have hfin : (⋃ i ∈ Set.Iio N, {c : ℤ | colHeight (μ (i + 1)) c ≠ colHeight (μ i) c}).Finite :=
    Set.Finite.biUnion (Set.finite_Iio N) fun i hi => path_finite hp hi
  have hsub : (Function.mulSupport fun c : ℤ =>
      pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)) ⊆
      ⋃ i ∈ Set.Iio N, {c : ℤ | colHeight (μ (i + 1)) c ≠ colHeight (μ i) c} := by
    intro c hc
    by_contra hn
    apply hc
    have hun : ∀ i < N, colHeight (μ (i + 1)) c = colHeight (μ i) c := by
      intro i hi
      by_contra hne
      exact hn (Set.mem_biUnion (show i ∈ Set.Iio N from hi) hne)
    obtain ⟨a, b⟩ := pathWord_unchanged isVec μ c
      (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N hun
    have hcard := hI c
    rw [b, hp.1, colHeight_zero] at hcard
    have h0 : (I c).card = 0 := by
      rw [hcard]; split_ifs <;> simp
    show pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c) = 1
    rw [a, Finset.card_eq_zero.1 h0]
    simp [oneF]
  refine ⟨hfin.subset hsub, fun i => ?_⟩
  unfold psiPath
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by rwa [Set.Finite.coe_toFinset])]
  have key := IsWeightedHomogeneous.prod hfin.toFinset
    (fun c : ℤ => pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c))
    (fun c : ℤ => if i < N ∧ colHeight (μ (i + 1)) c ≠ colHeight (μ i) c then 1 else 0)
    (w := fun x : ℕ × Fin n => if x.1 = i then 1 else 0)
    (fun c _ => pathWord_hom R isVec μ c i N (I c))
  convert key using 1
  by_cases hi : i < N
  · rw [if_pos hi, ← path_ncard hp hi, ← Finset.card_filter, ← Set.ncard_coe_finset]
    congr 1
    ext c
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨Set.mem_biUnion (show i ∈ Set.Iio N from hi) h, hi, h⟩
    · rintro ⟨-, -, h⟩
      exact h
  · rw [if_neg hi]
    exact (Finset.sum_eq_zero fun c _ => if_neg fun h => hi h.1).symm
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
