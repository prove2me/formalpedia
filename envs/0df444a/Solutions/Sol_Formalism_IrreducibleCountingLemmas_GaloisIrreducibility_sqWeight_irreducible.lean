-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqWeight_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:41.351628+00:00
-- url     : https://prove2.me/submissions/77a7cfee-cb55-460a-b80c-f9ee82425a29

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {K : Type} [Field K] [Fintype K] (P : K[X]) (hP : Irreducible P)
    (hm : P.Monic) : sqWeight P = ((Fintype.card K : ℝ) ^ P.natDegree - 1)⁻¹ := by
  unfold sqWeight
  classical
  have h1 := UniqueFactorizationMonoid.normalizedFactors_irreducible hP
  rw [hm.normalize_eq_self] at h1
  have h2 : (Multiset.map (fun P : K[X] => ((Fintype.card K : ℝ) ^ P.natDegree - 1)⁻¹)
      (UniqueFactorizationMonoid.normalizedFactors P)).prod =
      ((Fintype.card K : ℝ) ^ P.natDegree - 1)⁻¹ := by
    rw [h1]; simp
  convert h2
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
