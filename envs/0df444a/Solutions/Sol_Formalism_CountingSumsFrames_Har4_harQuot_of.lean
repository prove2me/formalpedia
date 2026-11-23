-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.harQuot_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:07.805887+00:00
-- url     : https://prove2.me/submissions/5d27e275-b260-4e83-85a5-2be8a9dd95c8

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_mem_latOf_iff
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_gaussLemmaPairing_holds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_smul_mem_latOf_gauss
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_exists_cofactor
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_h_mul_eq_zero_of_deg

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
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution (H1 : HarProj) (H2 : GaussProj) : HarQuot := by
  intro K _ _ k A B p O g hk hp hR
  obtain ⟨H1a, H1b, H1c⟩ := H1 K k A B hk
  refine ⟨fun w G hw hwG => ?_, fun f hf hfl => ?_⟩
  · have hwP : w ∈ PolAB K k A B :=
      (Submodule.mem_inf.1 (show w ∈ PolAB K k A B ⊓ LinearMap.ker (ctrF K k) from hw)).1
    by_cases hAB : 1 ≤ A ∧ 1 ≤ B
    · obtain ⟨G', hG', hwG'⟩ := exists_cofactor hAB.1 hAB.2 hwP hwG
      have e1 := H1b w hw
      have e2 := H1c hAB.1 hAB.2 G' hG'
      rw [← hwG'] at e2
      rw [← e1]
      exact e2
    · exact h_mul_eq_zero_of_deg (by omega) hwP hwG
  · obtain ⟨hhar, g', hg', hdiff⟩ := H1a f hf
    have hEO : (p : K) ^ ((k + 1) * Nat.log p (A + B + k)) ∈ O.toSubring :=
      O.toSubring.pow_mem (natCast_mem _ p) _
    have hw := ((H2 K k A B p O.toSubring g hk hp hR f hf).1 hfl).1
    refine ⟨((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • harProj K k A B f, Submodule.smul_mem _ _ hhar,
      ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • g', Submodule.smul_mem _ _ hg', hw, ?_, ?_⟩
    · apply gaussLemmaPairing_holds K k O g 1 _ hk
      rw [pow_one, mul_smul_comm, ← hdiff, smul_sub]
      have hf1 := smul_mem_latOf_gauss _ g hEO hfl
      rw [mem_latOf_iff] at hf1 hw ⊢
      rw [map_sub]
      have h1' : ∀ m, coeff m (glAct g⁻¹ (((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • f)) ∈ O.toSubring := hf1
      have h2' : ∀ m, coeff m (glAct g⁻¹ (((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) •
        harProj K k A B f)) ∈ O.toSubring := hw
      show ∀ m, coeff m (_ - _) ∈ O.toSubring
      intro m
      rw [MvPolynomial.coeff_sub]
      exact O.toSubring.sub_mem (h1' m) (h2' m)
    · rw [mul_smul_comm, ← hdiff, smul_sub]
      abel
end Formalism.CountingSumsFrames.Har4
