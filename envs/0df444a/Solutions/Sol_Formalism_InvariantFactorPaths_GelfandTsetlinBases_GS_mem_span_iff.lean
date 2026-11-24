-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.mem_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:54:15.759432+00:00
-- url     : https://prove2.me/submissions/bb72dbdd-58fb-4870-b387-f932e8b04266

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_slc_smul_map
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_slc_mem_slSpace

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
variable {k : Type*} [Field k] {σ : Type*}
variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k D]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution (N : Submodule k (MvPolynomial σ k)) (P : MvPolynomial σ A) :
    P ∈ Submodule.span A ((fun f => map (algebraMap k A) f) '' (N : Set (MvPolynomial σ k))) ↔
      slSpace (k := k) P ≤ N := by
  classical
  constructor
  · intro hP
    rintro _ ⟨ℓ, rfl⟩
    change slc ℓ P ∈ N
    induction hP using Submodule.span_induction generalizing ℓ with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      have := slc_smul_map ℓ 1 f
      rw [one_smul] at this
      rw [this]
      exact N.smul_mem _ hf
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact N.add_mem (hx ℓ) (hy ℓ)
    | smul a x _ hx =>
      have : slc ℓ (a • x) = slc (ℓ ∘ₗ LinearMap.mulLeft k a) x := by
        ext e
        simp
      rw [this]
      exact hx _
  · intro h
    let b := Module.Basis.ofVectorSpace k A
    let I := P.support.biUnion fun e => (b.repr (coeff e P)).support
    have key : P = ∑ i ∈ I, (b i) • map (algebraMap k A) (slc (b.coord i) P) := by
      ext e
      rw [coeff_sum]
      simp only [coeff_smul, coeff_map, coeff_slc, smul_eq_mul, Module.Basis.coord_apply]
      have hsub : (b.repr (coeff e P)).support ⊆ I := by
        by_cases he : e ∈ P.support
        · exact Finset.subset_biUnion_of_mem (fun e => (b.repr (coeff e P)).support) he
        · rw [notMem_support_iff.mp he]
          simp
      conv_lhs => rw [← b.linearCombination_repr (coeff e P), Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ hsub (fun i a => a • b i) (fun i _ => zero_smul _ _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, mul_comm]
    rw [key]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨_, h (slc_mem_slSpace P _), rfl⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
