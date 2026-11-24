-- Prove2me | solution 1 for Formalism.L2.NCov.exists_pt_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:28:08.489342+00:00
-- url     : https://prove2.me/submissions/598f0996-bfd7-4ae5-888b-88310649e842

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
import Theorems.Thm_Formalism_L2_NCov_cls_isMaximal
import Theorems.Thm_Formalism_L2_NCov_exists_finset_pts
import Theorems.Thm_Formalism_L2_NCov_pow_sub_apply_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
open Polynomial
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O]
  {S : Set (End K V)}
set_option linter.deprecated false
namespace Formalism.L2.NCov
theorem _root_.solution [FiniteDimensional K V] (hinj : Function.Injective (algebraMap O K))
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    (𝔪 : Ideal (Algebra.adjoin O S)) (h𝔪 : 𝔪.IsMaximal) :
    ∃ ψ : Algebra.adjoin O S →ₐ[O] O, W _ (pt ψ) ≠ ⊥ ∧ cls ψ = 𝔪 := by
  classical
  obtain ⟨F, hF, htop⟩ := exists_finset_pts hinj hS hsplit hint
  by_contra hne
  push Not at hne
  letI : CommRing (Algebra.adjoin O S) := Algebra.adjoinCommRingOfComm O fun a ha b hb => (hS a ha b hb).eq
  set F' := F.filter (fun ψ => W _ (pt ψ) ≠ ⊥) with hF'
  have ht : ∃ t ∈ 𝔪, ∀ ψ ∈ F', IsUnit (ψ t) := by
    rcases F'.eq_empty_or_nonempty with h0 | ⟨a, ha⟩
    · exact ⟨0, 𝔪.zero_mem, by simp [h0]⟩
    · have hcov : ¬ ((𝔪 : Set (Algebra.adjoin O S)) ⊆ ⋃ ψ ∈ (F' : Set (Algebra.adjoin O S →ₐ[O] O)),
          ((cls ψ : Ideal (Algebra.adjoin O S)) : Set (Algebra.adjoin O S))) := by
        intro hsub
        obtain ⟨ψ, hψ, hle⟩ :=
          (Ideal.subset_union_prime a a (fun ψ _ _ _ => (cls_isMaximal ψ).isPrime)).1 hsub
        exact hne ψ (Finset.mem_filter.1 hψ).2 (h𝔪.eq_of_le (cls_isMaximal ψ).ne_top hle).symm
      simp only [Set.not_subset, Set.mem_iUnion, not_exists] at hcov
      obtain ⟨t, htm, ht⟩ := hcov
      refine ⟨t, htm, fun ψ hψ => ?_⟩
      have h1 : t ∉ cls ψ := fun h => ht ψ hψ h
      change ¬ ((IsLocalRing.residue O) (ψ t) = 0) at h1
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1
  obtain ⟨t, htm, ht⟩ := ht
  let d : (Algebra.adjoin O S →ₐ[O] O) → ℕ := fun ψ => (t : End K V).maxGenEigenspaceIndex (pt ψ t)
  let P : O[X] := ∏ ψ ∈ F', (X - C (ψ t)) ^ d ψ
  have hP : aeval (t : End K V) P = 0 := by
    have hker : ∀ ψ ∈ F', W _ (pt ψ) ≤ LinearMap.ker (aeval (t : End K V) P) := by
      intro ψ hψ x hx
      rw [LinearMap.mem_ker]
      rw [show P = (∏ φ ∈ F'.erase ψ, (X - C (φ t)) ^ d φ) * (X - C (ψ t)) ^ d ψ from
        (Finset.prod_erase_mul _ _ hψ).symm]
      rw [map_mul, Module.End.mul_apply, map_pow, map_sub, aeval_X, aeval_C]
      rw [pow_sub_apply_eq_zero ψ t hx, map_zero]
    have htop' : F'.sup (fun ψ => W _ (pt ψ)) = ⊤ := by
      rw [← htop]
      apply le_antisymm
      · exact Finset.sup_mono (Finset.filter_subset _ _)
      · refine Finset.sup_le fun ψ hψ => ?_
        by_cases h : W _ (pt ψ) = ⊥
        · rw [h]; exact bot_le
        · exact Finset.le_sup (f := fun ψ => W _ (pt ψ)) (Finset.mem_filter.2 ⟨hψ, h⟩)
    have hle : (⊤ : Submodule K V) ≤ LinearMap.ker (aeval (t : End K V) P) := by
      rw [← htop']; exact Finset.sup_le hker
    ext x
    exact LinearMap.mem_ker.1 (hle Submodule.mem_top)
  have hPT : aeval t P = 0 := by
    apply Subtype.val_injective
    have e := aeval_algHom_apply (Algebra.adjoin O S).val t P
    simp only [Subalgebra.coe_val] at e
    rw [← e]
    simpa using hP
  have hu : IsUnit (P.coeff 0) := by
    rw [coeff_zero_eq_eval_zero, eval_prod]
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun ψ hψ => ?_
    simp only [eval_pow, eval_sub, eval_X, eval_C, zero_sub]
    exact ((ht ψ hψ).neg).pow _
  obtain ⟨u, hu'⟩ := hu
  have key := congrArg (aeval t) (X_mul_divX_add P)
  rw [hPT, map_add, map_mul, aeval_X, aeval_C, ← hu'] at key
  have e : t * aeval t P.divX = - algebraMap O _ (u : O) := eq_neg_of_add_eq_zero_left key
  have hunitT : IsUnit t := by
    have h : t * (aeval t P.divX * algebraMap O _ (-↑u⁻¹)) = 1 := by
      rw [← mul_assoc, e, ← map_neg, ← map_mul, neg_mul_neg, Units.mul_inv, map_one]
    exact ⟨⟨t, _, h, (mul_comm _ t).trans h⟩, rfl⟩
  exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem 𝔪 htm hunitT)
end Formalism.L2.NCov
