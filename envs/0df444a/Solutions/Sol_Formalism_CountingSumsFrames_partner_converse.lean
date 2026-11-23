-- Prove2me | solution 1 for Formalism.CountingSumsFrames.partner_converse
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:09.558029+00:00
-- url     : https://prove2.me/submissions/9dafa1b1-b27c-468e-bb7a-d6a9a771c8cc

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
import Theorems.Thm_Formalism_CountingSumsFrames_mat_comm_scalar

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
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : PartnerConverse := by
  intro O _ _ _ π hπ A B _ _ _ _ _ _ _ _ b n D hg
  obtain ⟨u, v, huv⟩ := hg
  have huv' : ∀ x, v (b (u x)) = π ^ D • x := by
    intro x
    have := congrArg (fun T => T x) huv
    simpa using this
  have hπD : π ^ D ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have hinj : Function.Injective u := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have := huv' x
    rw [hx, map_zero, map_zero] at this
    exact (smul_eq_zero.1 this.symm).resolve_left hπD
  obtain ⟨m, S⟩ := Submodule.smithNormalForm (Module.Free.chooseBasis O A) (LinearMap.range u)
  have hm : m = n := by
    have h1 : Module.finrank O (LinearMap.range u) = m := by
      rw [Module.finrank_eq_card_basis S.bN]; simp
    rw [← h1, ← (LinearEquiv.finrank_eq (LinearEquiv.ofInjective u hinj))]
    simp
  subst hm
  let g : (Fin m → O) →ₗ[O] A := (Pi.basisFun O (Fin m)).constr O (fun i => S.bM (S.f i))
  let P : A →ₗ[O] (Fin m → O) := LinearMap.pi fun i => S.bM.coord (S.f i)
  have hg_apply : ∀ z, g z = ∑ i, z i • S.bM (S.f i) := by
    intro z
    simp [g, Module.Basis.constr_apply_fintype]
  have hrepr_f : ∀ z i, S.bM.repr (g z) (S.f i) = z i := by
    intro z i
    rw [hg_apply, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have : S.f j ≠ S.f i := fun e => hj (S.f.injective e)
      simp [Finsupp.single_eq_of_ne (Ne.symm this)]
    · simp
  have hrepr_nf : ∀ z j, j ∉ Set.range S.f → S.bM.repr (g z) j = 0 := by
    intro z j hj
    rw [hg_apply, map_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have : S.f i ≠ j := fun e => hj ⟨i, e⟩
    simp [Finsupp.single_eq_of_ne (Ne.symm this)]
  have hPg : ∀ z, P (g z) = z := by
    intro z; funext i
    simp [P, hrepr_f]
  have hgP : ∀ y : A, (∀ j, j ∉ Set.range S.f → S.bM.repr y j = 0) → g (P y) = y := by
    intro y hy
    apply S.bM.ext_elem
    intro j
    by_cases hj : j ∈ Set.range S.f
    · obtain ⟨i, rfl⟩ := hj
      rw [hrepr_f]; simp [P]
    · rw [hrepr_nf _ _ hj, hy j hj]
  have hu_nf : ∀ x j, j ∉ Set.range S.f → S.bM.repr (u x) j = 0 := by
    intro x j hj
    exact S.repr_eq_zero_of_notMem_range ⟨u x, LinearMap.mem_range_self u x⟩ hj
  let T : (Fin m → O) →ₗ[O] (Fin m → O) := P ∘ₗ u
  let W : (Fin m → O) →ₗ[O] (Fin m → O) := v ∘ₗ b ∘ₗ g
  have hgT : ∀ x, g (T x) = u x := fun x => hgP (u x) (hu_nf x)
  have hWT : W ∘ₗ T = π ^ D • LinearMap.id := by
    apply LinearMap.ext; intro x
    simp only [W, LinearMap.comp_apply]
    rw [hgT x, huv' x]; simp
  have hTW : ∀ x, T (W x) = π ^ D • x := by
    have h1 : LinearMap.toMatrix' W * LinearMap.toMatrix' T = π ^ D • (1 : Matrix (Fin m) (Fin m) O) := by
      rw [← LinearMap.toMatrix'_comp, hWT]; simp
    have h2 := mat_comm_scalar _ _ _ hπD h1
    rw [← LinearMap.toMatrix'_comp] at h2
    have h3 : T ∘ₗ W = π ^ D • LinearMap.id := by
      apply LinearMap.toMatrix'.injective
      rw [h2]; simp
    intro x
    have := congrArg (fun Z => Z x) h3
    simpa using this
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z z' h
    rw [← hPg z, ← hPg z', h]
  · rintro x ⟨z, hz⟩
    refine ⟨P x, hgP x ?_⟩
    intro j hj
    have := hrepr_nf z j hj
    rw [hz, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hπ.ne_zero
  · rintro x ⟨i, hi⟩
    by_contra hall
    push Not at hall
    choose c hc using fun j => hall (Module.Free.chooseBasis O B j)
    let lam : Module.Dual O B := (Module.Free.chooseBasis O B).constr O c
    have hb : b (g x) = π ^ (D + 1) • lam := by
      apply (Module.Free.chooseBasis O B).ext
      intro j
      simp [lam, hc j]
    have h1 : W x = π ^ (D + 1) • v lam := by
      simp only [W, LinearMap.comp_apply, hb, map_smul]
    have h2 := hTW x
    rw [h1, map_smul, pow_succ, mul_smul] at h2
    have h3 : π • T (v lam) = x := smul_right_injective _ hπD h2
    apply hi
    rw [← h3]
    exact ⟨T (v lam) i, by simp⟩
end Formalism.CountingSumsFrames
