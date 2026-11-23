-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GoodRankMultinomialDepth.gr_of_primitive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:35.075824+00:00
-- url     : https://prove2.me/submissions/9e947ddb-2f02-4dfe-8599-8e26420c9a95

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_LemmaS
import Theorems.Thm_Formalism_CountingSumsFrames_GoodRankMultinomialDepth_pow_succ_dvd_of_not_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.GoodRankMultinomialDepth
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.CountingSumsFrames.GoodRankMultinomialDepth
theorem _root_.solution {B ι : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup B] [Module O B]
    [Module.Free O B] [Module.Finite O B] {π : O} (hπ : Irreducible π) (E : ℕ)
    (h : (ι → O) →ₗ[O] B) (hp : ∀ x z, h x = π ^ (E + 1) • z → ∀ i, π ∣ x i) :
    GR ι π h E := by
  classical
  have hx' : ∀ x z, h x = π ^ (E + 1) • z → ∃ x', x = π • x' := by
    intro x z hxz
    refine ⟨fun i => (hp x z hxz i).choose, funext fun i => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul]
    exact (hp x z hxz i).choose_spec
  have hker : LinearMap.ker h = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {π}) _
      (IsNoetherian.noetherian _)
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      obtain ⟨x', rfl⟩ := hx' x 0 (by rw [hx, smul_zero])
      have : h x' = 0 := by
        rw [map_smul] at hx
        exact (smul_eq_zero.mp hx).resolve_left hπ.ne_zero
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self π) this
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le,
        Set.singleton_subset_iff]
      exact hπ.not_isUnit
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Module.Free.chooseBasis O B) (LinearMap.range h)
  let eH : (ι → O) ≃ₗ[O] LinearMap.range h :=
    LinearEquiv.ofInjective h (LinearMap.ker_eq_bot.mp hker)
  have heH : ∀ x, ((eH x : LinearMap.range h) : B) = h x := fun x => rfl
  have hdvd : ∀ i, snf.a i ∣ π ^ E := by
    intro i
    by_contra hnd
    obtain ⟨c, hc⟩ := pow_succ_dvd_of_not_dvd hπ hnd
    have hy : h (eH.symm (snf.bN i)) = (snf.bN i : B) := by
      rw [← heH, LinearEquiv.apply_symm_apply]
    obtain ⟨y', hy'⟩ := hx' (eH.symm (snf.bN i)) (c • snf.bM (snf.f i))
      (by rw [hy, snf.snf i, hc, smul_smul])
    have hb : snf.bN i = π • eH y' := by
      rw [← map_smul, ← hy', LinearEquiv.apply_symm_apply]
    have h1 := congrArg (fun m => snf.bN.repr m i) hb
    simp only [Basis.repr_self, Finsupp.single_eq_same, map_smul, Finsupp.smul_apply,
      smul_eq_mul] at h1
    exact hπ.not_isUnit (isUnit_of_dvd_one ⟨_, h1⟩)
  choose c hc using hdvd
  let w : B →ₗ[O] (Fin n → O) := LinearMap.pi (fun i => c i • snf.bM.coord (snf.f i))
  have key : w ∘ₗ (LinearMap.range h).subtype = (π ^ E) • snf.bN.equivFun.toLinearMap := by
    apply snf.bN.ext
    intro i
    funext j
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, snf.snf i, map_smul,
      LinearMap.smul_apply, LinearEquiv.coe_coe, Basis.equivFun_self, w, LinearMap.pi_apply,
      Basis.coord_apply, Basis.repr_self, Pi.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp [hc i, mul_comm]
    · have : snf.f i ≠ snf.f j := fun h => hij (snf.f.injective h)
      simp [this, hij]
  refine ⟨LinearMap.id, eH.symm.toLinearMap ∘ₗ snf.bN.equivFun.symm.toLinearMap ∘ₗ w, ?_⟩
  apply LinearMap.ext
  intro x
  have hk := LinearMap.congr_fun key (eH x)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, heH, LinearMap.smul_apply,
    LinearEquiv.coe_coe] at hk
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearEquiv.coe_coe,
    hk, map_smul, LinearEquiv.symm_apply_apply]
end Formalism.CountingSumsFrames.GoodRankMultinomialDepth
