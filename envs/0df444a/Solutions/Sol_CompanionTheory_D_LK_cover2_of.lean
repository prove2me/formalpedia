-- Prove2me | solution 1 for CompanionTheory.D.LK.cover2_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:34.175402+00:00
-- url     : https://prove2.me/submissions/e0e11dd4-f413-48db-946a-8c267f864e81

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_GeneralizedVermaModulePolynomial
import Theorems.Thm_CompanionTheory_D_LK_kRel_tens
import Theorems.Thm_CompanionTheory_D_LK_free_all
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset MvPolynomial
open scoped TensorProduct
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Formalism.REAL GlobalTheory.CompanionTheory.DSVerma GlobalTheory.CompanionTheory.DSCover
open CompanionTheory.D.DSIC (KRel NC)
namespace CompanionTheory.D.LK
theorem _root_.solution (hA : AcycAbs) : Cover2 := by
  intro n ε V _ _ E hE
  obtain ⟨Z, _, _, M, χ, z₀, a, d, Fil, hM, h1, h0, hF⟩ := free_all n n
  let S : ℕ → Set (V ⊗[ℂ] Z) := fun k => {t | ∃ v z, z ∈ Fil k ∧ t = v ⊗ₜ z}
  have hin : ∀ {k : ℕ} (v : V) {z : Z}, z ∈ Fil k → v ⊗ₜ[ℂ] z ∈ Submodule.span ℂ (S k) :=
    fun v _ hz => Submodule.subset_span ⟨_, _, hz, rfl⟩
  have hmap : ∀ (T : Module.End ℂ (V ⊗[ℂ] Z)) (k : ℕ) (Q : Submodule ℂ (V ⊗[ℂ] Z)),
      (∀ v z, z ∈ Fil k → T (v ⊗ₜ z) ∈ Q) → ∀ t ∈ Submodule.span ℂ (S k), T t ∈ Q := by
    intro T k Q h
    refine fun t ht => (Submodule.span_le (p := Q.comap T)).2 ?_ ht
    rintro _ ⟨v, z, hz, rfl⟩
    exact h v z hz
  have hm : Monotone fun k => Submodule.span ℂ (S k) := fun k l hkl =>
    Submodule.span_mono (by rintro _ ⟨v, z, hz, rfl⟩; exact ⟨v, z, hF.mono hkl hz, rfl⟩)
  refine ⟨V ⊗[ℂ] Z, inferInstance, inferInstance, fun c e => (E c e).rTensor Z + (M c e).lTensor V,
    (TensorProduct.rid ℂ V).toLinearMap ∘ₗ χ.lTensor V, kRel_tens hE hM, fun v => ⟨v ⊗ₜ z₀, by simp [h1]⟩,
    fun c e t => ?_, hA n ε _ _ (fun i => (a i).lTensor V) (fun i => (d i).lTensor V)
      (fun k => Submodule.span ℂ (S k)) (kRel_tens hE hM) ⟨?_, ?_, ?_, hm, ?_, ?_, ?_, ?_, ?_⟩⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => simp [h0]
    | add p q hp hq => simp only [map_add, hp, hq]
  · exact fun i j => (hF.a_comm i j).map (Module.End.lTensorAlgHom ℂ Z V)
  · exact fun i j => (hF.d_comm i j).map (Module.End.lTensorAlgHom ℂ Z V)
  · intro i j _
    have := congrArg (Module.End.lTensorAlgHom ℂ Z V) (hF.da i j i.1.1.2)
    rw [map_sub, map_mul, map_mul, apply_ite (Module.End.lTensorAlgHom ℂ Z V), map_one, map_zero] at this
    exact this
  · intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, Submodule.zero_mem _⟩
    | tmul v z =>
      obtain ⟨k, hk⟩ := hF.exh z
      exact ⟨_, hin v hk⟩
    | add p q hp hq =>
      obtain ⟨k, hk⟩ := hp
      obtain ⟨l, hl⟩ := hq
      exact ⟨max k l, Submodule.add_mem _ (hm (le_max_left _ _) hk) (hm (le_max_right _ _) hl)⟩
  · exact fun i k => hmap _ k _ fun v z hz => hin v (hF.a_mem i _ z hz)
  · intro i k
    refine hmap (((E i.1.1 i.1.2).rTensor Z + (M i.1.1 i.1.2).lTensor V) - (a i).lTensor V) k _ fun v z hz => ?_
    have e : (((E i.1.1 i.1.2).rTensor Z + (M i.1.1 i.1.2).lTensor V) - (a i).lTensor V :
        Module.End ℂ (V ⊗[ℂ] Z)) (v ⊗ₜ z) = E i.1.1 i.1.2 v ⊗ₜ z + v ⊗ₜ (M i.1.1 i.1.2 z - a i z) := by
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.tmul_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ (hin _ hz) (hin _ (hF.r_mem i _ z hz))
  · exact fun i k => hmap _ _ _ fun v z hz => hin v (hF.d_mem i _ z hz)
  · exact fun i => hmap _ _ ⊥ fun v z hz => by simp [hF.d_zero i z hz]
end CompanionTheory.D.LK
