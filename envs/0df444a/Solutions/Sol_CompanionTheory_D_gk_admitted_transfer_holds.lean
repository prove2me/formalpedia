-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.transfer_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:26.88032+00:00
-- url     : https://prove2.me/submissions/e9c66219-0720-4070-a84b-fa77027da25b

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Transfer
import Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_exists_approx
import Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_integrable_of_cont
import Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_IsFam_sub
import Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_exists_bound
import Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_isFam_rep
import Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_apply_stdPoly
import Theorems.Thm_CompanionTheory_D_gk_admitted_map_stdPoly
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open MeasureTheory Matrix
open scoped Kronecker Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PrismTransfer
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution : Transfer := by
  intro G _ _ _ _ _ K _ _ _ μ _ st S ι₀ _ _ ρ₀ hρ₀ hi e he M g hgood H _ _ _ σ hσ E hE
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  set B : ℝ := ∫ k, ‖e k‖ ∂μ with hB
  choose C hC hbd using fun π : Equiv.Perm (Fin M) =>
    exists_bound (μ := μ) he (List.ofFn fun i => g (π i)) {1} isCompact_singleton
  have hCU : IsCompact (⋃ π, C π) := isCompact_iUnion hC
  let φ : (H →L[ℂ] H) →+* Module.End ℂ H := ContinuousLinearMap.toLinearMapRingHom
  let σ' : G →* Module.End ℂ H := φ.toMonoidHom.comp σ
  ext v
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun ℓ => ?_
  have hF := isFam_rep (μ := μ) he σ' (fun x => (σ x).continuous) hσ (φ E) hE ℓ v
  have hmap : stdPoly E (fun i => σ (g i)) v = stdPoly (φ E) (fun i => σ' (g i)) v := by
    change φ (stdPoly E fun i => σ (g i)) v = _
    rw [map_stdPoly]
    rfl
  rw [hmap]
  have main : ∀ δ : ℝ, 0 < δ → ‖ℓ (stdPoly (φ E) (fun i => σ' (g i)) v)‖ ≤
      (Fintype.card (Equiv.Perm (Fin M)) * B ^ (M + 1)) * δ := by
    intro δ hδ
    obtain ⟨κ, _, _, τ, a, b, hτ, hap⟩ := exists_approx hρ₀ hi hCU hF.cont₀ hδ
    let τ' : G →* Module.End ℂ (κ → ℂ) := (Matrix.toLinAlgEquiv' : Matrix κ κ ℂ ≃ₐ[ℂ] _).toMonoidHom.comp τ
    have hc : ∀ u : κ → ℂ, Continuous fun x => τ x *ᵥ u := fun u => hτ.cont.matrix_mulVec continuous_const
    have hint : ∀ u : κ → ℂ, Integrable (fun k : K => e k • (τ k *ᵥ u)) μ := fun u =>
      integrable_of_cont (he.smul ((hc u).comp continuous_subtype_val))
    let E' : Module.End ℂ (κ → ℂ) :=
      { toFun := fun u => ∫ k : K, e k • (τ k *ᵥ u) ∂μ
        map_add' := fun u w => by
          rw [← integral_add (hint u) (hint w)]
          simp only [mulVec_add, smul_add]
        map_smul' := fun c u => by
          rw [RingHom.id_apply, ← integral_smul]
          simp only [mulVec_smul, smul_comm c] }
    let ℓ' : (κ → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (dotProductBilin ℂ ℂ a)
    have hF' := isFam_rep (μ := μ) he τ' (fun x => (τ' x).continuous_of_finiteDimensional) hc E'
      (fun _ => rfl) ℓ' b
    have hz : stdPoly E' (fun i => τ' (g i)) = 0 := hgood κ τ hτ E' fun _ => rfl
    have e1 := apply_stdPoly σ' (φ E) g (ℓ : H →ₗ[ℂ] ℂ) v
    have e2 := apply_stdPoly τ' E' g (ℓ' : (κ → ℂ) →ₗ[ℂ] ℂ) b
    rw [hz, LinearMap.zero_apply, map_zero] at e2
    have e3 : ℓ (stdPoly (φ E) (fun i => σ' (g i)) v) = ∑ π : Equiv.Perm (Fin M),
        ((Equiv.Perm.sign π : ℤ) : ℂ) * (ℓ (word (φ E) ((List.ofFn fun i => g (π i)).map σ') v) -
          ℓ' (word E' ((List.ofFn fun i => g (π i)).map τ') b)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      exact e1.trans (by rw [← sub_zero (Finset.sum _ _), e2]; rfl)
    rw [e3]
    refine (norm_sum_le _ _).trans ?_
    rw [mul_assoc, ← nsmul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun π _ => ?_
    have hs : ‖((Equiv.Perm.sign π : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
    rw [norm_mul, hs, one_mul]
    have := hbd π _ _ (hF.sub he hF') δ
      (fun y hy => hap y (Set.mem_iUnion.2 ⟨π, hy⟩)) 1 rfl
    simpa only [map_one, Module.End.one_apply, List.length_ofFn] using this
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set D : ℝ := Fintype.card (Equiv.Perm (Fin M)) * B ^ (M + 1)
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (integral_nonneg fun _ => norm_nonneg _) _)
  refine (main (ε / (D + 1)) (by positivity)).trans ?_
  rw [zero_add, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith
end CompanionTheory.D.gk.admitted
