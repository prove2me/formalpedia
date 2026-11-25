-- Prove2me | solution 1 for CompanionTheory.D.LK.free_module_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:28:40.102558+00:00
-- url     : https://prove2.me/submissions/a28097dd-b955-4018-a5f0-aac2a5899663

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_GeneralizedVermaModulePolynomial
import Theorems.Thm_CompanionTheory_D_LK_deg_pderiv
import Theorems.Thm_CompanionTheory_D_LK_pderiv_deg_zero
import Theorems.Thm_CompanionTheory_D_LK_deg_X_mul
import Theorems.Thm_CompanionTheory_D_LK_generalized_verma_module_polynomial
import Theorems.Thm_CompanionTheory_D_LK_kRel_tens
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_DSVerma_dd_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_DSVerma_dd_yy
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
theorem _root_.solution : FreeStep := by
  rintro n m ⟨Z, _, _, M, χ, z₀, a, d, Fil, hM, h1, h0, hF⟩
  classical
  let ε : Fin n → Bool := fun c => decide ((c : ℕ) ≤ m)
  obtain ⟨M', hM', hX, hc, hdeg⟩ := generalized_verma_module_polynomial n ε
  let P := MvPolynomial (NC ε) ℂ
  let cc : P →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ (0 : NC ε →₀ ℕ)
  have hcc : ∀ f : P, cc f = constantCoeff f := fun f => rfl
  let y : Pos n → Module.End ℂ P := fun i =>
    if h : ε i.1.1 = true ∧ ε i.1.2 = false then yy (⟨i.1, h⟩ : NC ε) else 0
  let S : ℕ → Set (Z ⊗[ℂ] P) := fun k =>
    {t | ∃ k₁ z f, z ∈ Fil k₁ ∧ k₁ + f.totalDegree ≤ k ∧ t = z ⊗ₜ f}
  have hin : ∀ {k k₁ : ℕ} {z : Z} {f : P}, z ∈ Fil k₁ → k₁ + f.totalDegree ≤ k →
      z ⊗ₜ[ℂ] f ∈ Submodule.span ℂ (S k) := fun hz hf => Submodule.subset_span ⟨_, _, _, hz, hf, rfl⟩
  have hmap : ∀ (T : Module.End ℂ (Z ⊗[ℂ] P)) (k : ℕ) (Q : Submodule ℂ (Z ⊗[ℂ] P)),
      (∀ k₁ z f, z ∈ Fil k₁ → k₁ + f.totalDegree ≤ k → T (z ⊗ₜ f) ∈ Q) → ∀ t ∈ Submodule.span ℂ (S k), T t ∈ Q := by
    intro T k Q h
    refine fun t ht => (Submodule.span_le (p := Q.comap T)).2 ?_ ht
    rintro _ ⟨k₁, z, f, hz, hf, rfl⟩
    exact h k₁ z f hz hf
  have hy : ∀ i f, (y i f).totalDegree ≤ f.totalDegree + 1 := fun i f => by
    simp only [y]
    split_ifs
    · exact deg_X_mul _ _
    · simp
  have hddl : ∀ a b (f : P) k, f.totalDegree ≤ k + 1 → (dd ε a b f).totalDegree ≤ k := fun a b f k h => by
    unfold dd
    split_ifs
    · exact deg_pderiv _ _ _ h
    · simp
  have hdd0 : ∀ a b (f : P), f.totalDegree ≤ 0 → dd ε a b f = 0 := fun a b f h => by
    unfold dd
    split_ifs
    · exact pderiv_deg_zero _ _ h
    · simp
  refine ⟨Z ⊗[ℂ] P, inferInstance, inferInstance, fun c e => (M c e).rTensor P + (M' c e).lTensor Z,
    χ ∘ₗ (TensorProduct.rid ℂ Z).toLinearMap ∘ₗ cc.lTensor Z, z₀ ⊗ₜ 1,
    fun i => (a i).rTensor P + (y i).lTensor Z,
    fun i => if (i.1.1 : ℕ) < m then (d i).rTensor P else (dd ε i.1.1 i.1.2).lTensor Z,
    fun k => Submodule.span ℂ (S k),
    fun a b c e => kRel_tens (ε := allT n) (fun a b c d _ _ => hM a b c d) hM' a b c e rfl rfl, by simp [hcc, h1],
    fun c e t => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => simp [hcc, hc, h0]
    | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  · intro i j
    apply TensorProduct.ext'
    intro z f
    have e1 := LinearMap.congr_fun (hF.a_comm i j).eq z
    have e2 : y i (y j f) = y j (y i f) := by
      have hq : ∀ i, ∃ q : P, ∀ f, y i f = q * f := fun i => by
        simp only [y]
        split_ifs
        · exact ⟨_, fun _ => rfl⟩
        · exact ⟨0, fun f => (zero_mul f).symm⟩
      obtain ⟨q, hq1⟩ := hq i
      obtain ⟨q', hq2⟩ := hq j
      rw [hq1, hq2, hq2, hq1, mul_left_comm]
    simp only [Module.End.mul_apply] at e1
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, map_add,
      e1, e2]
    abel
  · intro i j
    apply TensorProduct.ext'
    intro z f
    have e1 := LinearMap.congr_fun (hF.d_comm i j).eq z
    have e2 := LinearMap.congr_fun (dd_comm (ε := ε) i.1.1 i.1.2 j.1.1 j.1.2).eq f
    simp only [Module.End.mul_apply] at e1 e2
    split_ifs <;> simp [e1, e2]
  · intro i j hi
    apply TensorProduct.ext'
    intro z f
    by_cases h : (i.1.1 : ℕ) < m
    · have e1 := LinearMap.congr_fun (hF.da i j h) z
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at e1
      simp only [if_pos h, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, map_add, sub_eq_iff_eq_add.1 e1, TensorProduct.add_tmul]
      split_ifs <;> simp
    · have e1 : dd ε i.1.1 i.1.2 (y j f) - y j (dd ε i.1.1 i.1.2 f) = if i = j then f else 0 := by
        simp only [y]
        by_cases hj : ε j.1.1 = true ∧ ε j.1.2 = false
        · rw [dif_pos hj]
          have := LinearMap.congr_fun (dd_yy i.1.1 i.1.2 (⟨j.1, hj⟩ : NC ε)) f
          simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
          rw [this]
          by_cases e : i = j
          · subst e; simp
          · rw [if_neg e, if_neg fun h' => e (Subtype.ext (Prod.ext h'.1 h'.2))]; rfl
        · rw [dif_neg hj, if_neg]
          · simp
          · rintro rfl
            have := i.2
            exact hj ⟨by simp only [ε, decide_eq_true_eq]; omega,
              by simp only [ε, decide_eq_false_iff_not]; rw [Fin.lt_def] at this; omega⟩
      simp only [if_neg h, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, map_add, sub_eq_iff_eq_add.1 e1, TensorProduct.tmul_add]
      split_ifs <;> simp
  · intro k l hkl
    refine Submodule.span_mono ?_
    rintro _ ⟨k₁, z, f, hz, hf, rfl⟩
    exact ⟨k₁, z, f, hz, hf.trans hkl, rfl⟩
  · intro t
    have hm : ∀ {k l}, k ≤ l → Submodule.span ℂ (S k) ≤ Submodule.span ℂ (S l) := fun hkl =>
      Submodule.span_mono (by rintro _ ⟨k₁, z, f, hz, hf, rfl⟩; exact ⟨k₁, z, f, hz, hf.trans hkl, rfl⟩)
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, Submodule.zero_mem _⟩
    | tmul z f =>
      obtain ⟨k, hk⟩ := hF.exh z
      exact ⟨_, hin hk le_rfl⟩
    | add p q hp hq =>
      obtain ⟨k, hk⟩ := hp
      obtain ⟨l, hl⟩ := hq
      exact ⟨max k l, Submodule.add_mem _ (hm (le_max_left _ _) hk) (hm (le_max_right _ _) hl)⟩
  · refine fun i k => hmap _ k _ fun k₁ z f hz hf => ?_
    have := hy i f
    rw [LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    exact Submodule.add_mem _ (hin (hF.a_mem i _ z hz) (by omega)) (hin hz (by omega))
  · intro i k
    refine hmap (((M i.1.1 i.1.2).rTensor P + (M' i.1.1 i.1.2).lTensor Z) - ((a i).rTensor P + (y i).lTensor Z)) k _
      fun k₁ z f hz hf => ?_
    have e : (((M i.1.1 i.1.2).rTensor P + (M' i.1.1 i.1.2).lTensor Z) - ((a i).rTensor P + (y i).lTensor Z) :
        Module.End ℂ (Z ⊗[ℂ] P)) (z ⊗ₜ f) =
        (M i.1.1 i.1.2 z - a i z) ⊗ₜ f + z ⊗ₜ (M' i.1.1 i.1.2 f - y i f) := by
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel
    rw [e]
    refine Submodule.add_mem _ (hin (hF.r_mem i _ z hz) hf) (hin hz (le_trans (Nat.add_le_add_left ?_ _) hf))
    simp only [y]
    split_ifs with h
    · rw [hX ⟨i.1, h⟩]; simp [yy]
    · rw [LinearMap.zero_apply, sub_zero]
      refine hdeg _ _ _ ?_
      have := i.2
      rw [Fin.lt_def] at this
      simp only [ε, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
      exact decide_eq_decide.2 (by omega)
  · refine fun i k => hmap _ _ _ fun k₁ z f hz hf => ?_
    split_ifs
    · cases k₁ with
      | zero => rw [LinearMap.rTensor_tmul, hF.d_zero i z hz, TensorProduct.zero_tmul]; exact Submodule.zero_mem _
      | succ k₁ => rw [LinearMap.rTensor_tmul]; exact hin (hF.d_mem i _ z hz) (by omega)
    · rw [LinearMap.lTensor_tmul]
      cases hf' : f.totalDegree with
      | zero => rw [hdd0 _ _ f hf'.le, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | succ l => have := hddl i.1.1 i.1.2 f l hf'.le; exact hin hz (by omega)
  · refine fun i => hmap _ _ ⊥ fun k₁ z f hz hf => ?_
    obtain rfl : k₁ = 0 := by omega
    split_ifs
    · simp [hF.d_zero i z hz]
    · simp [hdd0 _ _ f (by omega)]
end CompanionTheory.D.LK
