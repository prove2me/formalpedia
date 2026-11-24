-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.coefficient_isometry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:41.986342+00:00
-- url     : https://prove2.me/submissions/510339bc-401d-4f6d-8f90-4e9e152c3191

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CoeffIso := by
  intro G H₁ H₂ _ _ _ _ _ _ _ U₁ U₂ hU₁ hU₂ v₁ v₂ hcoef hcyc
  have hin₁ : ∀ g x y, inner ℂ (U₁ g x) (U₁ g y) = inner ℂ x y := fun g x y =>
    (LinearIsometry.mk (U₁ g).toLinearMap (hU₁ g)).inner_map_map x y
  have hin₂ : ∀ g x y, inner ℂ (U₂ g x) (U₂ g y) = inner ℂ x y := fun g x y =>
    (LinearIsometry.mk (U₂ g).toLinearMap (hU₂ g)).inner_map_map x y
  have hmul₁ : ∀ g h x, U₁ (g * h) x = U₁ g (U₁ h x) := by
    intro g h x; rw [map_mul]; rfl
  have hmul₂ : ∀ g h x, U₂ (g * h) x = U₂ g (U₂ h x) := by
    intro g h x; rw [map_mul]; rfl
  have hpair₁ : ∀ g h, inner ℂ (U₁ g v₁) (U₁ h v₁) = inner ℂ v₁ (U₁ (g⁻¹ * h) v₁) := by
    intro g h
    have : U₁ h v₁ = U₁ g (U₁ (g⁻¹ * h) v₁) := by
      rw [← hmul₁]; simp
    rw [this, hin₁]
  have hpair₂ : ∀ g h, inner ℂ (U₂ g v₂) (U₂ h v₂) = inner ℂ v₂ (U₂ (g⁻¹ * h) v₂) := by
    intro g h
    have : U₂ h v₂ = U₂ g (U₂ (g⁻¹ * h) v₂) := by
      rw [← hmul₂]; simp
    rw [this, hin₂]
  set T₁ : (G →₀ ℂ) →ₗ[ℂ] H₁ := Finsupp.linearCombination ℂ (fun g => U₁ g v₁) with hT₁
  set T₂ : (G →₀ ℂ) →ₗ[ℂ] H₂ := Finsupp.linearCombination ℂ (fun g => U₂ g v₂) with hT₂
  have hinner : ∀ c d, inner ℂ (T₁ c) (T₁ d) = inner ℂ (T₂ c) (T₂ d) := by
    intro c d
    simp only [hT₁, hT₂, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hpair₁, hpair₂, hcoef]
  have hnorm : ∀ c, ‖T₁ c‖ = ‖T₂ c‖ := by
    intro c
    have := hinner c c
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
    have h2 : ‖T₁ c‖ ^ 2 = ‖T₂ c‖ ^ 2 := by exact_mod_cast this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  have hr₂ : LinearMap.range T₂ = Submodule.span ℂ (Set.range fun g => U₂ g v₂) :=
    Finsupp.range_linearCombination _
  have hr₁ : LinearMap.range T₁ = Submodule.span ℂ (Set.range fun g => U₁ g v₁) :=
    Finsupp.range_linearCombination _
  have hdense : DenseRange T₂ := by
    have := (Submodule.dense_iff_topologicalClosure_eq_top).mpr hcyc
    rw [← hr₂] at this
    exact this
  have hbd : ∃ C : ℝ, ∀ x, ‖T₁ x‖ ≤ C * ‖T₂ x‖ := ⟨1, fun x => by rw [hnorm, one_mul]⟩
  set J0 := T₁.extendOfNorm T₂ with hJ0def
  have hJ0 : ∀ c, J0 (T₂ c) = T₁ c := fun c => LinearMap.extendOfNorm_eq hdense hbd c
  have hJnorm : ∀ x, ‖J0 x‖ = ‖x‖ := by
    refine hdense.induction ?_ (isClosed_eq (by fun_prop) continuous_norm)
    rintro _ ⟨c, rfl⟩
    rw [hJ0, hnorm]
  have hs₁ : ∀ g (a : ℂ), T₁ (Finsupp.single g a) = a • U₁ g v₁ := by
    intro g a; simp [hT₁]
  have hs₂ : ∀ g (a : ℂ), T₂ (Finsupp.single g a) = a • U₂ g v₂ := by
    intro g a; simp [hT₂]
  have horb : ∀ g, J0 (U₂ g v₂) = U₁ g v₁ := by
    intro g
    have := hJ0 (Finsupp.single g 1)
    rwa [hs₁, hs₂, one_smul, one_smul] at this
  refine ⟨⟨J0.toLinearMap, hJnorm⟩, ?_, ?_, ?_⟩
  · have := horb 1
    simpa using this
  · intro g
    show ∀ x, J0 (U₂ g x) = U₁ g (J0 x)
    refine hdense.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop))
    rintro _ ⟨c, rfl⟩
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single h a =>
      rw [hs₂, map_smul, map_smul, map_smul, map_smul, ← hmul₂, horb, horb, hmul₁]
  · apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      show J0 x ∈ _
      revert x
      refine hdense.induction ?_ ?_
      · rintro _ ⟨c, rfl⟩
        rw [hJ0]
        apply Submodule.le_topologicalClosure
        rw [← hr₁]
        exact LinearMap.mem_range_self _ _
      · exact (Submodule.isClosed_topologicalClosure _).preimage J0.continuous
    · have hcl : IsClosed ((LinearMap.range J0.toLinearMap : Submodule ℂ H₁) : Set H₁) := by
        have hiso : Isometry J0 := AddMonoidHomClass.isometry_of_norm J0 hJnorm
        exact hiso.isClosedEmbedding.isClosed_range
      have hle : Submodule.span ℂ (Set.range fun g => U₁ g v₁) ≤ LinearMap.range J0.toLinearMap := by
        rw [Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        exact ⟨U₂ g v₂, horb g⟩
      intro y hy
      obtain ⟨x, hx⟩ := Submodule.topologicalClosure_minimal _ hle hcl hy
      exact ⟨x, hx⟩
end Formalism.HermitianLatticeCounting.P
