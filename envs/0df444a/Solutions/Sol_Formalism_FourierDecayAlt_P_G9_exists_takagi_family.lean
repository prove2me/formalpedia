-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.exists_takagi_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:32.962912+00:00
-- url     : https://prove2.me/submissions/464a30ee-aa03-42fe-a433-f5c9a1abac02

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_exists_takagi_vector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate
open Module
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution (T : E →ₗ⋆[ℂ] E) (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪T y, x⟫_ℂ) :
    ∀ (n : ℕ) (S : Submodule ℂ E), finrank ℂ S = n → (∀ x ∈ S, T x ∈ S) →
      ∃ (e : Fin n → E) (σ : Fin n → ℝ), Orthonormal ℂ e ∧ (∀ i, e i ∈ S) ∧ (∀ i, 0 ≤ σ i) ∧
        ∀ i, T (e i) = (σ i : ℂ) • e i := by
  intro n
  induction n with
  | zero =>
    intro S _ _
    exact ⟨fun i => i.elim0, fun i => i.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro S hn hS
    have hne : S ≠ ⊥ := by
      rintro rfl
      simp at hn
    obtain ⟨v, hvS, σ₀, hσ₀, hv1, hTv⟩ := exists_takagi_vector T hT S hS hne
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv1
    have hle : (ℂ ∙ v) ≤ S := (Submodule.span_singleton_le_iff_mem _ _).2 hvS
    have hfr : finrank ℂ ((ℂ ∙ v)ᗮ ⊓ S : Submodule ℂ E) = n := by
      have h := Submodule.finrank_add_inf_finrank_orthogonal hle
      rw [finrank_span_singleton hv0, hn] at h
      omega
    have hS' : ∀ x ∈ ((ℂ ∙ v)ᗮ ⊓ S : Submodule ℂ E), T x ∈ ((ℂ ∙ v)ᗮ ⊓ S : Submodule ℂ E) := by
      intro x hx
      refine ⟨?_, hS _ hx.2⟩
      have hx1 : ⟪v, x⟫_ℂ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 hx.1
      refine Submodule.mem_orthogonal_singleton_iff_inner_left.2 ?_
      rw [hT, hTv, inner_smul_left, hx1, mul_zero]
    obtain ⟨e, σ, he, heS, hσ, hTe⟩ := ih _ hfr hS'
    have hve : ∀ i, ⟪v, e i⟫_ℂ = 0 := fun i =>
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 (heS i).1
    have hev : ∀ i, ⟪e i, v⟫_ℂ = 0 := fun i =>
      Submodule.mem_orthogonal_singleton_iff_inner_left.1 (heS i).1
    refine ⟨Fin.cons v e, Fin.cons σ₀ σ, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hv1
      · simpa using he.1 j
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using hve j
      | succ i =>
        induction j using Fin.cases with
        | zero => simpa using hev i
        | succ j =>
          have : i ≠ j := fun h => hij (by rw [h])
          simpa using he.2 this
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hvS
      · simpa using (heS j).2
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hσ₀
      · simpa using hσ j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hTv
      · simpa using hTe j
end Formalism.FourierDecayAlt.P.G9
