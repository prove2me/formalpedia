-- Prove2me | solution 1 for Formalism.HadamardInequality.P.tr_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:00:51.094561+00:00
-- url     : https://prove2.me/submissions/6b2f4ef8-629c-4c5c-8e9e-66a48dc46110

import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_NormUnitaryBounds_NormUnitary
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShortIndependentVectorsOfDualMinimum
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Theorems.Thm_Formalism_H_dualDual
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_H_dualIsLattice
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_gn1
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h1
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_discreteTopology_of_norm_ge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HadamardInequality Formalism.HadamardInequality.P
namespace Formalism.HadamardInequality.P
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Submodule ℤ E) (hspan : span ℝ (M : Set E) = ⊤)
    (W : Submodule ℝ E) {t : ℝ} (ht : 0 < t)
    (hmin : ∀ m ∈ M, Wᗮ.starProjection m ≠ 0 → t ≤ ‖Wᗮ.starProjection m‖) :
    ∃ y : Fin (finrank ℝ Wᗮ) → E, (∀ j, y j ∈ Formalism.HadamardInequality.zdual M) ∧ LinearIndependent ℝ y ∧
      ∀ j, ‖y j‖ ≤ (finrank ℝ Wᗮ : ℝ) ^ ((3 : ℝ) / 2) / t := by
  let P : E →ₗ[ℝ] Wᗮ := (Wᗮ.orthogonalProjectionOnto : E →L[ℝ] Wᗮ).toLinearMap
  have hP : ∀ x : E, ((P x : Wᗮ) : E) = Wᗮ.starProjection x := fun x => rfl
  let Q' : Submodule ℤ Wᗮ := M.map (P.restrictScalars ℤ)
  have hmemQ : ∀ x : Wᗮ, x ∈ Q' ↔ ∃ m ∈ M, P m = x := by
    intro x; simp [Q']
  have hQnorm : ∀ x ∈ Q', x ≠ 0 → t ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨m, hm, rfl⟩ := (hmemQ x).1 hx
    have h1 : Wᗮ.starProjection m ≠ 0 := by
      rw [← hP]; exact_mod_cast hx0
    have := hmin m hm h1
    rw [← hP] at this
    simpa using this
  have hQd : DiscreteTopology Q' := Formalism.NormUnitaryCountingLemmas.discreteTopology_of_norm_ge Q' ht hQnorm
  have hQl : IsZLattice ℝ Q' := ⟨by
    rw [eq_top_iff]
    intro x _
    have hx : (x : E) ∈ span ℝ (M : Set E) := by rw [hspan]; trivial
    have hPx : P (x : E) = x := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
    rw [← hPx]
    have : P (x : E) ∈ (span ℝ (M : Set E)).map P := Submodule.mem_map_of_mem hx
    rw [Submodule.map_span] at this
    refine span_mono ?_ this
    rintro _ ⟨m, hm, rfl⟩
    exact (hmemQ _).2 ⟨m, hm, rfl⟩⟩
  obtain ⟨hXd, hXl⟩ := Formalism.H.dualIsLattice (Wᗮ) Q'
  have := @hXl hXd
  have hDD := Formalism.H.dualDual (Wᗮ) Q'
  obtain ⟨v, hvX, hvli, hvn⟩ := Formalism.NormUnitaryCountingLemmas.Final.gn1 Wᗮ (Formalism.H.dual Q') hXd IsZLattice.span_top
    t ht (by
      intro y hy0 hint
      have hyQ : y ∈ Q' := by
        rw [← hDD, LinearMap.BilinForm.mem_dualSubmodule]
        intro x hx
        obtain ⟨z, hz⟩ := hint x hx
        rw [Submodule.mem_one]
        exact ⟨z, by rw [algebraMap_int_eq, eq_intCast, ← hz]; exact real_inner_comm _ _⟩
      exact hQnorm y hyQ hy0)
  refine ⟨fun j => (v j : E), fun j => ?_, ?_, fun j => ?_⟩
  · intro x hx
    have h := (LinearMap.BilinForm.mem_dualSubmodule _).1 (hvX j) (P x) ((hmemQ _).2 ⟨x, hx, rfl⟩)
    obtain ⟨z, hz⟩ := Submodule.mem_one.1 h
    refine ⟨z, ?_⟩
    rw [algebraMap_int_eq, eq_intCast] at hz
    change (z : ℝ) = inner ℝ (v j) (P x) at hz
    have e1 : inner ℝ x (v j : E) = inner ℝ (P x) (v j) :=
      (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (v j) x).symm
    show inner ℝ x (v j : E) = z
    rw [e1, real_inner_comm, hz]
  · exact hvli.map' Wᗮ.subtype (Submodule.ker_subtype _)
  · simpa using hvn j
end Formalism.HadamardInequality.P
