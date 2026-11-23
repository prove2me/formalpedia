-- Prove2me | solution 1 for CompanionTheory.HCMult.harish_chandra_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:34:39.297291+00:00
-- url     : https://prove2.me/submissions/4361ae6b-9956-4cd2-966d-a0ad8c1dc3ab

import Definitions.Def_Formalism_PeriodIntegrals_HCMult
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinalAll
import Definitions.Def_CompanionTheory_AutomorphicTheory_HarishChandraMultiplicity_HCMult
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_Kset_sub
import Theorems.Thm_CompanionTheory_D_gk_admitted_exists_elt
import Theorems.Thm_CompanionTheory_D_gk_admitted_unitary_group_admissible
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.HCMult
open PI.UpqRep CompanionTheory.D.gk.admitted
namespace CompanionTheory.HCMult
theorem _root_.solution : PI.HCMult := by
  intro n ε H _ _ _ σ hσ hirr S hfd hS
  let b := Module.finBasis ℂ S
  choose Y hYfd _ hvY hY using fun i => unitary_group_admissible n ε H σ hσ hirr S hS (b i) (b i).2
  have hsup : FiniteDimensional ℂ (⨆ i, Y i : Submodule ℂ H) := Submodule.finiteDimensional_iSup Y
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, Y i) (sSup_le ?_)
  rintro _ ⟨Θ, hΘ, rfl⟩
  let T : H →L[ℂ] H := (LinearMap.toContinuousLinearMap Θ).comp S.orthogonalProjectionOnto
  have hT : ∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    have hkU := Kset_sub hk
    have hk1 : k * k.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hk.1
    have hks : k.conjTranspose ∈ Kset ε := by
      refine ⟨Unitary.star_mem hk.1, ?_⟩
      have h1 : k.conjTranspose * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
      calc k.conjTranspose * Jm ε = k.conjTranspose * Jm ε * (k * k.conjTranspose) := by
            rw [hk1, Matrix.mul_one]
        _ = k.conjTranspose * (Jm ε * k) * k.conjTranspose := by simp only [Matrix.mul_assoc]
        _ = Jm ε * k.conjTranspose := by
            rw [← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    have hiso : ∀ x y, ⟪σ k x, σ k y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y =>
      (LinearIsometry.mk (σ k : H →ₗ[ℂ] H) (hσ.2.1 k hkU)).inner_map_map x y
    have hP : ((S.orthogonalProjectionOnto (σ k u) : S) : H) = σ k (S.orthogonalProjectionOnto u : S) := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS k hk _ (S.orthogonalProjectionOnto u).2) ?_
      intro w hw
      have hw' : σ k (σ k.conjTranspose w) = w := by
        rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hkU _ (Kset_sub hks), hk1, hσ.1.1]
        rfl
      rw [← hw', ← map_sub, hiso]
      exact S.starProjection_inner_eq_zero u _ (hS _ hks w hw)
    obtain ⟨g, hg⟩ := exists_elt hkU
    have := hΘ ⟨g, by show toM g ∈ Kset ε; rw [hg]; exact hk⟩ (S.orthogonalProjectionOnto u)
      (S.orthogonalProjectionOnto (σ k u)) (by show _ = σ (toM g) _; rw [hg]; exact hP)
    simpa [T, toMK, hg] using this
  rintro _ ⟨v, rfl⟩
  rw [← b.sum_repr v, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i ?_)
  have := hY i T hT _ (hvY i)
  simpa [T] using this
end CompanionTheory.HCMult
