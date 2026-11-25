-- Prove2me | solution 1 for Formalism.MainStatements.RankOne.KD.fin_of_finAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:55:58.709174+00:00
-- url     : https://prove2.me/submissions/e5d9801d-b61f-48b4-99e8-b27f8f31ee09

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
import Definitions.Def_CompanionTheory_AutomorphicTheory_RankOneTori_KDense
import Theorems.Thm_Formalism_MainStatements_RankOne_KD_int_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_continuous_orbit
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
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
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open Formalism Formalism.MainStatements Formalism.MainStatements.RankOne Formalism.MainStatements.RankOne.KD
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm
variable {n : ℕ} {K : Set (Mat n)} {hK : IsMatGroup K}
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] {G : Set (Mat n)}
  {σ : Mat n → (H →L[ℂ] H)} [CompactSpace (MG K hK)]
namespace Formalism.MainStatements.RankOne.KD
theorem _root_.solution (hG : IsMatGroup G) (hKG : K ⊆ G) (h : RepOn G σ) {v : H} (hv : IsSm G σ v)
    {p : C(MG K hK, ℝ)} (hp : p ∈ finAlg (MG K hK)) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ (∫ g, p g • σ g.mat v ∂haar) ∈ S ∧ ∀ a ∈ K, ∀ x ∈ S, σ a x ∈ S := by
  obtain ⟨V, ⟨⟨s, hs⟩, hinv⟩, hpV⟩ := hp
  have hj : Continuous fun g : MG K hK => MG.mk hG g.mat (hKG g.mem) := MG.continuous_iff.2 MG.continuous_mat
  have c1 : Continuous fun g : MG K hK => σ g.mat v :=
    (continuous_orbit (hG := hG) (W := []) h hv fun _ hX => absurd hX List.not_mem_nil).comp hj
  let T : C(MG K hK, ℝ) →ₗ[ℝ] H :=
    { toFun := fun q => ∫ g, q g • σ g.mat v ∂haar
      map_add' := fun q q' => by
        simp only [ContinuousMap.add_apply, add_smul]
        exact integral_add (int_smul _ q c1) (int_smul _ q' c1)
      map_smul' := fun c q => by
        simp only [ContinuousMap.smul_apply, smul_assoc, RingHom.id_apply]
        exact integral_smul _ _ }
  have hS : Submodule.span ℂ (V.map T : Set H) = Submodule.span ℂ (T '' s) := by
    rw [← hs, Submodule.map_span, Submodule.span_span_of_tower]
  refine ⟨Submodule.span ℂ (V.map T : Set H), ?_, Submodule.subset_span ⟨p, hpV, rfl⟩, fun a ha x hx => ?_⟩
  · rw [hS]; exact FiniteDimensional.span_of_finite ℂ (s.finite_toSet.image _)
  · refine Submodule.span_induction (fun y hy => ?_) (by simp) (fun y z _ _ hy hz => by rw [map_add]; exact add_mem hy hz)
      (fun c y _ hy => by rw [map_smul]; exact Submodule.smul_mem _ c hy) hx
    obtain ⟨q, hq, rfl⟩ := hy
    set a' : MG K hK := MG.mk hK a ha with ha'
    refine Submodule.subset_span ⟨tr a'⁻¹ q, hinv _ q hq, ?_⟩
    show ∫ g, q (a'⁻¹ * g) • σ g.mat v ∂haar = σ a (∫ g, q g • σ g.mat v ∂haar)
    rw [← (σ a).integral_comp_comm (int_smul _ q c1),
      ← integral_mul_left_eq_self (fun g : MG K hK => q (a'⁻¹ * g) • σ g.mat v) a']
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [inv_mul_cancel_left, ContinuousLinearMap.map_smul_of_tower]
    congr 1
    exact h.apply_mul (hKG ha) (hKG g.mem) v
end Formalism.MainStatements.RankOne.KD
