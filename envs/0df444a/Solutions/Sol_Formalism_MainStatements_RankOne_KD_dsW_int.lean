-- Prove2me | solution 1 for Formalism.MainStatements.RankOne.KD.dsW_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:34:18.184115+00:00
-- url     : https://prove2.me/submissions/08c32d4f-bd07-47b7-b801-e3a8b06af27a

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
import Definitions.Def_CompanionTheory_AutomorphicTheory_RankOneTori_KDense
import Theorems.Thm_Formalism_MainStatements_RankOne_KD_int_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_hasDerivAt
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_continuous_orbit
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_cons
import Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_integral_cpt
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_CompanionTheory_D_Upq_Sm_continuous_orbit__18ceb79e4f38
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
theorem _root_.solution (hG : IsMatGroup G) (hKG : K ⊆ G) (h : RepOn G σ) {v : H} (hv : IsSm G σ v) (μ : Measure (MG K hK))
    [IsFiniteMeasure μ] (p : C(MG K hK, ℝ)) : ∀ {W : List (Mat n)}, LieW G W →
    dsW σ W (∫ g, p g • σ g.mat v ∂μ) = ∫ g, p g • dsW σ W (σ g.mat v) ∂μ
  | [], _ => rfl
  | X :: W, hXW => by
    have hW : LieW G W := fun Y hY => hXW Y (List.mem_cons_of_mem _ hY)
    have hX := hXW X List.mem_cons_self
    have hj : Continuous fun g : MG K hK => MG.mk hG g.mat (hKG g.mem) := MG.continuous_iff.2 MG.continuous_mat
    have c1 : Continuous fun g : MG K hK => dsW σ W (σ g.mat v) := (continuous_orbit (hG := hG) h hv hW).comp hj
    have c2 : ∀ {W' : List (Mat n)}, LieW G W' →
        Continuous fun q : ℝ × MG K hK => σ (ex X q.1) (dsW σ W' (σ q.2.mat v)) := fun hW' =>
      (continuous_orbit₂ (hG := hG) h hv hW' hX).comp (continuous_fst.prodMk (hj.comp continuous_snd))
    rw [dsW_cons, solution hG hKG h hv μ p hW]
    have e : ∀ t, σ (ex X t) (∫ g, p g • dsW σ W (σ g.mat v) ∂μ) =
        ∫ g, p g • σ (ex X t) (dsW σ W (σ g.mat v)) ∂μ := fun t => by
      rw [← (σ (ex X t)).integral_comp_comm (int_smul μ p c1)]
      simp only [ContinuousLinearMap.map_smul_of_tower]
    have := hasDerivAt_integral_cpt (μ := μ)
      (F := fun t g => p g • σ (ex X t) (dsW σ W (σ g.mat v)))
      (F' := fun t g => p g • σ (ex X t) (dsW σ (X :: W) (σ g.mat v)))
      (fun t => p.continuous.smul ((c2 hW).comp (Continuous.prodMk_right t)))
      ((p.continuous.comp continuous_snd).smul (c2 hXW))
      (fun t a => (((hv.apply h (hKG a.mem)).dsW h hW).hasDerivAt h hX t).fun_const_smul _)
      isCompact_univ (fun a ha => absurd (mem_univ a) ha) (fun t _ a ha => absurd (mem_univ a) ha)
    unfold ds
    simp_rw [e]
    rw [this.deriv]
    simp [ex_zero, h.map_one]
end Formalism.MainStatements.RankOne.KD
