-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.IsSmForm.avg_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:18:19.04022+00:00
-- url     : https://prove2.me/submissions/ba29e13c-c67c-44a0-94d7-cbd2622188ed

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_continuous
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_continuous_orbit
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_integrable_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_integral_mem_of_isClosed
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsInvariant_topologicalClosure
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
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {hG : IsMatGroup G}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat n → (H →L[ℂ] H)}
variable {ι : Type} [Fintype ι] {W : ι → List (Mat n)} {C : ℝ} {l : H → ℂ}
namespace CompanionTheory.D.gk.Poul
namespace IsSmForm
theorem _root_.solution (hl : IsSmForm G σ W C l) (h : RepOn G σ) (hW : ∀ i, LieW G (W i)) {v : H}
    (hv : IsSm G σ v) {φ : Mat n → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) {x : H} (hx : IsSm G σ x) :
    ‖(∫ g : MG G hG, φ g.mat • l (σ g.mat v) ∂haar) - l x‖ ≤
      C * ∑ i, ‖(∫ g : MG G hG, φ g.mat • dsW σ (W i) (σ g.mat v) ∂haar) - dsW σ (W i) x‖ := by
  let S₀ : Submodule ℂ ((ι → H) × ℂ) :=
    { carrier := {p | ∃ y, IsSm G σ y ∧ p = (fun i => dsW σ (W i) y, l y)}
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, ha.add hb, Prod.ext (funext fun i => (dsW_add h ha hb (hW i)).symm) (hl.add _ _ ha hb).symm⟩
      zero_mem' := ⟨0, IsSm.zero, Prod.ext (funext fun i => by
          simpa using (dsW_smul h (IsSm.zero (G := G) (σ := σ)) 0 (hW i)).symm)
        (by simpa using (hl.smul 0 0 IsSm.zero).symm)⟩
      smul_mem' := by
        rintro c _ ⟨a, ha, rfl⟩
        exact ⟨c • a, ha.smul c, Prod.ext (funext fun i => (dsW_smul h ha c (hW i)).symm) (hl.smul _ _ ha).symm⟩ }
  have hcl : IsClosed {p : (ι → H) × ℂ | ‖p.2‖ ≤ C * ∑ i, ‖p.1 i‖} :=
    isClosed_le continuous_snd.norm (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).norm))
  have hsub : (S₀.topologicalClosure : Set ((ι → H) × ℂ)) ⊆ {p | ‖p.2‖ ≤ C * ∑ i, ‖p.1 i‖} :=
    closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact hl.bd y hy) hcl
  let F : MG G hG → (ι → H) × ℂ := fun g => (fun i => dsW σ (W i) (σ g.mat v), l (σ g.mat v))
  have hF : Continuous F := (continuous_pi fun i => continuous_orbit h hv (hW i)).prodMk (hl.continuous h hW hv)
  have hI := integrable_smul hφ hc hF
  have h1 : ∫ g : MG G hG, φ g.mat • F g ∂haar ∈ S₀.topologicalClosure :=
    integral_mem_of_isClosed _ S₀.isClosed_topologicalClosure fun g =>
      Submodule.smul_of_tower_mem _ _ (S₀.le_topologicalClosure ⟨_, hv.apply h g.mem, rfl⟩)
  have h2 := hsub (Submodule.sub_mem _ h1 (S₀.le_topologicalClosure ⟨x, hx, rfl⟩))
  have e2 := (ContinuousLinearMap.snd ℝ (ι → H) ℂ).integral_comp_comm hI
  have e1 := fun i => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => H) i) ∘L
    ContinuousLinearMap.fst ℝ (ι → H) ℂ).integral_comp_comm hI
  refine le_of_eq_of_le (congrArg (fun t => ‖t - l x‖) e2) (h2.trans (le_of_eq ?_))
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (congrArg (fun t => ‖t - dsW σ (W i) x‖) (e1 i)).symm
end IsSmForm
end CompanionTheory.D.gk.Poul
