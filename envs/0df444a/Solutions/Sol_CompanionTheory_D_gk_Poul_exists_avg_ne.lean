-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.exists_avg_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:57:25.006262+00:00
-- url     : https://prove2.me/submissions/e449d3dd-ff9c-4a1c-ba5c-006a84b61d39

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsBump_cpt
import Theorems.Thm_CompanionTheory_D_gk_Poul_exists_isBump
import Theorems.Thm_CompanionTheory_D_Upq_Sm_isCompact_supp
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_eq_zero_of_alt_alt
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_exists_nhds_close


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {hG : IsMatGroup G}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat n → (H →L[ℂ] H)}
namespace CompanionTheory.D.gk.Poul
theorem _root_.solution (hG : IsMatGroup G) (θ : Mat n →L[ℝ] Mat n) (hθ : ∀ x ∈ G, θ x = x⁻¹) (h : RepOn G σ)
    (hc : ∀ v, ContinuousOn (fun g => σ g v) G) {u : H} (hu : u ≠ 0) : ∃ φ, IsBump G φ ∧ avg hG φ σ u ≠ 0 := by
  have hρ : ∀ u, Continuous fun x : MG G hG => σ x.mat u := fun u =>
    (hc u).comp_continuous MG.continuous_mat fun g => g.mem
  obtain ⟨V, hV, hclose⟩ := exists_nhds_close (fun x : MG G hG => σ x.mat) hρ
    (fun u => by show σ 1 u = u; rw [h.map_one]; rfl) (Submodule.span ℂ {u})
  obtain ⟨φ, hφ, hφV⟩ := exists_isBump hG θ hθ hV
  refine ⟨φ, hφ, fun h0 => hu ?_⟩
  exact eq_zero_of_alt_alt (haar : Measure (MG G hG)) (fun x : MG G hG => σ x.mat) hρ
    (hφ.smooth.continuous.comp MG.continuous_mat)
    (HasCompactSupport.intro (isCompact_supp hφ.cpt) fun x hx => image_eq_zero_of_notMem_tsupport (f := φ) hx)
    (fun x => hφ.nonneg _) hφ.one u (fun x hx => hclose x (hφV x hx) u (Submodule.mem_span_singleton_self u)) h0
end CompanionTheory.D.gk.Poul
