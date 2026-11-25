-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.hasDerivAt_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:16.652254+00:00
-- url     : https://prove2.me/submissions/4e9b1982-3a36-451d-98d7-f9a4ed203481

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_integral_cpt
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_hasDerivAt
import Theorems.Thm_CompanionTheory_D_Upq_Sm_isCompact_supp
import Theorems.Thm_CompanionTheory_D_Upq_Sm_continuous_orbit
import Theorems.Thm_P2M_CompanionTheory_D_Upq_Sm_continuous_orbit__18ceb79e4f38
import Theorems.Thm_CompanionTheory_D_Upq_Sm_apply_integral
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
variable {hG : IsMatGroup G}
variable [CompleteSpace H]
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {X : Mat n} (hX : ∀ t, ex X t ∈ G)
    {W : List (Mat n)} (hW : LieW G W) {φ : Mat n → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    HasDerivAt (fun t => σ (ex X t) (∫ g : MG G hG, φ g.mat • dsW σ W (σ g.mat v) ∂haar))
      (∫ g : MG G hG, φ g.mat • dsW σ (X :: W) (σ g.mat v) ∂haar) 0 := by
  have hXW : LieW G (X :: W) := fun Y hY => by
    rcases List.mem_cons.1 hY with rfl | hY
    exacts [hX, hW Y hY]
  simp_rw [apply_integral _ hφ hc (continuous_orbit h hv hW)]
  have hφ' : Continuous fun g : MG G hG => φ g.mat := hφ.comp MG.continuous_mat
  have := hasDerivAt_integral_cpt (μ := (haar : Measure (MG G hG)))
    (F := fun t g => φ g.mat • σ (ex X t) (dsW σ W (σ g.mat v)))
    (F' := fun t g => φ g.mat • σ (ex X t) (dsW σ (X :: W) (σ g.mat v)))
    (fun t => hφ'.smul ((continuous_orbit₂ h hv hW hX).comp (Continuous.prodMk_right t)))
    ((hφ'.comp continuous_snd).smul (continuous_orbit₂ h hv hXW hX))
    (fun t a => (((hv.apply h a.mem).dsW h hW).hasDerivAt h hX t).fun_const_smul _)
    (isCompact_supp hc)
    (fun a ha => by rw [image_eq_zero_of_notMem_tsupport ha, zero_smul])
    (fun t _ a ha => by rw [image_eq_zero_of_notMem_tsupport ha, zero_smul])
  simpa [ex_zero, h.map_one] using this
end CompanionTheory.D.Upq.Sm
