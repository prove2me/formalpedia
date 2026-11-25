-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.contDiff_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:34:28.28074+00:00
-- url     : https://prove2.me/submissions/4ad190e7-9375-40e7-9b7e-1508c4185441

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_contDiff_integral_comp
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_emb_toM
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_contDiff_Phi
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_supp_local
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open MeasureTheory Matrix Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open CompanionTheory.D.gk.admitted.Gard
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.gk.admitted.Gard
theorem _root_.solution {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (v : UJ ε → H) (hv : Continuous v) {f : Matrix (Fin n) (Fin n) ℂ → ℝ} {S : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hf : ContDiff ℝ ∞ f) (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0) (hfS : ∀ y, f y ≠ 0 → y ∈ S) :
    ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => ∫ x : UJ ε, f (toM x⁻¹ * g) • v x ∂(muG ε) := by
  have hq : Continuous fun x : UJ ε => (toM x⁻¹, v x) := (emb_toM.continuous.comp continuous_inv).prodMk hv
  have key := contDiff_integral_comp (muG ε) _ (contDiff_Phi (H := H) hf) _ hq fun g₀ => by
    obtain ⟨U, hU, C, hC, h⟩ := supp_local (ε := ε) hS hd hfS g₀
    refine ⟨U, hU, C, hC, fun g hg x hx => ?_⟩
    simp only [h g hg x hx, zero_smul]
  simpa only using key
end CompanionTheory.D.gk.admitted.Gard
