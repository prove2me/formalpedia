-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.Gard.contDiff_Phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:31.598849+00:00
-- url     : https://prove2.me/submissions/1d50a9d3-15d6-4882-9270-59451e87b099

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_contDiff_mul
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
theorem _root_.solution {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : Matrix (Fin n) (Fin n) ℂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => f (p.2.1 * p.1) • p.2.2 := by
  have h1 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => (p.2.1, p.1) :=
    contDiff_snd.fst.prodMk contDiff_fst
  have h2 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => p.2.1 * p.1 := by
    have := contDiff_mul.comp h1
    simpa only [Function.comp_def] using this
  have h3 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => f (p.2.1 * p.1) :=
    hf.comp h2
  exact h3.smul contDiff_snd.snd
end CompanionTheory.D.gk.admitted.Gard
