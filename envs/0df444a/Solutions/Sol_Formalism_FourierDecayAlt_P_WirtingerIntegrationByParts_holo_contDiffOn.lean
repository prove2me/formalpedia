-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.holo_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:44.733801+00:00
-- url     : https://prove2.me/submissions/6022b46b-f3db-4666-a94d-34317d712aa1

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_differentiableOn_fderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F} (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (n : ℕ) :
    ContDiffOn ℂ n g Ω := by
  induction n generalizing F with
  | zero =>
    have h0 : ContDiffOn ℂ 0 g Ω := contDiffOn_zero.2 hg.continuousOn
    simpa using h0
  | succ n ih =>
    have h : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [h, contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨hg, fun h => ?_, ih (hol_differentiableOn_fderiv hΩ hg)⟩
    exact absurd h (by simp)
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
