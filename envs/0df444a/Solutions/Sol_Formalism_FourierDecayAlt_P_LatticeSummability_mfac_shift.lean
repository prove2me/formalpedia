-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LatticeSummability.mfac_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:18.024459+00:00
-- url     : https://prove2.me/submissions/ee105039-d9cd-4dec-86ce-cfcbd594d7cd

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Finset Function
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LatticeSummability
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.LatticeSummability
theorem _root_.solution (K : ℕ) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) {a : ℝ} (ha : 0 ≤ a) :
    mfac K L a ≤ mfac K (L + δ) (a + δ) := by
  unfold mfac
  have had : a + δ ≠ 0 := by linarith
  rw [if_neg had]
  have hone : ∀ {x : ℝ}, 1 ≤ x → min 1 (x ^ K) = 1 := fun hx => min_eq_left (one_le_pow₀ hx)
  rcases le_or_gt L a with hLa | hLa
  · have ha0 : a ≠ 0 := by linarith
    rw [if_neg ha0]
    have hapos : 0 < a := by linarith
    refine min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg hL.le hapos.le) ?_ K)
    rw [div_le_div_iff₀ hapos (by linarith)]
    nlinarith
  · have h1 : 1 ≤ (L + δ) / (a + δ) := (one_le_div (by linarith : (0 : ℝ) < a + δ)).mpr (by linarith)
    rw [hone h1]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
end Formalism.FourierDecayAlt.P.LatticeSummability
