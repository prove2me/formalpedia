-- Prove2me | solution 1 for Formalism.REAL.normSq_det_indefinite_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:27:42.151513+00:00
-- url     : https://prove2.me/submissions/49c78254-c360-4dcf-ab54-7986a0d6cd90

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Theorems.Thm_Formalism_REAL_Jm_mul_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Metric Kronecker
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Complex.normSq g.det = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ : (Jm ε).det ≠ 0 := by
    have := congrArg Matrix.det (Jm_mul_self ε)
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0; rw [h0, zero_mul] at this; exact zero_ne_one this
  have h2 : star g.det * g.det = 1 := by
    have : (star g.det * g.det - 1) * (Jm ε).det = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h3 | h3
    · linear_combination h3
    · exact absurd h3 hJ
  rw [Complex.star_def] at h2
  have h3 : (Complex.normSq g.det : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact h2
  exact_mod_cast h3
end Formalism.REAL
