-- Prove2me | solution 1 for Formalism.REAL.pderiv_pderiv_comm_real_place_taylor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:35:04.590647+00:00
-- url     : https://prove2.me/submissions/f3d7b868-97cd-4a2b-a721-6d506b0fbba4

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {σ : Type*} (v w : σ) (f : MvPolynomial σ ℂ) :
    pderiv v (pderiv w f) = pderiv w (pderiv v f) := by
  classical
  have hc : ⁅(pderiv v : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)),
      (pderiv w : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    rw [Derivation.commutator_apply]
    simp only [pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  have hf := congrArg (fun D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) => D f) hc
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at hf
  exact sub_eq_zero.mp hf
end Formalism.REAL
