-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TheSecStab.sZ_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:00:42.630516+00:00
-- url     : https://prove2.me/submissions/8a974190-deb2-4aa0-9a49-48ddee302151

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSectionStab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSecStab
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
variable {k : ℕ}
namespace Formalism.FourierDecayAlt.P.TheSecStab
theorem _root_.solution {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) : sZ T T' ζ ≠ 0 := by
  have hTT : 0 < T * T' := mul_pos hT hT'
  have h1 : 1 < Complex.normSq ζ / (T * T') := by
    rw [lt_div_iff₀ hTT, one_mul]
    exact hζ
  unfold sZ
  have hp : 0 < Real.sqrt (Complex.normSq ζ / (T * T') - 1) := Real.sqrt_pos.2 (by linarith)
  exact_mod_cast hp.ne'
end Formalism.FourierDecayAlt.P.TheSecStab
