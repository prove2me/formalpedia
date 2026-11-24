-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.zinv_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:56:18.878853+00:00
-- url     : https://prove2.me/submissions/5044e5cb-3357-4907-9953-5508a6a31cb7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_normSq_cd
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_sc_cd
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_sc_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {c : ℝ} (hc : 0 < c) (m : ℕ) : ContDiff ℝ ∞ (zinv c m) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · have hev : zinv c m =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      have hopen : IsOpen {w : ℂ | Complex.normSq w < c / 4} :=
        isOpen_lt normSq_cd.continuous continuous_const
      have hmem : z ∈ {w : ℂ | Complex.normSq w < c / 4} := by
        show Complex.normSq z < c / 4
        rw [hz, map_zero]
        positivity
      filter_upwards [hopen.mem_nhds hmem] with w hw
      unfold zinv
      rw [sc_zero hc (le_of_lt hw)]
      simp
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · unfold zinv
    have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => ((sc c (Complex.normSq w) : ℝ) : ℂ)) z :=
      (Complex.ofRealCLM.contDiff.comp ((sc_cd c).comp normSq_cd)).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun w : ℂ => w⁻¹ ^ m) z :=
      ((contDiffAt_inv ℂ hz).pow m).restrict_scalars ℝ
    exact h1.mul h2
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
