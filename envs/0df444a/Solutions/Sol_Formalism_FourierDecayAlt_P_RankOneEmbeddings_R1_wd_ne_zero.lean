-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.wd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:24:54.112233+00:00
-- url     : https://prove2.me/submissions/3c49da9d-b4dd-4d04-bd12-ddfc49ecf6f6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_zW_meas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
theorem _root_.solution (z z' : Vc k r) : wd k r z z' ≠ 0 := by
  intro h0
  have hmeas : Measurable fun ζ : ℂ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) :=
    (zW_meas k _ _).ennreal_ofReal
  have h1 : (volume : Measure ℂ).withDensity (fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)) = 0 := h0
  rw [withDensity_eq_zero_iff hmeas.aemeasurable] at h1
  have hc0 : (0 : ℝ) ≤ |Tz k r z * Tz k r z'| + 1 := by positivity
  have hS : IsOpen {ζ : ℂ | |Tz k r z * Tz k r z'| + 1 < Complex.normSq ζ} :=
    isOpen_lt continuous_const Complex.continuous_normSq
  have hne : ({ζ : ℂ | |Tz k r z * Tz k r z'| + 1 < Complex.normSq ζ}).Nonempty := by
    refine ⟨((|Tz k r z * Tz k r z'| + 2 : ℝ) : ℂ), ?_⟩
    show |Tz k r z * Tz k r z'| + 1 < Complex.normSq ((|Tz k r z * Tz k r z'| + 2 : ℝ) : ℂ)
    rw [Complex.normSq_ofReal]
    nlinarith
  have hpos := hS.measure_pos (volume : Measure ℂ) hne
  apply hpos.ne'
  apply measure_mono_null _ (ae_iff.1 h1)
  intro ζ hζ
  have hζ' : |Tz k r z * Tz k r z'| + 1 < Complex.normSq ζ := hζ
  have hlt : Tz k r z * Tz k r z' < Complex.normSq ζ :=
    lt_of_le_of_lt (le_trans (le_abs_self _) (by linarith)) hζ'
  have hp : 0 < (Complex.normSq ζ - Tz k r z * Tz k r z') ^ (k - 1) := pow_pos (by linarith) _
  show ¬ (ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) = 0)
  unfold zWeight
  rw [if_pos hlt.le]
  exact (ENNReal.ofReal_pos.2 hp).ne'
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
