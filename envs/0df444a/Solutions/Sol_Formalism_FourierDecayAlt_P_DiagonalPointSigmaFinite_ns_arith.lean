-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:03.18653+00:00
-- url     : https://prove2.me/submissions/f8a63bee-e900-49b5-9d3e-ef242dfa4757

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
theorem _root_.solution (m C₉ q ny : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hkey : ε * (((m : ℝ) + 2) * ((C₉ : ℝ) + 1)) ≤ 1 / 2) (hε2s : ε * ((m : ℝ) + 2) ≤ 1 / 2)
    (hq : q = 4 * m + 12) (hnyle : (ny : ℝ) ≤ ((m : ℝ) + 2) ^ 2) :
    ε * (((m + 2) * C₉ + (m + 2) * (C₉ + 1) * q + 2 * (m + 1) + 2 * ny : ℕ) : ℝ) +
      ((m + 2 : ℕ) : ℝ) ≤ (q : ℝ) := by
  have hqc : (q : ℝ) = 4 * (m : ℝ) + 12 := by rw [hq]; push_cast; ring
  have b1 : ε * (((m : ℝ) + 2) * C₉) ≤ 1 / 2 := by
    refine le_trans ?_ hkey
    gcongr
    linarith
  have b2 : ε * (((m : ℝ) + 2) * ((C₉ : ℝ) + 1)) * q ≤ 1 / 2 * q :=
    mul_le_mul_of_nonneg_right hkey (Nat.cast_nonneg _)
  have b3 : ε * (2 * ((m : ℝ) + 1)) ≤ 1 := by
    have : ε * (2 * ((m : ℝ) + 1)) = 2 * (ε * ((m : ℝ) + 2)) - 2 * ε := by ring
    linarith
  have b4 : ε * (2 * (ny : ℝ)) ≤ (m : ℝ) + 2 := by
    calc ε * (2 * (ny : ℝ)) ≤ ε * (2 * ((m : ℝ) + 2) ^ 2) := by gcongr
      _ = 2 * (ε * ((m : ℝ) + 2)) * ((m : ℝ) + 2) := by ring
      _ ≤ 2 * (1 / 2) * ((m : ℝ) + 2) := by gcongr
      _ = (m : ℝ) + 2 := by ring
  push_cast
  have e : ε * (((m : ℝ) + 2) * C₉ + ((m : ℝ) + 2) * ((C₉ : ℝ) + 1) * q + 2 * ((m : ℝ) + 1) + 2 * (ny : ℝ)) =
      ε * (((m : ℝ) + 2) * C₉) + ε * (((m : ℝ) + 2) * ((C₉ : ℝ) + 1)) * q + ε * (2 * ((m : ℝ) + 1)) +
        ε * (2 * (ny : ℝ)) := by ring
  rw [e]
  linarith
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
