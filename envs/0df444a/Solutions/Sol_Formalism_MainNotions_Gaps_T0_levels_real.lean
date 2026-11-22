-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.levels_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:24.913579+00:00
-- url     : https://prove2.me/submissions/986c63d7-48d7-4ccb-a32f-2d85faaff0f8

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
namespace Formalism.MainNotions.Gaps.T0
theorem _root_.solution (A B R δ d D T cg c w G PH Pη L F' fr aδ aF HF Hδ SS Λ' lδ : ℝ)
    (hR : 0 ≤ R) (hRδ : R * δ ≤ d) (hδ : 0 ≤ δ) (hlδ : 0 ≤ lδ) (hD : 0 ≤ D) (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hcg0 : 0 ≤ cg) (hcg1 : cg ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ PH * L) (hG : 0 ≤ G) (hPH : 0 ≤ PH)
    (hPη : 0 ≤ Pη) (hL : 0 ≤ L) (hfr : 0 ≤ fr)
    (h1 : 2 * A ≤ δ * lδ + 2 * SS + 2 * D * aF * w + 2 * HF)
    (h2 : B ≤ cg * (Hδ + D * aδ * w) + T * c * δ * Pη)
    (hSS : SS ≤ δ * Λ') (hΛ : Λ' ≤ G * F') (hF : F' ≤ (D + 2) * L + 5 * fr * T)
    (haδ : aδ ≤ 4 / 3 * δ) (haF : aF ≤ 4 / 3 * (D + 4) * δ)
    (hHF : HF ≤ (D + 4) * (D + 1) * δ * (2 * G + 6 * PH) * L)
    (hHδ : Hδ ≤ (D + 1) * δ * (2 * G + 6 * PH) * L) :
    R * (A + 1 / 2 * B) ≤
      d * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by
  have hSS' : SS ≤ δ * (G * ((D + 2) * L + 5 * fr * T)) :=
    hSS.trans (mul_le_mul_of_nonneg_left (hΛ.trans (mul_le_mul_of_nonneg_left hF hG)) hδ)
  have haFw : aF * w ≤ 4 / 3 * (D + 4) * δ * (PH * L) :=
    (mul_le_mul_of_nonneg_right haF hw0).trans (mul_le_mul_of_nonneg_left hw (by positivity))
  have haFw' : D * (aF * w) ≤ D * (4 / 3 * (D + 4) * δ * (PH * L)) := mul_le_mul_of_nonneg_left haFw hD
  have haδw : aδ * w ≤ 4 / 3 * δ * (PH * L) :=
    (mul_le_mul_of_nonneg_right haδ hw0).trans (mul_le_mul_of_nonneg_left hw (by positivity))
  have haδw' : D * (aδ * w) ≤ D * (4 / 3 * δ * (PH * L)) := mul_le_mul_of_nonneg_left haδw hD
  have hXb0 : 0 ≤ (D + 1) * δ * (2 * G + 6 * PH) * L + D * (4 / 3 * δ * (PH * L)) := by positivity
  have hin : Hδ + D * aδ * w ≤ (D + 1) * δ * (2 * G + 6 * PH) * L + D * (4 / 3 * δ * (PH * L)) := by
    have e : D * aδ * w = D * (aδ * w) := by ring
    linarith
  have hB' : B ≤ ((D + 1) * δ * (2 * G + 6 * PH) * L + D * (4 / 3 * δ * (PH * L))) + T * c * δ * Pη := by
    have e2 := mul_le_mul_of_nonneg_left hin hcg0
    have e3 := mul_le_of_le_one_left hXb0 hcg1
    linarith
  have hAB : A + 1 / 2 * B ≤ δ * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by
    have p1 : 0 ≤ δ * G * L * D ^ 2 := by positivity
    have p2 : 0 ≤ δ * G * L * D := by positivity
    have p3 : 0 ≤ δ * G * L := by positivity
    have p4 : 0 ≤ δ * PH * L * D ^ 2 := by positivity
    have p5 : 0 ≤ δ * PH * L * D := by positivity
    have p6 : 0 ≤ δ * PH * L := by positivity
    have p7 : 0 ≤ δ * lδ := by positivity
    have e : D * aF * w = D * (aF * w) := by ring
    linarith
  have hT0 : 0 ≤ ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by positivity
  calc R * (A + 1 / 2 * B) ≤ R * (δ * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη)) := mul_le_mul_of_nonneg_left hAB hR
    _ = (R * δ) * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by ring
    _ ≤ d * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := mul_le_mul_of_nonneg_right hRδ hT0
end Formalism.MainNotions.Gaps.T0
