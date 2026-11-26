-- Prove2me | solution 1 for CondMat0408017.scattering_potential_reciprocity
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:30:45.922081+00:00
-- url     : https://prove2.me/submissions/31a5d74f-82d9-493b-b5d0-cd6529faa987

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution (ν : Polarization) (eps : ℂ) (wv : ℝ)
    (α ζ1 ζ2 : ℝ → ℂ) (hα : ∀ q, α (-q) = α q) (q k : ℝ) :
    scatPotV1 ν eps wv α ζ1 q k = scatPotV1 ν eps wv α ζ1 (-k) (-q) ∧
      scatPotV2 ν eps wv α ζ1 ζ2 q k = scatPotV2 ν eps wv α ζ1 ζ2 (-k) (-q) := by
  have hsub : -k - -q = q - k := by ring
  cases ν
  · constructor
    · simp only [scatPotV1, hα, hsub, ofReal_neg]
      ring
    · simp only [scatPotV2, hα, hsub, ofReal_neg]
      have hint : ∫ p, ζ1 (q - p) * α p * ζ1 (p - k) / (2 * (Real.pi : ℂ)) =
          ∫ p, ζ1 (-k - p) * α p * ζ1 (p - -q) / (2 * (Real.pi : ℂ)) := by
        rw [← MeasureTheory.integral_neg_eq_self
          (fun p => ζ1 (-k - p) * α p * ζ1 (p - -q) / (2 * (Real.pi : ℂ)))]
        congr 1
        ext p
        have h1 : -k - -p = p - k := by ring
        have h2 : -p - -q = q - p := by ring
        rw [h1, h2, hα p]
        ring
      rw [hint]
      ring
  · constructor
    · simp only [scatPotV1, hsub]
    · simp only [scatPotV2, hα, hsub]
      ring
