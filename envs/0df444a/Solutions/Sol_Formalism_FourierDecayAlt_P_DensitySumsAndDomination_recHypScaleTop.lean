-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DensitySumsAndDomination.recHypScaleTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:25.448324+00:00
-- url     : https://prove2.me/submissions/fb40c9d8-7478-4210-9b04-181f7c52608f

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination
import Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_psd_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DensitySumsAndDomination
namespace Formalism.FourierDecayAlt.P.DensitySumsAndDomination
theorem _root_.solution : RecHypScaleTop := by
  intro hDS hSB E W _ D C₁ C₄ Θ jn H _ _ Vt c c' sd hsd he h hc1 hc2 hc3
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
  have hl1 : (1 : ℝ) ≤ max sd 1 := le_max_right _ _
  have hl0 : (0 : ℝ) ≤ max sd 1 := by linarith
  refine ⟨⟨a1, a2, a3, a4, a5, ?_, a7, ?_, ?_, ?_, a11, a12, a13, a14, a15, a16, ?_, ?_⟩, rfl, rfl, ?_, ?_⟩
  · intro i Y
    by_cases hit : i = D.r + 1
    · refine psd_congr (fun x _ y _ => ?_) (psd_smul _ hl0 (a6 i Y))
      simp [scaleTop, hit]
    · refine psd_congr (fun x _ y _ => ?_) (a6 i Y)
      simp [scaleTop, hit]
  · intro i s hs hsi hi x y t t' hx hy ht ht' htt hne
    refine a8 i s hs hsi hi x y t t' hx hy ht ht' htt ?_
    intro h0
    apply hne
    show (if i = D.r + 1 then ((max sd 1 : ℝ) : ℂ) * D.Kr i (TB.join x s t) (TB.join y s t')
      else D.Kr i (TB.join x s t) (TB.join y s t')) = 0
    rw [h0]; simp
  · intro i h1 hi
    by_cases hit : i = D.r + 1
    · simp only [scaleTop, hit, if_true]
      constructor
      · linarith
      · have : max sd 1 ≤ 2 := max_le hsd (by norm_num)
        linarith
    · simp only [scaleTop, hit, if_false]
      exact a9 i h1 hi
  · intro T
    obtain ⟨Th, hTh⟩ := a10 T
    exact ⟨_, hDS E W D T Th _ hl0 he hTh⟩
  · intro Y hY
    filter_upwards [a17 Y hY] with ε hε p hp q hq hne
    refine hε p hp q hq ?_
    intro h0
    apply hne
    simp [scaleTop, h0]
  · refine ⟨hc1, fun Y hY R => ?_, hc3⟩
    refine psd_congr (fun x _ y _ => ?_) (hSB _ Y (D.Kr (D.r + 1))
      (fun p q => ∑ ρ ∈ R, c' ρ p * conj (c' ρ q)) sd (a6 _ Y) (hc2 Y hY R))
    simp [scaleTop]
  · simp [scaleTop]
  · intro i hi
    have : i ≠ D.r + 1 := by have := (Finset.mem_Icc.1 hi).2; omega
    simp [scaleTop, this]
end Formalism.FourierDecayAlt.P.DensitySumsAndDomination
