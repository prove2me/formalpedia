-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx1.t_AxiomsAgree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:15.30284+00:00
-- url     : https://prove2.me/submissions/98304c3c-4cdd-4932-9b49-35f09967bbce

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_conv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
namespace Formalism.FourierDecayAlt.P.Jx1
theorem _root_.solution : AxiomsAgree := by
  unfold AxiomsAgree
  intro E W _ _ D hK hA2 hA13
  unfold TB.Data.KernelPSD at hK
  unfold TB.Data.KernelSupport at hA2
  unfold TB.Data.ThetaDomination at hA13
  have hlv : ∀ j (h : TB.Pt E), TA.IsPt j h → TB.level h = j := by
    intro j h hh
    first
    | exact hh.1
    | (have h0 := hh.1
       simpa [TA.lvl, TB.level] using h0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold TA.AxK
    exact ⟨D.K0, fun i _ P _ => conv P (D.Kr i) (hK.1 i P)⟩
  · unfold TA.KernelSupport
    intro i s hs hsi hir h h' t t' hh hh' ht ht' hor
    show D.Kr i (TA.ext h' s t') (TA.ext h s t) = 0
    by_contra hne
    by_cases htt : t' = t
    · subst htt
      rcases hor with h1 | h1
      · exact h1 (by simp)
      · exact h1.2.2 rfl
    · obtain ⟨h1, h2⟩ := hA2 i s hs hsi hir h' h t' t (hlv _ _ hh') (hlv _ _ hh) ht' ht htt hne
      rcases hor with h3 | h3
      · apply h3
        show 1 / t - 1 / t' ∈ D.Lap (i - s + 1) s
        have h4 := neg_mem h2
        simpa [one_div, neg_sub] using h4
      · exact h1 ⟨h3.1, h3.2.1⟩
  · unfold TA.ThetaDomination
    intro i s hs hsi hir
    obtain ⟨-, hC, hL, hS⟩ := hA13 i s hs hsi hir
    refine ⟨fun t Hd _ => conv Hd _ (hK.2 i s t Hd), fun t l hl => ?_, fun t Hd ht hHd => ?_,
      fun R Hd hR hHd => ?_⟩
    · show (fun h h' => D.Th i s (t + l) h' h) = (fun h h' => D.Th i s t h' h)
      have hl' : t + l - t ∈ D.La (i - s + 1) s := by
        rw [add_sub_cancel_left]
        exact hl
      rw [hL (t + l) t hl']
    · exact conv Hd _ (hC t ht Hd fun h hh => hlv _ _ (hHd h hh))
    · have h5 := conv Hd _ (hS R hR Hd fun h hh => hlv _ _ (hHd h hh))
      have e : ((1 + D.e i : ℝ) : ℂ) = 1 + (D.e i : ℂ) := by push_cast; ring
      show TA.PSDOn Hd (fun h h' => ((1 + D.e i : ℝ) : ℂ) * D.Kr (i - s) h' h - ∑ t ∈ R, D.Th i s t h' h)
      rw [e]
      exact h5
  · unfold TA.AxE
    intro i hi hir
    exact (hA13 i 1 le_rfl hi hir).1
end Formalism.FourierDecayAlt.P.Jx1
