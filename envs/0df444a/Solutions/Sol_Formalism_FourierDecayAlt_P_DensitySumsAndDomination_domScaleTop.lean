-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DensitySumsAndDomination.domScaleTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:45.267241+00:00
-- url     : https://prove2.me/submissions/a6da02e2-fcf0-46f6-a500-5837c3173630

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
theorem _root_.solution : DomScaleTop := by
  intro E W _ D T Th lam hlam he hD
  have hKr : ∀ j x y, (scaleTop D lam).Kr j x y =
      if j = D.r + 1 then (lam : ℂ) * D.Kr j x y else D.Kr j x y := fun _ _ _ => rfl
  have he' : ∀ j, (scaleTop D lam).e j = if j = D.r + 1 then lam - 1 else D.e j := fun _ => rfl
  intro i s hs hsi hir
  obtain ⟨h1, h2, h3⟩ := hD i s hs hsi hir
  have hir' : i ≤ D.r + 1 := hir
  have hne : i - s ≠ D.r + 1 := by omega
  by_cases hi : i = D.r + 1
  · refine ⟨fun t ht => ?_, fun t ht t' ht' hl x hx y hy => ?_, fun S hS hSd => ?_⟩
    · refine psd_congr (k := fun h h' => (lam : ℂ) * (Th i s t h h' - TB.blk (D.Kr i) s t t h h'))
        (fun x _ y _ => ?_) (psd_smul lam hlam (h1 t ht))
      simp only [TB.blk, hKr, if_pos hi]
      ring
    · simp only [if_pos hi]
      rw [h2 t ht t' ht' hl x hx y hy]
    · refine psd_congr
        (k := fun h h' => (lam : ℂ) * ((1 + (D.e i : ℂ)) * D.Kr (i - s) h h' - ∑ t ∈ S, Th i s t h h'))
        (fun x _ y _ => ?_) (psd_smul lam hlam (h3 S hS hSd))
      have he2 : D.e i = 0 := by rw [hi]; exact he
      simp only [hKr, he', if_pos hi, if_neg hne]
      rw [he2, ← Finset.mul_sum]
      push_cast
      ring
  · refine ⟨fun t ht => ?_, fun t ht t' ht' hl x hx y hy => ?_, fun S hS hSd => ?_⟩
    · refine psd_congr (fun x _ y _ => ?_) (h1 t ht)
      simp only [TB.blk, hKr, if_neg hi]
    · simp only [if_neg hi]
      exact h2 t ht t' ht' hl x hx y hy
    · refine psd_congr (fun x _ y _ => ?_) (h3 S hS hSd)
      simp only [hKr, he', if_neg hi, if_neg hne]
end Formalism.FourierDecayAlt.P.DensitySumsAndDomination
