-- Prove2me | solution 1 for Formalism.ZF.rectangle_double_pole
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:12:16.136867+00:00
-- url     : https://prove2.me/submissions/20400c6c-1e7f-425b-b069-57978c8d06be

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectDoublePole
import Theorems.Thm_Formalism_ZF_rdp_rectInt_eq_fx
import Theorems.Thm_Formalism_ZF_rdp_rectInt_add
import Theorems.Thm_Formalism_ZF_rdp_rectInt_double
import Theorems.Thm_Formalism_ZF_rdp_seg
import Theorems.Thm_Formalism_FX_rectangle_residue


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : RectDoublePole := by
  intro g G a b p x0 x1 y0 y1 h1 h2 h3 h4 hU hg
  obtain ⟨U, hUo, hRU, hGU⟩ := hU
  have hGc : ContinuousOn G U := hGU.continuousOn
  have hx01 : x0 ≤ x1 := by linarith
  have hy01 : y0 ≤ y1 := by linarith

  have hmem : ∀ x y : ℝ, x ∈ Set.uIcc x0 x1 → y ∈ Set.uIcc y0 y1 → (x : ℂ) + y * I ∈ U := by
    intro x y hx hy
    apply hRU
    rw [Complex.mem_reProdIm]
    simp [hx, hy]
  have hseg : ∀ (γ : ℝ → ℂ) (s t : ℝ), Continuous γ → (∀ u ∈ Set.uIcc s t, γ u ∈ U) →
      (∀ u ∈ Set.uIcc s t, γ u ≠ p) →
      IntervalIntegrable (fun u => g (γ u) - a / (γ u - p) ^ 2) MeasureTheory.volume s t ∧
      IntervalIntegrable (fun u => a / (γ u - p) ^ 2) MeasureTheory.volume s t := by
    intro γ s t hγ hγU hγp
    exact rdp_seg g G a b p γ s t hγ (hGc.comp hγ.continuousOn fun u hu => hγU u hu) hγp hg
  have hxl : x0 ∈ Set.uIcc x0 x1 := Set.left_mem_uIcc
  have hxr : x1 ∈ Set.uIcc x0 x1 := Set.right_mem_uIcc
  have hyl : y0 ∈ Set.uIcc y0 y1 := Set.left_mem_uIcc
  have hyr : y1 ∈ Set.uIcc y0 y1 := Set.right_mem_uIcc
  have hB := hseg (fun x : ℝ => (x : ℂ) + y0 * I) x0 x1 (by fun_prop)
    (fun u hu => hmem u y0 hu hyl)
    (fun u _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have hT := hseg (fun x : ℝ => (x : ℂ) + y1 * I) x0 x1 (by fun_prop)
    (fun u hu => hmem u y1 hu hyr)
    (fun u _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have hR := hseg (fun y : ℝ => (x1 : ℂ) + y * I) y0 y1 (by fun_prop)
    (fun u hu => hmem x1 u hxr hu)
    (fun u _ h => by have := congrArg Complex.re h; simp at this; linarith)
  have hL := hseg (fun y : ℝ => (x0 : ℂ) + y * I) y0 y1 (by fun_prop)
    (fun u hu => hmem x0 u hxl hu)
    (fun u _ h => by have := congrArg Complex.re h; simp at this; linarith)
  have hsplit : g = fun w => (g w - a / (w - p) ^ 2) + a / (w - p) ^ 2 := by
    funext w; ring
  rw [hsplit, rdp_rectInt_add _ _ x0 x1 y0 y1 hB.1 hB.2 hT.1 hT.2 hR.1 hR.2 hL.1 hL.2,
    rdp_rectInt_double a p x0 x1 y0 y1 h1 h2 h3 h4, add_zero, rdp_rectInt_eq_fx]
  have hres := Formalism.FX.rectangle_residue (fun w => g w - a / (w - p) ^ 2) G {p} (fun _ => b)
    x0 x1 y0 y1 (by linarith) (by linarith) (by simp [h1, h2, h3, h4]) ⟨U, hUo, hRU, hGU⟩
    (by
      intro w hw
      have hwp : w ≠ p := by simpa using hw
      simp only [Finset.sum_singleton]
      rw [hg w hwp]
      ring)
  simpa using hres
end Formalism.ZF
