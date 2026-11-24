-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.TraceQuadraticBound.denseRange_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:02:18.785742+00:00
-- url     : https://prove2.me/submissions/48e5f2d8-b95e-4d6f-9d7e-df898cbb9e7f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.TraceQuadraticBound
variable {n : Type} [Fintype n] [DecidableEq n]
variable {K : Type} [Field K]
namespace Formalism.L2.Geo.Rec.TraceQuadraticBound
theorem _root_.solution (σ : K →+* ℂ) (z : K) (hz : (σ z).im ≠ 0) : DenseRange σ := by
  let g : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * σ z
  have hg : Continuous g := by fun_prop
  have hgs : Function.Surjective g := by
    intro w
    refine ⟨(w.re - w.im / (σ z).im * (σ z).re, w.im / (σ z).im), ?_⟩
    apply Complex.ext
    · simp [g]
    · simp [g]; field_simp
  have hq : DenseRange (Prod.map (fun q : ℚ => (q : ℝ)) (fun q : ℚ => (q : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have h := hgs.denseRange.comp hq hg
  refine h.mono ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact ⟨(a : K) + (b : K) * z, by simp [g]⟩
end Formalism.L2.Geo.Rec.TraceQuadraticBound
