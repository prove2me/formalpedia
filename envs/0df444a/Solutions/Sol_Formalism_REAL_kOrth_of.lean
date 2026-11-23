-- Prove2me | solution 1 for Formalism.REAL.kOrth_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:53.165362+00:00
-- url     : https://prove2.me/submissions/3caedfc5-000b-48cd-8c90-0f75bd7a851c

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Theorems.Thm_Formalism_REAL_compact_span_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (hl : KLow) (hw : KWtOrth) : KOrth := by
  intro V _ _ n ε F μ ν x y h hU hx hy hne x' hx' y' hy'
  have base : ∀ z ∈ kSpan ε F y, ⟪x, z⟫_ℂ = 0 := by
    rw [(hl V n ε F ν y h hy).1]
    intro z hz
    have : lowSpan ε F y ≤ (ℂ ∙ x)ᗮ := by
      refine Submodule.span_le.mpr ?_
      rintro u ⟨w, hw', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      cases w with
      | nil => exact hw V n ε F μ ν x y hU hx.1 hy.1 hne
      | cons p w =>
        have hp := hw' p List.mem_cons_self
        show ⟪x, F p.1 p.2 (ew F w y)⟫_ℂ = 0
        rw [← hU p.2 p.1 hp.1.symm, hx.2 p.2 p.1 hp.2 hp.1.symm, inner_zero_left]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (this hz)
  rw [(hl V n ε F μ x h hx).1] at hx'
  have : lowSpan ε F x ≤ (kSpan ε F y)ᗮ := by
    refine Submodule.span_le.mpr ?_
    rintro u ⟨w, hw', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal']
    induction w with
    | nil => exact base
    | cons p w ih =>
      intro z hz
      have hp := hw' p List.mem_cons_self
      show ⟪F p.1 p.2 (ew F w x), z⟫_ℂ = 0
      rw [hU p.1 p.2 hp.1]
      exact ih (fun q hq => hw' q (List.mem_cons_of_mem _ hq)) _
        (compact_span_stable y p.2 p.1 hp.1.symm z hz)
  have h2 := this hx'
  rw [Submodule.mem_orthogonal'] at h2
  exact h2 y' hy'
end Formalism.REAL
