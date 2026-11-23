-- Prove2me | solution 1 for Formalism.DimensionVariation.fjMono_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:59.039532+00:00
-- url     : https://prove2.me/submissions/8a2ba985-8633-4661-8235-6f6598ed8462

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution {κ : Type} [Fintype κ] (N : ℕ) (a : κ → ℕ) (u : κ → ℂ) :
    ‖fjChiP N u * mono u a‖ ≤ ‖mono (fun _ : κ => (N : ℂ)) a‖ := by
  simp only [fjChiP, mono, ← Finset.prod_mul_distrib, norm_prod]
  refine Finset.prod_le_prod (fun x _ => norm_nonneg _) fun x _ => ?_
  rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
  unfold fjChi
  split_ifs with h
  · rw [norm_one, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) h _
  · rw [norm_zero, zero_mul]
    positivity
end Formalism.DimensionVariation
