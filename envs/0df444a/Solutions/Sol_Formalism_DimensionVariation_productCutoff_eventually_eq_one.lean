-- Prove2me | solution 1 for Formalism.DimensionVariation.productCutoff_eventually_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:05.329253+00:00
-- url     : https://prove2.me/submissions/27146304-1d01-4f5d-80c5-fc8f0c00c1b2

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
theorem _root_.solution {κ : Type} [Fintype κ] (u : κ → ℂ) :
    ∀ᶠ N : ℕ in atTop, fjChiP N u = 1 := by
  obtain ⟨M, hM⟩ := exists_nat_ge (∑ x, ‖u x‖)
  filter_upwards [Filter.eventually_ge_atTop M] with N hN
  unfold fjChiP
  refine Finset.prod_eq_one fun x _ => ?_
  have hx : ‖u x‖ ≤ (N : ℝ) := by
    calc ‖u x‖ ≤ ∑ y, ‖u y‖ :=
          Finset.single_le_sum (fun y _ => norm_nonneg (u y)) (Finset.mem_univ x)
      _ ≤ M := hM
      _ ≤ N := by exact_mod_cast hN
  simp [fjChi, hx]
end Formalism.DimensionVariation
