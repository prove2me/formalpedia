-- Prove2me | solution 1 for Formalism.H.PoissonPeriodization.summable_one_add_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:07.56501+00:00
-- url     : https://prove2.me/submissions/884f4a80-6251-419b-a58e-457b6085070f

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Periodization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex Metric
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
open Formalism.H.PoissonPeriodization
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
namespace Formalism.H.PoissonPeriodization
theorem _root_.solution (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {b : ℝ} (hb : (Module.finrank ℝ V : ℝ) < b) :
    Summable (fun l : Λ => (1 + ‖(l : V)‖) ^ (-b)) := by
  classical
  have hb0 : 0 < b := lt_of_le_of_lt (Nat.cast_nonneg _) hb
  have hr : -b < -(Module.finrank ℤ Λ : ℝ) := by
    rw [ZLattice.rank ℝ Λ]
    linarith
  have hs := ZLattice.summable_norm_rpow Λ (-b) hr
  refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_)
    (hs.add (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable)
  by_cases h : l = 0
  · subst h
    simp only [if_pos rfl, ZeroMemClass.coe_zero, norm_zero, add_zero, Real.one_rpow, if_true, ↓reduceIte]
    linarith [Real.rpow_nonneg (le_refl (0 : ℝ)) (-b)]
  · have hl : 0 < ‖(l : V)‖ := norm_pos_iff.mpr (by simpa using h)
    rw [if_neg h, add_zero]
    show (1 + ‖(l : V)‖) ^ (-b) ≤ ‖(l : V)‖ ^ (-b)
    rw [Real.rpow_neg (by positivity), Real.rpow_neg hl.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hl b) (Real.rpow_le_rpow hl.le (by linarith) hb0.le)
end Formalism.H.PoissonPeriodization
