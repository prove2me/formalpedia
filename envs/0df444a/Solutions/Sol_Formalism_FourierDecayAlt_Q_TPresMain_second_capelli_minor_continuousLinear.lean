-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.second_capelli_minor_continuousLinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:45:37.279315+00:00
-- url     : https://prove2.me/submissions/8fb21c3c-1898-4537-93e7-c9ebc8c24bec

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_qminor_clm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution (hD : IsOpen D) (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ)
    (L : E →L[ℂ] E') (f : Mx k r → E) (hf : SmoothLev k r i D f) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chat2L (EH k r) (posL k r i) u a a' β β' (fun y => L (f y)) g =
      L (chat2L (EH k r) (posL k r i) u a a' β β' f g) := by
  simp only [chat2L, map_sum]
  refine Finset.sum_congr rfl fun i0 _ => Finset.sum_congr rfl fun i1 _ =>
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 _ => ?_
  split_ifs
  · rw [map_smul]
    congr 1
    exact qminor_clm hD _ _ u L f hf g hg
  · exact (map_zero L).symm
end Formalism.FourierDecayAlt.Q.TPresMain
