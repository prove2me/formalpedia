-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresMain.exp_second_hermitian_mem_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:38:56.671258+00:00
-- url     : https://prove2.me/submissions/d78a46cb-8dc1-49b0-a76a-1ba173aa90a3

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresLie_exp_hpart2_mem


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
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution (p q : Fin (mdim k r i)) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • hpart2 (Hpk k r) (Matrix.single (posL k r i p) (posL k r i q) 1))
      ∈ Glev k r i := by
  exact Formalism.FourierDecayAlt.Q.TPresLie.exp_hpart2_mem i p q t
end Formalism.FourierDecayAlt.Q.TPresMain
