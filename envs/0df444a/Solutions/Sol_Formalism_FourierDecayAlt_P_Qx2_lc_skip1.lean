-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.lc_skip1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:46:34.050226+00:00
-- url     : https://prove2.me/submissions/8bdb0081-2e21-4e21-a470-2d3bbef1900a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_lc_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_lc_miss
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_skip_one_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_skip_one_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_exists_skip_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution (a b : Fin (mdim k r i)) : lc k r i (skip1 a) (skip1 b) = if a = b then 1 else 0 := by
  split_ifs with h
  · subst h
    exact lc_self _ (skip_one_injective a)
  · obtain ⟨l₀, hl₀⟩ := exists_skip_one_eq h
    exact lc_miss _ _ l₀ fun l e => skip_one_ne a l (e.trans hl₀)
end Formalism.FourierDecayAlt.P.Qx2
