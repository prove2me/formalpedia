-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.commute_Avr_Bvr_of_commute_siteOps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:02.953952+00:00
-- url     : https://prove2.me/submissions/43256da5-a598-4cfe-a2a9-fba831e4e1e6

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution (σ : Site A) (Y : K) (z : A) (hp : Commute z σ.p) (hc : Commute z σ.c)
    (hci : Commute z σ.ci) (i j : Fin 2) : Commute z (Ts σ Y i j) := by
  fin_cases i <;> fin_cases j <;> simp [Ts, Tm]
  · exact Commute.add_right (Algebra.commute_algebraMap_right Y z) hp
  · exact hc
  · exact hci
end Formalism.FourierDecayAlt.P.Wd6
