-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg.natDegree_fac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:00:09.470917+00:00
-- url     : https://prove2.me/submissions/85fbce46-4fb2-40ca-8170-b27d4cc9358f

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.GroupTheory.Perm.Support
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
open Formalism.REAL
open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg
theorem _root_.solution (lin : Prop) [Decidable lin] (B : A) :
    (fac lin B).natDegree ≤ if lin then 1 else 0 := by
  unfold fac
  split_ifs
  · exact (natDegree_add_le _ _).trans (by simp [natDegree_X_le])
  · simp
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg
