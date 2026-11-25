-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg.natDegree_prodP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:12:03.813158+00:00
-- url     : https://prove2.me/submissions/750499fe-4837-4f59-b454-c35b6d163889

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.GroupTheory.Perm.Support
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_TopAlg_natDegree_fac

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
theorem _root_.solution : ∀ {m : ℕ} (lin : Fin m → Prop) [DecidablePred lin] (B : Fin m → A),
    (prodP lin B).natDegree ≤ ∑ l, (if lin l then 1 else 0)
  | 0, lin, _, B => by simp [prodP]
  | m + 1, lin, _, B => by
    unfold prodP
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    refine (natDegree_mul_le).trans (add_le_add (natDegree_fac _ _) ?_)
    exact solution (fun l => lin l.succ) (fun l => B l.succ)
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg
