-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg.eval_prodP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:00:04.834034+00:00
-- url     : https://prove2.me/submissions/6dd33fd7-dc46-4853-b4a4-73cd3dcd287d

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
theorem _root_.solution {m : ℕ} (lin : Fin m → Prop) [DecidablePred lin] (B : Fin m → A) (Y : ℂ) :
    eval₂ (RingHom.id A) (algebraMap ℂ A Y) (prodP lin B) =
      (List.ofFn fun l => (if lin l then algebraMap ℂ A Y else 0) + B l).prod := by
  unfold prodP
  rw [eval₂_list_prod_noncomm]
  · rw [List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun l => ?_))
    simp only [Function.comp, fac, eval₂_add, eval₂_C, RingHom.id_apply]
    split_ifs <;> simp
  · intro p _ k
    exact (Algebra.commutes Y _).symm
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg
