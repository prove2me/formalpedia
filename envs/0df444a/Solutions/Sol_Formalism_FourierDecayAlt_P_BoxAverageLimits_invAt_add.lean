-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.invAt_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:34.93018+00:00
-- url     : https://prove2.me/submissions/365d9f30-884a-44c5-9c67-e0d70c05e83e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_bdd_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution (e : ι → Λ) (c : ℕ → Λ) (a b : Λ) (ha : InvAt e c a) (hb : InvAt e c b) :
    InvAt e c (a + b) := by
  intro g hg
  have hfun : (fun x => g (x + (a + b))) = (fun x => (fun y => g (y + a)) (x + b)) := by
    funext x
    show g (x + (a + b)) = g (x + b + a)
    rw [add_comm a b, add_assoc]
  rw [hfun, hb _ (bdd_shift hg a), ha g hg]
end Formalism.FourierDecayAlt.P.BoxAverageLimits
