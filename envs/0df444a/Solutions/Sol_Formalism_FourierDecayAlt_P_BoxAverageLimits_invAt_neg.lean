-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.invAt_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:35.253432+00:00
-- url     : https://prove2.me/submissions/092afa41-84c5-434f-94ac-54aff6198366

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
theorem _root_.solution (e : ι → Λ) (c : ℕ → Λ) (a : Λ) (ha : InvAt e c a) : InvAt e c (-a) := by
  intro g hg
  calc LIMf e c (fun x => g (x + -a))
      = LIMf e c (fun x => (fun y => g (y + -a)) (x + a)) := (ha _ (bdd_shift hg (-a))).symm
    _ = LIMf e c g := by
        have hfun : (fun x => (fun y => g (y + -a)) (x + a)) = g := by
          funext x; show g (x + a + -a) = g x; rw [add_neg_cancel_right]
        rw [hfun]
end Formalism.FourierDecayAlt.P.BoxAverageLimits
