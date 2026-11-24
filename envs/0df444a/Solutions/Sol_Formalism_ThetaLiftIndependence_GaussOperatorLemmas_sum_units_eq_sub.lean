-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.GaussOperatorLemmas.sum_units_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:37:22.497744+00:00
-- url     : https://prove2.me/submissions/bb0561f6-28a6-4a45-bebc-7eb1941fc938

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_GaussOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.GaussOperatorLemmas
variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
namespace Formalism.ThetaLiftIndependence.GaussOperatorLemmas
theorem _root_.solution {M : Type*} [AddCommGroup M] (f : 𝔽 → M) :
    ∑ u : 𝔽ˣ, f u = ∑ x, f x - f 0 := by
  rw [Fintype.sum_eq_add_sum_compl 0 f, add_sub_cancel_left,
    Finset.sum_subtype ({0}ᶜ : Finset 𝔽) (p := fun a => a ≠ 0) (by simp) f]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun u => rfl)
end Formalism.ThetaLiftIndependence.GaussOperatorLemmas
