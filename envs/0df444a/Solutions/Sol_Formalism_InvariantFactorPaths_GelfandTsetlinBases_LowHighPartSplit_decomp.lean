-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:54:52.824938+00:00
-- url     : https://prove2.me/submissions/2c78141e-a83b-44e0-aa9b-7667670debff

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_low_add_high

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
theorem _root_.solution {k : Type*} [CommRing k] (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    G = ∑ β ∈ G.support.image (highP i), Gc i G β * monomial β 1 := by
  symm
  simp only [Gc, Finset.sum_mul, monomial_mul, mul_one]
  have h1 : ∀ β ∈ G.support.image (highP i),
      ∑ e ∈ G.support.filter (fun e => highP i e = β), monomial (lowP i e + β) (coeff e G) =
      ∑ e ∈ G.support.filter (fun e => highP i e = β), monomial e (coeff e G) :=
    fun β _ => Finset.sum_congr rfl fun e he => by rw [← (Finset.mem_filter.mp he).2, low_add_high]
  rw [Finset.sum_congr rfl h1, Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx)]
  exact G.as_sum.symm
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
