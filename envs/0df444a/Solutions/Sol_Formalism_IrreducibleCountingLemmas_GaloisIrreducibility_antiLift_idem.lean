-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.antiLift_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:20.801517+00:00
-- url     : https://prove2.me/submissions/7fb1e117-d393-4105-bfbd-2de07b030e32

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_antiLift_of
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_twistedIdem_def


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {G : Type} [Group G] [Fintype G]
open Classical
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσσ : ∀ x, σ (σ x) = x)
    (J : Subgroup G) (χ : J →* ℂˣ) (hJ : ∀ u : J, ∃ h : σ u ∈ J, χ ⟨σ u, h⟩ = χ u) :
    antiLift σ hσ (twistedIdem J χ) = MulOpposite.op (twistedIdem J χ) := by
  let s : J ≃ J :=
    { toFun := fun u => ⟨σ u, (hJ u).1⟩
      invFun := fun u => ⟨σ u, (hJ u).1⟩
      left_inv := fun u => Subtype.ext (hσσ u)
      right_inv := fun u => Subtype.ext (hσσ u) }
  rw [twistedIdem_def, map_sum]
  show _ = MulOpposite.opAddEquiv _
  rw [map_sum]
  refine Fintype.sum_equiv s _ _ (fun u => ?_)
  rw [map_smul, antiLift_of, MulOpposite.opAddEquiv_apply, MulOpposite.op_smul]
  have : χ (s u) = χ u := (hJ u).2
  rw [this]
  rfl
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
