-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.DefiniteClassRepresentatives.pick_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:07:39.934493+00:00
-- url     : https://prove2.me/submissions/43644b79-dc2e-4b04-8637-af6f656242ef

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.DefiniteClassRepresentatives
open Formalism.HermitianLatticesTheory LatticeLiftIndependence
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
namespace Formalism.ThetaLiftIndependence.DefiniteClassRepresentatives
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K)
    (s₀ : Finset (Submodule (NumberField.RingOfIntegers K) V))
    {M : Submodule (NumberField.RingOfIntegers K) V} (hM : M ∈ s₀) :
    pick h s₀ (Quotient.mk (isoSetoid h) M) ∈ s₀ ∧
      Quotient.mk (isoSetoid h) (pick h s₀ (Quotient.mk (isoSetoid h) M)) =
        Quotient.mk (isoSetoid h) M := by
  have hq : ∃ N ∈ s₀, Quotient.mk (isoSetoid h) N = Quotient.mk (isoSetoid h) M := ⟨M, hM, rfl⟩
  have e : pick h s₀ (Quotient.mk (isoSetoid h) M) = Classical.choose hq := by
    unfold pick
    exact dif_pos hq
  rw [e]
  exact Classical.choose_spec hq
end Formalism.ThetaLiftIndependence.DefiniteClassRepresentatives
