-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locDual_sigma_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:52.542551+00:00
-- url     : https://prove2.me/submissions/b2d756fc-d55f-4039-a72e-56c8fead0f41

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) (p : Ideal R)
    (s : R) (hs : s ∈ hcompl (K := K) p) :
    locBasic_sigma hinj hstar s ∈ hcompl (K := K) p := by
  have spec : ∀ r : R, algebraMap R K (locBasic_sigma hinj hstar r) = star (algebraMap R K r) :=
    fun r => (hstar r).choose_spec
  unfold hcompl at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem s hs =>
    apply Submonoid.subset_closure
    obtain ⟨hs1, hs2⟩ := hs
    refine ⟨hs2 _ (spec s), fun t ht => ?_⟩
    rw [spec, star_star] at ht
    rw [hinj ht]
    exact hs1
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Submonoid.mul_mem _ ha hb
end Formalism.HermitianLatticesTheory
