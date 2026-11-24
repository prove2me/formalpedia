-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.neighbourConstruct_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:59.899811+00:00
-- url     : https://prove2.me/submissions/caf4ca42-e270-4d51-9103-7e187e18adb6

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_NeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourConstruct
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourConstruct_mem_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open nonZeroDivisors
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (P : Ideal R) (hP0 : P ≠ ⊥) :
    (1 : K) ∈ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P := by
  have e := FractionalIdeal.coe_ideal_mul_inv (K := K) P hP0
  have e2 : ((P : FractionalIdeal R⁰ K) : Submodule R K) *
      (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) = 1 := by
    rw [← FractionalIdeal.coe_mul, e, FractionalIdeal.coe_one]
  have h1 : (1 : K) ∈ ((P : FractionalIdeal R⁰ K) : Submodule R K) *
      (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) := by
    rw [e2]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hne : (P : FractionalIdeal R⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hP0
  refine (mul_le_mul' ?_ ?_ : _ ≤ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P) h1
  · rw [FractionalIdeal.coe_coeIdeal]; exact le_rfl
  · intro a ha
    rw [neighbourConstruct_mem_inv]
    intro p hp
    have := (FractionalIdeal.mem_inv_iff hne).mp ha (algebraMap R K p)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hp)
    rw [mul_comm]
    exact (FractionalIdeal.mem_one_iff _).mp this
end Formalism.HermitianLatticesTheory
