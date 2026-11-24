-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.neighbourConstruct_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:10.981213+00:00
-- url     : https://prove2.me/submissions/93403996-b747-4421-91fb-bad05a2f195f

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_NeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourConstruct
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourConstruct_one_mem

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
theorem _root_.solution (P : Ideal R) (hP0 : P ≠ ⊥) (L : Submodule R V) (x : V)
    (H : ∀ a ∈ invIdeal (K := K) P, a • x ∈ L) : x ∈ P • L := by
  have h1 := neighbourConstruct_one_mem (K := K) P hP0
  have : ((1 : K) • x) ∈ P • L := by
    refine Submodule.mul_induction_on (C := fun k => k • x ∈ P • L) h1 ?_ ?_
    · intro m hm n hn
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hm
      rw [Algebra.linearMap_apply, mul_smul, algebraMap_smul]
      exact Submodule.smul_mem_smul hp (H n hn)
    · intro a b ha hb
      rw [add_smul]; exact Submodule.add_mem _ ha hb
  simpa using this
end Formalism.HermitianLatticesTheory
