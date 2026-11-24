-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusBasic_common
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:45.593865+00:00
-- url     : https://prove2.me/submissions/f2662a5b-5cf1-48b5-86ec-f73fa3282740

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_mem_one_mul

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
theorem _root_.solution (S : Submonoid R) (s : Finset V) (f : V → K)
    (hf : ∀ v ∈ s, ∃ u ∈ S, algebraMap R K u * f v ∈ (1 : Submodule R K)) :
    ∃ u ∈ S, ∀ v ∈ s, algebraMap R K u * f v ∈ (1 : Submodule R K) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, S.one_mem, fun v hv => by simp at hv⟩
  | @insert a s ha ih =>
    obtain ⟨u, hu, hus⟩ := ih (fun v hv => hf v (Finset.mem_insert_of_mem hv))
    obtain ⟨w, hw, hwa⟩ := hf a (Finset.mem_insert_self a s)
    refine ⟨u * w, S.mul_mem hu hw, fun v hv => ?_⟩
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [map_mul, mul_assoc]
      exact genusBasic_mem_one_mul _ hwa u
    · rw [map_mul, mul_comm (algebraMap R K u), mul_assoc]
      exact genusBasic_mem_one_mul _ (hus v hv) w
end Formalism.HermitianLatticesTheory
