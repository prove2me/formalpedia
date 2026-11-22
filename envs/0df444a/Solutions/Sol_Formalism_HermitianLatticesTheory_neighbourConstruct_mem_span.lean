-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.neighbourConstruct_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:21.602838+00:00
-- url     : https://prove2.me/submissions/dd8622c6-a18d-4da3-b322-4bee2e2e3ba1

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_NeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourConstruct

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
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {P : Ideal R} {x z : V} :
    z ∈ Submodule.span R {z | ∃ a ∈ invIdeal (K := K) P, z = a • x} ↔
      ∃ a ∈ invIdeal (K := K) P, z = a • x := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add y y' _ _ h1 h2 =>
      obtain ⟨a, ha, rfl⟩ := h1
      obtain ⟨b, hb, rfl⟩ := h2
      exact ⟨a + b, Submodule.add_mem _ ha hb, by rw [add_smul]⟩
    | smul r y _ h1 =>
      obtain ⟨a, ha, rfl⟩ := h1
      refine ⟨r • a, Submodule.smul_mem _ r ha, ?_⟩
      rw [smul_assoc]
  · intro hz
    exact Submodule.subset_span hz
end Formalism.HermitianLatticesTheory
