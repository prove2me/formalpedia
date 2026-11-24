-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_dint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:29:29.652131+00:00
-- url     : https://prove2.me/submissions/f5a4eb50-5ff1-4956-a787-1ceea92a9b89

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_ratCast_mul
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_trace_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution [Module (NumberField.RingOfIntegers K) V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (d : ℕ) (x y : V)
    (hxy : (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K)) :
    ∃ z : ℤ, (d : ℚ) * Algebra.trace ℚ K (h x y) = z := by
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp hxy
  obtain ⟨z, hz⟩ := classSetAssembly_trace_int o
  refine ⟨z, ?_⟩
  rw [← hz, ho, ← classSetAssembly_ratCast_mul, Rat.cast_natCast]
end Formalism.HermitianLatticesTheory
