-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_trace_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:19.116601+00:00
-- url     : https://prove2.me/submissions/49d159ca-a93e-44bf-9f62-d961a0531130

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly

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
theorem _root_.solution (o : NumberField.RingOfIntegers K) :
    ∃ z : ℤ, Algebra.trace ℚ K (algebraMap (NumberField.RingOfIntegers K) K o) = z := by
  have hint_r : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K o) := by
    exact (NumberField.RingOfIntegers.isIntegral o).algebraMap
  have ht : IsIntegral ℤ (Algebra.trace ℚ K (algebraMap (NumberField.RingOfIntegers K) K o)) :=
    Algebra.isIntegral_trace hint_r
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp ht
  exact ⟨z, hz.symm.trans (eq_intCast (algebraMap ℤ ℚ) z)⟩
end Formalism.HermitianLatticesTheory
