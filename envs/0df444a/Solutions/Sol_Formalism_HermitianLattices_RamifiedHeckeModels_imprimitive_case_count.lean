-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedHeckeModels.imprimitive_case_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:31.281179+00:00
-- url     : https://prove2.me/submissions/ab28bf57-948f-4ee8-b178-be5c2aa9bf11

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LengthQuotientLeOfLatticeSandwich
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedHeckeModels
open Formalism.HermitianLattices.LocalLatticeBases Finset ComplexConjugate
namespace Formalism.HermitianLattices.RamifiedHeckeModels
theorem _root_.solution : ImprimitiveOrbitCondition := by
  intro q _ n f e xz he hl ⟨z, hz, hz1⟩
  refine ⟨fun hall => ?_, fun j => ?_⟩
  ·
    choose a ha using hall
    have hz' : (z : ℚ) = ((q * ∑ j, a j * e j : ℤ) : ℚ) := by
      rw [← hz]
      push_cast
      simp [ha]
    have hz'' : z = q * ∑ j, a j * e j := by exact_mod_cast hz'
    rw [hz''] at hz1
    push_cast at hz1
    simp at hz1
  · have h := hl (Pi.single j (q : ℤ)) ?_
    · have hs : (∑ i, xz i * ((Pi.single j (q : ℤ) : Fin n → ℤ) i : ℚ)) = (q : ℚ) * xz j := by
        rw [Finset.sum_eq_single j]
        · simp [mul_comm]
        · intro b _ hb
          simp [Pi.single_apply, hb]
        · simp
      rwa [hs] at h
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
end Formalism.HermitianLattices.RamifiedHeckeModels
