-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.mass_ratio_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:08:06.406812+00:00
-- url     : https://prove2.me/submissions/8ce0f159-07e3-499c-8256-068e8061acad

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : MassRatioArith := by
  intro M f v d hv hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have h1 : d ^ ((M : ℝ) - 1 / 2) = d ^ M * d ^ (-(1 / 2) : ℝ) := by
    rw [sub_eq_add_neg, Real.rpow_add hd0, Real.rpow_natCast]
  rw [h1, ← mul_assoc]; congr 1
  rw [hd]
  have hpi := Real.pi_pos
  simp only [div_pow, mul_pow, ← pow_mul]
  rw [mul_comm f M]
  field_simp
end Formalism.HermitianLatticeCounting.P
