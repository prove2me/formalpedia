-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_exp_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:45.274827+00:00
-- url     : https://prove2.me/submissions/1242025f-4dd8-419e-ac29-ac3c75eb5914

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℂ) (h3 : Y * Y * Y = 0) (s t : ℂ) :
    1 + (s + t) • Y + ((s + t) ^ 2 / 2) • (Y * Y) =
      (1 + s • Y + (s ^ 2 / 2) • (Y * Y)) * (1 + t • Y + (t ^ 2 / 2) • (Y * Y)) := by
  have h3' : Y * (Y * Y) = 0 := by rw [← Matrix.mul_assoc]; exact h3
  have h4 : Y * Y * (Y * Y) = 0 := by rw [← Matrix.mul_assoc, h3, Matrix.zero_mul]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h3, h3', h4, smul_zero, add_zero]
  module
end Formalism.HermitianLatticeCounting.P
