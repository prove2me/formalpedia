-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_hzz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:28.687314+00:00
-- url     : https://prove2.me/submissions/c6b37086-18d8-4f03-890f-ad16482999f0

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_Hh
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_swap


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
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have h := ggHerm_swap (Hpk k r) (s1c2_Hh k r) z z
  have him : (herm (Hpk k r) z z).im = 0 := by
    have h2 := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at h2
    linarith
  apply Complex.ext
  · simp [Tz]
  · simp [him]
end Formalism.HermitianLatticeCounting.P
