-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.derivative_of_psi_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:13.743995+00:00
-- url     : https://prove2.me/submissions/453150b3-fbea-474a-b1fe-a3bc41905f0b

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_nilpotent_model_computation_holds

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
theorem _root_.solution : CharacterDerivativeNorm := by
  intro k r z hz a e v ka l he hv hl t
  obtain ⟨_, _, h3⟩ := nilpotent_model_computation_holds k r z hz a e v he hv
  have h4 := (h3 t).2
  unfold Formalism.QuantumDeterminants.psi
  rw [h4, hl]
  have h5 : (ka : ℂ) * Formalism.QuantumDeterminants.cStd * ((t : ℂ) * (-Complex.I * (l : ℂ))) = ((-(2 * ka * l * t) : ℝ) : ℂ) := by
    unfold Formalism.QuantumDeterminants.cStd
    push_cast
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (2 * (ka : ℂ) * t * l) * this
  rw [h5, Complex.ofReal_re]
  congr 1
  push_cast
  ring
end Formalism.HermitianLatticeCounting.P
