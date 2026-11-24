-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ShearCoefficients.coeffHom_shear_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:11:22.181785+00:00
-- url     : https://prove2.me/submissions/fe260bf0-cbb1-4829-b0d3-39708247bb6f

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_CoeffHom_add
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_CoeffHom_zero
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_CoeffHom_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.ShearCoefficients
variable {R : Type*} [CommRing R]
namespace Formalism.NormUnitaryCountingLemmas.ShearCoefficients
theorem _root_.solution {N n : ℕ} (i j : Fin N) (p : Fin N × Fin n) :
    CoeffHom (R := R) (coordWt N n) (coordWt N n p)
      (Polynomial.C (X p) +
        (if p.1 = j then Polynomial.X * Polynomial.C (X (i, p.2)) else 0)) := by
  refine CoeffHom.add (CoeffHom.C (isWeightedHomogeneous_X R _ p)) ?_
  split_ifs
  · have h := (CoeffHom.X (R := R) (wt := coordWt N n)).mul
      (CoeffHom.C (isWeightedHomogeneous_X R (coordWt N n) (i, p.2)))
    rw [zero_add] at h
    exact h
  · exact CoeffHom.zero _
end Formalism.NormUnitaryCountingLemmas.ShearCoefficients
