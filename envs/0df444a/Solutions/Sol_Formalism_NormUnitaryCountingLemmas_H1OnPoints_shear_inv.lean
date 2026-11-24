-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.H1OnPoints.shear_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:34:08.01964+00:00
-- url     : https://prove2.me/submissions/e26e2a13-baa8-4c0a-9590-6343d44df96f

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NatDegreeAevalLe
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_H1OnPoints_shear_eval
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_H1OnPoints_shear_eq

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
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.H1OnPoints
variable {R : Type*} [CommRing R]
namespace Formalism.NormUnitaryCountingLemmas.H1OnPoints
theorem _root_.solution {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin N → ℕ}
    {F : MvPolynomial (Fin N × Fin n) R} (hF : F ∈ H R ν) (i j : Fin N) (hij : i < j)
    (y : Fin N × Fin n → S) (s : S) :
    aeval (fun p => y p + if p.1 = j then s * y (i, p.2) else 0) F = aeval y F := by
  rw [← shear_eval, shear_eq hF i j hij, Polynomial.eval₂_C]
  rfl
end Formalism.NormUnitaryCountingLemmas.H1OnPoints
