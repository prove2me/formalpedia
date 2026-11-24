-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.cv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:47:52.81414+00:00
-- url     : https://prove2.me/submissions/5cfd19fd-d4d7-4e31-8782-53b362388c7f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (t₁ t₂ : CT k r nf)
    (g : Mat k r) : cv D fib (mulCT t₁ t₂) g = cv D fib t₁ g * cv D fib t₂ g := by
  simp only [cv, cvs, mulCT, C6.monoM, C6.Epart, List.map_append, List.prod_append, map_mul, Pi.add_apply,
    pow_add, Finset.prod_mul_distrib]
  rw [smul_mul_smul_comm]
  congr 1
  ring
end Formalism.FourierDecayAlt.P.MinorPolynomials
