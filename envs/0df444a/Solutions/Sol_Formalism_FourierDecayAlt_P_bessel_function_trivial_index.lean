-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.bessel_function_trivial_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:34:28.384809+00:00
-- url     : https://prove2.me/submissions/b7646afa-dd94-4dc7-b1c1-a8c16889a518

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.JtauOne := by
  unfold Formalism.FourierDecayAlt.B.JtauOne
  intro k r Wp Wq _ _ _ _ D F g
  unfold Jtau JF xiTau besselJ RealPlaceData.μSS
  unfold rho sgs
  congr 1
  funext p
  congr 1
  unfold psi cStd
  have hs : ∀ z : ℂ, star (Complex.exp z) = Complex.exp ((starRingEnd ℂ) z) :=
    fun z => (Complex.exp_conj z).symm
  rw [hs, ← Complex.exp_add]
  congr 1
  try unfold lam
  dsimp only
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, one_mul]
  try unfold cStd
  ring_nf
  push_cast
  ring
end Formalism.FourierDecayAlt.P
