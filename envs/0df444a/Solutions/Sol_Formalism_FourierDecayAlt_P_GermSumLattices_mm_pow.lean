-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.mm_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:50.661416+00:00
-- url     : https://prove2.me/submissions/a536c300-ea44-42e6-909a-9fb7bb007046

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_mm_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] (R : Subring K)
variable {R}
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (h : MM R) (z : Kˣ) (n : ℕ) : modK R ((z : K) ^ n) = modK R (z : K) ^ n := by
  induction n with
  | zero => simpa using mm_one h
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih, ← Units.val_pow_eq_pow_val]
    exact (h (z ^ n) z).2
end Formalism.FourierDecayAlt.P.GermSumLattices
