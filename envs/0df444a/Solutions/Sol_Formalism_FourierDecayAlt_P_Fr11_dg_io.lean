-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.dg_io
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:34:12.999182+00:00
-- url     : https://prove2.me/submissions/f391023a-5cab-4023-bdf4-16999fc17639

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr11
theorem _root_.solution (g : Ix S → ℂ) (x : A) : (dg g * io x : SlopeTestRemainingChoices S A) = io x * dg g := by
  apply Matrix.ext
  intro x y
  simp only [dg, io, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs <;> simp [Algebra.commutes]
end Formalism.FourierDecayAlt.P.Fr11
