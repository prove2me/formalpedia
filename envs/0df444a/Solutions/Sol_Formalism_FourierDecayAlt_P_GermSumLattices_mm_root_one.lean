-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.mm_root_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:45.828796+00:00
-- url     : https://prove2.me/submissions/fa72ee24-6e4e-4557-b758-eac87185f0a9

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_mm_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_mm_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_mm_root

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
theorem _root_.solution (h : MM R) (z : Kˣ) (n : ℕ) (hz : z ^ (n + 1) = 1) : modK R (z : K) = 1 := by
  apply mm_root h z n
  rw [← mm_pow h, ← Units.val_pow_eq_pow_val, hz, Units.val_one, mm_one h]
end Formalism.FourierDecayAlt.P.GermSumLattices
