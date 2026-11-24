-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.herm_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:00:57.637435+00:00
-- url     : https://prove2.me/submissions/896e4cac-8a28-4fc0-a999-db6120ec5ce4

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections
variable {n : Type*} [Fintype n]
namespace Formalism.FourierDecayAlt.P.HermitianProjections
theorem _root_.solution (H : Matrix n n ℂ) (c : ℂ) (v a : n → ℂ) : herm H v (c • a) = conj c * herm H v a := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]
  rfl
end Formalism.FourierDecayAlt.P.HermitianProjections
