-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:22:47.582055+00:00
-- url     : https://prove2.me/submissions/da11d9ec-fd5d-4f65-b5ad-5198496e4b1c

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
variable {N : ℕ}
namespace Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
theorem _root_.solution {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g - Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p - q, (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_sub]
end Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
