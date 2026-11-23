-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.lamPSq_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:05.384806+00:00
-- url     : https://prove2.me/submissions/d0a90df7-a5f2-45ca-954c-44107c0b26f1

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremsAssembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
theorem _root_.solution {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (Rw ZZ : ℝ) (a : Fin K) :
    cg grid a ^ 2 * Rw * ZZ ≤ lamPSq grid Rw ZZ := by
  unfold lamPSq
  rw [Finset.le_fold_max]
  exact Or.inr ⟨a, Finset.mem_univ _, le_rfl⟩
end Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
