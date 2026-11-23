-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Ind.finsum_zero_of_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:45.768807+00:00
-- url     : https://prove2.me/submissions/98771fc0-d57d-4ddd-a51b-c1b4e946c569

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice

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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Ind
namespace Formalism.FourierDecayAlt.P.A6x7.Ind
theorem _root_.solution {X : Type} (σ : X ≃ X) (h : X → ℂ) (ω : ℂ) (hω : ω ≠ 1)
    (hs : ∀ x, h (σ x) = ω * h x) : ∑ᶠ x, h x = 0 := by
  have h1 : ∑ᶠ x, h x = ω * ∑ᶠ x, h x := by
    conv_lhs => rw [← finsum_comp_equiv σ]
    rw [mul_finsum]
    exact finsum_congr hs
  have h2 : (1 - ω) * ∑ᶠ x, h x = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h).symm hω
  · exact h
end Formalism.FourierDecayAlt.P.A6x7.Ind
