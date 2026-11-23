-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.germSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:30.430526+00:00
-- url     : https://prove2.me/submissions/05c30ce0-b2ea-487e-aca0-9891785d1298

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_finsum_if

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
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite) (t c : Kˣ)
    (f : Kˣ → ℂ) : germSum R ψ m γ t c f =
      ((modK R (t : K) ^ (-((m : ℝ) ^ 2) / 2) : ℝ) : ℂ) *
        ∑ z ∈ (hroots ((-t) ^ m * c)).toFinset, germCoef R ψ m γ t z * f z := by
  unfold germSum
  congr 1
  exact finsum_if (hroots ((-t) ^ m * c)) _
end Formalism.FourierDecayAlt.P.GermSumLattices
