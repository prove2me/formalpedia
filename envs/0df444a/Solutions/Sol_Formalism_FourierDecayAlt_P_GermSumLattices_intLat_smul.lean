-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.intLat_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:05.863673+00:00
-- url     : https://prove2.me/submissions/79fdfd58-cb00-46c6-8c08-9322497da9fe

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices

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
variable (R) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (Λ : AddSubgroup K) (Om : Set K) (F G : K → ℂ) (c : ℂ)
    (hF : ∀ z ∈ Om, F z = c * G z) : intLat R Λ Om F = c * intLat R Λ Om G := by
  unfold intLat
  rw [mul_left_comm]
  congr 1
  rw [← smul_eq_mul, smul_finsum]
  apply finsum_congr
  intro y
  split_ifs with hy
  · rw [hF _ hy, smul_eq_mul]
  · simp
end Formalism.FourierDecayAlt.P.GermSumLattices
