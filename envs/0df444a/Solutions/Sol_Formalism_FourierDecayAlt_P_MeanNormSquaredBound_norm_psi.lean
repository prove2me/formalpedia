-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MeanNormSquaredBound.norm_psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:41.775131+00:00
-- url     : https://prove2.me/submissions/8d4a839c-6eee-425b-bc98-8d3a447231dd

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanNormSquaredBound

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.MeanNormSquaredBound
namespace Formalism.FourierDecayAlt.P.MeanNormSquaredBound
theorem _root_.solution {K : Type} [CommRing K] (ψ : AddChar K ℂ) (hu : ∀ x : K, conj (ψ x) = ψ (-x))
    (x : K) : ‖ψ x‖ = 1 := by
  have h1 : ψ x * conj (ψ x) = 1 := by
    rw [hu, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
  have h2 : ‖ψ x‖ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : (‖ψ x‖ - 1) * (‖ψ x‖ + 1) = 0 := by ring_nf; rw [h2]; ring
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · have := norm_nonneg (ψ x); linarith
end Formalism.FourierDecayAlt.P.MeanNormSquaredBound
