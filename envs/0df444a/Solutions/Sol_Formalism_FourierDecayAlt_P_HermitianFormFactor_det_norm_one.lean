-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.det_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:18:19.921927+00:00
-- url     : https://prove2.me/submissions/56d19ee5-1645-492d-a0b0-9cfc08ce55ae

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution {g : Matrix m m ℂ} (hH : IsUnit H.det) (hg : g ∈ UH H) : ‖g.det‖ = 1 := by
  have h := congrArg Matrix.det (show gᴴ * H * g = H from hg)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have h1 : star g.det * g.det = 1 := by
    apply mul_right_cancel₀ hH.ne_zero
    linear_combination h
  have h2 : (Complex.normSq g.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]; exact h1
  have h3 : Complex.normSq g.det = 1 := by exact_mod_cast h2
  have h4 : ‖g.det‖ ^ 2 = 1 := by
    first
    | rw [Complex.sq_norm]; exact h3
    | rw [← Complex.normSq_eq_norm_sq]; exact h3
  rw [← Real.sqrt_sq (norm_nonneg _), h4, Real.sqrt_one]
end Formalism.FourierDecayAlt.P.HermitianFormFactor
