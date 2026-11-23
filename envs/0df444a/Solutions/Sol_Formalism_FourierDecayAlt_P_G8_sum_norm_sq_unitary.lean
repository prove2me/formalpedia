-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G8.sum_norm_sq_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:51.741882+00:00
-- url     : https://prove2.me/submissions/a1f5aaf9-2c9d-4cd2-bba6-790011b55555

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P.G8
theorem _root_.solution (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d → ℂ) :
    ∑ k, ‖(U *ᵥ x) k‖ ^ 2 = ∑ k, ‖x k‖ ^ 2 := by
  have e : ∀ y : Fin d → ℂ, ((∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ y := by
    intro y
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]; rfl
  have h := Matrix.mem_unitaryGroup_iff'.1 hU
  have : ((∑ k, ‖(U *ᵥ x) k‖ ^ 2 : ℝ) : ℂ) = ((∑ k, ‖x k‖ ^ 2 : ℝ) : ℂ) := by
    rw [e, e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, h, Matrix.one_mulVec]
  exact_mod_cast this
end Formalism.FourierDecayAlt.P.G8
