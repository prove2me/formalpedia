-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.sum_normSq_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:11.238704+00:00
-- url     : https://prove2.me/submissions/b11f0848-2768-4c4e-b581-fae96d2f7514

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution {d : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d → ℂ) :
    ∑ k, ‖(U *ᵥ x) k‖ ^ 2 = ∑ k, ‖x k‖ ^ 2 := by
  have key : ∀ y : Fin d → ℂ, ((∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ y := by
    intro y
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (Complex.conj_mul' (y k)).symm
  have h : star (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = star x ⬝ᵥ x := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    have : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    rw [this, Matrix.one_mulVec]
  exact_mod_cast (key _).trans (h.trans (key x).symm)
end Formalism.FourierDecayAlt.P.G9
