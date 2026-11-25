-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:36:32.329519+00:00
-- url     : https://prove2.me/submissions/aa85b9b2-2f76-4a9f-a98f-e90333d04339

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
open scoped Matrix.Norms.L2Operator
namespace Formalism.FourierDecayAlt.P.HermitianFormRankFour
theorem _root_.solution {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ∃ θ : ℝ, -Complex.exp (θ * Complex.I) ∉ spectrum ℂ A := by
  by_contra h
  push_neg at h
  have hfin : (spectrum ℂ A).Finite := by
    rw [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) ℂ ≃ₐ[ℂ] _) A]
    exact Module.End.finite_spectrum _
  refine Set.Icc_infinite Real.pi_pos
    (Set.Finite.of_finite_image (f := fun θ : ℝ => -Complex.exp (θ * Complex.I)) (hfin.subset ?_) ?_)
  · rintro _ ⟨θ, _, rfl⟩
    exact h θ
  · intro θ1 h1 θ2 h2 he
    apply Real.injOn_cos h1 h2
    have := congrArg Complex.re he
    simpa [Complex.exp_ofReal_mul_I_re] using this
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
