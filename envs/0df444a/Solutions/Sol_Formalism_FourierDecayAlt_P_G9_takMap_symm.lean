-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.takMap_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:28.453623+00:00
-- url     : https://prove2.me/submissions/2681fce2-d515-45ea-aefa-d541a512ac0f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_takMap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate
open Module
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsSymm)
    (x y : EuclideanSpace ℂ (Fin d)) : ⟪takMap H x, y⟫_ℂ = ⟪takMap H y, x⟫_ℂ := by
  simp only [PiLp.inner_apply, takMap_apply, RCLike.inner_apply, map_sum, map_mul, Complex.conj_conj,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH.apply i j]
  ring
end Formalism.FourierDecayAlt.P.G9
