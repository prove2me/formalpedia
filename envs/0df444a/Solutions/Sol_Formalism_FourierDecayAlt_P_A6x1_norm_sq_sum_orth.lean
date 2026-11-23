-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x1.norm_sq_sum_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:39.168842+00:00
-- url     : https://prove2.me/submissions/f2836923-47b2-470b-ad40-1f21394316fd

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialMeansOrthogonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x1
namespace Formalism.FourierDecayAlt.P.A6x1
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A : Type}
    [Fintype A] (P : A → E) (e₁ : A → ℂ) (he : ∀ ρ, ‖e₁ ρ‖ = 1)
    (h : ∀ ρ ρ', ρ ≠ ρ' → inner ℂ (P ρ) (P ρ') = 0) :
    ‖∑ ρ, e₁ ρ • P ρ‖ ^ 2 = ∑ ρ, ‖P ρ‖ ^ 2 := by
  classical
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [inner_sum, Finset.sum_eq_single ρ]
  · rw [inner_self_eq_norm_sq (𝕜 := ℂ), norm_smul, he ρ, one_mul]
  · intro ρ' _ hne
    rw [inner_smul_left, inner_smul_right, h ρ ρ' (Ne.symm hne), mul_zero, mul_zero]
  · intro hρ
    exact absurd (Finset.mem_univ ρ) hρ
end Formalism.FourierDecayAlt.P.A6x1
