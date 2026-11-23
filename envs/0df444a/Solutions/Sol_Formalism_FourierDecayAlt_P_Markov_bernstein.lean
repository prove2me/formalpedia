-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.bernstein
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:45.450455+00:00
-- url     : https://prove2.me/submissions/60e551e9-f37d-40e7-b38f-622f90c9b893

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_th_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_th_lt_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_schur
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_exists_rot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset
namespace Formalism.FourierDecayAlt.P.Markov
theorem _root_.solution (p : ℝ[X]) (n : ℕ) (hn : n ≠ 0) (hp : p.natDegree ≤ n) (M : ℝ)
    (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) (θ : ℝ) :
    |sin θ * p.derivative.eval (cos θ)| ≤ n * M := by
  obtain ⟨A, B, hB, hAB⟩ := exists_rot (cos θ) (sin θ) p n hn hp
  have hB1 : B.eval 1 = sin θ * p.derivative.eval (cos θ) := by
    have h1 : HasDerivAt (fun φ : ℝ => p.eval (cos θ * cos φ + sin θ * sin φ))
        (p.derivative.eval (cos θ * cos 0 + sin θ * sin 0) *
          (cos θ * (-sin 0) + sin θ * cos 0)) 0 :=
      (p.hasDerivAt _).comp 0 (((hasDerivAt_cos 0).const_mul _).add ((hasDerivAt_sin 0).const_mul _))
    have h2 : HasDerivAt (fun φ : ℝ => A.eval (cos φ) + sin φ * B.eval (cos φ))
        (A.derivative.eval (cos 0) * (-sin 0) + (cos 0 * B.eval (cos 0) +
          sin 0 * (B.derivative.eval (cos 0) * (-sin 0)))) 0 :=
      ((A.hasDerivAt _).comp 0 (hasDerivAt_cos 0)).add
        ((hasDerivAt_sin 0).mul ((B.hasDerivAt _).comp 0 (hasDerivAt_cos 0)))
    have h3 : (fun φ : ℝ => p.eval (cos θ * cos φ + sin θ * sin φ)) =
        fun φ : ℝ => A.eval (cos φ) + sin φ * B.eval (cos φ) :=
      funext fun φ => hAB _ _ (cos_sq_add_sin_sq φ)
    rw [h3] at h1
    have h4 := h2.unique h1
    simp at h4
    rw [h4]; ring
  rw [← hB1]
  refine schur n hn B hB M (fun k hk => ?_) 1 (fun k hk => ?_) le_rfl
  · have e1 := hAB (cos (th n k)) (sin (th n k)) (cos_sq_add_sin_sq _)
    have e2 := hAB (cos (th n k)) (-sin (th n k)) (by rw [neg_sq]; exact cos_sq_add_sin_sq _)
    have m1 := hM (cos θ * cos (th n k) + sin θ * sin (th n k))
      (by rw [← cos_sub]; exact ⟨neg_one_le_cos _, cos_le_one _⟩)
    have m2 := hM (cos θ * cos (th n k) + sin θ * -sin (th n k))
      (by rw [mul_neg, ← sub_eq_add_neg, ← cos_add]; exact ⟨neg_one_le_cos _, cos_le_one _⟩)
    rw [e1] at m1
    rw [e2] at m2
    rw [abs_le] at m1 m2 ⊢
    constructor <;> linarith [m1.1, m1.2, m2.1, m2.2]
  · rw [← cos_zero]
    exact cos_lt_cos_of_nonneg_of_le_pi le_rfl (th_lt_pi hk).le (th_pos n k hn)
end Formalism.FourierDecayAlt.P.Markov
