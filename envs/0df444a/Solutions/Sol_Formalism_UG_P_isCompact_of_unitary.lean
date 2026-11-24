-- Prove2me | solution 1 for Formalism.UG.P.isCompact_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:01.97745+00:00
-- url     : https://prove2.me/submissions/2d577d66-9dcc-47be-a84e-e26e2c80a1bb

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {T : Set (Matrix n n ℂ)} (hT : IsClosed T)
    (hU : ∀ M ∈ T, star M * M = 1) : IsCompact T := by
  have hsub : T ⊆ (Set.pi Set.univ (fun _ : n => Set.pi Set.univ
      (fun _ : n => Metric.closedBall (0 : ℂ) 1)) : Set (Matrix n n ℂ)) := by
    intro M hM i _ j _
    have h := congrFun (congrFun (hU M hM) j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
    have key : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
      intro z
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    simp only [key] at h
    rw [← Complex.ofReal_sum, ← Complex.ofReal_one, Complex.ofReal_inj] at h
    have hle : Complex.normSq (M i j) ≤ 1 := by
      rw [← h]
      exact Finset.single_le_sum (f := fun x => Complex.normSq (M x j))
        (fun x _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    rw [Metric.mem_closedBall, dist_zero_right]
    have h2 : ‖M i j‖ ^ 2 ≤ 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hle
    nlinarith [norm_nonneg (M i j)]
  have hK : IsCompact (Set.pi Set.univ (fun _ : n => Set.pi Set.univ
      (fun _ : n => Metric.closedBall (0 : ℂ) 1)) : Set (Matrix n n ℂ)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 1))
  exact hK.of_isClosed_subset hT hsub
end Formalism.UG.P
