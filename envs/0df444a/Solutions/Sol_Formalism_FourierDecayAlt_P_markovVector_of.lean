-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.markovVector_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:54.436336+00:00
-- url     : https://prove2.me/submissions/01569445-9587-4e2f-952a-023276f67c0f

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_interval_iter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_iteratedDeriv_vec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Polynomial
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.E.AMarkov → Formalism.FourierDecayAlt.E.MarkovVector := by
  intro hA H _ _ d a t₀ L M hL hM q t ht
  have hF : (fun s : ℝ => ∑ k : Fin (d + 1), s ^ (k : ℕ) • a k) =
      fun s : ℝ => ∑ k : Fin (d + 1), ((X : ℝ[X]) ^ (k : ℕ)).eval s • a k := by
    funext s; simp
  rw [hF, Markov.iteratedDeriv_vec Finset.univ a q (fun k : Fin (d + 1) => (X : ℝ[X]) ^ (k : ℕ))]
  obtain ⟨φ, hφ1, hφ2⟩ := exists_dual_vector'' ℝ
    (∑ k : Fin (d + 1), (derivative^[q] ((X : ℝ[X]) ^ (k : ℕ))).eval t • a k)
  set Q : ℝ[X] := ∑ k : Fin (d + 1), C (φ (a k)) * (X : ℝ[X]) ^ (k : ℕ) with hQ
  have hQdeg : Q.natDegree ≤ d := by
    rw [hQ]
    apply natDegree_sum_le_of_forall_le
    intro k _
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp k.2)
  have hQeval : ∀ s : ℝ, Q.eval s = φ (∑ k : Fin (d + 1), s ^ (k : ℕ) • a k) := by
    intro s
    rw [hQ, eval_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, map_smul, smul_eq_mul, mul_comm]
  have hQb : ∀ s ∈ Set.Icc t₀ (t₀ + L), |Q.eval s| ≤ M := by
    intro s hs
    rw [hQeval s, ← Real.norm_eq_abs]
    calc ‖φ (∑ k : Fin (d + 1), s ^ (k : ℕ) • a k)‖
        ≤ ‖φ‖ * ‖∑ k : Fin (d + 1), s ^ (k : ℕ) • a k‖ := φ.le_opNorm _
      _ ≤ 1 * ‖∑ k : Fin (d + 1), s ^ (k : ℕ) • a k‖ := by gcongr
      _ ≤ M := by rw [one_mul]; exact hM s hs
  have hQder : (derivative^[q] Q).eval t =
      φ (∑ k : Fin (d + 1), (derivative^[q] ((X : ℝ[X]) ^ (k : ℕ))).eval t • a k) := by
    rw [hQ, iterate_derivative_sum, eval_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iterate_derivative_C_mul, eval_mul, eval_C, map_smul, smul_eq_mul, mul_comm]
  have key := Markov.interval_iter hA d t₀ L hL q Q M hQdeg hQb t ht
  rw [hQder, hφ2] at key
  simpa using key
end Formalism.FourierDecayAlt.P
