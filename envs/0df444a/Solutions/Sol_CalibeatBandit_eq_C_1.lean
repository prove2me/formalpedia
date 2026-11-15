-- Prove2me | solution 1 for CalibeatBandit.eq_C_1
-- status  : ACCEPTED   (prove)
-- author  : @jasonhartline
-- created : 2026-11-14T12:46:53.042583+00:00
-- url     : https://prove2.me/submissions/b1a4edfd-4079-4507-a836-97f16989e5e2

import Mathlib.Tactic
import Definitions.Def_CalibeatBandit_algState

set_option autoImplicit false

open Matrix CalibeatBandit
open scoped BigOperators

private noncomputable def logPartition {K : ℕ} (η : ℝ) (G : Fin K → ℝ) : ℝ :=
  Real.log (1 / K * ∑ j, Real.exp (η * G j))

private theorem logPartition_step {K : ℕ} (i : Fin K) (η : ℝ) (G z : Fin K → ℝ) :
    Real.log (∑ j, FewExperts.hedgeWeights η G j * Real.exp (η * z j)) =
      logPartition η (fun j => G j + z j) - logPartition η G := by
  have hK : 0 < (K : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have pos (G : Fin K → ℝ) : 0 < ∑ j, Real.exp (η * G j) :=
    (Real.exp_pos _).trans_le (Finset.single_le_sum (fun _ _ => Real.exp_nonneg _) (Finset.mem_univ i))
  have hsum : ∑ j, FewExperts.hedgeWeights η G j * Real.exp (η * z j) =
      (∑ j, Real.exp (η * (G j + z j))) / (∑ j, Real.exp (η * G j)) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by
      rw [FewExperts.hedgeWeights, mul_add, Real.exp_add, div_mul_eq_mul_div]
  rw [hsum, Real.log_div (pos _).ne' (pos _).ne']
  unfold logPartition
  rw [Real.log_mul (by positivity) (pos _).ne', Real.log_mul (by positivity) (pos _).ne']
  ring

/-- **(C.1): the mixing learner's `SR` feedback telescopes** (§C.2, proof of Lemma C.3,
p.32). For the bandit calibeating algorithm with learning rate `η > 0` and every history,
`∑_{t=1}^T H^SR_t = (1/η) ∑_i log((1/K) ∑_j exp(η ∑_{t=1}^T x_t(i) v_t(j)))`,
and likewise
`∑_{t=1}^T H^Rec_t = (1/η) ∑_i log((1/K) ∑_j exp(η ∑_{t=1}^T 1{J_t = i} v_t(j)))`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, display (C.1), p.32; the `Rec` identity is the "similar" analysis of the
second term of Lemma C.3 (p.32).

**Formalization Note.** `algHSR`, `algHRec`, `algX`, `algV` are the algorithm's `H^SR_t`,
`H^Rec_t`, `x_t`, `v_t` computed from the learner's observations `J`, `I` and observed rewards
`r` (any sequences); rounds are `0, …, T − 1`; `log` is `Real.log`. The identity is exact for every
history and every exploration parameter `μ`. The second conjunct is the `Rec` analogue that the
paper uses without displaying it. -/
theorem solution {K : ℕ} (η μ : ℝ) (_hη : 0 < η) (J I : ℕ → Fin K) (r : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, algHSR η μ J I r t
      = 1 / η * ∑ i, Real.log (1 / K * ∑ j, Real.exp
          (η * ∑ t ∈ Finset.range T, algX η μ J I r t i * algV η μ J I r t j)) ∧
    ∑ t ∈ Finset.range T, algHRec η μ J I r t
      = 1 / η * ∑ i, Real.log (1 / K * ∑ j, Real.exp
          (η * ∑ t ∈ Finset.range T, (if J t = i then algV η μ J I r t j else 0))) := by
  let S := algState η μ J I r
  let x := algX η μ J I r
  let v := algV η μ J I r
  have stateSR (t : ℕ) (i j : Fin K) :
      (S t).cumSR i j = ∑ u ∈ Finset.range t, x u i * v u j := by
    induction t with
    | zero => simp [S, algState, LearnerState.init]
    | succ t ih =>
      rw [Finset.sum_range_succ, ← ih]
      rfl
  have stateRec (t : ℕ) (i j : Fin K) :
      (S t).cumRec i j = ∑ u ∈ Finset.range t, (if J u = i then v u j else 0) := by
    induction t with
    | zero => simp [S, algState, LearnerState.init]
    | succ t ih =>
      rw [Finset.sum_range_succ, ← ih]
      rfl
  have telescopes (g : ℕ → Fin K → ℝ) (t : ℕ) :
      ∑ u ∈ Finset.range t, (logPartition η (g (u + 1)) - logPartition η (g u)) =
        logPartition η (g t) - logPartition η (g 0) := by
    induction t with
    | zero => simp
    | succ t ih => rw [Finset.sum_range_succ, ih]; ring
  have initial (i : Fin K) : logPartition η (fun _ : Fin K => 0) = 0 := by
    have hK : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt).ne'
    simp [logPartition, hK]
  have hSR (t : ℕ) :
      algHSR η μ J I r t = 1 / η * ∑ i,
        (logPartition η ((S (t + 1)).cumSR i) - logPartition η ((S t).cumSR i)) := by
    unfold algHSR HSRof
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    change Real.log (∑ j, FewExperts.hedgeWeights η ((S t).cumSR i) j *
        Real.exp (η * x t i * v t j)) =
      logPartition η (fun j => (S t).cumSR i j + x t i * v t j) -
        logPartition η ((S t).cumSR i)
    simpa only [mul_assoc] using logPartition_step i η ((S t).cumSR i) (fun j => x t i * v t j)
  have hRec (t : ℕ) :
      algHRec η μ J I r t = 1 / η * ∑ i,
        (logPartition η ((S (t + 1)).cumRec i) - logPartition η ((S t).cumRec i)) := by
    unfold algHRec HRecOf
    congr 1
    symm
    rw [Finset.sum_eq_single (s := Finset.univ)
      (f := fun i => logPartition η ((S (t + 1)).cumRec i) - logPartition η ((S t).cumRec i)) (J t)]
    · change logPartition η (fun j => (S t).cumRec (J t) j + if J t = J t then v t j else 0) -
        logPartition η ((S t).cumRec (J t)) = Real.log
          (∑ j, FewExperts.hedgeWeights η ((S t).cumRec (J t)) j * Real.exp (η * v t j))
      simpa only [if_true] using (logPartition_step (J t) η ((S t).cumRec (J t)) (v t)).symm
    · intro i _ hi
      change logPartition η (fun j => (S t).cumRec i j + if J t = i then v t j else 0) -
        logPartition η ((S t).cumRec i) = 0
      simp [Ne.symm hi]
    · simp
  constructor
  · simp_rw [hSR, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [telescopes (fun t => (S t).cumSR i) T, show (S 0).cumSR i = (fun _ => 0) from rfl,
        initial i, sub_zero]
      simp only [logPartition, stateSR, x, v]
  · simp_rw [hRec, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [telescopes (fun t => (S t).cumRec i) T, show (S 0).cumRec i = (fun _ => 0) from rfl,
        initial i, sub_zero]
      simp only [logPartition, stateRec, v]

