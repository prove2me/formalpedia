-- Prove2me | solution 1 for DualSepClusterLP.deterministicApproximation
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-19T07:25:41.107756+00:00
-- url     : https://prove2.me/submissions/a6b1f428-6fe4-4e57-92fe-6991f45cc216

import Theorems.Thm_DualSepClusterLP_primalDualApproximation
import Theorems.Thm_DualSepClusterLP_deterministicRounding
import Theorems.Thm_DualSepClusterLP_composeSparseOutputMachines

set_option autoImplicit false

namespace DualSepClusterLP

private def fiber {n : ℕ} (D : Clustering n) (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => D i = p)

private theorem pair_sum {n : ℕ} (g : Bool) (u v : Fin n) :
    (∑ p : Fin n,
      if g then (if decide (u = p) != decide (v = p) then (1 : ℝ)/2 else 0)
      else (if u = p ∧ v = p then 1 else 0)) =
        (if g ≠ decide (u = v) then 1 else 0) := by
  classical
  cases g
  · by_cases h : u = v
    · subst v
      simp
    · have hx (p : Fin n) : ¬(u = p ∧ v = p) := fun hp => h (hp.1.trans hp.2.symm)
      simp [hx,h]
  · by_cases h : u = v
    · subst v
      simp
    · have expand (p : Fin n) :
            (if decide (u = p) != decide (v = p) then (1 : ℝ)/2 else 0) =
            (if u = p then (1 : ℝ)/2 else 0) + (if v = p then (1 : ℝ)/2 else 0) := by
            by_cases hu : u = p <;> by_cases hv : v = p <;> simp_all
      change (∑ p : Fin n, if decide (u = p) != decide (v = p) then (1 : ℝ)/2 else 0) = _
      simp_rw [expand]
      rw [Finset.sum_add_distrib]
      norm_num [h]

private theorem sum_fiber_cost {n : ℕ} (G : Graph n) (D : Clustering n) :
    ∑ p : Fin n, subsetCost G (fiber D p) = (disagreements G D : ℝ) := by
  classical
  unfold subsetCost disagreements
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simpa [hij, fiber] using pair_sum (G i j) (D i) (D j)
  · simp [hij]

private theorem partitionPoint {n : ℕ} (G : Graph n) (D : Clustering n) :
    ∃ z : Finset (Fin n) → ℝ, PrimalFeasible z ∧ primalValue G z = (disagreements G D : ℝ) := by
  classical
  let z (S : Finset (Fin n)) : ℝ := ∑ p : Fin n, if S = fiber D p then 1 else 0
  have push (f : Finset (Fin n) → ℝ) :
      ∑ S : Finset (Fin n), f S * z S = ∑ p : Fin n, f (fiber D p) := by
    simp_rw [z,Finset.mul_sum,mul_ite,mul_one,mul_zero]
    rw [Finset.sum_comm]
    simp
  refine ⟨z, ⟨fun S => Finset.sum_nonneg (fun p _ => by split <;> norm_num), ?_⟩, ?_⟩
  · intro i
    simpa [ite_mul, fiber] using push (fun S => if i ∈ S then 1 else 0)
  · exact (push (subsetCost G)).trans (sum_fiber_cost G D)

private theorem opt_le_integral {n : ℕ} (G : Graph n) (D : Clustering n) :
    sInf {v : ℝ | ∃ z : Finset (Fin n) → ℝ, PrimalFeasible z ∧ primalValue G z = v} ≤
      (disagreements G D : ℝ) := by
  apply csInf_le
  swap
  · exact partitionPoint G D
  refine ⟨0, ?_⟩
  intro v hv
  rcases hv with ⟨z,hz,rfl⟩
  apply Finset.sum_nonneg
  intro S _
  apply mul_nonneg _ (hz.1 S)
  unfold subsetCost
  positivity

private theorem roundingTransfer {n : ℕ} (G : Graph n) (C D : Clustering n) (t : ℕ)
    (v : ℝ) (hr : (disagreements G C : ℝ) ≤ (2773 / 2000 : ℝ) * v)
    (hp : v ≤ (1 + 1 / (((2*t+1 : ℕ) : ℝ) + 1)) *
      sInf {x : ℝ | ∃ z : Finset (Fin n) → ℝ, PrimalFeasible z ∧ primalValue G z = x}) :
    2000 * (t+1) * disagreements G C ≤ (2773 * (t+1) + 2000) * disagreements G D := by
  let e : ℝ := 1 + 1 / (((2*t+1 : ℕ) : ℝ) + 1)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hv : v ≤ e * (disagreements G D : ℝ) :=
    hp.trans (mul_le_mul_of_nonneg_left (opt_le_integral G D) he)
  have h : (disagreements G C : ℝ) ≤ (2773 / 2000 : ℝ) * (e * (disagreements G D : ℝ)) :=
    hr.trans (mul_le_mul_of_nonneg_left hv (by norm_num))
  have hz : (2000 : ℝ) * ((t : ℝ)+1) * ((2773 / 2000 : ℝ) * e) ≤
      (2773 : ℝ) * ((t : ℝ)+1) + 2000 := by
    dsimp [e]
    push_cast
    field_simp
    nlinarith only [Nat.cast_nonneg (α := ℝ) t]
  have hf := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (2000 : ℝ) * ((t : ℝ)+1))
  have hk := mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg (α := ℝ) (disagreements G D))
  have htotal : (2000 : ℝ) * ((t : ℝ)+1) * (disagreements G C : ℝ) ≤
      ((2773 : ℝ) * ((t : ℝ)+1) + 2000) * (disagreements G D : ℝ) := by
    calc
      _ ≤ _ := hf
      _ = ((2000 : ℝ) * ((t : ℝ)+1) * ((2773 / 2000 : ℝ) * e)) * (disagreements G D : ℝ) := by ring
      _ ≤ _ := hk
  exact_mod_cast htotal

end DualSepClusterLP

namespace DualSepClusterLP

/-- A polynomial of the LP solver's clock and the lengths of the unary parameter and
the graph matrix still has exponential-parameter, polynomial-input running time. -/
theorem eptasClockClosure (A a b K d : ℕ) :
    ∃ A' a' b' : ℕ, ∀ t n : ℕ,
      K * (2 ^ (A * (2 * (t+1)) ^ a) * (n+1)^b + (t+1) + (n+1)^2 + 1)^d ≤
        2 ^ (A' * (t+1)^a') * (n+1)^b' := by
  let c := A * 2^a + 1
  refine ⟨K * 4^d + c*d, a+1, (b+2)*d, ?_⟩
  intro t n
  let u := t+1
  let v := n+1
  have hu : 0 < u := Nat.succ_pos t
  have hv : 0 < v := Nat.succ_pos n
  let W := u^(a+1)
  let E := 2^(c*W)
  let V := v^(b+2)
  have hW : 0 < W := Nat.pow_pos hu
  have hE : 0 < E := Nat.pow_pos (by decide : 0<2)
  have hV : 0 < V := Nat.pow_pos hv
  have hc : 0 < c := Nat.succ_pos _
  have hA : A*(2*u)^a ≤ c*W := by
    rw [mul_pow, ← mul_assoc]
    exact Nat.mul_le_mul (by dsimp [c]; omega) (Nat.pow_le_pow_right hu (by omega))
  have hT : 2^(A*(2*u)^a)*v^b ≤ E*V :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hA) (Nat.pow_le_pow_right hv (by omega))
  have hU : u ≤ E*V := calc
    u ≤ 2^u := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ E := Nat.pow_le_pow_right (by decide) ((Nat.le_self_pow (by omega : a+1≠0) u).trans
      (Nat.le_mul_of_pos_left W hc))
    _ ≤ E*V := Nat.le_mul_of_pos_right E hV
  have hVV : v^2 ≤ E*V :=
    (Nat.pow_le_pow_right hv (show 2 ≤ b+2 by omega)).trans (Nat.le_mul_of_pos_left V hE)
  have hOne : 1 ≤ E*V := Nat.mul_pos hE hV
  have hSum : 2^(A*(2*u)^a)*v^b + u + v^2 + 1 ≤ 4*(E*V) := by omega
  have hK : K*4^d ≤ 2^((K*4^d)*W) := calc
    K*4^d ≤ 2^(K*4^d) := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ hW)
  change K * (2^(A*(2*u)^a)*v^b+u+v^2+1)^d ≤ 2^((K*4^d+c*d)*W)*v^((b+2)*d)
  calc
    _ ≤ K*(4*(E*V))^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hSum d)
    _ = (K*4^d)*E^d*V^d := by simp only [mul_pow]; ac_rfl
    _ ≤ (2^((K*4^d)*W))*E^d*V^d := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hK)
    _ = _ := by
      dsimp only [E, V]
      rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_mul]
      congr 2
      ring
end DualSepClusterLP

open DualSepClusterLP

theorem solution :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A a b : ℕ),
      (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ (t n : ℕ) (G : Graph n), ∃ C : Clustering n,
        Nonempty (Turing.TM2OutputsInTime M.tm
          ((graphInput t G).map M.inputAlphabet.symm)
          (some ((partitionOutput C).map M.outputAlphabet.symm))
          (2 ^ (A * (t+1)^a) * (n+1)^b)) ∧
        ∀ D : Clustering n,
          2000 * (t+1) * disagreements G C ≤
            (2773 * (t+1) + 2000) * disagreements G D  := by
  obtain ⟨solver, A, a, b, supportConst, supportPower, solverFinite, solveLP⟩ :=
    primalDualApproximation
  obtain ⟨rounder, R, r, rounderFinite, roundLP⟩ := deterministicRounding
  obtain ⟨machine, K, d, machineFinite, pipeline⟩ :=
    composeSparseOutputMachines solver rounder solverFinite rounderFinite R r
  obtain ⟨A', a', b', bound⟩ := eptasClockClosure A a b K d
  refine ⟨machine, A', a', b', machineFinite, ?_⟩
  intro t n G
  obtain ⟨L, q, solverRun, valid, _, _, _, nearOptimal⟩ := solveLP (2*t+1) n G
  obtain ⟨C, rounderRun, roundingCost⟩ := roundLP n G L valid
  let s := 2 ^ (A * ((2*t+1)+1)^a) * (n+1)^b
  obtain ⟨run⟩ := pipeline t n G L (pricesBits q) (partitionOutput C) s solverRun rounderRun
  have clock : K * (s + (t+1) + (n+1)^2 + 1)^d ≤
      2 ^ (A' * (t+1)^a') * (n+1)^b' := by
    simpa only [s, show 2*t+1+1 = 2*(t+1) by omega] using bound t n
  exact ⟨C, ⟨⟨run.toEvalsTo, run.steps_le_m.trans clock⟩⟩,
    fun D => roundingTransfer G C D t _ roundingCost nearOptimal⟩
