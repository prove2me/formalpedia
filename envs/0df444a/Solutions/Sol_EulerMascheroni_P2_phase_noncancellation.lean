-- Prove2me | solution 1 for EulerMascheroni.P2.phase_noncancellation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T00:17:24.31649+00:00
-- url     : https://prove2.me/submissions/57aefd8f-1139-4679-a1de-d260a2cdcc27

import Definitions.Def_eulerMascheroni_p2Approximation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Filter Topology
open EulerMascheroni.P2

private lemma frequent_sine_of_small_steps (a : ℕ → ℝ)
    (ha : Tendsto a atTop atTop)
    (hstep : Tendsto (fun n => a (n+1)-a n) atTop (nhds 0)) :
    ∃ᶠ n in atTop, (1/2 : ℝ) ≤ |Real.sin (a n)| := by
  rw [frequently_atTop]
  intro N
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (hstep.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)))
  let B := max N M
  obtain ⟨k, hk⟩ := exists_nat_gt ((a B - Real.pi/2)/(2*Real.pi))
  let T := Real.pi/2 + (k : ℝ)*(2*Real.pi)
  have hT : a B < T := by
    have hpp : (0 : ℝ) < 2*Real.pi := by positivity
    have := (div_lt_iff₀ hpp).mp hk
    dsimp [T]
    linarith
  have hex : ∃ j : ℕ, T ≤ a (B+j) := by
    have hab := ha.comp (tendsto_add_atTop_nat B)
    obtain ⟨j, hj⟩ := (hab.eventually (eventually_ge_atTop T)).exists
    exact ⟨j, by simpa [Nat.add_comm] using hj⟩
  let j := Nat.find hex
  have hj : T ≤ a (B+j) := Nat.find_spec hex
  have hjpos : 0 < j := by
    apply (Nat.find_pos hex).mpr
    simpa using not_le_of_gt hT
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
  have hiprev : a (B+i) < T := by
    apply lt_of_not_ge
    exact Nat.find_min hex (by change i < j; omega)
  have hist : a (B+i+1)-a (B+i) < 1/2 := hM (B+i) (by dsimp [B]; omega)
  have hclose : |a (B+j)-T| < 1/2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hj)]
    rw [hi] at hj ⊢
    simp only [Nat.succ_eq_add_one, ← Nat.add_assoc] at hj ⊢
    linarith
  have hsinT : Real.sin T = 1 := by
    dsimp [T]
    rw [Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  have hdist := (Real.abs_sin_sub_sin_le (a (B+j)) T).trans_lt hclose
  rw [hsinT, abs_lt] at hdist
  refine ⟨B+j, by dsimp [B]; omega, ?_⟩
  have hsin : 1/2 ≤ Real.sin (a (B+j)) := by linarith [hdist.1]
  exact hsin.trans (le_abs_self _)

private lemma power_step_bound (x p : ℝ) (hx : 0 < x) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ (x+1)^p-x^p ∧ (x+1)^p-x^p ≤ p*x^(p-1) := by
  constructor
  · exact sub_nonneg.mpr (Real.rpow_le_rpow hx.le (by linarith) hp0)
  · have hb := rpow_one_add_le_one_add_mul_self
      (show (-1 : ℝ) ≤ 1/x by have : (0 : ℝ) < 1/x := one_div_pos.mpr hx; linarith) hp0 hp1
    have hb' := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx.le p)
    have heq : x^p * (1+1/x)^p = (x+1)^p := by
      rw [← Real.mul_rpow hx.le (by positivity)]
      congr 1
      field_simp
    rw [heq] at hb'
    rw [Real.rpow_sub hx, Real.rpow_one]
    calc
      (x+1)^p-x^p ≤ x^p * (1+p*(1/x))-x^p := sub_le_sub_right hb' _
      _ = p*(x^p/x) := by ring

private lemma power_step_limit (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Tendsto (fun n : ℕ => (((n : ℝ)+1)+1)^p - ((n : ℝ)+1)^p) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop := by
    simpa [Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hh : Tendsto (fun n : ℕ => ((n : ℝ)+1)^(p-1)) atTop (nhds 0) := by
    convert (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < 1-p)).comp ht using 1
    funext n
    congr 1
    ring
  apply squeeze_zero
    (fun n : ℕ => (power_step_bound ((n : ℝ)+1) p (by positivity) hp0 hp1.le).1)
    (fun n : ℕ => (power_step_bound ((n : ℝ)+1) p (by positivity) hp0 hp1.le).2)
  simpa using hh.const_mul p

theorem solution :
    ∃ᶠ n : ℕ in atTop, (1/2 : ℝ) ≤ |Real.sin (phase (n+1))| := by
  apply frequent_sine_of_small_steps
  · have hsin : 0 < Real.sin theta := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · unfold theta; positivity
      · unfold theta; nlinarith [Real.pi_pos]
    have hsin3 : Real.sin (3*theta) ≤ 0 := by
      rw [show 3*theta = Real.pi/5 + Real.pi by unfold theta; ring,
        Real.sin_add_pi]
      have := Real.sin_pos_of_pos_of_lt_pi
        (by positivity : (0 : ℝ) < Real.pi/5)
        (by nlinarith [Real.pi_pos] : Real.pi/5 < Real.pi)
      linarith
    have ht : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hs : Tendsto (fun n : ℕ => scale (n+1)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/5)).comp ht
    have hlead : Tendsto (fun n : ℕ => (5 * Real.sin theta) * scale (n+1) - 2*theta)
        atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(2*theta))
        (hs.const_mul_atTop (by positivity : (0 : ℝ) < 5 * Real.sin theta))
    apply tendsto_atTop_mono (f := fun n : ℕ => (5 * Real.sin theta) * scale (n+1) - 2*theta) _ hlead
    intro n
    have hsub : 0 ≤ subscale (n+1) := by unfold subscale; positivity
    unfold phase
    nlinarith
  · have h4 := (power_step_limit (4/5) (by norm_num) (by norm_num)).const_mul
      (5 * Real.sin theta)
    have h2 := (power_step_limit (2/5) (by norm_num) (by norm_num)).const_mul
      ((2/3 : ℝ) * Real.sin (3*theta))
    convert h4.sub h2 using 1
    · funext n
      unfold phase scale subscale
      push_cast
      ring
    · simp


#print axioms solution
