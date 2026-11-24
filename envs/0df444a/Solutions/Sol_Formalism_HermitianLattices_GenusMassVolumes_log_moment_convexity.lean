-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.log_moment_convexity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:19.46505+00:00
-- url     : https://prove2.me/submissions/647b3e3d-51f7-4e03-a237-254e87c74e82

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HolderExponentialMoments
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset
private lemma exponential_moment_pos {ι : Type} [Fintype ι] (P y : ι → ℝ) (hP : ∀ j, 0 ≤ P j) (h1 : ∑ j, P j = 1)
    (t : ℝ) : 0 < ∑ j, P j * Real.exp (t * y j) := by
  have hne : ∃ j, 0 < P j := by
    by_contra hc
    push_neg at hc
    have : ∑ j, P j ≤ 0 := sum_nonpos fun j _ => hc j
    linarith
  obtain ⟨j, hj⟩ := hne
  exact lt_of_lt_of_le (mul_pos hj (Real.exp_pos _))
    (single_le_sum (f := fun j => P j * Real.exp (t * y j))
      (fun i _ => mul_nonneg (hP i) (Real.exp_pos _).le) (mem_univ j))
private lemma holder_exponential_moments {ι : Type} [Fintype ι] (P y : ι → ℝ) (hP : ∀ j, 0 ≤ P j)
    (s t a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ∑ j, P j * Real.exp ((a * s + b * t) * y j) ≤
      (∑ j, P j * Real.exp (s * y j)) ^ a * (∑ j, P j * Real.exp (t * y j)) ^ b := by
  have hzero : ∀ u : ℝ, ∑ j, P j * Real.exp (u * y j) = 0 → ∀ j, P j = 0 := by
    intro u hu j
    have := (sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (hP i) (Real.exp_pos (u * y i)).le)).1 hu j (mem_univ j)
    exact (mul_eq_zero.1 this).resolve_right (Real.exp_pos _).ne'
  have hL0 : (∀ j, P j = 0) → ∑ j, P j * Real.exp ((a * s + b * t) * y j) = 0 := by
    intro h0; simp [h0]
  have hS0 : 0 ≤ ∑ j, P j * Real.exp (s * y j) :=
    sum_nonneg fun j _ => mul_nonneg (hP j) (Real.exp_pos _).le
  have hT0 : 0 ≤ ∑ j, P j * Real.exp (t * y j) :=
    sum_nonneg fun j _ => mul_nonneg (hP j) (Real.exp_pos _).le
  rcases hS0.eq_or_lt with hS | hS
  · rw [hL0 (hzero s hS.symm), ← hS, Real.zero_rpow ha.ne', zero_mul]
  rcases hT0.eq_or_lt with hT | hT
  · rw [hL0 (hzero t hT.symm), ← hT, Real.zero_rpow hb.ne', mul_zero]
  set S := ∑ j, P j * Real.exp (s * y j) with hSdef
  set T := ∑ j, P j * Real.exp (t * y j) with hTdef
  have key : ∀ j, Real.exp ((a * s + b * t) * y j) =
      Real.exp (s * y j) ^ a * Real.exp (t * y j) ^ b := by
    intro j
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hSa : 0 < S ^ a := Real.rpow_pos_of_pos hS a
  have hTb : 0 < T ^ b := Real.rpow_pos_of_pos hT b
  have pt : ∀ j, P j * Real.exp ((a * s + b * t) * y j) / (S ^ a * T ^ b) ≤
      a * (P j * Real.exp (s * y j) / S) + b * (P j * Real.exp (t * y j) / T) := by
    intro j
    have g := Real.geom_mean_le_arith_mean2_weighted ha.le hb.le
      (div_nonneg (Real.exp_pos (s * y j)).le hS.le)
      (div_nonneg (Real.exp_pos (t * y j)).le hT.le) hab
    rw [Real.div_rpow (Real.exp_pos _).le hS.le, Real.div_rpow (Real.exp_pos _).le hT.le] at g
    rw [key j]
    calc P j * (Real.exp (s * y j) ^ a * Real.exp (t * y j) ^ b) / (S ^ a * T ^ b)
        = P j * (Real.exp (s * y j) ^ a / S ^ a * (Real.exp (t * y j) ^ b / T ^ b)) := by
          field_simp
      _ ≤ P j * (a * (Real.exp (s * y j) / S) + b * (Real.exp (t * y j) / T)) :=
          mul_le_mul_of_nonneg_left g (hP j)
      _ = a * (P j * Real.exp (s * y j) / S) + b * (P j * Real.exp (t * y j) / T) := by ring
  have hsum := sum_le_sum fun j (_ : j ∈ univ) => pt j
  have e1 : ∑ j, (a * (P j * Real.exp (s * y j) / S) + b * (P j * Real.exp (t * y j) / T)) = 1 := by
    simp only [sum_add_distrib, ← mul_sum, ← sum_div]
    rw [← hSdef, ← hTdef, div_self hS.ne', div_self hT.ne', mul_one, mul_one, hab]
  rw [e1, ← sum_div, div_le_one (mul_pos hSa hTb)] at hsum
  exact hsum
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : LogMomentConvexity := by
  intro ι _ P y hP h1
  have hpos := fun t => exponential_moment_pos P y hP h1 t
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (∑ j, P j * Real.exp (t * y j))) := by
    refine ⟨convex_univ, ?_⟩
    intro s _ t _ a b ha hb hab
    simp only [smul_eq_mul]
    rcases ha.eq_or_lt with ha0 | ha0
    · subst ha0
      have hb1 : b = 1 := by linarith
      subst hb1
      simp
    rcases hb.eq_or_lt with hb0 | hb0
    · subst hb0
      have ha1 : a = 1 := by linarith
      subst ha1
      simp
    have hh := holder_exponential_moments P y hP s t a b ha0 hb0 hab
    calc Real.log (∑ j, P j * Real.exp ((a * s + b * t) * y j))
        ≤ Real.log ((∑ j, P j * Real.exp (s * y j)) ^ a * (∑ j, P j * Real.exp (t * y j)) ^ b) :=
          Real.log_le_log (hpos _) hh
      _ = a * Real.log (∑ j, P j * Real.exp (s * y j)) +
            b * Real.log (∑ j, P j * Real.exp (t * y j)) := by
          rw [Real.log_mul (Real.rpow_pos_of_pos (hpos s) a).ne' (Real.rpow_pos_of_pos (hpos t) b).ne',
            Real.log_rpow (hpos s), Real.log_rpow (hpos t)]
  refine ⟨hconv, ?_⟩
  intro t₀ t ht₀ ht
  have htpos : 0 < t := lt_of_lt_of_le ht₀ ht
  have ht0ne : t₀ ≠ 0 := ht₀.ne'
  have htne : t ≠ 0 := htpos.ne'
  have hf0 : Real.log (∑ j, P j * Real.exp (0 * y j)) = 0 := by simp [h1]
  have hc := hconv.2 (Set.mem_univ t) (Set.mem_univ 0) (div_nonneg ht₀.le htpos.le)
    (sub_nonneg.2 ((div_le_one htpos).2 ht)) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, hf0] at hc
  have e : t₀ / t * t = t₀ := by field_simp
  rw [e] at hc
  calc t / t₀ * Real.log (∑ j, P j * Real.exp (t₀ * y j))
      ≤ t / t₀ * (t₀ / t * Real.log (∑ j, P j * Real.exp (t * y j))) :=
        mul_le_mul_of_nonneg_left hc (div_nonneg htpos.le ht₀.le)
    _ = Real.log (∑ j, P j * Real.exp (t * y j)) := by
        rw [← mul_assoc, div_mul_div_comm, mul_comm t t₀, div_self (mul_ne_zero ht0ne htne), one_mul]
end Formalism.HermitianLattices.GenusMassVolumes
