-- Prove2me | solution 1 for Freiman.form_lattice_descent_negative
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:16:12.064758+00:00
-- url     : https://prove2.me/submissions/f5b5867e-3a02-4e96-ab0b-38f3b945d058

import Definitions.Def_Freiman_reducedForms
import Theorems.Thm_Freiman_form_step_identity

open Freiman

private theorem reduced_factor (α β : ℝ) (p q : ℤ) :
    reducedValue α β p q = ((p : ℝ) - α*q) * ((p : ℝ) + β*q) / (α+β) := by
  unfold reducedValue quadraticValue reducedA reducedB reducedC
  ring

private theorem orbit_infimum_le (R : ReducedOrbit) (n : ℤ) :
    orbitReciprocalInfimum R ≤ 1 / (R.alpha n + R.beta n) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro y ⟨j, rfl⟩
    exact le_of_lt (div_pos one_pos (by have := R.alpha_gt j; have := R.beta_pos j; linarith))
  · exact ⟨n, rfl⟩

theorem solution (R : ReducedOrbit) (n p q : ℤ) (hp : 0 < p) (hq : q < 0)
    (hv : |reducedValue (R.alpha n) (R.beta n) p q| < orbitReciprocalInfimum R) :
    let r := ((R.digits (n-1) : ℕ) : ℤ)*p+q;
      (r ≠ 0 ∨ p ≠ 0) ∧
      |reducedValue (R.alpha (n-1)) (R.beta (n-1)) r p| = |reducedValue (R.alpha n) (R.beta n) p q| ∧
      latticeSize r p < latticeSize p q := by
  let a : ℤ := (R.digits (n-1) : ℕ)
  let r : ℤ := a*p+q
  change (r ≠ 0 ∨ p ≠ 0) ∧ _ ∧ _
  have ha : 1 ≤ a := by
    have ht := (R.digits (n-1)).pos
    dsimp [a]
    omega
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hβ : 0 < R.beta n := R.beta_pos n
  have hα : 1 < R.alpha n := R.alpha_gt n
  have hβprev : 0 < R.beta (n-1) := R.beta_pos (n-1)
  have hden : 0 < R.alpha n + R.beta n := by linarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hq1 : (q : ℝ) ≤ -1 := by exact_mod_cast (show q ≤ -1 by omega)
  have hindices : n-1+1=n := by omega
  have hreciprocal : 1 / (R.alpha (n-1) + R.beta (n-1)) =
      R.alpha n * R.beta n / (R.alpha n + R.beta n) := by
    have ht := form_step_identity R (n-1) 0 1
    rw [hindices] at ht
    simpa [reducedValue, quadraticValue, reducedA, reducedB, reducedC, neg_div] using ht
  have hprod : |((p : ℝ) - R.alpha n*q) * ((p : ℝ) + R.beta n*q)| <
      R.alpha n * R.beta n := by
    have ht := lt_of_lt_of_le hv (orbit_infimum_le R (n-1))
    rw [hreciprocal, reduced_factor, abs_div, abs_of_pos hden] at ht
    exact (div_lt_div_iff_of_pos_right hden).mp ht
  have hbs : R.beta n = 1 / ((a : ℝ) + R.beta (n-1)) := by
    simpa [a] using R.beta_step (n-1)
  have hbid : R.beta n * ((a : ℝ) + R.beta (n-1)) = 1 :=
    (eq_div_iff (ne_of_gt (by linarith : 0 < (a : ℝ) + R.beta (n-1)))).mp hbs
  have hr : r ≤ 0 := by
    by_contra hbad
    have hz : 1 ≤ a*p+q := by dsimp [r] at hbad; omega
    have hzR : (1 : ℝ) ≤ (a : ℝ)*p+q := by exact_mod_cast hz
    have hfirst : R.alpha n < (p : ℝ) - R.alpha n*q := by
      have ht := mul_le_mul_of_nonneg_left hq1 (by linarith : 0 ≤ R.alpha n)
      nlinarith
    have hsecond : R.beta n < (p : ℝ) + R.beta n*q := by
      have ht := mul_le_mul_of_nonneg_left hzR (le_of_lt hβ)
      have hstrict := mul_pos (mul_pos hβ hβprev) hpR
      have hidp := congrArg (fun x : ℝ => x * (p : ℝ)) hbid
      nlinarith
    have hfactor : |((p : ℝ) - R.alpha n*q) * ((p : ℝ) + R.beta n*q)| =
        ((p : ℝ)-R.alpha n*q)*((p : ℝ)+R.beta n*q) := by
      exact abs_of_pos (mul_pos (by linarith) (by linarith))
    rw [hfactor] at hprod
    have ht := mul_lt_mul hfirst (le_of_lt hsecond) hβ (by linarith)
    linarith
  refine ⟨Or.inr (ne_of_gt hp), ?_, ?_⟩
  · have ht := congrArg abs (form_step_identity R (n-1) p q)
    simpa only [hindices, abs_neg] using ht
  · have hsize : (latticeSize r p : ℤ) < latticeSize p q := by
      simp only [latticeSize, Nat.cast_add, Int.natCast_natAbs,
        abs_of_nonneg (le_of_lt hp), abs_of_nonpos (le_of_lt hq), abs_of_nonpos hr]
      dsimp [r]
      have ht := mul_pos (by omega : 0 < a) hp
      nlinarith
    exact_mod_cast hsize
