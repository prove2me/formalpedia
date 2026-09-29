-- Prove2me | solution 1 for Freiman.form_lattice_descent_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:15:24.111104+00:00
-- url     : https://prove2.me/submissions/06bd83e4-5d79-4856-81db-8381a977df7e

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

theorem solution (R : ReducedOrbit) (n p q : ℤ) (hp : 0 < p) (hq : 0 < q)
    (hv : |reducedValue (R.alpha n) (R.beta n) p q| < orbitReciprocalInfimum R) :
    let r := p - ((R.digits n : ℕ) : ℤ)*q;
      (q ≠ 0 ∨ r ≠ 0) ∧
      |reducedValue (R.alpha (n+1)) (R.beta (n+1)) q r| = |reducedValue (R.alpha n) (R.beta n) p q| ∧
      latticeSize q r < latticeSize p q := by
  let a : ℤ := (R.digits n : ℕ)
  let r : ℤ := p-a*q
  change (q ≠ 0 ∨ r ≠ 0) ∧ _ ∧ _
  have ha : 1 ≤ a := by
    have ht := (R.digits n).pos
    dsimp [a]
    omega
  have haα : (a : ℝ) ≤ R.alpha n := by
    have ht := Int.floor_le (R.alpha n)
    rw [← R.digit_floor n] at ht
    exact_mod_cast ht
  have hβ : 0 < R.beta n := R.beta_pos n
  have hα : 1 < R.alpha n := R.alpha_gt n
  have hden : 0 < R.alpha n + R.beta n := by linarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hprod : |((p : ℝ) - R.alpha n*q) * ((p : ℝ) + R.beta n*q)| < 1 := by
    have ht := lt_of_lt_of_le hv (orbit_infimum_le R n)
    rw [reduced_factor, abs_div, abs_of_pos hden] at ht
    exact (div_lt_div_iff_of_pos_right hden).mp ht
  have hr : 0 ≤ r := by
    by_contra hbad
    have hz : 1 ≤ a*q-p := by dsimp [r] at hbad; omega
    have hzR : (1 : ℝ) ≤ (a : ℝ)*q-p := by exact_mod_cast hz
    have hfirst : 1 ≤ R.alpha n*(q : ℝ)-(p : ℝ) := by
      have ht := mul_le_mul_of_nonneg_right haα (le_of_lt hqR)
      linarith
    have hsecond : 1 < (p : ℝ)+R.beta n*q := by
      have ht := mul_pos hβ hqR
      linarith
    have hfactor : |((p : ℝ) - R.alpha n*q) * ((p : ℝ) + R.beta n*q)| =
        (R.alpha n*q-(p : ℝ))*((p : ℝ)+R.beta n*q) := by
      rw [abs_mul, abs_of_nonpos (by linarith), abs_of_pos (by linarith)]
      ring
    rw [hfactor] at hprod
    have ht := mul_le_mul_of_nonneg_right hfirst (le_of_lt (lt_trans (by norm_num) hsecond))
    nlinarith
  refine ⟨Or.inl (ne_of_gt hq), ?_, ?_⟩
  · have ht := congrArg abs (form_step_identity R n q r)
    have he : ((R.digits n : ℕ) : ℤ)*q+r=p := by dsimp [a,r]; ring
    rw [he, abs_neg] at ht
    exact ht.symm
  · have hsize : (latticeSize q r : ℤ) < latticeSize p q := by
      simp only [latticeSize, Nat.cast_add, Int.natCast_natAbs,
        abs_of_nonneg (le_of_lt hp), abs_of_nonneg (le_of_lt hq), abs_of_nonneg hr]
      dsimp [r]
      have ht := mul_le_mul_of_nonneg_right ha (le_of_lt hq)
      nlinarith
    exact_mod_cast hsize
