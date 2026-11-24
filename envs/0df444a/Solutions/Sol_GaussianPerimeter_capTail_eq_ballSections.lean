-- Prove2me | solution 1 for GaussianPerimeter.capTail_eq_ballSections
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:57.492659+00:00
-- url     : https://prove2.me/submissions/d5e368da-f551-419a-bbdb-d04f2b5ad39d

module
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Theorems.Thm_GaussianPerimeter_capProfile_continuous
public import Theorems.Thm_GaussianPerimeter_capNormalizer_pos
section
@[expose] public section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace GaussianPerimeter
private theorem capProfile_shift {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    capProfile (n + 2) x = (1 - x ^ 2) * capProfile n x := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : 0 ≤ 1 - x ^ 2 := by
    have := sq_le_sq' hx.1 hx.2
    linarith
  unfold capProfile
  rw [show (((n + 2 : ℕ) : ℝ) - 2) / 2 = 1 + ((n : ℝ) - 2) / 2 by push_cast; ring,
    Real.rpow_add_of_nonneg hb zero_le_one (by linarith), Real.rpow_one]
private theorem capProfile_integral_shift {n : ℕ} (hn : 2 ≤ n) {l : ℝ}
    (hl : -1 ≤ l) (hl' : l ≤ 1) :
    (n : ℝ) * (∫ u in l..1, capProfile n u) =
      ((n : ℝ) + 1) * (∫ u in l..1, capProfile (n + 2) u) + l * capProfile (n + 2) l := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcont := capProfile_continuous hn
  have hcont' := capProfile_continuous (show 2 ≤ n + 2 by omega)
  let primitive (u : ℝ) := u * capProfile (n + 2) u
  have hprimitive : Continuous primitive := continuous_id.mul hcont'
  have hderiv (u : ℝ) (hu : u ∈ Ioo l 1) :
      HasDerivAt primitive (((n : ℝ) + 1) * capProfile (n + 2) u - (n : ℝ) * capProfile n u) u := by
    have hu' : u ∈ Icc (-1 : ℝ) 1 := ⟨hl.trans hu.1.le, hu.2.le⟩
    have heq : ∀ x, capProfile (n + 2) x = (1 - x ^ 2) ^ ((n : ℝ) / 2) := by
      intro x
      simp [capProfile, Nat.cast_add]
    have hb := (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_pow 2 u)
    have hd := hb.rpow_const (p := (n : ℝ) / 2) (Or.inr (by linarith))
    have hd' := (hasDerivAt_id u).mul hd
    simp only [primitive, heq]
    convert hd' using 1 <;> try rfl
    have hshift := capProfile_shift hn hu'
    rw [heq] at hshift
    rw [show (n : ℝ) / 2 - 1 = ((n : ℝ) - 2) / 2 by ring]
    simp only [Pi.sub_apply]
    rw [show (1 - u ^ 2) ^ (((n : ℝ) - 2) / 2) = capProfile n u by rfl, hshift]
    simp
    ring
  have hderivcont : Continuous (fun u : ℝ => ((n : ℝ) + 1) * capProfile (n + 2) u -
      (n : ℝ) * capProfile n u) := (hcont'.const_mul _).sub (hcont.const_mul _)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hl' hprimitive.continuousOn
    hderiv (hderivcont.intervalIntegrable _ _)
  have h1 : capProfile (n + 2) 1 = 0 := by
    simp [capProfile, Real.zero_rpow (show (n : ℝ) / 2 ≠ 0 by linarith)]
  rw [intervalIntegral.integral_sub ((hcont'.const_mul _).intervalIntegrable _ _)
      ((hcont.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at h
  simp [primitive, h1] at h
  linarith
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped Interval Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    capTail n t = (t / ((n : ℝ) + 1) * capProfile (n + 2) t +
      (∫ u in t..1, capProfile (n + 2) u)) / capNormalizer (n + 2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hmass := capProfile_integral_shift hn (l := -1) le_rfl (by norm_num)
  have htail := capProfile_integral_shift hn (l := t) (by linarith) ht'
  have h1 : capProfile (n + 2) (-1) = 0 := by
    norm_num [capProfile, Real.zero_rpow (show (n : ℝ) / 2 ≠ 0 by linarith)]
  rw [h1, mul_zero, add_zero, ← capNormalizer, ← capNormalizer] at hmass
  have hN := capNormalizer_pos hn
  have hN' := capNormalizer_pos (show 2 ≤ n + 2 by omega)
  unfold capTail
  field_simp [hN.ne', hN'.ne']
  -- Both sides reduce to the same numerator after the integral shifts.
  apply (mul_left_cancel₀ hn0.ne')
  linear_combination capNormalizer (n + 2) * ((n : ℝ) + 1) * htail -
    (((n : ℝ) + 1) * (∫ u in t..1, capProfile (n + 2) u) +
      t * capProfile (n + 2) t) * hmass
end GaussianPerimeter
