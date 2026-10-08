-- Prove2me | solution 1 for CosmoConstCentury.friedman_first_integral
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:02:43.42078+00:00
-- url     : https://prove2.me/submissions/6637b7f4-eade-4997-bf05-b76918cbecea

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

/-- The Friedmann energy function `g = R R'^2/c^2 + R - Λ R^3/(3c^2)`. -/
noncomputable def fq22a (c Λ : ℝ) (R : ℝ → ℝ) (t : ℝ) : ℝ :=
  R t * deriv R t ^ 2 / c ^ 2 + R t - Λ * R t ^ 3 / (3 * c ^ 2)

lemma fq22a_hasDerivAt_zero (G c Λ : ℝ) (hc : 0 < c) (I : Set ℝ)
    (R ρ : ℝ → ℝ) (hsol : IsFriedmannSolution G c Λ 1 I R ρ) (t : ℝ) (ht : t ∈ I) :
    HasDerivAt (fq22a c Λ R) 0 t := by
  obtain ⟨hR, hC, _, h16⟩ := hsol t ht
  have hd1 : DifferentiableAt ℝ R t := hC.differentiableAt (by norm_num)
  have hC1 : ContDiffAt ℝ 1 (deriv R) t := hC.derivWithin (by norm_num)
  have hd2 : DifferentiableAt ℝ (deriv R) t := hC1.differentiableAt (by norm_num)
  have h1 := hd1.hasDerivAt
  have h2 := hd2.hasDerivAt
  have hg := ((h1.mul (h2.pow 2)).div_const (c ^ 2)).add h1 |>.sub
    (((h1.pow 3).const_mul Λ).div_const (3 * c ^ 2))
  have hc2 : c ≠ 0 := hc.ne'
  have hR0 : R t ≠ 0 := hR.ne'
  have key2 : deriv R t ^ 2 / c ^ 2 + 2 * deriv (deriv R) t * R t / c ^ 2 + 1
      - Λ * R t ^ 2 / c ^ 2
      = (R t ^ 2 / c ^ 2) * (deriv R t ^ 2 / R t ^ 2 + 2 * deriv (deriv R) t / R t
          + 1 * c ^ 2 / R t ^ 2 - Λ) := by
    field_simp <;> ring
  rw [h16, mul_zero] at key2
  have hfun : fq22a c Λ R = ((fun x => (R * deriv R ^ 2) x / c ^ 2) + R
      - fun x => Λ * (R ^ 3) x / (3 * c ^ 2)) := by
    funext s
    simp only [fq22a, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  rw [hfun]
  refine hg.congr_deriv ?_
  simp only [Pi.pow_apply, Nat.reduceSub, Nat.cast_ofNat]
  linear_combination (deriv R t) * key2

lemma fq22a_eq (G c Λ : ℝ) (hc : 0 < c) (I : Set ℝ)
    (R ρ : ℝ → ℝ) (hsol : IsFriedmannSolution G c Λ 1 I R ρ) (t : ℝ) (ht : t ∈ I) :
    einsteinKappa G c * ρ t * R t ^ 3 / 3 = fq22a c Λ R t := by
  obtain ⟨hR, _, h15, _⟩ := hsol t ht
  have hc2 : c ≠ 0 := hc.ne'
  have hR0 : R t ≠ 0 := hR.ne'
  have hk : einsteinKappa G c * ρ t
      = (3 * deriv R t ^ 2 / R t ^ 2 + 3 * 1 * c ^ 2 / R t ^ 2 - Λ) / c ^ 2 := by
    rw [h15]; field_simp
  rw [hk]
  simp only [fq22a]
  field_simp <;> ring

lemma fq22a_const (G c Λ : ℝ) (hc : 0 < c) (I : Set ℝ) (hI : IsPreconnected I)
    (R ρ : ℝ → ℝ) (hsol : IsFriedmannSolution G c Λ 1 I R ρ) (x y : ℝ)
    (hx : x ∈ I) (hy : y ∈ I) (hxy : x ≤ y) : fq22a c Λ R y = fq22a c Λ R x := by
  have hsub := hI.Icc_subset hx hy
  refine constant_of_has_deriv_right_zero (f := fq22a c Λ R) (a := x) (b := y)
    (fun z hz => (fq22a_hasDerivAt_zero G c Λ hc I R ρ hsol z
      (hsub hz)).continuousAt.continuousWithinAt)
    (fun z hz => (fq22a_hasDerivAt_zero G c Λ hc I R ρ hsol z
      (hsub (Set.Ico_subset_Icc_self hz))).hasDerivWithinAt) y ⟨hxy, le_rfl⟩

end CosmoConstCentury

open CosmoConstCentury in
theorem solution (G c Λ : ℝ) (hc : 0 < c) (I : Set ℝ) (hI : IsPreconnected I)
    (R ρ : ℝ → ℝ) (hsol : IsFriedmannSolution G c Λ 1 I R ρ) :
    ∃ A : ℝ, ∀ t ∈ I, einsteinKappa G c * ρ t * R t ^ 3 / 3 = A ∧
      (1 / c ^ 2) * deriv R t ^ 2 = (A - R t + Λ * R t ^ 3 / (3 * c ^ 2)) / R t := by
  rcases I.eq_empty_or_nonempty with hE | ⟨t0, ht0⟩
  · exact ⟨0, by simp [hE]⟩
  refine ⟨fq22a c Λ R t0, fun t ht => ?_⟩
  have hgt : fq22a c Λ R t = fq22a c Λ R t0 := by
    rcases le_total t0 t with h | h
    · exact fq22a_const G c Λ hc I hI R ρ hsol t0 t ht0 ht h
    · exact (fq22a_const G c Λ hc I hI R ρ hsol t t0 ht ht0 h).symm
  refine ⟨(fq22a_eq G c Λ hc I R ρ hsol t ht).trans hgt, ?_⟩
  rw [← hgt]
  have hR0 : R t ≠ 0 := (hsol t ht).1.ne'
  have hc2 : c ≠ 0 := hc.ne'
  simp only [fq22a]
  field_simp <;> ring
