-- Prove2me | solution 1 for EulerMascheroni.Mixed.differential_independence_criterion
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:05:18.750413+00:00
-- url     : https://prove2.me/submissions/b3f641af-0f4a-4b78-914f-2936a578d653

import Mathlib
set_option autoImplicit false
namespace EulerDifferential
lemma residue_derivative_zero (f : LaurentSeries ℂ) :
    (LaurentSeries.derivative ℂ f).coeff (-1) = 0 := by
  simp [LaurentSeries.derivative]
lemma no_logarithmic_primitive (f : LaurentSeries ℂ) :
    LaurentSeries.derivative ℂ f ≠ HahnSeries.single (-1) (1:ℂ) := by
  intro h
  have hh := congrArg (fun g : LaurentSeries ℂ => g.coeff (-1)) h
  simpa [residue_derivative_zero] using hh
lemma independence {K F : Type*} [Field K] [Field F] [Algebra ℚ K] [Algebra ℚ F]
    [Algebra K F] [IsScalarTower ℚ K F]
    (d : Derivation ℚ K K) (D : Derivation ℚ F F)
    (hD : ∀ r : K, D (algebraMap K F r) = algebraMap K F (d r))
    (z : K) (hz : z ≠ 0) (e y : F)
    (he : D e = e) (hy : D y = y+(e-1)/algebraMap K F z)
    (hexp : ∀ p q : K, algebraMap K F p+algebraMap K F q*e=0 → p=0 ∧ q=0)
    (hlog : ∀ u : K, d u ≠ z⁻¹)
    (a b c : K) (hrel : algebraMap K F a+algebraMap K F b*e+algebraMap K F c*y=0) :
    a=0 ∧ b=0 ∧ c=0 := by
  by_cases hc : c=0
  · simp only [hc,map_zero,zero_mul,add_zero] at hrel
    exact ⟨(hexp a b hrel).1,(hexp a b hrel).2,hc⟩
  · let u : K := -b/c
    let v : K := -a/c
    have hcF : algebraMap K F c ≠ 0 := (map_ne_zero (algebraMap K F)).mpr hc
    have hzF : algebraMap K F z ≠ 0 := (map_ne_zero (algebraMap K F)).mpr hz
    have hform : y=algebraMap K F v+algebraMap K F u*e := by
      dsimp [u,v]
      push_cast
      field_simp
      linear_combination hrel
    have hd := congrArg D hform
    simp only [map_add, D.leibniz, hD, he, smul_eq_mul, hy] at hd
    have hlin : algebraMap K F (d v-v+z⁻¹)+
        algebraMap K F (d u-z⁻¹)*e=0 := by
      push_cast
      rw [hform] at hd
      field_simp at hd ⊢
      linear_combination -hd
    have hu := (hexp _ _ hlin).2
    exact False.elim (hlog u (sub_eq_zero.mp hu))
end EulerDifferential


theorem solution {K F : Type*} [Field K] [Field F] [Algebra ℚ K] [Algebra ℚ F]
    [Algebra K F] [IsScalarTower ℚ K F]
    (d : Derivation ℚ K K) (D : Derivation ℚ F F)
    (hD : ∀ r : K, D (algebraMap K F r) = algebraMap K F (d r))
    (z : K) (hz : z ≠ 0) (e y : F)
    (he : D e = e) (hy : D y = y+(e-1)/algebraMap K F z)
    (hexp : ∀ p q : K, algebraMap K F p+algebraMap K F q*e=0 → p=0 ∧ q=0)
    (hlog : ∀ u : K, d u ≠ z⁻¹)
    (a b c : K) (hrel : algebraMap K F a+algebraMap K F b*e+algebraMap K F c*y=0) :
    a=0 ∧ b=0 ∧ c=0 := by
  exact EulerDifferential.independence d D hD z hz e y he hy hexp hlog a b c hrel

#print axioms solution
