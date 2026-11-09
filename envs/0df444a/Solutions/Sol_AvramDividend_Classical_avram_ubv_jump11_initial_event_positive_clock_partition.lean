-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump11_initial_event_positive_clock_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:46:51.890884+00:00
-- url     : https://prove2.me/submissions/e8276aa6-6c43-4220-a385-0ee8d084a88d

import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Z : Set Ω) (hZ : MeasurableSet[m] Z)
    (f : Ω → ℝ) (hf : Integrable f P) (c : ℝ)
    (hZero : ∀ ω ∈ Z, f ω ≤ c)
    (hPositive : ∀ A : Set Ω, MeasurableSet[m] A →
      (∫ ω in A ∩ Zᶜ, f ω ∂P) ≤ c * (P (A ∩ Zᶜ)).toReal) :
    ∀ A : Set Ω, MeasurableSet[m] A →
      (∫ ω in A, f ω ∂P) ≤ c * (P A).toReal := by
  classical
  intro A hA
  have hAm : MeasurableSet[mΩ] A := hm A hA
  have hZm : MeasurableSet[mΩ] Z := hm Z hZ
  have hAZ : MeasurableSet[mΩ] (A ∩ Z) := hAm.inter hZm
  have hAN : MeasurableSet[mΩ] (A ∩ Zᶜ) := hAm.inter hZm.compl
  have hdisj : Disjoint (A ∩ Z) (A ∩ Zᶜ) := by
    apply Set.disjoint_left.mpr
    intro ω hω hω'
    exact hω'.2 hω.2
  have hUnion : A = (A ∩ Z) ∪ (A ∩ Zᶜ) := by
    ext ω
    by_cases hz : ω ∈ Z <;> simp [hz]
  have hSplit (g : Ω → ℝ) (hg : Integrable g P) :
      (∫ ω in A, g ω ∂P) =
        (∫ ω in A ∩ Z, g ω ∂P) +
        (∫ ω in A ∩ Zᶜ, g ω ∂P) := by
    calc
      (∫ ω in A, g ω ∂P) =
          (∫ ω in (A ∩ Z) ∪ (A ∩ Zᶜ), g ω ∂P) := by
            rw [← hUnion]
      _ = (∫ ω in A ∩ Z, g ω ∂P) +
          (∫ ω in A ∩ Zᶜ, g ω ∂P) :=
        setIntegral_union hdisj hAN hg.integrableOn hg.integrableOn
  have hZeroAe : ∀ᵐ ω ∂P.restrict (A ∩ Z), f ω ≤ c := by
    filter_upwards [ae_restrict_mem hAZ] with ω hω
    exact hZero ω hω.2
  have hZeroBound :
      (∫ ω in A ∩ Z, f ω ∂P) ≤
      (∫ ω in A ∩ Z, c ∂P) :=
    setIntegral_mono_ae_restrict hf.integrableOn
      (integrable_const c).integrableOn hZeroAe
  have hPosBound :
      (∫ ω in A ∩ Zᶜ, f ω ∂P) ≤
      (∫ ω in A ∩ Zᶜ, c ∂P) := by
    simpa [integral_const, Measure.real, smul_eq_mul, mul_comm] using
      hPositive A hA
  calc
    (∫ ω in A, f ω ∂P) =
        (∫ ω in A ∩ Z, f ω ∂P) +
        (∫ ω in A ∩ Zᶜ, f ω ∂P) := hSplit f hf
    _ ≤ (∫ ω in A ∩ Z, c ∂P) +
        (∫ ω in A ∩ Zᶜ, c ∂P) := add_le_add hZeroBound hPosBound
    _ = (∫ ω in A, c ∂P) :=
        (hSplit (fun _ => c) (integrable_const c)).symm
    _ = c * (P A).toReal := by
        simp [integral_const, Measure.real, smul_eq_mul, mul_comm]
