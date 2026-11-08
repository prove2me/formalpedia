-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_renewal_cdf_atomless_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:31:09.46547+00:00
-- url     : https://prove2.me/submissions/ab145bce-34c3-4f2a-b445-b4e60285e16e

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter

noncomputable section

theorem solution
    (ν : Measure ℝ)
    (hAtom : ∀ x : ℝ, ν {x} = 0)
    (hFin : ∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤) :
    ContinuousOn (fun x : ℝ => if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0)
      (Ici (0 : ℝ)) := by
  classical
  letI : NullSingletonClass ν := ⟨hAtom⟩
  have hLocal (B : ℝ) (hB : 0 ≤ B) :
      ContinuousOn (fun x : ℝ => (ν (Ioc (0 : ℝ) x)).toReal) (Icc 0 B) := by
    let μ : Measure ℝ := ν.restrict (Ioc 0 B)
    letI : NullSingletonClass μ := by
      dsimp [μ]
      infer_instance
    have hμfinite : μ univ < ⊤ := by
      simpa only [μ, Measure.restrict_apply_univ] using hFin B hB
    letI : IsFiniteMeasure μ := ⟨hμfinite⟩
    have hInt : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iio B) μ :=
      (integrable_const (1 : ℝ)).integrableOn
    have hCont :
        ContinuousOn (fun x : ℝ => ∫ y in Iio x, (1 : ℝ) ∂μ) (Iic B) :=
      hInt.continuousOn_Iic_primitive_Iio
    have hEq (x : ℝ) (hx : x ∈ Icc (0 : ℝ) B) :
        (ν (Ioc (0 : ℝ) x)).toReal =
          ∫ y in Iio x, (1 : ℝ) ∂μ := by
      have hsets : Ioc (0 : ℝ) B ∩ Iio x = Ioo 0 x := by
        ext y
        simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
        constructor
        · intro h
          exact ⟨h.1.1, h.2⟩
        · intro h
          exact ⟨⟨h.1, le_trans (le_of_lt h.2) hx.2⟩, h.2⟩
      have hmeasure : μ (Iio x) = ν (Ioc (0 : ℝ) x) := by
        rw [Measure.restrict_apply measurableSet_Iio]
        rw [Set.inter_comm (Iio x) (Ioc (0 : ℝ) B), hsets]
        exact (Ioo_ae_eq_Ioc' (hAtom x)).measure_eq
      calc
        (ν (Ioc (0 : ℝ) x)).toReal = (μ (Iio x)).toReal :=
          congrArg ENNReal.toReal hmeasure.symm
        _ = ∫ y in Iio x, (1 : ℝ) ∂μ := by simp [Measure.real_def]
    apply (hCont.mono (by intro x hx; exact hx.2)).congr
    intro x hx
    exact hEq x hx
  intro x hx
  simp only [mem_Ici] at hx
  have hCx :
      ContinuousWithinAt (fun y : ℝ => (ν (Ioc (0 : ℝ) y)).toReal)
        (Ici (0 : ℝ)) x := by
    let B : ℝ := x + 1
    have hB : 0 ≤ B := by dsimp [B]; linarith
    have hlocal := hLocal B hB
    have hmem : x ∈ Icc (0 : ℝ) B := by
      simp only [mem_Icc]
      constructor
      · exact hx
      · dsimp [B]; linarith
    have hnb : Icc (0 : ℝ) B ∈ nhdsWithin x (Ici (0 : ℝ)) := by
      apply mem_nhdsWithin.2
      have hxB : x < B := by
        dsimp [B]
        nlinarith
      refine ⟨Iio B, isOpen_Iio, hxB, ?_⟩
      intro y hy
      exact ⟨hy.2, le_of_lt hy.1⟩
    exact (hlocal.continuousWithinAt hmem).mono_of_mem_nhdsWithin hnb
  have hEq : (fun y : ℝ => if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0) =ᶠ[nhdsWithin x (Ici (0 : ℝ))]
      (fun y : ℝ => (ν (Ioc (0 : ℝ) y)).toReal) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) ≤ y := hy
    simp [hy0]
  apply hCx.congr_of_eventuallyEq hEq
  simp [hx]
