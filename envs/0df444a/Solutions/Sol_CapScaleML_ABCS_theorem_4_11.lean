-- Prove2me | solution 1 for CapScaleML.ABCS.theorem_4_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T19:01:26.794407+00:00
-- url     : https://prove2.me/submissions/5c5fa79a-4f75-4ce2-ae4b-deb3ffec391e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CapScaleML_ABCS_Defs
import Theorems.Thm_CapScaleML_ABCS_theorem_4_7
import Theorems.Thm_CapScaleML_ABCS_proposition_6_1
import Theorems.Thm_CapScaleML_ABCS_proposition_6_3

open MeasureTheory Set
open scoped ENNReal

namespace CapScaleML.ABCS.Thm411Aux

/-- The underprediction process is nonnegative everywhere. -/
lemma deltaLam_nonneg (lam lamHat : ℝ → ℝ) (t : ℝ) : 0 ≤ deltaLam lam lamHat t := by
  unfold deltaLam; split_ifs <;> simp

/-- The underprediction process is interval integrable on `[-τ, T]`. -/
lemma deltaLam_ii (T τ : ℝ) (hT : 0 ≤ T) (hτ : 0 ≤ τ) (lam lamHat : ℝ → ℝ)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (hlamHatI : IntervalIntegrable lamHat volume 0 T) :
    IntervalIntegrable (deltaLam lam lamHat) volume (-τ) T := by
  have h1 : IntervalIntegrable (deltaLam lam lamHat) volume (-τ) 0 := by
    have h0 : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume (-τ) 0 :=
      intervalIntegrable_const
    refine h0.congr_uIoo ?_
    intro x hx
    rw [uIoo_of_le (by linarith)] at hx
    simp [deltaLam, not_le.mpr hx.2]
  have h2 : IntervalIntegrable (deltaLam lam lamHat) volume 0 T := by
    have hsub := hlamI.sub hlamHatI
    have hmax : IntervalIntegrable (fun s => max (lam s - lamHat s) 0) volume 0 T := by
      have := hsub.abs
      have h' : IntervalIntegrable (fun s => (|lam s - lamHat s| + (lam s - lamHat s)) / 2)
          volume 0 T := (this.add hsub).div_const 2
      refine h'.congr (fun x _ => ?_)
      rcases le_total 0 (lam x - lamHat x) with h | h
      · rw [abs_of_nonneg h, max_eq_left h]; ring
      · rw [abs_of_nonpos h, max_eq_right h]; ring
    refine hmax.congr (fun x hx => ?_)
    rw [uIoc_of_le hT] at hx
    simp [deltaLam, le_of_lt hx.1]
  exact h1.trans h2

/-- Value of AP's online correction: a sliding-window integral. -/
lemma apOnline_eq (ω β T : ℝ) (lam lamHat : ℝ → ℝ) (hT : 0 ≤ T)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (hlamHatI : IntervalIntegrable lamHat volume 0 T) (t : ℝ) (ht : t ∈ Icc 0 T) :
    apOnline ω β lam lamHat t = Real.sqrt (ω / (2 * β)) *
      ∫ s in (t - Real.sqrt (2 * β / ω))..t, deltaLam lam lamHat s := by
  set τ := Real.sqrt (2 * β / ω) with hτdef
  have hτ : 0 ≤ τ := Real.sqrt_nonneg _
  have hD := deltaLam_ii T τ hT hτ lam lamHat hlamI hlamHatI
  have sub : ∀ a b, a ∈ Icc (-τ) T → b ∈ Icc (-τ) T → IntervalIntegrable (deltaLam lam lamHat) volume a b := by
    intro a b ha hb
    refine hD.mono_set ?_
    rw [uIcc_of_le (by linarith : -τ ≤ T)]
    intro x hx
    rcases mem_uIcc.mp hx with h | h
    · exact ⟨by linarith [ha.1, h.1], by linarith [hb.2, h.2]⟩
    · exact ⟨by linarith [hb.1, h.1], by linarith [ha.2, h.2]⟩
  have i1 : IntervalIntegrable (deltaLam lam lamHat) volume 0 t := sub 0 t ⟨by linarith, hT⟩ ⟨by linarith [ht.1], ht.2⟩
  have i2 : IntervalIntegrable (fun s => (deltaLam lam lamHat) (s - τ)) volume 0 t := by
    have := sub (0 - τ) (t - τ) ⟨by linarith, by linarith⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa using this.comp_sub_right τ
  unfold apOnline
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_comp_sub_right]
  congr 1
  have z : ∫ s in (0 - τ)..0, (deltaLam lam lamHat) s = 0 := by
    rw [intervalIntegral.integral_congr_uIoo (g := fun _ => (0:ℝ))]
    · simp
    · intro x hx
      rw [uIoo_of_le (by linarith)] at hx
      simp [deltaLam, not_le.mpr hx.2]
  have a1 : ∫ s in (0 - τ)..(t - τ), (deltaLam lam lamHat) s = (∫ s in (0 - τ)..0, (deltaLam lam lamHat) s) + ∫ s in (0:ℝ)..(t - τ), (deltaLam lam lamHat) s :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sub (0 - τ) 0 ⟨by linarith, by linarith⟩ ⟨by linarith, hT⟩)
      (sub 0 (t - τ) ⟨by linarith, hT⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩)).symm
  have a2 : ∫ s in (0:ℝ)..t, (deltaLam lam lamHat) s = (∫ s in (0:ℝ)..(t - τ), (deltaLam lam lamHat) s) + ∫ s in (t - τ)..t, (deltaLam lam lamHat) s :=
    (intervalIntegral.integral_add_adjacent_intervals
      (sub 0 (t - τ) ⟨by linarith, hT⟩ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (sub (t - τ) t ⟨by linarith [ht.1], by linarith [ht.2]⟩ ⟨by linarith [ht.1], ht.2⟩)).symm
  rw [a1, a2, z]; ring

lemma apOnline_nonneg (ω β T : ℝ) (lam lamHat : ℝ → ℝ) (hT : 0 ≤ T)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (hlamHatI : IntervalIntegrable lamHat volume 0 T) (t : ℝ) (ht : t ∈ Icc 0 T) :
    0 ≤ apOnline ω β lam lamHat t := by
  rw [apOnline_eq ω β T lam lamHat hT hlamI hlamHatI t ht]
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply intervalIntegral.integral_nonneg
  · linarith [Real.sqrt_nonneg (2 * β / ω)]
  · intro s _; exact deltaLam_nonneg _ _ _

/-- AP's advice is a feasible schedule. -/
lemma apAdvice_admissible (ω β θ T : ℝ) (hT : 0 < T) (lam lamHat mAdv : ℝ → ℝ)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (hlamHatI : IntervalIntegrable lamHat volume 0 T)
    (hAP : IsAPAdvice ω β θ T lam lamHat mAdv) : Admissible T mAdv := by
  obtain ⟨m₁, q₁, ⟨⟨hm0, hmpos, hmint⟩, _, _⟩, heq⟩ := hAP
  have hT' : 0 ≤ T := hT.le
  refine ⟨?_, ?_, ?_⟩
  · rw [heq 0 ⟨le_rfl, hT'⟩, hm0]; simp [apOnline]
  · intro t ht
    have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    rw [heq t ht']
    exact add_nonneg (hmpos t ht) (apOnline_nonneg ω β T lam lamHat hT' hlamI hlamHatI t ht')
  · -- integrability: m₁ plus a continuous primitive
    set τ := Real.sqrt (2 * β / ω)
    have hτ : 0 ≤ τ := Real.sqrt_nonneg _
    have hD := deltaLam_ii T τ hT' hτ lam lamHat hlamI hlamHatI
    have hD0 : IntervalIntegrable (deltaLam lam lamHat) volume 0 T :=
      hD.mono_set (by
        rw [uIcc_of_le hT', uIcc_of_le (by linarith)]
        exact Icc_subset_Icc (by linarith) le_rfl)
    have hDs : IntervalIntegrable (fun s => deltaLam lam lamHat (s - τ)) volume 0 T := by
      have := hD.mono_set (c := 0 - τ) (d := T - τ) (by
        rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
        exact Icc_subset_Icc (by linarith) (by linarith))
      simpa using this.comp_sub_right τ
    have hG : IntervalIntegrable (fun s => Real.sqrt (ω / (2 * β)) *
        (deltaLam lam lamHat s - deltaLam lam lamHat (s - τ))) volume 0 T :=
      (hD0.sub hDs).const_mul _
    have hcont : ContinuousOn (apOnline ω β lam lamHat) (uIcc 0 T) := by
      have hI : IntegrableOn (fun s => Real.sqrt (ω / (2 * β)) *
          (deltaLam lam lamHat s - deltaLam lam lamHat (s - τ))) (uIcc 0 T) volume := by
        rw [uIcc_of_le hT']; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT').mp hG
      exact intervalIntegral.continuousOn_primitive_interval hI
    have hsum : IntervalIntegrable (fun t => m₁ t + apOnline ω β lam lamHat t) volume 0 T :=
      hmint.add (hcont.intervalIntegrable)
    refine hsum.congr (fun x hx => ?_)
    rw [uIoc_of_le hT'] at hx
    exact (heq x ⟨hx.1.le, hx.2⟩).symm

end CapScaleML.ABCS.Thm411Aux

open CapScaleML.ABCS in
theorem solution (ω β θ T r₁ r₂ R₁ R₂ η : ℝ)
    (hω : 0 < ω) (hβ : 0 < β) (hθ : 0 ≤ θ) (hT : 0 < T)
    (hr₁ : 0 < r₁) (hR₁ : r₁ ≤ R₁) (hr₂ : 0 < r₂) (hR₂ : r₂ ≤ R₂)
    (hη : 0 < η) (lam lamHat : ℝ → ℝ)
    (hlam : ∀ t ∈ Icc 0 T, 0 ≤ lam t)
    (hlamHat : ∀ t ∈ Icc 0 T, 0 ≤ lamHat t)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (hlamHatI : IntervalIntegrable lamHat volume 0 T)
    (hacc : IsEtaAccurate ω β θ T η lam lamHat)
    (mAdv qAdv : ℝ → ℝ) (hAP : IsAPAdvice ω β θ T lam lamHat mAdv)
    (hqAdv : IsWorkload T lam mAdv qAdv) (m q : ℝ → ℝ)
    (hm : IsABCS ω β θ T r₁ r₂ R₁ R₂ lam mAdv qAdv m q) :
    cost ω β θ T m q ≤
      min (ENNReal.ofReal ((1 + (Real.sqrt (2 * ω * β) + θ) * η) *
            OCR r₁ r₂ R₁ R₂) * opt ω β θ T lam)
          (ENNReal.ofReal (PCR r₁ r₂ R₁ R₂) * opt ω β θ T lam) := by
  have hAdv : Admissible T mAdv :=
    Thm411Aux.apAdvice_admissible ω β θ T hT lam lamHat mAdv hlamI hlamHatI hAP
  refine le_min ?_ ?_
  · have h63 := proposition_6_3 ω β θ T r₁ r₂ R₁ R₂ hω hβ hθ hT hr₁ hR₁ hr₂ hR₂ lam hlam hlamI
      mAdv qAdv hAdv hqAdv m q hm
    have h47 := (theorem_4_7 ω β θ T hω hβ hθ hT lam lamHat hlam hlamHat hlamI hlamHatI
      mAdv qAdv hAP hqAdv).2 η hη hacc
    have hpos : 0 ≤ 1 + (Real.sqrt (2 * ω * β) + θ) * η := by
      have := Real.sqrt_nonneg (2 * ω * β); positivity
    calc cost ω β θ T m q ≤ ENNReal.ofReal (OCR r₁ r₂ R₁ R₂) * cost ω β θ T mAdv qAdv := h63
      _ ≤ ENNReal.ofReal (OCR r₁ r₂ R₁ R₂) *
          (ENNReal.ofReal (1 + (Real.sqrt (2 * ω * β) + θ) * η) * opt ω β θ T lam) := by
          gcongr
      _ = _ := by rw [ENNReal.ofReal_mul hpos]; ring
  · exact proposition_6_1 ω β θ T r₁ r₂ R₁ R₂ hω hβ hθ hT hr₁ hR₁ hr₂ hR₂ lam hlam hlamI
      mAdv qAdv hAdv hqAdv m q hm
