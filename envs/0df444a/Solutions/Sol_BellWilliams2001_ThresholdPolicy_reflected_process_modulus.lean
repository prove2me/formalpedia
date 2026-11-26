-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.reflected_process_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:04:37.4488+00:00
-- url     : https://prove2.me/submissions/1b816d28-ae66-4ef1-9cfe-591de716be95

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

private theorem past_infimum_modulus (x : ℝ → ℝ) {s t e : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (he : 0 ≤ e) (hBs : BddBelow (range (fun u : Icc (0:ℝ) s => x u)))
    (hBt : BddBelow (range (fun u : Icc (0:ℝ) t => x u)))
    (h : ∀ u ∈ Icc s t, |x u-x s| ≤ e) :
    |(⨅ u : Icc (0:ℝ) s, x u)-(⨅ u : Icc (0:ℝ) t, x u)| ≤ e := by
  letI : Nonempty (Icc (0:ℝ) s) := ⟨⟨0,le_rfl,hs⟩⟩
  letI : Nonempty (Icc (0:ℝ) t) := ⟨⟨0,le_rfl,hs.trans hst⟩⟩
  let I := ⨅ u : Icc (0:ℝ) s, x u
  let J := ⨅ u : Icc (0:ℝ) t, x u
  have h1 : J ≤ I :=
    le_ciInf fun u : Icc (0:ℝ) s => ciInf_le hBt ⟨u,u.2.1,u.2.2.trans hst⟩
  have h2 : I-e ≤ J := by
    apply le_ciInf
    intro u
    by_cases hu : (u:ℝ) ≤ s
    · exact (sub_le_self _ he).trans (ciInf_le hBs ⟨u,u.2.1,hu⟩)
    · have hh := (abs_le.1 (h u ⟨(lt_of_not_ge hu).le,u.2.2⟩)).1
      have hI : I ≤ x s := ciInf_le hBs ⟨s,hs,le_rfl⟩
      linarith
  change |I-J| ≤ e
  rw [abs_of_nonneg (sub_nonneg.2 h1)]
  linarith

set_option maxHeartbeats 1450000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ → ℝ)
    (hBd : ∀ᶠ n in atTop, ∀ ω t, 0 ≤ t → BddBelow (range (fun s : Icc (0:ℝ) t => X n ω s)))
    (hM : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ |X n ω s-X n ω t|} ≤ ENNReal.ofReal η)
    (a b : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (hCoe : ∀ᶠ n in atTop, |a n| ≤ C ∧ |b n| ≤ C) :
    let R (x : ℝ → ℝ) (t : ℝ) := x t-⨅ s : Icc (0:ℝ) t, x s
    let V (x : ℝ → ℝ) (t : ℝ) := -(⨅ s : Icc (0:ℝ) t, x s)
    let Y (n : ℕ) (ω : Ω) (t : ℝ) := ![0,a n*R (X n ω) t,0,b n*V (X n ω) t]
    ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖Y n ω s-Y n ω t‖} ≤ ENNReal.ofReal η := by
  intro R V Y T ε η hε hη
  let e := ε/(3*C)
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨δ,hδ,hM⟩ := hM T e η he hη
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hM,hBd,hCoe] with n hn hbb hc
  refine (measure_mono ?_).trans hn
  rintro ω ⟨s,hs,t,ht,hst,hBad⟩
  by_contra hNo
  have hClose (u v : ℝ) (hu : u ∈ Icc (0:ℝ) (T:ℝ)) (hv : v ∈ Icc (0:ℝ) (T:ℝ))
      (huv : |u-v| ≤ δ) : |X n ω u-X n ω v| ≤ e :=
    (lt_of_not_ge (fun hh => hNo ⟨u,hu,v,hv,huv,hh⟩)).le
  have hv (u v : ℝ) (hu : u ∈ Icc (0:ℝ) (T:ℝ)) (hv : v ∈ Icc (0:ℝ) (T:ℝ))
      (huv : u ≤ v) (hc : |u-v| ≤ δ) :
      |(⨅ w : Icc (0:ℝ) u, X n ω w)-(⨅ w : Icc (0:ℝ) v, X n ω w)| ≤ e := by
    refine past_infimum_modulus (X n ω) hu.1 huv he.le (hbb ω u hu.1) (hbb ω v hv.1) ?_
    intro w hw
    apply hClose w u ⟨hu.1.trans hw.1,hw.2.trans hv.2⟩ hu
    rw [abs_of_nonpos (sub_nonpos.2 huv)] at hc
    rw [abs_of_nonneg (sub_nonneg.2 hw.1)]
    linarith [hw.2]
  have hI : |(⨅ w : Icc (0:ℝ) s, X n ω w)-(⨅ w : Icc (0:ℝ) t, X n ω w)| ≤ e := by
    rcases le_total s t with h | h
    · exact hv s t hs ht h hst
    · rw [abs_sub_comm]
      exact hv t s ht hs h (by rwa [abs_sub_comm])
  have hR : |R (X n ω) s-R (X n ω) t| ≤ 2*e := by
    dsimp only [R]
    rw [show X n ω s-(⨅ w : Icc (0:ℝ) s,X n ω w)-(X n ω t-(⨅ w : Icc (0:ℝ) t,X n ω w)) =
      X n ω s-X n ω t-((⨅ w : Icc (0:ℝ) s,X n ω w)-(⨅ w : Icc (0:ℝ) t,X n ω w)) by ring]
    exact (abs_sub _ _).trans (by linarith [hClose s t hs ht hst])
  have hV : |V (X n ω) s-V (X n ω) t| ≤ e := by
    simpa only [V,neg_sub_neg,abs_sub_comm] using hI
  have hNorm : ‖Y n ω s-Y n ω t‖ ≤ 2*C*e := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    fin_cases i
    · simp [Y]
      positivity
    · change |a n*R (X n ω) s-a n*R (X n ω) t| ≤ 2*C*e
      rw [←mul_sub,abs_mul]
      have h := mul_le_mul hc.1 hR (abs_nonneg _) hC.le
      linarith only [h]
    · simp [Y]
      positivity
    · change |b n*V (X n ω) s-b n*V (X n ω) t| ≤ 2*C*e
      rw [←mul_sub,abs_mul]
      have h := mul_le_mul hc.2 hV (abs_nonneg _) hC.le
      linarith [mul_nonneg hC.le he.le]
  have hEq : 2*C*e = 2*ε/3 := by dsimp [e]; field_simp
  linarith
