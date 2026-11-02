-- Prove2me | solution 1 for BIInsurance.Screening.proposition_1_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:05:26.300843+00:00
-- url     : https://prove2.me/submissions/c9692104-49bb-4d6d-91cd-46a4d04bb458

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model

open Set

namespace BIInsurance.Screening.P1i

open BIInsurance.Screening

lemma Aeff_lower (P : Params) (hS : P.Standing) (s : ℝ) (hs : s ∈ Icc 0 P.sbar) :
    P.c < Aeff P s := by
  obtain ⟨hτ, hK, hmuL, hmuLH, hdL, hdH, hβ0, hβ1, hβd, hα0, hα1, hγ, hρ0, hρ1, hlam, hp, hc,
    hcT, hw, hsb0, hsb⟩ := hS
  obtain ⟨hs0, hs1⟩ := hs
  have hTp : 0 < ((P.T : ℝ) - P.τ) * P.p := lt_of_lt_of_le hc hcT
  have hE : 0 < Real.exp (-(P.muL + P.dL) / P.γ) := Real.exp_pos _
  have h1 : P.c / (((P.T : ℝ) - P.τ) * P.p) < 1 - P.sbar := by
    have : P.c / (((P.T : ℝ) - P.τ) * P.p) <
        P.c / (((P.T : ℝ) - P.τ) * P.p) * (1 + Real.exp (-(P.muL + P.dL) / P.γ)) := by
      have : 0 < P.c / (((P.T : ℝ) - P.τ) * P.p) := div_pos hc hTp
      nlinarith
    linarith
  have h2 : P.c < (1 - P.sbar) * (((P.T : ℝ) - P.τ) * P.p) := by
    rwa [div_lt_iff₀ hTp] at h1
  have hw0 : (0 : ℝ) ≤ P.w := Nat.cast_nonneg _
  unfold Aeff
  have e1 : (1 - P.sbar) * (((P.T : ℝ) - P.τ) * P.p) ≤ (1 - s) * (((P.T : ℝ) - P.τ) * P.p) :=
    mul_le_mul_of_nonneg_right (by linarith) hTp.le
  have e2 : 0 ≤ (P.w : ℝ) * P.p * s := by positivity
  nlinarith

/-- the unconstrained effort level `(m + γ ln((A(s)-c)/c))/K` -/
noncomputable def fe (P : Params) (m s : ℝ) : ℝ :=
  (m + P.γ * (Real.log (Aeff P s - P.c) - Real.log P.c)) / P.K

lemma eStar_eq (P : Params) (hS : P.Standing) (m s : ℝ) (hs : s ∈ Icc 0 P.sbar) :
    eStar P m s = min (fe P m s) 1 := by
  have hK : 0 < P.K := hS.2.1
  have hc : 0 < P.c := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hA := Aeff_lower P hS s hs
  unfold eStar fe
  rw [Real.log_div (by linarith) hc.ne']
  split_ifs with h
  · rw [min_eq_left]; rw [div_le_one hK]; exact h.le
  · rw [min_eq_right]; rw [one_le_div hK]; linarith

lemma Aeff_affine (P : Params) (a b x y : ℝ) (hab : a + b = 1) :
    Aeff P (a * x + b * y) - P.c = a * (Aeff P x - P.c) + b * (Aeff P y - P.c) := by
  unfold Aeff
  have : b = 1 - a := by linarith
  subst this; ring

lemma fe_concave (P : Params) (hS : P.Standing) (m : ℝ) :
    ConcaveOn ℝ (Icc 0 P.sbar) (fe P m) := by
  have hK : 0 < P.K := hS.2.1
  have hγ : 0 < P.γ := hS.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hAx := Aeff_lower P hS x hx
  have hAy := Aeff_lower P hS y hy
  have hlog := (strictConcaveOn_log_Ioi.concaveOn).2 (show Aeff P x - P.c ∈ Ioi 0 by
    simp; linarith) (show Aeff P y - P.c ∈ Ioi 0 by simp; linarith) ha hb hab
  simp only [smul_eq_mul] at hlog ⊢
  rw [← Aeff_affine P a b x y hab] at hlog
  unfold fe
  have key : a * ((m + P.γ * (Real.log (Aeff P x - P.c) - Real.log P.c)) / P.K)
      + b * ((m + P.γ * (Real.log (Aeff P y - P.c) - Real.log P.c)) / P.K)
      = (m + P.γ * ((a * Real.log (Aeff P x - P.c) + b * Real.log (Aeff P y - P.c))
          - Real.log P.c)) / P.K := by
    have : b = 1 - a := by linarith
    subst this
    field_simp
    ring
  rw [key]
  apply div_le_div_of_nonneg_right _ hK.le
  have := mul_le_mul_of_nonneg_left hlog hγ.le
  linarith

lemma fe_anti (P : Params) (hS : P.Standing) (m : ℝ) :
    AntitoneOn (fe P m) (Icc 0 P.sbar) := by
  have hK : 0 < P.K := hS.2.1
  have hγ : 0 < P.γ := hS.2.2.2.2.2.2.2.2.2.2.2.1
  have hp : 0 < P.p := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw : (P.w : ℝ) < (P.T : ℝ) - P.τ := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro x hx y hy hxy
  have hAy := Aeff_lower P hS y hy
  have hle : Aeff P y - P.c ≤ Aeff P x - P.c := by
    unfold Aeff
    have : 0 ≤ ((P.T : ℝ) - P.τ - P.w) * P.p * (y - x) :=
      mul_nonneg (mul_nonneg (by linarith) hp.le) (by linarith)
    nlinarith
  have hl := Real.log_le_log (by linarith) hle
  unfold fe
  apply div_le_div_of_nonneg_right _ hK.le
  have := mul_le_mul_of_nonneg_left hl hγ.le
  linarith

theorem main (P : Params) (hS : P.Standing) (m : ℝ) :
    AntitoneOn (eStar P m) (Set.Icc 0 P.sbar) ∧
      ConcaveOn ℝ (Set.Icc 0 P.sbar) (eStar P m) ∧
      ∀ s ∈ Set.Icc 0 P.sbar, eStar P m s ≤ eHat P m := by
  have hsb : (0:ℝ) ∈ Icc 0 P.sbar := ⟨le_rfl, hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.le⟩
  have hanti : AntitoneOn (eStar P m) (Set.Icc 0 P.sbar) := by
    intro x hx y hy hxy
    rw [eStar_eq P hS m x hx, eStar_eq P hS m y hy]
    exact min_le_min (fe_anti P hS m hx hy hxy) le_rfl
  refine ⟨hanti, ?_, ?_⟩
  · have hc : ConcaveOn ℝ (Icc 0 P.sbar) (fe P m ⊓ fun _ => (1:ℝ)) :=
      (fe_concave P hS m).inf (concaveOn_const _ (convex_Icc _ _))
    refine hc.congr ?_
    intro s hs
    simp only [Pi.inf_apply]
    rw [eStar_eq P hS m s hs]
  · intro s hs
    have h0 : eStar P m 0 = eHat P m := by
      have hA0 : Aeff P 0 = ((P.T : ℝ) - P.τ) * P.p := by unfold Aeff; ring
      unfold eStar eHat; rw [hA0]
    rw [← h0]
    exact hanti hsb hs hs.1

end BIInsurance.Screening.P1i

open BIInsurance.Screening in
theorem solution (P : Params) (hS : P.Standing) (m : ℝ) (_hm : P.muL + P.dL ≤ m) :
    AntitoneOn (eStar P m) (Set.Icc 0 P.sbar) ∧
      ConcaveOn ℝ (Set.Icc 0 P.sbar) (eStar P m) ∧
      ∀ s ∈ Set.Icc 0 P.sbar, eStar P m s ≤ eHat P m :=
  BIInsurance.Screening.P1i.main P hS m
