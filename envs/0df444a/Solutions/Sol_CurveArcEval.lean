-- Prove2me | solution 1 for CurveArcEval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:45.703811+00:00
-- url     : https://prove2.me/submissions/13f0523e-2900-4ee0-ba4d-0cd54b69cabd

import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_CurveArcEval

set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (hcl : IsClosedCurve γ)
    (t t' : ℝ) (ht0 : 0 ≤ t) (htl : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'l : t' ≤ γ.len) :
    (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len
        = (if t ≤ t' then t' - t else (γ.len - t) + t') ∧
      ∃ σ : ℝ → ℝ,
        σ 0 = t ∧
        γ.toFun (σ (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len) = γ.toFun t' ∧
        (∀ p ∈ Set.Icc (0 : ℝ) (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len,
          σ p ∈ Set.Icc (0 : ℝ) γ.len ∧
            (curveArc γ hcl t t' ht0 htl ht'0 ht'l).toFun p = γ.toFun (σ p)) ∧
        (∀ p ∈ Set.Icc (0 : ℝ) (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len,
          ∀ p' ∈ Set.Icc (0 : ℝ) (curveArc γ hcl t t' ht0 htl ht'0 ht'l).len, p ≤ p' →
            (if σ p ≤ σ p' then σ p' - σ p else (γ.len - σ p) + σ p') = p' - p) := by
-- BODY
  have hcl' : γ.toFun γ.len = γ.toFun 0 := hcl
  by_cases h : t ≤ t'
  · -- Ordinary case: the arc is the plain restriction `γ|_{[t,t']}`.
    have hA : curveArc γ hcl t t' ht0 htl ht'0 ht'l = curveRestrict γ t t' ht0 h ht'l := by
      unfold curveArc; exact dif_pos h
    rw [hA]
    have hRlen : (curveRestrict γ t t' ht0 h ht'l).len = t' - t := rfl
    have hRfun : ∀ p : ℝ, (curveRestrict γ t t' ht0 h ht'l).toFun p
        = γ.toFun (t + min (t' - t) (max 0 p)) := fun _ => rfl
    refine ⟨by rw [hRlen, if_pos h], fun p => t + p, by ring, ?_, ?_, ?_⟩
    · rw [hRlen]
      show γ.toFun (t + (t' - t)) = γ.toFun t'
      congr 1; ring
    · intro p hp
      obtain ⟨hp0, hp1⟩ := hp
      rw [hRlen] at hp1
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      rw [hRfun p, max_eq_right hp0, min_eq_right hp1]
    · intro p _ p' _ hpp
      rw [if_pos (by linarith : t + p ≤ t + p')]
      ring
  · -- Wrap case: the arc is `γ|_{[t,γ.len]}` followed by `γ|_{[0,t']}`.
    have hlt : t' < t := not_le.mp h
    have hA : curveArc γ hcl t t' ht0 htl ht'0 ht'l
        = curveWrapRestrict γ t t' hcl ht0 htl ht'0 hlt := by
      unfold curveArc; exact dif_neg h
    rw [hA]
    have hR0 : (0 : ℝ) ≤ γ.len - t := by linarith
    have hWlen : (curveWrapRestrict γ t t' hcl ht0 htl ht'0 hlt).len = (γ.len - t) + t' := by
      show (γ.len - t) + (t' - 0) = (γ.len - t) + t'
      ring
    have hWfun : ∀ p : ℝ, (curveWrapRestrict γ t t' hcl ht0 htl ht'0 hlt).toFun p
        = if p ≤ γ.len - t then γ.toFun (t + min (γ.len - t) (max 0 p))
          else γ.toFun (0 + min (t' - 0) (max 0 (p - (γ.len - t)))) := fun _ => rfl
    refine ⟨by rw [hWlen, if_neg h],
      fun p => if p ≤ γ.len - t then t + p else p - (γ.len - t), ?_, ?_, ?_, ?_⟩
    · show (if (0 : ℝ) ≤ γ.len - t then t + (0 : ℝ) else (0 : ℝ) - (γ.len - t)) = t
      rw [if_pos hR0]; ring
    · rw [hWlen]
      rcases eq_or_lt_of_le ht'0 with he | hpos
      · -- `t' = 0`: the arc ends at parameter `γ.len`, and closedness identifies it with `γ(0)`.
        show γ.toFun (if (γ.len - t) + t' ≤ γ.len - t then t + ((γ.len - t) + t')
          else ((γ.len - t) + t') - (γ.len - t)) = γ.toFun t'
        rw [if_pos (by linarith)]
        have hgl : t + ((γ.len - t) + t') = γ.len := by linarith
        rw [hgl, hcl']
        exact congr_arg γ.toFun he
      · show γ.toFun (if (γ.len - t) + t' ≤ γ.len - t then t + ((γ.len - t) + t')
          else ((γ.len - t) + t') - (γ.len - t)) = γ.toFun t'
        rw [if_neg (by linarith)]
        congr 1; ring
    · intro p hp
      obtain ⟨hp0, hp1⟩ := hp
      rw [hWlen] at hp1
      by_cases hpR : p ≤ γ.len - t
      · refine ⟨?_, ?_⟩
        · show (if p ≤ γ.len - t then t + p else p - (γ.len - t)) ∈ Set.Icc (0 : ℝ) γ.len
          rw [if_pos hpR]
          exact ⟨by linarith, by linarith⟩
        · rw [hWfun p]
          simp only [if_pos hpR]
          rw [max_eq_right hp0, min_eq_right hpR]
      · have hpR' : γ.len - t < p := not_le.mp hpR
        refine ⟨?_, ?_⟩
        · show (if p ≤ γ.len - t then t + p else p - (γ.len - t)) ∈ Set.Icc (0 : ℝ) γ.len
          rw [if_neg hpR]
          exact ⟨by linarith, by linarith⟩
        · rw [hWfun p]
          simp only [if_neg hpR]
          rw [sub_zero, max_eq_right (by linarith : (0 : ℝ) ≤ p - (γ.len - t)),
            min_eq_right (by linarith : p - (γ.len - t) ≤ t'), zero_add]
    · intro p hp p' hp' hpp
      obtain ⟨hp0, hp1⟩ := hp
      obtain ⟨hp'0, hp'1⟩ := hp'
      rw [hWlen] at hp1 hp'1
      by_cases hpR : p ≤ γ.len - t
      · by_cases hp'R : p' ≤ γ.len - t
        · simp only [if_pos hpR, if_pos hp'R]
          rw [if_pos (by linarith : t + p ≤ t + p')]
          ring
        · simp only [if_pos hpR, if_neg hp'R]
          rw [if_neg (by
            refine not_le.mpr ?_
            linarith : ¬ (t + p ≤ p' - (γ.len - t)))]
          ring
      · have hpR' : γ.len - t < p := not_le.mp hpR
        by_cases hp'R : p' ≤ γ.len - t
        · exact absurd hp'R (by exact not_le.mpr (by linarith))
        · simp only [if_neg hpR, if_neg hp'R]
          rw [if_pos (by linarith : p - (γ.len - t) ≤ p' - (γ.len - t))]
          ring
