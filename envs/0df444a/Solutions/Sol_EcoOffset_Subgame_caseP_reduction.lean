-- Prove2me | solution 1 for EcoOffset.Subgame.caseP_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:24:06.88745+00:00
-- url     : https://prove2.me/submissions/662c6dbc-64c8-46d2-8560-9f93711cab89

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model
import Theorems.Thm_EcoOffset_Subgame_segOpt_spec

namespace EcoCasePAux
open EcoOffset.Subgame

theorem antitone_of_deriv_neg (h : ℝ → ℝ) (hh : ContDiff ℝ 2 h) (ebar : ℝ)
    (hd : ∀ e ∈ Set.Icc 0 ebar, deriv h e < 0) : AntitoneOn h (Set.Icc 0 ebar) := by
  have hdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 ebar) hdiff.continuous.continuousOn
    hdiff.differentiableOn
  intro x hx
  rw [interior_Icc] at hx
  exact (hd x (Set.Ioo_subset_Icc_self hx)).le

/-- `c(e) ≥ c(¯e)` and `f(e) ≥ 0` on `[0, ¯e]`. -/
theorem c_f_bounds (P : Params) (hS : P.Standing) (e : ℝ) (he : e ∈ Set.Icc 0 P.ebar) :
    P.c P.ebar ≤ P.c e ∧ 0 ≤ P.f e := by
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe,
    hder⟩ := hS
  have hebar : P.ebar ∈ Set.Icc 0 P.ebar := ⟨heb.le, le_rfl⟩
  refine ⟨antitone_of_deriv_neg P.c hc2 P.ebar (fun e he => (hder e he).1) he hebar he.2, ?_⟩
  have := antitone_of_deriv_neg P.f hf2 P.ebar (fun e he => (hder e he).2.2.1) he hebar he.2
  linarith

theorem segObj_le (P : Params) (hS : P.Standing) (x a : ℝ) (hx : 0 ≤ x) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (e : ℝ) (he : e ∈ Set.Icc 0 P.ebar) :
    segObj P x a e ≤ segObj P x a (segOpt P x a) :=
  (segOpt_spec P hS x a hx ha0 ha1).1.2 e he

theorem eq_segOpt_of_segObj (P : Params) (hS : P.Standing) (x a : ℝ) (hx : 0 ≤ x)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (e : ℝ) (he : e ∈ Set.Icc 0 P.ebar)
    (heq : segObj P x a (segOpt P x a) ≤ segObj P x a e) : e = segOpt P x a := by
  apply (segOpt_spec P hS x a hx ha0 ha1).2.1
  exact ⟨he, fun e' he' => le_trans (segObj_le P hS x a hx ha0 ha1 e' he') heq⟩

theorem aP_mem (P : Params) (hS : P.Standing) : 0 ≤ aP P ∧ aP P ≤ 1 := by
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, -⟩ := hS
  unfold aP
  constructor <;> nlinarith

/-- The case split of the proof in Case P. -/
theorem caseP_cases (P : Params) (hS : P.Standing) (hβc : P.βc = 1) (g : ℝ)
    (hg0 : 0 < g) (hgξ : g < P.ξ) (p e t : ℝ) (hfeas : Feasible P e t) :
    (0 ≤ P.vl - p ∧ 0 ≤ P.vh - P.ξ * footprint P e t - p ∧
      profit P g p e t = valAllP P g - ((P.vl + g * ((P.vh - P.vl) / P.ξ) - p -
        g * footprint P e t) * P.m + (segObj P g 1 (segOpt P g 1) - segObj P g 1 e))) ∨
    (0 ≤ P.vh - P.ξ * footprint P e t - p ∧
      profit P g p e t = valTwoP P g - ((P.vh - P.ξ * footprint P e t - p) * aP P * P.m +
        (P.ξ - g) * footprint P e t * aP P * P.m +
        (segObj P g (aP P) (segOpt P g (aP P)) - segObj P g (aP P) e))) ∨
    profit P g p e t ≤ valOne P ∨ profit P g p e t ≤ valThree P := by
  have hS' := hS
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe,
    hder⟩ := hS'
  have hF : footprint P e t = e + P.eo - t := rfl
  have hF0 : 0 ≤ footprint P e t := by rw [hF]; linarith [hfeas.2.2]
  have hξF : 0 ≤ P.ξ * footprint P e t := mul_nonneg hξ.le hF0
  have hcf := c_f_bounds P hS e hfeas.1
  have ht : 0 ≤ g * t := mul_nonneg hg0.le hfeas.2.1
  by_cases i1 : 0 ≤ P.vh - P.ξ * footprint P e t - p
  · have i3 : 0 ≤ P.vh - p := by linarith
    by_cases i4 : 0 ≤ P.vl - p
    · left
      refine ⟨i4, i1, ?_⟩
      have hd : demand P p e t = P.m := by
        simp only [demand, demandC, demandU, hβc, if_pos i1, if_pos i3, if_pos i4]
        ring
      rw [profit, hd]
      unfold valAllP segObj
      rw [hF]
      field_simp
      ring
    · right; left
      refine ⟨i1, ?_⟩
      have hd : demand P p e t = aP P * P.m := by
        simp only [demand, demandC, demandU, hβc, if_pos i1, if_pos i3, if_neg i4, aP]
        ring
      rw [profit, hd]
      unfold valTwoP segObj
      rw [hF]
      ring
  · right; right
    by_cases i4 : 0 ≤ P.vl - p
    · right
      have i3 : 0 ≤ P.vh - p := by linarith
      have hd : demand P p e t = (1 - P.α) * P.m := by
        simp only [demand, demandC, demandU, hβc, if_neg i1, if_pos i3, if_pos i4]
        ring
      rw [profit, hd]
      unfold valThree
      have h1 : 0 ≤ (1 - P.α) * P.m := mul_nonneg (by linarith) hm.le
      have : (p - P.c e - g * t) * ((1 - P.α) * P.m) ≤ (P.vl - P.c P.ebar) * ((1 - P.α) * P.m) :=
        mul_le_mul_of_nonneg_right (by linarith) h1
      nlinarith
    · left
      by_cases i3 : 0 ≤ P.vh - p
      · have hd : demand P p e t = (1 - P.α) * P.βu * P.m := by
          simp only [demand, demandC, demandU, hβc, if_neg i1, if_pos i3, if_neg i4]
          ring
        rw [profit, hd]
        unfold valOne
        have h1 : 0 ≤ (1 - P.α) * P.βu * P.m := by
          have : 0 ≤ 1 - P.α := by linarith
          positivity
        have : (p - P.c e - g * t) * ((1 - P.α) * P.βu * P.m) ≤
            (P.vh - P.c P.ebar) * ((1 - P.α) * P.βu * P.m) :=
          mul_le_mul_of_nonneg_right (by linarith) h1
        nlinarith
      · have hd : demand P p e t = 0 := by
          simp only [demand, demandC, demandU, hβc, if_neg i1, if_neg i3, if_neg i4]
          ring
        rw [profit, hd]
        unfold valOne
        have : 0 ≤ (P.vh - P.c P.ebar) * (1 - P.α) * P.βu * P.m := by
          have : 0 ≤ P.vh - P.c P.ebar := by linarith
          have : 0 ≤ 1 - P.α := by linarith
          positivity
        nlinarith

/-- The slack in the first case is nonnegative, and vanishes only at `p = vl`, `ℰ = (vh−vl)/ξ`. -/
theorem slackA (P : Params) (hS : P.Standing) (g : ℝ) (hg0 : 0 < g) (hgξ : g < P.ξ)
    (p F : ℝ) (h4 : 0 ≤ P.vl - p) (h1 : 0 ≤ P.vh - P.ξ * F - p) :
    0 ≤ P.vl + g * ((P.vh - P.vl) / P.ξ) - p - g * F ∧
    (P.vl + g * ((P.vh - P.vl) / P.ξ) - p - g * F = 0 → p = P.vl ∧ F = (P.vh - P.vl) / P.ξ) := by
  have hξ : 0 < P.ξ := hS.2.2.2.1
  set K := (P.vh - P.vl) / P.ξ with hK
  have hξK : P.ξ * K = P.vh - P.vl := by rw [hK]; field_simp
  rcases le_or_gt F K with hFK | hFK
  · have : 0 ≤ g * (K - F) := mul_nonneg hg0.le (by linarith)
    refine ⟨by nlinarith, fun h0 => ?_⟩
    have h5 : g * (K - F) = 0 := by nlinarith
    rcases mul_eq_zero.1 h5 with h | h
    · linarith
    · constructor <;> linarith
  · have : 0 < (P.ξ - g) * (F - K) := mul_pos (by linarith) (by linarith)
    refine ⟨by nlinarith, fun h0 => ?_⟩
    exfalso
    nlinarith

end EcoCasePAux

open EcoOffset.Subgame EcoCasePAux in
theorem solution (P : Params) (hS : P.Standing) (hβc : P.βc = 1)
    (hv : P.vh - P.vl < P.ξ * P.eo) (g : ℝ) (hg0 : 0 < g) (hgξ : g < P.ξ) :
    (∀ p e t, Feasible P e t →
      profit P g p e t ≤ max (max (valOne P) (valThree P)) (max (valTwoP P g) (valAllP P g))) ∧
    (max (max (valOne P) (valThree P)) (valTwoP P g) < valAllP P g →
      ∀ p e t, IsBestResponse P g p e t ↔
        (p = P.vl ∧ e = segOpt P g 1 ∧
          t = segOpt P g 1 + P.eo - (P.vh - P.vl) / P.ξ)) ∧
    (max (max (valOne P) (valThree P)) (valAllP P g) < valTwoP P g →
      ∀ p e t, IsBestResponse P g p e t ↔
        (p = P.vh ∧ e = segOpt P g (aP P) ∧ t = segOpt P g (aP P) + P.eo)) ∧
    (demandC P P.vh (segOpt P g (aP P)) (segOpt P g (aP P) + P.eo) = P.α * P.m ∧
      demandU P P.vh (segOpt P g (aP P)) (segOpt P g (aP P) + P.eo) =
        (1 - P.α) * P.βu * P.m) ∧
    (demandC P P.vl (segOpt P g 1) (segOpt P g 1 + P.eo - (P.vh - P.vl) / P.ξ) = P.α * P.m ∧
      demandU P P.vl (segOpt P g 1) (segOpt P g 1 + P.eo - (P.vh - P.vl) / P.ξ) =
        (1 - P.α) * P.m) := by
  have hS' := hS
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe,
    hder⟩ := hS'
  obtain ⟨haP0, haP1⟩ := aP_mem P hS
  set K := (P.vh - P.vl) / P.ξ with hK
  have hξK : P.ξ * K = P.vh - P.vl := by rw [hK]; field_simp
  have hK0 : 0 < K := by rw [hK]; apply div_pos (by linarith) hξ
  have hKeo : K < P.eo := by
    by_contra h; push Not at h
    have := mul_le_mul_of_nonneg_left h hξ.le
    linarith
  set s1 := segOpt P g 1 with hs1
  set sP := segOpt P g (aP P) with hsP
  have hs1m : s1 ∈ Set.Icc 0 P.ebar := (segOpt_spec P hS g 1 hg0.le zero_le_one le_rfl).1.1
  have hsPm : sP ∈ Set.Icc 0 P.ebar := (segOpt_spec P hS g (aP P) hg0.le haP0 haP1).1.1
  have hfp : footprint P s1 (s1 + P.eo - K) = K := by unfold footprint; ring
  have hfpP : footprint P sP (sP + P.eo) = 0 := by unfold footprint; ring
  have hvhvl : ¬ (0 ≤ P.vl - P.vh) := by intro h; linarith
  have hll : (0:ℝ) ≤ P.vl - P.vl := by simp
  have hhh : (0:ℝ) ≤ P.vh - P.vh := by simp
  have hhl : (0:ℝ) ≤ P.vh - P.vl := by linarith
  have hK1 : (0:ℝ) ≤ P.vh - P.ξ * K - P.vl := by rw [hξK]; simp
  have hK2 : (0:ℝ) ≤ P.vh - P.ξ * 0 - P.vh := by simp
  -- demands at the two profiles
  have hdCP : demandC P P.vh sP (sP + P.eo) = P.α * P.m := by
    simp only [demandC, hfpP, hβc]
    rw [if_pos hK2]; ring
  have hdUP : demandU P P.vh sP (sP + P.eo) = (1 - P.α) * P.βu * P.m := by
    simp only [demandU]
    rw [if_pos hhh, if_neg hvhvl]; ring
  have hdC1 : demandC P P.vl s1 (s1 + P.eo - K) = P.α * P.m := by
    simp only [demandC, hfp, hβc]
    rw [if_pos hK1]; ring
  have hdU1 : demandU P P.vl s1 (s1 + P.eo - K) = (1 - P.α) * P.m := by
    simp only [demandU]
    rw [if_pos hhl, if_pos hll]; ring
  -- profits at the two profiles
  have hπ1 : profit P g P.vl s1 (s1 + P.eo - K) = valAllP P g := by
    unfold profit demand valAllP
    rw [hdC1, hdU1, ← hs1, hK]; ring
  have hπP : profit P g P.vh sP (sP + P.eo) = valTwoP P g := by
    unfold profit demand valTwoP
    rw [hdCP, hdUP, ← hsP]; unfold aP; ring
  have hfeas1 : Feasible P s1 (s1 + P.eo - K) := ⟨hs1m, by constructor <;> linarith [hs1m.1]⟩
  have hfeasP : Feasible P sP (sP + P.eo) := ⟨hsPm, by constructor <;> linarith [hsPm.1]⟩
  have hT3 : ∀ e ∈ Set.Icc 0 P.ebar, 0 ≤ segObj P g 1 s1 - segObj P g 1 e := fun e he => by
    have := segObj_le P hS g 1 hg0.le zero_le_one le_rfl e he; linarith
  have hT3P : ∀ e ∈ Set.Icc 0 P.ebar, 0 ≤ segObj P g (aP P) sP - segObj P g (aP P) e :=
    fun e he => by
      have := segObj_le P hS g (aP P) hg0.le haP0 haP1 e he; linarith
  have hF0 : ∀ e t, Feasible P e t → 0 ≤ footprint P e t := fun e t h => by
    unfold footprint; linarith [h.2.2]
  have hgap : 0 < P.ξ - g := by linarith
  -- bounds in the two main cases
  have boundA : ∀ p e t, Feasible P e t → 0 ≤ P.vl - p →
      0 ≤ P.vh - P.ξ * footprint P e t - p →
      profit P g p e t = valAllP P g - ((P.vl + g * K - p - g * footprint P e t) * P.m +
        (segObj P g 1 s1 - segObj P g 1 e)) → profit P g p e t ≤ valAllP P g := by
    intro p e t hfeas h4 h1 heq
    have := hT3 e hfeas.1
    have := mul_nonneg (slackA P hS g hg0 hgξ p _ h4 h1).1 hm.le
    linarith
  have boundB : ∀ p e t, Feasible P e t → 0 ≤ P.vh - P.ξ * footprint P e t - p →
      profit P g p e t = valTwoP P g - ((P.vh - P.ξ * footprint P e t - p) * aP P * P.m +
        (P.ξ - g) * footprint P e t * aP P * P.m +
        (segObj P g (aP P) sP - segObj P g (aP P) e)) → profit P g p e t ≤ valTwoP P g := by
    intro p e t hfeas h1 heq
    have := hT3P e hfeas.1
    have := hF0 e t hfeas
    have : 0 ≤ (P.vh - P.ξ * footprint P e t - p) * aP P * P.m := by
      have := mul_nonneg h1 haP0; positivity
    have : 0 ≤ (P.ξ - g) * footprint P e t * aP P * P.m := by positivity
    linarith
  have part1 : ∀ p e t, Feasible P e t →
      profit P g p e t ≤ max (max (valOne P) (valThree P)) (max (valTwoP P g) (valAllP P g)) := by
    intro p e t hfeas
    rcases caseP_cases P hS hβc g hg0 hgξ p e t hfeas with ⟨h4, h1, heq⟩ | ⟨h1, heq⟩ | hle | hle
    · exact le_max_of_le_right (le_max_of_le_right (boundA p e t hfeas h4 h1 heq))
    · exact le_max_of_le_right (le_max_of_le_left (boundB p e t hfeas h1 heq))
    · exact le_max_of_le_left (le_max_of_le_left hle)
    · exact le_max_of_le_left (le_max_of_le_right hle)
  have hm1 := le_max_left (valOne P) (valThree P)
  have hm3 := le_max_right (valOne P) (valThree P)
  refine ⟨part1, ?_, ?_, ⟨hdCP, hdUP⟩, ⟨hdC1, hdU1⟩⟩
  · intro hlt p e t
    have hlt1 := lt_of_le_of_lt (le_max_left _ _) hlt
    have hlt2 := lt_of_le_of_lt (le_max_right _ _) hlt
    constructor
    · rintro ⟨hfeas, hbest⟩
      have hge := hbest P.vl s1 (s1 + P.eo - K) hfeas1
      rw [hπ1] at hge
      rcases caseP_cases P hS hβc g hg0 hgξ p e t hfeas with ⟨h4, h1, heq⟩ | ⟨h1, heq⟩ | hle | hle
      · have hA := hT3 e hfeas.1
        obtain ⟨hs0, hsz⟩ := slackA P hS g hg0 hgξ p _ h4 h1
        have hB := mul_nonneg hs0 hm.le
        have hB0 : (P.vl + g * K - p - g * footprint P e t) * P.m = 0 := by linarith
        have hz : P.vl + g * K - p - g * footprint P e t = 0 := by
          rcases mul_eq_zero.1 hB0 with h | h
          · exact h
          · linarith
        obtain ⟨hp, hFK⟩ := hsz hz
        have he : e = s1 := eq_segOpt_of_segObj P hS g 1 hg0.le zero_le_one le_rfl e hfeas.1
          (by linarith)
        refine ⟨hp, he, ?_⟩
        unfold footprint at hFK
        rw [← he]; linarith
      · exfalso
        have := boundB p e t hfeas h1 heq
        linarith
      · exfalso; linarith
      · exfalso; linarith
    · rintro ⟨rfl, rfl, rfl⟩
      refine ⟨hfeas1, fun p' e' t' h' => ?_⟩
      rw [hπ1]
      have := part1 p' e' t' h'
      have : max (max (valOne P) (valThree P)) (max (valTwoP P g) (valAllP P g)) = valAllP P g := by
        apply le_antisymm
        · apply max_le (max_le (by linarith) (by linarith)) (max_le (by linarith) le_rfl)
        · exact le_max_of_le_right (le_max_right _ _)
      linarith
  · intro hlt p e t
    have hlt1 := lt_of_le_of_lt (le_max_left _ _) hlt
    have hlt2 := lt_of_le_of_lt (le_max_right _ _) hlt
    have haPpos : 0 < aP P := by
      rcases haP0.lt_or_eq with h | h
      · exact h
      · exfalso
        have hf0 := (c_f_bounds P hS sP hsPm).2
        have : valTwoP P g ≤ 0 := by unfold valTwoP; rw [← hsP, ← h]; simp; linarith
        have hα : P.α = 0 := by
          unfold aP at h
          have : 0 ≤ (1 - P.α) * P.βu := mul_nonneg (by linarith) hβu0
          linarith
        have : 0 < valThree P := by
          unfold valThree; rw [hα]
          have : 0 < P.vl - P.c P.ebar := by linarith
          positivity
        linarith
    constructor
    · rintro ⟨hfeas, hbest⟩
      have hge := hbest P.vh sP (sP + P.eo) hfeasP
      rw [hπP] at hge
      have hF := hF0 e t hfeas
      rcases caseP_cases P hS hβc g hg0 hgξ p e t hfeas with ⟨h4, h1, heq⟩ | ⟨h1, heq⟩ | hle | hle
      · exfalso
        have := boundA p e t hfeas h4 h1 heq
        linarith
      · have hA := hT3P e hfeas.1
        have hB : 0 ≤ (P.vh - P.ξ * footprint P e t - p) * aP P * P.m := by
          have := mul_nonneg h1 haP0; positivity
        have hC : 0 ≤ (P.ξ - g) * footprint P e t * aP P * P.m := by positivity
        have hFz : footprint P e t = 0 := by
          have hpos : 0 < (P.ξ - g) * (aP P * P.m) := by positivity
          have : footprint P e t * ((P.ξ - g) * (aP P * P.m)) = 0 := by linarith
          rcases mul_eq_zero.1 this with h | h
          · exact h
          · linarith
        have hp : p = P.vh := by
          have hpos : 0 < aP P * P.m := by positivity
          have : (P.vh - P.ξ * footprint P e t - p) * (aP P * P.m) = 0 := by linarith
          rcases mul_eq_zero.1 this with h | h
          · rw [hFz] at h; linarith
          · linarith
        have he : e = sP := eq_segOpt_of_segObj P hS g (aP P) hg0.le haP0 haP1 e hfeas.1
          (by linarith)
        refine ⟨hp, he, ?_⟩
        unfold footprint at hFz
        rw [← he]; linarith
      · exfalso; linarith
      · exfalso; linarith
    · rintro ⟨rfl, rfl, rfl⟩
      refine ⟨hfeasP, fun p' e' t' h' => ?_⟩
      rw [hπP]
      have := part1 p' e' t' h'
      have : max (max (valOne P) (valThree P)) (max (valTwoP P g) (valAllP P g)) = valTwoP P g := by
        apply le_antisymm
        · apply max_le (max_le (by linarith) (by linarith)) (max_le le_rfl (by linarith))
        · exact le_max_of_le_right (le_max_left _ _)
      linarith
