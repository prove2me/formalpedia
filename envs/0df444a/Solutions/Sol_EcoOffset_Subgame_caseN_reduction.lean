-- Prove2me | solution 1 for EcoOffset.Subgame.caseN_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:22:11.019204+00:00
-- url     : https://prove2.me/submissions/91bc14b2-f79b-4896-8ee3-4ffe492c7de6

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model
import Theorems.Thm_EcoOffset_Subgame_segOpt_spec

namespace EcoCaseNAux
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

theorem aN_mem (P : Params) (hS : P.Standing) : 0 ≤ aN P ∧ aN P ≤ 1 := by
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, -⟩ := hS
  unfold aN
  constructor <;> nlinarith

/-- The case split of the proof: every feasible profit is one of three explicit forms. -/
theorem caseN_cases (P : Params) (hS : P.Standing) (hβu : P.βu = 1) (g : ℝ)
    (hg0 : 0 < g) (hgξ : g < P.ξ) (p e t : ℝ) (hfeas : Feasible P e t) :
    (0 ≤ P.vl - P.ξ * footprint P e t - p ∧
      profit P g p e t = valAll P g - ((P.vl - P.ξ * footprint P e t - p) * P.m +
        (P.ξ - g) * footprint P e t * P.m +
        (segObj P g 1 (segOpt P g 1) - segObj P g 1 e))) ∨
    (0 ≤ P.vh - P.ξ * footprint P e t - p ∧
      profit P g p e t = valTwoN P g - ((P.vh - P.ξ * footprint P e t - p) * aN P * P.m +
        (P.ξ - g) * footprint P e t * aN P * P.m +
        (segObj P g (aN P) (segOpt P g (aN P)) - segObj P g (aN P) e))) ∨
    profit P g p e t ≤ valOne P := by
  have hS' := hS
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe,
    hder⟩ := hS'
  have hF : footprint P e t = e + P.eo - t := rfl
  have hF0 : 0 ≤ footprint P e t := by rw [hF]; linarith [hfeas.2.2]
  have hξF : 0 ≤ P.ξ * footprint P e t := mul_nonneg hξ.le hF0
  by_cases i2 : 0 ≤ P.vl - P.ξ * footprint P e t - p
  · left
    refine ⟨i2, ?_⟩
    have i1 : 0 ≤ P.vh - P.ξ * footprint P e t - p := by linarith
    have i3 : 0 ≤ P.vh - p := by linarith
    have hd : demand P p e t = P.m := by
      simp only [demand, demandC, demandU, hβu, if_pos i1, if_pos i2, if_pos i3]
      ring
    rw [profit, hd]
    unfold valAll segObj
    rw [hF]
    ring
  · by_cases i1 : 0 ≤ P.vh - P.ξ * footprint P e t - p
    · right; left
      refine ⟨i1, ?_⟩
      have i3 : 0 ≤ P.vh - p := by linarith
      have hd : demand P p e t = aN P * P.m := by
        simp only [demand, demandC, demandU, hβu, if_pos i1, if_neg i2, if_pos i3, aN]
        ring
      rw [profit, hd]
      unfold valTwoN segObj
      rw [hF]
      ring
    · right; right
      have hcf := c_f_bounds P hS e hfeas.1
      have i2' : ¬ (0 ≤ P.vl - P.ξ * footprint P e t - p) := i2
      by_cases i3 : 0 ≤ P.vh - p
      · have hd : demand P p e t = (1 - P.α) * P.m := by
          simp only [demand, demandC, demandU, hβu, if_neg i1, if_neg i2', if_pos i3]
          ring
        rw [profit, hd]
        unfold valOne
        rw [hβu]
        have h1 : 0 ≤ (1 - P.α) * P.m := mul_nonneg (by linarith) hm.le
        have ht : 0 ≤ g * t := mul_nonneg hg0.le hfeas.2.1
        have : (p - P.c e - g * t) * ((1 - P.α) * P.m) ≤ (P.vh - P.c P.ebar) * ((1 - P.α) * P.m) :=
          mul_le_mul_of_nonneg_right (by linarith) h1
        nlinarith
      · have i4 : ¬ (0 ≤ P.vl - p) := by intro h; exact i3 (by linarith)
        have hd : demand P p e t = 0 := by
          simp only [demand, demandC, demandU, hβu, if_neg i1, if_neg i2', if_neg i3, if_neg i4]
          ring
        rw [profit, hd]
        unfold valOne
        rw [hβu]
        have : 0 ≤ (P.vh - P.c P.ebar) * (1 - P.α) * 1 * P.m := by
          have : 0 ≤ P.vh - P.c P.ebar := by linarith
          have : 0 ≤ 1 - P.α := by linarith
          positivity
        nlinarith

end EcoCaseNAux

open EcoOffset.Subgame EcoCaseNAux in
theorem solution (P : Params) (hS : P.Standing) (hβu : P.βu = 1) (g : ℝ)
    (hg0 : 0 < g) (hgξ : g < P.ξ) :
    (∀ p e t, Feasible P e t →
      profit P g p e t ≤ max (max (valOne P) (valTwoN P g)) (valAll P g)) ∧
    (max (valOne P) (valTwoN P g) < valAll P g →
      ∀ p e t, IsBestResponse P g p e t ↔
        (p = P.vl ∧ e = segOpt P g 1 ∧ t = segOpt P g 1 + P.eo)) ∧
    (max (valOne P) (valAll P g) < valTwoN P g →
      ∀ p e t, IsBestResponse P g p e t ↔
        (p = P.vh ∧ e = segOpt P g (aN P) ∧ t = segOpt P g (aN P) + P.eo)) ∧
    (demandC P P.vl (segOpt P g 1) (segOpt P g 1 + P.eo) = P.α * P.m ∧
      demandU P P.vl (segOpt P g 1) (segOpt P g 1 + P.eo) = (1 - P.α) * P.m) ∧
    (demandC P P.vh (segOpt P g (aN P)) (segOpt P g (aN P) + P.eo) = P.α * P.βc * P.m ∧
      demandU P P.vh (segOpt P g (aN P)) (segOpt P g (aN P) + P.eo) = (1 - P.α) * P.m) := by
  have hS' := hS
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe,
    hder⟩ := hS'
  obtain ⟨haN0, haN1⟩ := aN_mem P hS
  set s1 := segOpt P g 1 with hs1
  set sN := segOpt P g (aN P) with hsN
  have hs1m : s1 ∈ Set.Icc 0 P.ebar := (segOpt_spec P hS g 1 hg0.le zero_le_one le_rfl).1.1
  have hsNm : sN ∈ Set.Icc 0 P.ebar := (segOpt_spec P hS g (aN P) hg0.le haN0 haN1).1.1
  have hfp : footprint P s1 (s1 + P.eo) = 0 := by unfold footprint; ring
  have hfpN : footprint P sN (sN + P.eo) = 0 := by unfold footprint; ring
  have hvhvl : ¬ (0 ≤ P.vl - P.vh) := by intro h; linarith
  have hll : (0:ℝ) ≤ P.vl - P.vl := by simp
  have hhh : (0:ℝ) ≤ P.vh - P.vh := by simp
  have hhl : (0:ℝ) ≤ P.vh - P.vl := by linarith
  -- demands at the two profiles
  have hdC1 : demandC P P.vl s1 (s1 + P.eo) = P.α * P.m := by
    simp only [demandC, hfp, mul_zero, sub_zero]
    rw [if_pos hhl, if_pos hll]; ring
  have hdU1 : demandU P P.vl s1 (s1 + P.eo) = (1 - P.α) * P.m := by
    simp only [demandU, hβu]
    rw [if_pos hhl, if_pos hll]; ring
  have hdCN : demandC P P.vh sN (sN + P.eo) = P.α * P.βc * P.m := by
    simp only [demandC, hfpN, mul_zero, sub_zero]
    rw [if_pos hhh, if_neg hvhvl]; ring
  have hdUN : demandU P P.vh sN (sN + P.eo) = (1 - P.α) * P.m := by
    simp only [demandU, hβu]
    rw [if_pos hhh]; ring
  -- profits at the two profiles
  have hπ1 : profit P g P.vl s1 (s1 + P.eo) = valAll P g := by
    unfold profit demand valAll
    rw [hdC1, hdU1, ← hs1]; ring
  have hπN : profit P g P.vh sN (sN + P.eo) = valTwoN P g := by
    unfold profit demand valTwoN
    rw [hdCN, hdUN, ← hsN]; unfold aN; ring
  have hfeas1 : Feasible P s1 (s1 + P.eo) := ⟨hs1m, by constructor <;> linarith [hs1m.1]⟩
  have hfeasN : Feasible P sN (sN + P.eo) := ⟨hsNm, by constructor <;> linarith [hsNm.1]⟩
  -- nonnegativity of the slack terms
  have hT3 : ∀ e ∈ Set.Icc 0 P.ebar, 0 ≤ segObj P g 1 s1 - segObj P g 1 e := fun e he => by
    have := segObj_le P hS g 1 hg0.le zero_le_one le_rfl e he; linarith
  have hT3N : ∀ e ∈ Set.Icc 0 P.ebar, 0 ≤ segObj P g (aN P) sN - segObj P g (aN P) e :=
    fun e he => by
      have := segObj_le P hS g (aN P) hg0.le haN0 haN1 e he; linarith
  have hF0 : ∀ e t, Feasible P e t → 0 ≤ footprint P e t := fun e t h => by
    unfold footprint; linarith [h.2.2]
  have hgap : 0 < P.ξ - g := by linarith
  have part1 : ∀ p e t, Feasible P e t →
      profit P g p e t ≤ max (max (valOne P) (valTwoN P g)) (valAll P g) := by
    intro p e t hfeas
    have hF := hF0 e t hfeas
    rcases caseN_cases P hS hβu g hg0 hgξ p e t hfeas with ⟨h2, heq⟩ | ⟨h1, heq⟩ | hle
    · apply le_max_of_le_right
      have := hT3 e hfeas.1
      have : 0 ≤ (P.vl - P.ξ * footprint P e t - p) * P.m := mul_nonneg h2 hm.le
      have : 0 ≤ (P.ξ - g) * footprint P e t * P.m := by positivity
      linarith
    · apply le_max_of_le_left; apply le_max_of_le_right
      have := hT3N e hfeas.1
      have : 0 ≤ (P.vh - P.ξ * footprint P e t - p) * aN P * P.m := by
        have := mul_nonneg h1 haN0; positivity
      have : 0 ≤ (P.ξ - g) * footprint P e t * aN P * P.m := by positivity
      linarith
    · exact le_max_of_le_left (le_max_of_le_left hle)
  refine ⟨part1, ?_, ?_, ⟨hdC1, hdU1⟩, ⟨hdCN, hdUN⟩⟩
  · intro hlt p e t
    constructor
    · rintro ⟨hfeas, hbest⟩
      have hge := hbest P.vl s1 (s1 + P.eo) hfeas1
      rw [hπ1] at hge
      have hF := hF0 e t hfeas
      rcases caseN_cases P hS hβu g hg0 hgξ p e t hfeas with ⟨h2, heq⟩ | ⟨h1, heq⟩ | hle
      · have hA := hT3 e hfeas.1
        have hB : 0 ≤ (P.vl - P.ξ * footprint P e t - p) * P.m := mul_nonneg h2 hm.le
        have hC : 0 ≤ (P.ξ - g) * footprint P e t * P.m := by positivity
        have hC0 : (P.ξ - g) * footprint P e t * P.m = 0 := by linarith
        have hFz : footprint P e t = 0 := by
          rcases mul_eq_zero.1 hC0 with h | h
          · rcases mul_eq_zero.1 h with h | h
            · linarith
            · exact h
          · linarith
        have hB0 : (P.vl - P.ξ * footprint P e t - p) * P.m = 0 := by linarith
        have hp : p = P.vl := by
          rcases mul_eq_zero.1 hB0 with h | h
          · rw [hFz] at h; linarith
          · linarith
        have he : e = s1 := eq_segOpt_of_segObj P hS g 1 hg0.le zero_le_one le_rfl e hfeas.1
          (by linarith)
        refine ⟨hp, he, ?_⟩
        unfold footprint at hFz
        rw [← he]; linarith
      · exfalso
        have := hT3N e hfeas.1
        have : 0 ≤ (P.vh - P.ξ * footprint P e t - p) * aN P * P.m := by
          have := mul_nonneg h1 haN0; positivity
        have : 0 ≤ (P.ξ - g) * footprint P e t * aN P * P.m := by positivity
        have := le_max_right (valOne P) (valTwoN P g)
        linarith
      · exfalso
        have := le_max_left (valOne P) (valTwoN P g)
        linarith
    · rintro ⟨rfl, rfl, rfl⟩
      refine ⟨hfeas1, fun p' e' t' h' => ?_⟩
      rw [hπ1]
      have := part1 p' e' t' h'
      rwa [max_eq_right hlt.le] at this
  · intro hlt p e t
    have hval1 : 0 ≤ valOne P := by
      unfold valOne
      have : 0 ≤ P.vh - P.c P.ebar := by linarith
      have : 0 ≤ 1 - P.α := by linarith
      positivity
    have haNpos : 0 < aN P := by
      rcases haN0.lt_or_eq with h | h
      · exact h
      · exfalso
        have hf0 := (c_f_bounds P hS sN hsNm).2
        have : valTwoN P g ≤ 0 := by unfold valTwoN; rw [← hsN, ← h]; simp; linarith
        have := le_max_left (valOne P) (valAll P g)
        linarith
    constructor
    · rintro ⟨hfeas, hbest⟩
      have hge := hbest P.vh sN (sN + P.eo) hfeasN
      rw [hπN] at hge
      have hF := hF0 e t hfeas
      rcases caseN_cases P hS hβu g hg0 hgξ p e t hfeas with ⟨h2, heq⟩ | ⟨h1, heq⟩ | hle
      · exfalso
        have := hT3 e hfeas.1
        have : 0 ≤ (P.vl - P.ξ * footprint P e t - p) * P.m := mul_nonneg h2 hm.le
        have : 0 ≤ (P.ξ - g) * footprint P e t * P.m := by positivity
        have := le_max_right (valOne P) (valAll P g)
        linarith
      · have hA := hT3N e hfeas.1
        have hB : 0 ≤ (P.vh - P.ξ * footprint P e t - p) * aN P * P.m := by
          have := mul_nonneg h1 haN0; positivity
        have hC : 0 ≤ (P.ξ - g) * footprint P e t * aN P * P.m := by positivity
        have hC0 : (P.ξ - g) * footprint P e t * aN P * P.m = 0 := by linarith
        have hFz : footprint P e t = 0 := by
          have hpos : 0 < (P.ξ - g) * (aN P * P.m) := by positivity
          have : footprint P e t * ((P.ξ - g) * (aN P * P.m)) = 0 := by linarith
          rcases mul_eq_zero.1 this with h | h
          · exact h
          · linarith
        have hB0 : (P.vh - P.ξ * footprint P e t - p) * aN P * P.m = 0 := by linarith
        have hp : p = P.vh := by
          have hpos : 0 < aN P * P.m := by positivity
          have : (P.vh - P.ξ * footprint P e t - p) * (aN P * P.m) = 0 := by linarith
          rcases mul_eq_zero.1 this with h | h
          · rw [hFz] at h; linarith
          · linarith
        have he : e = sN := eq_segOpt_of_segObj P hS g (aN P) hg0.le haN0 haN1 e hfeas.1
          (by linarith)
        refine ⟨hp, he, ?_⟩
        unfold footprint at hFz
        rw [← he]; linarith
      · exfalso
        have := le_max_left (valOne P) (valAll P g)
        linarith
    · rintro ⟨rfl, rfl, rfl⟩
      refine ⟨hfeasN, fun p' e' t' h' => ?_⟩
      rw [hπN]
      have := part1 p' e' t' h'
      have h1 := le_max_left (valOne P) (valAll P g)
      have h2 := le_max_right (valOne P) (valAll P g)
      have : max (max (valOne P) (valTwoN P g)) (valAll P g) = valTwoN P g := by
        apply le_antisymm
        · apply max_le (max_le (by linarith) le_rfl) (by linarith)
        · exact le_max_of_le_left (le_max_right _ _)
      linarith
