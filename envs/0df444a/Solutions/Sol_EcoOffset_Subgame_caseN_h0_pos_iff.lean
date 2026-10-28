-- Prove2me | solution 1 for EcoOffset.Subgame.caseN_h0_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:24:00.020239+00:00
-- url     : https://prove2.me/submissions/a7c29081-4eaf-40a4-b5af-d6cdc959b081

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace Aux_Eco_caseN
open EcoOffset.Subgame

theorem segOpt_zero (P : Params) (hS : P.Standing) (a : ℝ) (ha : 0 ≤ a) :
    segOpt P 0 a = P.ebar := by
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe, hder⟩ := hS
  have hcd : Differentiable ℝ P.c := hc2.differentiable (by norm_num)
  have hfd : Differentiable ℝ P.f := hf2.differentiable (by norm_num)
  set G : ℝ → ℝ := fun y => -P.c y * a * P.m - P.f y with hG
  have hseg : ∀ e, segObj P 0 a e = G e := by intro e; simp only [segObj, hG]; ring
  have hGd : ∀ x, HasDerivAt G (-(deriv P.c x) * a * P.m - deriv P.f x) x := fun x =>
    (((hcd x).hasDerivAt.neg.mul_const a).mul_const P.m).sub (hfd x).hasDerivAt
  have hmono : StrictMonoOn G (Set.Icc 0 P.ebar) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact fun x _ => (hGd x).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hGd x).deriv]
      obtain ⟨h1, -, h3, -⟩ := hder x (Set.Ioo_subset_Icc_self hx)
      have : 0 ≤ -(deriv P.c x) * a * P.m := by
        have : 0 ≤ -(deriv P.c x) := by linarith
        positivity
      linarith
  have hebar : P.ebar ∈ Set.Icc 0 P.ebar := Set.right_mem_Icc.mpr heb.le
  have uniq : ∀ e, IsSegOpt P 0 a e → e = P.ebar := by
    intro e ⟨he, hopt⟩
    by_contra hne
    have hlt : e < P.ebar := lt_of_le_of_ne he.2 hne
    have h1 := hmono he hebar hlt
    have h2 := hopt P.ebar hebar
    rw [hseg, hseg] at h2
    linarith
  have hex : ∃ e, IsSegOpt P 0 a e := by
    refine ⟨P.ebar, hebar, fun e' he' => ?_⟩
    rw [hseg, hseg]
    exact hmono.monotoneOn he' hebar he'.2
  unfold segOpt
  split_ifs
  apply uniq
  exact Exists.choose_spec _

end Aux_Eco_caseN

open EcoOffset.Subgame in
theorem solution (P : Params) (hS : P.Standing) (hβu : P.βu = 1) (hα : 0 < P.α) :
    0 < hN P 0 ↔ P.βc < B2 P := by
  have hS' := hS
  obtain ⟨hm, heb, heo, hξ, hα0, hα1, hβc0, hβc1, hβu0, hβu1, hvl0, hcvl, hvlh, hc2, hf2, hfe, hder⟩ := hS'
  have haN : 0 ≤ aN P := by
    unfold aN
    have : 0 ≤ P.α * P.βc := mul_nonneg hα0 hβc0
    linarith
  unfold hN valAll valTwoN
  rw [Aux_Eco_caseN.segOpt_zero P hS 1 (by norm_num), Aux_Eco_caseN.segOpt_zero P hS _ haN, hfe]
  have hK : 0 < P.vh - P.c P.ebar := by linarith
  have key : (P.vl - P.c P.ebar - 0 * P.ebar - 0 * P.eo) * P.m - 0 -
      ((P.vh - P.c P.ebar - 0 * P.ebar - 0 * P.eo) * aN P * P.m - 0) =
      P.m * ((P.vl - P.c P.ebar) - (P.vh - P.c P.ebar) * aN P) := by ring
  rw [key]
  unfold B2 aN
  rw [lt_div_iff₀ hα]
  constructor
  · intro h
    have h' : 0 < (P.vl - P.c P.ebar) - (P.vh - P.c P.ebar) * (1 - P.α + P.α * P.βc) := by
      by_contra hc
      push_neg at hc
      have := mul_nonpos_of_nonneg_of_nonpos hm.le hc
      linarith
    have : 1 - P.α + P.α * P.βc < (P.vl - P.c P.ebar) / (P.vh - P.c P.ebar) := by
      rw [lt_div_iff₀ hK]; linarith
    linarith
  · intro h
    have : 1 - P.α + P.α * P.βc < (P.vl - P.c P.ebar) / (P.vh - P.c P.ebar) := by linarith
    rw [lt_div_iff₀ hK] at this
    apply mul_pos hm
    linarith
