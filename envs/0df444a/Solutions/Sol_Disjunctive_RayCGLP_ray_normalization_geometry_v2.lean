-- Prove2me | solution 1 for Disjunctive.RayCGLP.ray_normalization_geometry_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:37:27.562701+00:00
-- url     : https://prove2.me/submissions/5a384205-f583-484a-8ebc-3daa6b60c687

import Mathlib
import Definitions.Def_Disjunctive_RayCGLP_Basic

open Disjunctive.RayCGLP

theorem solution {n m : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) (g : Fin m → ℝ)
    (PD : Set (Fin n → ℝ)) (hPD : PD = {x | ∀ r, g r ≤ (G.mulVec x) r})
    (xbar xstar : Fin n → ℝ) (hxbar : xbar ∉ PD) (hxstar : xstar ∈ PD) :
    ∃ alphaT betaT, IsCGLPYOptimal PD (xstar - xbar) xbar alphaT betaT ∧
      dotProduct alphaT xbar < betaT ∧ (∀ x ∈ PD, betaT ≤ dotProduct alphaT x) ∧
      ∃ t : ℝ, IsGreatest
        {t' : ℝ | t' ∈ Set.Ioc (0 : ℝ) 1 ∧
          dotProduct alphaT (xbar + t' • (xstar - xbar)) = betaT} t ∧
        xbar + t • (xstar - xbar) ∈ PD := by
  set y := xstar - xbar with hy
  have hmv : ∀ (t : ℝ) r, (G.mulVec (xbar + t • y)) r = G.mulVec xbar r + t * G.mulVec y r := by
    intro t r
    simp [Matrix.mulVec_add, Matrix.mulVec_smul]
  have hdot : ∀ (α : Fin n → ℝ) (t : ℝ), α ⬝ᵥ (xbar + t • y) = α ⬝ᵥ xbar + t * (α ⬝ᵥ y) := by
    intro α t
    simp [dotProduct_add, dotProduct_smul]
  set S : Set ℝ := {t | t ∈ Set.Icc (0:ℝ) 1 ∧ xbar + t • y ∈ PD} with hS
  have hclosed : IsClosed S := by
    have : S = Set.Icc (0:ℝ) 1 ∩ ⋂ r, {t : ℝ | g r ≤ G.mulVec xbar r + t * G.mulVec y r} := by
      ext t
      simp only [hS, hPD, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, hmv]
    rw [this]
    refine isClosed_Icc.inter (isClosed_iInter fun r => ?_)
    exact isClosed_le continuous_const (by fun_prop)
  have hcpt : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed (fun t ht => ht.1)
  have h1 : (1:ℝ) ∈ S := by
    refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
    have : xbar + (1:ℝ) • y = xstar := by simp [hy]
    rw [this]; exact hxstar
  obtain ⟨ts, hts, hmin⟩ := hcpt.exists_isMinOn ⟨1, h1⟩ continuous_id.continuousOn
  have hts0 : 0 < ts := by
    rcases lt_or_eq_of_le hts.1.1 with h | h
    · exact h
    · exfalso; apply hxbar
      have := hts.2; rw [← h] at this; simpa using this
  have hp : ∀ r, g r ≤ G.mulVec xbar r + ts * G.mulVec y r := by
    have := hts.2; rw [hPD] at this
    intro r; have := this r; rwa [hmv] at this
  -- a tight row with positive direction
  have htight : ∃ r, G.mulVec xbar r + ts * G.mulVec y r = g r ∧ 0 < G.mulVec y r := by
    by_contra hcon
    push_neg at hcon
    have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
        ε < ts ∧ ∀ r, g r ≤ G.mulVec xbar r + (ts - ε) * G.mulVec y r := by
      refine Filter.Eventually.and ?_ ?_
      · exact nhdsWithin_le_nhds (eventually_lt_nhds hts0)
      · rw [Filter.eventually_all]
        intro r
        rcases lt_or_eq_of_le (hp r) with hlt | heq
        · have hc : Continuous fun ε : ℝ => G.mulVec xbar r + (ts - ε) * G.mulVec y r := by
            fun_prop
          have : ∀ᶠ ε in nhds (0:ℝ), g r < G.mulVec xbar r + (ts - ε) * G.mulVec y r := by
            have h0 : g r < G.mulVec xbar r + (ts - 0) * G.mulVec y r := by simpa using hlt
            exact continuousAt_const.eventually_lt hc.continuousAt h0
          exact nhdsWithin_le_nhds (this.mono fun _ h => h.le)
        · have hb := hcon r heq.symm
          filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
          nlinarith
    obtain ⟨ε, ⟨hεt, hεr⟩, hε0⟩ := (hev.and (self_mem_nhdsWithin :
      Set.Ioi (0:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0))).exists
    have hε0 : (0:ℝ) < ε := hε0
    have hmem : ts - ε ∈ S := by
      refine ⟨⟨by linarith, by linarith [hts.1.2]⟩, ?_⟩
      rw [hPD]; intro r; rw [hmv]; exact hεr r
    have := hmin hmem
    simp at this; linarith
  obtain ⟨r, hr, hbr⟩ := htight
  set c := G.mulVec y r
  refine ⟨(1 / c) • G r, g r / c, ?_⟩
  have hrow : ∀ x, ((1 / c) • G r) ⬝ᵥ x = (G.mulVec x r) / c := by
    intro x
    rw [smul_dotProduct, smul_eq_mul]; simp [Matrix.mulVec, div_eq_inv_mul]
  have hvalid : ∀ x ∈ PD, g r / c ≤ ((1 / c) • G r) ⬝ᵥ x := by
    intro x hx
    rw [hPD] at hx
    rw [hrow]; exact div_le_div_of_nonneg_right (hx r) hbr.le
  have hy1 : ((1 / c) • G r) ⬝ᵥ y = 1 := by rw [hrow]; exact div_self hbr.ne'
  have hobj : ((1 / c) • G r) ⬝ᵥ xbar - g r / c = -ts := by
    rw [hrow, ← sub_div, div_eq_iff hbr.ne']; linarith
  refine ⟨⟨⟨hvalid, hy1⟩, ?_⟩, ?_, hvalid, ts, ⟨⟨⟨hts0, hts.1.2⟩, ?_⟩, ?_⟩, hts.2⟩
  · rintro α' β' ⟨hv', hy'⟩
    have := hv' _ hts.2
    rw [hdot, hy'] at this
    rw [hobj]; linarith
  · linarith
  · rw [hdot, hy1]; linarith
  · rintro t' ⟨_, ht'⟩
    rw [hdot, hy1] at ht'
    linarith
