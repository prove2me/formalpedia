-- Prove2me | solution 1 for CommodityCPC.kappa_pos
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:58:34.817344+00:00
-- url     : https://prove2.me/submissions/99998c7e-815a-4918-944c-ad6e8dcc8387

import Mathlib
import Definitions.Def_CommodityCPC_Model

open CommodityCPC in
theorem solution (p : CommodityCPC.Params) :
    0 < 4 - p.γ ^ 2 * p.lam .A * p.lam .B * (1 + p.β) ^ 2 ∧ 0 < p.κ := by
  have ha := p.hσa
  have hA := p.hσA
  have hB := p.hσB
  have hη0 := p.hη0
  have hη1 := p.hη1
  have hγ0 := p.hγ0
  have hγ1 := p.hγ1
  have hdA : 0 < p.σa ^ 2 + p.σA ^ 2 := by positivity
  have hdB : 0 < p.σa ^ 2 + p.σB ^ 2 := by positivity
  have key : p.lam .A * p.lam .B * (1 + p.β) ^ 2 =
      (p.σa ^ 2 + p.η * p.σA * p.σB) ^ 2 / ((p.σa ^ 2 + p.σA ^ 2) * (p.σa ^ 2 + p.σB ^ 2)) := by
    simp only [CommodityCPC.Params.lam, CommodityCPC.Params.σf, CommodityCPC.Params.β]
    field_simp
  have hAB : 0 < p.σA * p.σB := mul_pos hA hB
  have e1 : p.η * p.σA * p.σB ≤ p.σA * p.σB := by nlinarith
  have e2 : 0 ≤ p.η * p.σA * p.σB := by positivity
  have hnum : (p.σa ^ 2 + p.η * p.σA * p.σB) ^ 2 ≤
      (p.σa ^ 2 + p.σA ^ 2) * (p.σa ^ 2 + p.σB ^ 2) := by
    have s1 : (p.σa ^ 2 + p.η * p.σA * p.σB) ^ 2 ≤ (p.σa ^ 2 + p.σA * p.σB) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have s2 : (p.σa ^ 2 + p.σA * p.σB) ^ 2 ≤ (p.σa ^ 2 + p.σA ^ 2) * (p.σa ^ 2 + p.σB ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg p.σa) (sq_nonneg (p.σA - p.σB))]
    linarith
  have hX1 : p.lam .A * p.lam .B * (1 + p.β) ^ 2 ≤ 1 := by
    rw [key]; exact (div_le_one (by positivity)).mpr hnum
  have hX0 : 0 ≤ p.lam .A * p.lam .B * (1 + p.β) ^ 2 := by
    rw [key]; positivity
  have hg : p.γ ^ 2 ≤ 1 := by nlinarith
  have hprod : p.γ ^ 2 * p.lam .A * p.lam .B * (1 + p.β) ^ 2 ≤ 1 := by
    have : p.γ ^ 2 * p.lam .A * p.lam .B * (1 + p.β) ^ 2 =
        p.γ ^ 2 * (p.lam .A * p.lam .B * (1 + p.β) ^ 2) := by ring
    rw [this]
    exact mul_le_one₀ hg hX0 hX1
  have hpos : 0 < 4 - p.γ ^ 2 * p.lam .A * p.lam .B * (1 + p.β) ^ 2 := by linarith
  refine ⟨hpos, ?_⟩
  unfold CommodityCPC.Params.κ
  exact one_div_pos.mpr hpos
