-- Prove2me | solution 1 for ComplementarySourcing.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T14:22:36.26782+00:00
-- url     : https://prove2.me/submissions/3718019d-dbfd-46bf-a11d-5144f4aa1855

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Definitions.Def_ComplementarySourcing_IsBestResponse
import Definitions.Def_ComplementarySourcing_supplierStageProfit
import Definitions.Def_ComplementarySourcing_manufacturerStageProfit
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Definitions.Def_ComplementarySourcing_ModelM_manufacturerProfit
import Definitions.Def_ComplementarySourcing_ModelM_supplierProfit
import Definitions.Def_ComplementarySourcing_ModelS_supplierProfit
import Definitions.Def_ComplementarySourcing_ModelS_manufacturerProfit
import Mathlib.Tactic.Ring
import Definitions.Def_ComplementarySourcing_StackelbergGame_IsEquilibrium
import Definitions.Def_ComplementarySourcing_ModelM_game
import Definitions.Def_ComplementarySourcing_ModelS_game

namespace S14Complementary

/-- A payment at least as large as the demand cap forces full demand, even
when the follower is allowed any nonnegative effort. -/
theorem saturated_response {e c b : ℝ} (he : 0 ≤ e) (hec : e ≤ c)
    (hb : ComplementarySourcing.IsBestResponse (Set.Ici 0)
      (fun y : ℝ => c * min y e - (1 / 2) * y ^ 2) b) : b = e := by
  have hb0 : 0 ≤ b := hb.1
  have h := hb.2 e he
  dsimp only at h
  rw [min_self] at h
  by_cases hbe : b ≤ e
  · rw [min_eq_left hbe] at h
    have hp := mul_nonneg (sub_nonneg.mpr hec) (sub_nonneg.mpr hbe)
    have hs : (e - b) ^ 2 ≤ 0 := by nlinarith
    have hz : e - b = 0 := sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))
    linarith
  · have heb : e < b := lt_of_not_ge hbe
    rw [min_eq_right (le_of_lt heb)] at h
    have hp : 0 < (b - e) * (b + e) :=
      mul_pos (sub_pos.mpr heb) (by linarith)
    nlinarith

/-- At zero manufacturer effort, the payment `c / μ` induces the cap. -/
theorem supplier_response_at_zero {μ α c e b : ℝ} (hμ : 0 < μ)
    (he : 0 ≤ e) (hec : e ≤ c)
    (hb : ComplementarySourcing.IsBestResponse (Set.Ici 0)
      (ComplementarySourcing.supplierStageProfit μ α 0 (c / μ) e) b) : b = e := by
  have hp : ComplementarySourcing.supplierStageProfit μ α 0 (c / μ) e =
      fun y : ℝ => c * min y e - (1 / 2) * y ^ 2 := by
    funext y
    dsimp [ComplementarySourcing.supplierStageProfit, ComplementarySourcing.demand]
    simp only [zero_add, zero_mul, mul_zero, add_zero]
    field_simp
  rw [hp] at hb
  exact saturated_response he hec hb

/-- At zero supplier effort, the complementary wholesale payment induces the cap. -/
theorem manufacturer_response_at_zero {μ α r c e b : ℝ} (hμ : 0 < μ)
    (he : 0 ≤ e) (hec : e ≤ c)
    (hb : ComplementarySourcing.IsBestResponse (Set.Ici 0)
      (ComplementarySourcing.manufacturerStageProfit μ α r 0 (r - c / μ) e) b) :
    b = e := by
  have hp : ComplementarySourcing.manufacturerStageProfit μ α r 0 (r - c / μ) e =
      fun y : ℝ => c * min y e - (1 / 2) * y ^ 2 := by
    funext y
    dsimp [ComplementarySourcing.manufacturerStageProfit, ComplementarySourcing.demand]
    simp only [mul_zero, add_zero, sub_sub_cancel]
    field_simp
  rw [hp] at hb
  exact saturated_response he hec hb

end S14Complementary

open ComplementarySourcing

namespace S14Complementary

lemma demand_upper {μ α xm xs ε : ℝ} (hμ : 0 ≤ μ) :
    demand μ α xm xs ε ≤ μ * ε := by
  exact mul_le_mul_of_nonneg_left (min_le_right _ _) hμ

lemma total_profit_M {μ α r ε₀ σ xm w : ℝ} (f : ℝ → ℝ)
    (hμ : 0 ≤ μ) (hr : 0 ≤ r) :
    ModelM.manufacturerProfit μ α r ε₀ σ xm w f +
      ModelM.supplierProfit μ α ε₀ σ xm w f ≤ r * μ * ε₀ := by
  have hmean : 1 / 2 * demand μ α xm (f (ε₀ + σ)) (ε₀ + σ) +
      1 / 2 * demand μ α xm (f (ε₀ - σ)) (ε₀ - σ) ≤ μ * ε₀ := by
    nlinarith [demand_upper (α := α) (xm := xm) (xs := f (ε₀ + σ))
      (ε := ε₀ + σ) hμ,
      demand_upper (α := α) (xm := xm) (xs := f (ε₀ - σ))
      (ε := ε₀ - σ) hμ]
  have htotal := mul_le_mul_of_nonneg_left hmean hr
  dsimp [ModelM.manufacturerProfit, ModelM.supplierProfit, supplierStageProfit]
  nlinarith [sq_nonneg xm, sq_nonneg (f (ε₀ + σ)), sq_nonneg (f (ε₀ - σ))]

lemma total_profit_S {μ α r ε₀ σ xs w : ℝ} (f : ℝ → ℝ)
    (hμ : 0 ≤ μ) (hr : 0 ≤ r) :
    ModelS.supplierProfit μ α ε₀ σ xs w f +
      ModelS.manufacturerProfit μ α r ε₀ σ xs w f ≤ r * μ * ε₀ := by
  have hmean : 1 / 2 * demand μ α (f (ε₀ + σ)) xs (ε₀ + σ) +
      1 / 2 * demand μ α (f (ε₀ - σ)) xs (ε₀ - σ) ≤ μ * ε₀ := by
    nlinarith [demand_upper (α := α) (xm := f (ε₀ + σ)) (xs := xs)
      (ε := ε₀ + σ) hμ,
      demand_upper (α := α) (xm := f (ε₀ - σ)) (xs := xs)
      (ε := ε₀ - σ) hμ]
  have htotal := mul_le_mul_of_nonneg_left hmean hr
  dsimp [ModelS.supplierProfit, ModelS.manufacturerProfit, manufacturerStageProfit]
  nlinarith [sq_nonneg xs, sq_nonneg (f (ε₀ + σ)), sq_nonneg (f (ε₀ - σ))]

lemma risk_lt_mean {ε₀ σ : ℝ} (hε₀ : 0 < ε₀)
    (hσ : σ / ε₀ ≤ 3 - 2 * Real.sqrt 2) : σ < ε₀ := by
  have hroot : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  have hratio : σ / ε₀ < 1 := by linarith
  exact (div_lt_one hε₀).mp hratio

end S14Complementary

open ComplementarySourcing

namespace S14Complementary

lemma leader_lower_M {μ α r ε₀ σ x w : ℝ} {s : ℝ × ℝ → ℝ → ℝ}
    (hμ : 0 < μ) (hε₀ : 0 ≤ ε₀) (hσ : 0 ≤ σ) (hsmall : σ ≤ ε₀)
    (hprice : ε₀ + σ ≤ r * μ)
    (hM : (ModelM.game μ α r ε₀ σ).IsEquilibrium s (x,w)) :
    (r * μ - (ε₀ + σ)) * ε₀ ≤
      ModelM.manufacturerProfit μ α r ε₀ σ x w (s (x,w)) := by
  have hfeas : (0, (ε₀ + σ) / μ) ∈
      (ModelM.game μ α r ε₀ σ).leaderFeasible := by
    change 0 ≤ (0 : ℝ) ∧ 0 ≤ (ε₀ + σ) / μ ∧ (ε₀ + σ) / μ ≤ r
    exact ⟨le_rfl, div_nonneg (by linarith) hμ.le, (div_le_iff₀ hμ).mpr hprice⟩
  have hp : s (0, (ε₀ + σ) / μ) (ε₀ + σ) = ε₀ + σ :=
    supplier_response_at_zero hμ (by linarith) le_rfl
      (hM.1 _ hfeas _ (by simp [ModelM.game]))
  have hm : s (0, (ε₀ + σ) / μ) (ε₀ - σ) = ε₀ - σ :=
    supplier_response_at_zero hμ (by linarith) (by linarith)
      (hM.1 _ hfeas _ (by simp [ModelM.game]))
  have hval : ModelM.manufacturerProfit μ α r ε₀ σ 0 ((ε₀ + σ) / μ)
      (s (0, (ε₀ + σ) / μ)) = (r * μ - (ε₀ + σ)) * ε₀ := by
    simp only [ModelM.manufacturerProfit, hp, hm, demand, zero_add, zero_mul,
      add_zero, min_self, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero]
    field_simp
    <;> ring
  have hbest := hM.2.2 (0, (ε₀ + σ) / μ) hfeas
  change ModelM.manufacturerProfit μ α r ε₀ σ 0 ((ε₀ + σ) / μ)
      (s (0, (ε₀ + σ) / μ)) ≤
        ModelM.manufacturerProfit μ α r ε₀ σ x w (s (x,w)) at hbest
  rwa [hval] at hbest

lemma leader_lower_S {μ α r ε₀ σ x w : ℝ} {s : ℝ × ℝ → ℝ → ℝ}
    (hμ : 0 < μ) (hε₀ : 0 ≤ ε₀) (hσ : 0 ≤ σ) (hsmall : σ ≤ ε₀)
    (hprice : ε₀ + σ ≤ r * μ)
    (hS : (ModelS.game μ α r ε₀ σ).IsEquilibrium s (x,w)) :
    (r * μ - (ε₀ + σ)) * ε₀ ≤
      ModelS.supplierProfit μ α ε₀ σ x w (s (x,w)) := by
  have hq0 : 0 ≤ (ε₀ + σ) / μ := div_nonneg (by linarith) hμ.le
  have hqr : (ε₀ + σ) / μ ≤ r := (div_le_iff₀ hμ).mpr hprice
  have hfeas : (0, r - (ε₀ + σ) / μ) ∈
      (ModelS.game μ α r ε₀ σ).leaderFeasible := by
    change 0 ≤ (0 : ℝ) ∧ 0 ≤ r - (ε₀ + σ) / μ ∧ r - (ε₀ + σ) / μ ≤ r
    exact ⟨le_rfl, by linarith, by linarith⟩
  have hp : s (0, r - (ε₀ + σ) / μ) (ε₀ + σ) = ε₀ + σ :=
    manufacturer_response_at_zero hμ (by linarith) le_rfl
      (hS.1 _ hfeas _ (by simp [ModelS.game]))
  have hm : s (0, r - (ε₀ + σ) / μ) (ε₀ - σ) = ε₀ - σ :=
    manufacturer_response_at_zero hμ (by linarith) (by linarith)
      (hS.1 _ hfeas _ (by simp [ModelS.game]))
  have hval : ModelS.supplierProfit μ α ε₀ σ 0 (r - (ε₀ + σ) / μ)
      (s (0, r - (ε₀ + σ) / μ)) = (r * μ - (ε₀ + σ)) * ε₀ := by
    simp only [ModelS.supplierProfit, hp, hm, demand, add_zero, mul_zero,
      min_self, zero_pow (by decide : 2 ≠ 0), sub_zero]
    field_simp
    <;> ring
  have hbest := hS.2.2 (0, r - (ε₀ + σ) / μ) hfeas
  change ModelS.supplierProfit μ α ε₀ σ 0 (r - (ε₀ + σ) / μ)
      (s (0, r - (ε₀ + σ) / μ)) ≤
        ModelS.supplierProfit μ α ε₀ σ x w (s (x,w)) at hbest
  rwa [hval] at hbest

end S14Complementary

open ComplementarySourcing S14Complementary

theorem solution {μ α r ε₀ σ xM wM xS wS : ℝ} {sM sS : ℝ × ℝ → ℝ → ℝ}
    (hμ : 0 < μ) (_hα : 0 ≤ α) (hε₀ : 0 < ε₀) (hσ₀ : 0 ≤ σ)
    (hr : r * μ ≥ 3 * ε₀ + σ) (hσ : σ / ε₀ ≤ 3 - 2 * Real.sqrt 2)
    (hM : (ModelM.game μ α r ε₀ σ).IsEquilibrium sM (xM, wM))
    (hS : (ModelS.game μ α r ε₀ σ).IsEquilibrium sS (xS, wS)) :
    ModelM.manufacturerProfit μ α r ε₀ σ xM wM (sM (xM, wM)) >
        ModelS.manufacturerProfit μ α r ε₀ σ xS wS (sS (xS, wS)) ∧
      ModelS.supplierProfit μ α ε₀ σ xS wS (sS (xS, wS)) >
        ModelM.supplierProfit μ α ε₀ σ xM wM (sM (xM, wM)) := by
  have hsmall := risk_lt_mean hε₀ hσ
  have hprice : ε₀ + σ ≤ r * μ := by linarith
  have hrnonneg : 0 ≤ r := by
    by_contra! hneg
    have hproduct := mul_neg_of_neg_of_pos hneg hμ
    linarith
  have hLM := leader_lower_M hμ hε₀.le hσ₀ hsmall.le hprice hM
  have hLS := leader_lower_S hμ hε₀.le hσ₀ hsmall.le hprice hS
  have hTM := total_profit_M (α := α) (ε₀ := ε₀) (σ := σ) (xm := xM) (w := wM) (sM (xM,wM)) hμ.le hrnonneg
  have hTS := total_profit_S (α := α) (ε₀ := ε₀) (σ := σ) (xs := xS) (w := wS) (sS (xS,wS)) hμ.le hrnonneg
  have hgap : (ε₀ + σ) * ε₀ < (r * μ - (ε₀ + σ)) * ε₀ :=
    mul_lt_mul_of_pos_right (by linarith) hε₀
  constructor <;> linarith only [hLM, hLS, hTM, hTS, hgap]

#print axioms solution
