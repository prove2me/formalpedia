-- Prove2me | solution 1 for CloudCostOpt.corollary_6_asymptotic_optimality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T18:02:44.498918+00:00
-- url     : https://prove2.me/submissions/7500d926-bdaf-4d4d-b9af-d581eadf4cc8

import Mathlib
import Definitions.Def_CloudCostOpt_piStar
import Definitions.Def_CloudCostOpt_opt
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_IsStable
import Definitions.Def_CloudCostOpt_mu
import Definitions.Def_CloudCostOpt_zCoef
import Definitions.Def_CloudCostOpt_Standing
import Definitions.Def_CloudCostOpt_rateX
import Theorems.Thm_CloudCostOpt_eq_8_9_piHat_optimal
import Theorems.Thm_CloudCostOpt_eq_12_14_gap_bound
import Theorems.Thm_CloudCostOpt_piStar_stable_finite_cost
import Theorems.Thm_CloudCostOpt_piStar_zero_demand

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

theorem cor6_rateX_smul (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (θ : ℝ≥0)
    (i : Fin S.I) : ∀ s l, rateX S sel (θ • lam) i s l = θ * rateX S sel lam i s l := by
  intro s
  induction s with
  | zero =>
    intro l
    simp only [rateX, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  | succ s ih =>
    intro l
    simp only [rateX, ih]
    split_ifs <;> ring

theorem cor6_mu_smul (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (θ : ℝ≥0)
    (j : Fin S.J) : mu S sel (θ • lam) j = (θ : ℝ≥0∞) * mu S sel lam j := by
  unfold mu
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun p => ?_
  split_ifs <;> simp [cor6_rateX_smul, ENNReal.coe_mul]

theorem cor6_F_smul (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (θ : ℝ≥0) :
    (∑ j, ENNReal.ofReal (S.R j) * mu S sel (θ • lam) j +
      ∑ i, ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
        ENNReal.ofReal (S.W i) * (rateX S sel (θ • lam) i (S.δ i + k) l : ℝ≥0∞)) =
    (θ : ℝ≥0∞) * (∑ j, ENNReal.ofReal (S.R j) * mu S sel lam j +
      ∑ i, ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
        ENNReal.ofReal (S.W i) * (rateX S sel lam i (S.δ i + k) l : ℝ≥0∞)) := by
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by rw [cor6_mu_smul]; ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [cor6_rateX_smul, ENNReal.coe_mul]
    ring

theorem cor6_mu_pos (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (i : Fin S.I) : ∃ j : Fin S.J, (lam i : ℝ≥0∞) ≤ mu S sel lam j := by
  classical
  have hL : ¬ S.L i ≤ 0 := by have := hS.one_le_L i; omega
  have hex : ∃ s, sel.jStar i s 0 ≠ 0 := by
    refine ⟨S.δ i, ?_⟩
    simp only [Selection.jStar, lt_self_iff_false, if_false]
    intro h
    have := sel.jLate_pos i
    rw [h, hS.β_idle] at this
    exact lt_irrefl _ this
  have hrow : ∀ s, s ≤ Nat.find hex → rateX S sel lam i s 0 = lam i := by
    intro s
    induction s with
    | zero => intro _; simp [rateX, hL]
    | succ s ih =>
      intro hs
      have hlt : s < Nat.find hex := hs
      have h0 : sel.jStar i s 0 = 0 := by
        have := Nat.find_min hex hlt
        simpa using this
      simp [rateX, hL, h0, hS.β_idle, ih (le_of_lt hlt)]
  have hne : sel.jStar i (Nat.find hex) 0 ≠ 0 := Nat.find_spec hex
  obtain ⟨j, hj⟩ := Fin.exists_succ_eq.2 hne
  refine ⟨j, ?_⟩
  unfold mu
  calc (lam i : ℝ≥0∞)
      = (if (0:ℕ) ≤ Nat.find hex ∧ 0 < S.L i ∧ sel.jStar i (Nat.find hex) 0 = j.succ then
          (rateX S sel lam i (Nat.find hex) 0 : ℝ≥0∞) else 0) := by
        rw [if_pos ⟨Nat.zero_le _, by omega, hj.symm⟩, hrow _ le_rfl]
    _ ≤ ∑' p : ℕ × ℕ, (if p.2 ≤ p.1 ∧ p.2 < S.L i ∧ sel.jStar i p.1 p.2 = j.succ then
          (rateX S sel lam i p.1 p.2 : ℝ≥0∞) else 0) :=
        ENNReal.le_tsum (f := fun p : ℕ × ℕ => (if p.2 ≤ p.1 ∧ p.2 < S.L i ∧
          sel.jStar i p.1 p.2 = j.succ then (rateX S sel lam i p.1 p.2 : ℝ≥0∞) else 0)) (Nat.find hex, 0)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑' p : ℕ × ℕ, (if p.2 ≤ p.1 ∧ p.2 < S.L i' ∧
          sel.jStar i' p.1 p.2 = j.succ then (rateX S sel lam i' p.1 p.2 : ℝ≥0∞) else 0))
          (fun _ _ => by simp) (Finset.mem_univ i)

theorem cor6_avgCost_mono (S : System) (hS : Standing S) (lam : Fin S.I → ℝ≥0) (π : Policy S) :
    avgCost S S.R S.R lam π ≤ avgCost S S.R S.V lam π := by
  unfold avgCost
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun T => ?_)
  refine ENNReal.div_le_div_right ?_ _
  refine Finset.sum_le_sum fun n _ => lintegral_mono fun ω => ?_
  unfold periodCost
  gcongr with j
  first
  | exact ENNReal.ofReal_le_ofReal (hS.R_le_V j)
  | exact hS.R_le_V j

theorem cor6_opt_mono (S : System) (hS : Standing S) (lam : Fin S.I → ℝ≥0) :
    opt S S.R S.R lam ≤ opt S S.R S.V lam := by
  unfold opt
  exact iInf₂_mono fun π _ => cor6_avgCost_mono S hS lam π

theorem cor6_opt_le (S : System) (A B : Fin S.J → ℝ) (lam : Fin S.I → ℝ≥0) (π : Policy S)
    (h : IsStable S lam π) : opt S A B lam ≤ avgCost S A B lam π := by
  unfold opt
  exact iInf₂_le π h

theorem cor6_real_aux (m z : ℝ) (hm0 : 0 ≤ m) :
    ∀ᶠ θ : ℝ≥0 in atTop, 0 ≤ (θ : ℝ) * m + z * √((θ : ℝ) * m) := by
  rcases hm0.eq_or_lt with h0 | hpos
  · refine Filter.Eventually.of_forall fun θ => ?_
    rw [← h0]; simp
  · refine (Filter.eventually_ge_atTop (Real.toNNReal (z ^ 2 / m))).mono fun θ hθ => ?_
    have hθ' : z ^ 2 / m ≤ (θ : ℝ) := Real.toNNReal_le_iff_le_coe.1 hθ
    have hz : z ^ 2 ≤ (θ : ℝ) * m := by
      rw [div_le_iff₀ hpos] at hθ'; linarith
    have habs := Real.abs_le_sqrt hz
    have hx0 : 0 ≤ √((θ : ℝ) * m) := Real.sqrt_nonneg _
    have hsq : √((θ : ℝ) * m) * √((θ : ℝ) * m) = (θ : ℝ) * m :=
      Real.mul_self_sqrt (mul_nonneg θ.2 hm0)
    have h1 : 0 ≤ √((θ : ℝ) * m) + z := by
      have := neg_abs_le z; linarith
    have e : √((θ : ℝ) * m) * (√((θ : ℝ) * m) + z) = (θ : ℝ) * m + z * √((θ : ℝ) * m) := by
      rw [mul_add, hsq]; ring
    rw [← e]; exact mul_nonneg hx0 h1

theorem cor6_hM_eventually (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    ∀ᶠ θ : ℝ≥0 in atTop, ∀ j, 0 ≤ (mu S sel (θ • lam) j).toReal +
        zCoef S j * √((mu S sel (θ • lam) j).toReal) := by
  rw [Filter.eventually_all]
  intro j
  refine (cor6_real_aux (mu S sel lam j).toReal (zCoef S j) ENNReal.toReal_nonneg).mono fun θ h => ?_
  rw [cor6_mu_smul, ENNReal.toReal_mul, ENNReal.coe_toReal]
  exact h

theorem cor6_core (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i)
    (hR : ∀ j, 0 < S.R j) (_hRV : ∀ j, S.R j < S.V j)
    (h89 : ∀ lam' : Fin S.I → ℝ≥0, (∀ i, 0 < lam' i) → opt S S.R S.R lam' =
      ∑ j, ENNReal.ofReal (S.R j) * mu S sel lam' j +
      ∑ i, ∑' k : ℕ, ∑ l ∈ Finset.range (S.L i),
        ENNReal.ofReal (S.W i) * (rateX S sel lam' i (S.δ i + k) l : ℝ≥0∞))
    (h1214 : ∀ lam' : Fin S.I → ℝ≥0, (∀ i, 0 < lam' i) →
      (∀ j, 0 ≤ (mu S sel lam' j).toReal + zCoef S j * √((mu S sel lam' j).toReal)) →
      (avgCost S S.R S.V lam' (piStar S sel lam')).toReal - (opt S S.R S.R lam').toReal ≤
        ∑ j, (S.R j * zCoef S j + S.V j * (√(1 + zCoef S j ^ 2) - zCoef S j) / 2) *
          √((mu S sel lam' j).toReal))
    (hC1 : ∀ lam' : Fin S.I → ℝ≥0, (∀ i, 0 < lam' i) →
      IsStable S lam' (piStar S sel lam') ∧ avgCost S S.R S.V lam' (piStar S sel lam') < ⊤)
    (hC2 : IsStable S 0 (piStar S sel 0) ∧ avgCost S S.R S.V 0 (piStar S sel 0) = 0) :
    let LB : ℝ≥0 → ℝ≥0∞ := fun θ => opt S S.R S.R (θ • lam)
    let OPT : ℝ≥0 → ℝ≥0∞ := fun θ => opt S S.R S.V (θ • lam)
    let fStar : ℝ≥0 → ℝ≥0∞ := fun θ => avgCost S S.R S.V (θ • lam) (piStar S sel (θ • lam))
    let B1 : ℝ := ∑ j, (S.R j * zCoef S j + S.V j * (√(1 + zCoef S j ^ 2) - zCoef S j) / 2) *
      √((mu S sel lam j).toReal)
    -- 1. scaling of the lower bound, and `0 < LB(1) < ∞`
    (∀ θ : ℝ≥0, LB θ = (θ : ℝ≥0∞) * LB 1) ∧ 0 < LB 1 ∧ LB 1 < ⊤ ∧
    -- 2. `π*(θ)` is stable, with finite cost
    (∀ θ : ℝ≥0, IsStable S (θ • lam) (piStar S sel (θ • lam)) ∧ fStar θ < ⊤) ∧
    -- 3. the bounds, under `M^{π*}_j(θ) ≥ 0`
    (∀ θ : ℝ≥0,
      (∀ j, 0 ≤ (mu S sel (θ • lam) j).toReal +
        zCoef S j * √((mu S sel (θ • lam) j).toReal)) →
      LB θ ≤ OPT θ ∧ OPT θ ≤ fStar θ ∧
      (fStar θ).toReal - (LB θ).toReal ≤ √(θ : ℝ) * B1) ∧
    (∀ θ : ℝ≥0, 0 < θ →
      (∀ j, 0 ≤ (mu S sel (θ • lam) j).toReal +
        zCoef S j * √((mu S sel (θ • lam) j).toReal)) →
      ((fStar θ).toReal - (OPT θ).toReal) / (OPT θ).toReal ≤
        ((fStar θ).toReal - (LB θ).toReal) / (OPT θ).toReal ∧
      ((fStar θ).toReal - (LB θ).toReal) / (OPT θ).toReal ≤
        ((fStar θ).toReal - (LB θ).toReal) / (LB θ).toReal ∧
      ((fStar θ).toReal - (LB θ).toReal) / (LB θ).toReal ≤
        B1 / ((LB 1).toReal * √(θ : ℝ))) ∧
    -- 4. asymptotic optimality
    Tendsto (fun θ : ℝ≥0 => ((fStar θ).toReal - (OPT θ).toReal) / (OPT θ).toReal)
      atTop (𝓝 0) ∧
    Tendsto (fun θ : ℝ≥0 => ((fStar θ).toReal - (LB θ).toReal) / (OPT θ).toReal)
      atTop (𝓝 0) ∧
    Tendsto (fun θ : ℝ≥0 => ((fStar θ).toReal - (LB θ).toReal) / (LB θ).toReal)
      atTop (𝓝 0) := by
  intro LB OPT fStar B1
  have hpos : ∀ θ : ℝ≥0, 0 < θ → ∀ i, 0 < (θ • lam) i := fun θ hθ i => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos hθ (hlam i)
  have hone : (1 : ℝ≥0) • lam = lam := one_smul _ _
  have hzero : (0 : ℝ≥0) • lam = 0 := zero_smul _ _
  have hLB1 : LB 1 = opt S S.R S.R lam := by
    show opt S S.R S.R ((1 : ℝ≥0) • lam) = _; rw [hone]
  have hf0 : fStar 0 = 0 := by
    show avgCost S S.R S.V ((0 : ℝ≥0) • lam) (piStar S sel ((0 : ℝ≥0) • lam)) = 0
    rw [hzero]; exact hC2.2
  have hLBscale : ∀ θ : ℝ≥0, LB θ = (θ : ℝ≥0∞) * LB 1 := by
    intro θ
    rcases eq_or_ne θ 0 with h0 | hθ0
    · subst h0
      rw [ENNReal.coe_zero, zero_mul]
      show opt S S.R S.R ((0 : ℝ≥0) • lam) = 0
      rw [hzero]
      exact le_antisymm ((cor6_opt_le S _ _ 0 _ hC2.1).trans
        ((cor6_avgCost_mono S hS 0 _).trans hC2.2.le)) (by simp)
    · rw [hLB1]
      show opt S S.R S.R (θ • lam) = _
      rw [h89 _ (hpos θ (pos_iff_ne_zero.2 hθ0)), h89 _ hlam]
      exact cor6_F_smul S sel lam θ
  have hLB1pos : 0 < LB 1 := by
    rw [hLB1, h89 _ hlam]
    obtain ⟨j, hj⟩ := cor6_mu_pos S hS sel lam ⟨0, hS.I_pos⟩
    have h1 : 0 < ENNReal.ofReal (S.R j) * mu S sel lam j :=
      ENNReal.mul_pos (ENNReal.ofReal_pos.2 (hR j)).ne'
        ((ENNReal.coe_pos.2 (hlam _)).trans_le hj).ne'
    calc 0 < ENNReal.ofReal (S.R j) * mu S sel lam j := h1
      _ ≤ ∑ j, ENNReal.ofReal (S.R j) * mu S sel lam j :=
          Finset.single_le_sum (f := fun j => ENNReal.ofReal (S.R j) * mu S sel lam j)
            (fun _ _ => by simp) (Finset.mem_univ j)
      _ ≤ _ := le_self_add
  have hstab : ∀ θ : ℝ≥0, IsStable S (θ • lam) (piStar S sel (θ • lam)) ∧ fStar θ < ⊤ := by
    intro θ
    rcases eq_or_ne θ 0 with h0 | hθ0
    · subst h0
      refine ⟨?_, by rw [hf0]; exact ENNReal.zero_lt_top⟩
      rw [hzero]; exact hC2.1
    · exact hC1 _ (hpos θ (pos_iff_ne_zero.2 hθ0))
  have hle : ∀ θ : ℝ≥0, LB θ ≤ OPT θ ∧ OPT θ ≤ fStar θ := fun θ =>
    ⟨cor6_opt_mono S hS _, cor6_opt_le S _ _ _ _ (hstab θ).1⟩
  have hLB1top : LB 1 < ⊤ := ((hle 1).1.trans (hle 1).2).trans_lt (hstab 1).2
  have hL1 : 0 < (LB 1).toReal := ENNReal.toReal_pos hLB1pos.ne' hLB1top.ne
  have hgap : ∀ θ : ℝ≥0, (∀ j, 0 ≤ (mu S sel (θ • lam) j).toReal +
        zCoef S j * √((mu S sel (θ • lam) j).toReal)) →
      (fStar θ).toReal - (LB θ).toReal ≤ √(θ : ℝ) * B1 := by
    intro θ hM
    rcases eq_or_ne θ 0 with h0 | hθ0
    · subst h0
      rw [hf0, ENNReal.toReal_zero, NNReal.coe_zero, Real.sqrt_zero, zero_mul]
      linarith [ENNReal.toReal_nonneg (a := LB 0)]
    · refine (h1214 _ (hpos θ (pos_iff_ne_zero.2 hθ0)) hM).trans (le_of_eq ?_)
      show ∑ j, (S.R j * zCoef S j + S.V j * (√(1 + zCoef S j ^ 2) - zCoef S j) / 2) *
          √((mu S sel (θ • lam) j).toReal) = √(θ : ℝ) * ∑ j, (S.R j * zCoef S j +
          S.V j * (√(1 + zCoef S j ^ 2) - zCoef S j) / 2) * √((mu S sel lam j).toReal)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [cor6_mu_smul, ENNReal.toReal_mul, ENNReal.coe_toReal, Real.sqrt_mul' _ ENNReal.toReal_nonneg]
      ring
  have hratio : ∀ θ : ℝ≥0, 0 < θ → (∀ j, 0 ≤ (mu S sel (θ • lam) j).toReal +
        zCoef S j * √((mu S sel (θ • lam) j).toReal)) →
      0 ≤ ((fStar θ).toReal - (OPT θ).toReal) / (OPT θ).toReal ∧
      ((fStar θ).toReal - (OPT θ).toReal) / (OPT θ).toReal ≤
        ((fStar θ).toReal - (LB θ).toReal) / (OPT θ).toReal ∧
      ((fStar θ).toReal - (LB θ).toReal) / (OPT θ).toReal ≤
        ((fStar θ).toReal - (LB θ).toReal) / (LB θ).toReal ∧
      ((fStar θ).toReal - (LB θ).toReal) / (LB θ).toReal ≤
        B1 / ((LB 1).toReal * √(θ : ℝ)) := by
    intro θ hθ hM
    have hfT : fStar θ ≠ ⊤ := (hstab θ).2.ne
    have hoT : OPT θ ≠ ⊤ := ne_top_of_le_ne_top hfT (hle θ).2
    have hbo : (LB θ).toReal ≤ (OPT θ).toReal := ENNReal.toReal_mono hoT (hle θ).1
    have hof : (OPT θ).toReal ≤ (fStar θ).toReal := ENNReal.toReal_mono hfT (hle θ).2
    have hb : (LB θ).toReal = (θ : ℝ) * (LB 1).toReal := by
      rw [hLBscale θ, ENNReal.toReal_mul, ENNReal.coe_toReal]
    have hθr : (0 : ℝ) < θ := NNReal.coe_pos.2 hθ
    have hbpos : 0 < (LB θ).toReal := by rw [hb]; exact mul_pos hθr hL1
    have hg := hgap θ hM
    have hs : 0 < √(θ : ℝ) := Real.sqrt_pos.2 hθr
    have hsq : √(θ : ℝ) * √(θ : ℝ) = θ := Real.mul_self_sqrt hθr.le
    refine ⟨div_nonneg (by linarith) (by linarith),
      div_le_div_of_nonneg_right (by linarith) (by linarith),
      div_le_div_of_nonneg_left (by linarith) hbpos hbo, ?_⟩
    rw [div_le_div_iff₀ hbpos (mul_pos hL1 hs)]
    have h2 := mul_le_mul_of_nonneg_right hg (mul_pos hL1 hs).le
    calc ((fStar θ).toReal - (LB θ).toReal) * ((LB 1).toReal * √(θ : ℝ))
        ≤ √(θ : ℝ) * B1 * ((LB 1).toReal * √(θ : ℝ)) := h2
      _ = B1 * (LB θ).toReal := by rw [hb]; linear_combination (B1 * (LB 1).toReal) * hsq
  have hB : Tendsto (fun θ : ℝ≥0 => B1 / ((LB 1).toReal * √(θ : ℝ))) atTop (𝓝 0) := by
    refine Tendsto.div_atTop tendsto_const_nhds ?_
    refine Tendsto.const_mul_atTop hL1 ?_
    exact Real.tendsto_sqrt_atTop.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have hev := (eventually_gt_atTop (0 : ℝ≥0)).and (cor6_hM_eventually S sel lam)
  refine ⟨hLBscale, hLB1pos, hLB1top, hstab, fun θ hM => ⟨(hle θ).1, (hle θ).2, hgap θ hM⟩,
    fun θ hθ hM => ⟨(hratio θ hθ hM).2.1, (hratio θ hθ hM).2.2.1, (hratio θ hθ hM).2.2.2⟩,
    ?_, ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
      (hev.mono fun θ h => (hratio θ h.1 h.2).1) (hev.mono fun θ h => ?_)
    have r := hratio θ h.1 h.2
    exact r.2.1.trans (r.2.2.1.trans r.2.2.2)
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
      (hev.mono fun θ h => ?_) (hev.mono fun θ h => ?_)
    · have r := hratio θ h.1 h.2
      exact r.1.trans r.2.1
    · have r := hratio θ h.1 h.2
      exact r.2.2.1.trans r.2.2.2
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
      (hev.mono fun θ h => ?_) (hev.mono fun θ h => (hratio θ h.1 h.2).2.2.2)
    have r := hratio θ h.1 h.2
    exact r.1.trans (r.2.1.trans r.2.2.1)

end CloudCostOpt

open CloudCostOpt in
theorem solution (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i)
    (hR : ∀ j, 0 < S.R j) (hRV : ∀ j, S.R j < S.V j) :
    let LB : ℝ≥0 → ℝ≥0∞ := fun θ => opt S S.R S.R (θ • lam)
    let OPT : ℝ≥0 → ℝ≥0∞ := fun θ => opt S S.R S.V (θ • lam)
    let fStar : ℝ≥0 → ℝ≥0∞ := fun θ => avgCost S S.R S.V (θ • lam) (piStar S sel (θ • lam))
    let B1 : ℝ := ∑ j, (S.R j * zCoef S j + S.V j * (√(1 + zCoef S j ^ 2) - zCoef S j) / 2) *
      √((mu S sel lam j).toReal)
    -- 1. scaling of the lower bound, and `0 < LB(1) < ∞`
    (∀ θ : ℝ≥0, LB θ = (θ : ℝ≥0∞) * LB 1) ∧ 0 < LB 1 ∧ LB 1 < ⊤ ∧
    -- 2. `π*(θ)` is stable, with finite cost
    (∀ θ : ℝ≥0, IsStable S (θ • lam) (piStar S sel (θ • lam)) ∧ fStar θ < ⊤) ∧
    -- 3. the bounds, under `M^{π*}_j(θ) ≥ 0`
    (∀ θ : ℝ≥0,
      (∀ j, 0 ≤ (mu S sel (θ • lam) j).toReal +
        zCoef S j * √((mu S sel (θ • lam) j).toReal)) →
      LB θ ≤ OPT θ ∧ OPT θ ≤ fStar θ ∧
      (fStar θ).toReal - (LB θ).toReal ≤ √(θ : ℝ) * B1) ∧
    (∀ θ : ℝ≥0, 0 < θ →
      (∀ j, 0 ≤ (mu S sel (θ • lam) j).toReal +
        zCoef S j * √((mu S sel (θ • lam) j).toReal)) →
      ((fStar θ).toReal - (OPT θ).toReal) / (OPT θ).toReal ≤
        ((fStar θ).toReal - (LB θ).toReal) / (OPT θ).toReal ∧
      ((fStar θ).toReal - (LB θ).toReal) / (OPT θ).toReal ≤
        ((fStar θ).toReal - (LB θ).toReal) / (LB θ).toReal ∧
      ((fStar θ).toReal - (LB θ).toReal) / (LB θ).toReal ≤
        B1 / ((LB 1).toReal * √(θ : ℝ))) ∧
    -- 4. asymptotic optimality
    Tendsto (fun θ : ℝ≥0 => ((fStar θ).toReal - (OPT θ).toReal) / (OPT θ).toReal)
      atTop (𝓝 0) ∧
    Tendsto (fun θ : ℝ≥0 => ((fStar θ).toReal - (LB θ).toReal) / (OPT θ).toReal)
      atTop (𝓝 0) ∧
    Tendsto (fun θ : ℝ≥0 => ((fStar θ).toReal - (LB θ).toReal) / (LB θ).toReal)
      atTop (𝓝 0) := by
  exact CloudCostOpt.cor6_core S hS sel lam hlam hR hRV
    (fun lam' h => (CloudCostOpt.eq_8_9_piHat_optimal S hS sel lam' h).2.2.trans
      (CloudCostOpt.eq_8_9_piHat_optimal S hS sel lam' h).2.1)
    (fun lam' h hM => by
      have h' := CloudCostOpt.eq_12_14_gap_bound S hS sel lam' h hR hRV hM
      dsimp only at h'
      exact h'.2.2.2.2.2.1.trans h'.2.2.2.2.2.2.le)
    (fun lam' h => CloudCostOpt.piStar_stable_finite_cost S hS sel lam' h hR hRV)
    (CloudCostOpt.piStar_zero_demand S hS sel)
