-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.J_abConvex_limits
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:28:39.93661+00:00
-- url     : https://prove2.me/submissions/035fbfba-88ec-42a5-b737-2554b6a9d829

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model

open Filter Topology

namespace GallegoOzerADI.PositiveSetup

theorem aux_Jl_kconv {K : ℝ} {V : ℝ → ℝ} (hV : ABConvex 0 K V) {a z b : ℝ}
    (hab : a < b) (haz : a ≤ z) (hzb : z ≤ b) :
    (b - a) * V z ≤ (b - z) * V a + (z - a) * (K + V b) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have h0 : 0 ≤ (b - z) / (b - a) := div_nonneg (by linarith) hba.le
  have h1 : (b - z) / (b - a) ≤ 1 := (div_le_one hba).mpr (by linarith)
  have h := hV a b hab.le ((b - z) / (b - a)) h0 h1
  have hz : (b - z) / (b - a) * a + (1 - (b - z) / (b - a)) * b = z := by
    field_simp
    ring
  rw [hz, zero_add] at h
  have e1 : (b - a) * ((b - z) / (b - a)) = b - z := by
    field_simp
  have e2 : (b - a) * (1 - (b - z) / (b - a)) = z - a := by
    rw [mul_sub, e1]; ring
  calc (b - a) * V z
      ≤ (b - a) * ((b - z) / (b - a) * V a + (1 - (b - z) / (b - a)) * (K + V b)) :=
        mul_le_mul_of_nonneg_left h hba.le
    _ = ((b - a) * ((b - z) / (b - a))) * V a
          + ((b - a) * (1 - (b - z) / (b - a))) * (K + V b) := by ring
    _ = (b - z) * V a + (z - a) * (K + V b) := by rw [e1, e2]

theorem aux_Jl_iInf_eq {f : ℝ → ℝ} {x c : ℝ} (hlow : ∀ y, x ≤ y → c ≤ f y)
    (hatt : ∃ y, x ≤ y ∧ f y ≤ c) : (⨅ y : {y : ℝ // x ≤ y}, f y) = c := by
  obtain ⟨y0, hy0, hy0c⟩ := hatt
  have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
  apply le_antisymm
  · have hb : BddBelow (Set.range fun y : {y : ℝ // x ≤ y} => f y) :=
      ⟨c, by rintro _ ⟨y, rfl⟩; exact hlow y y.2⟩
    exact (ciInf_le hb ⟨y0, hy0⟩).trans hy0c
  · exact le_ciInf fun y => hlow y y.2

theorem aux_Jl_ind_self (x : ℝ) : setupIndicator (x - x) = 0 := by
  simp [setupIndicator]

theorem aux_Jl_ind_pos {x y : ℝ} (h : x < y) : setupIndicator (y - x) = 1 := by
  unfold setupIndicator
  rw [if_pos (sub_pos.mpr h)]

theorem aux_Jl_ind_nonneg (z : ℝ) : 0 ≤ setupIndicator z := by
  unfold setupIndicator; split_ifs <;> norm_num

theorem aux_Jl_sS (K : ℝ) (hK : 0 < K) (V : ℝ → ℝ) (hV : ABConvex 0 K V)
    (hcont : Continuous V) (S : ℝ) (hS : ∀ x, V S ≤ V x)
    (hiii : ∃ x, x < S ∧ K + V S < V x) :
    ∃ s : ℝ, IsGreatest {x | reorderGap K V x ≤ 0} s ∧
      (∀ x, (x < S ∧ orderCost K V x = K + V S) ↔ x ≤ s) ∧
      ∀ x, orderCost K V x = V (max s x) := by
  -- reorder gap to the left of S
  have hRG1 : ∀ x, x ≤ S → reorderGap K V x = K + V S - V x := by
    intro x hx
    unfold reorderGap
    rw [aux_Jl_iInf_eq (f := V) (fun y _ => hS y) ⟨S, hx, le_rfl⟩]
  -- reorder gap is positive to the right of S
  have hRG2 : ∀ x, S < x → 0 < reorderGap K V x := by
    intro x hSx
    obtain ⟨δ, hδ, hδV⟩ := Metric.continuous_iff.mp hcont x (K / 2) (by linarith)
    have hD : 0 < x + δ - S := by linarith
    have hc : 0 < min (K / 2) (K * δ / (x + δ - S)) :=
      lt_min (by linarith) (div_pos (mul_pos hK hδ) hD)
    have hbound : ∀ y, x ≤ y → V x - K + min (K / 2) (K * δ / (x + δ - S)) ≤ V y := by
      intro y hxy
      by_cases hy : y < x + δ
      · have hd := hδV y (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
        rw [Real.dist_eq, abs_lt] at hd
        have : min (K / 2) (K * δ / (x + δ - S)) ≤ K / 2 := min_le_left _ _
        linarith [hd.1]
      · push Not at hy
        have h := aux_Jl_kconv hV (a := S) (z := x) (b := y) (by linarith) hSx.le hxy
        have hc2 : min (K / 2) (K * δ / (x + δ - S)) ≤ K * δ / (x + δ - S) :=
          min_le_right _ _
        have hyS : 0 < y - S := by linarith
        have h1 : (y - x) * K ≤ (y - S) * (V y - V x + K) := by
          nlinarith [hS y, mul_le_mul_of_nonneg_left (hS y) (by linarith : (0:ℝ) ≤ y - x)]
        have h2 : 0 ≤ (y - S) * ((V y - V x + K) * (x + δ - S) - K * δ) := by
          nlinarith [mul_le_mul_of_nonneg_left h1 hD.le,
            mul_nonneg (mul_nonneg hK.le (by linarith : (0:ℝ) ≤ x - S))
              (by linarith : (0:ℝ) ≤ y - x - δ)]
        have h3 := (mul_nonneg_iff_of_pos_left hyS).mp h2
        have h4 : K * δ / (x + δ - S) ≤ V y - V x + K := by
          rw [div_le_iff₀ hD]; linarith
        linarith
    have hinf : V x - K + min (K / 2) (K * δ / (x + δ - S)) ≤ ⨅ y : {y : ℝ // x ≤ y}, V y := by
      have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
      exact le_ciInf fun y => hbound y y.2
    unfold reorderGap
    linarith
  -- to the right of S, not ordering is optimal
  have hright : ∀ x y, S ≤ x → x ≤ y → V x ≤ K + V y := by
    intro x y hSx hxy
    rcases hSx.eq_or_lt with h | hlt
    · rw [← h]; linarith [hS y]
    · have h := aux_Jl_kconv hV (lt_of_lt_of_le hlt hxy) hlt.le hxy
      have hyS : 0 < y - S := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (by linarith [hS y] : 0 ≤ K + V y - V S)]
  obtain ⟨B, hBdef⟩ : ∃ B : Set ℝ, B = {x | x ≤ S ∧ K + V S ≤ V x} := ⟨_, rfl⟩
  have hmemB : ∀ x, x ∈ B ↔ (x ≤ S ∧ K + V S ≤ V x) := by
    intro x; rw [hBdef]; rfl
  have hAB : {x | reorderGap K V x ≤ 0} = B := by
    ext x
    rw [hmemB, Set.mem_ofPred_eq]
    constructor
    · intro h
      by_cases hx : x ≤ S
      · rw [hRG1 x hx] at h; exact ⟨hx, by linarith⟩
      · exact absurd h (not_le.mpr (hRG2 x (not_le.mp hx)))
    · rintro ⟨hx, hv⟩
      rw [hRG1 x hx]; linarith
  have hBclosed : IsClosed B := by
    have : B = {x | x ≤ S} ∩ {x | K + V S ≤ V x} := by
      ext x; rw [hmemB]; rfl
    rw [this]
    exact (isClosed_le continuous_id continuous_const).inter (isClosed_le continuous_const hcont)
  have hBne : B.Nonempty := by
    obtain ⟨x, hx, hv⟩ := hiii
    exact ⟨x, (hmemB x).mpr ⟨hx.le, hv.le⟩⟩
  have hBbdd : BddAbove B := ⟨S, fun x hx => ((hmemB x).mp hx).1⟩
  obtain ⟨s, hsdef⟩ : ∃ s, s = sSup B := ⟨_, rfl⟩
  have hsB : s ∈ B := hsdef ▸ hBclosed.csSup_mem hBne hBbdd
  have hsB' := (hmemB s).mp hsB
  have hsGreat : IsGreatest B s := ⟨hsB, fun x hx => hsdef ▸ le_csSup hBbdd hx⟩
  have hsS : s < S := by
    rcases hsB'.1.eq_or_lt with h | h
    · exfalso; have := hsB'.2; rw [h] at this; linarith
    · exact h
  have hVs : V s = K + V S := by
    obtain ⟨c, ⟨hsc, hcS⟩, hVc⟩ :=
      intermediate_value_Icc' hsS.le hcont.continuousOn
        (show K + V S ∈ Set.Icc (V S) (V s) from ⟨by linarith, hsB'.2⟩)
    have hcB : c ∈ B := (hmemB c).mpr ⟨hcS, hVc.ge⟩
    have hcs : c = s := le_antisymm (hsGreat.2 hcB) hsc
    rw [← hcs, hVc]
  have hleft : ∀ x, x ≤ s → K + V S ≤ V x := by
    intro x hx
    rcases hx.eq_or_lt with h | hlt
    · rw [h]; exact hsB'.2
    · have h := aux_Jl_kconv hV (lt_trans hlt hsS) hlt.le hsS.le
      rw [hVs] at h
      have hSs : 0 < S - s := by linarith
      nlinarith
  have hOC1 : ∀ x, x ≤ s → orderCost K V x = K + V S := by
    intro x hx
    unfold orderCost
    apply aux_Jl_iInf_eq (f := fun y => K * setupIndicator (y - x) + V y)
    · intro y hxy
      rcases hxy.eq_or_lt with h | hlt
      · rw [← h, aux_Jl_ind_self]; linarith [hleft x hx]
      · rw [aux_Jl_ind_pos hlt]; linarith [hS y]
    · refine ⟨S, hx.trans hsS.le, ?_⟩
      rw [aux_Jl_ind_pos (lt_of_le_of_lt hx hsS)]
      linarith
  have hOC2 : ∀ x, s < x → orderCost K V x = V x := by
    intro x hx
    unfold orderCost
    apply aux_Jl_iInf_eq (f := fun y => K * setupIndicator (y - x) + V y)
    · intro y hxy
      rcases hxy.eq_or_lt with h | hlt
      · rw [← h, aux_Jl_ind_self]; linarith
      · rw [aux_Jl_ind_pos hlt]
        by_cases hxS : x ≤ S
        · have hnot : ¬ (K + V S ≤ V x) := fun h =>
            absurd (hsGreat.2 ((hmemB x).mpr ⟨hxS, h⟩)) (not_le.mpr hx)
          have := not_le.mp hnot
          linarith [hS y]
        · linarith [hright x y (le_of_lt (not_le.mp hxS)) hlt.le]
    · refine ⟨x, le_rfl, ?_⟩
      rw [aux_Jl_ind_self]
      linarith
  refine ⟨s, by rw [hAB]; exact hsGreat, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨hxS, hoc⟩
      by_contra hxs
      push Not at hxs
      rw [hOC2 x hxs] at hoc
      exact absurd (hsGreat.2 ((hmemB x).mpr ⟨hxS.le, hoc.ge⟩)) (not_le.mpr hxs)
    · intro hx
      exact ⟨lt_of_le_of_lt hx hsS, hOC1 x hx⟩
  · intro x
    rcases le_or_gt x s with hx | hx
    · rw [max_eq_left hx, hOC1 x hx, hVs]
    · rw [max_eq_right hx.le, hOC2 x hx]

/-- Single-period structure: `orderCost K V = V ∘ max s`, it is `K`-convex, and `s` is the
largest point where reordering is optimal. -/
theorem aux_Jl_scarf {K : ℝ} (hK : 0 < K) {V : ℝ → ℝ} (hV : ABConvex 0 K V)
    (hcont : Continuous V) (hcoer : Tendsto V (cocompact ℝ) atTop) :
    ∃ s : ℝ, IsGreatest {x | reorderGap K V x ≤ 0} s ∧ (∀ x, orderCost K V x = V (max s x)) ∧
      ABConvex 0 K (orderCost K V) := by
  obtain ⟨S, hS⟩ := hcont.exists_forall_le hcoer
  have hiii : ∃ x, x < S ∧ K + V S < V x := by
    have hbot : Tendsto V atBot atTop := hcoer.mono_left atBot_le_cocompact
    obtain ⟨x, hx1, hx2⟩ :=
      ((hbot.eventually (eventually_gt_atTop (K + V S))).and (eventually_lt_atBot S)).exists
    exact ⟨x, hx2, hx1⟩
  obtain ⟨s, hgr, hiff, heq⟩ := aux_Jl_sS K hK V hV hcont S hS hiii
  have hsS := (hiff s).mpr le_rfl
  have hVs : V s = K + V S := by rw [← hsS.2, heq s, max_self]
  refine ⟨s, hgr, heq, ?_⟩
  intro x₁ x₂ hx θ h0 h1
  rw [heq, heq, heq]
  have hz1 : x₁ ≤ θ * x₁ + (1 - θ) * x₂ := by nlinarith
  have hz2 : θ * x₁ + (1 - θ) * x₂ ≤ x₂ := by nlinarith
  by_cases hs1 : s ≤ x₁
  · rw [max_eq_right hs1, max_eq_right (hs1.trans hz1), max_eq_right (hs1.trans hx)]
    exact hV x₁ x₂ hx θ h0 h1
  by_cases hs2 : x₂ ≤ s
  · rw [max_eq_left hs2, max_eq_left (hz2.trans hs2), max_eq_left (hx.trans hs2)]
    nlinarith
  push Not at hs1 hs2
  rw [max_eq_left hs1.le, max_eq_right hs2.le, hVs]
  by_cases hzs : θ * x₁ + (1 - θ) * x₂ ≤ s
  · rw [max_eq_left hzs, hVs]
    nlinarith [hS x₂, mul_le_mul_of_nonneg_left (hS x₂) (by linarith : (0:ℝ) ≤ 1 - θ)]
  · push Not at hzs
    rw [max_eq_right hzs.le]
    have h := aux_Jl_kconv hV hs2 hzs.le hz2
    rw [hVs] at h
    have hd : 0 ≤ V x₂ - V S := by linarith [hS x₂]
    have hp : 0 ≤ θ * (s - x₁) * (V x₂ - V S) :=
      mul_nonneg (mul_nonneg h0 (by linarith)) hd
    have hxs : 0 < x₂ - s := by linarith
    have key : (x₂ - s) * V (θ * x₁ + (1 - θ) * x₂) ≤
        (x₂ - s) * (θ * (0 + (K + V S)) + (1 - θ) * (K + V x₂)) := by
      nlinarith
    exact le_of_mul_le_mul_left key hxs

theorem aux_Jl_orderCost_le {K : ℝ} (hK : 0 ≤ K) {V : ℝ → ℝ} {m : ℝ} (hm : ∀ y, m ≤ V y)
    (x : ℝ) : orderCost K V x ≤ V x := by
  unfold orderCost
  have hb : BddBelow (Set.range fun y : {y : ℝ // x ≤ y} =>
      K * setupIndicator ((y : ℝ) - x) + V y) := by
    refine ⟨m, ?_⟩
    rintro _ ⟨y, rfl⟩
    have := mul_nonneg hK (aux_Jl_ind_nonneg ((y : ℝ) - x))
    linarith [hm y]
  have := ciInf_le hb ⟨x, le_rfl⟩
  have h0 : setupIndicator 0 = 0 := by simp [setupIndicator]
  simpa [h0] using this

section ModelPart

open MeasureTheory

variable {L M : ℕ}

theorem aux_Jl_obs_le (o : Fin M → ℝ) (i : ℕ) : |obsComp o i| ≤ ∑ j, |o j| := by
  unfold obsComp
  split_ifs with h
  · exact Finset.single_le_sum (f := fun j => |o j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ _)
  · simp only [abs_zero]; exact Finset.sum_nonneg (fun j _ => abs_nonneg _)

theorem aux_Jl_obs_meas (i : ℕ) : Measurable (fun o : Fin M → ℝ => obsComp o i) := by
  by_cases h : i < M
  · simp only [obsComp, h, dif_pos]
    exact measurable_pi_apply _
  · simp only [obsComp, h, dif_neg, not_false_eq_true]
    exact measurable_const

theorem aux_Jl_ind_meas : Measurable setupIndicator := by
  unfold setupIndicator
  exact Measurable.ite measurableSet_Ioi measurable_const measurable_const

theorem aux_Jl_meas_next :
    Measurable (fun p : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
      (nextX p.1.1 p.1.2 p.2, nextO p.1.2 p.2)) := by
  apply Measurable.prodMk
  · unfold nextX
    apply Measurable.sub
    · apply Measurable.sub measurable_fst.fst
      exact Finset.measurable_sum _ (fun k _ => (measurable_pi_apply _).comp measurable_snd)
    · exact (aux_Jl_obs_meas 0).comp measurable_fst.snd
  · unfold nextO
    apply measurable_pi_lambda
    intro j
    exact ((aux_Jl_obs_meas _).comp measurable_fst.snd).add
      ((measurable_pi_apply _).comp measurable_snd)

/-- An integrable envelope of the demand components entering the transitions. -/
noncomputable def aux_Jl_W (D : Fin (L + M + 2) → ℝ) : ℝ :=
  ∑ k : Fin (L + 2), |D (Fin.castLE (by omega) k)| +
    ∑ j : Fin M, |D ⟨L + 2 + j.val, by have := j.isLt; omega⟩|

theorem aux_Jl_W_int (μ : Measure (Fin (L + M + 2) → ℝ))
    (hμi : ∀ k, Integrable (fun D : Fin (L + M + 2) → ℝ => D k) μ) :
    Integrable (fun D => aux_Jl_W (L := L) (M := M) D) μ := by
  unfold aux_Jl_W
  refine Integrable.add ?_ ?_
  · exact integrable_finsetSum _ (fun k _ => (hμi _).abs)
  · exact integrable_finsetSum _ (fun j _ => (hμi _).abs)

theorem aux_Jl_next_bound (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    |nextX y o D| + ∑ j, |nextO o D j| ≤ |y| + (M + 1) * ∑ j, |o j| + aux_Jl_W D := by
  have h1 : |nextX y o D| ≤
      |y| + ∑ k : Fin (L + 2), |D (Fin.castLE (by omega) k)| + ∑ j, |o j| := by
    unfold nextX
    have ha := Finset.abs_sum_le_sum_abs
      (fun k : Fin (L + 2) => D (Fin.castLE (by omega) k)) Finset.univ
    have hb := aux_Jl_obs_le o 0
    rw [abs_le]
    constructor
    · linarith [le_abs_self y, neg_abs_le y,
        le_abs_self (∑ k : Fin (L + 2), D (Fin.castLE (by omega) k)),
        neg_abs_le (∑ k : Fin (L + 2), D (Fin.castLE (by omega) k)),
        le_abs_self (obsComp o 0), neg_abs_le (obsComp o 0)]
    · linarith [le_abs_self y, neg_abs_le y,
        le_abs_self (∑ k : Fin (L + 2), D (Fin.castLE (by omega) k)),
        neg_abs_le (∑ k : Fin (L + 2), D (Fin.castLE (by omega) k)),
        le_abs_self (obsComp o 0), neg_abs_le (obsComp o 0)]
  have e : ∀ j : Fin M, |nextO o D j| ≤
      ∑ i, |o i| + |D ⟨L + 2 + j.val, by have := j.isLt; omega⟩| := by
    intro j
    unfold nextO
    exact (abs_add_le _ _).trans (by linarith [aux_Jl_obs_le o (j.val + 1)])
  have h2 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => e j)
  rw [Finset.sum_add_distrib] at h2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  unfold aux_Jl_W
  linarith

/-- The inductive invariant of the value functions. -/
def aux_Jl_Good (c : ℝ) (F : ℝ → (Fin M → ℝ) → ℝ) : Prop :=
  Measurable (Function.uncurry F) ∧ (∀ o, ABConvex 0 c (fun x => F x o)) ∧
    (∀ o, Continuous (fun x => F x o)) ∧ (∃ m, ∀ x o, m ≤ F x o) ∧
    (∃ A B, 0 ≤ B ∧ ∀ x o, F x o ≤ A + B * (|x| + ∑ j, |o j|))

theorem aux_Jl_orderCost_rat {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ} (hf : Continuous f) {m : ℝ}
    (hm : ∀ y, m ≤ f y) (x : ℝ) :
    orderCost K f x = ⨅ q : ℚ, (K * setupIndicator (max x (q : ℝ) - x) + f (max x q)) := by
  unfold orderCost
  have hTm : ∀ y, m ≤ K * setupIndicator (y - x) + f y := fun y => by
    have := mul_nonneg hK (aux_Jl_ind_nonneg (y - x)); linarith [hm y]
  have hb1 : BddBelow (Set.range fun y : {y : ℝ // x ≤ y} =>
      K * setupIndicator ((y : ℝ) - x) + f y) :=
    ⟨m, by rintro _ ⟨y, rfl⟩; exact hTm y⟩
  have hb2 : BddBelow (Set.range fun q : ℚ =>
      K * setupIndicator (max x (q : ℝ) - x) + f (max x q)) :=
    ⟨m, by rintro _ ⟨q, rfl⟩; exact hTm _⟩
  have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
  apply le_antisymm
  · exact le_ciInf fun q => ciInf_le hb1 ⟨max x q, le_max_left _ _⟩
  · refine le_ciInf fun y => ?_
    obtain ⟨y, hy⟩ := y
    rcases hy.eq_or_lt with h | h
    · subst h
      obtain ⟨q, hq⟩ := exists_rat_lt x
      have := ciInf_le hb2 q
      rw [max_eq_left hq.le] at this
      exact this
    · apply le_of_forall_pos_lt_add
      intro ε hε
      obtain ⟨δ, hδ, hδf⟩ := Metric.continuous_iff.mp hf y ε hε
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt h (sub_lt_self y hδ))
      have hxq : x < q := lt_of_le_of_lt (le_max_left _ _) hq1
      have hq3 : y - δ < q := lt_of_le_of_lt (le_max_right _ _) hq1
      have hfq := hδf q (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rw [Real.dist_eq, abs_lt] at hfq
      have := ciInf_le hb2 q
      rw [max_eq_right hxq.le, aux_Jl_ind_pos hxq] at this
      show _ < K * setupIndicator (y - x) + f y + ε
      rw [aux_Jl_ind_pos h]
      linarith

theorem aux_Jl_stage (G : ℝ → ℝ) (hGc : ConvexOn ℝ Set.univ G)
    (hGco : Tendsto G (cocompact ℝ) atTop) (hGl : ∃ a b : ℝ, ∀ y, |G y| ≤ a + b * |y|)
    (K α c : ℝ) (hK : 0 < K) (hα : 0 < α) (hαc : α * c ≤ K)
    (μ : Measure (Fin (L + M + 2) → ℝ)) [IsProbabilityMeasure μ]
    (hμi : ∀ k, Integrable (fun D : Fin (L + M + 2) → ℝ => D k) μ)
    (F : ℝ → (Fin M → ℝ) → ℝ) (hF : aux_Jl_Good c F) :
    (∀ o, ABConvex 0 K (fun y => G y + α * ∫ D, F (nextX y o D) (nextO o D) ∂μ) ∧
      Continuous (fun y => G y + α * ∫ D, F (nextX y o D) (nextO o D) ∂μ) ∧
      Tendsto (fun y => G y + α * ∫ D, F (nextX y o D) (nextO o D) ∂μ) (cocompact ℝ) atTop) ∧
    aux_Jl_Good K (fun x o =>
      orderCost K (fun y => G y + α * ∫ D, F (nextX y o D) (nextO o D) ∂μ) x) := by
  obtain ⟨hmeas, hconv, hcont, ⟨m, hm⟩, ⟨A, B, hB, hAB⟩⟩ := hF
  obtain ⟨a, b, hab⟩ := hGl
  have hGcont : Continuous G := continuousOn_univ.mp (hGc.continuousOn isOpen_univ)
  obtain ⟨E, hE⟩ : ∃ E : ℝ → (Fin M → ℝ) → ℝ,
      E = fun y o => ∫ D, F (nextX y o D) (nextO o D) ∂μ := ⟨_, rfl⟩
  have hEy : ∀ y o, ∫ D, F (nextX y o D) (nextO o D) ∂μ = E y o := by
    intro y o; rw [hE]
  simp only [hEy]
  -- pointwise bound
  have hFabs : ∀ x o, |F x o| ≤ (|m| + |A|) + B * (|x| + ∑ j, |o j|) := by
    intro x o
    have h0 : 0 ≤ B * (|x| + ∑ j, |o j|) :=
      mul_nonneg hB (add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ => abs_nonneg _))
    rw [abs_le]; constructor
    · linarith [hm x o, neg_abs_le m, abs_nonneg A]
    · linarith [hAB x o, le_abs_self A, abs_nonneg m]
  have hFb : ∀ y o (D : Fin (L + M + 2) → ℝ), |F (nextX y o D) (nextO o D)| ≤
      (|m| + |A|) + B * (|y| + (M + 1) * ∑ j, |o j| + aux_Jl_W D) := by
    intro y o D
    have h1 := hFabs (nextX y o D) (nextO o D)
    have h2 := mul_le_mul_of_nonneg_left (aux_Jl_next_bound y o D) hB
    linarith
  have hWi := aux_Jl_W_int μ hμi
  have hgi : ∀ X : ℝ, Integrable (fun (D : Fin (L + M + 2) → ℝ) =>
      (|m| + |A|) + B * (X + aux_Jl_W D)) μ := fun X =>
    (integrable_const _).add (((integrable_const _).add hWi).const_mul B)
  have hmeasI : ∀ y o, Measurable (fun (D : Fin (L + M + 2) → ℝ) =>
      F (nextX y o D) (nextO o D)) := fun y o => by
    have h1 := hmeas.comp (aux_Jl_meas_next (L := L) (M := M))
    have h2 : Measurable (fun D : Fin (L + M + 2) → ℝ => (((y, o) : ℝ × (Fin M → ℝ)), D)) :=
      measurable_const.prodMk measurable_id
    exact h1.comp h2
  have hint : ∀ y o, Integrable (fun (D : Fin (L + M + 2) → ℝ) => F (nextX y o D) (nextO o D)) μ := by
    intro y o
    refine Integrable.mono' (hgi (|y| + (M + 1) * ∑ j, |o j|))
      (hmeasI y o).aestronglyMeasurable (ae_of_all _ fun D => ?_)
    rw [Real.norm_eq_abs]; exact hFb y o D
  have hElow : ∀ y o, m ≤ E y o := by
    intro y o
    have := integral_mono (integrable_const m) (hint y o) (fun D => hm _ _)
    rw [← hEy]
    simpa using this
  have hEup : ∀ y o, E y o ≤
      (|m| + |A|) + B * (|y| + (M + 1) * ∑ j, |o j| + ∫ D, aux_Jl_W D ∂μ) := by
    intro y o
    have := integral_mono (hint y o) (hgi (|y| + (M + 1) * ∑ j, |o j|))
      (fun D => (le_abs_self _).trans (hFb y o D))
    have i1 : Integrable (fun D : Fin (L + M + 2) → ℝ =>
        (|y| + (M + 1) * ∑ j, |o j|) + aux_Jl_W D) μ := (integrable_const _).add hWi
    have i2 : Integrable (fun D : Fin (L + M + 2) → ℝ =>
        B * ((|y| + (M + 1) * ∑ j, |o j|) + aux_Jl_W D)) μ := i1.const_mul B
    rw [integral_add (integrable_const _) i2, integral_const_mul,
      integral_add (integrable_const _) hWi] at this
    rw [← hEy]
    simpa using this
  have hEconv : ∀ o, ABConvex 0 c (fun y => E y o) := by
    intro o x₁ x₂ hx θ h0 h1
    have hpt : ∀ (D : Fin (L + M + 2) → ℝ), F (nextX (θ * x₁ + (1 - θ) * x₂) o D) (nextO o D) ≤
        θ * (0 + F (nextX x₁ o D) (nextO o D)) +
          (1 - θ) * (c + F (nextX x₂ o D) (nextO o D)) := by
      intro D
      have h := hconv (nextO o D) (nextX x₁ o D) (nextX x₂ o D)
        (by unfold nextX; linarith) θ h0 h1
      have heq : θ * nextX x₁ o D + (1 - θ) * nextX x₂ o D =
          nextX (θ * x₁ + (1 - θ) * x₂) o D := by unfold nextX; ring
      rw [heq] at h; exact h
    have h1' := hint x₁ o
    have h2' := hint x₂ o
    have hA : Integrable (fun (D : Fin (L + M + 2) → ℝ) =>
        θ * (0 + F (nextX x₁ o D) (nextO o D))) μ :=
      ((integrable_const _).add h1').const_mul θ
    have hB' : Integrable (fun (D : Fin (L + M + 2) → ℝ) =>
        (1 - θ) * (c + F (nextX x₂ o D) (nextO o D))) μ :=
      ((integrable_const _).add h2').const_mul (1 - θ)
    have hAB' : Integrable (fun (D : Fin (L + M + 2) → ℝ) =>
        θ * (0 + F (nextX x₁ o D) (nextO o D)) +
          (1 - θ) * (c + F (nextX x₂ o D) (nextO o D))) μ := hA.add hB'
    have := integral_mono (hint _ o) hAB' hpt
    rw [integral_add hA hB', integral_const_mul, integral_const_mul,
      integral_add (integrable_const _) h1', integral_add (integrable_const _) h2'] at this
    simp only [← hEy]
    simpa using this
  have hEcont : ∀ o, Continuous (fun y => E y o) := by
    intro o
    simp only [← hEy]
    refine continuous_iff_continuousAt.mpr fun y₀ => ?_
    refine continuousAt_of_dominated
      (bound := fun (D : Fin (L + M + 2) → ℝ) =>
        (|m| + |A|) + B * (((|y₀| + 1) + (M + 1) * ∑ j, |o j|) + aux_Jl_W D))
      ?_ ?_ (hgi _) ?_
    · exact Eventually.of_forall fun y => (hmeasI y o).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds y₀ one_pos] with y hy
      refine ae_of_all _ fun D => ?_
      rw [Real.norm_eq_abs]
      have hy' : |y| ≤ |y₀| + 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at hy
        have := abs_sub_abs_le_abs_sub y y₀
        linarith
      have h1 := hFb y o D
      have h2 : B * (|y| + (M + 1) * ∑ j, |o j| + aux_Jl_W D) ≤
          B * (((|y₀| + 1) + (M + 1) * ∑ j, |o j|) + aux_Jl_W D) :=
        mul_le_mul_of_nonneg_left (by linarith) hB
      linarith
    · refine ae_of_all _ fun D => ?_
      have : Continuous fun y => nextX y o D := by unfold nextX; fun_prop
      exact ((hcont (nextO o D)).comp this).continuousAt
  have hVco : ∀ o, Tendsto (fun y => G y + α * E y o) (cocompact ℝ) atTop := by
    intro o
    refine tendsto_atTop_mono (fun y => ?_) (tendsto_atTop_add_const_right _ (α * m) hGco)
    have := mul_le_mul_of_nonneg_left (hElow y o) hα.le
    linarith
  have hVconv : ∀ o, ABConvex 0 K (fun y => G y + α * E y o) := by
    intro o x₁ x₂ hx θ h0 h1
    have hG := hGc.2 (Set.mem_univ x₁) (Set.mem_univ x₂) h0 (by linarith : (0:ℝ) ≤ 1 - θ)
      (by ring : θ + (1 - θ) = 1)
    simp only [smul_eq_mul] at hG
    have hEc := hEconv o x₁ x₂ hx θ h0 h1
    simp only at hEc ⊢
    have h3 := mul_le_mul_of_nonneg_left hEc hα.le
    have h4 := mul_le_mul_of_nonneg_left hαc (by linarith : (0:ℝ) ≤ 1 - θ)
    linarith
  have hVcont : ∀ o, Continuous (fun y => G y + α * E y o) := fun o =>
    hGcont.add (continuous_const.mul (hEcont o))
  obtain ⟨y0, hy0⟩ := hGcont.exists_forall_le hGco
  have hVlow : ∀ y o, G y0 + α * m ≤ G y + α * E y o := by
    intro y o
    have := mul_le_mul_of_nonneg_left (hElow y o) hα.le
    linarith [hy0 y]
  refine ⟨fun o => ⟨hVconv o, hVcont o, hVco o⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- measurability
    have hΦ : StronglyMeasurable (fun q : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
        F (nextX q.1.1 q.1.2 q.2) (nextO q.1.2 q.2)) :=
      (hmeas.comp aux_Jl_meas_next).stronglyMeasurable
    have hI := hΦ.integral_prod_right' (ν := μ)
    have hVmeas : Measurable (fun p : ℝ × (Fin M → ℝ) => G p.1 + α * E p.1 p.2) := by
      have : (fun p : ℝ × (Fin M → ℝ) => G p.1 + α * E p.1 p.2) =
          fun p => G p.1 + α * ∫ D, F (nextX p.1 p.2 D) (nextO p.2 D) ∂μ := by
        funext p; rw [hEy]
      rw [this]
      exact (hGcont.measurable.comp measurable_fst).add (hI.measurable.const_mul α)
    have hJ : Function.uncurry (fun x o => orderCost K (fun y => G y + α * E y o) x) =
        fun p : ℝ × (Fin M → ℝ) => ⨅ q : ℚ, (K * setupIndicator (max p.1 (q : ℝ) - p.1) +
          (G (max p.1 (q : ℝ)) + α * E (max p.1 (q : ℝ)) p.2)) := by
      funext p
      exact aux_Jl_orderCost_rat hK.le (hVcont p.2) (fun y => hVlow y p.2) p.1
    rw [hJ]
    refine Measurable.iInf fun q => ?_
    have hmx : Measurable (fun p : ℝ × (Fin M → ℝ) => max p.1 (q : ℝ)) :=
      measurable_fst.max measurable_const
    exact (measurable_const.mul (aux_Jl_ind_meas.comp (hmx.sub measurable_fst))).add
      (hVmeas.comp (hmx.prodMk measurable_snd))
  · intro o
    obtain ⟨s, -, -, hc⟩ := aux_Jl_scarf hK (hVconv o) (hVcont o) (hVco o)
    exact hc
  · intro o
    obtain ⟨s, -, heq, -⟩ := aux_Jl_scarf hK (hVconv o) (hVcont o) (hVco o)
    have : (fun x => orderCost K (fun y => G y + α * E y o) x) =
        fun x => G (max s x) + α * E (max s x) o := funext heq
    rw [this]
    exact (hVcont o).comp (continuous_const.max continuous_id)
  · refine ⟨G y0 + α * m, fun x o => ?_⟩
    obtain ⟨s, -, heq, -⟩ := aux_Jl_scarf hK (hVconv o) (hVcont o) (hVco o)
    show G y0 + α * m ≤ orderCost K (fun y => G y + α * E y o) x
    rw [heq]
    exact hVlow _ o
  · refine ⟨a + α * (|m| + |A|) + α * B * ∫ D, aux_Jl_W D ∂μ, |b| + α * B * (M + 1),
      add_nonneg (abs_nonneg b) (mul_nonneg (mul_nonneg hα.le hB) (by positivity)), ?_⟩
    intro x o
    have hle := aux_Jl_orderCost_le hK.le (fun y => hVlow y o) x
    have hS : 0 ≤ ∑ j, |o j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have h1 := mul_le_mul_of_nonneg_left (hEup x o) hα.le
    have h2 : G x ≤ a + |b| * |x| := by
      have := hab x
      have := mul_le_mul_of_nonneg_right (le_abs_self b) (abs_nonneg x)
      linarith [le_abs_self (G x)]
    have h3 : 0 ≤ α * B * M * |x| :=
      mul_nonneg (mul_nonneg (mul_nonneg hα.le hB) (Nat.cast_nonneg M)) (abs_nonneg x)
    have h4 : 0 ≤ |b| * ∑ j, |o j| := mul_nonneg (abs_nonneg b) hS
    simp only at hle ⊢
    nlinarith

theorem aux_Jl_zero (c : ℝ) (hc : 0 ≤ c) : aux_Jl_Good (M := M) c (fun _ _ => 0) := by
  refine ⟨measurable_const, fun o => ?_, fun o => continuous_const, ⟨0, fun _ _ => le_rfl⟩,
    ⟨0, 0, le_rfl, fun x o => by simp⟩⟩
  intro x₁ x₂ _ θ h0 h1
  simp only
  nlinarith

theorem aux_Jl_ind (P : Model L M) :
    ∀ n, n ≤ P.T → aux_Jl_Good (P.K (P.T + 1 - n)) (P.Jgo n)
  | 0, _ => by
    have hJ : P.Jgo 0 = fun _ _ => 0 := by
      funext x o; simp only [Model.Jgo]
    rw [hJ]
    exact aux_Jl_zero _ (P.K_pos _).le
  | n + 1, h => by
    have ih := aux_Jl_ind P n (by omega)
    have e : P.T + 1 - n = P.T - n + 1 := by omega
    rw [e] at ih
    have := P.μ_prob (P.T - n)
    have st := aux_Jl_stage (P.G (P.T - n)) (P.G_convex _) (P.G_coercive _)
      (P.G_linearGrowth _) (P.K (P.T - n)) (P.α (P.T - n + 1)) (P.K (P.T - n + 1))
      (P.K_pos _) (P.α_pos _) (P.discount_setup _) (P.μ (P.T - n)) (P.μ_integrable _)
      (P.Jgo n) ih
    have e2 : P.T + 1 - (n + 1) = P.T - n := by omega
    rw [e2]
    have hJ : P.Jgo (n + 1) = fun x o => orderCost (P.K (P.T - n))
        (fun y => P.G (P.T - n) y + P.α (P.T - n + 1) *
          ∫ D, P.Jgo n (nextX y o D) (nextO o D) ∂(P.μ (P.T - n))) x := by
      funext x o; simp only [Model.Jgo]
    rw [hJ]
    exact st.2

end ModelPart

end GallegoOzerADI.PositiveSetup

open GallegoOzerADI.PositiveSetup
open Filter Topology

theorem solution {L M : ℕ} [NeZero M] (P : Model L M) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ABConvex 0 (P.K t) (fun x => P.J t x o) ∧
      Tendsto (fun x => P.J t x o) atTop atTop ∧
      ∃ s : ℝ, IsGreatest {x | P.H t x o ≤ 0} s ∧
        Tendsto (fun x => P.J t x o) atBot (𝓝 (P.V t s o)) := by
  have hgood : aux_Jl_Good (P.K (t + 1)) (P.J (t + 1)) := by
    have h := aux_Jl_ind P (P.T - t) (by omega)
    have e1 : P.T + 1 - (P.T - t) = t + 1 := by omega
    have e2 : P.T + 1 - (t + 1) = P.T - t := by omega
    rw [e1] at h
    unfold Model.J
    rw [e2]
    exact h
  have := P.μ_prob t
  have st := aux_Jl_stage (P.G t) (P.G_convex t) (P.G_coercive t) (P.G_linearGrowth t)
    (P.K t) (P.α (t + 1)) (P.K (t + 1)) (P.K_pos t) (P.α_pos _) (P.discount_setup t)
    (P.μ t) (P.μ_integrable t) (P.J (t + 1)) hgood
  obtain ⟨hVc, hVcont, hVco⟩ := st.1 o
  have hVc' : ABConvex 0 (P.K t) (fun y => P.V t y o) := hVc
  have hVcont' : Continuous (fun y => P.V t y o) := hVcont
  have hVco' : Tendsto (fun y => P.V t y o) (cocompact ℝ) atTop := hVco
  obtain ⟨s, hgr, heq, hconv⟩ := aux_Jl_scarf (P.K_pos t) hVc' hVcont' hVco'
  have hJ' : (fun x => P.J t x o) = orderCost (P.K t) (fun y => P.V t y o) := by
    funext x; exact P.J_eq t ht₁ htT x o
  have hJ : (fun x => P.J t x o) = fun x => P.V t (max s x) o := by
    rw [hJ']; funext x; exact heq x
  refine ⟨?_, ?_, s, hgr, ?_⟩
  · rw [hJ']; exact hconv
  · rw [hJ]
    have htop : Tendsto (fun y => P.V t y o) atTop atTop := hVco'.mono_left atTop_le_cocompact
    refine htop.congr' ?_
    filter_upwards [eventually_ge_atTop s] with x hx
    rw [max_eq_right hx]
  · rw [hJ]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_le_atBot s] with x hx
    rw [max_eq_left hx]
