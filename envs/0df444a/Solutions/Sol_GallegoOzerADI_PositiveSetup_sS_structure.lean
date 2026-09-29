-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.sS_structure
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:05:15.3258+00:00
-- url     : https://prove2.me/submissions/80ecb74d-638e-4b0a-b376-a0a1f467a0ba

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost

namespace GallegoOzerADI.PositiveSetup

theorem aux_sS_kconv {K : ℝ} {V : ℝ → ℝ} (hV : ABConvex 0 K V) {a z b : ℝ}
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

theorem aux_sS_iInf_eq {f : ℝ → ℝ} {x c : ℝ} (hlow : ∀ y, x ≤ y → c ≤ f y)
    (hatt : ∃ y, x ≤ y ∧ f y ≤ c) : (⨅ y : {y : ℝ // x ≤ y}, f y) = c := by
  obtain ⟨y0, hy0, hy0c⟩ := hatt
  have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
  apply le_antisymm
  · have hb : BddBelow (Set.range fun y : {y : ℝ // x ≤ y} => f y) :=
      ⟨c, by rintro _ ⟨y, rfl⟩; exact hlow y y.2⟩
    exact (ciInf_le hb ⟨y0, hy0⟩).trans hy0c
  · exact le_ciInf fun y => hlow y y.2

theorem aux_sS_ind_self (x : ℝ) : setupIndicator (x - x) = 0 := by
  simp [setupIndicator]

theorem aux_sS_ind_pos {x y : ℝ} (h : x < y) : setupIndicator (y - x) = 1 := by
  unfold setupIndicator
  rw [if_pos (sub_pos.mpr h)]

end GallegoOzerADI.PositiveSetup

open GallegoOzerADI.PositiveSetup

theorem solution (K : ℝ) (hK : 0 < K) (V : ℝ → ℝ) (hV : ABConvex 0 K V)
    (hcont : Continuous V) (S : ℝ) (hS : ∀ x, V S ≤ V x)
    (hiii : ∃ x, x < S ∧ K + V S < V x) :
    ∃ s : ℝ, IsGreatest {x | reorderGap K V x ≤ 0} s ∧
      (∀ x, (x < S ∧ orderCost K V x = K + V S) ↔ x ≤ s) ∧
      ∀ x, orderCost K V x = V (max s x) := by
  -- reorder gap to the left of S
  have hRG1 : ∀ x, x ≤ S → reorderGap K V x = K + V S - V x := by
    intro x hx
    unfold reorderGap
    rw [aux_sS_iInf_eq (f := V) (fun y _ => hS y) ⟨S, hx, le_rfl⟩]
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
        have h := aux_sS_kconv hV (a := S) (z := x) (b := y) (by linarith) hSx.le hxy
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
    · have h := aux_sS_kconv hV (lt_of_lt_of_le hlt hxy) hlt.le hxy
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
    · have h := aux_sS_kconv hV (lt_trans hlt hsS) hlt.le hsS.le
      rw [hVs] at h
      have hSs : 0 < S - s := by linarith
      nlinarith
  have hOC1 : ∀ x, x ≤ s → orderCost K V x = K + V S := by
    intro x hx
    unfold orderCost
    apply aux_sS_iInf_eq (f := fun y => K * setupIndicator (y - x) + V y)
    · intro y hxy
      rcases hxy.eq_or_lt with h | hlt
      · rw [← h, aux_sS_ind_self]; linarith [hleft x hx]
      · rw [aux_sS_ind_pos hlt]; linarith [hS y]
    · refine ⟨S, hx.trans hsS.le, ?_⟩
      rw [aux_sS_ind_pos (lt_of_le_of_lt hx hsS)]
      linarith
  have hOC2 : ∀ x, s < x → orderCost K V x = V x := by
    intro x hx
    unfold orderCost
    apply aux_sS_iInf_eq (f := fun y => K * setupIndicator (y - x) + V y)
    · intro y hxy
      rcases hxy.eq_or_lt with h | hlt
      · rw [← h, aux_sS_ind_self]; linarith
      · rw [aux_sS_ind_pos hlt]
        by_cases hxS : x ≤ S
        · have hnot : ¬ (K + V S ≤ V x) := fun h =>
            absurd (hsGreat.2 ((hmemB x).mpr ⟨hxS, h⟩)) (not_le.mpr hx)
          have := not_le.mp hnot
          linarith [hS y]
        · linarith [hright x y (le_of_lt (not_le.mp hxS)) hlt.le]
    · refine ⟨x, le_rfl, ?_⟩
      rw [aux_sS_ind_self]
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
