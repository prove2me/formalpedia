-- Prove2me | solution 1 for EngageInfo.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T20:38:01.569375+00:00
-- url     : https://prove2.me/submissions/4df8bda9-6326-40c4-be51-348ea1379b38

import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_vstar
import Definitions.Def_EngageInfo_designs
import Definitions.Def_EngageInfo_designValue
import Theorems.Thm_EngageInfo_eq_6_vstar
import Theorems.Thm_EngageInfo_eq_3_bayes_plausibility
import Theorems.Thm_EngageInfo_concave_closure_segments
import Theorems.Thm_EngageInfo_eq_8_concavification

namespace Aux_EngageInfo_prop1
open EngageInfo

lemma Θ_pos (M : Params) : 0 < M.Θ := by unfold Params.Θ; linarith [M.θL_lt_θH]
lemma ebar_pos (M : Params) : 0 < M.ebar := by linarith [M.k_pos, M.k_lt_ebar]

lemma α₀_pos (M : Params) : 0 < M.α₀ := by
  unfold Params.α₀ Params.alpha
  exact div_pos (by linarith [M.c_lt_θL]) (by linarith [M.c_lt_θL, M.θL_lt_θH])

lemma α₀_lt_αbar (M : Params) : M.α₀ < M.αbar := by
  unfold Params.α₀ Params.αbar Params.alpha
  have hd0 : 0 < M.θH + 0 - M.c := by linarith [M.c_lt_θL, M.θL_lt_θH]
  have hd1 : 0 < M.θH + M.ebar - M.c := by linarith [M.c_lt_θL, M.θL_lt_θH, ebar_pos M]
  rw [div_lt_div_iff₀ hd0 hd1]
  nlinarith [M.θL_lt_θH, ebar_pos M]

lemma αbar_lt_one (M : Params) : M.αbar < 1 := by
  unfold Params.αbar Params.alpha
  have hd1 : 0 < M.θH + M.ebar - M.c := by linarith [M.c_lt_θL, M.θL_lt_θH, ebar_pos M]
  rw [div_lt_one hd1]
  linarith [M.θL_lt_θH]

lemma m_bounds (M : Params) (hα : M.α₁ < M.αbar) :
    0 < M.m ∧ M.m < M.αbar ∧ M.αbar < 1 :=
  ⟨lt_of_lt_of_le (α₀_pos M) (le_max_left _ _), max_lt (α₀_lt_αbar M) hα, αbar_lt_one M⟩

lemma vstar_0 (M : Params) (hα : M.α₁ < M.αbar) : vstar M 0 = M.θL - M.c := by
  obtain ⟨hm_pos, _, _⟩ := m_bounds M hα
  rw [(eq_6_vstar M 0 ⟨le_rfl, zero_le_one⟩).2, if_neg (by intro h; linarith [h.1])]
  simp only [zero_mul]
  exact max_eq_left (by linarith [M.c_lt_θL])

lemma vstar_mid (M : Params) {α : ℝ} (hα_mem : α ∈ Set.Icc (0 : ℝ) 1)
    (hm : M.m ≤ α ∧ α ≤ M.αbar) : vstar M α = M.θL + M.ebar - M.c := by
  rw [(eq_6_vstar M α hα_mem).2, if_pos hm]

lemma vstar_1 (M : Params) (hα : M.α₁ < M.αbar) : vstar M 1 = M.θH - M.c := by
  obtain ⟨_, _, hbar_lt⟩ := m_bounds M hα
  rw [(eq_6_vstar M 1 ⟨zero_le_one, le_rfl⟩).2, if_neg (by intro h; linarith [h.2])]
  simp only [one_mul]
  exact max_eq_right (by linarith [M.θL_lt_θH])

lemma high_lt_at_m (M : Params) (hα : M.α₁ < M.αbar) :
    M.m * (M.θH - M.c) < M.θL + M.ebar - M.c := by
  obtain ⟨hm_pos, hm_lt, _⟩ := m_bounds M hα
  have hd : 0 < M.θH + M.ebar - M.c := by linarith [M.c_lt_θL, M.θL_lt_θH, ebar_pos M]
  unfold Params.αbar Params.alpha at hm_lt
  have h1 := (lt_div_iff₀ hd).mp hm_lt
  nlinarith [ebar_pos M]

lemma high_lt_at_αbar (M : Params) (hα : M.α₁ < M.αbar) :
    M.αbar * (M.θH - M.c) < M.θL + M.ebar - M.c := by
  obtain ⟨hm_pos, hm_lt, _⟩ := m_bounds M hα
  have hbar_pos : 0 < M.αbar := hm_pos.trans hm_lt
  have hd : 0 < M.θH + M.ebar - M.c := by linarith [M.c_lt_θL, M.θL_lt_θH, ebar_pos M]
  have h1 : M.αbar * (M.θH + M.ebar - M.c) = M.θL + M.ebar - M.c := by
    unfold Params.αbar Params.alpha
    exact div_mul_cancel₀ _ hd.ne'
  nlinarith [ebar_pos M]

lemma isOptimal_iff (M : Params) (hα : M.α₁ < M.αbar) {a0 : ℝ} (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1)
    (π : ℝ × ℝ) :
    IsOptimal M a0 π ↔ π ∈ designs ∧ designValue M a0 π = concaveClosure (vstar M) a0 := by
  have hgreat := (eq_8_concavification M hα).1 a0 ha0
  constructor
  · rintro ⟨hπ, hmax⟩
    rcases hgreat.1 with ⟨πStar, hπStar, hvalStar⟩
    exact ⟨hπ, le_antisymm (hgreat.2 ⟨π, hπ, rfl⟩) (hvalStar ▸ hmax πStar hπStar)⟩
  · rintro ⟨hπ, hval⟩
    refine ⟨hπ, fun π' hπ' => ?_⟩
    rw [hval]
    exact hgreat.2 ⟨π', hπ', rfl⟩

lemma uninformative_optimal_of_eq (M : Params) (hα : M.α₁ < M.αbar) {a0 : ℝ}
    (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1) (heq : vstar M a0 = concaveClosure (vstar M) a0)
    {π : ℝ × ℝ} (hU : IsUninformative π) : IsOptimal M a0 π := by
  rw [isOptimal_iff M hα ha0]
  refine ⟨hU.1, ?_⟩
  have hp2 : π.2 = 1 - π.1 := by linarith [hU.2]
  have hpH : probH a0 π = π.1 := by unfold probH; rw [hp2]; ring
  have hpL : probL a0 π = 1 - π.1 := by unfold probL; rw [hp2]; ring
  have htH : probH a0 π * vstar M (postH a0 π) = π.1 * vstar M a0 := by
    by_cases h0 : π.1 = 0
    · rw [hpH, h0, zero_mul, zero_mul]
    · have hpost : postH a0 π = a0 := by
        unfold postH
        rw [hpH, if_neg h0, mul_div_cancel_right₀ _ h0]
      rw [hpH, hpost]
  have htL : probL a0 π * vstar M (postL a0 π) = (1 - π.1) * vstar M a0 := by
    by_cases h1 : 1 - π.1 = 0
    · rw [hpL, h1, zero_mul, zero_mul]
    · have hpost : postL a0 π = a0 := by
        unfold postL
        rw [hpL, if_neg h1, mul_div_cancel_right₀ _ h1]
      rw [hpL, hpost]
  unfold designValue
  rw [htH, htL, ← heq]
  ring

lemma optimal_designOf_of_chord (M : Params) (hα : M.α₁ < M.αbar) {a0 u w : ℝ}
    (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1)
    (hu0 : 0 ≤ u) (hua : u < a0) (haw : a0 < w) (hw1 : w ≤ 1)
    (hchord : ((w - a0) / (w - u)) * vstar M u + ((a0 - u) / (w - u)) * vstar M w =
      concaveClosure (vstar M) a0) :
    ∃ π, IsOptimal M a0 π ∧ Induces a0 π u w := by
  have hbp := eq_3_bayes_plausibility a0 ha0
  obtain ⟨hmem, hind, hpH⟩ := hbp.2 u w hu0 hua haw hw1
  have hsum := (hbp.1 (designOf a0 u w) hmem).2.2.2.2.2.2.1
  have hwu : w - u ≠ 0 := (by linarith : 0 < w - u).ne'
  have hpL : probL a0 (designOf a0 u w) = (w - a0) / (w - u) := by
    have : probL a0 (designOf a0 u w) = 1 - probH a0 (designOf a0 u w) := by linarith
    rw [this, hpH]; field_simp; ring
  refine ⟨designOf a0 u w, ?_, hind⟩
  rw [isOptimal_iff M hα ha0]
  refine ⟨hmem, ?_⟩
  unfold designValue
  rw [hpH, hpL, hind.2, hind.1]
  linarith

lemma induces_of_supporting_line (M : Params) (hα : M.α₁ < M.αbar) {a0 c0 c1 u w : ℝ}
    (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1) (hua : u < a0) (haw : a0 < w)
    (hdom : ∀ x ∈ Set.Icc (0 : ℝ) 1, vstar M x ≤ c0 + c1 * x)
    (hstrict : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ u → x ≠ w → vstar M x < c0 + c1 * x)
    (hval : c0 + c1 * a0 = concaveClosure (vstar M) a0)
    {π : ℝ × ℝ} (hopt : IsOptimal M a0 π) : Induces a0 π u w := by
  obtain ⟨hπ, hdval⟩ := (isOptimal_iff M hα ha0 π).mp hopt
  obtain ⟨hL0, hLa0, hHa0, hH1, hpH_cc, hpL_cc, hpsum, hbayes⟩ :=
    (eq_3_bayes_plausibility a0 ha0).1 π hπ
  have hH_cc : postH a0 π ∈ Set.Icc (0 : ℝ) 1 := ⟨ha0.1.le.trans hHa0, hH1⟩
  have hL_cc : postL a0 π ∈ Set.Icc (0 : ℝ) 1 := ⟨hL0, hLa0.trans ha0.2.le⟩
  have ha0_cc : a0 ∈ Set.Icc (0 : ℝ) 1 := ⟨ha0.1.le, ha0.2.le⟩
  have ha0_strict : vstar M a0 < c0 + c1 * a0 := hstrict a0 ha0_cc (ne_of_gt hua) (ne_of_lt haw)
  unfold designValue at hdval
  have hlin : probH a0 π * (c0 + c1 * postH a0 π) + probL a0 π * (c0 + c1 * postL a0 π) =
      c0 + c1 * a0 := by
    calc probH a0 π * (c0 + c1 * postH a0 π) + probL a0 π * (c0 + c1 * postL a0 π)
        = c0 * (probH a0 π + probL a0 π) +
            c1 * (probH a0 π * postH a0 π + probL a0 π * postL a0 π) := by ring
      _ = c0 + c1 * a0 := by rw [hpsum, hbayes]; ring
  have hgapH_nn : 0 ≤ probH a0 π * (c0 + c1 * postH a0 π - vstar M (postH a0 π)) :=
    mul_nonneg hpH_cc.1 (sub_nonneg.mpr (hdom _ hH_cc))
  have hgapL_nn : 0 ≤ probL a0 π * (c0 + c1 * postL a0 π - vstar M (postL a0 π)) :=
    mul_nonneg hpL_cc.1 (sub_nonneg.mpr (hdom _ hL_cc))
  have hgap_sum : probH a0 π * (c0 + c1 * postH a0 π - vstar M (postH a0 π)) +
      probL a0 π * (c0 + c1 * postL a0 π - vstar M (postL a0 π)) = 0 := by
    linarith
  have hpH_pos : 0 < probH a0 π := by
    rcases eq_or_lt_of_le hpH_cc.1 with hpH0 | hpos
    · exfalso
      have hpL1 : probL a0 π = 1 := by linarith
      have hLa0_eq : postL a0 π = a0 := by nlinarith
      rw [← hpH0, zero_mul, zero_add, hpL1, one_mul, hLa0_eq] at hdval
      linarith
    · exact hpos
  have hpL_pos : 0 < probL a0 π := by
    rcases eq_or_lt_of_le hpL_cc.1 with hpL0 | hpos
    · exfalso
      have hpH1 : probH a0 π = 1 := by linarith
      have hHa0_eq : postH a0 π = a0 := by nlinarith
      rw [← hpL0, zero_mul, add_zero, hpH1, one_mul, hHa0_eq] at hdval
      linarith
    · exact hpos
  refine ⟨?_, ?_⟩
  · by_contra hne_u
    have hne_w : postL a0 π ≠ w := ne_of_lt (hLa0.trans_lt haw)
    have hpos := mul_pos hpL_pos (sub_pos.mpr (hstrict _ hL_cc hne_u hne_w))
    linarith
  · by_contra hne_w
    have hne_u : postH a0 π ≠ u := ne_of_gt (hua.trans_le hHa0)
    have hpos := mul_pos hpH_pos (sub_pos.mpr (hstrict _ hH_cc hne_u hne_w))
    linarith

lemma support_AB (M : Params) (hα : M.α₁ < M.αbar) (hgt0 : M.α₀ * M.Θ < M.ebar) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, vstar M x ≤ (M.θL - M.c) + (M.ebar / M.m) * x) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ 0 → x ≠ M.m →
      vstar M x < (M.θL - M.c) + (M.ebar / M.m) * x) := by
  obtain ⟨hm_pos, hm_lt, hbar_lt⟩ := m_bounds M hα
  have hm_lt1 : M.m < 1 := hm_lt.trans hbar_lt
  have h1m_pos : 0 < 1 - M.m := by linarith
  have hm_strict := high_lt_at_m M hα
  have hmΘ_lt : M.m * M.Θ < M.ebar := by
    have hα1Θ : M.α₁ * M.Θ = M.k := div_mul_cancel₀ _ (Θ_pos M).ne'
    unfold Params.m
    rcases max_choice M.α₀ M.α₁ with hm0 | hm1
    · rw [hm0]; exact hgt0
    · rw [hm1, hα1Θ]; exact M.k_lt_ebar
  have hstrict_fn : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ 0 → x ≠ M.m →
      vstar M x < (M.θL - M.c) + (M.ebar / M.m) * x := by
    intro x hx hx0 hxm
    have hx_pos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    rw [(eq_6_vstar M x hx).2]
    split_ifs with hint
    · have hgt_m : M.m < x := lt_of_le_of_ne hint.1 (Ne.symm hxm)
      have hgt1 : M.ebar < (M.ebar / M.m) * x := by
        rw [div_mul_eq_mul_div, lt_div_iff₀ hm_pos]
        nlinarith [ebar_pos M]
      linarith
    · refine max_lt ?_ ?_
      · have : 0 < (M.ebar / M.m) * x := mul_pos (div_pos (ebar_pos M) hm_pos) hx_pos
        linarith
      · rcases lt_or_gt_of_ne hxm with hlt_m | hgt_m
        · rw [← sub_pos]
          have hm_ne : M.m ≠ 0 := hm_pos.ne'
          have hid : (M.θL - M.c) + (M.ebar / M.m) * x - x * (M.θH - M.c) =
              ((M.m - x) * (M.θL - M.c) +
                x * (M.θL + M.ebar - M.c - M.m * (M.θH - M.c))) / M.m := by
            field_simp; ring
          rw [hid]
          exact div_pos (by nlinarith [M.c_lt_θL]) hm_pos
        · rw [← sub_pos]
          have hm_ne : M.m ≠ 0 := hm_pos.ne'
          have h1m_ne : 1 - M.m ≠ 0 := h1m_pos.ne'
          have hid : (M.θL - M.c) + (M.ebar / M.m) * x - x * (M.θH - M.c) =
              ((1 - x) * M.m * (M.θL + M.ebar - M.c - M.m * (M.θH - M.c)) +
                (x - M.m) * (M.ebar - M.m * (M.θH - M.θL))) / (M.m * (1 - M.m)) := by
            field_simp; ring
          rw [hid]
          unfold Params.Θ at hmΘ_lt
          have ht1 : 0 ≤ (1 - x) * M.m * (M.θL + M.ebar - M.c - M.m * (M.θH - M.c)) :=
            mul_nonneg (mul_nonneg (by linarith [hx.2]) hm_pos.le) (by linarith)
          have ht2 : 0 < (x - M.m) * (M.ebar - M.m * (M.θH - M.θL)) :=
            mul_pos (by linarith) (by linarith)
          exact div_pos (by linarith) (mul_pos hm_pos h1m_pos)
  refine ⟨fun x hx => ?_, hstrict_fn⟩
  by_cases hx0 : x = 0
  · subst hx0; rw [vstar_0 M hα]; ring_nf; exact le_rfl
  · by_cases hxm : x = M.m
    · subst hxm
      rw [vstar_mid M ⟨hm_pos.le, hm_lt1.le⟩ ⟨le_rfl, hm_lt.le⟩, div_mul_cancel₀ _ hm_pos.ne']
      linarith
    · exact (hstrict_fn x hx hx0 hxm).le

lemma support_BD (M : Params) (hα : M.α₁ < M.αbar)
    (hgt0 : M.α₀ * M.Θ < M.ebar) (hltΘ : M.ebar < M.Θ) :
    let c1 := (M.Θ - M.ebar) / (1 - M.m)
    let c0 := M.θL + M.ebar - M.c - M.m * c1
    (∀ x ∈ Set.Icc (0 : ℝ) 1, vstar M x ≤ c0 + c1 * x) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ M.m → x ≠ 1 → vstar M x < c0 + c1 * x) := by
  dsimp only
  obtain ⟨hm_pos, hm_lt, hbar_lt⟩ := m_bounds M hα
  have hm_lt1 : M.m < 1 := hm_lt.trans hbar_lt
  have h1m_pos : 0 < 1 - M.m := by linarith
  have hm_strict := high_lt_at_m M hα
  have hmΘ_lt : M.m * M.Θ < M.ebar := by
    have hα1Θ : M.α₁ * M.Θ = M.k := div_mul_cancel₀ _ (Θ_pos M).ne'
    unfold Params.m
    rcases max_choice M.α₀ M.α₁ with hm0 | hm1
    · rw [hm0]; exact hgt0
    · rw [hm1, hα1Θ]; exact M.k_lt_ebar
  have hAB := (support_AB M hα hgt0).1
  have hstrict_fn : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ M.m → x ≠ 1 →
      vstar M x < M.θL + M.ebar - M.c - M.m * ((M.Θ - M.ebar) / (1 - M.m)) +
        ((M.Θ - M.ebar) / (1 - M.m)) * x := by
    intro x hx hxm hx1
    have hx_lt1 : x < 1 := lt_of_le_of_ne hx.2 hx1
    rcases lt_or_gt_of_ne hxm with hlt_m | hgt_m
    · refine lt_of_le_of_lt (hAB x hx) ?_
      rw [← sub_pos]
      have hm_ne : M.m ≠ 0 := hm_pos.ne'
      have h1m_ne : 1 - M.m ≠ 0 := h1m_pos.ne'
      have hid : M.θL + M.ebar - M.c - M.m * ((M.Θ - M.ebar) / (1 - M.m)) +
            ((M.Θ - M.ebar) / (1 - M.m)) * x - ((M.θL - M.c) + (M.ebar / M.m) * x) =
          (M.m - x) * (M.ebar - M.m * M.Θ) / (M.m * (1 - M.m)) := by
        field_simp; ring
      rw [hid]
      exact div_pos (mul_pos (by linarith) (by linarith)) (mul_pos hm_pos h1m_pos)
    · rw [(eq_6_vstar M x hx).2]
      split_ifs with hint
      · have hpos : 0 < (x - M.m) * ((M.Θ - M.ebar) / (1 - M.m)) :=
          mul_pos (by linarith) (div_pos (by linarith) h1m_pos)
        linarith
      · have hα0_lt : M.α₀ < x := lt_of_le_of_lt (le_max_left _ _) hgt_m
        unfold Params.α₀ Params.alpha at hα0_lt
        simp only [add_zero] at hα0_lt
        have hlow_lt := (div_lt_iff₀ (by linarith [M.c_lt_θL, M.θL_lt_θH])).mp hα0_lt
        rw [max_eq_right hlow_lt.le, ← sub_pos]
        have h1m_ne : 1 - M.m ≠ 0 := h1m_pos.ne'
        unfold Params.Θ
        have hid : M.θL + M.ebar - M.c - M.m * ((M.θH - M.θL - M.ebar) / (1 - M.m)) +
              ((M.θH - M.θL - M.ebar) / (1 - M.m)) * x - x * (M.θH - M.c) =
            (1 - x) * (M.θL + M.ebar - M.c - M.m * (M.θH - M.c)) / (1 - M.m) := by
          field_simp; ring
        rw [hid]
        exact div_pos (by nlinarith) h1m_pos
  refine ⟨fun x hx => ?_, hstrict_fn⟩
  by_cases hxm : x = M.m
  · subst hxm
    rw [vstar_mid M ⟨hm_pos.le, hm_lt1.le⟩ ⟨le_rfl, hm_lt.le⟩]
    ring_nf; exact le_rfl
  · by_cases hx1 : x = 1
    · subst hx1
      rw [vstar_1 M hα]
      unfold Params.Θ
      have h1m_ne : 1 - M.m ≠ 0 := h1m_pos.ne'
      have : M.θL + M.ebar - M.c - M.m * ((M.θH - M.θL - M.ebar) / (1 - M.m)) +
          (M.θH - M.θL - M.ebar) / (1 - M.m) * 1 = M.θH - M.c := by
        field_simp; ring
      linarith
    · exact (hstrict_fn x hx hxm hx1).le

lemma support_BC (M : Params) (hgtΘ : M.Θ < M.ebar) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, vstar M x ≤ M.θL + M.ebar - M.c) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, ¬ (M.m ≤ x ∧ x ≤ M.αbar) → vstar M x < M.θL + M.ebar - M.c) := by
  have hstrict_fn : ∀ x ∈ Set.Icc (0 : ℝ) 1, ¬ (M.m ≤ x ∧ x ≤ M.αbar) →
      vstar M x < M.θL + M.ebar - M.c := by
    intro x hx hnot
    rw [(eq_6_vstar M x hx).2, if_neg hnot]
    refine max_lt (by linarith [ebar_pos M]) ?_
    have hx1 : x * (M.θH - M.c) ≤ 1 * (M.θH - M.c) :=
      mul_le_mul_of_nonneg_right hx.2 (by linarith [M.c_lt_θL, M.θL_lt_θH])
    unfold Params.Θ at hgtΘ
    linarith
  refine ⟨fun x hx => ?_, hstrict_fn⟩
  by_cases hm : M.m ≤ x ∧ x ≤ M.αbar
  · rw [vstar_mid M hx hm]
  · exact (hstrict_fn x hx hm).le

lemma support_CD (M : Params) (hα : M.α₁ < M.αbar) (hgtΘ : M.Θ < M.ebar) :
    let c1 := (M.Θ - M.ebar) / (1 - M.αbar)
    let c0 := M.θL + M.ebar - M.c - M.αbar * c1
    (∀ x ∈ Set.Icc (0 : ℝ) 1, vstar M x ≤ c0 + c1 * x) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ M.αbar → x ≠ 1 → vstar M x < c0 + c1 * x) := by
  dsimp only
  obtain ⟨hm_pos, hm_lt, hbar_lt⟩ := m_bounds M hα
  have h1b_pos : 0 < 1 - M.αbar := by linarith
  have hb_strict := high_lt_at_αbar M hα
  have hBC := (support_BC M hgtΘ).1
  have hstrict_fn : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ M.αbar → x ≠ 1 →
      vstar M x < M.θL + M.ebar - M.c - M.αbar * ((M.Θ - M.ebar) / (1 - M.αbar)) +
        ((M.Θ - M.ebar) / (1 - M.αbar)) * x := by
    intro x hx hxb hx1
    have hx_lt1 : x < 1 := lt_of_le_of_ne hx.2 hx1
    rcases lt_or_gt_of_ne hxb with hlt_b | hgt_b
    · refine lt_of_le_of_lt (hBC x hx) ?_
      have hpos : 0 < (x - M.αbar) * ((M.Θ - M.ebar) / (1 - M.αbar)) :=
        mul_pos_of_neg_of_neg (by linarith) (div_neg_of_neg_of_pos (by linarith) h1b_pos)
      linarith
    · rw [(eq_6_vstar M x hx).2, if_neg (by intro h; linarith [h.2])]
      have hα0_lt : M.α₀ < x := (α₀_lt_αbar M).trans hgt_b
      unfold Params.α₀ Params.alpha at hα0_lt
      simp only [add_zero] at hα0_lt
      have hlow_lt := (div_lt_iff₀ (by linarith [M.c_lt_θL, M.θL_lt_θH])).mp hα0_lt
      rw [max_eq_right hlow_lt.le, ← sub_pos]
      have h1b_ne : 1 - M.αbar ≠ 0 := h1b_pos.ne'
      unfold Params.Θ
      have hid : M.θL + M.ebar - M.c - M.αbar * ((M.θH - M.θL - M.ebar) / (1 - M.αbar)) +
            ((M.θH - M.θL - M.ebar) / (1 - M.αbar)) * x - x * (M.θH - M.c) =
          (1 - x) * (M.θL + M.ebar - M.c - M.αbar * (M.θH - M.c)) / (1 - M.αbar) := by
        field_simp; ring
      rw [hid]
      exact div_pos (by nlinarith) h1b_pos
  refine ⟨fun x hx => ?_, hstrict_fn⟩
  by_cases hxb : x = M.αbar
  · subst hxb
    rw [vstar_mid M ⟨(hm_pos.trans hm_lt).le, hbar_lt.le⟩ ⟨hm_lt.le, le_rfl⟩]
    ring_nf; exact le_rfl
  · by_cases hx1 : x = 1
    · subst hx1
      rw [vstar_1 M hα]
      unfold Params.Θ
      have h1b_ne : 1 - M.αbar ≠ 0 := h1b_pos.ne'
      have : M.θL + M.ebar - M.c - M.αbar * ((M.θH - M.θL - M.ebar) / (1 - M.αbar)) +
          (M.θH - M.θL - M.ebar) / (1 - M.αbar) * 1 = M.θH - M.c := by
        field_simp; ring
      linarith
    · exact (hstrict_fn x hx hxb hx1).le

end Aux_EngageInfo_prop1

open EngageInfo Aux_EngageInfo_prop1

theorem solution (M : Params) (hα : M.α₁ < M.αbar) (a0 : ℝ) (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1) :
    ((M.ebar < M.α₀ * M.Θ → ∃ π, IsOptimal M a0 π ∧ Induces a0 π 0 1) ∧
      (M.α₀ * M.Θ ≤ M.ebar ∧ M.ebar ≤ M.Θ →
        (a0 < M.m → ∃ π, IsOptimal M a0 π ∧ Induces a0 π 0 M.m) ∧
        (M.m < a0 → ∃ π, IsOptimal M a0 π ∧ Induces a0 π M.m 1)) ∧
      (M.Θ < M.ebar →
        (a0 < M.m → ∃ π, IsOptimal M a0 π ∧ Induces a0 π 0 M.m) ∧
        (M.m < a0 → a0 < M.αbar → ∀ π, IsUninformative π → IsOptimal M a0 π) ∧
        (M.αbar < a0 → ∃ π, IsOptimal M a0 π ∧ Induces a0 π M.αbar 1))) ∧
    ((M.ebar < M.α₀ * M.Θ → ∀ π, IsOptimal M a0 π → Induces a0 π 0 1) ∧
      (M.α₀ * M.Θ < M.ebar ∧ M.ebar ≤ M.Θ →
        a0 < M.m → ∀ π, IsOptimal M a0 π → Induces a0 π 0 M.m) ∧
      (M.α₀ * M.Θ < M.ebar ∧ M.ebar < M.Θ →
        M.m < a0 → ∀ π, IsOptimal M a0 π → Induces a0 π M.m 1) ∧
      (M.Θ < M.ebar →
        (a0 < M.m → ∀ π, IsOptimal M a0 π → Induces a0 π 0 M.m) ∧
        (M.m < a0 → a0 < M.αbar → ∀ π, IsOptimal M a0 π →
          postL a0 π ∈ Set.Icc M.m M.αbar ∧ postH a0 π ∈ Set.Icc M.m M.αbar) ∧
        (M.αbar < a0 → ∀ π, IsOptimal M a0 π → Induces a0 π M.αbar 1))) ∧
    (M.ebar = M.Θ → M.m < a0 → a0 ≤ M.αbar →
      ∀ π, IsUninformative π → IsOptimal M a0 π) := by
  obtain ⟨hm_pos, hm_lt, hbar_lt⟩ := m_bounds M hα
  have hm_lt1 : M.m < 1 := hm_lt.trans hbar_lt
  have h1m_pos : 0 < 1 - M.m := by linarith
  have h1b_pos : 0 < 1 - M.αbar := by linarith
  have ha0_cc : a0 ∈ Set.Icc (0 : ℝ) 1 := ⟨ha0.1.le, ha0.2.le⟩
  have hseg := concave_closure_segments M hα
  have hα0Θ_lt_Θ : M.α₀ * M.Θ < M.Θ := by
    have hα0_lt1 : M.α₀ < 1 := (α₀_lt_αbar M).trans hbar_lt
    nlinarith [Θ_pos M]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- (a)(i)
    intro hsc1
    refine optimal_designOf_of_chord M hα ha0 le_rfl ha0.1 ha0.2 le_rfl ?_
    rw [(hseg.1 hsc1).1 a0 ha0_cc, vstar_0 M hα, vstar_1 M hα]
    unfold Params.Θ; ring
  · -- (a)(ii)
    intro hsc2
    refine ⟨fun hlt_m => ?_, fun hgt_m => ?_⟩
    · refine optimal_designOf_of_chord M hα ha0 le_rfl ha0.1 hlt_m hm_lt1.le ?_
      rw [(hseg.2.1 hsc2).1 a0 ⟨ha0.1.le, hlt_m.le⟩, vstar_0 M hα,
        vstar_mid M ⟨hm_pos.le, hm_lt1.le⟩ ⟨le_rfl, hm_lt.le⟩]
      have := hm_pos.ne'; field_simp; ring
    · refine optimal_designOf_of_chord M hα ha0 hm_pos.le hgt_m ha0.2 le_rfl ?_
      rw [(hseg.2.1 hsc2).2 a0 ⟨hgt_m.le, ha0.2.le⟩,
        vstar_mid M ⟨hm_pos.le, hm_lt1.le⟩ ⟨le_rfl, hm_lt.le⟩, vstar_1 M hα]
      unfold Params.Θ
      have := h1m_pos.ne'; field_simp; ring
  · -- (a)(iii)
    intro hsc3
    refine ⟨fun hlt_m => ?_, fun hgt_m hlt_b π hU => ?_, fun hgt_b => ?_⟩
    · refine optimal_designOf_of_chord M hα ha0 le_rfl ha0.1 hlt_m hm_lt1.le ?_
      rw [(hseg.2.2 hsc3).1 a0 ⟨ha0.1.le, hlt_m.le⟩, vstar_0 M hα,
        vstar_mid M ⟨hm_pos.le, hm_lt1.le⟩ ⟨le_rfl, hm_lt.le⟩]
      have := hm_pos.ne'; field_simp; ring
    · refine uninformative_optimal_of_eq M hα ha0 ?_ hU
      rw [(hseg.2.2 hsc3).2.1 a0 ⟨hgt_m.le, hlt_b.le⟩, vstar_mid M ha0_cc ⟨hgt_m.le, hlt_b.le⟩]
    · refine optimal_designOf_of_chord M hα ha0 (hm_pos.trans hm_lt).le hgt_b ha0.2 le_rfl ?_
      rw [(hseg.2.2 hsc3).2.2 a0 ⟨hgt_b.le, ha0.2.le⟩,
        vstar_mid M ⟨(hm_pos.trans hm_lt).le, hbar_lt.le⟩ ⟨hm_lt.le, le_rfl⟩, vstar_1 M hα]
      unfold Params.Θ
      have := h1b_pos.ne'; field_simp; ring
  · -- (b.1)
    intro hsc1 π hopt
    have hstrict_AD : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ≠ 0 → x ≠ 1 →
        vstar M x < (M.θL - M.c) + M.Θ * x := by
      intro x hx hx0 hx1
      have h := (hseg.1 hsc1).2 x ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
      linarith
    have hdom_AD : ∀ x ∈ Set.Icc (0 : ℝ) 1, vstar M x ≤ (M.θL - M.c) + M.Θ * x := by
      intro x hx
      by_cases hx0 : x = 0
      · subst hx0; rw [vstar_0 M hα]; ring_nf; exact le_rfl
      · by_cases hx1 : x = 1
        · subst hx1; rw [vstar_1 M hα]; unfold Params.Θ; linarith
        · exact (hstrict_AD x hx hx0 hx1).le
    refine induces_of_supporting_line M hα ha0 ha0.1 ha0.2 hdom_AD hstrict_AD ?_ hopt
    rw [(hseg.1 hsc1).1 a0 ha0_cc]; ring
  · -- (b.2)
    intro hsc2 hlt_m π hopt
    obtain ⟨hdom_AB, hstrict_AB⟩ := support_AB M hα hsc2.1
    refine induces_of_supporting_line M hα ha0 ha0.1 hlt_m hdom_AB hstrict_AB ?_ hopt
    rw [(hseg.2.1 ⟨hsc2.1.le, hsc2.2⟩).1 a0 ⟨ha0.1.le, hlt_m.le⟩]; ring
  · -- (b.3)
    intro hsc2 hgt_m π hopt
    obtain ⟨hdom_BD, hstrict_BD⟩ := support_BD M hα hsc2.1 hsc2.2
    refine induces_of_supporting_line M hα ha0 hgt_m ha0.2 hdom_BD hstrict_BD ?_ hopt
    rw [(hseg.2.1 ⟨hsc2.1.le, hsc2.2.le⟩).2 a0 ⟨hgt_m.le, ha0.2.le⟩]; ring
  · -- (b.4)
    intro hsc3
    refine ⟨fun hlt_m π hopt => ?_, fun hgt_m hlt_b π hopt => ?_, fun hgt_b π hopt => ?_⟩
    · obtain ⟨hdom_AB, hstrict_AB⟩ := support_AB M hα (hα0Θ_lt_Θ.trans hsc3)
      refine induces_of_supporting_line M hα ha0 ha0.1 hlt_m hdom_AB hstrict_AB ?_ hopt
      rw [(hseg.2.2 hsc3).1 a0 ⟨ha0.1.le, hlt_m.le⟩]; ring
    · obtain ⟨hdom_BC, hstrict_BC⟩ := support_BC M hsc3
      obtain ⟨hπ, hdval⟩ := (isOptimal_iff M hα ha0 π).mp hopt
      obtain ⟨hL0, hLa0, hHa0, hH1, hpH_cc, hpL_cc, hpsum, _⟩ :=
        (eq_3_bayes_plausibility a0 ha0).1 π hπ
      have hH_cc : postH a0 π ∈ Set.Icc (0 : ℝ) 1 := ⟨ha0.1.le.trans hHa0, hH1⟩
      have hL_cc : postL a0 π ∈ Set.Icc (0 : ℝ) 1 := ⟨hL0, hLa0.trans ha0.2.le⟩
      rw [(hseg.2.2 hsc3).2.1 a0 ⟨hgt_m.le, hlt_b.le⟩] at hdval
      unfold designValue at hdval
      have hgapH_nn : 0 ≤ probH a0 π * (M.θL + M.ebar - M.c - vstar M (postH a0 π)) :=
        mul_nonneg hpH_cc.1 (sub_nonneg.mpr (hdom_BC _ hH_cc))
      have hgapL_nn : 0 ≤ probL a0 π * (M.θL + M.ebar - M.c - vstar M (postL a0 π)) :=
        mul_nonneg hpL_cc.1 (sub_nonneg.mpr (hdom_BC _ hL_cc))
      have hgap_sum : probH a0 π * (M.θL + M.ebar - M.c - vstar M (postH a0 π)) +
          probL a0 π * (M.θL + M.ebar - M.c - vstar M (postL a0 π)) = 0 := by
        have hconst : (probH a0 π + probL a0 π) * (M.θL + M.ebar - M.c) =
            M.θL + M.ebar - M.c := by rw [hpsum, one_mul]
        linarith
      refine ⟨?_, ?_⟩
      · rcases eq_or_lt_of_le hpL_cc.1 with hpL0 | hpL_pos
        · unfold postL
          rw [if_pos hpL0.symm]
          exact ⟨hgt_m.le, hlt_b.le⟩
        · by_contra hnot
          have hpos := mul_pos hpL_pos (sub_pos.mpr (hstrict_BC _ hL_cc hnot))
          linarith
      · rcases eq_or_lt_of_le hpH_cc.1 with hpH0 | hpH_pos
        · unfold postH
          rw [if_pos hpH0.symm]
          exact ⟨hgt_m.le, hlt_b.le⟩
        · by_contra hnot
          have hpos := mul_pos hpH_pos (sub_pos.mpr (hstrict_BC _ hH_cc hnot))
          linarith
    · obtain ⟨hdom_CD, hstrict_CD⟩ := support_CD M hα hsc3
      refine induces_of_supporting_line M hα ha0 hgt_b ha0.2 hdom_CD hstrict_CD ?_ hopt
      rw [(hseg.2.2 hsc3).2.2 a0 ⟨hgt_b.le, ha0.2.le⟩]; ring
  · -- (c)
    intro hebar_eq hgt_m hle_b π hU
    refine uninformative_optimal_of_eq M hα ha0 ?_ hU
    have hsc2 : M.α₀ * M.Θ ≤ M.ebar ∧ M.ebar ≤ M.Θ := by
      rw [hebar_eq]
      exact ⟨hα0Θ_lt_Θ.le, le_rfl⟩
    rw [(hseg.2.1 hsc2).2 a0 ⟨hgt_m.le, ha0.2.le⟩, vstar_mid M ha0_cc ⟨hgt_m.le, hle_b⟩, hebar_eq]
    ring
