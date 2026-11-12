-- Prove2me | solution 1 for EngageInfo.eq_8_concavification
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T20:35:55.7872+00:00
-- url     : https://prove2.me/submissions/6dbff036-d4a0-41f8-9fce-f432629b27fb

import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_vstar
import Definitions.Def_EngageInfo_designs
import Definitions.Def_EngageInfo_designValue
import Definitions.Def_EngageInfo_concaveClosure
import Theorems.Thm_EngageInfo_eq_6_vstar
import Theorems.Thm_EngageInfo_eq_3_bayes_plausibility
import Theorems.Thm_EngageInfo_concave_closure_segments

namespace Aux_EngageInfo_eq_8
open EngageInfo

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

def fibre (M : Params) (α : ℝ) : Set ℝ :=
  {y | (α, y) ∈ convexHull ℝ (graphOn01 (vstar M))}

lemma fibre_nonempty (M : Params) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (fibre M α).Nonempty :=
  ⟨vstar M α, subset_convexHull ℝ (graphOn01 (vstar M)) ⟨hα, rfl⟩⟩

lemma convexHull_le_of_concave (M : Params) {g : ℝ → ℝ}
    (hg_conc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g)
    (hg_ge : ∀ x ∈ Set.Icc (0 : ℝ) 1, vstar M x ≤ g x)
    {α y : ℝ} (hy : (α, y) ∈ convexHull ℝ (graphOn01 (vstar M))) :
    α ∈ Set.Icc (0 : ℝ) 1 ∧ y ≤ g α := by
  let H : Set (ℝ × ℝ) := {q | q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ≤ g q.1}
  have hH_conv : Convex ℝ H := by
    intro p hp q hq a b ha hb hab
    refine ⟨(convex_Icc (0 : ℝ) 1) hp.1 hq.1 ha hb hab, ?_⟩
    dsimp
    exact le_trans (add_le_add (mul_le_mul_of_nonneg_left hp.2 ha)
      (mul_le_mul_of_nonneg_left hq.2 hb)) (hg_conc.2 hp.1 hq.1 ha hb hab)
  have hsub : graphOn01 (vstar M) ⊆ H := fun q hq => ⟨hq.1, hq.2.trans_le (hg_ge q.1 hq.1)⟩
  exact convexHull_min hsub hH_conv hy

lemma vstar_le_const (M : Params) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    vstar M x ≤ M.θH + M.ebar - M.c := by
  rw [(eq_6_vstar M x hx).2]
  split_ifs
  · linarith [M.θL_lt_θH]
  · refine max_le (by linarith [M.θL_lt_θH, ebar_pos M]) ?_
    have : x * (M.θH - M.c) ≤ 1 * (M.θH - M.c) :=
      mul_le_mul_of_nonneg_right hx.2 (by linarith [M.c_lt_θL, M.θL_lt_θH])
    linarith [ebar_pos M]

lemma fibre_bddAbove (M : Params) (α : ℝ) : BddAbove (fibre M α) := by
  refine ⟨M.θH + M.ebar - M.c, fun y hy => ?_⟩
  have hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun _ => M.θH + M.ebar - M.c) := by
    refine ⟨convex_Icc 0 1, fun _ _ _ _ a b _ _ hab => ?_⟩
    simp only [smul_eq_mul]
    have : a * (M.θH + M.ebar - M.c) + b * (M.θH + M.ebar - M.c) =
        (a + b) * (M.θH + M.ebar - M.c) := by ring
    rw [this, hab, one_mul]
  exact (convexHull_le_of_concave M hconc (fun x hx => vstar_le_const M hx) hy).2

lemma vstar_le_closure (M : Params) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    vstar M α ≤ concaveClosure (vstar M) α :=
  le_csSup (fibre_bddAbove M α) (subset_convexHull ℝ (graphOn01 (vstar M)) ⟨hα, rfl⟩)

lemma closure_le_of_concave (M : Params) {g : ℝ → ℝ}
    (hg_conc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g)
    (hg_ge : ∀ x ∈ Set.Icc (0 : ℝ) 1, vstar M x ≤ g x)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    concaveClosure (vstar M) α ≤ g α :=
  csSup_le (fibre_nonempty M hα) fun _ hy =>
    (convexHull_le_of_concave M hg_conc hg_ge hy).2

lemma closure_concaveOn (M : Params) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (concaveClosure (vstar M)) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · have hb1 : b = 1 := by linarith
    subst hb1; simp
  · rcases eq_or_lt_of_le hb with rfl | hb_pos
    · have ha1 : a = 1 := by linarith
      subst ha1; simp
    · set z := a * x + b * y
      have hstep1 : a * concaveClosure (vstar M) x ≤
          concaveClosure (vstar M) z - b * concaveClosure (vstar M) y := by
        rw [mul_comm a, ← le_div_iff₀ ha_pos]
        refine csSup_le (fibre_nonempty M hx) fun ux hux => ?_
        rw [le_div_iff₀ ha_pos]
        have hstep2 : b * concaveClosure (vstar M) y ≤
            concaveClosure (vstar M) z - a * ux := by
          rw [mul_comm b, ← le_div_iff₀ hb_pos]
          refine csSup_le (fibre_nonempty M hy) fun uy huy => ?_
          rw [le_div_iff₀ hb_pos]
          have hcomb := (convex_convexHull ℝ (graphOn01 (vstar M))) hux huy ha hb hab
          have hpt : (a • (x, ux) + b • (y, uy) : ℝ × ℝ) = (z, a * ux + b * uy) := by
            ext <;> simp [z, smul_eq_mul]
          rw [hpt] at hcomb
          have hle : a * ux + b * uy ≤ concaveClosure (vstar M) z :=
            le_csSup (fibre_bddAbove M z) hcomb
          linarith
        linarith
      linarith

lemma attain_self (M : Params) {a0 : ℝ} (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1)
    (heq : vstar M a0 = concaveClosure (vstar M) a0) :
    concaveClosure (vstar M) a0 ∈ designValue M a0 '' designs := by
  refine ⟨(1, 0), ?_, ?_⟩
  · unfold designs
    simp only [Set.mem_setOf_eq]
    norm_num
  · have hpH : probH a0 (1, 0) = 1 := by unfold probH; ring
    have hpL : probL a0 (1, 0) = 0 := by unfold probL; ring
    have hpostH : postH a0 (1, 0) = a0 := by
      unfold postH
      rw [hpH, if_neg one_ne_zero]
      ring
    unfold designValue
    rw [hpH, hpL, hpostH]
    linarith

lemma attain_chord (M : Params) {a0 u w : ℝ} (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1)
    (hu0 : 0 ≤ u) (hua : u < a0) (haw : a0 < w) (hw1 : w ≤ 1)
    (hchord : ((w - a0) / (w - u)) * vstar M u + ((a0 - u) / (w - u)) * vstar M w =
      concaveClosure (vstar M) a0) :
    concaveClosure (vstar M) a0 ∈ designValue M a0 '' designs := by
  have hbp := eq_3_bayes_plausibility a0 ha0
  obtain ⟨hmem, ⟨hpostL, hpostH⟩, hpH⟩ := hbp.2 u w hu0 hua haw hw1
  have hsum := (hbp.1 (designOf a0 u w) hmem).2.2.2.2.2.2.1
  have hwu : w - u ≠ 0 := (by linarith : 0 < w - u).ne'
  have hpL : probL a0 (designOf a0 u w) = (w - a0) / (w - u) := by
    have : probL a0 (designOf a0 u w) = 1 - probH a0 (designOf a0 u w) := by linarith
    rw [this, hpH]
    field_simp
    ring
  refine ⟨designOf a0 u w, hmem, ?_⟩
  unfold designValue
  rw [hpH, hpL, hpostH, hpostL]
  linarith

end Aux_EngageInfo_eq_8

open EngageInfo Aux_EngageInfo_eq_8

theorem solution (M : Params) (hα : M.α₁ < M.αbar) :
    (∀ a0 ∈ Set.Ioo (0 : ℝ) 1,
      IsGreatest (designValue M a0 '' designs) (concaveClosure (vstar M) a0)) ∧
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (concaveClosure (vstar M)) ∧
    (∀ α ∈ Set.Icc (0 : ℝ) 1, vstar M α ≤ concaveClosure (vstar M) α) ∧
    (∀ g : ℝ → ℝ, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g → (∀ α ∈ Set.Icc (0 : ℝ) 1, vstar M α ≤ g α) →
      ∀ α ∈ Set.Icc (0 : ℝ) 1, concaveClosure (vstar M) α ≤ g α) := by
  have hconc := closure_concaveOn M
  refine ⟨fun a0 ha0 => ⟨?_, ?_⟩, hconc, fun α hα_mem => vstar_le_closure M hα_mem,
    fun g hg_conc hg_ge α hα_mem => closure_le_of_concave M hg_conc hg_ge hα_mem⟩
  · obtain ⟨hm_pos, hm_lt, hbar_lt⟩ := m_bounds M hα
    have hm_lt1 : M.m < 1 := hm_lt.trans hbar_lt
    have h1m_pos : 0 < 1 - M.m := by linarith
    have h1b_pos : 0 < 1 - M.αbar := by linarith
    have ha0_cc : a0 ∈ Set.Icc (0 : ℝ) 1 := ⟨ha0.1.le, ha0.2.le⟩
    have hseg := concave_closure_segments M hα
    rcases lt_or_ge M.ebar (M.α₀ * M.Θ) with hsc1 | hge1
    · refine attain_chord M ha0 le_rfl ha0.1 ha0.2 le_rfl ?_
      rw [(hseg.1 hsc1).1 a0 ha0_cc, vstar_0 M hα, vstar_1 M hα]
      unfold Params.Θ
      ring
    · rcases le_or_gt M.ebar M.Θ with hle2 | hsc3
      · have hsc2 := hseg.2.1 ⟨hge1, hle2⟩
        rcases lt_trichotomy a0 M.m with hlt_m | rfl | hgt_m
        · refine attain_chord M ha0 le_rfl ha0.1 hlt_m hm_lt1.le ?_
          rw [hsc2.1 a0 ⟨ha0.1.le, hlt_m.le⟩, vstar_0 M hα,
            vstar_mid M ⟨hm_pos.le, hm_lt1.le⟩ ⟨le_rfl, hm_lt.le⟩]
          have := hm_pos.ne'; field_simp; ring
        · refine attain_self M ha0 ?_
          rw [hsc2.1 M.m ⟨hm_pos.le, le_rfl⟩,
            vstar_mid M ⟨hm_pos.le, hm_lt1.le⟩ ⟨le_rfl, hm_lt.le⟩]
          have := hm_pos.ne'; field_simp; ring
        · refine attain_chord M ha0 hm_pos.le hgt_m ha0.2 le_rfl ?_
          rw [hsc2.2 a0 ⟨hgt_m.le, ha0.2.le⟩,
            vstar_mid M ⟨hm_pos.le, hm_lt1.le⟩ ⟨le_rfl, hm_lt.le⟩, vstar_1 M hα]
          unfold Params.Θ
          have := h1m_pos.ne'; field_simp; ring
      · have hsc3' := hseg.2.2 hsc3
        rcases lt_or_ge a0 M.m with hlt_m | hge_m
        · refine attain_chord M ha0 le_rfl ha0.1 hlt_m hm_lt1.le ?_
          rw [hsc3'.1 a0 ⟨ha0.1.le, hlt_m.le⟩, vstar_0 M hα,
            vstar_mid M ⟨hm_pos.le, hm_lt1.le⟩ ⟨le_rfl, hm_lt.le⟩]
          have := hm_pos.ne'; field_simp; ring
        · rcases le_or_gt a0 M.αbar with hle_b | hgt_b
          · refine attain_self M ha0 ?_
            rw [hsc3'.2.1 a0 ⟨hge_m, hle_b⟩, vstar_mid M ha0_cc ⟨hge_m, hle_b⟩]
          · refine attain_chord M ha0 (hm_pos.trans hm_lt).le hgt_b ha0.2 le_rfl ?_
            rw [hsc3'.2.2 a0 ⟨hgt_b.le, ha0.2.le⟩,
              vstar_mid M ⟨(hm_pos.trans hm_lt).le, hbar_lt.le⟩ ⟨hm_lt.le, le_rfl⟩,
              vstar_1 M hα]
            unfold Params.Θ
            have := h1b_pos.ne'; field_simp; ring
  · rintro _ ⟨π, hπ, rfl⟩
    have hbp := (eq_3_bayes_plausibility a0 ha0).1 π hπ
    rcases hbp with ⟨hL0, hLa0, hHa0, hH1, hpH_cc, hpL_cc, hpsum, hbayes⟩
    have hH_cc : postH a0 π ∈ Set.Icc (0 : ℝ) 1 := ⟨ha0.1.le.trans hHa0, hH1⟩
    have hL_cc : postL a0 π ∈ Set.Icc (0 : ℝ) 1 := ⟨hL0, hLa0.trans ha0.2.le⟩
    unfold designValue
    have h1 : probH a0 π * vstar M (postH a0 π) + probL a0 π * vstar M (postL a0 π) ≤
        probH a0 π * concaveClosure (vstar M) (postH a0 π) +
          probL a0 π * concaveClosure (vstar M) (postL a0 π) :=
      add_le_add (mul_le_mul_of_nonneg_left (vstar_le_closure M hH_cc) hpH_cc.1)
        (mul_le_mul_of_nonneg_left (vstar_le_closure M hL_cc) hpL_cc.1)
    have h2 := hconc.2 hH_cc hL_cc hpH_cc.1 hpL_cc.1 hpsum
    simp only [smul_eq_mul] at h2
    rw [hbayes] at h2
    exact h1.trans h2
