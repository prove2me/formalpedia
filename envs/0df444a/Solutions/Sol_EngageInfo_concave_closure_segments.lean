-- Prove2me | solution 1 for EngageInfo.concave_closure_segments
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T20:33:33.425108+00:00
-- url     : https://prove2.me/submissions/20bdddad-6e30-45df-875b-3ee82c8cfbaf

import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_vstar
import Definitions.Def_EngageInfo_concaveClosure
import Theorems.Thm_EngageInfo_eq_6_vstar

namespace Aux_EngageInfo_segments
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
    0 < M.m ∧ M.m < M.αbar ∧ M.αbar < 1 := by
  have hm_pos : 0 < M.m := lt_of_lt_of_le (α₀_pos M) (le_max_left _ _)
  have hm_lt : M.m < M.αbar := max_lt (α₀_lt_αbar M) hα
  exact ⟨hm_pos, hm_lt, αbar_lt_one M⟩

lemma vstar_0 (M : Params) (hα : M.α₁ < M.αbar) : vstar M 0 = M.θL - M.c := by
  obtain ⟨hm_pos, _, _⟩ := m_bounds M hα
  rw [(eq_6_vstar M 0 ⟨le_rfl, zero_le_one⟩).2, if_neg (by intro h; linarith [h.1])]
  simp only [zero_mul]
  exact max_eq_left (by linarith [M.c_lt_θL])

lemma vstar_m (M : Params) (hα : M.α₁ < M.αbar) : vstar M M.m = M.θL + M.ebar - M.c := by
  obtain ⟨hm_pos, hm_lt, hbar_lt⟩ := m_bounds M hα
  rw [(eq_6_vstar M M.m ⟨hm_pos.le, (hm_lt.trans hbar_lt).le⟩).2, if_pos ⟨le_rfl, hm_lt.le⟩]

lemma vstar_αbar (M : Params) (hα : M.α₁ < M.αbar) : vstar M M.αbar = M.θL + M.ebar - M.c := by
  obtain ⟨hm_pos, hm_lt, hbar_lt⟩ := m_bounds M hα
  rw [(eq_6_vstar M M.αbar ⟨(hm_pos.trans hm_lt).le, hbar_lt.le⟩).2, if_pos ⟨hm_lt.le, le_rfl⟩]

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

lemma concaveOn_affine (a b : ℝ) : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun x => a + b * x) := by
  refine ⟨convex_Icc 0 1, fun x _ y _ u v _ _ huv => ?_⟩
  simp only [smul_eq_mul]
  have hid : u * (a + b * x) + v * (a + b * y) = (u + v) * a + b * (u * x + v * y) := by ring
  rw [hid, huv, one_mul]

lemma concaveOn_min {f g : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f)
    (hg : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun x => min (f x) (g x)) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy u v hu hv huv => le_min ?_ ?_⟩
  · exact le_trans (add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) hu)
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hv)) (hf.2 hx hy hu hv huv)
  · exact le_trans (add_le_add (mul_le_mul_of_nonneg_left (min_le_right _ _) hu)
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hv)) (hg.2 hx hy hu hv huv)

lemma concaveClosure_eq_of_chord {f F : ℝ → ℝ}
    (hConc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) F)
    (hle : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ F x)
    {α u w t : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (hw : w ∈ Set.Icc (0 : ℝ) 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hα_eq : (1 - t) * u + t * w = α)
    (hF_eq : (1 - t) * f u + t * f w = F α) :
    concaveClosure f α = F α := by
  let H : Set (ℝ × ℝ) := {q | q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ≤ F q.1}
  have hH_conv : Convex ℝ H := by
    intro p hp q hq a b ha hb hab
    refine ⟨(convex_Icc (0 : ℝ) 1) hp.1 hq.1 ha hb hab, ?_⟩
    dsimp
    exact le_trans (add_le_add (mul_le_mul_of_nonneg_left hp.2 ha)
      (mul_le_mul_of_nonneg_left hq.2 hb)) (hConc.2 hp.1 hq.1 ha hb hab)
  have hsub : graphOn01 f ⊆ H := fun q hq => ⟨hq.1, hq.2.trans_le (hle q.1 hq.1)⟩
  have hhull : convexHull ℝ (graphOn01 f) ⊆ H := convexHull_min hsub hH_conv
  have hgreat : IsGreatest {y | (α, y) ∈ convexHull ℝ (graphOn01 f)} (F α) := by
    refine ⟨?_, fun y hy => (hhull hy).2⟩
    have hpu : (u, f u) ∈ convexHull ℝ (graphOn01 f) := subset_convexHull ℝ _ ⟨hu, rfl⟩
    have hpw : (w, f w) ∈ convexHull ℝ (graphOn01 f) := subset_convexHull ℝ _ ⟨hw, rfl⟩
    have hcomb := (convex_convexHull ℝ (graphOn01 f)) hpu hpw (sub_nonneg.mpr ht1) ht0 (by ring)
    have hpt : ((1 - t) • (u, f u) + t • (w, f w) : ℝ × ℝ) = (α, F α) := by
      ext <;> simp [hα_eq, hF_eq]
    rw [hpt] at hcomb
    exact hcomb
  exact hgreat.csSup_eq

noncomputable def L_AD (M : Params) (α : ℝ) : ℝ := M.θL - M.c + α * M.Θ
noncomputable def L_AB (M : Params) (α : ℝ) : ℝ := M.θL - M.c + α * M.ebar / M.m
noncomputable def L_BD (M : Params) (α : ℝ) : ℝ :=
  M.θL + M.ebar - M.c + (α - M.m) * (M.Θ - M.ebar) / (1 - M.m)
noncomputable def L_BC (M : Params) (_α : ℝ) : ℝ := M.θL + M.ebar - M.c
noncomputable def L_CD (M : Params) (α : ℝ) : ℝ :=
  M.θL + M.ebar - M.c + (α - M.αbar) * (M.Θ - M.ebar) / (1 - M.αbar)

lemma L_AB_concave (M : Params) : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (L_AB M) := by
  have : L_AB M = fun x => (M.θL - M.c) + (M.ebar / M.m) * x := by
    ext x; unfold L_AB; ring
  rw [this]; exact concaveOn_affine _ _

lemma L_BD_concave (M : Params) : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (L_BD M) := by
  have : L_BD M = fun x =>
      (M.θL + M.ebar - M.c - M.m * ((M.Θ - M.ebar) / (1 - M.m))) +
        ((M.Θ - M.ebar) / (1 - M.m)) * x := by
    ext x; unfold L_BD; ring
  rw [this]; exact concaveOn_affine _ _

lemma L_BC_concave (M : Params) : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (L_BC M) := by
  have : L_BC M = fun x => (M.θL + M.ebar - M.c) + 0 * x := by
    ext x; unfold L_BC; ring
  rw [this]; exact concaveOn_affine _ _

lemma L_CD_concave (M : Params) : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (L_CD M) := by
  have : L_CD M = fun x =>
      (M.θL + M.ebar - M.c - M.αbar * ((M.Θ - M.ebar) / (1 - M.αbar))) +
        ((M.Θ - M.ebar) / (1 - M.αbar)) * x := by
    ext x; unfold L_CD; ring
  rw [this]; exact concaveOn_affine _ _

lemma vstar_lt_AD (M : Params) (h_sc1 : M.ebar < M.α₀ * M.Θ) {α : ℝ}
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    vstar M α < L_AD M α := by
  rcases hα with ⟨h0, h1⟩
  rw [(eq_6_vstar M α ⟨h0.le, h1.le⟩).2]
  unfold L_AD Params.Θ
  split_ifs with hm
  · have hα0 : M.α₀ ≤ α := le_trans (le_max_left _ _) hm.1
    have hΘ := Θ_pos M
    unfold Params.Θ at h_sc1 hΘ
    nlinarith
  · refine max_lt ?_ ?_
    · nlinarith [M.θL_lt_θH]
    · nlinarith [M.c_lt_θL, M.θL_lt_θH]

lemma high_le_AB (M : Params) (hα : M.α₁ < M.αbar) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) M.m) :
    x * (M.θH - M.c) ≤ L_AB M x := by
  obtain ⟨hm_pos, _, _⟩ := m_bounds M hα
  have hm_strict := high_lt_at_m M hα
  unfold L_AB
  rw [← sub_nonneg]
  have hpos_m : M.m ≠ 0 := hm_pos.ne'
  have : M.θL - M.c + x * M.ebar / M.m - x * (M.θH - M.c) =
      ((M.m - x) * (M.θL - M.c) + x * (M.θL + M.ebar - M.c - M.m * (M.θH - M.c))) / M.m := by
    field_simp; ring
  rw [this]
  refine div_nonneg ?_ hm_pos.le
  rcases hx with ⟨hx0, hxm⟩
  nlinarith [M.c_lt_θL]

lemma high_le_BD (M : Params) (hα : M.α₁ < M.αbar) {x : ℝ} (hx : x ∈ Set.Icc M.m 1) :
    x * (M.θH - M.c) ≤ L_BD M x := by
  obtain ⟨_, hm_lt, hbar_lt⟩ := m_bounds M hα
  have h1m_pos : 0 < 1 - M.m := by linarith
  have hm_strict := high_lt_at_m M hα
  unfold L_BD Params.Θ
  rw [← sub_nonneg]
  have h1m_ne : 1 - M.m ≠ 0 := h1m_pos.ne'
  have : M.θL + M.ebar - M.c + (x - M.m) * (M.θH - M.θL - M.ebar) / (1 - M.m) - x * (M.θH - M.c) =
      (1 - x) * (M.θL + M.ebar - M.c - M.m * (M.θH - M.c)) / (1 - M.m) := by
    field_simp; ring
  rw [this]
  rcases hx with ⟨_, hx1⟩
  exact div_nonneg (by nlinarith) h1m_pos.le

lemma high_le_CD (M : Params) (hα : M.α₁ < M.αbar) {x : ℝ} (hx : x ∈ Set.Icc M.αbar 1) :
    x * (M.θH - M.c) ≤ L_CD M x := by
  obtain ⟨_, _, hbar_lt⟩ := m_bounds M hα
  have h1b_pos : 0 < 1 - M.αbar := by linarith
  have hb_strict := high_lt_at_αbar M hα
  unfold L_CD Params.Θ
  rw [← sub_nonneg]
  have h1b_ne : 1 - M.αbar ≠ 0 := h1b_pos.ne'
  have : M.θL + M.ebar - M.c + (x - M.αbar) * (M.θH - M.θL - M.ebar) / (1 - M.αbar) -
      x * (M.θH - M.c) =
      (1 - x) * (M.θL + M.ebar - M.c - M.αbar * (M.θH - M.c)) / (1 - M.αbar) := by
    field_simp; ring
  rw [this]
  rcases hx with ⟨_, hx1⟩
  exact div_nonneg (by nlinarith) h1b_pos.le

end Aux_EngageInfo_segments

open EngageInfo Aux_EngageInfo_segments

theorem solution (M : Params) (hα : M.α₁ < M.αbar) :
    (M.ebar < M.α₀ * M.Θ →
      (∀ α ∈ Set.Icc (0 : ℝ) 1, concaveClosure (vstar M) α = M.θL - M.c + α * M.Θ) ∧
      ∀ α ∈ Set.Ioo (0 : ℝ) 1, vstar M α < M.θL - M.c + α * M.Θ) ∧
    (M.α₀ * M.Θ ≤ M.ebar ∧ M.ebar ≤ M.Θ →
      (∀ α ∈ Set.Icc (0 : ℝ) M.m, concaveClosure (vstar M) α = M.θL - M.c + α * M.ebar / M.m) ∧
      ∀ α ∈ Set.Icc M.m 1, concaveClosure (vstar M) α =
        M.θL + M.ebar - M.c + (α - M.m) * (M.Θ - M.ebar) / (1 - M.m)) ∧
    (M.Θ < M.ebar →
      (∀ α ∈ Set.Icc (0 : ℝ) M.m, concaveClosure (vstar M) α = M.θL - M.c + α * M.ebar / M.m) ∧
      (∀ α ∈ Set.Icc M.m M.αbar, concaveClosure (vstar M) α = M.θL + M.ebar - M.c) ∧
      ∀ α ∈ Set.Icc M.αbar 1, concaveClosure (vstar M) α =
        M.θL + M.ebar - M.c + (α - M.αbar) * (M.Θ - M.ebar) / (1 - M.αbar)) := by
  obtain ⟨hm_pos, hm_lt, hbar_lt⟩ := m_bounds M hα
  have hm_lt1 : M.m < 1 := hm_lt.trans hbar_lt
  have h1m_pos : 0 < 1 - M.m := by linarith
  have h1b_pos : 0 < 1 - M.αbar := by linarith
  have hm_mem : M.m ∈ Set.Icc (0 : ℝ) 1 := ⟨hm_pos.le, hm_lt1.le⟩
  have hbar_mem : M.αbar ∈ Set.Icc (0 : ℝ) 1 := ⟨(hm_pos.trans hm_lt).le, hbar_lt.le⟩
  refine ⟨fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
  · -- Scenario (i): ē < α₀ Θ
    have hConc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (L_AD M) := by
      have : L_AD M = fun x => (M.θL - M.c) + M.Θ * x := by ext x; unfold L_AD; ring
      rw [this]; exact concaveOn_affine _ _
    have hle : ∀ x ∈ Set.Icc (0 : ℝ) 1, vstar M x ≤ L_AD M x := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with rfl | hx0
      · rw [vstar_0 M hα]; unfold L_AD; ring_nf; exact le_rfl
      · rcases eq_or_lt_of_le hx.2 with rfl | hx1
        · rw [vstar_1 M hα]; unfold L_AD Params.Θ; linarith
        · exact (vstar_lt_AD M h1 ⟨hx0, hx1⟩).le
    refine ⟨fun α hα_mem => ?_, fun α hα_oo => vstar_lt_AD M h1 hα_oo⟩
    exact concaveClosure_eq_of_chord hConc hle ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
      hα_mem.1 hα_mem.2 (by ring)
      (by rw [vstar_0 M hα, vstar_1 M hα]; unfold L_AD Params.Θ; ring)
  · -- Scenario (ii): α₀ Θ ≤ ē ≤ Θ
    let F2 := fun x => min (L_AB M x) (L_BD M x)
    have hConc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) F2 :=
      concaveOn_min (L_AB_concave M) (L_BD_concave M)
    have hmΘ_le : M.m * M.Θ ≤ M.ebar := by
      have hα1Θ : M.α₁ * M.Θ = M.k := div_mul_cancel₀ _ (Θ_pos M).ne'
      unfold Params.m
      rcases max_choice M.α₀ M.α₁ with hm0 | hm1
      · rw [hm0]; exact h2.1
      · rw [hm1, hα1Θ]; exact M.k_lt_ebar.le
    have hF2_left : ∀ x ≤ M.m, F2 x = L_AB M x := by
      intro x hx
      refine min_eq_left ?_
      unfold L_AB L_BD
      have hm_ne : M.m ≠ 0 := hm_pos.ne'
      have h1m_ne : 1 - M.m ≠ 0 := h1m_pos.ne'
      rw [← sub_nonneg]
      have : M.θL + M.ebar - M.c + (x - M.m) * (M.Θ - M.ebar) / (1 - M.m) -
          (M.θL - M.c + x * M.ebar / M.m) =
          (M.m - x) * (M.ebar - M.m * M.Θ) / (M.m * (1 - M.m)) := by
        field_simp; ring
      rw [this]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_pos hm_pos h1m_pos).le
    have hF2_right : ∀ x, M.m ≤ x → F2 x = L_BD M x := by
      intro x hx
      refine min_eq_right ?_
      unfold L_AB L_BD
      have hm_ne : M.m ≠ 0 := hm_pos.ne'
      have h1m_ne : 1 - M.m ≠ 0 := h1m_pos.ne'
      rw [← sub_nonneg]
      have : M.θL - M.c + x * M.ebar / M.m -
          (M.θL + M.ebar - M.c + (x - M.m) * (M.Θ - M.ebar) / (1 - M.m)) =
          (x - M.m) * (M.ebar - M.m * M.Θ) / (M.m * (1 - M.m)) := by
        field_simp; ring
      rw [this]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_pos hm_pos h1m_pos).le
    have hle : ∀ x ∈ Set.Icc (0 : ℝ) 1, vstar M x ≤ F2 x := by
      intro x hx
      rw [(eq_6_vstar M x hx).2]
      by_cases hxm : x ≤ M.m
      · rw [hF2_left x hxm]
        split_ifs with hint
        · have hxeq : x = M.m := le_antisymm hxm hint.1
          subst hxeq
          unfold L_AB
          rw [mul_div_cancel_left₀ _ hm_pos.ne']
          linarith
        · refine max_le ?_ (high_le_AB M hα ⟨hx.1, hxm⟩)
          unfold L_AB
          have : 0 ≤ x * M.ebar / M.m := div_nonneg (mul_nonneg hx.1 (ebar_pos M).le) hm_pos.le
          linarith
      · push_neg at hxm
        rw [hF2_right x hxm.le]
        split_ifs with hint
        · unfold L_BD
          have : 0 ≤ (x - M.m) * (M.Θ - M.ebar) / (1 - M.m) :=
            div_nonneg (mul_nonneg (by linarith) (by linarith [h2.2])) h1m_pos.le
          linarith
        · refine max_le ?_ (high_le_BD M hα ⟨hxm.le, hx.2⟩)
          have hα0_lt : M.α₀ < x := lt_of_le_of_lt (le_max_left _ _) hxm
          unfold Params.α₀ Params.alpha at hα0_lt
          simp only [add_zero] at hα0_lt
          have hlow_lt := (div_lt_iff₀ (by linarith [M.c_lt_θL, M.θL_lt_θH])).mp hα0_lt
          exact le_trans hlow_lt.le (high_le_BD M hα ⟨hxm.le, hx.2⟩)
    refine ⟨fun α hα_mem => ?_, fun α hα_mem => ?_⟩
    · change concaveClosure (vstar M) α = L_AB M α
      rw [← hF2_left α hα_mem.2]
      refine concaveClosure_eq_of_chord (t := α / M.m) hConc hle ⟨le_rfl, zero_le_one⟩ hm_mem
        (div_nonneg hα_mem.1 hm_pos.le) ((div_le_one hm_pos).mpr hα_mem.2)
        (by have := hm_pos.ne'; field_simp; ring) ?_
      rw [hF2_left α hα_mem.2, vstar_0 M hα, vstar_m M hα]
      unfold L_AB
      have := hm_pos.ne'; field_simp; ring
    · change concaveClosure (vstar M) α = L_BD M α
      rw [← hF2_right α hα_mem.1]
      refine concaveClosure_eq_of_chord (t := (α - M.m) / (1 - M.m)) hConc hle hm_mem
        ⟨zero_le_one, le_rfl⟩
        (div_nonneg (sub_nonneg.mpr hα_mem.1) h1m_pos.le)
        ((div_le_one h1m_pos).mpr (by linarith [hα_mem.2]))
        (by have := h1m_pos.ne'; field_simp; ring) ?_
      rw [hF2_right α hα_mem.1, vstar_m M hα, vstar_1 M hα]
      unfold L_BD Params.Θ
      have := h1m_pos.ne'; field_simp; ring
  · -- Scenario (iii): Θ < ē
    let F3 := fun x => min (min (L_AB M x) (L_BC M x)) (L_CD M x)
    have hConc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) F3 :=
      concaveOn_min (concaveOn_min (L_AB_concave M) (L_BC_concave M)) (L_CD_concave M)
    have hAB_le_BC : ∀ x ≤ M.m, L_AB M x ≤ L_BC M x := by
      intro x hx
      unfold L_AB L_BC
      have : x * M.ebar / M.m ≤ M.ebar := by
        rw [div_le_iff₀ hm_pos]
        nlinarith [ebar_pos M]
      linarith
    have hBC_le_AB : ∀ x, M.m ≤ x → L_BC M x ≤ L_AB M x := by
      intro x hx
      unfold L_AB L_BC
      have : M.ebar ≤ x * M.ebar / M.m := by
        rw [le_div_iff₀ hm_pos]
        nlinarith [ebar_pos M]
      linarith
    have hBC_le_CD : ∀ x ≤ M.αbar, L_BC M x ≤ L_CD M x := by
      intro x hx
      unfold L_BC L_CD
      have hnum : 0 ≤ (x - M.αbar) * (M.Θ - M.ebar) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      have := div_nonneg hnum h1b_pos.le
      linarith
    have hCD_le_BC : ∀ x, M.αbar ≤ x → L_CD M x ≤ L_BC M x := by
      intro x hx
      unfold L_BC L_CD
      have hnum : (x - M.αbar) * (M.Θ - M.ebar) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have := div_nonpos_of_nonpos_of_nonneg hnum h1b_pos.le
      linarith
    have hF3_1 : ∀ x ≤ M.m, F3 x = L_AB M x := fun x hx => by
      dsimp [F3]
      rw [min_eq_left (hAB_le_BC x hx),
        min_eq_left ((hAB_le_BC x hx).trans (hBC_le_CD x (hx.trans hm_lt.le)))]
    have hF3_2 : ∀ x, M.m ≤ x → x ≤ M.αbar → F3 x = L_BC M x := fun x h1 h2 => by
      dsimp [F3]
      rw [min_eq_right (hBC_le_AB x h1), min_eq_left (hBC_le_CD x h2)]
    have hF3_3 : ∀ x, M.αbar ≤ x → F3 x = L_CD M x := fun x hx => by
      dsimp [F3]
      rw [min_eq_right (hBC_le_AB x (hm_lt.le.trans hx)), min_eq_right (hCD_le_BC x hx)]
    have hle : ∀ x ∈ Set.Icc (0 : ℝ) 1, vstar M x ≤ F3 x := by
      intro x hx
      rw [(eq_6_vstar M x hx).2]
      by_cases hxm : x ≤ M.m
      · rw [hF3_1 x hxm]
        split_ifs with hint
        · have hxeq : x = M.m := le_antisymm hxm hint.1
          subst hxeq; unfold L_AB; rw [mul_div_cancel_left₀ _ hm_pos.ne']; linarith
        · refine max_le ?_ (high_le_AB M hα ⟨hx.1, hxm⟩)
          unfold L_AB
          have : 0 ≤ x * M.ebar / M.m := div_nonneg (mul_nonneg hx.1 (ebar_pos M).le) hm_pos.le
          linarith
      · push_neg at hxm
        by_cases hxb : x ≤ M.αbar
        · rw [hF3_2 x hxm.le hxb, if_pos ⟨hxm.le, hxb⟩]; unfold L_BC; exact le_rfl
        · push_neg at hxb
          rw [hF3_3 x hxb.le, if_neg (by intro h; linarith [h.2])]
          have hα0_lt : M.α₀ < x := (α₀_lt_αbar M).trans hxb
          unfold Params.α₀ Params.alpha at hα0_lt
          simp only [add_zero] at hα0_lt
          have hlow_lt := (div_lt_iff₀ (by linarith [M.c_lt_θL, M.θL_lt_θH])).mp hα0_lt
          exact max_le (hlow_lt.le.trans (high_le_CD M hα ⟨hxb.le, hx.2⟩))
            (high_le_CD M hα ⟨hxb.le, hx.2⟩)
    refine ⟨fun α hα_mem => ?_, fun α hα_mem => ?_, fun α hα_mem => ?_⟩
    · change concaveClosure (vstar M) α = L_AB M α
      rw [← hF3_1 α hα_mem.2]
      refine concaveClosure_eq_of_chord (t := α / M.m) hConc hle ⟨le_rfl, zero_le_one⟩ hm_mem
        (div_nonneg hα_mem.1 hm_pos.le) ((div_le_one hm_pos).mpr hα_mem.2)
        (by have := hm_pos.ne'; field_simp; ring) ?_
      rw [hF3_1 α hα_mem.2, vstar_0 M hα, vstar_m M hα]
      unfold L_AB; have := hm_pos.ne'; field_simp; ring
    · change concaveClosure (vstar M) α = L_BC M α
      rw [← hF3_2 α hα_mem.1 hα_mem.2]
      have hlen : 0 < M.αbar - M.m := by linarith
      refine concaveClosure_eq_of_chord (t := (α - M.m) / (M.αbar - M.m)) hConc hle hm_mem hbar_mem
        (div_nonneg (sub_nonneg.mpr hα_mem.1) hlen.le)
        ((div_le_one hlen).mpr (by linarith [hα_mem.2]))
        (by have := hlen.ne'; field_simp; ring) ?_
      rw [hF3_2 α hα_mem.1 hα_mem.2, vstar_m M hα, vstar_αbar M hα]
      unfold L_BC; ring
    · change concaveClosure (vstar M) α = L_CD M α
      rw [← hF3_3 α hα_mem.1]
      refine concaveClosure_eq_of_chord (t := (α - M.αbar) / (1 - M.αbar)) hConc hle hbar_mem
        ⟨zero_le_one, le_rfl⟩
        (div_nonneg (sub_nonneg.mpr hα_mem.1) h1b_pos.le)
        ((div_le_one h1b_pos).mpr (by linarith [hα_mem.2]))
        (by have := h1b_pos.ne'; field_simp; ring) ?_
      rw [hF3_3 α hα_mem.1, vstar_αbar M hα, vstar_1 M hα]
      unfold L_CD Params.Θ; have := h1b_pos.ne'; field_simp; ring
