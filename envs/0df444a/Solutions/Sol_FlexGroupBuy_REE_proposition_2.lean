-- Prove2me | solution 1 for FlexGroupBuy.REE.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:11:30.928393+00:00
-- url     : https://prove2.me/submissions/7a46bc25-4d58-488b-92d2-987654df5459

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model
import Theorems.Thm_FlexGroupBuy_REE_price_switch
import Theorems.Thm_FlexGroupBuy_REE_profit_formula
import Theorems.Thm_FlexGroupBuy_REE_late_branch
import Theorems.Thm_FlexGroupBuy_REE_early_branch
import Theorems.Thm_FlexGroupBuy_REE_xbar1_pos_iff
import Theorems.Thm_FlexGroupBuy_REE_Nbar_order

open FlexGroupBuy.REE

/-- Late-branch profit fraction (Online Appendix p. 4). -/
noncomputable def FGB_fL (P : Params) (N : ℕ) (y : ℝ) : ℝ :=
  (P.theta * P.L * P.gam * P.lam * N + P.L * (1 - P.gam) * P.lam * (N - y)
    - P.c * P.gam * N * (y - 1)) / (N - (1 - P.gam) * y)

/-- Its derivative. -/
noncomputable def FGB_dL (P : Params) (N : ℕ) (x : ℝ) : ℝ :=
  (P.gam * N * (P.L * (1 - P.gam) * (P.theta - 1) * P.lam - P.c * ((N : ℝ) - 1 + P.gam))
    / (N - (1 - P.gam) * x) ^ 2)

/-- Early-branch profit fraction (Online Appendix p. 4). -/
noncomputable def FGB_fE (P : Params) (N : ℕ) (y : ℝ) : ℝ :=
  (((P.theta - 1) * P.H + P.L) * P.gam * P.lam * N
    + P.L * (1 - P.gam) * P.lam * (N - y) - P.c * N * ((N : ℝ) - 1)
    + P.c * (1 - P.gam) * N * y) / (N - (1 - P.gam) * y)

/-- Its derivative. -/
noncomputable def FGB_dE (P : Params) (N : ℕ) (x : ℝ) : ℝ :=
  ((1 - P.gam) * N * (P.c + (P.theta - 1) * P.H * P.gam * P.lam) / (N - (1 - P.gam) * x) ^ 2)

theorem FGB_aux_mono (f f' : ℝ → ℝ) (a b : ℝ) (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (h0 : ∀ x ∈ Set.Icc a b, 0 ≤ f' x) : MonotoneOn f (Set.Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx; rw [interior_Icc] at hx
    exact (hd x (Set.Ioo_subset_Icc_self hx)).hasDerivWithinAt
  · intro x hx; rw [interior_Icc] at hx; exact h0 x (Set.Ioo_subset_Icc_self hx)

theorem FGB_aux_anti (f f' : ℝ → ℝ) (a b : ℝ) (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (h0 : ∀ x ∈ Set.Icc a b, f' x ≤ 0) : AntitoneOn f (Set.Icc a b) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx; rw [interior_Icc] at hx
    exact (hd x (Set.Ioo_subset_Icc_self hx)).hasDerivWithinAt
  · intro x hx; rw [interior_Icc] at hx; exact h0 x (Set.Ioo_subset_Icc_self hx)

theorem solution (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N) :
    (P.H / P.L ≤ 1 / P.gam →
      ((N : ℝ) ≤ Nbar1 P →
          IsOptimalTip P N N ∧
          pG P N N = P.theta * P.L - P.c * ((N : ℝ) - 1) / P.lam ∧
          piG P N N = P.theta * P.L * P.lam - P.c * ((N : ℝ) - 1)) ∧
      (Nbar1 P < N →
          0 < xbar1 P N ∧ xbar1 P N < N ∧ IsOptimalTip P N (xbar1 P N) ∧
          pG P N (xbar1 P N) = P.theta * P.L + P.gam * (P.theta - 1) * (P.H - P.L)
                                 - P.c * ((N : ℝ) - 2 + P.gam) / P.lam ∧
          piG P N (xbar1 P N) = piG1 P N)) ∧
    (1 / P.gam < P.H / P.L →
      ((N : ℝ) ≤ Nbar2 P →
          IsOptimalTip P N 0 ∧
          pG P N 0 = (P.theta - 1) * P.H + P.L - P.c * ((N : ℝ) - 1) / (P.gam * P.lam) ∧
          piG P N 0 = (P.theta - 1) * P.H * P.gam * P.lam + P.L * P.lam - P.c * ((N : ℝ) - 1)) ∧
      (Nbar2 P < N →
          0 < xbar1 P N ∧ xbar1 P N < N ∧ IsOptimalTip P N (xbar1 P N) ∧
          pG P N (xbar1 P N) = P.theta * P.L + P.gam * (P.theta - 1) * (P.H - P.L)
                                 - P.c * ((N : ℝ) - 2 + P.gam) / P.lam ∧
          piG P N (xbar1 P N) = piG1 P N)) := by

  have hP' := hP
  obtain ⟨hL, hLH, hg0, hg1, hl, hc, ht⟩ := hP'
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨LA, LB, LC⟩ := late_branch P hP N hN
  obtain ⟨EA, EB, EC⟩ := early_branch P hP N hN
  have LA' : ∀ x : ℝ, 0 < x → x ≤ N → xbar1 P N < x → piG P N x = FGB_fL P N x := LA
  have EA' : ∀ x ∈ Set.Icc (0 : ℝ) N, x ≤ xbar1 P N → piG P N x = FGB_fE P N x := EA
  have hdom : ∀ x ∈ Set.Icc (0 : ℝ) N, (1 - P.gam) * x < N := by
    intro x hx
    have : (1 - P.gam) * x ≤ (1 - P.gam) * N := mul_le_mul_of_nonneg_left hx.2 (by linarith)
    nlinarith
  have hDpos : ∀ x ∈ Set.Icc (0 : ℝ) N, 0 < (N : ℝ) - (1 - P.gam) * x := fun x hx => by
    linarith [hdom x hx]
  have LB' : ∀ x ∈ Set.Icc (0 : ℝ) N, HasDerivAt (FGB_fL P N) (FGB_dL P N x) x :=
    fun x hx => LB x (hdom x hx)
  have EB' : ∀ x ∈ Set.Icc (0 : ℝ) N, HasDerivAt (FGB_fE P N) (FGB_dE P N x) x :=
    fun x hx => EB x (hdom x hx)
  have FEmono : MonotoneOn (FGB_fE P N) (Set.Icc 0 N) :=
    FGB_aux_mono _ _ 0 N EB' (fun x hx => (EC x (hdom x hx)).le)
  have FLmono : (N : ℝ) ≤ Nbar1 P → MonotoneOn (FGB_fL P N) (Set.Icc 0 N) := fun h =>
    FGB_aux_mono _ _ 0 N LB' (fun x hx => (LC x (hdom x hx)).mpr h)
  have FLanti : Nbar1 P < N → AntitoneOn (FGB_fL P N) (Set.Icc 0 N) := fun h =>
    FGB_aux_anti _ _ 0 N LB' (fun x hx => by
      have := (LC x (hdom x hx)).not.mpr (not_le.mpr h)
      exact (not_le.mp this).le)
  have hK : 0 < (P.theta - 1) * (P.H - P.L) * P.gam * P.lam / P.c := by
    apply div_pos _ hc
    apply mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) hg0) hl
  have hX : xbar1 P N < N := by unfold xbar1; linarith
  have hNmem : (N : ℝ) ∈ Set.Icc (0 : ℝ) N := ⟨by linarith, le_refl _⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) N := ⟨le_refl _, by linarith⟩
  -- closed forms at the endpoints
  have hpGN : pG P N N = P.theta * P.L - P.c * ((N : ℝ) - 1) / P.lam := by
    have hle : pbar1 P N ≤ pbar2 P N N := by
      unfold pbar1 pbar2; nlinarith [mul_pos (by linarith : (0:ℝ) < P.theta - 1) (by linarith : (0:ℝ) < P.H - P.L)]
    unfold pG
    rw [if_neg (by linarith), min_eq_left hle]
    unfold pbar1 wG; rw [if_pos (le_refl _)]; ring
  have hpiN : piG P N N = P.theta * P.L * P.lam - P.c * ((N : ℝ) - 1) := by
    rw [LA' N (by linarith) le_rfl hX]
    unfold FGB_fL
    have : (N : ℝ) - (1 - P.gam) * N = P.gam * N := by ring
    rw [this, div_eq_iff (by positivity)]
    ring
  have hpG0 : pG P N 0 = (P.theta - 1) * P.H + P.L - P.c * ((N : ℝ) - 1) / (P.gam * P.lam) := by
    unfold pG; rw [if_pos rfl]
    unfold pbar2 wG; rw [if_neg (not_le.mpr (by linarith))]
    field_simp; ring
  have hpi0 : piG P N 0 = (P.theta - 1) * P.H * P.gam * P.lam + P.L * P.lam - P.c * ((N : ℝ) - 1) := by
    rw [profit_formula P hP N hN 0 h0mem, hpG0]
    rw [div_eq_iff (by simp; linarith)]
    field_simp; ring
  have hFL0 : FGB_fL P N 0 = piG P N 0 + P.c * xbar1 P N := by
    rw [hpi0]; unfold FGB_fL xbar1
    rw [div_eq_iff (by simp; linarith)]
    field_simp; ring
  have hagree : FGB_fL P N (xbar1 P N) = FGB_fE P N (xbar1 P N) := by
    unfold FGB_fL FGB_fE
    congr 1
    have e : P.c * ((N : ℝ) - 1 + P.gam - xbar1 P N) = (P.theta - 1) * (P.H - P.L) * P.gam * P.lam := by
      unfold xbar1; field_simp; ring
    linear_combination (N : ℝ) * e
  -- the interior case (i-2) / (ii-2)
  have mid : 0 < xbar1 P N → Nbar1 P < N →
      0 < xbar1 P N ∧ xbar1 P N < N ∧ IsOptimalTip P N (xbar1 P N) ∧
          pG P N (xbar1 P N) = P.theta * P.L + P.gam * (P.theta - 1) * (P.H - P.L)
                                 - P.c * ((N : ℝ) - 2 + P.gam) / P.lam ∧
          piG P N (xbar1 P N) = piG1 P N := by
    intro h0 h1
    have hxmem : xbar1 P N ∈ Set.Icc (0 : ℝ) N := ⟨h0.le, hX.le⟩
    have hpix : piG P N (xbar1 P N) = FGB_fE P N (xbar1 P N) := EA' _ hxmem le_rfl
    refine ⟨h0, hX, ⟨hxmem, ?_⟩, ?_, ?_⟩
    · intro y hy
      rw [hpix]
      rcases le_or_gt y (xbar1 P N) with hyx | hyx
      · rw [EA' y hy hyx]; exact FEmono hy hxmem hyx
      · rw [LA' y (by linarith) hy.2 hyx, ← hagree]
        exact FLanti h1 hxmem hy hyx.le
    · have hnl : ¬ pbar1 P (xbar1 P N) < pbar2 P N (xbar1 P N) := by
        rw [price_switch P hP N hN _ hxmem]; exact lt_irrefl _
      unfold pG
      rw [if_neg h0.ne', min_eq_right (not_lt.mp hnl)]
      unfold pbar2 wG
      rw [if_neg (not_le.mpr hX)]
      unfold xbar1
      field_simp; ring
    · rw [hpix]
      unfold FGB_fE piG1
      have hd1 := hDpos _ hxmem
      have hd2 : 0 < P.c * (1 + P.gam * ((N : ℝ) - 2 + P.gam))
          + (P.theta - 1) * (P.H - P.L) * (1 - P.gam) * P.gam * P.lam := by
        have : 0 < 1 + P.gam * ((N : ℝ) - 2 + P.gam) := by nlinarith
        have : 0 < (P.theta - 1) * (P.H - P.L) * (1 - P.gam) * P.gam * P.lam :=
          mul_pos (mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) hg0) hl
        positivity
      rw [div_eq_div_iff hd1.ne' hd2.ne']
      unfold xbar1
      field_simp
      ring
  have hiff1 : P.H / P.L ≤ 1 / P.gam ↔ P.gam * P.H ≤ P.L := by
    rw [div_le_div_iff₀ hL hg0]; constructor <;> intro h <;> linarith
  have hiff2 : 1 / P.gam < P.H / P.L ↔ P.L < P.gam * P.H := by
    rw [div_lt_div_iff₀ hg0 hL]; constructor <;> intro h <;> linarith
  refine ⟨fun hc1 => ⟨fun hN1 => ⟨⟨hNmem, ?_⟩, hpGN, hpiN⟩, fun hN1 => ?_⟩,
          fun hc2 => ⟨fun hN2 => ⟨⟨h0mem, ?_⟩, hpG0, hpi0⟩, fun hN2 => ?_⟩⟩
  · -- (i-1)
    have hgH := hiff1.mp hc1
    intro y hy
    rcases eq_or_lt_of_le hy.1 with hy0 | hy0
    · subst hy0; rw [hpi0, hpiN]
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ P.theta - 1) hl.le) (by linarith : (0:ℝ) ≤ P.L - P.gam * P.H)]
    · rw [LA' N (by linarith) le_rfl hX]
      rcases le_or_gt y (xbar1 P N) with hyx | hyx
      · have hxmem : xbar1 P N ∈ Set.Icc (0 : ℝ) N := ⟨by linarith, hX.le⟩
        rw [EA' y hy hyx]
        calc FGB_fE P N y ≤ FGB_fE P N (xbar1 P N) := FEmono hy hxmem hyx
          _ = FGB_fL P N (xbar1 P N) := hagree.symm
          _ ≤ FGB_fL P N N := FLmono hN1 hxmem hNmem hX.le
      · rw [LA' y hy0 hy.2 hyx]; exact FLmono hN1 hy hNmem hy.2
  · -- (i-2)
    have hnot : ¬ Nbar1 P < Nbar2 P := fun h => (not_lt.mpr hc1) ((Nbar_order P hP).mp h)
    have h0 : 0 < xbar1 P N := (xbar1_pos_iff P hP N hN).mpr (by linarith [not_lt.mp hnot])
    exact mid h0 hN1
  · -- (ii-1)
    have hgH := hiff2.mp hc2
    have hx0 : xbar1 P N ≤ 0 := not_lt.mp (fun h => (not_lt.mpr hN2) ((xbar1_pos_iff P hP N hN).mp h))
    intro y hy
    rcases eq_or_lt_of_le hy.1 with hy0 | hy0
    · rw [← hy0]
    · rw [LA' y hy0 hy.2 (by linarith)]
      rcases le_or_gt (N : ℝ) (Nbar1 P) with hN1 | hN1
      · calc FGB_fL P N y ≤ FGB_fL P N N := FLmono hN1 hy hNmem hy.2
          _ = piG P N N := (LA' N (by linarith) le_rfl hX).symm
          _ ≤ piG P N 0 := by
            rw [hpi0, hpiN]
            nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ P.theta - 1) hl.le) (by linarith : (0:ℝ) ≤ P.gam * P.H - P.L)]
      · calc FGB_fL P N y ≤ FGB_fL P N 0 := FLanti hN1 h0mem hy hy.1
          _ = piG P N 0 + P.c * xbar1 P N := hFL0
          _ ≤ piG P N 0 := by nlinarith
  · -- (ii-2)
    have h0 : 0 < xbar1 P N := (xbar1_pos_iff P hP N hN).mpr hN2
    have h1 : Nbar1 P < N := by linarith [(Nbar_order P hP).mpr hc2]
    exact mid h0 h1
