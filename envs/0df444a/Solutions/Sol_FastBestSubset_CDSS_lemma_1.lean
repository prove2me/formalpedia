-- Prove2me | solution 1 for FastBestSubset.CDSS.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T06:06:24.656124+00:00
-- url     : https://prove2.me/submissions/5a55f98e-09f8-4309-a14c-f636fed5af2c

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

set_option autoImplicit false

open Filter Topology FastBestSubset.CDSS

namespace FastBestSubset.CDSS.Lemma1Proof

noncomputable def gradCoord {n p : ℕ} (D : Data n p) (β : Fin p → ℝ) (i : Fin p) : ℝ :=
  -∑ r, (D.y r - ∑ j, D.X r j * β j) * D.X r i +
    D.lam1 * (if 0 < β i then 1 else -1) + 2 * D.lam2 * β i

theorem nhdsGT_zero_neBot : NeBot (𝓝[>] (0 : ℝ)) := by
  rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioi]
  exact Set.mem_Ici.mpr le_rfl

theorem liminf_ereal_nonneg {q : ℝ → ℝ} (hq : ∀ᶠ α in 𝓝[>] (0 : ℝ), 0 ≤ q α) :
    (0 : EReal) ≤ Filter.liminf (fun α : ℝ => ((q α : ℝ) : EReal)) (𝓝[>] (0 : ℝ)) := by
  rw [Filter.liminf_eq]
  exact le_sSup (hq.mono fun α hα => EReal.coe_nonneg.mpr hα)

theorem f_local_taylor {n p : ℕ} (D : Data n p) (β d : Fin p → ℝ) (α : ℝ)
    (hd_supp : ∀ j, j ∉ supp β → d j = 0)
    (hsign : ∀ i ∈ supp β, (0 < β i → 0 < β i + α * d i) ∧ (β i < 0 → β i + α * d i < 0)) :
    f D (β + α • d) - f D β =
      α * (∑ i, d i * gradCoord D β i) +
        α ^ 2 * ((1 / 2 : ℝ) * ∑ r, (∑ j, D.X r j * d j) ^ 2 + D.lam2 * ∑ j, d j ^ 2) := by
  have hres : (1 / 2 : ℝ) * ∑ r, (D.y r - ∑ j, D.X r j * (β j + α * d j)) ^ 2 -
      (1 / 2 : ℝ) * ∑ r, (D.y r - ∑ j, D.X r j * β j) ^ 2 =
      -α * ∑ i, d i * (∑ r, (D.y r - ∑ j, D.X r j * β j) * D.X r i) +
        α ^ 2 * ((1 / 2 : ℝ) * ∑ r, (∑ j, D.X r j * d j) ^ 2) := by
    have hrow : ∀ r : Fin n,
        (D.y r - ∑ j, D.X r j * (β j + α * d j)) ^ 2 -
          (D.y r - ∑ j, D.X r j * β j) ^ 2 =
        -2 * α * ∑ i, d i * ((D.y r - ∑ j, D.X r j * β j) * D.X r i) +
          α ^ 2 * (∑ j, D.X r j * d j) ^ 2 := by
      intro r
      have hlin : ∑ j, D.X r j * (β j + α * d j) =
          (∑ j, D.X r j * β j) + α * ∑ j, D.X r j * d j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hcross : (D.y r - ∑ j, D.X r j * β j) * ∑ i, D.X r i * d i =
          ∑ i, d i * ((D.y r - ∑ j, D.X r j * β j) * D.X r i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hlin]
      linear_combination -2 * α * hcross
    rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun r _ => hrow r,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    ring
  have hl1 : ∑ j, |β j + α * d j| - ∑ j, |β j| =
      α * ∑ i, d i * (if 0 < β i then (1 : ℝ) else -1) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ supp β
    · have hne : β j ≠ 0 := (Finset.mem_filter.mp hj).2
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have hneg' := (hsign j hj).2 hneg
        have hnotpos : ¬ 0 < β j := not_lt.mpr hneg.le
        rw [if_neg hnotpos, abs_of_neg hneg', abs_of_neg hneg]
        ring
      · have hpos' := (hsign j hj).1 hpos
        rw [if_pos hpos, abs_of_pos hpos', abs_of_pos hpos]
        ring
    · have hβ0 : β j = 0 := by
        by_contra h; exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
      have hd0 : d j = 0 := hd_supp j hj
      simp [hβ0, hd0]
  have hl2 : ∑ j, (β j + α * d j) ^ 2 - ∑ j, β j ^ 2 =
      α * ∑ i, d i * (2 * β i) + α ^ 2 * ∑ j, d j ^ 2 := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcomb : f D (β + α • d) - f D β =
      ((1 / 2 : ℝ) * ∑ r, (D.y r - ∑ j, D.X r j * (β j + α * d j)) ^ 2 -
        (1 / 2 : ℝ) * ∑ r, (D.y r - ∑ j, D.X r j * β j) ^ 2) +
      D.lam1 * (∑ j, |β j + α * d j| - ∑ j, |β j|) +
      D.lam2 * (∑ j, (β j + α * d j) ^ 2 - ∑ j, β j ^ 2) := by
    unfold f
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hcomb, hres, hl1, hl2]
  have hgrad : -α * ∑ i, d i * (∑ r, (D.y r - ∑ j, D.X r j * β j) * D.X r i) +
        D.lam1 * (α * ∑ i, d i * if 0 < β i then 1 else -1) +
        D.lam2 * (α * ∑ i, d i * (2 * β i)) =
      α * ∑ i, d i * gradCoord D β i := by
    have hsum : ∑ i, d i * gradCoord D β i =
        -(∑ i, d i * (∑ r, (D.y r - ∑ j, D.X r j * β j) * D.X r i)) +
          D.lam1 * (∑ i, d i * if 0 < β i then 1 else -1) +
          D.lam2 * (∑ i, d i * (2 * β i)) := by
      unfold gradCoord
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    ring
  linarith

theorem hasDerivAt_coord {n p : ℕ} (D : Data n p) (β : Fin p → ℝ) {i : Fin p}
    (hi : i ∈ supp β) :
    HasDerivAt (fun t : ℝ => f D (Function.update β i t)) (gradCoord D β i) (β i) := by
  have hβi : β i ≠ 0 := (Finset.mem_filter.mp hi).2
  have habs_pos : 0 < |β i| := abs_pos.mpr hβi
  let d : Fin p → ℝ := Pi.single i 1
  let C₂ : ℝ := (1 / 2 : ℝ) * ∑ r, (∑ j, D.X r j * d j) ^ 2 + D.lam2 * ∑ j, d j ^ 2
  let q : ℝ → ℝ := fun t => f D β + (t - β i) * gradCoord D β i + (t - β i) ^ 2 * C₂
  have hq_deriv : HasDerivAt q (gradCoord D β i) (β i) := by
    have hsub : HasDerivAt (fun t : ℝ => t - β i) 1 (β i) := (hasDerivAt_id (β i)).sub_const (β i)
    have h1 : HasDerivAt (fun t : ℝ => (t - β i) * gradCoord D β i)
        (1 * gradCoord D β i) (β i) := hsub.mul_const _
    have h2 : HasDerivAt (fun t : ℝ => (t - β i) ^ 2 * C₂)
        ((2 * (β i - β i) ^ (2 - 1) * 1) * C₂) (β i) := (hsub.pow 2).mul_const C₂
    have h0 : HasDerivAt (fun _ : ℝ => f D β) 0 (β i) := hasDerivAt_const (β i) (f D β)
    have hd_tot := (h0.add h1).add h2
    have hval : 0 + 1 * gradCoord D β i + 2 * (β i - β i) ^ (2 - 1) * 1 * C₂ =
        gradCoord D β i := by ring
    rw [hval] at hd_tot
    exact hd_tot
  refine hq_deriv.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds (β i) habs_pos] with t ht
  rw [Metric.mem_ball, Real.dist_eq] at ht
  obtain ⟨ht1, ht2⟩ := abs_lt.mp ht
  have hupd : Function.update β i t = β + (t - β i) • d := by
    ext j
    by_cases hji : j = i
    · subst hji; simp [d]
    · simp [d, hji]
  have hd_supp : ∀ j, j ∉ supp β → d j = 0 := by
    intro j hj
    have hji : j ≠ i := fun h => hj (h ▸ hi)
    simp [d, hji]
  have hsign : ∀ k ∈ supp β,
      (0 < β k → 0 < β k + (t - β i) * d k) ∧ (β k < 0 → β k + (t - β i) * d k < 0) := by
    intro k _
    by_cases hki : k = i
    · subst hki
      simp only [d, Pi.single_eq_same, mul_one, add_sub_cancel]
      exact ⟨fun h => by have := abs_of_pos h; linarith,
        fun h => by have := abs_of_neg h; linarith⟩
    · simp [d, hki]
  have htaylor := f_local_taylor D β d (t - β i) hd_supp hsign
  have hsum_d : ∑ j, d j * gradCoord D β j = gradCoord D β i := by
    rw [Finset.sum_eq_single i]
    · simp [d]
    · intro j _ hji; simp [d, hji]
    · intro habs; exact absurd (Finset.mem_univ i) habs
  rw [hupd]
  rw [hsum_d] at htaylor
  dsimp only [q, C₂]
  linarith

theorem continuous_f {n p : ℕ} (D : Data n p) : Continuous (f D) := by
  unfold f
  have hres : Continuous (fun β : Fin p → ℝ =>
      (1 / 2 : ℝ) * ∑ r, (D.y r - ∑ j, D.X r j * β j) ^ 2) :=
    continuous_const.mul (continuous_finsetSum _ fun r _ =>
      (continuous_const.sub (continuous_finsetSum _ fun j _ =>
        continuous_const.mul (continuous_apply j))).pow 2)
  have hl1 : Continuous (fun β : Fin p → ℝ => D.lam1 * ∑ j, |β j|) :=
    continuous_const.mul (continuous_finsetSum _ fun j _ =>
      continuous_abs.comp (continuous_apply j))
  have hl2 : Continuous (fun β : Fin p → ℝ => D.lam2 * ∑ j, β j ^ 2) :=
    continuous_const.mul (continuous_finsetSum _ fun j _ =>
      (continuous_apply j).pow 2)
  exact (hres.add hl1).add hl2

end FastBestSubset.CDSS.Lemma1Proof

open FastBestSubset.CDSS.Lemma1Proof in
theorem solution {n p : ℕ} (D : Data n p) (_hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (_hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2) (β : Fin p → ℝ) :
    IsStationary D β ↔
      ∀ i ∈ supp β, HasDerivAt (fun t : ℝ => f D (Function.update β i t)) 0 (β i) := by
  have : NeBot (𝓝[>] (0 : ℝ)) := nhdsGT_zero_neBot
  constructor
  · intro hstat i hi
    have hderiv := hasDerivAt_coord D β hi
    suffices hzero : gradCoord D β i = 0 by rwa [hzero] at hderiv
    have hβi : β i ≠ 0 := (Finset.mem_filter.mp hi).2
    have habs : 0 < |β i| := abs_pos.mpr hβi
    have hdir : ∀ s : ℝ, |s| = 1 → 0 ≤ s * gradCoord D β i := by
      intro s hs
      let d : Fin p → ℝ := Pi.single i s
      let C₂ : ℝ := (1 / 2 : ℝ) * ∑ r, (∑ j, D.X r j * d j) ^ 2 + D.lam2 * ∑ j, d j ^ 2
      have hev : (fun α : ℝ => (((F D (β + α • d) - F D β) / α : ℝ) : EReal)) =ᶠ[𝓝[>] (0 : ℝ)]
          fun α : ℝ => ((s * gradCoord D β i + α * C₂ : ℝ) : EReal) := by
        filter_upwards [Ioo_mem_nhdsGT habs] with α ⟨hα0, hα_lt⟩
        have hl0_eq : l0 (β + α • d) = l0 β := by
          unfold l0
          congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul]
          by_cases hji : j = i
          · subst hji
            simp only [d, Pi.single_eq_same]
            have hne' : β j + α * s ≠ 0 := by
              intro heq
              have : |α * s| = |β j| := by
                have : α * s = -β j := by linarith
                rw [this, abs_neg]
              rw [abs_mul, hs, mul_one, abs_of_pos hα0] at this
              linarith
            exact ⟨fun _ => hβi, fun _ => hne'⟩
          · simp [d, hji]
        have hd_supp : ∀ j, j ∉ supp β → d j = 0 := by
          intro j hj
          have hji : j ≠ i := fun h => hj (h ▸ hi)
          simp [d, hji]
        have hsign : ∀ k ∈ supp β,
            (0 < β k → 0 < β k + α * d k) ∧ (β k < 0 → β k + α * d k < 0) := by
          intro k _
          by_cases hki : k = i
          · subst hki
            simp only [d, Pi.single_eq_same]
            have habs_as : |α * s| < |β k| := by
              rwa [abs_mul, hs, mul_one, abs_of_pos hα0]
            obtain ⟨hb1, hb2⟩ := abs_lt.mp habs_as
            exact ⟨fun h => by rw [abs_of_pos h] at hb1; linarith,
              fun h => by rw [abs_of_neg h] at hb2; linarith⟩
          · simp [d, hki]
        have htaylor := f_local_taylor D β d α hd_supp hsign
        have hsum_d : ∑ j, d j * gradCoord D β j = s * gradCoord D β i := by
          rw [Finset.sum_eq_single i]
          · simp [d]
          · intro j _ hji; simp [d, hji]
          · intro habs'; exact absurd (Finset.mem_univ i) habs'
        have hF_diff : F D (β + α • d) - F D β = f D (β + α • d) - f D β := by
          unfold F; rw [hl0_eq]; ring
        congr 1
        rw [hF_diff, htaylor, hsum_d]
        dsimp only [C₂]
        field_simp [hα0.ne']
      have htend_real : Tendsto (fun α : ℝ => s * gradCoord D β i + α * C₂)
          (𝓝[>] (0 : ℝ)) (𝓝 (s * gradCoord D β i)) := by
        have hc : Continuous (fun α : ℝ => s * gradCoord D β i + α * C₂) :=
          continuous_const.add (continuous_id.mul continuous_const)
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      have htend_ereal : Tendsto (fun α : ℝ => ((s * gradCoord D β i + α * C₂ : ℝ) : EReal))
          (𝓝[>] (0 : ℝ)) (𝓝 ((s * gradCoord D β i : ℝ) : EReal)) := by
        rw [tendsto_order]
        constructor
        · intro b hb
          cases b with
          | bot => exact Filter.Eventually.of_forall fun _ => EReal.bot_lt_coe _
          | top => exact absurd hb (not_lt.mpr le_top)
          | coe r =>
            exact ((tendsto_order.mp htend_real).1 r (EReal.coe_lt_coe_iff.mp hb)).mono
              fun _ h => EReal.coe_lt_coe_iff.mpr h
        · intro b hb
          cases b with
          | bot => exact absurd hb (not_lt.mpr bot_le)
          | top => exact Filter.Eventually.of_forall fun _ => EReal.coe_lt_top _
          | coe r =>
            exact ((tendsto_order.mp htend_real).2 r (EReal.coe_lt_coe_iff.mp hb)).mono
              fun _ h => EReal.coe_lt_coe_iff.mpr h
      have hlim_eq : lowerDirDeriv (F D) β d = ((s * gradCoord D β i : ℝ) : EReal) := by
        unfold lowerDirDeriv
        rw [Filter.liminf_congr hev]
        exact htend_ereal.liminf_eq
      have hge := hstat d
      rw [hlim_eq] at hge
      exact EReal.coe_nonneg.mp hge
    have hpos := hdir 1 (by norm_num)
    have hneg := hdir (-1) (by norm_num)
    linarith
  · intro hgrad d
    have hgrad0 : ∀ i ∈ supp β, gradCoord D β i = 0 :=
      fun i hi => (hasDerivAt_coord D β hi).unique (hgrad i hi)
    let M_d : ℝ := (∑ j, |d j|) + 1
    have hMd_pos : 0 < M_d := by
      have : 0 ≤ ∑ j, |d j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    have hdi_le : ∀ j : Fin p, |d j| < M_d := by
      intro j
      have : |d j| ≤ ∑ k, |d k| :=
        Finset.single_le_sum (f := fun k => |d k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      linarith
    let δ : ℝ := if hne : (supp β).Nonempty then (supp β).inf' hne (fun i => |β i|) else 1
    have hδ_pos : 0 < δ := by
      dsimp only [δ]
      split_ifs with hne
      · refine (Finset.lt_inf'_iff hne).mpr fun i hi => abs_pos.mpr (Finset.mem_filter.mp hi).2
      · exact zero_lt_one
    have hδ_le : ∀ i ∈ supp β, δ ≤ |β i| := by
      intro i hi
      dsimp only [δ]
      rw [dif_pos ⟨i, hi⟩]
      exact Finset.inf'_le _ hi
    have hsupp_keep : ∀ α : ℝ, 0 < α → α < δ / M_d →
        ∀ i ∈ supp β,
          (0 < β i → 0 < β i + α * d i) ∧ (β i < 0 → β i + α * d i < 0) ∧
          β i + α * d i ≠ 0 := by
      intro α hα0 hα_lt i hi
      have had_lt : |α * d i| < |β i| := by
        rw [abs_mul, abs_of_pos hα0]
        calc α * |d i| ≤ α * M_d := mul_le_mul_of_nonneg_left (hdi_le i).le hα0.le
          _ < (δ / M_d) * M_d := mul_lt_mul_of_pos_right hα_lt hMd_pos
          _ = δ := div_mul_cancel₀ δ hMd_pos.ne'
          _ ≤ |β i| := hδ_le i hi
      obtain ⟨hb1, hb2⟩ := abs_lt.mp had_lt
      refine ⟨fun h => by rw [abs_of_pos h] at hb1; linarith,
        fun h => by rw [abs_of_neg h] at hb2; linarith, ?_⟩
      intro heq
      have : |α * d i| = |β i| := by
        have : α * d i = -β i := by linarith
        rw [this, abs_neg]
      linarith
    by_cases hleave : ∃ j₀ ∉ supp β, d j₀ ≠ 0
    · obtain ⟨j₀, hj₀_not, hdj₀⟩ := hleave
      have hcont_path : Continuous (fun α : ℝ => f D (β + α • d) - f D β) :=
        ((continuous_f D).comp (continuous_const.add (continuous_id.smul continuous_const))).sub
          continuous_const
      have htend0 : Tendsto (fun α : ℝ => f D (β + α • d) - f D β) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa using hcont_path.tendsto 0
      have hev_f : ∀ᶠ α in 𝓝[>] (0 : ℝ), -(D.lam0 / 2) < f D (β + α • d) - f D β :=
        (htend0.eventually (Ioo_mem_nhds (by linarith : -(D.lam0 / 2) < 0)
          (by linarith : (0 : ℝ) < D.lam0 / 2))).filter_mono nhdsWithin_le_nhds |>.mono
          fun _ h => h.1
      apply liminf_ereal_nonneg
      filter_upwards [Ioo_mem_nhdsGT (div_pos hδ_pos hMd_pos), hev_f] with α ⟨hα0, hα_lt⟩ hf_gt
      have hsub_supp : insert j₀ (supp β) ⊆ supp (β + α • d) := by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk_supp
        · have hβj₀ : β k = 0 := by
            by_contra h; exact hj₀_not (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩)
          simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul, hβj₀, zero_add]
          exact mul_ne_zero hα0.ne' hdj₀
        · simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul]
          exact (hsupp_keep α hα0 hα_lt k hk_supp).2.2
      have hl0_ge : (l0 β : ℝ) + 1 ≤ (l0 (β + α • d) : ℝ) := by
        have hcard : (supp β).card + 1 ≤ (supp (β + α • d)).card := by
          rw [← Finset.card_insert_of_notMem hj₀_not]
          exact Finset.card_le_card hsub_supp
        exact_mod_cast hcard
      have hF_pos : 0 ≤ F D (β + α • d) - F D β := by
        unfold F
        have : D.lam0 * 1 ≤ D.lam0 * ((l0 (β + α • d) : ℝ) - (l0 β : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hlam0.le
        linarith
      exact div_nonneg hF_pos hα0.le
    · push Not at hleave
      apply liminf_ereal_nonneg
      filter_upwards [Ioo_mem_nhdsGT (div_pos hδ_pos hMd_pos)] with α ⟨hα0, hα_lt⟩
      have hl0_eq : l0 (β + α • d) = l0 β := by
        unfold l0
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        by_cases hk : k ∈ supp β
        · exact ⟨fun _ => (Finset.mem_filter.mp hk).2,
            fun _ => (hsupp_keep α hα0 hα_lt k hk).2.2⟩
        · have hβk : β k = 0 := by
            by_contra h; exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩)
          have hdk : d k = 0 := hleave k hk
          simp [hβk, hdk]
      have hsign : ∀ i ∈ supp β,
          (0 < β i → 0 < β i + α * d i) ∧ (β i < 0 → β i + α * d i < 0) :=
        fun i hi => ⟨(hsupp_keep α hα0 hα_lt i hi).1, (hsupp_keep α hα0 hα_lt i hi).2.1⟩
      have htaylor := f_local_taylor D β d α hleave hsign
      have hlin0 : ∑ i, d i * gradCoord D β i = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        by_cases hi : i ∈ supp β
        · rw [hgrad0 i hi, mul_zero]
        · rw [hleave i hi, zero_mul]
      have hF_eq : F D (β + α • d) - F D β = f D (β + α • d) - f D β := by
        unfold F; rw [hl0_eq]; ring
      rw [hF_eq, htaylor, hlin0, mul_zero, zero_add]
      have hquad_nn : 0 ≤ (1 / 2 : ℝ) * ∑ r, (∑ j, D.X r j * d j) ^ 2 + D.lam2 * ∑ j, d j ^ 2 :=
        add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
          (mul_nonneg hlam2 (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      exact div_nonneg (mul_nonneg (sq_nonneg α) hquad_nn) hα0.le
