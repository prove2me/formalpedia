-- Prove2me | solution 1 for DirectedSearch.Approx.proposition_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:03:28.956999+00:00
-- url     : https://prove2.me/submissions/4cd2468a-abc9-4d49-8521-6e754845137d

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting
import Theorems.Thm_DirectedSearch_Approx_lemma_4_5

namespace DSA44

open DirectedSearch.Approx MeasureTheory

lemma tailMass_nonneg (μ : Measure ℝ) (a : ℝ) : 0 ≤ tailMass μ a := ENNReal.toReal_nonneg

/-- `A(τ) ≤ ρ` for every real `τ`, from the unimodality in Lemma 4.5. -/
lemma ratio_le_rho (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hint : Integrable id μ) (δ : ℝ) (hδ : 0 < δ) (τ : ℝ) :
    ratio μ δ τ ≤ sSup (ratio μ δ '' Set.Ici 0) := by
  have h := lemma_4_5 μ hint δ hδ
  simp only at h
  obtain ⟨_, hfix, hmono, hanti⟩ := h
  set ρ := sSup (ratio μ δ '' Set.Ici 0)
  rcases le_total τ ρ with hτ | hτ
  · calc ratio μ δ τ ≤ ratio μ δ ρ := hmono (Set.mem_Iic.mpr hτ) (Set.mem_Iic.mpr le_rfl) hτ
      _ = ρ := hfix
  · calc ratio μ δ τ ≤ ratio μ δ ρ := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hτ) hτ
      _ = ρ := hfix

lemma tailInt_le {M W : Type} (mk : Market M W) (hmk : mk.Standing) (m : M) (w : W) (τ : ℝ) :
    tailInt (mk.F m w) τ ≤ rho mk m w * (mk.δ + tailMass (mk.F m w) τ) := by
  have := hmk.prob m w; have := hmk.noAtoms m w
  have h := ratio_le_rho (mk.F m w) (hmk.integrable m w) mk.δ hmk.delta_pos τ
  have hpos : 0 < mk.δ + tailMass (mk.F m w) τ := by
    have := tailMass_nonneg (mk.F m w) τ; linarith [hmk.delta_pos]
  unfold ratio at h
  rw [div_le_iff₀ hpos] at h
  exact h

lemma exists_root {M W : Type} (mk : Market M W) (hmk : mk.Standing) (m : M) (w : W) :
    ∃ τ, 0 ≤ τ ∧ tailInt (mk.F m w) τ = rho mk m w * (mk.δ + tailMass (mk.F m w) τ) := by
  have := hmk.prob m w; have := hmk.noAtoms m w
  have h := lemma_4_5 (mk.F m w) (hmk.integrable m w) mk.δ hmk.delta_pos
  simp only at h
  obtain ⟨⟨τ, hτ0, hτ⟩, -⟩ := h
  refine ⟨τ, hτ0, ?_⟩
  have hpos : 0 < mk.δ + tailMass (mk.F m w) τ := by
    have := tailMass_nonneg (mk.F m w) τ; linarith [hmk.delta_pos]
  have e : sSup (ratio (mk.F m w) mk.δ '' Set.Ici 0) =
      tailInt (mk.F m w) τ / (mk.δ + tailMass (mk.F m w) τ) := hτ.symm
  change _ = sSup (ratio (mk.F m w) mk.δ '' Set.Ici 0) * _
  rw [e]; field_simp

variable {M W : Type} [Fintype M] [Fintype W]

/-- Part 2: every LP-feasible `β` is realised by a first-best feasible profile. -/
theorem part2 (mk : Market M W) (hmk : mk.Standing) (β : M → W → ℝ) (hβ : LPFeasible mk β) :
    ∃ Q : FBProfile M W, FirstBestFeasible mk Q ∧ fbWelfare mk Q = lpObj mk β := by
  choose τ hτ0 hτ using exists_root mk hmk
  have hδ := hmk.delta_pos
  set t : M → W → ℝ := fun m w => tailMass (mk.F m w) (τ m w) with ht
  have ht0 : ∀ m w, 0 ≤ t m w := fun m w => tailMass_nonneg _ _
  have hdt : ∀ m w, 0 < mk.δ + t m w := fun m w => by linarith [ht0 m w]
  set x : M → W → ℝ := fun m w => β m w / (mk.δ + t m w) with hx
  have hx0 : ∀ m w, 0 ≤ x m w := fun m w => div_nonneg (hβ.1 m w) (hdt m w).le
  have hxβ : ∀ m w, x m w * (mk.δ + t m w) = β m w := fun m w => by
    have := (hdt m w).ne'
    simp only [hx]; field_simp
  set eM : M → ℝ := fun m => (mk.αM m - ∑ w, x m w * t m w) / mk.δ with heM
  set eW : W → ℝ := fun w => (mk.αW w - ∑ m, x m w * t m w) / mk.δ with heW
  -- key identity: α_m - Σ x t = (α_m - Σ β) + δ Σ x
  have keyM : ∀ m, mk.αM m - ∑ w, x m w * t m w = (mk.αM m - ∑ w, β m w) + mk.δ * ∑ w, x m w := by
    intro m
    have : ∑ w, β m w = ∑ w, (x m w * t m w + mk.δ * x m w) :=
      Finset.sum_congr rfl (fun w _ => by rw [← hxβ m w]; ring)
    rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  have keyW : ∀ w, mk.αW w - ∑ m, x m w * t m w = (mk.αW w - ∑ m, β m w) + mk.δ * ∑ m, x m w := by
    intro w
    have : ∑ m, β m w = ∑ m, (x m w * t m w + mk.δ * x m w) :=
      Finset.sum_congr rfl (fun m _ => by rw [← hxβ m w]; ring)
    rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  have heMpos : ∀ m, 0 < eM m := by
    intro m
    apply div_pos _ hδ
    rw [keyM]
    have h1 : 0 ≤ mk.αM m - ∑ w, β m w := by linarith [hβ.2.1 m]
    have h2 : 0 ≤ ∑ w, x m w := Finset.sum_nonneg (fun w _ => hx0 m w)
    rcases h2.lt_or_eq with h2 | h2
    · nlinarith
    · have hx00 : ∀ w, x m w = 0 := by
        intro w
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => hx0 m w)).mp h2.symm w
          (Finset.mem_univ _)
        exact this
      have hb0 : ∑ w, β m w = 0 :=
        Finset.sum_eq_zero (fun w _ => by rw [← hxβ m w, hx00 w, zero_mul])
      rw [hb0, ← h2]; simp [hmk.alphaM_pos m]
  have heWpos : ∀ w, 0 < eW w := by
    intro w
    apply div_pos _ hδ
    rw [keyW]
    have h1 : 0 ≤ mk.αW w - ∑ m, β m w := by linarith [hβ.2.2 w]
    have h2 : 0 ≤ ∑ m, x m w := Finset.sum_nonneg (fun m _ => hx0 m w)
    rcases h2.lt_or_eq with h2 | h2
    · nlinarith
    · have hx00 : ∀ m, x m w = 0 := by
        intro m
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => hx0 m w)).mp h2.symm m
          (Finset.mem_univ _)
      have hb0 : ∑ m, β m w = 0 :=
        Finset.sum_eq_zero (fun m _ => by rw [← hxβ m w, hx00 m, zero_mul])
      rw [hb0, ← h2]; simp [hmk.alphaW_pos w]
  let Q : FBProfile M W :=
    { lamM := fun m w => x m w / eM m
      lamW := fun w m => x m w / eW w
      tauMW := τ
      xiM := fun m => ∑ w, x m w / eM m * t m w
      xiW := fun w => ∑ m, x m w / eW w * t m w
      etaM := eM
      etaW := eW }
  refine ⟨Q, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro m
    show mk.αM m = (mk.δ + ∑ w, x m w / eM m * t m w) * eM m
    have hne := (heMpos m).ne'
    rw [add_mul, Finset.sum_mul]
    have : ∑ w, x m w / eM m * t m w * eM m = ∑ w, x m w * t m w :=
      Finset.sum_congr rfl (fun w _ => by field_simp)
    rw [this]; simp only [heM]; field_simp; ring
  · intro w
    show mk.αW w = (mk.δ + ∑ m, x m w / eW w * t m w) * eW w
    have hne := (heWpos w).ne'
    rw [add_mul, Finset.sum_mul]
    have : ∑ m, x m w / eW w * t m w * eW w = ∑ m, x m w * t m w :=
      Finset.sum_congr rfl (fun m _ => by field_simp)
    rw [this]; simp only [heW]; field_simp; ring
  · intro m w
    show eM m * (x m w / eM m) = eW w * (x m w / eW w)
    have h1 := (heMpos m).ne'; have h2 := (heWpos w).ne'
    field_simp
  · intro m
    show ∑ w, x m w / eM m ≤ 1
    rw [← Finset.sum_div, div_le_one (heMpos m)]
    simp only [heM]
    rw [keyM, le_div_iff₀ hδ]
    nlinarith [hβ.2.1 m]
  · intro w
    show ∑ m, x m w / eW w ≤ 1
    rw [← Finset.sum_div, div_le_one (heWpos w)]
    simp only [heW]
    rw [keyW, le_div_iff₀ hδ]
    nlinarith [hβ.2.2 w]
  · intro m; rfl
  · intro w; rfl
  · intro m w; exact div_nonneg (hx0 m w) (heMpos m).le
  · intro w m; exact div_nonneg (hx0 m w) (heWpos w).le
  · show (∑ m, ∑ w, eM m * (x m w / eM m) * tailInt (mk.F m w) (τ m w)) +
        ∑ w, ∑ m, eW w * (x m w / eW w) * tailInt (mk.F m w) (τ m w) =
        2 * ∑ m, ∑ w, rho mk m w * β m w
    have e1 : ∀ m w, eM m * (x m w / eM m) * tailInt (mk.F m w) (τ m w) =
        rho mk m w * β m w := by
      intro m w
      have := (heMpos m).ne'
      rw [hτ m w, ← hxβ m w]; field_simp; rfl
    have e2 : ∀ m w, eW w * (x m w / eW w) * tailInt (mk.F m w) (τ m w) =
        rho mk m w * β m w := by
      intro m w
      have := (heWpos w).ne'
      rw [hτ m w, ← hxβ m w]; field_simp; rfl
    simp only [e1, e2]
    rw [Finset.sum_comm (f := fun w m => rho mk m w * β m w)]
    ring

/-- Every first-best feasible profile is dominated by an LP-feasible `β`. -/
theorem fb_le (mk : Market M W) (hmk : mk.Standing) (Q : FBProfile M W)
    (hQ : FirstBestFeasible mk Q) :
    ∃ β, LPFeasible mk β ∧ fbWelfare mk Q ≤ lpObj mk β := by
  obtain ⟨h6aM, h6aW, h6b, h6cM, h6cW, h6dM, h6dW, h6fM, h6fW⟩ := hQ
  have hδ := hmk.delta_pos
  have hxiM : ∀ m, 0 ≤ Q.xiM m := fun m => by
    rw [h6dM m]; exact Finset.sum_nonneg (fun w _ => mul_nonneg (h6fM m w) (tailMass_nonneg _ _))
  have hxiW : ∀ w, 0 ≤ Q.xiW w := fun w => by
    rw [h6dW w]; exact Finset.sum_nonneg (fun m _ => mul_nonneg (h6fW w m) (tailMass_nonneg _ _))
  have hetaM : ∀ m, 0 ≤ Q.etaM m := fun m => by
    have h := h6aM m
    have hp := hmk.alphaM_pos m
    by_contra hneg; push Not at hneg
    have : (mk.δ + Q.xiM m) * Q.etaM m < 0 :=
      mul_neg_of_pos_of_neg (by linarith [hxiM m]) hneg
    linarith
  have hetaW : ∀ w, 0 ≤ Q.etaW w := fun w => by
    have h := h6aW w
    have hp := hmk.alphaW_pos w
    by_contra hneg; push Not at hneg
    have : (mk.δ + Q.xiW w) * Q.etaW w < 0 :=
      mul_neg_of_pos_of_neg (by linarith [hxiW w]) hneg
    linarith
  set β : M → W → ℝ := fun m w => Q.etaM m * Q.lamM m w * (mk.δ + tailMass (mk.F m w) (Q.tauMW m w))
    with hβ
  refine ⟨β, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro m w
    exact mul_nonneg (mul_nonneg (hetaM m) (h6fM m w))
      (by linarith [tailMass_nonneg (mk.F m w) (Q.tauMW m w)])
  · intro m
    have e : ∑ w, β m w = Q.etaM m * (mk.δ * ∑ w, Q.lamM m w + Q.xiM m) := by
      rw [h6dM m, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w _ => ?_); simp only [hβ]; ring
    rw [e, h6aM m]
    have h1 := h6cM m
    have h2 := hetaM m
    nlinarith [mul_nonneg (mul_nonneg h2 hδ.le) (sub_nonneg.mpr h1)]
  · intro w
    have e : ∑ m, β m w = Q.etaW w * (mk.δ * ∑ m, Q.lamW w m + Q.xiW w) := by
      rw [h6dW w, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_); simp only [hβ]
      rw [h6b m w]; ring
    rw [e, h6aW w]
    have h1 := h6cW w
    have h2 := hetaW w
    nlinarith [mul_nonneg (mul_nonneg h2 hδ.le) (sub_nonneg.mpr h1)]
  · unfold fbWelfare lpObj
    have e2 : ∑ w, ∑ m, Q.etaW w * Q.lamW w m * tailInt (mk.F m w) (Q.tauMW m w) =
        ∑ m, ∑ w, Q.etaM m * Q.lamM m w * tailInt (mk.F m w) (Q.tauMW m w) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun w _ => ?_))
      rw [h6b m w]
    rw [e2, ← two_mul]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun w _ => ?_)
      (by norm_num)
    show _ ≤ rho mk m w * (Q.etaM m * Q.lamM m w * (mk.δ + tailMass (mk.F m w) (Q.tauMW m w)))
    have := tailInt_le mk hmk m w (Q.tauMW m w)
    have h0 : 0 ≤ Q.etaM m * Q.lamM m w := mul_nonneg (hetaM m) (h6fM m w)
    nlinarith

/-- The LP (7) attains its maximum. -/
theorem lp_max (mk : Market M W) (hmk : mk.Standing) :
    ∃ β, LPFeasible mk β ∧ ∀ β', LPFeasible mk β' → lpObj mk β' ≤ lpObj mk β := by
  set S : Set (M → W → ℝ) := {β | LPFeasible mk β} with hS
  have hcl : IsClosed S := by
    have : S = (⋂ m, ⋂ w, {β : M → W → ℝ | 0 ≤ β m w}) ∩
        ((⋂ m, {β : M → W → ℝ | ∑ w, β m w ≤ mk.αM m}) ∩
          (⋂ w, {β : M → W → ℝ | ∑ m, β m w ≤ mk.αW w})) := by
      ext β; simp [hS, LPFeasible]
    rw [this]
    refine (isClosed_iInter fun m => isClosed_iInter fun w => ?_).inter
      ((isClosed_iInter fun m => ?_).inter (isClosed_iInter fun w => ?_))
    · exact isClosed_le continuous_const ((continuous_apply w).comp (continuous_apply m))
    · exact isClosed_le (continuous_finset_sum _ fun w _ =>
        (continuous_apply w).comp (continuous_apply m)) continuous_const
    · exact isClosed_le (continuous_finset_sum _ fun m _ =>
        (continuous_apply w).comp (continuous_apply m)) continuous_const
  have hsub : S ⊆ Set.pi Set.univ (fun m => Set.pi Set.univ (fun _ : W => Set.Icc 0 (mk.αM m))) := by
    intro β hβ m _ w _
    refine ⟨hβ.1 m w, ?_⟩
    calc β m w ≤ ∑ w', β m w' :=
          Finset.single_le_sum (fun w' _ => hβ.1 m w') (Finset.mem_univ w)
      _ ≤ mk.αM m := hβ.2.1 m
  have hcpt : IsCompact S :=
    (isCompact_univ_pi fun m => isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset
      hcl hsub
  have hne : S.Nonempty := ⟨0, fun m w => le_rfl, fun m => by simp [(hmk.alphaM_pos m).le],
    fun w => by simp [(hmk.alphaW_pos w).le]⟩
  have hcont : Continuous (lpObj mk) := by
    unfold lpObj
    exact continuous_const.mul (continuous_finset_sum _ fun m _ => continuous_finset_sum _
      fun w _ => continuous_const.mul ((continuous_apply w).comp (continuous_apply m)))
  obtain ⟨β, hβ, hmax⟩ := hcpt.exists_isMaxOn hne hcont.continuousOn
  exact ⟨β, hβ, fun β' hβ' => hmax hβ'⟩

end DSA44

open DirectedSearch.Approx DSA44 in
theorem solution {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) :
    (∃ v : ℝ, IsGreatest (fbWelfare mk '' {Q | FirstBestFeasible mk Q}) v ∧
      IsGreatest (lpObj mk '' {β | LPFeasible mk β}) v) ∧
    (∀ β : M → W → ℝ, LPFeasible mk β →
      ∃ Q : FBProfile M W, FirstBestFeasible mk Q ∧ fbWelfare mk Q = lpObj mk β) := by
  obtain ⟨β, hβ, hmax⟩ := lp_max mk hmk
  refine ⟨⟨lpObj mk β, ⟨?_, ?_⟩, ⟨⟨β, hβ, rfl⟩, ?_⟩⟩, part2 mk hmk⟩
  · obtain ⟨Q, hQ, hQv⟩ := part2 mk hmk β hβ
    exact ⟨Q, hQ, hQv⟩
  · rintro _ ⟨Q, hQ, rfl⟩
    obtain ⟨β', hβ', hle⟩ := fb_le mk hmk Q hQ
    exact hle.trans (hmax β' hβ')
  · rintro _ ⟨β', hβ', rfl⟩
    exact hmax β' hβ'
