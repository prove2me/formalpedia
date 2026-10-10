-- Prove2me | solution 1 for ConvexOptAlg.CenterGravity.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T20:01:04.738034+00:00
-- url     : https://prove2.me/submissions/de057281-b65e-4798-bdd4-33d3fbea567a

import Mathlib
import Definitions.Def_ConvexOptAlg_CenterGravity_Defs
import Theorems.Thm_ConvexOptAlg_CenterGravity_thm_2_1_volume_decay

open MeasureTheory
open scoped InnerProductSpace

namespace CGAux

open ConvexOptAlg.CenterGravity

theorem inner_cut_neg {n : ℕ} (c x w : EuclideanSpace ℝ (Fin n)) :
    ⟪w, c - x⟫_ℝ = -⟪x - c, w⟫_ℝ := by
  rw [real_inner_comm, ← inner_neg_left]; congr 1; abel

theorem S_subset {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {c w : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsCenterOfGravityRun X f S c w) :
    ∀ s, 1 ≤ s → S s ⊆ X := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => rw [hrun.init]
  | succ s hs ih => rw [hrun.cut s hs]; exact Set.inter_subset_left.trans ih

theorem removed_pos {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {c w : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsCenterOfGravityRun X f S c w)
    (s : ℕ) (hs : 1 ≤ s) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S s) (hx' : x ∉ S (s + 1)) :
    0 < ⟪x - c s, w s⟫_ℝ := by
  rw [hrun.cut s hs] at hx'
  by_contra h
  exact hx' ⟨hx, not_lt.mp h⟩

theorem removed_gt {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {c w : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsCenterOfGravityRun X f S c w)
    (s : ℕ) (hs : 1 ≤ s) {x : EuclideanSpace ℝ (Fin n)} (hxX : x ∈ X)
    (hpos : 0 < ⟪x - c s, w s⟫_ℝ) : f (c s) < f x := by
  have h := (hrun.oracle s hs).2 x hxX
  rw [inner_cut_neg] at h
  linarith

theorem xstar_mem {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {S : ℕ → Set (EuclideanSpace ℝ (Fin n))}
    {c w : ℕ → EuclideanSpace ℝ (Fin n)} (hrun : IsCenterOfGravityRun X f S c w)
    {xstar : EuclideanSpace ℝ (Fin n)} (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y) :
    ∀ t, 1 ≤ t → xstar ∈ S t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rw [hrun.init]; exact hxstar
  | succ t ht ih =>
    rw [hrun.cut t ht]
    refine ⟨ih, ?_⟩
    have h1 := (hrun.oracle t ht).2 xstar hxstar
    have h2 := hmin _ (hrun.oracle t ht).1
    rw [inner_cut_neg] at h1
    show ⟪xstar - c t, w t⟫_ℝ ≤ 0
    linarith

end CGAux
namespace CGAux

open ConvexOptAlg.CenterGravity

theorem body_vol {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K) :
    0 < volume K ∧ volume K < ⊤ :=
  ⟨lt_of_lt_of_le (isOpen_interior.measure_pos volume hK.2.2) (measure_mono interior_subset),
    hK.1.measure_lt_top⟩

theorem integral_self_eq {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K) :
    ∫ x in K, x = (volume K).toReal • centroid K := by
  have h := body_vol hK
  have hne : (volume K).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨h.1.ne', h.2.ne⟩
  unfold centroid
  rw [smul_inv_smul₀ hne]

theorem integral_centered {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K) :
    ∫ x in (fun y => y + centroid K) ⁻¹' K, x = 0 := by
  set c := centroid K with hc
  have hmeas : MeasurableSet K := hK.1.isClosed.measurableSet
  have hP : MeasurableSet ((fun y => y + c) ⁻¹' K) := hmeas.preimage (measurable_add_const c)
  have hint : IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) => y) K volume :=
    continuousOn_id.integrableOn_compact hK.1
  have hintc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => c) K volume :=
    continuousOn_const.integrableOn_compact hK.1
  have e1 : ∫ x in (fun y => y + c) ⁻¹' K, x =
      ∫ x, K.indicator (fun y => y - c) (x + c) := by
    rw [← integral_indicator hP]
    congr 1
    funext x
    by_cases hx : x + c ∈ K
    · have : x ∈ (fun y => y + c) ⁻¹' K := hx
      simp [Set.indicator, this, hx]
    · have : x ∉ (fun y => y + c) ⁻¹' K := hx
      simp [Set.indicator, this, hx]
  rw [e1, integral_add_right_eq_self (fun y => K.indicator (fun y => y - c) y) c,
    integral_indicator hmeas, integral_sub hint hintc, setIntegral_const, integral_self_eq hK]
  simp [Measure.real, ← hc]

end CGAux
namespace CGAux

open ConvexOptAlg.CenterGravity

theorem vol_scaled {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {xstar : EuclideanSpace ℝ (Fin n)} (ε : ℝ) (hε0 : 0 ≤ ε) :
    volume ((fun x => (1 - ε) • xstar + ε • x) '' X) = ENNReal.ofReal ε ^ n * volume X := by
  have h : (fun x : EuclideanSpace ℝ (Fin n) => (1 - ε) • xstar + ε • x) =
      AffineMap.homothety xstar ε := by
    funext x
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [h, Measure.addHaar_image_homothety, finrank_euclideanSpace_fin,
    abs_of_nonneg (pow_nonneg hε0 n), ENNReal.ofReal_pow hε0]

theorem value_scaled {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ} (hfB : ∀ x ∈ X, |f x| ≤ B)
    (hfconv : ConvexOn ℝ X f)
    {xstar : EuclideanSpace ℝ (Fin n)} (hxstar : xstar ∈ X)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) :
    f ((1 - ε) • xstar + ε • x) ≤ f xstar + 2 * ε * B := by
  have h1 := hfconv.2 hxstar hx (by linarith : 0 ≤ 1 - ε) hε0 (by ring)
  simp only [smul_eq_mul] at h1
  have h2 := (abs_le.mp (hfB x hx)).2
  have h3 := (abs_le.mp (hfB xstar hxstar)).1
  nlinarith

end CGAux

theorem solution {n : ℕ} (hn : 1 ≤ n) {X : Set (EuclideanSpace ℝ (Fin n))} (hX : ConvexOptAlg.CenterGravity.IsConvexBody X)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ} (hfB : ∀ x ∈ X, |f x| ≤ B)
    (hfc : ContinuousOn f X) (hfconv : ConvexOn ℝ X f)
    {xstar : EuclideanSpace ℝ (Fin n)} (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    {S : ℕ → Set (EuclideanSpace ℝ (Fin n))} {c w : ℕ → EuclideanSpace ℝ (Fin n)}
    (hrun : ConvexOptAlg.CenterGravity.IsCenterOfGravityRun X f S c w) (t : ℕ) (ht : 1 ≤ t) :
    (Finset.Icc 1 t).inf' (Finset.nonempty_Icc.mpr ht) (fun r => f (c r)) - f xstar
      ≤ 2 * B * (1 - Real.exp (-1)) ^ ((t : ℝ) / n) := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hfB xstar hxstar)
  have hlt : Real.exp (-1) < 1 := by
    simpa using Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
  have ha0 : 0 < 1 - Real.exp (-1) := by linarith
  have ha1 : 1 - Real.exp (-1) < 1 := by have := Real.exp_pos (-1); linarith
  set a := 1 - Real.exp (-1) with ha
  set ε₀ := a ^ ((t : ℝ) / n) with hε₀
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hε0pos : 0 < ε₀ := Real.rpow_pos_of_pos ha0 _
  have hε0lt1 : ε₀ < 1 :=
    Real.rpow_lt_one ha0.le ha1 (div_pos (by exact_mod_cast ht) (by exact_mod_cast hn))
  have hε0n : ε₀ ^ n = a ^ t := by
    rw [hε₀, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le, div_mul_cancel₀ _ hn',
      Real.rpow_natCast]
  set m := (Finset.Icc 1 t).inf' (Finset.nonempty_Icc.mpr ht) (fun r => f (c r)) with hm
  have hmle : ∀ s, 1 ≤ s → s ≤ t → m ≤ f (c s) := fun s h1 h2 =>
    Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  by_cases hz : ∃ s, 1 ≤ s ∧ s ≤ t ∧ w s = 0
  · obtain ⟨s, hs1, hst, hws⟩ := hz
    have hcs : f (c s) ≤ f xstar := by
      have := (hrun.oracle s hs1).2 xstar hxstar
      simpa [hws] using this
    have h1 := hmle s hs1 hst
    have h2 : 0 ≤ 2 * B * ε₀ := by positivity
    linarith
  · push_neg at hz
    have hvol := ConvexOptAlg.CenterGravity.thm_2_1_volume_decay hX hfB hfc hfconv hrun t hz
    have hV := CGAux.body_vol hX
    have hclaim : ∀ ε, ε₀ < ε → ε ≤ 1 → m ≤ f xstar + 2 * ε * B := by
      intro ε hε hε1
      have hεpos : 0 < ε := hε0pos.trans hε
      have hlt1 : volume (S (t + 1)) <
          volume ((fun x => (1 - ε) • xstar + ε • x) '' X) := by
        rw [CGAux.vol_scaled ε hεpos.le]
        calc volume (S (t + 1)) ≤ ENNReal.ofReal (a ^ t) * volume X := hvol
          _ = ENNReal.ofReal (ε₀ ^ n) * volume X := by rw [hε0n]
          _ < ENNReal.ofReal (ε ^ n) * volume X := by
            rw [ENNReal.mul_lt_mul_iff_left hV.1.ne' hV.2.ne,
              ENNReal.ofReal_lt_ofReal_iff (pow_pos hεpos n)]
            exact pow_lt_pow_left₀ hε hε0pos.le (by omega)
          _ = ENNReal.ofReal ε ^ n * volume X := by rw [ENNReal.ofReal_pow hεpos.le]
      have hnot : ¬ ((fun x => (1 - ε) • xstar + ε • x) '' X ⊆ S (t + 1)) :=
        fun h => absurd (measure_mono (μ := volume) h) (not_le.mpr hlt1)
      rw [Set.not_subset] at hnot
      obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := hnot
      have hyX : (1 - ε) • xstar + ε • x ∈ X :=
        hX.2.1 hxstar hx (by linarith) hεpos.le (by ring)
      by_contra hcon
      push_neg at hcon
      have hs : ∃ s, 1 ≤ s ∧ s ≤ t ∧ (1 - ε) • xstar + ε • x ∈ S s ∧
          (1 - ε) • xstar + ε • x ∉ S (s + 1) := by
        by_contra hno
        push_neg at hno
        have : ∀ k, k ≤ t → (1 - ε) • xstar + ε • x ∈ S (k + 1) := by
          intro k
          induction k with
          | zero => intro _; rw [hrun.init]; exact hyX
          | succ k ih => intro hk; exact hno (k + 1) (by omega) hk (ih (by omega))
        exact hy (this t le_rfl)
      obtain ⟨s, hs1, hst, hys, hys'⟩ := hs
      have h1 := CGAux.removed_gt hrun s hs1 hyX (CGAux.removed_pos hrun s hs1 hys hys')
      have h2 := CGAux.value_scaled hfB hfconv hxstar ε hεpos.le hε1 x hx
      have h3 := hmle s hs1 hst
      linarith
    have hfin : m - f xstar ≤ 2 * B * ε₀ := by
      apply le_of_forall_pos_le_add
      intro δ hδ
      have hB1 : 0 < 2 * B + 1 := by linarith
      set ε := min (ε₀ + δ / (2 * B + 1)) 1 with hε
      have hδp : 0 < δ / (2 * B + 1) := by positivity
      have hεgt : ε₀ < ε := lt_min (by linarith) hε0lt1
      have hεle : ε ≤ ε₀ + δ / (2 * B + 1) := min_le_left _ _
      have h1 := hclaim ε hεgt (min_le_right _ _)
      have h2 : 2 * B * (δ / (2 * B + 1)) ≤ δ := by
        rw [← mul_div_assoc, div_le_iff₀ hB1]; nlinarith
      nlinarith
    exact hfin
