-- Prove2me | solution 1 for BHTOpinion.Continuum.prop3a_limit_in_Fbar
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:58:51.203007+00:00
-- url     : https://prove2.me/submissions/2418f6c8-d4ae-4735-987e-52e0f58c1d8e

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHT6P3a

open BHTOpinion.Continuum

/-- The interaction kernel `φ(u, v) = 1{|u - v| < 1} (v - u)`. -/
noncomputable def φ (u v : ℝ) : ℝ := if |u - v| < 1 then v - u else 0

lemma φ_meas : Measurable (fun p : ℝ × ℝ => φ p.1 p.2) := by
  unfold φ
  refine Measurable.ite ?_ (measurable_snd.sub measurable_fst) measurable_const
  exact measurableSet_lt (measurable_fst.sub measurable_snd).abs measurable_const

lemma φ_abs (u v : ℝ) : |φ u v| ≤ 1 := by
  unfold φ; split_ifs with h
  · rw [abs_sub_comm]; exact h.le
  · simp

lemma φ_anti (u v : ℝ) : φ v u = - φ u v := by
  unfold φ
  rw [abs_sub_comm]
  split_ifs <;> ring

lemma φ_nonneg (u v : ℝ) (h : u ≤ v) : 0 ≤ φ u v := by
  unfold φ; split_ifs <;> linarith

instance finI : IsFiniteMeasure (volume.restrict I) := by
  rw [isFiniteMeasure_restrict]; exact measure_Icc_lt_top.ne

lemma inner_abs (u : ℝ → ℝ) (α : ℝ) : |∫ γ in I, φ (u α) (u γ)| ≤ 1 := by
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := I) measure_Icc_lt_top
    (f := fun γ => φ (u α) (u γ)) (fun γ _ => by rw [Real.norm_eq_abs]; exact φ_abs _ _)
  simpa [Real.volume_real_Icc] using this

/-- (3.9): for `u` measurable and nondecreasing on `I`, the interaction of `[0,c]` with itself
cancels, leaving only the pull of `(c,1]`. -/
lemma cross_eq (u : ℝ → ℝ) (hu : Measurable u) (c : ℝ) (hc : c ∈ I) :
    ∫ α in Set.Ioc 0 c, ∫ γ in I, φ (u α) (u γ) =
      ∫ α in Set.Ioc 0 c, ∫ γ in Set.Ioc c 1, φ (u α) (u γ) := by
  have hmeas2 : Measurable (fun p : ℝ × ℝ => φ (u p.1) (u p.2)) :=
    φ_meas.comp ((hu.comp measurable_fst).prodMk (hu.comp measurable_snd))
  have hint_on : ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (α : ℝ),
      Integrable (fun γ => φ (u α) (u γ)) μ := by
    intro μ _ α
    refine Integrable.of_bound (C := 1)
      (hmeas2.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
    exact Eventually.of_forall (fun γ => by rw [Real.norm_eq_abs]; exact φ_abs _ _)
  have fin1 : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) c)) := by
    rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
  have fin2 : IsFiniteMeasure (volume.restrict (Set.Ioc c (1 : ℝ))) := by
    rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
  -- split the inner integral
  have hsplit : ∀ α, ∫ γ in I, φ (u α) (u γ) =
      (∫ γ in Set.Ioc 0 c, φ (u α) (u γ)) + ∫ γ in Set.Ioc c 1, φ (u α) (u γ) := by
    intro α
    rw [setIntegral_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1)).symm,
      ← Set.Ioc_union_Ioc_eq_Ioc hc.1 hc.2]
    exact setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hint_on _ α) (hint_on _ α)
  have hmeasA : ∀ (ν : Measure ℝ) [SFinite ν],
      Measurable (fun α => ∫ γ, φ (u α) (u γ) ∂ν) := by
    intro ν _
    exact (hmeas2.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hboundA : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν] (μ : Measure ℝ) [IsFiniteMeasure μ],
      Integrable (fun α => ∫ γ, φ (u α) (u γ) ∂ν) μ := by
    intro ν _ μ _
    refine Integrable.of_bound (C := ν.real Set.univ) (hmeasA ν).aestronglyMeasurable ?_
    refine Eventually.of_forall (fun α => ?_)
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun γ => φ (u α) (u γ)) (C := 1)
      (Eventually.of_forall (fun γ => by rw [Real.norm_eq_abs]; exact φ_abs _ _))
    simpa [mul_comm] using this
  rw [integral_congr_ae (Eventually.of_forall hsplit)]
  rw [integral_add (hboundA _ _) (hboundA _ _)]
  -- the symmetric part vanishes
  have hzero : ∫ α in Set.Ioc 0 c, ∫ γ in Set.Ioc 0 c, φ (u α) (u γ) = 0 := by
    have hswap := integral_integral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) c))
      (ν := volume.restrict (Set.Ioc (0 : ℝ) c)) (f := fun α γ => φ (u α) (u γ)) (by
        refine Integrable.of_bound (C := 1) hmeas2.aestronglyMeasurable ?_
        exact Eventually.of_forall (fun p => by rw [Real.norm_eq_abs]; exact φ_abs _ _))
    have hneg : ∫ γ in Set.Ioc 0 c, ∫ α in Set.Ioc 0 c, φ (u α) (u γ) =
        - ∫ α in Set.Ioc 0 c, ∫ γ in Set.Ioc 0 c, φ (u α) (u γ) := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall (fun γ => ?_))
      simp only
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall (fun α => ?_))
      exact φ_anti _ _
    linarith
  rw [hzero, zero_add]

/-- Uniform bounds: opinions stay in `[x0 0, x0 1]`. -/
lemma bounds (x0 : ℝ → ℝ) (x : ℝ → ℝ → ℝ)
    (hx : IsSolution x0 x) (hmono : ∀ t : ℝ, 0 ≤ t → InX (x t)) :
    ∀ t : ℝ, 0 ≤ t → ∀ α ∈ I, x0 0 ≤ x t α ∧ x t α ≤ x0 1 := by
  have h0I : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ I := ⟨zero_le_one, le_rfl⟩
  intro t ht α hα
  have hlow : x0 0 ≤ x t 0 := by
    rw [hx.eq t ht 0 h0I]
    have : 0 ≤ ∫ τ in (0 : ℝ)..t, opL (x τ) 0 := by
      refine intervalIntegral.integral_nonneg ht (fun τ hτ => ?_)
      unfold opL
      refine setIntegral_nonneg measurableSet_Icc (fun γ hγ => ?_)
      have := (hmono τ hτ.1).1 h0I hγ hγ.1
      split_ifs <;> linarith
    linarith
  have hup : x t 1 ≤ x0 1 := by
    rw [hx.eq t ht 1 h1I]
    have : 0 ≤ ∫ τ in (0 : ℝ)..t, -opL (x τ) 1 := by
      refine intervalIntegral.integral_nonneg ht (fun τ hτ => ?_)
      rw [neg_nonneg]
      unfold opL
      refine setIntegral_nonpos measurableSet_Icc (fun γ hγ => ?_)
      have := (hmono τ hτ.1).1 hγ h1I hγ.2
      split_ifs <;> linarith
    rw [intervalIntegral.integral_neg] at this
    linarith
  exact ⟨hlow.trans ((hmono t ht).1 h0I hα hα.1), ((hmono t ht).1 hα h1I hα.2).trans hup⟩

end BHT6P3a

open BHTOpinion.Continuum BHT6P3a in
theorem solution (x0 : ℝ → ℝ) (x : ℝ → ℝ → ℝ)
    (hx : IsSolution x0 x) (hmono : ∀ t : ℝ, 0 ≤ t → InX (x t)) (y : ℝ → ℝ)
    (hy : ∀ᵐ α ∂(volume.restrict I), Tendsto (fun t => x t α) atTop (𝓝 (y α))) :
    ∃ y' : ℝ → ℝ, InFbar y' ∧ y' =ᵐ[volume.restrict I] y := by
  classical
  ------------------------------------------------------------------
  -- jointly measurable extension of `x`
  let pI : ℝ → I := fun α => ⟨max 0 (min 1 α), le_max_left _ _,
    max_le zero_le_one (min_le_left _ _)⟩
  let pT : ℝ → Set.Ici (0 : ℝ) := fun τ => ⟨max 0 τ, Set.mem_Ici.mpr (le_max_left _ _)⟩
  have hpI : Measurable pI :=
    (measurable_const.max (measurable_const.min measurable_id)).subtype_mk
  have hpT : Measurable pT := (measurable_const.max measurable_id).subtype_mk
  let xh : ℝ → ℝ → ℝ := fun τ α => x (pT τ) (pI α)
  have hxh_meas : Measurable (fun p : ℝ × ℝ => xh p.1 p.2) :=
    hx.measurable.comp ((hpI.comp measurable_snd).prodMk (hpT.comp measurable_fst))
  have hxh_eq : ∀ τ, 0 ≤ τ → ∀ α ∈ I, xh τ α = x τ α := by
    intro τ hτ α hα
    simp only [xh, pT, pI]
    rw [max_eq_right hτ, min_eq_right hα.2, max_eq_right hα.1]
  have hxh_meas1 : ∀ τ, Measurable (xh τ) := fun τ =>
    hxh_meas.comp (measurable_const.prodMk measurable_id)
  let G : ℝ → ℝ → ℝ := fun τ α => ∫ γ in I, φ (xh τ α) (xh τ γ)
  have hG_eq : ∀ τ, 0 ≤ τ → ∀ α ∈ I, opL (x τ) α = G τ α := by
    intro τ hτ α hα
    simp only [G, opL, φ]
    refine setIntegral_congr_fun measurableSet_Icc (fun γ hγ => ?_)
    simp only [hxh_eq τ hτ α hα, hxh_eq τ hτ γ hγ]
  have h3 : Measurable (fun q : (ℝ × ℝ) × ℝ => φ (xh q.1.1 q.1.2) (xh q.1.1 q.2)) :=
    φ_meas.comp ((hxh_meas.comp measurable_fst).prodMk
      (hxh_meas.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  have hG_meas : Measurable (fun p : ℝ × ℝ => G p.1 p.2) :=
    (h3.stronglyMeasurable.integral_prod_right' (ν := volume.restrict I)).measurable
  have hG_abs : ∀ τ α, |G τ α| ≤ 1 := fun τ α => inner_abs (xh τ) α
  have hb := bounds x0 x hx hmono
  have hint : ∀ t, 0 ≤ t → ∀ c ∈ I, IntervalIntegrable (x t) volume 0 c := by
    intro t ht c hc
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hc.1]
    exact (hmono t ht).1.mono (fun β hβ => ⟨hβ.1, hβ.2.trans hc.2⟩)
  have h0I : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  have hx01 : x0 0 ≤ x0 1 := by
    have := hb 0 le_rfl 0 h0I; linarith [this.1, this.2]
  ------------------------------------------------------------------
  -- the cross interaction `H c τ`
  let H : ℝ → ℝ → ℝ := fun c τ =>
    ∫ α in Set.Ioc 0 c, ∫ γ in Set.Ioc c 1, φ (xh τ α) (xh τ γ)
  have hH_meas : ∀ c, Measurable (H c) := by
    intro c
    have h4 : Measurable (fun p : ℝ × ℝ => ∫ γ in Set.Ioc c 1, φ (xh p.1 p.2) (xh p.1 γ)) :=
      (h3.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc c 1))).measurable
    exact (h4.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Ioc 0 c))).measurable
  have hH_nonneg : ∀ c ∈ I, ∀ τ, 0 ≤ τ → 0 ≤ H c τ := by
    intro c hc τ hτ
    refine setIntegral_nonneg measurableSet_Ioc (fun α hα => ?_)
    refine setIntegral_nonneg measurableSet_Ioc (fun γ hγ => ?_)
    have hαI : α ∈ I := ⟨hα.1.le, hα.2.trans hc.2⟩
    have hγI : γ ∈ I := ⟨(hc.1.trans_lt hγ.1).le, hγ.2⟩
    rw [hxh_eq τ hτ α hαI, hxh_eq τ hτ γ hγI]
    exact φ_nonneg _ _ ((hmono τ hτ).1 hαI hγI (hα.2.trans hγ.1.le))
  have hH_abs : ∀ c ∈ I, ∀ τ, |H c τ| ≤ 1 := by
    intro c hc τ
    have hin : ∀ α, ‖∫ γ in Set.Ioc c 1, φ (xh τ α) (xh τ γ)‖ ≤ 1 := by
      intro α
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc c 1)
        measure_Ioc_lt_top (f := fun γ => φ (xh τ α) (xh τ γ)) (C := 1)
        (fun γ _ => by rw [Real.norm_eq_abs]; exact φ_abs _ _)
      rw [Real.volume_real_Ioc_of_le hc.2] at this
      linarith [hc.1]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc 0 c)
      measure_Ioc_lt_top (C := 1) (fun α _ => hin α)
    rw [Real.volume_real_Ioc_of_le hc.1] at this
    rw [← Real.norm_eq_abs]; linarith [hc.2]
  have hH_int : ∀ c ∈ I, ∀ a b : ℝ, IntegrableOn (H c) (Set.Ioc a b) := by
    intro c hc a b
    have : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := by
      rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
    exact Integrable.of_bound (C := 1) (hH_meas c).aestronglyMeasurable
      (Eventually.of_forall (fun τ => by rw [Real.norm_eq_abs]; exact hH_abs c hc τ))
  ------------------------------------------------------------------
  -- (3.8): the time integral of `H c` is bounded
  have hHbound : ∀ c ∈ I, ∀ T, 0 ≤ T → ∫ τ in Set.Ioc 0 T, H c τ ≤ c * (x0 1 - x0 0) := by
    intro c hc T hT
    have hdiff : (∫ α in (0 : ℝ)..c, x T α) - ∫ α in (0 : ℝ)..c, x 0 α =
        ∫ α in Set.Ioc 0 c, ∫ τ in Set.Ioc 0 T, G τ α := by
      rw [show (∫ α in (0 : ℝ)..c, x T α) - ∫ α in (0 : ℝ)..c, x 0 α =
          ∫ α in (0 : ℝ)..c, (x T α - x 0 α) from
          (intervalIntegral.integral_sub (hint T hT c hc) (hint 0 le_rfl c hc)).symm,
        intervalIntegral.integral_of_le hc.1]
      refine setIntegral_congr_fun measurableSet_Ioc (fun α hα => ?_)
      have hαI : α ∈ I := ⟨hα.1.le, hα.2.trans hc.2⟩
      have e1 := hx.eq T hT α hαI
      have e2 := hx.eq 0 le_rfl α hαI
      have hsub := intervalIntegral.integral_interval_sub_left
        (hx.integrable T hT α hαI) (hx.integrable 0 le_rfl α hαI)
      rw [e1, e2, add_sub_add_left_eq_sub, hsub, intervalIntegral.integral_of_le hT]
      refine setIntegral_congr_fun measurableSet_Ioc (fun τ hτ => ?_)
      exact hG_eq τ hτ.1.le α hαI
    have fin1 : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) c)) := by
      rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
    have fin2 : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) T)) := by
      rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
    have hswap := integral_integral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) c))
      (ν := volume.restrict (Set.Ioc (0 : ℝ) T)) (f := fun α τ => G τ α) (by
        refine Integrable.of_bound (C := 1)
          (hG_meas.comp measurable_swap).aestronglyMeasurable ?_
        exact Eventually.of_forall (fun p => by rw [Real.norm_eq_abs]; exact hG_abs _ _))
    have hcross : ∫ τ in Set.Ioc 0 T, ∫ α in Set.Ioc 0 c, G τ α =
        ∫ τ in Set.Ioc 0 T, H c τ := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun τ _ => ?_)
      exact cross_eq (xh τ) (hxh_meas1 τ) c hc
    have hFT : ∫ α in (0 : ℝ)..c, x T α ≤ c * x0 1 := by
      have := intervalIntegral.integral_mono_on (μ := volume) hc.1
        (hint T hT c hc) intervalIntegrable_const
        (g := fun _ => x0 1) (fun β hβ => (hb T hT β ⟨hβ.1, hβ.2.trans hc.2⟩).2)
      simpa using this
    have hF0 : c * x0 0 ≤ ∫ α in (0 : ℝ)..c, x 0 α := by
      have := intervalIntegral.integral_mono_on (μ := volume) hc.1
        intervalIntegrable_const (hint 0 le_rfl c hc)
        (f := fun _ => x0 0) (fun β hβ => (hb 0 le_rfl β ⟨hβ.1, hβ.2.trans hc.2⟩).1)
      simpa using this
    rw [← hcross, ← hswap, ← hdiff]
    linarith
  ------------------------------------------------------------------
  -- a sequence of times along which `H c` tends to zero
  have hsmall : ∀ c ∈ I, ∀ n : ℕ, ∃ τ : ℝ, (n : ℝ) ≤ τ ∧ H c τ ≤ 1 / ((n : ℝ) + 1) := by
    intro c hc n
    by_contra hcon
    push Not at hcon
    set B := c * (x0 1 - x0 0)
    have hB0 : 0 ≤ B := mul_nonneg hc.1 (by linarith)
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set T := (n : ℝ) + (B + 1) * ((n : ℝ) + 1)
    have hnT : (n : ℝ) ≤ T := by
      have : 0 ≤ (B + 1) * ((n : ℝ) + 1) := by positivity
      linarith
    have hT0 : 0 ≤ T := le_trans (Nat.cast_nonneg n) hnT
    have h1 := hHbound c hc T hT0
    have h2 : ∫ τ in Set.Ioc (n : ℝ) T, H c τ ≤ ∫ τ in Set.Ioc 0 T, H c τ := by
      refine setIntegral_mono_set (hH_int c hc 0 T) ?_ ?_
      · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall (fun τ hτ => hH_nonneg c hc τ hτ.1.le)
      · exact Eventually.of_forall (Set.Ioc_subset_Ioc_left (Nat.cast_nonneg n))
    have h3' : ∫ τ in Set.Ioc (n : ℝ) T, (1 / ((n : ℝ) + 1)) ≤
        ∫ τ in Set.Ioc (n : ℝ) T, H c τ := by
      refine setIntegral_mono_on ?_ (hH_int c hc _ _) measurableSet_Ioc
        (fun τ hτ => (hcon τ hτ.1.le).le)
      exact integrableOn_const (by simp)
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hnT, smul_eq_mul] at h3'
    have : (T - n) * (1 / ((n : ℝ) + 1)) = B + 1 := by
      simp only [T]; field_simp; ring
    linarith
  ------------------------------------------------------------------
  -- the monotone representative `Y` of the limit
  let cl : ℝ → ℝ := fun α => max 0 (min 1 α)
  have hclI : ∀ α, cl α ∈ I := fun α =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hclmono : Monotone cl := fun a b hab => max_le_max le_rfl (min_le_min le_rfl hab)
  have hclid : ∀ α ∈ I, cl α = α := fun α hα => by
    simp only [cl]; rw [min_eq_right hα.2, max_eq_right hα.1]
  have hbdd : ∀ α, IsBoundedUnder (· ≤ ·) atTop (fun t => x t (cl α)) := fun α =>
    ⟨x0 1, eventually_map.2 ((eventually_ge_atTop 0).mono fun t ht => (hb t ht _ (hclI α)).2)⟩
  have hcobdd : ∀ α, IsCoboundedUnder (· ≤ ·) atTop (fun t => x t (cl α)) := fun α =>
    isCoboundedUnder_le_of_eventually_le atTop
      ((eventually_ge_atTop 0).mono fun t ht => (hb t ht _ (hclI α)).1)
  let Y : ℝ → ℝ := fun α => limsup (fun t => x t (cl α)) atTop
  have hYmono : Monotone Y := by
    intro a b hab
    refine limsup_le_limsup ?_ (hcobdd a) (hbdd b)
    exact (eventually_ge_atTop 0).mono fun t ht =>
      (hmono t ht).1 (hclI a) (hclI b) (hclmono hab)
  have hYmeas : Measurable Y := hYmono.measurable
  have hYbd : ∀ α, x0 0 ≤ Y α ∧ Y α ≤ x0 1 := by
    intro α
    refine ⟨le_limsup_of_le (hbdd α) (fun b hb' => ?_), limsup_le_of_le (hcobdd α)
      ((eventually_ge_atTop 0).mono fun t ht => (hb t ht _ (hclI α)).2)⟩
    obtain ⟨t, h1, h2⟩ := (hb'.and (eventually_ge_atTop 0)).exists
    exact (hb t h2 _ (hclI α)).1.trans h1
  have hYconv : ∀ᵐ α ∂(volume.restrict I), α ∈ I ∧
      Tendsto (fun t => x t α) atTop (𝓝 (Y α)) ∧ Y α = y α := by
    filter_upwards [hy, ae_restrict_mem measurableSet_Icc] with α hα hαI
    have hYα : Y α = y α := by
      simp only [Y, hclid α hαI]; exact hα.limsup_eq
    exact ⟨hαI, hYα ▸ hα, hYα⟩
  ------------------------------------------------------------------
  -- Fatou: for each `c`, the limit has no connected pair across `c`
  let good : ℝ × ℝ → Prop := fun p => Y p.1 = Y p.2 ∨ 1 ≤ |Y p.1 - Y p.2|
  have hcut : ∀ c ∈ I, ∀ᵐ p ∂((volume.restrict (Set.Ioc (0 : ℝ) c)).prod
      (volume.restrict (Set.Ioc c (1 : ℝ)))), good p := by
    intro c hc
    choose τs hτs1 hτs2 using hsmall c hc
    have hτs0 : ∀ n, 0 ≤ τs n := fun n => le_trans (Nat.cast_nonneg n) (hτs1 n)
    have hτtend : Tendsto τs atTop atTop :=
      tendsto_atTop_mono hτs1 tendsto_natCast_atTop_atTop
    have hHtend : Tendsto (fun n => H c (τs n)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat (fun n => hH_nonneg c hc _ (hτs0 n)) hτs2
    set μc := (volume.restrict (Set.Ioc (0 : ℝ) c)).prod (volume.restrict (Set.Ioc c (1 : ℝ)))
    have fin1 : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) c)) := by
      rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
    have fin2 : IsFiniteMeasure (volume.restrict (Set.Ioc c (1 : ℝ))) := by
      rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
    have hreg : ∀ᵐ p ∂μc, p.1 ∈ Set.Ioc 0 c ∧ p.2 ∈ Set.Ioc c 1 := by
      have : ∀ᵐ p ∂μc, p ∈ Set.Ioc (0 : ℝ) c ×ˢ Set.Ioc c (1 : ℝ) := by
        simp only [μc]; rw [Measure.prod_restrict]
        exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
      exact this
    have hconv1 : ∀ᵐ p ∂μc, Tendsto (fun t => x t p.1) atTop (𝓝 (Y p.1)) := by
      have : ∀ᵐ α ∂(volume.restrict (Set.Ioc (0 : ℝ) c)),
          Tendsto (fun t => x t α) atTop (𝓝 (Y α)) :=
        ae_mono (Measure.restrict_mono (show Set.Ioc (0 : ℝ) c ⊆ I from
          fun a ha => ⟨ha.1.le, ha.2.trans hc.2⟩) le_rfl)
          (hYconv.mono fun α h => h.2.1)
      exact Measure.quasiMeasurePreserving_fst.ae this
    have hconv2 : ∀ᵐ p ∂μc, Tendsto (fun t => x t p.2) atTop (𝓝 (Y p.2)) := by
      have : ∀ᵐ α ∂(volume.restrict (Set.Ioc c (1 : ℝ))),
          Tendsto (fun t => x t α) atTop (𝓝 (Y α)) :=
        ae_mono (Measure.restrict_mono (show Set.Ioc c (1 : ℝ) ⊆ I from
          fun a ha => ⟨(hc.1.trans_lt ha.1).le, ha.2⟩) le_rfl)
          (hYconv.mono fun α h => h.2.1)
      exact Measure.quasiMeasurePreserving_snd.ae this
    let f : ℕ → ℝ × ℝ → ℝ := fun n p => φ (xh (τs n) p.1) (xh (τs n) p.2)
    have hf_meas : ∀ n, Measurable (f n) := fun n =>
      φ_meas.comp (((hxh_meas1 _).comp measurable_fst).prodMk ((hxh_meas1 _).comp measurable_snd))
    have hf_int : ∀ n, Integrable (f n) μc := fun n =>
      Integrable.of_bound (C := 1) (hf_meas n).aestronglyMeasurable
        (Eventually.of_forall (fun p => by rw [Real.norm_eq_abs]; exact φ_abs _ _))
    have hf_nn : ∀ n, 0 ≤ᵐ[μc] f n := by
      intro n
      filter_upwards [hreg] with p hp
      have h1I : p.1 ∈ I := ⟨hp.1.1.le, hp.1.2.trans hc.2⟩
      have h2I : p.2 ∈ I := ⟨(hc.1.trans_lt hp.2.1).le, hp.2.2⟩
      simp only [f, Pi.zero_apply]
      rw [hxh_eq _ (hτs0 n) _ h1I, hxh_eq _ (hτs0 n) _ h2I]
      exact φ_nonneg _ _ ((hmono _ (hτs0 n)).1 h1I h2I (hp.1.2.trans hp.2.1.le))
    have hlint : ∀ n, ∫⁻ p, ENNReal.ofReal (f n p) ∂μc = ENNReal.ofReal (H c (τs n)) := by
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (hf_int n) (hf_nn n)]
      congr 1
      exact integral_prod (f n) (hf_int n)
    have hfatou := lintegral_liminf_le (μ := μc) (u := atTop)
      (fun n => (hf_meas n).ennreal_ofReal)
    simp only [hlint] at hfatou
    have hlim0 : liminf (fun n => ENNReal.ofReal (H c (τs n))) atTop = 0 := by
      have := (ENNReal.tendsto_ofReal hHtend).liminf_eq
      simpa using this
    rw [hlim0] at hfatou
    let ψ : ℝ × ℝ → ℝ := fun p => φ (Y p.1) (Y p.2)
    have hψle : ∀ᵐ p ∂μc, ENNReal.ofReal (ψ p) ≤
        liminf (fun n => ENNReal.ofReal (f n p)) atTop := by
      filter_upwards [hreg, hconv1, hconv2] with p hp hc1 hc2
      have h1I : p.1 ∈ I := ⟨hp.1.1.le, hp.1.2.trans hc.2⟩
      have h2I : p.2 ∈ I := ⟨(hc.1.trans_lt hp.2.1).le, hp.2.2⟩
      have hs1 := hc1.comp hτtend
      have hs2 := hc2.comp hτtend
      have hfeq : ∀ n, f n p = φ (x (τs n) p.1) (x (τs n) p.2) := by
        intro n; simp only [f]; rw [hxh_eq _ (hτs0 n) _ h1I, hxh_eq _ (hτs0 n) _ h2I]
      by_cases hcon : |Y p.1 - Y p.2| < 1
      · have hd : Tendsto (fun n => |x (τs n) p.1 - x (τs n) p.2|) atTop
            (𝓝 |Y p.1 - Y p.2|) := (hs1.sub hs2).abs
        have hev : ∀ᶠ n in atTop, |x (τs n) p.1 - x (τs n) p.2| < 1 :=
          (tendsto_order.1 hd).2 1 hcon
        have hft : Tendsto (fun n => f n p) atTop (𝓝 (ψ p)) := by
          have : Tendsto (fun n => x (τs n) p.2 - x (τs n) p.1) atTop
              (𝓝 (Y p.2 - Y p.1)) := hs2.sub hs1
          refine (this.congr' ?_).trans ?_
          · filter_upwards [hev] with n hn
            rw [hfeq n]; simp only [φ, if_pos hn]
          · simp only [ψ, φ, if_pos hcon]; exact le_rfl
        rw [(ENNReal.tendsto_ofReal hft).liminf_eq]
      · simp only [ψ, φ, if_neg hcon, ENNReal.ofReal_zero]
        exact bot_le
    have hψint : ∫⁻ p, ENNReal.ofReal (ψ p) ∂μc = 0 := by
      refine le_antisymm ?_ bot_le
      exact (lintegral_mono_ae hψle).trans hfatou
    have hψmeas : Measurable (fun p => ENNReal.ofReal (ψ p)) :=
      ENNReal.measurable_ofReal.comp
        (φ_meas.comp ((hYmeas.comp measurable_fst).prodMk (hYmeas.comp measurable_snd)))
    rw [lintegral_eq_zero_iff hψmeas] at hψint
    filter_upwards [hψint, hreg] with p hp hreg'
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hp
    have hYle : Y p.1 ≤ Y p.2 := hYmono (hreg'.1.2.trans hreg'.2.1.le)
    by_cases hcon : |Y p.1 - Y p.2| < 1
    · left
      simp only [ψ, φ, if_pos hcon] at hp
      linarith
    · right; linarith [not_lt.mp hcon]
  ------------------------------------------------------------------
  -- assemble over rational cuts
  set ν := (volume.restrict I).prod (volume.restrict I)
  have hν : ν = (volume.prod volume).restrict (I ×ˢ I) := Measure.prod_restrict _ _
  have hcut' : ∀ q : ℚ, ∀ᵐ p ∂ν, (q : ℝ) ∈ I → p.1 ∈ Set.Ioc 0 (q : ℝ) →
      p.2 ∈ Set.Ioc (q : ℝ) 1 → good p := by
    intro q
    by_cases hq : (q : ℝ) ∈ I
    · have h := hcut q hq
      rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)] at h
      rw [hν]
      filter_upwards [ae_restrict_of_ae h] with p hp _ h1 h2
      exact hp ⟨h1, h2⟩
    · exact Eventually.of_forall (fun p h => absurd h hq)
  have hall := ae_all_iff.2 hcut'
  have hne0 : ∀ᵐ p ∂ν, p.1 ≠ 0 := by
    have : ∀ᵐ α ∂(volume.restrict I), α ≠ 0 :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (Real.volume_singleton (a := 0)))
    exact Measure.quasiMeasurePreserving_fst.ae this
  have hmemI : ∀ᵐ p ∂ν, p.1 ∈ I ∧ p.2 ∈ I := by
    have : ∀ᵐ p ∂ν, p ∈ I ×ˢ I := by
      rw [hν]; exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
    exact this
  have hlt : ∀ᵐ p ∂ν, p.1 < p.2 → good p := by
    filter_upwards [hall, hne0, hmemI] with p hp h0 hI hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hpos : 0 < p.1 := lt_of_le_of_ne hI.1.1 (Ne.symm h0)
    exact hp q ⟨(hI.1.1.trans hq1.le), hq2.le.trans hI.2.2⟩ ⟨hpos, hq1.le⟩ ⟨hq2, hI.2.2⟩
  have hgt : ∀ᵐ p ∂ν, p.2 < p.1 → good p := by
    have h := (Measure.measurePreserving_swap (μ := volume.restrict I)
      (ν := volume.restrict I)).quasiMeasurePreserving.ae hlt
    filter_upwards [h] with p hp hlt'
    rcases hp hlt' with h1 | h1
    · left; exact h1.symm
    · right; rw [abs_sub_comm]; exact h1
  refine ⟨Y, ⟨⟨hYmono.monotoneOn _, max |x0 0| |x0 1|, fun α _ => ?_⟩, ?_⟩, ?_⟩
  · rw [abs_le]
    have := hYbd α
    constructor
    · linarith [neg_abs_le (x0 0), le_max_left |x0 0| |x0 1|]
    · linarith [le_abs_self (x0 1), le_max_right |x0 0| |x0 1|]
  · filter_upwards [hlt, hgt] with p h1 h2
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · exact h1 h
    · left; rw [h]
    · exact h2 h
  · filter_upwards [hYconv] with α h
    exact h.2.2
