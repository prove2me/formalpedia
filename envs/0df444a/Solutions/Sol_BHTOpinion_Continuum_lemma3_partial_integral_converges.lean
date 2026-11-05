-- Prove2me | solution 1 for BHTOpinion.Continuum.lemma3_partial_integral_converges
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:53:15.97728+00:00
-- url     : https://prove2.me/submissions/51d86ad4-3017-4995-bd26-0fbe9db4d3ba

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHT6L3

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

/-- The key symmetry estimate (3.9): for `u` measurable and nondecreasing on `I`,
`∫_0^c ∫_I φ(u α, u γ) dγ dα ≥ 0`. -/
lemma sym_nonneg (u : ℝ → ℝ) (hu : Measurable u) (hmono : MonotoneOn u I) (c : ℝ)
    (hc : c ∈ I) : 0 ≤ ∫ α in Set.Ioc 0 c, ∫ γ in I, φ (u α) (u γ) := by
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
  -- the cross part is nonnegative
  refine setIntegral_nonneg measurableSet_Ioc (fun α hα => ?_)
  refine setIntegral_nonneg measurableSet_Ioc (fun γ hγ => ?_)
  have hαI : α ∈ I := ⟨hα.1.le, hα.2.trans hc.2⟩
  have hγI : γ ∈ I := ⟨(hc.1.trans_lt hγ.1).le, hγ.2⟩
  exact φ_nonneg _ _ (hmono hαI hγI (hα.2.trans hγ.1.le))

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

end BHT6L3

open BHTOpinion.Continuum in
theorem solution (x0 : ℝ → ℝ) (x : ℝ → ℝ → ℝ)
    (hx : IsSolution x0 x) (hmono : ∀ t : ℝ, 0 ≤ t → InX (x t)) :
    (∀ c ∈ I, ∃ l : ℝ, Tendsto (fun t => ∫ α in (0 : ℝ)..c, x t α) atTop (𝓝 l)) ∧
      ∀ b ∈ I, ∀ c ∈ I, b < c →
        ∃ l : ℝ, Tendsto (fun t => (∫ α in b..c, x t α) / (c - b)) atTop (𝓝 l) := by
  open BHT6L3 in
  -- a jointly measurable extension of `x`
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
  -- the jointly measurable version of `opL`
  let G : ℝ → ℝ → ℝ := fun τ α => ∫ γ in I, φ (xh τ α) (xh τ γ)
  have hG_eq : ∀ τ, 0 ≤ τ → ∀ α ∈ I, opL (x τ) α = G τ α := by
    intro τ hτ α hα
    simp only [G, opL, φ]
    refine setIntegral_congr_fun measurableSet_Icc (fun γ hγ => ?_)
    simp only [hxh_eq τ hτ α hα, hxh_eq τ hτ γ hγ]
  have hG_meas : Measurable (fun p : ℝ × ℝ => G p.1 p.2) := by
    have h3 : Measurable (fun q : (ℝ × ℝ) × ℝ => φ (xh q.1.1 q.1.2) (xh q.1.1 q.2)) :=
      φ_meas.comp ((hxh_meas.comp measurable_fst).prodMk
        (hxh_meas.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
    exact (h3.stronglyMeasurable.integral_prod_right' (ν := volume.restrict I)).measurable
  have hG_abs : ∀ τ α, |G τ α| ≤ 1 := fun τ α => inner_abs (xh τ) α
  have hb := bounds x0 x hx hmono
  have hint : ∀ t, 0 ≤ t → ∀ c ∈ I, IntervalIntegrable (x t) volume 0 c := by
    intro t ht c hc
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hc.1]
    exact (hmono t ht).1.mono (fun β hβ => ⟨hβ.1, hβ.2.trans hc.2⟩)
  -- monotonicity in time of the partial integrals
  have hFmono : ∀ c ∈ I, ∀ t1 t2 : ℝ, 0 ≤ t1 → t1 ≤ t2 →
      ∫ α in (0 : ℝ)..c, x t1 α ≤ ∫ α in (0 : ℝ)..c, x t2 α := by
    intro c hc t1 t2 ht1 ht12
    have ht2 : 0 ≤ t2 := ht1.trans ht12
    have hdiff : (∫ α in (0 : ℝ)..c, x t2 α) - ∫ α in (0 : ℝ)..c, x t1 α =
        ∫ α in Set.Ioc 0 c, ∫ τ in Set.Ioc t1 t2, G τ α := by
      rw [show (∫ α in (0 : ℝ)..c, x t2 α) - ∫ α in (0 : ℝ)..c, x t1 α =
          ∫ α in (0 : ℝ)..c, (x t2 α - x t1 α) from
          (intervalIntegral.integral_sub (hint t2 ht2 c hc) (hint t1 ht1 c hc)).symm,
        intervalIntegral.integral_of_le hc.1]
      refine setIntegral_congr_fun measurableSet_Ioc (fun α hα => ?_)
      have hαI : α ∈ I := ⟨hα.1.le, hα.2.trans hc.2⟩
      have e1 := hx.eq t2 ht2 α hαI
      have e2 := hx.eq t1 ht1 α hαI
      have hsub := intervalIntegral.integral_interval_sub_left
        (hx.integrable t2 ht2 α hαI) (hx.integrable t1 ht1 α hαI)
      rw [e1, e2, add_sub_add_left_eq_sub, hsub, intervalIntegral.integral_of_le ht12]
      refine setIntegral_congr_fun measurableSet_Ioc (fun τ hτ => ?_)
      exact hG_eq τ (ht1.trans hτ.1.le) α hαI
    have fin1 : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) c)) := by
      rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
    have fin2 : IsFiniteMeasure (volume.restrict (Set.Ioc t1 t2)) := by
      rw [isFiniteMeasure_restrict]; exact measure_Ioc_lt_top.ne
    have hswap := integral_integral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) c))
      (ν := volume.restrict (Set.Ioc t1 t2)) (f := fun α τ => G τ α) (by
        refine Integrable.of_bound (C := 1)
          (hG_meas.comp measurable_swap).aestronglyMeasurable ?_
        exact Eventually.of_forall (fun p => by rw [Real.norm_eq_abs]; exact hG_abs _ _))
    have hnn : 0 ≤ ∫ α in Set.Ioc 0 c, ∫ τ in Set.Ioc t1 t2, G τ α := by
      rw [hswap]
      refine setIntegral_nonneg measurableSet_Ioc (fun τ hτ => ?_)
      have hτ0 : 0 ≤ τ := ht1.trans hτ.1.le
      refine sym_nonneg (xh τ) (hxh_meas1 τ) ?_ c hc
      intro a ha b hb' hab
      rw [hxh_eq τ hτ0 a ha, hxh_eq τ hτ0 b hb']
      exact (hmono τ hτ0).1 ha hb' hab
    linarith
  -- convergence of the partial integrals
  have hconv : ∀ c ∈ I, ∃ l : ℝ, Tendsto (fun t => ∫ α in (0 : ℝ)..c, x t α) atTop (𝓝 l) := by
    intro c hc
    let F : ℝ → ℝ := fun t => ∫ α in (0 : ℝ)..c, x (max 0 t) α
    have hFm : Monotone F := fun a b hab =>
      hFmono c hc _ _ (le_max_left _ _) (max_le_max le_rfl hab)
    have hFb : BddAbove (Set.range F) := by
      refine ⟨c * x0 1, ?_⟩
      rintro _ ⟨t, rfl⟩
      have := intervalIntegral.integral_mono_on (μ := volume) hc.1
        (hint (max 0 t) (le_max_left _ _) c hc) intervalIntegrable_const
        (g := fun _ => x0 1) (fun β hβ => (hb (max 0 t) (le_max_left _ _) β
          ⟨hβ.1, hβ.2.trans hc.2⟩).2)
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
      exact this
    refine ⟨_, (tendsto_atTop_ciSup hFm hFb).congr' ?_⟩
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [F, max_eq_right ht]
  refine ⟨hconv, fun b hbI c hcI hbc => ?_⟩
  obtain ⟨lb, hlb⟩ := hconv b hbI
  obtain ⟨lc, hlc⟩ := hconv c hcI
  refine ⟨(lc - lb) / (c - b), ((hlc.sub hlb).div_const (c - b)).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [intervalIntegral.integral_interval_sub_left (hint t ht c hcI) (hint t ht b hbI)]
