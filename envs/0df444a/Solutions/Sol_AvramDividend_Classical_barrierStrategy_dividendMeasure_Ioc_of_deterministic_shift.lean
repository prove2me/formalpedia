-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_dividendMeasure_Ioc_of_deterministic_shift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:41:12.020305+00:00
-- url     : https://prove2.me/submissions/16d917b4-5db2-44c0-afb9-1cb339446351

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace A3S49BS

lemma bdd_of_cadlag (f : ℝ≥0 → ℝ) (hr : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hl : ∀ t, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (𝓝 l)) {K : Set ℝ≥0} (hK : IsCompact K) :
    BddAbove (f '' K) := by
  refine hK.induction_on (p := fun S => BddAbove (f '' S)) (by simp)
    (fun s t hst ht => ht.mono (image_mono hst)) (fun s t hs ht => by rw [image_union]; exact hs.union ht) ?_
  intro x _
  have hR : ∀ᶠ y in 𝓝[≥] x, f y < f x + 1 :=
    (hr x).eventually (gt_mem_nhds (by linarith))
  have hnhds : ∃ c : ℝ, ∀ᶠ y in 𝓝 x, f y < c := by
    rcases eq_or_ne x 0 with rfl | hx0
    · refine ⟨f 0 + 1, ?_⟩
      have : 𝓝[≥] (0 : ℝ≥0) = 𝓝 0 := by
        rw [show Ici (0 : ℝ≥0) = univ from Set.ext fun y => by simp, nhdsWithin_univ]
      rwa [this] at hR
    · obtain ⟨l, hl⟩ := hl x (pos_iff_ne_zero.mpr hx0)
      have hL : ∀ᶠ y in 𝓝[<] x, f y < l + 1 := hl.eventually (gt_mem_nhds (by linarith))
      refine ⟨max (f x + 1) (l + 1), ?_⟩
      rw [← nhdsLT_sup_nhdsGE, eventually_sup]
      exact ⟨hL.mono fun y hy => lt_max_of_lt_right hy, hR.mono fun y hy => lt_max_of_lt_left hy⟩
  obtain ⟨c, hc⟩ := hnhds
  refine ⟨{y | f y < c}, mem_nhdsWithin_of_mem_nhds hc, c, ?_⟩
  rintro _ ⟨y, hy, rfl⟩; exact le_of_lt hy

lemma runSup_mono (g : ℝ≥0 → ℝ) (hb : ∀ T, BddAbove (g '' Icc 0 T)) :
    Monotone (fun r => sSup (g '' Icc 0 r)) := by
  intro r r' h
  exact csSup_le_csSup (hb r') ⟨g 0, 0, ⟨le_rfl, zero_le⟩, rfl⟩
    (image_mono (Icc_subset_Icc le_rfl h))

lemma le_runSup (g : ℝ≥0 → ℝ) (hb : ∀ T, BddAbove (g '' Icc 0 T)) {s r : ℝ≥0} (h : s ≤ r) :
    g s ≤ sSup (g '' Icc 0 r) :=
  le_csSup (hb r) ⟨s, ⟨zero_le, h⟩, rfl⟩

lemma runSup_rc (g : ℝ≥0 → ℝ) (hb : ∀ T, BddAbove (g '' Icc 0 T))
    (hr : ∀ t, ContinuousWithinAt g (Ici t) t) (t : ℝ≥0) :
    Tendsto (fun r => sSup (g '' Icc 0 r)) (𝓝[>] t) (𝓝 (sSup (g '' Icc 0 t))) := by
  rw [tendsto_order]
  constructor
  · intro b hb'
    filter_upwards [self_mem_nhdsWithin] with r hr'
    exact lt_of_lt_of_le hb' (runSup_mono g hb (le_of_lt hr'))
  · intro b hb'
    obtain ⟨c, hc1, hc2⟩ := exists_between hb'
    have hgt : g t < c := lt_of_le_of_lt (le_runSup g hb le_rfl) hc1
    have hev : ∀ᶠ y in 𝓝[≥] t, g y < c := (hr t).eventually (gt_mem_nhds hgt)
    obtain ⟨w, hw, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
    filter_upwards [Ioo_mem_nhdsGT hw] with r hr'
    refine lt_of_le_of_lt ?_ hc2
    refine csSup_le ⟨g 0, 0, ⟨le_rfl, zero_le⟩, rfl⟩ ?_
    rintro _ ⟨s, hs, rfl⟩
    rcases le_or_gt s t with hst | hst
    · exact (le_runSup g hb hst).trans hc1.le
    · exact (hsub ⟨hst.le, lt_of_le_of_lt hs.2 hr'.2⟩).le

lemma tendsto_toNNReal_nhdsGT {y : ℝ} (hy : 0 ≤ y) :
    Tendsto Real.toNNReal (𝓝[>] y) (𝓝[>] y.toNNReal) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact (continuous_real_toNNReal.tendsto y).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    show y.toNNReal < z.toNNReal
    exact (Real.toNNReal_lt_toNNReal_iff (lt_of_le_of_lt hy hz)).mpr hz

end A3S49BS

open A3S49BS in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hxa : x ≤ a)
    (ω : Ω) (u t : ℝ≥0)
    (hb : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t)))
    (hshift : ∀ s : ℝ≥0, s ≤ t →
      barrierStrategy X x a (u + s) ω - barrierStrategy X x a u ω =
        max 0
          (sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 s))) :
    (dividendMeasure (barrierStrategy X x a) ω)
        (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) =
      (dividendMeasure
        (fun r _ =>
          sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
        ω) (Set.Ioc (0 : ℝ) (t : ℝ)) := by
  set f : ℝ≥0 → ℝ := fun r => X.X r ω with hf
  have hbdd : ∀ T, BddAbove (f '' Icc 0 T) := fun T =>
    bdd_of_cadlag f (X.rightCont ω) (fun s hs => X.leftLim ω s hs) isCompact_Icc
  set g : ℝ≥0 → ℝ := fun v => X.X (u + v) ω - X.X u ω with hg
  have hgb : ∀ T, BddAbove (g '' Icc 0 T) := by
    intro T
    obtain ⟨C, hC⟩ := hbdd (u + T)
    refine ⟨C - f u, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    have := hC ⟨u + v, ⟨zero_le, add_le_add le_rfl hv.2⟩, rfl⟩
    simp only [g, f] at this ⊢; linarith
  have hgr : ∀ s, ContinuousWithinAt g (Ici s) s := by
    intro s
    have h1 : ContinuousWithinAt (fun v : ℝ≥0 => X.X (u + v) ω) (Ici s) s :=
      (X.rightCont ω (u + s)).comp (continuous_const.add continuous_id).continuousWithinAt
        (fun v hv => by simp only [mem_Ici] at hv ⊢; exact add_le_add le_rfl hv)
    exact h1.sub continuousWithinAt_const
  set G : ℝ≥0 → ℝ := fun r => sSup (g '' Icc 0 r) with hG
  have hG0 : G 0 = 0 := by
    simp [G, g]
  have hGnn : ∀ r, 0 ≤ G r := fun r => hG0 ▸ runSup_mono g hgb (zero_le : (0 : ℝ≥0) ≤ r)
  set M : ℝ≥0 → ℝ := fun r => sSup (f '' Icc 0 r) with hM
  have hB : ∀ s, barrierStrategy X x a s ω = if s = 0 then 0 else max 0 (x - a + M s) := by
    intro s; simp only [barrierStrategy, M, f, sSup_image']
  have hM0 : M 0 = 0 := by simp [M, f, X.X_zero ω]
  have hBy : ∀ y, barrierStrategy X x a y ω = max 0 (x - a + M y) := by
    intro y; rw [hB]; split_ifs with h
    · subst h; rw [hM0]; simp [hxa]
    · rfl
  have hBrc : ∀ y, Tendsto (fun s => barrierStrategy X x a s ω) (𝓝[>] y)
      (𝓝 (barrierStrategy X x a y ω)) := by
    intro y
    rw [hBy]
    have : Tendsto (fun s => max 0 (x - a + M s)) (𝓝[>] y) (𝓝 (max 0 (x - a + M y))) :=
      tendsto_const_nhds.max ((runSup_rc f hbdd (X.rightCont ω) y).const_add (x - a))
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hBy s).symm
  have hBmono : Monotone (fun s => barrierStrategy X x a s ω) := by
    intro s s' h
    simp only [hBy]
    exact max_le_max le_rfl (add_le_add le_rfl (runSup_mono f hbdd h))
  have hφ : Monotone (fun s : ℝ => barrierStrategy X x a s.toNNReal ω) :=
    hBmono.comp (fun _ _ h => Real.toNNReal_le_toNNReal h)
  have hψ : Monotone (fun s : ℝ => G s.toNNReal) :=
    (runSup_mono g hgb).comp (fun _ _ h => Real.toNNReal_le_toNNReal h)
  have rlφ : ∀ y : ℝ≥0, Function.rightLim (fun s : ℝ => barrierStrategy X x a s.toNNReal ω) y =
      barrierStrategy X x a y ω := by
    intro y
    apply rightLim_eq_of_tendsto
    have := (hBrc y).comp (by simpa using tendsto_toNNReal_nhdsGT (y := (y : ℝ)) y.2 :
      Tendsto Real.toNNReal (𝓝[>] (y : ℝ)) (𝓝[>] y))
    exact this
  have rlψ : ∀ y : ℝ≥0, Function.rightLim (fun s : ℝ => G s.toNNReal) y = G y := by
    intro y
    apply rightLim_eq_of_tendsto
    have := (runSup_rc g hgb hgr y).comp (by simpa using tendsto_toNNReal_nhdsGT (y := (y : ℝ)) y.2 :
      Tendsto Real.toNNReal (𝓝[>] (y : ℝ)) (𝓝[>] y))
    exact this
  simp only [dividendMeasure]
  rw [dif_pos hφ, dif_pos (show Monotone (fun s : ℝ => G s.toNNReal) from hψ),
    StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc, Monotone.stieltjesFunction_eq,
    Monotone.stieltjesFunction_eq, Monotone.stieltjesFunction_eq, Monotone.stieltjesFunction_eq,
    rlφ, rlφ]
  rw [show ((0 : ℝ)) = ((0 : ℝ≥0) : ℝ) by simp, rlψ, rlψ, hG0, sub_zero, hshift t le_rfl,
    max_eq_right (hGnn t)]
