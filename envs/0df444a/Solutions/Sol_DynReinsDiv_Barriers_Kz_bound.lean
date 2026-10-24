-- Prove2me | solution 1 for DynReinsDiv.Barriers.Kz_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:05:51.262091+00:00
-- url     : https://prove2.me/submissions/89141090-30a3-4b7c-829d-3bf2694474c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DynReinsDiv_Barriers_Model
import Definitions.Def_DynReinsDiv_Barriers_Boundaries
import Theorems.Thm_DynReinsDiv_Barriers_lemma_4_3
import Theorems.Thm_DynReinsDiv_Barriers_lemma_4_4

namespace DRD45Aux

open Set Filter Topology

/-- If `f(·, t)` has derivative `f'(·, t)` for `t < T`, and `f, f'` are jointly continuous up to
`t = T`, then `f(·, T)` has derivative `f'(·, T)`. -/
lemma hasDerivAt_limit {T : ℝ} (hT : 0 < T) {f f' : ℝ → ℝ → ℝ}
    (hcf : ContinuousOn (Function.uncurry f) (Ioi 0 ×ˢ Icc 0 T))
    (hcf' : ContinuousOn (Function.uncurry f') (Ioi 0 ×ˢ Icc 0 T))
    (hd : ∀ x t : ℝ, 0 < x → 0 < t → t < T → HasDerivAt (fun y => f y t) (f' x t) x)
    {x : ℝ} (hx : 0 < x) : HasDerivAt (fun y => f y T) (f' x T) x := by
  set l : Filter ℝ := 𝓝[Ioo (T/2) T] T with hl
  have : l.NeBot := by
    rw [hl, ← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by linarith)]
    exact ⟨by linarith, le_rfl⟩
  have hcomp : ∀ (g : ℝ → ℝ → ℝ), ContinuousOn (Function.uncurry g) (Ioi 0 ×ˢ Icc 0 T) →
      ∀ K : Set ℝ, K ⊆ Ioi 0 → IsCompact K →
      TendstoUniformlyOn (fun n y => g y n) (fun y => g y T) l K := by
    intro g hg K hK hKc
    have hUC : UniformContinuousOn (Function.uncurry (fun n y => g y n)) (Icc (T/2) T ×ˢ K) := by
      apply IsCompact.uniformContinuousOn_of_continuous (isCompact_Icc.prod hKc)
      have : Function.uncurry (fun n y => g y n) = Function.uncurry g ∘ Prod.swap := by
        ext p; rfl
      rw [this]
      refine hg.comp continuous_swap.continuousOn ?_
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      simp only [mem_Icc] at ha
      exact ⟨hK hb, ⟨by simp; linarith [ha.1], by simpa using ha.2⟩⟩
    have := UniformContinuousOn.tendstoUniformlyOn (F := fun n y => g y n) hUC
      (show T ∈ Icc (T/2) T from ⟨by linarith, le_rfl⟩)
    exact fun u hu => (this u hu).filter_mono (nhdsWithin_mono _ Ioo_subset_Icc_self)
  have hpt : ∀ (g : ℝ → ℝ → ℝ), ContinuousOn (Function.uncurry g) (Ioi 0 ×ˢ Icc 0 T) →
      ∀ y ∈ Ioi (0:ℝ), Tendsto (fun n => g y n) l (𝓝 (g y T)) := by
    intro g hg y hy
    have h1 := hg (y, T) ⟨hy, ⟨hT.le, le_rfl⟩⟩
    have h2 : Tendsto (fun n : ℝ => (y, n)) l (𝓝[Ioi 0 ×ˢ Icc 0 T] (y, T)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (Continuous.prodMk continuous_const continuous_id).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with n hn
        exact ⟨hy, ⟨by linarith [hn.1], hn.2.le⟩⟩
    exact h1.tendsto.comp h2
  refine hasDerivAt_of_tendstoLocallyUniformlyOn (l := l) (f := fun n y => f y n)
    (f' := fun n y => f' y n) (g := fun y => f y T) (g' := fun y => f' y T) isOpen_Ioi ?_ ?_
    (hpt f hcf) hx
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi]
    intro K hK hKc
    exact hcomp f' hcf' K hK hKc
  · filter_upwards [self_mem_nhdsWithin] with n hn y hy
    exact hd y n hy (by linarith [hn.1]) hn.2

end DRD45Aux

namespace DRD45Aux

open Set Filter Topology DynReinsDiv.Barriers

section
variable (M : Model) (v vx vxx vt : ℝ → ℝ → ℝ)

lemma slice_cont {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) ((Ici 0 ×ˢ Icc 0 M.T) \ {((0 : ℝ), (0 : ℝ))}))
    {τ : ℝ} (hτ : 0 < τ) (hτT : τ ≤ M.T) : ContinuousOn (fun y => F y τ) (Ici 0) := by
  have : (fun y => F y τ) = Function.uncurry F ∘ (fun y => (y, τ)) := rfl
  rw [this]
  refine hF.comp (Continuous.prodMk continuous_id continuous_const).continuousOn ?_
  intro y hy
  refine ⟨⟨hy, ⟨hτ.le, hτT⟩⟩, ?_⟩
  simp only [mem_singleton_iff, Prod.mk.injEq, not_and]
  intro _; exact hτ.ne'

lemma open_cont {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (Function.uncurry F) ((Ici 0 ×ˢ Icc 0 M.T) \ {((0 : ℝ), (0 : ℝ))})) :
    ContinuousOn (Function.uncurry F) (Ioi 0 ×ˢ Icc 0 M.T) := by
  refine hF.mono ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  refine ⟨⟨show (0:ℝ) ≤ a from le_of_lt ha, hb⟩, ?_⟩
  simp only [mem_singleton_iff, Prod.mk.injEq, not_and]
  intro h; exact absurd h (ne_of_gt ha)

variable {M v vx vxx vt}

lemma vx_deriv (hv : M.IsTheorem31Solution v vx vxx vt) :
    ∀ x τ : ℝ, 0 < x → 0 < τ → τ ≤ M.T → HasDerivAt (fun y => vx y τ) (vxx x τ) x := by
  obtain ⟨⟨_, hcvx, hcvxx, _, hder⟩, _, _⟩ := hv
  intro x τ hx hτ hτT
  rcases lt_or_eq_of_le hτT with h | rfl
  · exact (hder x τ hx hτ h).2.1
  · exact hasDerivAt_limit M.T_pos (open_cont M hcvx) (open_cont M hcvxx)
      (fun x t hx ht htT => (hder x t hx ht htT).2.1) hx

lemma vx_antitone (hv : M.IsTheorem31Solution v vx vxx vt) :
    ∀ τ : ℝ, 0 < τ → τ ≤ M.T → AntitoneOn (fun y => vx y τ) (Ioi 0) := by
  intro τ hτ hτT
  have hd := vx_deriv hv
  have hneg := hv.2.2.2.2.1
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro y hy; exact (hd y τ hy hτ hτT).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro y hy; exact (hd y τ hy hτ hτT).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]; intro y hy; rw [(hd y τ hy hτ hτT).deriv]; exact hneg y τ hy hτ hτT

lemma ND_nhds (hv : M.IsTheorem31Solution v vx vxx vt) :
    ∀ p ∈ NDset M.T vx, NDset M.T vx ∈ 𝓝[univ ×ˢ Icc 0 M.T] p := by
  rintro ⟨x, τ⟩ ⟨hx, hτ, hτT, h1⟩
  have hc := open_cont M hv.1.2.1
  have hcw : ContinuousWithinAt (Function.uncurry vx) (Ioi 0 ×ˢ Icc 0 M.T) (x, τ) :=
    hc _ ⟨hx, ⟨hτ.le, hτT⟩⟩
  have hgt : {q : ℝ × ℝ | 1 < vx q.1 q.2} ∈ 𝓝[Ioi 0 ×ˢ Icc 0 M.T] (x, τ) :=
    hcw (Ioi_mem_nhds h1)
  rw [mem_nhdsWithin] at hgt
  obtain ⟨u, hu, hxu, hsub⟩ := hgt
  rw [mem_nhdsWithin]
  refine ⟨u ∩ (Ioi 0 ×ˢ Ioi 0), hu.inter (isOpen_Ioi.prod isOpen_Ioi), ⟨hxu, ⟨hx, hτ⟩⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨⟨hau, ⟨ha, hb⟩⟩, ⟨_, hbT⟩⟩
  have := hsub ⟨hau, ⟨ha, hbT⟩⟩
  exact ⟨ha, hb, hbT.2, this⟩

lemma ND_box (hv : M.IsTheorem31Solution v vx vxx vt) {x0 τ0 : ℝ}
    (hp : (x0, τ0) ∈ NDset M.T vx) :
    ∃ ρ > 0, ∀ x σ, |x - x0| < ρ → |σ - τ0| < ρ → σ ∈ Icc 0 M.T → (x, σ) ∈ NDset M.T vx := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.1 (ND_nhds hv _ hp)
  refine ⟨ρ, hρ, fun x σ hx hσ hσT => hball ⟨?_, ⟨mem_univ _, hσT⟩⟩⟩
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_lt hx hσ

/-- Structure of a time slice: `{v_x = 1}` starts at `d(τ)`. -/
lemma slice_struct (hv : M.IsTheorem31Solution v vx vxx vt) {τ : ℝ} (hτ : 0 < τ)
    (hτT : τ ≤ M.T) (hne : {x : ℝ | 0 ≤ x ∧ vx x τ = 1}.Nonempty)
    (hdpos : 0 < dBoundary vx τ) :
    vx (dBoundary vx τ) τ = 1 ∧
    (∀ x, dBoundary vx τ ≤ x → vx x τ = 1 ∧ vxx x τ = 0) ∧
    (∀ x, 0 < x → x < dBoundary vx τ → 1 < vx x τ) := by
  set d := dBoundary vx τ with hd
  have hge : ∀ x, 0 < x → 1 ≤ vx x τ := fun x hx => hv.2.2.1 x τ hx hτ hτT
  have hclosed : IsClosed {x : ℝ | 0 ≤ x ∧ vx x τ = 1} := by
    have := (slice_cont M hv.1.2.1 hτ hτT).preimage_isClosed_of_isClosed isClosed_Ici
      (isClosed_singleton (x := (1:ℝ)))
    convert this using 1
    ext x; simp [mem_Ici]
  have hbdd : BddBelow {x : ℝ | 0 ≤ x ∧ vx x τ = 1} := ⟨0, fun x hx => hx.1⟩
  have hdmem : d ∈ {x : ℝ | 0 ≤ x ∧ vx x τ = 1} := hclosed.csInf_mem hne hbdd
  have hanti := vx_antitone hv τ hτ hτT
  have hone : ∀ x, d ≤ x → vx x τ = 1 := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hdpos hx
    have := hanti hdpos hxpos hx
    simp only at this
    linarith [hge x hxpos, hdmem.2]
  refine ⟨hdmem.2, fun x hx => ⟨hone x hx, ?_⟩, ?_⟩
  · have hxpos : 0 < x := lt_of_lt_of_le hdpos hx
    have hmin : IsLocalMin (fun y => vx y τ) x := by
      filter_upwards [Ioi_mem_nhds hxpos] with y hy
      simp only [hone x hx]
      exact hge y hy
    exact hmin.hasDerivAt_eq_zero (vx_deriv hv x τ hxpos hτ hτT)
  · intro x hx hxd
    rcases lt_or_eq_of_le (hge x hx) with h | h
    · exact h
    · exfalso
      have : d ≤ x := csInf_le hbdd ⟨hx.le, h.symm⟩
      linarith

end

end DRD45Aux

open Set Filter Topology DynReinsDiv.Barriers DRD45Aux

theorem solution (M : Model) (v vx vxx vt : ℝ → ℝ → ℝ)
    (hv : M.IsTheorem31Solution v vx vxx vt) (lam : ℝ) (hlam : 0 < lam) (hf : M.fA lam = 0)
    (z : ℝ) (hz : 1 / lam < z) :
    ∀ τ ∈ Set.Ioc 0 M.T, Kz vx vxx z τ ≤ z / (2 * M.c) - 1 / (2 * M.c * lam) := by
  intro τ hτ
  obtain ⟨-, hneg43, -⟩ := lemma_4_3 M v vx vxx vt hv
  obtain ⟨h48, -, h410⟩ := lemma_4_4 M v vx vxx vt hv lam hlam hf
  have hc := M.c_pos
  have hlam' : 0 < 1 / lam := by positivity
  have hzpos : 0 < z := lt_trans hlam' hz
  have hbd : z / (2 * M.c) - 1 / (2 * M.c * lam) = (z - 1 / lam) / (2 * M.c) := by
    field_simp
  rw [hbd]
  unfold Kz
  apply Real.sSup_le _ (div_nonneg (by linarith) (by positivity))
  rintro x ⟨hx, hr⟩
  have hP1 : ∀ y, 0 < y → 1 ≤ vx y τ := fun y hy => hv.2.2.1 y τ hy hτ.1 hτ.2
  -- the point lies in 𝒩𝒟
  have hxND : 1 < vx x τ := by
    rcases lt_or_eq_of_le (hP1 x hx) with h | h
    · exact h
    · exfalso
      have hmin : IsLocalMin (fun y => vx y τ) x := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        simp only [← h]
        exact hP1 y hy
      have h0 := hmin.hasDerivAt_eq_zero (vx_deriv hv x τ hx hτ.1 hτ.2)
      rw [h0, neg_zero, zero_div] at hr
      linarith [show 0 < 1 / z from by positivity]
  have hanti := vx_antitone hv τ hτ.1 hτ.2
  have hND : ∀ y, 0 < y → y ≤ x → (y, τ) ∈ NDset M.T vx := by
    intro y hy hyx
    have := hanti hy hx hyx
    simp only at this
    exact ⟨hy, hτ.1, hτ.2, lt_of_lt_of_le hxND this⟩
  have hQ0 : vxx 0 τ ≠ 0 := by
    intro h; have := h48 τ hτ.1 hτ.2; rw [h, div_zero] at this; exact hlam'.ne' this.symm
  have hQne : ∀ y ∈ Icc 0 x, vxx y τ ≠ 0 := by
    intro y hy
    rcases lt_or_eq_of_le hy.1 with h | h
    · exact (hneg43 (y, τ) (hND y h hy.2)).ne
    · rw [← h]; exact hQ0
  set g : ℝ → ℝ := fun y => -vx y τ / vxx y τ with hg
  have hcont : ContinuousOn g (Icc 0 x) := by
    have hsub : Icc 0 x ⊆ Ici 0 := fun y hy => hy.1
    exact (((slice_cont M hv.1.2.1 hτ.1 hτ.2).mono hsub).neg).div
      ((slice_cont M hv.1.2.2.1 hτ.1 hτ.2).mono hsub) hQne
  have hd : ∀ y ∈ Ioo 0 x, HasDerivAt g (deriv g y) y := by
    intro y hy
    obtain ⟨g', hg', _⟩ := h410 (y, τ) (hND y hy.1 hy.2.le)
    exact hg'.differentiableAt.hasDerivAt
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope g (deriv g) hx hcont hd
  obtain ⟨g', hg', hg'c⟩ := h410 (ξ, τ) (hND ξ hξ.1 hξ.2.le)
  simp only at hg' hg'c
  rw [hg'.deriv, sub_zero] at hslope
  have hg0 : g 0 = 1 / lam := h48 τ hτ.1 hτ.2
  have hgx : g x < z := by
    have hPx : 0 < vx x τ := by linarith
    have hQx : 0 < -vxx x τ := neg_pos.2 (hneg43 (x, τ) (hND x hx le_rfl))
    change -vx x τ / vxx x τ < z
    rw [gt_iff_lt, div_lt_div_iff₀ hzpos hPx] at hr
    rw [neg_div, ← div_neg, div_lt_iff₀ hQx]
    linarith
  have h2 : 2 * M.c * x ≤ g x - g 0 := by
    rw [eq_div_iff hx.ne'] at hslope
    rw [← hslope]
    exact mul_le_mul_of_nonneg_right hg'c hx.le
  rw [hg0] at h2
  rw [le_div_iff₀ (by positivity)]
  linarith
