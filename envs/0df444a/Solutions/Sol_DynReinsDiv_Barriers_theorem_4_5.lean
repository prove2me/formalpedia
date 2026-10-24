-- Prove2me | solution 1 for DynReinsDiv.Barriers.theorem_4_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:01:54.515837+00:00
-- url     : https://prove2.me/submissions/8fad5012-e96b-4f47-b87f-3bea9260a1fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DynReinsDiv_Barriers_Model
import Definitions.Def_DynReinsDiv_Barriers_Boundaries
import Definitions.Def_DynReinsDiv_Barriers_Discrete
import Theorems.Thm_DynReinsDiv_Barriers_theorem_4_2
import Theorems.Thm_DynReinsDiv_Barriers_lemma_4_3
import Theorems.Thm_DynReinsDiv_Barriers_lemma_4_4
import Theorems.Thm_DynReinsDiv_Barriers_lemma_4_4_strict

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

open Set Filter Topology

/-- Mean value theorem on an unordered segment. -/
lemma mvt_seg {φ φ' : ℝ → ℝ} {a b : ℝ} (hc : ContinuousOn φ (uIcc a b))
    (hd : ∀ t, min a b < t → t < max a b → HasDerivAt φ (φ' t) t) :
    ∃ t ∈ uIcc a b, φ b - φ a = φ' t * (b - a) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · have hc' : ContinuousOn φ (Icc a b) := by rwa [uIcc_of_le hab.le] at hc
    obtain ⟨t, ht, h⟩ := exists_hasDerivAt_eq_slope φ φ' hab hc'
      (fun t ht => hd t (by rw [min_eq_left hab.le]; exact ht.1)
        (by rw [max_eq_right hab.le]; exact ht.2))
    refine ⟨t, by rw [uIcc_of_le hab.le]; exact Ioo_subset_Icc_self ht, ?_⟩
    rw [h]; field_simp [sub_ne_zero.2 hab.ne']
  · exact ⟨a, left_mem_uIcc, by ring⟩
  · have hc' : ContinuousOn φ (Icc b a) := by rwa [uIcc_of_ge hab.le] at hc
    obtain ⟨t, ht, h⟩ := exists_hasDerivAt_eq_slope φ φ' hab hc'
      (fun t ht => hd t (by rw [min_eq_right hab.le]; exact ht.1)
        (by rw [max_eq_left hab.le]; exact ht.2))
    refine ⟨t, by rw [uIcc_of_ge hab.le]; exact Ioo_subset_Icc_self ht, ?_⟩
    rw [h]; field_simp [sub_ne_zero.2 hab.ne']; ring

lemma abs_sub_lt_of_mem_uIcc {a b t ε : ℝ} (ht : t ∈ uIcc a b) (hb : |b - a| < ε) :
    |t - a| < ε := by
  rcases le_total a b with h | h
  · rw [uIcc_of_le h] at ht
    rw [abs_lt] at hb ⊢; constructor <;> linarith [ht.1, ht.2]
  · rw [uIcc_of_ge h] at ht
    rw [abs_lt] at hb ⊢; constructor <;> linarith [ht.1, ht.2]

lemma uIcc_subset_Icc_of {a b T : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) :
    uIcc a b ⊆ Icc 0 T := (ordConnected_Icc).uIcc_subset ha hb

/-- Schwarz/Clairaut-type lemma: if `∂_x f = fx`, `∂_τ f = ft` (within `[0,T]`), and
`∂_x ft = ftx` exists near `(x0, τ0)` and is continuous at `(x0, τ0)`, then
`∂_τ fx (x0, τ0) = ftx (x0, τ0)` (within `[0, T]`). -/
lemma schwarz {T : ℝ} {f fx ft ftx : ℝ → ℝ → ℝ} {x0 τ0 ε : ℝ} (hε : 0 < ε)
    (hτ0 : τ0 ∈ Icc 0 T)
    (hfx : ∀ x σ, |x - x0| < ε → |σ - τ0| < ε → σ ∈ Icc 0 T →
      HasDerivAt (fun y => f y σ) (fx x σ) x)
    (hft : ∀ x σ, |x - x0| < ε → |σ - τ0| < ε → σ ∈ Icc 0 T →
      HasDerivWithinAt (fun s => f x s) (ft x σ) (Icc 0 T) σ)
    (hftx : ∀ x σ, |x - x0| < ε → |σ - τ0| < ε → σ ∈ Icc 0 T →
      HasDerivAt (fun y => ft y σ) (ftx x σ) x)
    (hcont : ContinuousWithinAt (Function.uncurry ftx) (univ ×ˢ Icc 0 T) (x0, τ0)) :
    HasDerivWithinAt (fun s => fx x0 s) (ftx x0 τ0) (Icc 0 T) τ0 := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro η hη
  obtain ⟨δ0, hδ0, hδ0'⟩ := Metric.continuousWithinAt_iff.1 hcont η hη
  set δ := min δ0 ε with hδ
  have hδpos : 0 < δ := lt_min hδ0 hε
  have hδε : δ ≤ ε := min_le_right _ _
  have hδδ0 : δ ≤ δ0 := min_le_left _ _
  have hbound : ∀ x σ, |x - x0| < δ → |σ - τ0| < δ → σ ∈ Icc 0 T →
      |ftx x σ - ftx x0 τ0| ≤ η := by
    intro x σ hx hσ hσT
    have := hδ0' (x := (x, σ)) ⟨mem_univ _, hσT⟩ (by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_lt (lt_of_lt_of_le hx hδδ0) (lt_of_lt_of_le hσ hδδ0))
    rw [Real.dist_eq] at this
    exact this.le
  have hev : ∀ᶠ σ in 𝓝[Icc 0 T] τ0, σ ∈ Icc 0 T ∧ |σ - τ0| < δ := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds τ0 hδpos)] with σ h1 h2
    exact ⟨h1, by simpa [Metric.mem_ball, Real.dist_eq] using h2⟩
  filter_upwards [hev] with σ ⟨hσT, hσ⟩
  simp only [smul_eq_mul, Real.norm_eq_abs]
  -- key estimate for `y ≠ x0` close to `x0`
  have hkey : ∀ y, |y - x0| < δ → y ≠ x0 →
      |(f y σ - f x0 σ) / (y - x0) - (f y τ0 - f x0 τ0) / (y - x0) - (σ - τ0) * ftx x0 τ0|
        ≤ η * |σ - τ0| := by
    intro y hy hyne
    have hyx : y - x0 ≠ 0 := sub_ne_zero.2 hyne
    -- MVT in τ for φ(s) = f y s - f x0 s
    have hseg : uIcc τ0 σ ⊆ Icc 0 T := uIcc_subset_Icc_of hτ0 hσT
    have hsegε : ∀ s ∈ uIcc τ0 σ, |s - τ0| < δ := fun s hs => abs_sub_lt_of_mem_uIcc hs hσ
    have hφc : ContinuousOn (fun s => f y s - f x0 s) (uIcc τ0 σ) := by
      intro s hs
      have h1 := (hft y s (lt_of_lt_of_le hy hδε) (lt_of_lt_of_le (hsegε s hs) hδε)
        (hseg hs)).continuousWithinAt
      have h2 := (hft x0 s (by simpa using hε) (lt_of_lt_of_le (hsegε s hs) hδε)
        (hseg hs)).continuousWithinAt
      exact (h1.sub h2).mono hseg
    have hφd : ∀ s, min τ0 σ < s → s < max τ0 σ →
        HasDerivAt (fun s => f y s - f x0 s) (ft y s - ft x0 s) s := by
      intro s hs1 hs2
      have hsI : s ∈ uIcc τ0 σ := ⟨hs1.le, hs2.le⟩
      have hsT := hseg hsI
      have hsIoo : s ∈ Ioo 0 T := by
        constructor
        · exact lt_of_le_of_lt (le_min hτ0.1 hσT.1) hs1
        · exact lt_of_lt_of_le hs2 (max_le hτ0.2 hσT.2)
      have hnhds : Icc 0 T ∈ 𝓝 s := Icc_mem_nhds hsIoo.1 hsIoo.2
      have h1 := (hft y s (lt_of_lt_of_le hy hδε) (lt_of_lt_of_le (hsegε s hsI) hδε)
        hsT).hasDerivAt hnhds
      have h2 := (hft x0 s (by simpa using hε) (lt_of_lt_of_le (hsegε s hsI) hδε)
        hsT).hasDerivAt hnhds
      exact h1.sub h2
    obtain ⟨s, hs, hseq⟩ := mvt_seg hφc hφd
    -- MVT in x for ψ(x) = ft x s
    have hsδ := hsegε s hs
    have hsT := hseg hs
    have hxseg : ∀ x ∈ uIcc x0 y, |x - x0| < δ := fun x hx => abs_sub_lt_of_mem_uIcc hx hy
    have hψc : ContinuousOn (fun x => ft x s) (uIcc x0 y) := by
      intro x hx
      exact (hftx x s (lt_of_lt_of_le (hxseg x hx) hδε) (lt_of_lt_of_le hsδ hδε)
        hsT).continuousAt.continuousWithinAt
    have hψd : ∀ x, min x0 y < x → x < max x0 y → HasDerivAt (fun x => ft x s) (ftx x s) x := by
      intro x h1 h2
      exact hftx x s (lt_of_lt_of_le (hxseg x ⟨h1.le, h2.le⟩) hδε) (lt_of_lt_of_le hsδ hδε) hsT
    obtain ⟨ξ, hξ, hξeq⟩ := mvt_seg hψc hψd
    have hb := hbound ξ s (hxseg ξ hξ) hsδ hsT
    have hexpr : (f y σ - f x0 σ) / (y - x0) - (f y τ0 - f x0 τ0) / (y - x0)
        - (σ - τ0) * ftx x0 τ0 = (σ - τ0) * (ftx ξ s - ftx x0 τ0) := by
      have : (f y σ - f x0 σ) - (f y τ0 - f x0 τ0) = (ftx ξ s * (y - x0)) * (σ - τ0) := by
        rw [← hξeq]; linarith [hseq]
      field_simp
      linear_combination this
    rw [hexpr, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  -- pass to the limit `y → x0`
  have hlim1 := (hasDerivAt_iff_tendsto_slope.1 (hfx x0 σ (by simpa using hε)
    (lt_of_lt_of_le hσ hδε) hσT))
  have hlim2 := (hasDerivAt_iff_tendsto_slope.1 (hfx x0 τ0 (by simpa using hε)
    (by simpa using hε) hτ0))
  have hlim := ((hlim1.sub hlim2).sub_const ((σ - τ0) * ftx x0 τ0)).abs
  refine le_of_tendsto hlim ?_
  have hball : ∀ᶠ y in 𝓝[≠] x0, |y - x0| < δ ∧ y ≠ x0 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Metric.ball_mem_nhds x0 hδpos)] with y h1 h2
    exact ⟨by simpa [Metric.mem_ball, Real.dist_eq] using h2, h1⟩
  filter_upwards [hball] with y ⟨hy, hyne⟩
  have := hkey y hy hyne
  simp only [slope_def_field] at *
  convert this using 2

end DRD45Aux

namespace DRD45Aux

open Set Filter Topology

/-- Implicit-function lemma (one space and one time variable) on a relatively open set `U` of
`ℝ × (0, T]` whose time slices are intervals: if `G (K τ) τ = z` with `(K τ, τ) ∈ U`, the partials
`Gx`, `Gt` exist and are continuous on `U`, and `Gx ≥ c > 0`, then `K` is `C¹` on `(0, T]`. -/
lemma implicit_C1 {T c z : ℝ} (hc : 0 < c) {G Gx Gt : ℝ → ℝ → ℝ} {K : ℝ → ℝ}
    {U : Set (ℝ × ℝ)}
    (hUopen : ∀ p ∈ U, U ∈ 𝓝[univ ×ˢ Ioc 0 T] p)
    (hUconn : ∀ τ a b y, (a, τ) ∈ U → (b, τ) ∈ U → y ∈ uIcc a b → (y, τ) ∈ U)
    (hK : ∀ τ ∈ Ioc 0 T, (K τ, τ) ∈ U ∧ G (K τ) τ = z)
    (hGx : ∀ p ∈ U, HasDerivAt (fun y => G y p.2) (Gx p.1 p.2) p.1)
    (hGt : ∀ p ∈ U, HasDerivWithinAt (fun s => G p.1 s) (Gt p.1 p.2) (Icc 0 T) p.2)
    (hGxc : ContinuousOn (Function.uncurry Gx) U) (hGtc : ContinuousOn (Function.uncurry Gt) U)
    (hGxpos : ∀ p ∈ U, c ≤ Gx p.1 p.2) :
    ContDiffOn ℝ 1 K (Ioc 0 T) := by
  -- neighbourhood radius
  have hnb : ∀ τ0 ∈ Ioc 0 T, ∃ ρ > 0, ∀ x σ, σ ∈ Ioc 0 T → |x - K τ0| < ρ → |σ - τ0| < ρ →
      (x, σ) ∈ U := by
    intro τ0 hτ0
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhdsWithin_iff.1 (hUopen _ (hK τ0 hτ0).1)
    refine ⟨ρ, hρ, fun x σ hσ hx hσ' => hball ⟨?_, ⟨mem_univ _, hσ⟩⟩⟩
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt hx hσ'
  -- MVT in `x` on a slice
  have hmvtx : ∀ σ a b, (a, σ) ∈ U → (b, σ) ∈ U →
      ∃ ξ ∈ uIcc a b, G b σ - G a σ = Gx ξ σ * (b - a) := by
    intro σ a b ha hb
    apply mvt_seg
    · intro y hy
      exact (hGx (y, σ) (hUconn σ a b y ha hb hy)).continuousAt.continuousWithinAt
    · intro y h1 h2
      exact hGx (y, σ) (hUconn σ a b y ha hb ⟨h1.le, h2.le⟩)
  -- MVT in `τ` at fixed `x`
  have hmvtt : ∀ x τ0 σ, τ0 ∈ Ioc 0 T → σ ∈ Ioc 0 T →
      (∀ θ ∈ uIcc τ0 σ, (x, θ) ∈ U) →
      ∃ θ ∈ uIcc τ0 σ, G x σ - G x τ0 = Gt x θ * (σ - τ0) := by
    intro x τ0 σ hτ0 hσ hseg
    have hsub : uIcc τ0 σ ⊆ Icc 0 T :=
      uIcc_subset_Icc_of ⟨hτ0.1.le, hτ0.2⟩ ⟨hσ.1.le, hσ.2⟩
    apply mvt_seg
    · intro θ hθ
      exact ((hGt (x, θ) (hseg θ hθ)).continuousWithinAt).mono hsub
    · intro θ h1 h2
      have hθ : θ ∈ Ioo 0 T := ⟨lt_of_le_of_lt (le_min hτ0.1.le hσ.1.le) h1,
        lt_of_lt_of_le h2 (max_le hτ0.2 hσ.2)⟩
      exact (hGt (x, θ) (hseg θ ⟨h1.le, h2.le⟩)).hasDerivAt (Icc_mem_nhds hθ.1 hθ.2)
  -- continuity of `K`
  have hKcont : ∀ τ0 ∈ Ioc 0 T, ContinuousWithinAt K (Ioc 0 T) τ0 := by
    intro τ0 hτ0
    obtain ⟨ρ, hρ, hU⟩ := hnb τ0 hτ0
    set x0 := K τ0
    have hGc : ContinuousWithinAt (fun s => G x0 s) (Ioc 0 T) τ0 :=
      ((hGt (x0, τ0) (hK τ0 hτ0).1).continuousWithinAt).mono Ioc_subset_Icc_self
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 hGc (c * ε) (mul_pos hc hε)
    refine ⟨min δ ρ, lt_min hδ hρ, fun {σ} hσ hdist => ?_⟩
    rw [Real.dist_eq] at hdist ⊢
    have hσρ : |σ - τ0| < ρ := lt_of_lt_of_le hdist (min_le_right _ _)
    have hx0σ : (x0, σ) ∈ U := hU x0 σ hσ (by simpa using hρ) hσρ
    obtain ⟨ξ, hξ, heq⟩ := hmvtx σ x0 (K σ) hx0σ (hK σ hσ).1
    have hξU := hUconn σ x0 (K σ) ξ hx0σ (hK σ hσ).1 hξ
    have hGxξ := hGxpos _ hξU
    have h1 := hδ' hσ (by rw [Real.dist_eq]; exact lt_of_lt_of_le hdist (min_le_left _ _))
    rw [Real.dist_eq] at h1
    rw [(hK σ hσ).2, ← (hK τ0 hτ0).2] at heq
    -- |K σ - x0| * c ≤ |Gx ξ σ * (K σ - x0)| = |G x0 τ0 - G x0 σ| < c ε
    have : c * |K σ - x0| ≤ |G x0 σ - G x0 τ0| := by
      rw [abs_sub_comm (G x0 σ), heq, abs_mul]
      exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans' hGxξ) (abs_nonneg _)
    by_contra hcon
    push Not at hcon
    nlinarith
  -- the derivative
  set D : ℝ → ℝ := fun τ => -Gt (K τ) τ / Gx (K τ) τ with hD
  have hderiv : ∀ τ0 ∈ Ioc 0 T, HasDerivWithinAt K (D τ0) (Ioc 0 T) τ0 := by
    intro τ0 hτ0
    obtain ⟨ρ, hρ, hU⟩ := hnb τ0 hτ0
    set x0 := K τ0 with hx0
    have hp0 : (x0, τ0) ∈ U := (hK τ0 hτ0).1
    have hGx0 : c ≤ Gx x0 τ0 := hGxpos _ hp0
    rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro η hη
    -- continuity of the quotient
    have hq : ContinuousAt (fun p : ℝ × ℝ => p.1 / p.2) (Gt x0 τ0, Gx x0 τ0) :=
      continuousAt_fst.div continuousAt_snd (by simp; linarith)
    obtain ⟨κ, hκ, hκ'⟩ := Metric.continuousAt_iff.1 hq η hη
    obtain ⟨ρ1, hρ1, hρ1'⟩ := Metric.continuousWithinAt_iff.1 (hGxc _ hp0) (κ / 2) (by linarith)
    obtain ⟨ρ2, hρ2, hρ2'⟩ := Metric.continuousWithinAt_iff.1 (hGtc _ hp0) (κ / 2) (by linarith)
    set r := min ρ (min ρ1 ρ2) with hr
    have hrpos : 0 < r := lt_min hρ (lt_min hρ1 hρ2)
    have hquot : ∀ a b, (x0, b) ∈ U → |a - x0| < r → |b - τ0| < r → ∀ σ,
        (a, σ) ∈ U → |σ - τ0| < r →
        |Gt x0 b / Gx a σ - Gt x0 τ0 / Gx x0 τ0| < η := by
      intro a b hb ha' hb' σ haσ hσ
      have e1 := hρ1' (x := (a, σ)) haσ (by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        exact max_lt (lt_of_lt_of_le ha' (le_trans (min_le_right _ _) (min_le_left _ _)))
          (lt_of_lt_of_le hσ (le_trans (min_le_right _ _) (min_le_left _ _))))
      have e2 := hρ2' (x := (x0, b)) hb (by
        rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        simp only [sub_self, abs_zero]
        exact max_lt hρ2 (lt_of_lt_of_le hb' (le_trans (min_le_right _ _) (min_le_right _ _))))
      have := hκ' (x := (Gt x0 b, Gx a σ)) (by
        rw [Prod.dist_eq]
        simp only [Function.uncurry_apply_pair] at e1 e2
        exact max_lt (by linarith) (by linarith))
      simpa [Real.dist_eq] using this
    have hev : ∀ᶠ σ in 𝓝[Ioc 0 T] τ0, σ ∈ Ioc 0 T ∧ |σ - τ0| < r ∧ |K σ - x0| < r := by
      have hKt := hKcont τ0 hτ0
      have h3 : ∀ᶠ σ in 𝓝[Ioc 0 T] τ0, |K σ - x0| < r := by
        have := Metric.tendsto_nhds.1 hKt r hrpos
        filter_upwards [this] with σ hσ
        simpa [Real.dist_eq] using hσ
      filter_upwards [self_mem_nhdsWithin, h3,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds τ0 hrpos)] with σ h1 h3 h2
      exact ⟨h1, by simpa [Metric.mem_ball, Real.dist_eq] using h2, h3⟩
    filter_upwards [hev] with σ ⟨hσ, hστ, hKσ⟩
    simp only [smul_eq_mul, Real.norm_eq_abs]
    have hrρ : r ≤ ρ := min_le_left _ _
    have hx0σ : (x0, σ) ∈ U := hU x0 σ hσ (by simpa using hρ) (lt_of_lt_of_le hστ hrρ)
    obtain ⟨ξ, hξ, heqx⟩ := hmvtx σ x0 (K σ) hx0σ (hK σ hσ).1
    have hξU := hUconn σ x0 (K σ) ξ hx0σ (hK σ hσ).1 hξ
    have hseg : ∀ θ ∈ uIcc τ0 σ, (x0, θ) ∈ U := by
      intro θ hθ
      have hθT : θ ∈ Ioc 0 T := by
        rcases le_total τ0 σ with h | h
        · rw [uIcc_of_le h] at hθ; exact ⟨lt_of_lt_of_le hτ0.1 hθ.1, le_trans hθ.2 hσ.2⟩
        · rw [uIcc_of_ge h] at hθ; exact ⟨lt_of_lt_of_le hσ.1 hθ.1, le_trans hθ.2 hτ0.2⟩
      exact hU x0 θ hθT (by simpa using hρ)
        (lt_of_lt_of_le (abs_sub_lt_of_mem_uIcc hθ hστ) hrρ)
    obtain ⟨θ, hθ, heqt⟩ := hmvtt x0 τ0 σ hτ0 hσ hseg
    have hθU := hseg θ hθ
    have hGxξ : c ≤ Gx ξ σ := hGxpos _ hξU
    have hGxξne : Gx ξ σ ≠ 0 := by intro h; rw [h] at hGxξ; linarith
    have hGx0ne : Gx x0 τ0 ≠ 0 := by intro h; rw [h] at hGx0; linarith
    rw [(hK σ hσ).2, ← (hK τ0 hτ0).2] at heqx
    -- K σ - x0 = - Gt x0 θ (σ - τ0) / Gx ξ σ
    have hKexp : K σ - x0 = -(Gt x0 θ / Gx ξ σ) * (σ - τ0) := by
      field_simp
      linear_combination -heqx - heqt
    have hξx0 : |ξ - x0| < r := abs_sub_lt_of_mem_uIcc hξ hKσ
    have hθτ0 : |θ - τ0| < r := abs_sub_lt_of_mem_uIcc hθ hστ
    have hqb := hquot ξ θ hθU hξx0 hθτ0 σ hξU hστ
    · have : K σ - K τ0 - (σ - τ0) * D τ0 =
          (σ - τ0) * (-(Gt x0 θ / Gx ξ σ - Gt x0 τ0 / Gx x0 τ0)) := by
        rw [← hx0, hKexp, hD]; simp only; rw [← hx0]; ring
      rw [this, abs_mul, abs_neg, mul_comm]
      exact mul_le_mul_of_nonneg_right hqb.le (abs_nonneg _)
  have hKc : ContinuousOn K (Ioc 0 T) := fun τ hτ => hKcont τ hτ
  have hmaps : MapsTo (fun τ => (K τ, τ)) (Ioc 0 T) U := fun τ hτ => (hK τ hτ).1
  have hpc : ContinuousOn (fun τ => (K τ, τ)) (Ioc 0 T) := hKc.prodMk continuousOn_id
  have hDc : ContinuousOn D (Ioc 0 T) := by
    have h1 : ContinuousOn (fun τ => Gt (K τ) τ) (Ioc 0 T) := hGtc.comp hpc hmaps
    have h2 : ContinuousOn (fun τ => Gx (K τ) τ) (Ioc 0 T) := hGxc.comp hpc hmaps
    exact h1.neg.div h2 (fun τ hτ => by
      have := hGxpos _ (hK τ hτ).1; intro h; simp only at h this; rw [h] at this; linarith)
  rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ioc 0 T)]
  refine ⟨fun τ hτ => (hderiv τ hτ).differentiableWithinAt, ?_⟩
  refine hDc.congr (fun τ hτ => ?_)
  exact (hderiv τ hτ).derivWithin ((uniqueDiffOn_Ioc 0 T) τ hτ)

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

namespace DRD45Aux

open Set Filter Topology DynReinsDiv.Barriers

/-- Strict growth of `g = −v_x/v_xx` on `[0, d)` from `g' > 2c` on `(0, d)`. -/
lemma g_strict {P Q : ℝ → ℝ} {d c : ℝ}
    (hP : ContinuousOn P (Ici 0)) (hQ : ContinuousOn Q (Ici 0))
    (hQne : ∀ x, 0 ≤ x → x < d → Q x ≠ 0)
    (hder : ∀ x, 0 < x → x < d → ∃ g', HasDerivAt (fun y => -P y / Q y) g' x ∧ 2 * c < g') :
    ∀ a b, 0 ≤ a → a < b → b < d → 2 * c * (b - a) < (-P b / Q b) - (-P a / Q a) := by
  intro a b ha hab hbd
  set g : ℝ → ℝ := fun y => -P y / Q y with hg
  have hcont : ContinuousOn g (Icc a b) := by
    have hsub : Icc a b ⊆ Ici 0 := fun y hy => le_trans ha hy.1
    exact ((hP.mono hsub).neg).div (hQ.mono hsub)
      (fun y hy => hQne y (le_trans ha hy.1) (lt_of_le_of_lt hy.2 hbd))
  have hd : ∀ y ∈ Ioo a b, HasDerivAt g (deriv g y) y := by
    intro y hy
    obtain ⟨g', hg', _⟩ := hder y (lt_of_le_of_lt ha hy.1) (lt_trans hy.2 hbd)
    exact hg'.differentiableAt.hasDerivAt
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope g (deriv g) hab hcont hd
  obtain ⟨g', hg', hg'c⟩ := hder ξ (lt_of_le_of_lt ha hξ.1) (lt_trans hξ.2 hbd)
  rw [hg'.deriv] at hslope
  have hba : 0 < b - a := sub_pos.2 hab
  rw [eq_div_iff hba.ne'] at hslope
  change 2 * c * (b - a) < g b - g a
  rw [← hslope]
  exact mul_lt_mul_of_pos_right hg'c hba

/-- Characterisation of `K_j(τ)` on a slice, for `z > 1/λ`. -/
lemma Kinf_char {P Q : ℝ → ℝ} {d c lam z : ℝ} (hc : 0 < c) (hd : 0 < d) (hlam : 0 < lam)
    (hz : 1 / lam < z)
    (hP : ContinuousOn P (Ici 0)) (hQ : ContinuousOn Q (Ici 0))
    (hP1 : ∀ x, 0 < x → 1 ≤ P x)
    (hQneg : ∀ x, 0 < x → x < d → Q x < 0)
    (hPd : P d = 1) (hQd : Q d = 0)
    (h48 : -P 0 / Q 0 = 1 / lam)
    (hder : ∀ x, 0 < x → x < d → ∃ g', HasDerivAt (fun y => -P y / Q y) g' x ∧ 2 * c < g') :
    0 < sInf {x : ℝ | 0 < x ∧ -Q x / P x ≤ 1 / z} ∧
    sInf {x : ℝ | 0 < x ∧ -Q x / P x ≤ 1 / z} < d ∧
    -P (sInf {x : ℝ | 0 < x ∧ -Q x / P x ≤ 1 / z}) / Q (sInf {x : ℝ | 0 < x ∧ -Q x / P x ≤ 1 / z})
      = z := by
  have hlam' : 0 < 1 / lam := by positivity
  have hzpos : 0 < z := lt_trans hlam' hz
  have hQ0 : Q 0 ≠ 0 := by
    intro h; rw [h, div_zero] at h48; exact hlam'.ne' h48.symm
  have hQne : ∀ x, 0 ≤ x → x < d → Q x ≠ 0 := by
    intro x hx hxd
    rcases lt_or_eq_of_le hx with h | h
    · exact (hQneg x h hxd).ne
    · rw [← h]; exact hQ0
  have hgs := g_strict hP hQ hQne hder
  -- r is small near d
  have hrc : ContinuousAt (fun y => -Q y / P y) d := by
    have h1 := (hQ.continuousAt (Ici_mem_nhds hd)).neg
    have h2 := hP.continuousAt (Ici_mem_nhds hd)
    exact h1.div h2 (by rw [hPd]; norm_num)
  have hrd : -Q d / P d = 0 := by rw [hQd]; simp
  have hev : ∀ᶠ y in 𝓝 d, -Q y / P y < 1 / z := by
    have h0 : -Q d / P d < 1 / z := by rw [hrd]; positivity
    exact hrc.eventually (gt_mem_nhds h0)
  obtain ⟨b, hb1, hb2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT hd)).exists
  have hbpos : 0 < b := hb2.1
  have hbd : b < d := hb2.2
  -- g b > z
  have hgb : z < -P b / Q b := by
    have hPb : 0 < P b := lt_of_lt_of_le one_pos (hP1 b hbpos)
    have hQb : 0 < -Q b := neg_pos.2 (hQneg b hbpos hbd)
    rw [div_lt_div_iff₀ hPb hzpos] at hb1
    rw [neg_div, ← div_neg, lt_div_iff₀ hQb]
    linarith
  -- IVT
  have hcont : ContinuousOn (fun y => -P y / Q y) (Icc 0 b) := by
    have hsub : Icc 0 b ⊆ Ici 0 := fun y hy => hy.1
    exact ((hP.mono hsub).neg).div (hQ.mono hsub)
      (fun y hy => hQne y hy.1 (lt_of_le_of_lt hy.2 hbd))
  obtain ⟨K0, hK0, hgK0⟩ := intermediate_value_Icc hbpos.le hcont
    (show z ∈ Icc (-P 0 / Q 0) (-P b / Q b) from ⟨by rw [h48]; exact hz.le, hgb.le⟩)
  simp only at hgK0
  have hK0pos : 0 < K0 := by
    rcases lt_or_eq_of_le hK0.1 with h | h
    · exact h
    · exfalso; rw [← h, h48] at hgK0; linarith
  have hK0d : K0 < d := lt_of_le_of_lt hK0.2 hbd
  -- r = 1/g on (0,d)
  have hr_iff : ∀ y, 0 < y → y < d → (-Q y / P y ≤ 1 / z ↔ z ≤ -P y / Q y) := by
    intro y hy hyd
    have hPy : 0 < P y := lt_of_lt_of_le one_pos (hP1 y hy)
    have hQy : 0 < -Q y := neg_pos.2 (hQneg y hy hyd)
    rw [div_le_div_iff₀ hPy hzpos, neg_div, ← div_neg, le_div_iff₀ hQy]
    constructor <;> intro h <;> linarith
  have hleast : IsLeast {x : ℝ | 0 < x ∧ -Q x / P x ≤ 1 / z} K0 := by
    refine ⟨⟨hK0pos, (hr_iff K0 hK0pos hK0d).2 hgK0.ge⟩, ?_⟩
    rintro y ⟨hy, hry⟩
    by_contra hlt
    push Not at hlt
    have h1 := (hr_iff y hy (lt_trans hlt hK0d)).1 hry
    have h2 := hgs y K0 hy.le hlt hK0d
    have h3 : 0 < 2 * c * (K0 - y) := by
      have : 0 < K0 - y := sub_pos.2 hlt
      positivity
    rw [hgK0] at h2
    linarith
  rw [hleast.csInf_eq]
  exact ⟨hK0pos, hK0d, hgK0⟩

end DRD45Aux

namespace DRD45Aux

open Set Filter Topology DynReinsDiv.Barriers

/-- Mixed partials on `𝒩𝒟`: `∂_τ v_x = ∂_x v_t` and `∂_τ v_xx = ∂_x ∂_x v_t`. -/
lemma mixed_partials {M : Model} {v vx vxx vt vxxx vxt vtx vtxx vtt : ℝ → ℝ → ℝ}
    (hv : M.IsTheorem31Solution v vx vxx vt)
    (c_vxt : ContinuousOn (Function.uncurry vxt) (NDset M.T vx))
    (c_vtx : ContinuousOn (Function.uncurry vtx) (NDset M.T vx))
    (c_vtxx : ContinuousOn (Function.uncurry vtxx) (NDset M.T vx))
    (hd43 : ∀ p ∈ NDset M.T vx,
        HasDerivAt (fun y => vxx y p.2) (vxxx p.1 p.2) p.1 ∧
        HasDerivWithinAt (fun s => vx p.1 s) (vxt p.1 p.2) (Set.Icc 0 M.T) p.2 ∧
        HasDerivAt (fun y => vt y p.2) (vtx p.1 p.2) p.1 ∧
        HasDerivAt (fun y => vtx y p.2) (vtxx p.1 p.2) p.1 ∧
        HasDerivWithinAt (fun s => vt p.1 s) (vtt p.1 p.2) (Set.Icc 0 M.T) p.2) :
    (∀ p ∈ NDset M.T vx, vxt p.1 p.2 = vtx p.1 p.2) ∧
    (∀ p ∈ NDset M.T vx,
      HasDerivWithinAt (fun s => vxx p.1 s) (vtxx p.1 p.2) (Icc 0 M.T) p.2) := by
  have hT := M.T_pos
  have hder := hv.1.2.2.2.2
  -- step 1: interior times
  have step1 : ∀ x0 τ0, (x0, τ0) ∈ NDset M.T vx → τ0 < M.T → vxt x0 τ0 = vtx x0 τ0 := by
    intro x0 τ0 hp hτT
    obtain ⟨ρ, hρ, hbox⟩ := ND_box hv hp
    have hx0 := hp.1
    have hτ0 := hp.2.1
    set ε := min ρ (min x0 (min τ0 (M.T - τ0))) with hε
    have hεpos : 0 < ε := lt_min hρ (lt_min hx0 (lt_min hτ0 (by linarith)))
    have hερ : ε ≤ ρ := min_le_left _ _
    have hεx : ε ≤ x0 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hετ : ε ≤ τ0 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hεT : ε ≤ M.T - τ0 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hprops : ∀ x σ, |x - x0| < ε → |σ - τ0| < ε → σ ∈ Icc 0 M.T →
        0 < x ∧ 0 < σ ∧ σ < M.T ∧ (x, σ) ∈ NDset M.T vx := by
      intro x σ hx hσ hσT
      rw [abs_lt] at hx hσ
      refine ⟨by linarith, by linarith, by linarith, hbox x σ ?_ ?_ hσT⟩
      · rw [abs_lt]; constructor <;> linarith
      · rw [abs_lt]; constructor <;> linarith
    have hS := schwarz (f := v) (fx := vx) (ft := vt) (ftx := vtx) (x0 := x0) (τ0 := τ0)
      hεpos ⟨hτ0.le, hτT.le⟩
      (fun x σ hx hσ hσT => by
        obtain ⟨a, b, c, _⟩ := hprops x σ hx hσ hσT
        exact (hder x σ a b c).1)
      (fun x σ hx hσ hσT => by
        obtain ⟨a, b, c, _⟩ := hprops x σ hx hσ hσT
        exact (hder x σ a b c).2.2.hasDerivWithinAt)
      (fun x σ hx hσ hσT => by
        obtain ⟨_, _, _, d⟩ := hprops x σ hx hσ hσT
        exact (hd43 (x, σ) d).2.2.1)
      ((c_vtx _ hp).mono_of_mem_nhdsWithin (ND_nhds hv _ hp))
    exact (uniqueDiffOn_Icc hT τ0 ⟨hτ0.le, hτT.le⟩).eq_deriv _ (hd43 _ hp).2.1 hS
  -- step 2: all of ND (limit at τ = T)
  have heq : ∀ p ∈ NDset M.T vx, vxt p.1 p.2 = vtx p.1 p.2 := by
    rintro ⟨x0, τ0⟩ hp
    rcases lt_or_eq_of_le hp.2.2.1 with h | h
    · exact step1 x0 τ0 hp h
    · simp only
      subst h
      obtain ⟨ρ, hρ, hbox⟩ := ND_box hv hp
      have htend : Tendsto (fun σ => (x0, σ)) (𝓝[<] M.T) (𝓝[NDset M.T vx] (x0, M.T)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · exact ((Continuous.prodMk continuous_const continuous_id).tendsto M.T).mono_left
            nhdsWithin_le_nhds
        · filter_upwards [Ioo_mem_nhdsLT (show max 0 (M.T - ρ) < M.T from
            max_lt hT (by linarith))] with σ hσ
          have h1 : 0 < σ := lt_of_le_of_lt (le_max_left _ _) hσ.1
          have h2 : M.T - ρ < σ := lt_of_le_of_lt (le_max_right _ _) hσ.1
          exact hbox x0 σ (by simpa using hρ)
            (by rw [abs_lt]; constructor <;> linarith [hσ.2]) ⟨h1.le, hσ.2.le⟩
      have hev : ∀ᶠ σ in 𝓝[<] M.T, vxt x0 σ = vtx x0 σ := by
        filter_upwards [Ioo_mem_nhdsLT (show max 0 (M.T - ρ) < M.T from
            max_lt hT (by linarith))] with σ hσ
        have h1 : 0 < σ := lt_of_le_of_lt (le_max_left _ _) hσ.1
        have h2 : M.T - ρ < σ := lt_of_le_of_lt (le_max_right _ _) hσ.1
        exact step1 x0 σ (hbox x0 σ (by simpa using hρ)
            (by rw [abs_lt]; constructor <;> linarith [hσ.2]) ⟨h1.le, hσ.2.le⟩) hσ.2
      have t1 : Tendsto (fun σ => vxt x0 σ) (𝓝[<] M.T) (𝓝 (vxt x0 M.T)) :=
        (c_vxt _ hp).tendsto.comp htend
      have t2 : Tendsto (fun σ => vtx x0 σ) (𝓝[<] M.T) (𝓝 (vtx x0 M.T)) :=
        (c_vtx _ hp).tendsto.comp htend
      exact tendsto_nhds_unique (t1.congr' hev) t2
  refine ⟨heq, ?_⟩
  rintro ⟨x0, τ0⟩ hp
  obtain ⟨ρ, hρ, hbox⟩ := ND_box hv hp
  have hx0 := hp.1
  have hτ0 := hp.2.1
  set ε := min (ρ / 2) (min x0 τ0) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (lt_min hx0 hτ0)
  have hερ : ε ≤ ρ / 2 := min_le_left _ _
  have hεx : ε ≤ x0 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hετ : ε ≤ τ0 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hprops : ∀ x σ, |x - x0| < ε → |σ - τ0| < ε → σ ∈ Icc 0 M.T →
      0 < x ∧ 0 < σ ∧ (x, σ) ∈ NDset M.T vx := by
    intro x σ hx hσ hσT
    rw [abs_lt] at hx hσ
    refine ⟨by linarith, by linarith, hbox x σ ?_ ?_ hσT⟩
    · rw [abs_lt]; constructor <;> linarith
    · rw [abs_lt]; constructor <;> linarith
  exact schwarz (f := vx) (fx := vxx) (ft := vxt) (ftx := vtxx) (x0 := x0) (τ0 := τ0)
    hεpos ⟨hτ0.le, hp.2.2.1⟩
    (fun x σ hx hσ hσT => by
      obtain ⟨a, b, _⟩ := hprops x σ hx hσ hσT
      exact vx_deriv hv x σ a b hσT.2)
    (fun x σ hx hσ hσT => by
      obtain ⟨_, _, d⟩ := hprops x σ hx hσ hσT
      exact (hd43 (x, σ) d).2.1)
    (fun x σ hx hσ hσT => by
      obtain ⟨_, _, d⟩ := hprops x σ hx hσ hσT
      refine (hd43 (x, σ) d).2.2.2.1.congr_of_eventuallyEq ?_
      have hball : Metric.ball x (ρ / 2) ∈ 𝓝 x := Metric.ball_mem_nhds x (by linarith)
      filter_upwards [hball] with y hy
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have hy' : |y - x0| < ρ := by
        rw [abs_lt] at hy hx ⊢; constructor <;> linarith
      have hyσ : |σ - τ0| < ρ := by rw [abs_lt] at hσ ⊢; constructor <;> linarith
      exact heq (y, σ) (hbox y σ hy' hyσ hσT))
    ((c_vtxx _ hp).mono_of_mem_nhdsWithin (ND_nhds hv _ hp))

end DRD45Aux

open Set Filter Topology DynReinsDiv.Barriers DRD45Aux

theorem solution (M : Model) {N : ℕ} (D : DiscreteClaims N) (hμ : M.μ = D.law)
    (v vx vxx vt : ℝ → ℝ → ℝ) (hv : M.IsTheorem31Solution v vx vxx vt)
    (lam : ℝ) (hlam : 0 < lam) (hf : M.fA lam = 0) :
    (∀ j : Fin N, ContDiffOn ℝ 1 (Kinf vx vxx (D.z j)) (Set.Ioc 0 M.T)) ∧
    (∀ j : Fin N, D.z j ≤ 1 / lam →
      ∀ τ ∈ Set.Ioc 0 M.T, Kinf vx vxx (D.z j) τ = 0) ∧
    (∀ j : Fin N, 1 / lam < D.z j → (∀ i : Fin N, i.val + 1 = j.val → D.z i ≤ 1 / lam) →
      ∀ τ ∈ Set.Ioc 0 M.T, 0 < Kinf vx vxx (D.z j) τ ∧
        Kinf vx vxx (D.z j) τ < (D.z j - 1 / lam) / (2 * M.c)) ∧
    (∀ i j : Fin N, i.val + 1 = j.val → 1 / lam < D.z i →
      ∀ τ ∈ Set.Ioc 0 M.T, 0 < Kinf vx vxx (D.z j) τ - Kinf vx vxx (D.z i) τ ∧
        Kinf vx vxx (D.z j) τ - Kinf vx vxx (D.z i) τ < (D.z j - D.z i) / (2 * M.c)) ∧
    (∀ j : Fin N, Filter.Tendsto (Kinf vx vxx (D.z j)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) := by
  obtain ⟨⟨vxxx, vxt, vtx, vtxx, vtt, c_vx, c_vxx, c_vxxx, c_vxt, c_vt, c_vtx, c_vtxx, c_vtt,
    hd43⟩, hneg43, -⟩ := lemma_4_3 M v vx vxx vt hv
  obtain ⟨h48, -, -⟩ := lemma_4_4 M v vx vxx vt hv lam hlam hf
  have hstrict := lemma_4_4_strict M v vx vxx vt hv lam hlam hf
  obtain ⟨hne, -, -, hd0, hdpos⟩ := theorem_4_2 M v vx vxx vt hv
  obtain ⟨-, hvxxt⟩ := mixed_partials hv c_vxt c_vtx c_vtxx hd43
  have hT := M.T_pos
  have hc := M.c_pos
  have hlam' : 0 < 1 / lam := by positivity
  set ND := NDset M.T vx with hND
  -- slice data
  have hslice : ∀ τ ∈ Ioc 0 M.T, _ := fun τ hτ =>
    slice_struct hv hτ.1 hτ.2 (hne τ hτ) (hdpos τ hτ).1
  have hP : ∀ τ ∈ Ioc 0 M.T, ContinuousOn (fun y => vx y τ) (Ici 0) := fun τ hτ =>
    slice_cont M hv.1.2.1 hτ.1 hτ.2
  have hQ : ∀ τ ∈ Ioc 0 M.T, ContinuousOn (fun y => vxx y τ) (Ici 0) := fun τ hτ =>
    slice_cont M hv.1.2.2.1 hτ.1 hτ.2
  have hinND : ∀ τ ∈ Ioc 0 M.T, ∀ x, 0 < x → x < dBoundary vx τ → (x, τ) ∈ ND :=
    fun τ hτ x hx hxd => ⟨hx, hτ.1, hτ.2, (hslice τ hτ).2.2 x hx hxd⟩
  have hder : ∀ τ ∈ Ioc 0 M.T, ∀ x, 0 < x → x < dBoundary vx τ →
      ∃ g', HasDerivAt (fun y => -vx y τ / vxx y τ) g' x ∧ 2 * M.c < g' :=
    fun τ hτ x hx hxd => hstrict (x, τ) (hinND τ hτ x hx hxd)
  have hQneg : ∀ τ ∈ Ioc 0 M.T, ∀ x, 0 < x → x < dBoundary vx τ → vxx x τ < 0 :=
    fun τ hτ x hx hxd => hneg43 (x, τ) (hinND τ hτ x hx hxd)
  have hK : ∀ z, 1 / lam < z → ∀ τ ∈ Ioc 0 M.T,
      0 < Kinf vx vxx z τ ∧ Kinf vx vxx z τ < dBoundary vx τ ∧
      -vx (Kinf vx vxx z τ) τ / vxx (Kinf vx vxx z τ) τ = z := by
    intro z hz τ hτ
    exact Kinf_char (P := fun y => vx y τ) (Q := fun y => vxx y τ) hc (hdpos τ hτ).1 hlam hz
      (hP τ hτ) (hQ τ hτ) (fun x hx => hv.2.2.1 x τ hx hτ.1 hτ.2) (hQneg τ hτ)
      (hslice τ hτ).1 ((hslice τ hτ).2.1 _ le_rfl).2 (h48 τ hτ.1 hτ.2) (hder τ hτ)
  have hK0 : ∀ z, 0 < z → z ≤ 1 / lam → ∀ τ ∈ Ioc 0 M.T, Kinf vx vxx z τ = 0 := by
    intro z hz hzl τ hτ
    have hset : {x : ℝ | 0 < x ∧ -vxx x τ / vx x τ ≤ 1 / z} = Ioi 0 := by
      ext x
      simp only [mem_ofPred_eq, mem_Ioi, and_iff_left_iff_imp]
      intro hx
      have hP1 : 1 ≤ vx x τ := hv.2.2.1 x τ hx hτ.1 hτ.2
      have h39 := hv.2.2.2.2.2.2.2 lam hlam hf x τ hx hτ.1 hτ.2
      have hlz : lam ≤ 1 / z := by
        rw [le_one_div hlam hz]; exact hzl
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    unfold Kinf
    rw [hset, csInf_Ioi]
  have hgs : ∀ τ ∈ Ioc 0 M.T, ∀ a b, 0 ≤ a → a < b → b < dBoundary vx τ →
      2 * M.c * (b - a) < (-vx b τ / vxx b τ) - (-vx a τ / vxx a τ) := by
    intro τ hτ
    have hQ0 : vxx 0 τ ≠ 0 := by
      intro h; have := h48 τ hτ.1 hτ.2; rw [h, div_zero] at this; exact hlam'.ne' this.symm
    exact g_strict (P := fun y => vx y τ) (Q := fun y => vxx y τ) (hP τ hτ) (hQ τ hτ)
      (fun x hx hxd => by
        rcases lt_or_eq_of_le hx with h | h
        · exact (hQneg τ hτ x h hxd).ne
        · rw [← h]; exact hQ0) (hder τ hτ)
  have hzpos : ∀ j : Fin N, 0 < D.z j := D.z_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- C¹ regularity
    intro j
    by_cases hzj : D.z j ≤ 1 / lam
    · exact (contDiffOn_const (c := (0:ℝ))).congr (fun τ hτ => hK0 _ (hzpos j) hzj τ hτ)
    · push Not at hzj
      have hND_open : ∀ p ∈ ND, ND ∈ 𝓝[univ ×ˢ Ioc 0 M.T] p := fun p hp =>
        nhdsWithin_mono _ (prod_mono subset_rfl Ioc_subset_Icc_self) (ND_nhds hv p hp)
      have hconn : ∀ τ a b y, (a, τ) ∈ ND → (b, τ) ∈ ND → y ∈ uIcc a b → (y, τ) ∈ ND := by
        intro τ a b y ha hb hy
        have hy0 : 0 < y := lt_of_lt_of_le (lt_min ha.1 hb.1) hy.1
        refine ⟨hy0, ha.2.1, ha.2.2.1, ?_⟩
        have hanti := vx_antitone hv τ ha.2.1 ha.2.2.1
        have hmax : 0 < max a b := lt_of_lt_of_le ha.1 (le_max_left _ _)
        have := hanti hy0 hmax hy.2
        simp only at this
        rcases le_total a b with h | h
        · rw [max_eq_right h] at this; linarith [hb.2.2.2]
        · rw [max_eq_left h] at this; linarith [ha.2.2.2]
      have hne0 : ∀ p ∈ ND, vxx p.1 p.2 ≠ 0 := fun p hp => (hneg43 p hp).ne
      refine implicit_C1 (T := M.T) (c := 2 * M.c) (z := D.z j)
        (G := fun x τ => -vx x τ / vxx x τ)
        (Gx := fun x τ => ((-vxx x τ) * vxx x τ - (-vx x τ) * vxxx x τ) / (vxx x τ) ^ 2)
        (Gt := fun x τ => ((-vxt x τ) * vxx x τ - (-vx x τ) * vtxx x τ) / (vxx x τ) ^ 2)
        (U := ND) (by positivity) hND_open hconn ?_ ?_ ?_ ?_ ?_ ?_
      · intro τ hτ
        obtain ⟨h1, h2, h3⟩ := hK _ hzj τ hτ
        exact ⟨hinND τ hτ _ h1 h2, h3⟩
      · intro p hp
        exact ((vx_deriv hv p.1 p.2 hp.1 hp.2.1 hp.2.2.1).neg).div (hd43 p hp).1 (hne0 p hp)
      · intro p hp
        exact ((hd43 p hp).2.1.neg).div (hvxxt p hp) (hne0 p hp)
      · refine ((c_vxx.neg.mul c_vxx).sub (c_vx.neg.mul c_vxxx)).div (c_vxx.pow 2) ?_
        intro p hp; exact pow_ne_zero _ (hne0 p hp)
      · refine ((c_vxt.neg.mul c_vxx).sub (c_vx.neg.mul c_vtxx)).div (c_vxx.pow 2) ?_
        intro p hp; exact pow_ne_zero _ (hne0 p hp)
      · intro p hp
        obtain ⟨g', hg', hg'c⟩ := hstrict p hp
        have h2 := ((vx_deriv hv p.1 p.2 hp.1 hp.2.1 hp.2.2.1).neg).div (hd43 p hp).1 (hne0 p hp)
        rw [hg'.unique h2] at hg'c
        exact hg'c.le
  · -- (4.12)
    intro j hj τ hτ
    exact hK0 _ (hzpos j) hj τ hτ
  · -- (4.13)
    intro j hj _ τ hτ
    obtain ⟨h1, h2, h3⟩ := hK _ hj τ hτ
    refine ⟨h1, ?_⟩
    have := hgs τ hτ 0 _ le_rfl h1 h2
    rw [h3, h48 τ hτ.1 hτ.2] at this
    rw [lt_div_iff₀ (by positivity)]
    linarith
  · -- (4.14)
    intro i j hij hi τ hτ
    have hzij : D.z i < D.z j := D.z_strictMono (Fin.lt_def.2 (by omega))
    obtain ⟨hi1, hi2, hi3⟩ := hK _ hi τ hτ
    obtain ⟨hj1, hj2, hj3⟩ := hK _ (lt_trans hi hzij) τ hτ
    have hlt : Kinf vx vxx (D.z i) τ < Kinf vx vxx (D.z j) τ := by
      by_contra hcon
      push Not at hcon
      rcases lt_or_eq_of_le hcon with h | h
      · have := hgs τ hτ _ _ hj1.le h hi2
        rw [hi3, hj3] at this
        have : 0 < 2 * M.c * (Kinf vx vxx (D.z i) τ - Kinf vx vxx (D.z j) τ) := by
          have : 0 < Kinf vx vxx (D.z i) τ - Kinf vx vxx (D.z j) τ := sub_pos.2 h
          positivity
        linarith
      · rw [h] at hj3; rw [hj3] at hi3; linarith
    refine ⟨sub_pos.2 hlt, ?_⟩
    have := hgs τ hτ _ _ hi1.le hlt hj2
    rw [hi3, hj3] at this
    rw [lt_div_iff₀ (by positivity)]
    linarith
  · -- (4.15)
    intro j
    have hbounds : ∀ τ ∈ Ioc 0 M.T, 0 ≤ Kinf vx vxx (D.z j) τ ∧
        Kinf vx vxx (D.z j) τ ≤ dBoundary vx τ := by
      intro τ hτ
      by_cases hzj : D.z j ≤ 1 / lam
      · rw [hK0 _ (hzpos j) hzj τ hτ]; exact ⟨le_rfl, (hdpos τ hτ).1.le⟩
      · push Not at hzj
        obtain ⟨h1, h2, _⟩ := hK _ hzj τ hτ
        exact ⟨h1.le, h2.le⟩
    have hev : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ Ioc 0 M.T := Ioc_mem_nhdsGT hT
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hd0 ?_ ?_
    · filter_upwards [hev] with τ hτ using (hbounds τ hτ).1
    · filter_upwards [hev] with τ hτ using (hbounds τ hτ).2
