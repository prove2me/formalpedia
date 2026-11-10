-- Prove2me | solution 1 for BoundConstrainedPatternSearch.FullConvergence.residual_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T10:02:17.752288+00:00
-- url     : https://prove2.me/submissions/70166d04-731c-48bd-8d8f-ea8504251f74

import Mathlib
import Definitions.Def_BoundConstrainedPatternSearch_FullConvergence_LevelSetRegularity
import Definitions.Def_BoundConstrainedPatternSearch_FullConvergence_StrictStrongMoves

set_option autoImplicit false

open LewisTorczon.BoundPS
open scoped Topology

namespace GPS3816

lemma clamp_coe {a b : EReal} (hab : a < b) (t : ℝ) :
    ((clampCoord a b t : ℝ) : EReal) = max a (min b (t : EReal)) := by
  unfold clampCoord
  apply EReal.coe_toReal
  · exact (max_lt (lt_of_lt_of_le hab le_top)
      (lt_of_le_of_lt (min_le_right _ _) (EReal.coe_lt_top t))).ne
  · exact (lt_max_of_lt_right (lt_min (lt_of_le_of_lt bot_le hab) (EReal.bot_lt_coe t))).ne'

lemma clamp_up {a b : EReal} (hab : a < b) {x t η : ℝ} (hx : a ≤ (x : EReal)) (hη : 0 < η)
    (h : x + η ≤ clampCoord a b t) : ((x + η : ℝ) : EReal) ≤ b ∧ x + η ≤ t := by
  have h1 : ((x + η : ℝ) : EReal) ≤ max a (min b (t : EReal)) := by
    rw [← clamp_coe hab]; exact_mod_cast h
  rcases le_max_iff.1 h1 with h2 | h2
  · exfalso
    have h3 : (x : EReal) < ((x + η : ℝ) : EReal) := by
      exact_mod_cast (by linarith : x < x + η)
    exact absurd (lt_of_lt_of_le h3 (h2.trans hx)) (lt_irrefl _)
  · rw [le_min_iff] at h2
    exact ⟨h2.1, by exact_mod_cast h2.2⟩

lemma clamp_down {a b : EReal} (hab : a < b) {x t η : ℝ} (hx : (x : EReal) ≤ b) (hη : 0 < η)
    (h : clampCoord a b t ≤ x - η) : a ≤ ((x - η : ℝ) : EReal) ∧ t ≤ x - η := by
  have h1 : max a (min b (t : EReal)) ≤ ((x - η : ℝ) : EReal) := by
    rw [← clamp_coe hab]; exact_mod_cast h
  rw [max_le_iff] at h1
  refine ⟨h1.1, ?_⟩
  rcases min_le_iff.1 h1.2 with h2 | h2
  · exfalso
    have h3 : ((x - η : ℝ) : EReal) < (x : EReal) := by
      exact_mod_cast (by linarith : x - η < x)
    exact absurd (lt_of_le_of_lt h2 (h3.trans_le hx)) (lt_irrefl _)
  · exact_mod_cast h2

lemma clamp_continuous {a b : EReal} (hab : a < b) : Continuous (clampCoord a b) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hc : Continuous (fun s : ℝ => max a (min b (s : EReal))) :=
    continuous_const.max (continuous_const.min continuous_coe_real_ereal)
  have hmem : max a (min b (t : EReal)) ∈ ({⊥, ⊤}ᶜ : Set EReal) := by
    rw [← clamp_coe hab]
    simp
  have hA : ContinuousAt EReal.toReal (max a (min b (t : EReal))) :=
    EReal.continuousOn_toReal.continuousAt
      ((isOpen_compl_iff.2 (Set.toFinite _).isClosed).mem_nhds hmem)
  show ContinuousAt (EReal.toReal ∘ fun s : ℝ => max a (min b (s : EReal))) t
  exact ContinuousAt.comp (g := EReal.toReal) hA hc.continuousAt

lemma boxProj_continuous {n : ℕ} {lo hi : Fin n → EReal} (h : ∀ j, lo j < hi j) :
    Continuous (boxProj lo hi) := by
  unfold boxProj
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun j => ?_
  exact (clamp_continuous (h j)).comp ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _))

lemma exists_coord {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) (hv : r ≤ ‖v‖) :
    ∃ j, r / (n + 1) ≤ |v j| := by
  by_contra h
  push_neg at h
  have hsq := EuclideanSpace.real_norm_sq_eq v
  have hle : ∑ j, (v j) ^ 2 ≤ ∑ _j : Fin n, (r / (n + 1)) ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h j).le 2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hlt : (n:ℝ) * (r / (n + 1)) ^ 2 < r ^ 2 := by
    rw [div_pow, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos (mul_pos hr hr) (by positivity : (0:ℝ) < n ^ 2 + n + 1)]
  have hr2 : r ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ hr.le hv 2
  linarith

lemma exists_pos_lb {ι : Type*} (s : Finset ι) (F : ι → ℝ) (h : ∀ p ∈ s, 0 < F p) :
    ∃ a : ℝ, 0 < a ∧ ∀ p ∈ s, a ≤ F p := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · exact ⟨1, one_pos, by simp [hs]⟩
  · obtain ⟨p0, hp0, hmin⟩ := s.exists_min_image F hs
    exact ⟨F p0, h _ hp0, hmin⟩

lemma diag_entry_ne_zero {n : ℕ} (P : GPSParams n) (M : Matrix (Fin n) (Fin n) ℤ) (hM : M ∈ P.𝕄)
    (hdiag : (P.B * M.map (fun a : ℤ => (a : ℝ))).IsDiag) (j : Fin n) :
    (P.B * M.map (fun a : ℤ => (a : ℝ))) j j ≠ 0 := by
  have hdet : (P.B * M.map (fun a : ℤ => (a : ℝ))).det ≠ 0 := by
    rw [Matrix.det_mul]
    refine mul_ne_zero P.B_det_ne_zero ?_
    rw [← Int.cast_det]
    exact_mod_cast P.𝕄_det_ne_zero M hM
  rw [← hdiag.diagonal_diag, Matrix.det_diagonal] at hdet
  exact Finset.prod_ne_zero_iff.1 hdet j (Finset.mem_univ j)

lemma stepOf_col {n : ℕ} (P : GPSParams n) (M : Matrix (Fin n) (Fin n) ℤ)
    (hdiag : (P.B * M.map (fun a : ℤ => (a : ℝ))).IsDiag) (Δ : ℝ) (j : Fin n) :
    stepOf P Δ (M.transpose j) =
      EuclideanSpace.single j (Δ * (P.B * M.map (fun a : ℤ => (a : ℝ))) j j) := by
  ext r
  have key : (P.B.mulVec (fun s => ((M.transpose j s : ℤ) : ℝ))) r =
      (P.B * M.map (fun a : ℤ => (a : ℝ))) r j := by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [stepOf, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul, key]
  by_cases hr : r = j
  · subst hr; simp
  · simp [hr, hdiag hr]

lemma stepOf_negcol {n : ℕ} (P : GPSParams n) (M : Matrix (Fin n) (Fin n) ℤ)
    (hdiag : (P.B * M.map (fun a : ℤ => (a : ℝ))).IsDiag) (Δ : ℝ) (j : Fin n) :
    stepOf P Δ (-(M.transpose j)) =
      EuclideanSpace.single j (-(Δ * (P.B * M.map (fun a : ℤ => (a : ℝ))) j j)) := by
  ext r
  have key : (P.B.mulVec (fun s => (((-(M.transpose j)) s : ℤ) : ℝ))) r =
      -(P.B * M.map (fun a : ℤ => (a : ℝ))) r j := by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [stepOf, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul, key]
  by_cases hr : r = j
  · subst hr; simp
  · simp [hr, hdiag hr]

lemma step_bound {n : ℕ} (P : GPSParams n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Δ : ℝ) (c : Fin n → ℤ), 0 ≤ Δ →
      ‖stepOf P Δ c‖ ≤ K * Δ * ‖intVec c‖ := by
  let Lin : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    { toFun := fun v => WithLp.toLp 2 (P.B.mulVec (WithLp.ofLp v))
      map_add' := by intro a b; simp [Matrix.mulVec_add]
      map_smul' := by intro r a; simp [Matrix.mulVec_smul] }
  let L := LinearMap.toContinuousLinearMap Lin
  refine ⟨‖L‖ + 1, by positivity, fun Δ c hΔ => ?_⟩
  have h1 : stepOf P Δ c = Δ • L (intVec c) := by
    simp [stepOf, intVec, L, Lin]
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hΔ]
  have h2 := L.le_opNorm (intVec c)
  have h3 := mul_le_mul_of_nonneg_left h2 hΔ
  nlinarith [mul_nonneg hΔ (norm_nonneg (intVec c))]

/-- One-dimensional descent along a segment whose gradient stays uniformly descending on the
sublevel set; regularity is only used at points that the argument proves lie in `S`. -/
lemma descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (S Bx : Set E) (hS : IsClosed S) (x u : E) (hx : x ∈ S) (μ : ℝ) (hμ : 0 < μ)
    (hmem : ∀ y, y ∈ Bx → f y ≤ f x → y ∈ S)
    (hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • u ∈ Bx)
    (hd : ∀ y ∈ S, DifferentiableAt ℝ f y)
    (hg : ∀ y ∈ S, ‖y - x‖ ≤ ‖u‖ → inner ℝ (gradient f y) u ≤ -μ) :
    f (x + u) ≤ f x - μ / 2 := by
  let φ : ℝ → ℝ := fun t => f (x + t • u)
  have φ0 : φ 0 = f x := by simp [φ]
  have key : ∀ t ∈ Set.Icc (0:ℝ) 1, φ t ≤ φ 0 - μ / 2 * t := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨t0, ht0, ht0'⟩ := hcon
    let Bad : Set ℝ := {t | t ∈ Set.Icc (0:ℝ) 1 ∧ φ 0 - μ / 2 * t < φ t}
    have hne : Bad.Nonempty := ⟨t0, ht0, ht0'⟩
    have hbdd : BddBelow Bad := ⟨0, fun t ht => ht.1.1⟩
    obtain ⟨T, hTdef⟩ : ∃ T, T = sInf Bad := ⟨_, rfl⟩
    have hT0 : 0 ≤ T := hTdef ▸ le_csInf hne (fun t ht => ht.1.1)
    have below : ∀ t, 0 ≤ t → t < T → φ t ≤ φ 0 - μ / 2 * t := by
      intro t h0 htT
      by_contra h
      push_neg at h
      have h1 : T ≤ t := hTdef ▸ csInf_le hbdd
        ⟨⟨h0, by linarith [(hTdef ▸ csInf_le hbdd ⟨ht0, ht0'⟩ : T ≤ t0), ht0.2]⟩, h⟩
      linarith
    have belowS : ∀ t, 0 ≤ t → t < T → x + t • u ∈ S := by
      intro t h0 htT
      have hT1 : T ≤ 1 := (hTdef ▸ csInf_le hbdd ⟨ht0, ht0'⟩ : T ≤ t0).trans ht0.2
      apply hmem _ (hseg t ⟨h0, by linarith⟩)
      have h1 := below t h0 htT
      have h2 : φ t ≤ f x := by rw [← φ0]; nlinarith
      exact h2
    have hTS : x + T • u ∈ S ∧ φ T ≤ φ 0 - μ / 2 * T := by
      rcases hT0.eq_or_lt with h | h
      · rw [← h]; simp [φ, hx]
      · have htend : Filter.Tendsto (fun t : ℝ => x + t • u) (𝓝[<] T) (𝓝 (x + T • u)) :=
          ((continuous_const.add (continuous_id.smul continuous_const)).tendsto T).mono_left
            nhdsWithin_le_nhds
        have hev : ∀ᶠ t in 𝓝[<] T, 0 ≤ t ∧ t < T := by
          filter_upwards [Ioo_mem_nhdsLT h] with t ht using ⟨ht.1.le, ht.2⟩
        have hmemT : x + T • u ∈ S :=
          hS.mem_of_tendsto htend (hev.mono fun t ht => belowS t ht.1 ht.2)
        refine ⟨hmemT, ?_⟩
        have hcont : ContinuousAt f (x + T • u) := (hd _ hmemT).continuousAt
        have h1 : Filter.Tendsto φ (𝓝[<] T) (𝓝 (φ T)) := hcont.tendsto.comp htend
        have h2 : Filter.Tendsto (fun t => φ 0 - μ / 2 * t) (𝓝[<] T) (𝓝 (φ 0 - μ / 2 * T)) :=
          ((continuous_const.sub (continuous_const.mul continuous_id)).tendsto T).mono_left
            nhdsWithin_le_nhds
        exact le_of_tendsto_of_tendsto h1 h2 (hev.mono fun t ht => below t ht.1 ht.2)
    have hder : HasDerivAt φ (inner ℝ (gradient f (x + T • u)) u) T := by
      have h1 : HasDerivAt (fun t : ℝ => x + t • u) u T := by
        simpa using ((hasDerivAt_id T).smul_const u).const_add x
      have h2 := (hd _ hTS.1).hasGradientAt.hasFDerivAt
      have h3 := h2.comp_hasDerivAt T h1
      rw [InnerProductSpace.toDual_apply_apply] at h3
      exact h3
    have hT1 : T ≤ 1 := (hTdef ▸ csInf_le hbdd ⟨ht0, ht0'⟩ : T ≤ t0).trans ht0.2
    have hD : inner ℝ (gradient f (x + T • u)) u ≤ -μ := by
      apply hg _ hTS.1
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hT0]
      nlinarith [norm_nonneg u]
    have hslope : slope φ T ⁻¹' Set.Iio (-(μ / 2)) ∈ 𝓝[>] T := by
      have h1 := hasDerivAt_iff_tendsto_slope.1 hder
      have h2 : Filter.Tendsto (slope φ T) (𝓝[>] T) (𝓝 (inner ℝ (gradient f (x + T • u)) u)) :=
        h1.mono_left (nhdsWithin_mono _ (fun t ht => (Set.mem_Ioi.1 ht).ne'))
      exact h2 (Iio_mem_nhds (by linarith))
    obtain ⟨U, hU, hUsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hslope
    have hTnot : T ∉ Bad := fun h => absurd hTS.2 (not_le.2 h.2)
    have hall : ∀ b ∈ Bad, U ≤ b := by
      intro b hb
      by_contra hbU
      push_neg at hbU
      have hTb : T ≤ b := hTdef ▸ csInf_le hbdd hb
      have hTb' : T < b := lt_of_le_of_ne hTb (fun h => hTnot (by rw [h]; exact hb))
      have hs := hUsub ⟨hTb', hbU⟩
      simp only [Set.mem_preimage, Set.mem_Iio, slope_def_field] at hs
      have hpos : 0 < b - T := by linarith
      rw [div_lt_iff₀ hpos] at hs
      have := hb.2
      nlinarith [hTS.2]
    have hUT : U ≤ T := hTdef ▸ le_csInf hne hall
    exact absurd hUT (not_le.2 (Set.mem_Ioi.1 hU))
  have h1 := key 1 ⟨zero_le_one, le_rfl⟩
  simpa [φ] using h1

lemma coord_descent {n : ℕ} (lo hi : Fin n → EReal) (hlohi : ∀ j, lo j < hi j)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n))
    (hS : IsClosed (levelSet lo hi f x0))
    (hd : ∀ y ∈ levelSet lo hi f x0, DifferentiableAt ℝ f y)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ levelSet lo hi f x0)
    (η δ : ℝ) (hη : 0 < η)
    (hδ : ∀ y ∈ levelSet lo hi f x0, dist y x < δ → dist (gradient f y) (gradient f x) < η / 2)
    (j : Fin n) (w : ℝ) (hw0 : w ≠ 0) (hwδ : |w| < δ) (hwη : |w| ≤ η)
    (hq : (0 < w ∧ η ≤ projQ lo hi f x j) ∨ (w < 0 ∧ projQ lo hi f x j ≤ -η)) :
    x + EuclideanSpace.single j w ∈ box lo hi ∧
      f (x + EuclideanSpace.single j w) ≤ f x - |w| * η / 4 := by
  have hxb := hx.1
  have hqdef : projQ lo hi f x j =
      clampCoord (lo j) (hi j) (x j - gradient f x j) - x j := by
    simp [projQ, boxProj]
  have hfacts : (∀ t ∈ Set.Icc (0:ℝ) 1, lo j ≤ ((x j + t * w : ℝ) : EReal) ∧
      ((x j + t * w : ℝ) : EReal) ≤ hi j) ∧ w * gradient f x j ≤ -(|w| * η) := by
    rcases hq with ⟨hw, hqj⟩ | ⟨hw, hqj⟩
    · rw [hqdef] at hqj
      obtain ⟨h1, h2⟩ := clamp_up (hlohi j) (hxb j).1 hη (by linarith)
      rw [abs_of_pos hw] at hwη ⊢
      refine ⟨fun t ht => ⟨?_, ?_⟩, ?_⟩
      · exact (hxb j).1.trans (by exact_mod_cast (by nlinarith [ht.1] : x j ≤ x j + t * w))
      · refine le_trans ?_ h1
        exact_mod_cast (by nlinarith [ht.1, ht.2] : x j + t * w ≤ x j + η)
      · nlinarith
    · rw [hqdef] at hqj
      obtain ⟨h1, h2⟩ := clamp_down (hlohi j) (hxb j).2 hη (by linarith)
      rw [abs_of_neg hw] at hwη ⊢
      refine ⟨fun t ht => ⟨?_, ?_⟩, ?_⟩
      · refine le_trans h1 ?_
        exact_mod_cast (by nlinarith [ht.1, ht.2] : x j - η ≤ x j + t * w)
      · exact le_trans (by exact_mod_cast (by nlinarith [ht.1] : x j + t * w ≤ x j)) (hxb j).2
      · nlinarith
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • EuclideanSpace.single j w ∈ box lo hi := by
    intro t ht r
    by_cases hr : r = j
    · subst hr; simpa using hfacts.1 t ht
    · simpa [hr] using hxb r
  have hwpos : 0 < |w| := abs_pos.2 hw0
  have hnorm : ‖EuclideanSpace.single j w‖ = |w| := by simp
  have hin0 : inner ℝ (gradient f x) (EuclideanSpace.single j w) = w * gradient f x j := by
    rw [EuclideanSpace.inner_single_right, conj_trivial]
  have hdesc := descent f (levelSet lo hi f x0) (box lo hi) hS x (EuclideanSpace.single j w) hx
    (|w| * η / 2) (by positivity)
    (fun y hy hfy => ⟨hy, hfy.trans hx.2⟩) hseg hd
    (by
      intro y hy hyx
      have hdist : dist y x < δ := by rw [dist_eq_norm]; linarith
      have hg := hδ y hy hdist
      rw [dist_eq_norm] at hg
      have h1 : inner ℝ (gradient f y) (EuclideanSpace.single j w) =
          inner ℝ (gradient f x) (EuclideanSpace.single j w) +
            inner ℝ (gradient f y - gradient f x) (EuclideanSpace.single j w) := by
        rw [inner_sub_left]; ring
      have h2 := real_inner_le_norm (gradient f y - gradient f x) (EuclideanSpace.single j w)
      rw [hnorm] at h2
      have h3 : ‖gradient f y - gradient f x‖ * |w| ≤ η / 2 * |w| :=
        mul_le_mul_of_nonneg_right hg.le (abs_nonneg w)
      rw [h1, hin0]
      linarith [hfacts.2])
  refine ⟨by simpa using hseg 1 ⟨zero_le_one, le_rfl⟩, ?_⟩
  linarith

end GPS3816

open LewisTorczon.BoundPS in
theorem solution {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0)))
    (hf : BoundConstrainedPatternSearch.FullConvergence.LevelSetRegularity lo hi f (R.x 0))
    (hbdd : BoundedCols R)
    (hΔ : Filter.Tendsto R.Δ Filter.atTop (nhds 0))
    (hstrong : BoundConstrainedPatternSearch.FullConvergence.StrictStrongMoves P lo hi f R) :
    Filter.Tendsto (fun k => ‖projQ lo hi f (R.x k)‖) Filter.atTop (nhds 0) := by
  classical
  obtain ⟨C, hC, hcols⟩ := hbdd
  obtain ⟨K, hK, hKb⟩ := GPS3816.step_bound P
  have hSc : IsClosed (levelSet lo hi f (R.x 0)) := hcpt.isClosed
  have hτ : (1:ℝ) < P.τ := by exact_mod_cast P.one_lt_τ
  have hτ0 : (0:ℝ) < P.τ := lt_trans zero_lt_one hτ
  -- iterates
  have hstep : ∀ k, f (R.x (k+1)) ≤ f (R.x k) := by
    intro k
    rw [hR.x_succ k]
    split_ifs with h
    · exact h.le
    · exact le_rfl
  have hxS : ∀ k, R.x k ∈ levelSet lo hi f (R.x 0) := by
    intro k
    induction k with
    | zero => exact ⟨hR.x_zero_mem, le_rfl⟩
    | succ k ih =>
      rw [hR.x_succ k]
      split_ifs with h
      · exact ⟨hR.step_feasible k, h.le.trans ih.2⟩
      · exact ih
  have hΔpos : ∀ k, 0 < R.Δ k := by
    intro k
    induction k with
    | zero => exact hR.Δ_zero_pos
    | succ k ih =>
      by_cases h : f (R.x k + R.s k) < f (R.x k)
      · obtain ⟨w, _, he⟩ := hR.Δ_succ_success k h
        rw [he]; exact mul_pos (zpow_pos hτ0 _) ih
      · rw [hR.Δ_succ_failure k h]; exact mul_pos (zpow_pos hτ0 _) ih
  have hΔmono : ∀ k, f (R.x k + R.s k) < f (R.x k) → R.Δ k ≤ R.Δ (k+1) := by
    intro k h
    obtain ⟨w, hw, he⟩ := hR.Δ_succ_success k h
    rw [he]
    exact le_mul_of_one_le_left (hΔpos k).le (one_le_zpow₀ hτ.le (P.W_nonneg w hw))
  have hcolb : ∀ k, ∀ c ∈ cols R k, ‖stepOf P (R.Δ k) c‖ ≤ K * C * R.Δ k := by
    intro k c hc
    have h1 := hKb (R.Δ k) c (hΔpos k).le
    have h2 := hcols k c hc
    have h3 : K * R.Δ k * ‖intVec c‖ ≤ K * R.Δ k * C :=
      mul_le_mul_of_nonneg_left h2.le (mul_nonneg hK.le (hΔpos k).le)
    linarith
  -- diagonal lower bound
  obtain ⟨a, ha0, ha⟩ : ∃ a : ℝ, 0 < a ∧
      ∀ k j, a ≤ |(P.B * (R.M k).map (fun z : ℤ => (z : ℝ))) j j| := by
    let F : Matrix (Fin n) (Fin n) ℤ × Fin n → ℝ := fun p =>
      if (P.B * p.1.map (fun z : ℤ => (z : ℝ))).IsDiag then
        |(P.B * p.1.map (fun z : ℤ => (z : ℝ))) p.2 p.2| else 1
    have hF : ∀ p ∈ P.𝕄 ×ˢ (Finset.univ : Finset (Fin n)), 0 < F p := by
      rintro ⟨M, j⟩ hp
      rw [Finset.mem_product] at hp
      simp only [F]
      split_ifs with h
      · exact abs_pos.2 (GPS3816.diag_entry_ne_zero P M hp.1 h j)
      · exact one_pos
    obtain ⟨a, ha, hab⟩ := GPS3816.exists_pos_lb _ F hF
    refine ⟨a, ha, fun k j => ?_⟩
    have := hab (R.M k, j) (Finset.mem_product.2 ⟨hR.M_mem k, Finset.mem_univ j⟩)
    simpa [F, hR.diag k] using this
  -- uniform continuity
  have hgu : UniformContinuousOn (gradient f) (levelSet lo hi f (R.x 0)) :=
    hcpt.uniformContinuousOn_of_continuous hf.2
  have hqc : ContinuousOn (projQ lo hi f) (levelSet lo hi f (R.x 0)) := by
    show ContinuousOn (fun x => boxProj lo hi (x - gradient f x) - x) _
    exact ((GPS3816.boxProj_continuous hlohi).comp_continuousOn
      (continuousOn_id.sub hf.2)).sub continuousOn_id
  have hqu : UniformContinuousOn (projQ lo hi f) (levelSet lo hi f (R.x 0)) :=
    hcpt.uniformContinuousOn_of_continuous hqc
  -- the sufficient-decrease step
  have hD : ∀ ε > 0, ∃ N : ℕ, ∃ c' > 0, ∀ k ≥ N, ε ≤ ‖projQ lo hi f (R.x k)‖ →
      f (R.x k + R.s k) < f (R.x k) ∧
        c' * ‖R.x (k+1) - R.x k‖ ≤ f (R.x k) - f (R.x (k+1)) := by
    intro ε hε
    have hη : 0 < ε / (n + 1) := by positivity
    obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.1 hgu (ε / (n + 1) / 2) (by positivity)
    have hev : ∀ᶠ k in Filter.atTop, K * C * R.Δ k < min δ (ε / (n + 1)) := by
      have h1 : Filter.Tendsto (fun k => K * C * R.Δ k) Filter.atTop (𝓝 0) := by
        simpa using hΔ.const_mul (K * C)
      exact h1 (Iio_mem_nhds (lt_min hδ hη))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N, a * (ε / (n + 1)) / (4 * (K * C)), by positivity, fun k hk hq => ?_⟩
    obtain ⟨j, hj⟩ := GPS3816.exists_coord _ ε hε hq
    have hdlb := ha k j
    have hΔk := hΔpos k
    have hsmall := hN k hk
    have hd0 := GPS3816.diag_entry_ne_zero P (R.M k) (hR.M_mem k) (hR.diag k) j
    obtain ⟨c, hc, w, hcw, hwabs, hsign⟩ : ∃ c ∈ coreCols R k, ∃ w : ℝ,
        stepOf P (R.Δ k) c = EuclideanSpace.single j w ∧
        |w| = R.Δ k * |(P.B * (R.M k).map (fun z : ℤ => (z : ℝ))) j j| ∧
        ((0 < w ∧ ε / (n + 1) ≤ projQ lo hi f (R.x k) j) ∨
          (w < 0 ∧ projQ lo hi f (R.x k) j ≤ -(ε / (n + 1)))) := by
      have hcol := GPS3816.stepOf_col P (R.M k) (hR.diag k) (R.Δ k) j
      have hneg := GPS3816.stepOf_negcol P (R.M k) (hR.diag k) (R.Δ k) j
      have hm1 : (R.M k).transpose j ∈ coreCols R k := ⟨j, Or.inl rfl⟩
      have hm2 : -((R.M k).transpose j) ∈ coreCols R k := ⟨j, Or.inr rfl⟩
      rcases le_abs'.1 hj with hq' | hq' <;> rcases hd0.lt_or_gt with hdn | hdp
      · exact ⟨_, hm1, _, hcol, by rw [abs_mul, abs_of_pos hΔk],
          Or.inr ⟨mul_neg_of_pos_of_neg hΔk hdn, hq'⟩⟩
      · exact ⟨_, hm2, _, hneg, by rw [abs_neg, abs_mul, abs_of_pos hΔk],
          Or.inr ⟨neg_neg_of_pos (mul_pos hΔk hdp), hq'⟩⟩
      · exact ⟨_, hm2, _, hneg, by rw [abs_neg, abs_mul, abs_of_pos hΔk],
          Or.inl ⟨neg_pos.2 (mul_neg_of_pos_of_neg hΔk hdn), hq'⟩⟩
      · exact ⟨_, hm1, _, hcol, by rw [abs_mul, abs_of_pos hΔk],
          Or.inl ⟨mul_pos hΔk hdp, hq'⟩⟩
    have hcK := hcolb k c (Or.inl hc)
    rw [hcw] at hcK
    have hnorm : ‖EuclideanSpace.single j w‖ = |w| := by simp
    rw [hnorm] at hcK
    have hwa : a * R.Δ k ≤ |w| := by rw [hwabs]; nlinarith
    have hw0 : w ≠ 0 := by
      intro h; rw [h, abs_zero] at hwa; nlinarith [mul_pos ha0 hΔk]
    have hwδ : |w| < δ := lt_of_le_of_lt hcK (lt_of_lt_of_le hsmall (min_le_left _ _))
    have hwη : |w| ≤ ε / (n + 1) :=
      le_trans hcK (lt_of_lt_of_le hsmall (min_le_right _ _)).le
    obtain ⟨hbox, hdec⟩ := GPS3816.coord_descent lo hi hlohi f (R.x 0) hSc hf.1 (R.x k) (hxS k)
      (ε / (n + 1)) δ hη (fun y hy hyx => hδg y hy (R.x k) (hxS k) hyx) j w hw0 hwδ hwη hsign
    have hwpos : 0 < |w| := abs_pos.2 hw0
    have hlt : f (R.x k + stepOf P (R.Δ k) c) < f (R.x k) := by
      rw [hcw]
      have : 0 < |w| * (ε / (n + 1)) / 4 := by positivity
      linarith
    have hbox' : R.x k + stepOf P (R.Δ k) c ∈ box lo hi := by rw [hcw]; exact hbox
    have hstr := (hstrong k).2.2 ⟨c, hc, hbox', hlt⟩ c hc hbox'
    rw [hcw] at hstr
    have hpos4 : 0 < |w| * (ε / (n + 1)) / 4 := by positivity
    have hsucc : f (R.x k + R.s k) < f (R.x k) := by linarith
    refine ⟨hsucc, ?_⟩
    have hxk1 : R.x (k+1) = R.x k + R.s k := by rw [hR.x_succ k, if_pos hsucc]
    rw [hxk1, add_sub_cancel_left]
    obtain ⟨c2, hc2, hs2⟩ := hR.step_mem k
    have hsb : ‖R.s k‖ ≤ K * C * R.Δ k := by rw [hs2]; exact hcolb k c2 hc2
    have hKC : 0 < K * C := mul_pos hK hC
    have e1 : a * (ε / (n + 1)) / (4 * (K * C)) * ‖R.s k‖ ≤
        a * (ε / (n + 1)) / (4 * (K * C)) * (K * C * R.Δ k) :=
      mul_le_mul_of_nonneg_left hsb (by positivity)
    have e2 : a * (ε / (n + 1)) / (4 * (K * C)) * (K * C * R.Δ k) =
        a * R.Δ k * (ε / (n + 1)) / 4 := by
      field_simp
    have e3 : a * R.Δ k * (ε / (n + 1)) / 4 ≤ |w| * (ε / (n + 1)) / 4 := by
      have := mul_le_mul_of_nonneg_right hwa hη.le
      linarith
    linarith
  -- main argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra hcon
  push_neg at hcon
  simp only [Real.dist_eq, sub_zero, abs_norm] at hcon
  obtain ⟨N1, c', hc', hD1⟩ := hD (ε / 2) (by positivity)
  obtain ⟨δq, hδq, hq⟩ := Metric.uniformContinuousOn_iff.1 hqu (ε / 2) (by positivity)
  have hfc : ContinuousOn f (levelSet lo hi f (R.x 0)) :=
    fun y hy => (hf.1 y hy).continuousAt.continuousWithinAt
  obtain ⟨mlb, hmlb⟩ := hcpt.bddBelow_image hfc
  have hbddr : BddBelow (Set.range fun k => f (R.x k)) := by
    refine ⟨mlb, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hmlb ⟨R.x k, hxS k, rfl⟩
  have hanti : Antitone (fun k => f (R.x k)) := antitone_nat_of_succ_le hstep
  obtain ⟨N2, hN2⟩ := exists_lt_of_ciInf_lt
    (by have := mul_pos hc' hδq; linarith : (⨅ k, f (R.x k)) < (⨅ k, f (R.x k)) + c' * δq)
  obtain ⟨k, hk, hqk⟩ := hcon (max N1 N2)
  have hkN1 : N1 ≤ k := le_trans (le_max_left _ _) hk
  have hkN2 : N2 ≤ k := le_trans (le_max_right _ _) hk
  have hex : ∃ l, k ≤ l ∧ ‖projQ lo hi f (R.x l)‖ < ε / 2 := by
    by_contra h
    push_neg at h
    have hgrow : ∀ l, k ≤ l → R.Δ k ≤ R.Δ l := by
      intro l hl
      induction l, hl using Nat.le_induction with
      | base => exact le_rfl
      | succ l hkl ih =>
        exact ih.trans (hΔmono l (hD1 l (le_trans hkN1 hkl) (h l hkl)).1)
    obtain ⟨N3, hN3⟩ := Filter.eventually_atTop.1 (hΔ (Iio_mem_nhds (hΔpos k)))
    have h1 := hN3 (max N3 k) (le_max_left _ _)
    have h2 := hgrow (max N3 k) (le_max_right _ _)
    simp only [Set.mem_preimage, Set.mem_Iio] at h1
    linarith
  let l := Nat.find hex
  have hl : k ≤ l ∧ ‖projQ lo hi f (R.x l)‖ < ε / 2 := Nat.find_spec hex
  have hmin : ∀ i < l, ¬ (k ≤ i ∧ ‖projQ lo hi f (R.x i)‖ < ε / 2) :=
    fun i hi => Nat.find_min hex hi
  have hchain : ∀ i, k ≤ i → i ≤ l → c' * ‖R.x i - R.x k‖ ≤ f (R.x k) - f (R.x i) := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => intro _; simp
    | succ i hki ih =>
      intro hil
      have hil' : i < l := by omega
      have hqi : ε / 2 ≤ ‖projQ lo hi f (R.x i)‖ := by
        by_contra h; push_neg at h; exact hmin i hil' ⟨hki, h⟩
      have h1 := (hD1 i (le_trans hkN1 hki) hqi).2
      have h2 := ih hil'.le
      have h3 : ‖R.x (i+1) - R.x k‖ ≤ ‖R.x (i+1) - R.x i‖ + ‖R.x i - R.x k‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h4 := mul_le_mul_of_nonneg_left h3 hc'.le
      linarith
  have hfin := hchain l hl.1 le_rfl
  have hdist : δq ≤ ‖R.x l - R.x k‖ := by
    by_contra h
    push_neg at h
    have h1 : dist (R.x k) (R.x l) < δq := by rw [dist_comm, dist_eq_norm]; exact h
    have h2 := hq (R.x k) (hxS k) (R.x l) (hxS l) h1
    rw [dist_eq_norm] at h2
    have h3 := norm_sub_norm_le (projQ lo hi f (R.x k)) (projQ lo hi f (R.x l))
    linarith [hl.2]
  have h1 : f (R.x k) ≤ f (R.x N2) := hanti hkN2
  have h2 : (⨅ k, f (R.x k)) ≤ f (R.x l) := ciInf_le hbddr l
  have h3 := mul_le_mul_of_nonneg_left hdist hc'.le
  linarith
