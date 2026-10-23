-- Prove2me | solution 1 for CertDRO.SGD.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T10:20:27.238992+00:00
-- url     : https://prove2.me/submissions/e18c75bf-f334-4649-85f4-c2c44bd6ad17

import Definitions.Def_CertDRO_SGD_model
open MeasureTheory Filter Topology Set
open CertDRO.SGD
open scoped ENNReal NNReal InnerProductSpace

namespace CertDROProof
end CertDROProof

open Filter Topology Set
open scoped InnerProductSpace

namespace CertDROProof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem line_mem (s : Set E) (hs : Convex ℝ s) (x y : E) (hx : x ∈ s) (hy : y ∈ s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (y - x) ∈ s := by
  convert hs hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring) using 1
  module

theorem smooth_upper_on (s : Set E) (hs : Convex ℝ s) (f : E → ℝ) (g : E → E)
    (L : ℝ) (hL : 0 ≤ L) (hf : ∀ x ∈ s, HasGradientAt f (g x) x)
    (hg : ∀ x ∈ s, ∀ y ∈ s, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (x y : E) (hx : x ∈ s) (hy : y ∈ s) :
    f y - f x - inner ℝ (g x) (y - x) ≤ L / 2 * ‖y - x‖ ^ 2 := by
  have _ := hL
  let v := y - x
  let p : ℝ → E := fun t => x + t • v
  let q : ℝ → ℝ := fun t => f (p t) - f x - t * inner ℝ (g x) v -
    L / 2 * t ^ 2 * ‖v‖ ^ 2
  let q' : ℝ → ℝ := fun t => inner ℝ (g (p t)) v - inner ℝ (g x) v -
    L * t * ‖v‖ ^ 2
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt q (q' t) t := by
    have hp : HasDerivAt p v t := by
      convert! (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v) using 1
      simp
    have hf' : HasDerivAt (fun t => f (p t)) (inner ℝ (g (p t)) v) t := by
      exact (hf (p t) (line_mem s hs x y hx hy ht)).hasFDerivAt.comp_hasDerivAt t hp
    dsimp only [q, q']
    convert! ((hf'.sub_const (f x)).sub ((hasDerivAt_id t).mul_const (inner ℝ (g x) v))).sub
      ((((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖v‖ ^ 2)) using 1
    dsimp only [id_eq]
    ring
  have hnon (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : q' t ≤ 0 := by
    have hg' := hg (p t) (line_mem s hs x y hx hy ht) x hx
    have hp : ‖p t - x‖ = t * ‖v‖ := by simp [p, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    rw [hp] at hg'
    have hi := real_inner_le_norm (g (p t) - g x) v
    rw [inner_sub_left] at hi
    have hh := mul_le_mul_of_nonneg_right hg' (norm_nonneg v)
    dsimp [q']
    nlinarith
  have ha : AntitoneOn q (Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hnon t (interior_subset ht))
  have h := ha (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num)
  have hp1 : p 1 = y := by dsimp [p, v]; module
  have hp0 : p 0 = x := by simp [p]
  simp [q, hp1, hp0] at h
  dsimp [v] at h
  linarith

theorem smooth_model_on (s : Set E) (hs : Convex ℝ s) (f : E → ℝ) (g : E → E)
    (L : ℝ) (hL : 0 ≤ L) (hf : ∀ x ∈ s, HasGradientAt f (g x) x)
    (hg : ∀ x ∈ s, ∀ y ∈ s, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (x y : E) (hx : x ∈ s) (hy : y ∈ s) :
    |f y - f x - inner ℝ (g x) (y - x)| ≤ L / 2 * ‖y - x‖ ^ 2 := by
  have hu := smooth_upper_on s hs f g L hL hf hg x y hx hy
  have hn := smooth_upper_on s hs (fun z => -f z) (fun z => -g z) L hL
    (fun z hz => by
      change HasFDerivAt _ _ _
      convert! (hf z hz).hasFDerivAt.neg using 1
      simp) (by simpa only [neg_sub_neg, norm_sub_rev] using hg) x y hx hy
  simp only [inner_neg_left] at hn
  exact abs_le.mpr ⟨by linarith, hu⟩

end CertDROProof

open MeasureTheory Filter Topology Set
open CertDRO.SGD
open scoped InnerProductSpace

namespace CertDROProof

theorem right_linear_bound (A B : ℝ)
    (h : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) * A ≤ B) : A ≤ B := by
  have ht : Tendsto (fun t : ℝ => (1 - t) * A) (𝓝[>] 0) (𝓝 A) := by
    have hc : Continuous (fun t : ℝ => (1-t)*A) := by fun_prop
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with t ht ht1
  exact h t ht ht1

variable {d m : ℕ} {Z : Set (Data m)} {c : Data m → Data m → ℝ}
    {ℓ : Param d → Data m → ℝ} {gθ : Param d → Data m → Param d}
    {gz : Param d → Data m → Data m} {Lθθ Lzz Lθz Lzθ γ : ℝ}

theorem cost_lower (hA : AssumptionA Z c) (z z₀ : Data m) (hz : z ∈ Z) (hz₀ : z₀ ∈ Z) :
    ‖z - z₀‖ ^ 2 / 2 ≤ c z z₀ := by
  apply right_linear_bound
  intro t ht ht1
  have hu := (hA.strongConvexOn z₀ hz₀).1 hz₀ hz (by linarith : 0 ≤ 1 - t) ht.le
    (by ring : 1 - t + t = 1)
  have hc := (hA.strongConvexOn z₀ hz₀).2 hz₀ hz (by linarith : 0 ≤ 1 - t) ht.le
    (by ring : 1 - t + t = 1)
  have hn := hA.nonneg _ hu z₀ hz₀
  simp only [smul_eq_mul, hA.diag z₀ hz₀, mul_zero, zero_add, norm_sub_rev] at hc
  apply (mul_le_mul_iff_right₀ ht).mp
  nlinarith

theorem penalized_upper (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (θ : Param d) (z z₀ : Data m) (hz : z ∈ Z) (hz₀ : z₀ ∈ Z) :
    penalized ℓ c γ z₀ θ z ≤ ℓ θ z₀ + ‖gz θ z₀‖ * ‖z - z₀‖ -
      (γ - Lzz) / 2 * ‖z - z₀‖ ^ 2 := by
  have hγ : 0 ≤ γ := le_trans hS.assumptionB.Lzz_nonneg hS.gamma_gt.le
  have hs := smooth_upper_on Z hS.convex (ℓ θ) (gz θ) Lzz hS.assumptionB.Lzz_nonneg
    (hS.assumptionB.hasGradientAt_z θ) (hS.assumptionB.lip_zz θ) z₀ z hz₀ hz
  have hi := real_inner_le_norm (gz θ z₀) (z - z₀)
  have hc := mul_le_mul_of_nonneg_left (cost_lower hS.assumptionA z z₀ hz hz₀) hγ
  dsimp [penalized]
  nlinarith

theorem penalized_continuousOn (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (θ : Param d) (z₀ : Data m) (hz₀ : z₀ ∈ Z) :
    ContinuousOn (penalized ℓ c γ z₀ θ) Z := by
  have hl : ContinuousOn (ℓ θ) Z := fun z hz =>
    (hS.assumptionB.hasGradientAt_z θ z hz).continuousAt.continuousWithinAt
  exact hl.sub
    (continuousOn_const.mul (hS.assumptionA.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun _ hz => ⟨hz, hz₀⟩)))

theorem maximizer_exists (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (θ : Param d) (z₀ : Data m) (hz₀ : z₀ ∈ Z) :
    ∃ zs, IsMaximizer Z ℓ c γ θ z₀ zs := by
  let a := γ - Lzz
  have ha : 0 < a := sub_pos.mpr hS.gamma_gt
  let R := 1 + 2 * ‖gz θ z₀‖ / a
  have hR : 0 < R := by dsimp [R]; positivity
  let K := Z ∩ Metric.closedBall z₀ R
  have hK : IsCompact K := (isCompact_closedBall z₀ R).inter_left hS.closed
  have hzK : z₀ ∈ K := ⟨hz₀, by simpa using hR.le⟩
  obtain ⟨zs, hzs, hmax⟩ := hK.exists_isMaxOn ⟨z₀, hzK⟩
    ((penalized_continuousOn hS θ z₀ hz₀).mono inter_subset_left)
  refine ⟨zs, hzs.1, fun z hz => ?_⟩
  by_cases hzK' : z ∈ K
  · exact hmax hzK'
  · have hr : R < ‖z - z₀‖ := by
      have hn : z ∉ Metric.closedBall z₀ R := fun h => hzK' ⟨hz, h⟩
      simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hn
    have hr0 : 0 < ‖z - z₀‖ := lt_trans hR hr
    have hcoef : 2 * ‖gz θ z₀‖ < a * ‖z - z₀‖ := by
      have hh : 2 * ‖gz θ z₀‖ / a < ‖z - z₀‖ := by dsimp [R] at hr; linarith
      have := (div_lt_iff₀ ha).mp hh
      nlinarith
    have hprod := mul_pos (sub_pos.mpr hcoef) hr0
    have hu := penalized_upper hS θ z z₀ hz hz₀
    have hbase : penalized ℓ c γ z₀ θ z₀ ≤ penalized ℓ c γ z₀ θ zs := hmax hzK
    have hb0 : penalized ℓ c γ z₀ θ z₀ = ℓ θ z₀ := by
      simp [penalized, hS.assumptionA.diag z₀ hz₀]
    rw [hb0] at hbase
    dsimp [a] at hprod
    linarith

theorem maximizer_value {θ : Param d} {z₀ zs : Data m}
    (h : IsMaximizer Z ℓ c γ θ z₀ zs) :
    robustSurrogate Z ℓ c γ θ z₀ = penalized ℓ c γ z₀ θ zs := by
  change sSup (penalized ℓ c γ z₀ θ '' Z) = penalized ℓ c γ z₀ θ zs
  apply le_antisymm
  · exact _root_.csSup_le (s := penalized ℓ c γ z₀ θ '' Z)
      (a := penalized ℓ c γ z₀ θ zs)
      ⟨penalized ℓ c γ z₀ θ zs, zs, h.1, rfl⟩
      (by rintro _ ⟨z, hz, rfl⟩; exact h.2 z hz)
  · exact le_csSup ⟨penalized ℓ c γ z₀ θ zs, by rintro _ ⟨z, hz, rfl⟩; exact h.2 z hz⟩ ⟨zs, h.1, rfl⟩

theorem penalized_segment (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (θ : Param d) (z₀ x y : Data m) (hz₀ : z₀ ∈ Z) (hx : x ∈ Z) (hy : y ∈ Z)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (1-t) * penalized ℓ c γ z₀ θ x + t * penalized ℓ c γ z₀ θ y +
      (γ-Lzz)/2 * t*(1-t)*‖x-y‖^2 ≤
      penalized ℓ c γ z₀ θ ((1-t) • x + t • y) := by
  let u := (1-t) • x + t • y
  have hu : u ∈ Z := hS.convex hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hux := smooth_upper_on Z hS.convex (ℓ θ) (gz θ) Lzz hS.assumptionB.Lzz_nonneg
    (hS.assumptionB.hasGradientAt_z θ) (hS.assumptionB.lip_zz θ) u x hu hx
  have huy := smooth_upper_on Z hS.convex (ℓ θ) (gz θ) Lzz hS.assumptionB.Lzz_nonneg
    (hS.assumptionB.hasGradientAt_z θ) (hS.assumptionB.lip_zz θ) u y hu hy
  have hxu : x-u = t • (x-y) := by dsimp [u]; module
  have hyu : y-u = (1-t) • (y-x) := by dsimp [u]; module
  have hnx : ‖x-u‖ = t*‖x-y‖ := by rw [hxu, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hny : ‖y-u‖ = (1-t)*‖x-y‖ := by
    rw [hyu, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2), norm_sub_rev]
  have hlin : (1-t)*inner ℝ (gz θ u) (x-u) + t*inner ℝ (gz θ u) (y-u) = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
    have he : (1-t) • (x-u) + t • (y-u) = 0 := by dsimp [u]; module
    rw [he, inner_zero_right]
  rw [hnx] at hux
  rw [hny] at huy
  have hx' := mul_le_mul_of_nonneg_left hux (sub_nonneg.mpr ht.2)
  have hy' := mul_le_mul_of_nonneg_left huy ht.1
  have hl : (1-t)*ℓ θ x + t*ℓ θ y - Lzz/2*t*(1-t)*‖x-y‖^2 ≤ ℓ θ u := by
    nlinarith
  have hc := (hS.assumptionA.strongConvexOn z₀ hz₀).2 hx hy
    (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  simp only [smul_eq_mul] at hc
  have hγ : 0 ≤ γ := le_trans hS.assumptionB.Lzz_nonneg hS.gamma_gt.le
  have hc' := mul_le_mul_of_nonneg_left hc hγ
  dsimp [penalized]
  dsimp [u] at hl
  nlinarith

theorem maximizer_gap (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    {θ : Param d} {z₀ zs : Data m} (hz₀ : z₀ ∈ Z)
    (hmax : IsMaximizer Z ℓ c γ θ z₀ zs) (z : Data m) (hz : z ∈ Z) :
    (γ-Lzz)/2 * ‖z-zs‖^2 ≤ penalized ℓ c γ z₀ θ zs - penalized ℓ c γ z₀ θ z := by
  apply right_linear_bound
  intro t ht ht1
  have hc := penalized_segment hS θ z₀ zs z hz₀ hmax.1 hz t ⟨ht.le, ht1.le⟩
  have hu := hS.convex hmax.1 hz (by linarith : 0 ≤ 1-t) ht.le (by ring : 1-t+t=1)
  have hm := hmax.2 _ hu
  rw [norm_sub_rev zs z] at hc
  apply (mul_le_mul_iff_right₀ ht).mp
  nlinarith

theorem loss_cross_bound (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (θ θ' : Param d) (x y : Data m) (hx : x ∈ Z) (hy : y ∈ Z) :
    |(ℓ θ y - ℓ θ' y) - (ℓ θ x - ℓ θ' x)| ≤
      Lzθ * ‖θ-θ'‖ * ‖y-x‖ := by
  let p : ℝ → Data m := fun t => x + t • (y-x)
  let f : ℝ → ℝ := fun t => ℓ θ (p t) - ℓ θ' (p t)
  let f' : ℝ → ℝ := fun t => inner ℝ (gz θ (p t) - gz θ' (p t)) (y-x)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f (f' t) t := by
    have hp : HasDerivAt p (y-x) t := by
      convert! (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const (y-x)) using 1
      simp
    have hz := line_mem Z hS.convex x y hx hy ht
    have h1 := (hS.assumptionB.hasGradientAt_z θ (p t) hz).hasFDerivAt.comp_hasDerivAt t hp
    have h2 := (hS.assumptionB.hasGradientAt_z θ' (p t) hz).hasFDerivAt.comp_hasDerivAt t hp
    convert! h1.sub h2 using 1
    simp [f', inner_sub_left]
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖f' t‖ ≤ Lzθ * ‖θ-θ'‖ * ‖y-x‖ := by
    have hz := line_mem Z hS.convex x y hx hy ⟨ht.1, ht.2.le⟩
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hS.assumptionB.lip_zθ θ θ' (p t) hz) (norm_nonneg _))
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hd t ht).hasDerivWithinAt) hb 1 (by norm_num)
  have h1 : p 1 = y := by dsimp [p]; module
  have h0 : p 0 = x := by simp [p]
  simpa [f, h1, h0, Real.norm_eq_abs] using h

theorem maximizer_distance (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    {θ θ' : Param d} {z₀ x y : Data m} (hz₀ : z₀ ∈ Z)
    (hx : IsMaximizer Z ℓ c γ θ z₀ x) (hy : IsMaximizer Z ℓ c γ θ' z₀ y) :
    ‖x-y‖ ≤ Lzθ / (γ-Lzz) * ‖θ-θ'‖ := by
  have ha : 0 < γ-Lzz := sub_pos.mpr hS.gamma_gt
  have h1 := maximizer_gap hS hz₀ hx y hy.1
  have h2 := maximizer_gap hS hz₀ hy x hx.1
  have h3 := (abs_le.mp (loss_cross_bound hS θ θ' x y hx.1 hy.1)).1
  rw [norm_sub_rev y x] at h1 h3
  dsimp [penalized] at h1 h2
  have hh : (γ-Lzz)*‖x-y‖^2 ≤ Lzθ*‖θ-θ'‖*‖x-y‖ := by linarith
  by_cases hz : ‖x-y‖ = 0
  · rw [hz]
    exact mul_nonneg (div_nonneg hS.assumptionB.Lzθ_nonneg ha.le) (norm_nonneg _)
  · have hr := lt_of_le_of_ne (norm_nonneg (x-y)) (Ne.symm hz)
    have hbound : (γ-Lzz)*‖x-y‖ ≤ Lzθ*‖θ-θ'‖ := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    nlinarith

end CertDROProof

open MeasureTheory Filter Topology Set
open CertDRO.SGD
open scoped InnerProductSpace NNReal

namespace CertDROProof

variable {d m : ℕ} {Z : Set (Data m)} {c : Data m → Data m → ℝ}
    {ℓ : Param d → Data m → ℝ} {gθ : Param d → Data m → Param d}
    {gz : Param d → Data m → Data m} {Lθθ Lzz Lθz Lzθ γ : ℝ}

theorem lphi_nonneg (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ) :
    0 ≤ Lphi Lθθ Lzz Lθz Lzθ γ :=
  add_nonneg hS.assumptionB.Lθθ_nonneg
    (div_nonneg (mul_nonneg hS.assumptionB.Lθz_nonneg hS.assumptionB.Lzθ_nonneg)
      (sub_pos.mpr hS.gamma_gt).le)

theorem surrogate_model (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    {θ : Param d} {z₀ zs : Data m} (hz₀ : z₀ ∈ Z)
    (hmax : IsMaximizer Z ℓ c γ θ z₀ zs) (θ' : Param d) :
    |robustSurrogate Z ℓ c γ θ' z₀ - robustSurrogate Z ℓ c γ θ z₀ -
      inner ℝ (gθ θ zs) (θ'-θ)| ≤
      (Lθθ/2 + Lθz*Lzθ/(γ-Lzz))*‖θ'-θ‖^2 := by
  obtain ⟨zs', hm'⟩ := maximizer_exists hS θ' z₀ hz₀
  have h1 := smooth_model_on univ convex_univ (fun p => ℓ p zs) (fun p => gθ p zs)
    Lθθ hS.assumptionB.Lθθ_nonneg (fun p _ => hS.assumptionB.hasGradientAt_θ p zs hmax.1)
    (fun p _ q _ => hS.assumptionB.lip_θθ p q zs hmax.1) θ θ' (mem_univ _) (mem_univ _)
  have h2 := smooth_upper_on univ convex_univ (fun p => ℓ p zs') (fun p => gθ p zs')
    Lθθ hS.assumptionB.Lθθ_nonneg (fun p _ => hS.assumptionB.hasGradientAt_θ p zs' hm'.1)
    (fun p _ q _ => hS.assumptionB.lip_θθ p q zs' hm'.1) θ θ' (mem_univ _) (mem_univ _)
  have hg := hS.assumptionB.lip_θz θ zs' hm'.1 zs hmax.1
  have hd := maximizer_distance hS hz₀ hm' hmax
  have hg' := hg.trans (mul_le_mul_of_nonneg_left hd hS.assumptionB.Lθz_nonneg)
  have hi := (real_inner_le_norm (gθ θ zs' - gθ θ zs) (θ'-θ)).trans
    (mul_le_mul_of_nonneg_right hg' (norm_nonneg _))
  rw [inner_sub_left] at hi
  have hlo := hm'.2 zs hmax.1
  have hup := hmax.2 zs' hm'.1
  rw [maximizer_value hmax, maximizer_value hm']
  have hnon : 0 ≤ Lθz*Lzθ/(γ-Lzz) := div_nonneg
    (mul_nonneg hS.assumptionB.Lθz_nonneg hS.assumptionB.Lzθ_nonneg)
    (sub_pos.mpr hS.gamma_gt).le
  have hmore := mul_nonneg hnon (sq_nonneg ‖θ'-θ‖)
  have hlow := (abs_le.mp h1).1
  dsimp [penalized] at hlo hup ⊢
  apply abs_le.mpr
  simp only [div_eq_mul_inv] at hi hmore hlow h2 ⊢
  constructor <;> nlinarith

theorem gradient_at_maximizer (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    {θ : Param d} {z₀ zs : Data m} (hz₀ : z₀ ∈ Z)
    (hmax : IsMaximizer Z ℓ c γ θ z₀ zs) :
    HasGradientAt (fun p => robustSurrogate Z ℓ c γ p z₀) (gθ θ zs) θ := by
  change HasFDerivAt _ _ _
  rw [hasFDerivAt_iff_tendsto]
  let C := Lθθ/2 + Lθz*Lzθ/(γ-Lzz)
  have hC : 0 ≤ C := add_nonneg (div_nonneg hS.assumptionB.Lθθ_nonneg (by norm_num))
    (div_nonneg (mul_nonneg hS.assumptionB.Lθz_nonneg hS.assumptionB.Lzθ_nonneg)
      (sub_pos.mpr hS.gamma_gt).le)
  have hb (p : Param d) :
      ‖p-θ‖⁻¹ * ‖robustSurrogate Z ℓ c γ p z₀ - robustSurrogate Z ℓ c γ θ z₀ -
        (InnerProductSpace.toDual ℝ (Param d) (gθ θ zs)) (p-θ)‖ ≤ C*‖p-θ‖ := by
    have hs := surrogate_model hS hz₀ hmax p
    change _ ≤ C*‖p-θ‖^2 at hs
    change ‖p-θ‖⁻¹ * |robustSurrogate Z ℓ c γ p z₀ - robustSurrogate Z ℓ c γ θ z₀ -
      inner ℝ (gθ θ zs) (p-θ)| ≤ C*‖p-θ‖
    by_cases hz : ‖p-θ‖ = 0
    · simp [hz]
    · have hp : 0 < ‖p-θ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      apply (inv_mul_le_iff₀ hp).2
      nlinarith
  have ht : Tendsto (fun p : Param d => C*‖p-θ‖) (𝓝 θ) (𝓝 0) := by
    have hc : Continuous (fun p : Param d => C*‖p-θ‖) := by fun_prop
    simpa using hc.tendsto θ
  exact squeeze_zero (fun p => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) hb ht

theorem surrogate_hasGradient (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (θ : Param d) (z₀ : Data m) (hz₀ : z₀ ∈ Z) :
    HasGradientAt (fun θ' => robustSurrogate Z ℓ c γ θ' z₀)
      (gradient (fun θ' => robustSurrogate Z ℓ c γ θ' z₀) θ) θ := by
  obtain ⟨zs, hmax⟩ := maximizer_exists hS θ z₀ hz₀
  have h := gradient_at_maximizer hS hz₀ hmax
  rw [h.gradient]
  exact h

theorem surrogate_gradient_lipschitz (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (θ θ' : Param d) (z₀ : Data m) (hz₀ : z₀ ∈ Z) :
    ‖gradient (fun p => robustSurrogate Z ℓ c γ p z₀) θ -
        gradient (fun p => robustSurrogate Z ℓ c γ p z₀) θ'‖ ≤
      Lphi Lθθ Lzz Lθz Lzθ γ * ‖θ - θ'‖ := by
  obtain ⟨zs, hm⟩ := maximizer_exists hS θ z₀ hz₀
  obtain ⟨zs', hm'⟩ := maximizer_exists hS θ' z₀ hz₀
  rw [(gradient_at_maximizer hS hz₀ hm).gradient, (gradient_at_maximizer hS hz₀ hm').gradient]
  have hd := maximizer_distance hS hz₀ hm hm'
  have h1 := hS.assumptionB.lip_θz θ zs hm.1 zs' hm'.1
  have h2 := hS.assumptionB.lip_θθ θ θ' zs' hm'.1
  have ht : ‖gθ θ zs-gθ θ' zs'‖ ≤ ‖gθ θ zs-gθ θ zs'‖ + ‖gθ θ zs'-gθ θ' zs'‖ := by
    simpa only [dist_eq_norm] using dist_triangle (gθ θ zs) (gθ θ zs') (gθ θ' zs')
  have h3 := mul_le_mul_of_nonneg_left hd hS.assumptionB.Lθz_nonneg
  dsimp [Lphi]
  simp only [div_eq_mul_inv] at h3 ⊢
  nlinarith

theorem surrogate_oracle_bias_sq (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    {ε : ℝ} (hε : 0 ≤ ε) {zhat : Param d → Data m → Data m}
    (hzhat : IsOracle Z ℓ c γ ε zhat) (θ : Param d) (z₀ : Data m) (hz₀ : z₀ ∈ Z) :
    ‖gθ θ (zhat θ z₀) - gradient (fun p => robustSurrogate Z ℓ c γ p z₀) θ‖ ^ 2 ≤
      2 * Lθz ^ 2 / (γ - Lzz) * ε := by
  have _ := hε
  obtain ⟨zs, hm⟩ := maximizer_exists hS θ z₀ hz₀
  rw [(gradient_at_maximizer hS hz₀ hm).gradient]
  have ho := hzhat θ z₀ hz₀
  have hgap := maximizer_gap hS hz₀ hm (zhat θ z₀) ho.1
  have happrox := ho.2
  rw [maximizer_value hm] at happrox
  have hg := hS.assumptionB.lip_θz θ (zhat θ z₀) ho.1 zs hm.1
  have hs := sq_le_sq₀ (norm_nonneg (gθ θ (zhat θ z₀) - gθ θ zs))
    (mul_nonneg hS.assumptionB.Lθz_nonneg (norm_nonneg (zhat θ z₀-zs)))
  have hs' := hs.mpr hg
  have ha : 0 < γ-Lzz := sub_pos.mpr hS.gamma_gt
  have hr : ‖zhat θ z₀-zs‖^2 ≤ 2*ε/(γ-Lzz) := by
    apply (le_div_iff₀ ha).2
    linarith [happrox]
  have hr' := mul_le_mul_of_nonneg_left hr (sq_nonneg Lθz)
  simp only [div_eq_mul_inv] at hr' ⊢
  nlinarith

theorem loss_gradient_continuous (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ) :
    Continuous (fun p : Param d × Z => gθ p.1 p.2) := by
  let K : ℝ≥0 := ⟨Lθθ+Lθz, add_nonneg hS.assumptionB.Lθθ_nonneg hS.assumptionB.Lθz_nonneg⟩
  have h : LipschitzWith K (fun p : Param d × Z => gθ p.1 p.2) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    have h1 := hS.assumptionB.lip_θθ p.1 q.1 p.2 p.2.property
    have h2 := hS.assumptionB.lip_θz q.1 p.2 p.2.property q.2 q.2.property
    have h3 : ‖gθ p.1 p.2-gθ q.1 q.2‖ ≤
        ‖gθ p.1 p.2-gθ q.1 p.2‖ + ‖gθ q.1 p.2-gθ q.1 q.2‖ := by
      simpa only [dist_eq_norm] using dist_triangle (gθ p.1 p.2) (gθ q.1 p.2) (gθ q.1 q.2)
    have hf : dist p.1 q.1 ≤ dist p q := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    have hs : dist p.2 q.2 ≤ dist p q := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    simp only [dist_eq_norm, Subtype.dist_eq] at hf hs ⊢
    have h4 := mul_le_mul_of_nonneg_left hf hS.assumptionB.Lθθ_nonneg
    have h5 := mul_le_mul_of_nonneg_left hs hS.assumptionB.Lθz_nonneg
    change ‖gθ p.1 p.2-gθ q.1 q.2‖ ≤ (Lθθ+Lθz)*dist p q
    nlinarith
  exact h.continuous

end CertDROProof

open Set
open scoped InnerProductSpace

namespace CertDROProof

theorem biased_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (F : E → ℝ) (G : E → E) (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (α : ℝ) (hα : 0 ≤ α) (hstep : L * α ≤ 1) (θ u v : E) :
    F (θ - α • v) ≤ F θ - α / 2 * ‖G θ‖ ^ 2 +
      α * (1 - L * α) * inner ℝ (G θ) (G θ - u) +
      α * ‖v - u‖ ^ 2 + L * α ^ 2 * ‖u - G θ‖ ^ 2 := by
  have hm := smooth_upper_on univ convex_univ F G L hL (fun x _ => hF x)
    (fun x _ y _ => hG x y) θ (θ - α • v) (mem_univ _) (mem_univ _)
  have he : θ - α • v - θ = -(α • v) := by module
  rw [he] at hm
  simp only [inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hα] at hm
  have hpos : 0 ≤ α/2 * ((1-L*α)*‖G θ+(v-u)‖^2 +
      (L*α)*‖(u-G θ)-(v-u)‖^2 + (1-L*α)*‖v-u‖^2) := by
    exact mul_nonneg (div_nonneg hα (by norm_num)) (add_nonneg
      (add_nonneg (mul_nonneg (sub_nonneg.mpr hstep) (sq_nonneg _))
        (mul_nonneg (mul_nonneg hL hα) (sq_nonneg _)))
      (mul_nonneg (sub_nonneg.mpr hstep) (sq_nonneg _)))
  have hid : α/2 * ((1-L*α)*‖G θ+(v-u)‖^2 +
      (L*α)*‖(u-G θ)-(v-u)‖^2 + (1-L*α)*‖v-u‖^2) =
      -α/2*‖G θ‖^2 + α*(1-L*α)*inner ℝ (G θ) (G θ-u) +
      α*‖v-u‖^2 + L*α^2*‖u-G θ‖^2 + α*inner ℝ (G θ) v -
      L/2*(α*‖v‖)^2 := by
    simp only [norm_add_sq_real, norm_sub_sq_real,
      inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    simp only [real_inner_comm u (G θ), real_inner_comm v (G θ), real_inner_comm v u]
    ring
  rw [hid] at hpos
  linarith

end CertDROProof

open MeasureTheory Filter Topology Set
open CertDRO.SGD
open scoped ENNReal NNReal InnerProductSpace

namespace CertDROProof

theorem gradient_aestronglyMeasurable {d m : ℕ}
    (P : Measure (Data m)) (φ : Param d → Data m → ℝ) (U : Param d → Data m → Param d)
    (hm : ∀ θ, AEStronglyMeasurable (φ θ) P)
    (hd : ∀ᵐ z ∂P, ∀ θ, HasGradientAt (fun p => φ p z) (U θ z) θ) (θ : Param d) :
    AEStronglyMeasurable (U θ) P := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hc : ∀ i : Fin d, AEStronglyMeasurable (fun z => inner ℝ (U θ z) (b i)) P := by
    intro i
    let q : ℕ → Data m → ℝ := fun n z =>
      ((n : ℝ) + 1) * (φ (θ + (1 / ((n : ℝ) + 1)) • b i) z - φ θ z)
    apply aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := q)
    · intro n
      exact ((hm _).sub (hm θ)).const_mul _
    · filter_upwards [hd] with z hz
      have hp : HasDerivAt (fun r : ℝ => θ + r • b i) (b i) 0 := by
        convert! (hasDerivAt_const (0 : ℝ) θ).add ((hasDerivAt_id (0 : ℝ)).smul_const (b i)) using 1
        simp
      have hh : HasDerivAt (fun r : ℝ => φ (θ + r • b i) z) (inner ℝ (U θ z) (b i)) 0 := by
        have hh := (hz (θ + (0 : ℝ) • b i)).hasFDerivAt.comp_hasDerivAt 0 hp
        convert! hh using 1
        simp
      have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
        tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
          Filter.Eventually.of_forall fun n => by
            change 0 < 1 / ((n : ℝ) + 1)
            positivity⟩
      simpa [q, one_div, smul_eq_mul, Function.comp_def] using hh.tendsto_slope_zero_right.comp ht
  have hsum : AEStronglyMeasurable (fun z => ∑ i, inner ℝ (U θ z) (b i) • b i) P := by
    convert! Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => (hc i).smul_const (b i)) using 1
    funext z
    simp only [Finset.sum_apply]
  convert! hsum using 1
  funext z
  simpa only [real_inner_comm] using (b.sum_repr' (U θ z)).symm

theorem variance_moments {d m : ℕ} (P : Measure (Data m)) [IsProbabilityMeasure P]
    (U : Data m → Param d) (G : Param d) (σ : ℝ)
    (hm : AEStronglyMeasurable U P)
    (hv : (∫⁻ z, ENNReal.ofReal (‖G - U z‖ ^ 2) ∂P) ≤ ENNReal.ofReal (σ ^ 2)) :
    Integrable U P ∧ Integrable (fun z => ‖U z‖ ^ 2) P ∧
      Integrable (fun z => ‖G - U z‖ ^ 2) P ∧ (∫ z, ‖G - U z‖ ^ 2 ∂P) ≤ σ ^ 2 := by
  have hd : AEStronglyMeasurable (fun z => G - U z) P := aestronglyMeasurable_const.sub hm
  have hsq : Integrable (fun z => ‖G - U z‖ ^ 2) P :=
    ⟨hd.norm.pow 2, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => sq_nonneg _)).2
      (lt_of_le_of_lt hv ENNReal.ofReal_lt_top)⟩
  have hdiff : MemLp (fun z => G - U z) 2 P := (memLp_two_iff_integrable_sq_norm hd).2 hsq
  have hu : MemLp U 2 P := by
    have h := (memLp_const G (p := (2 : ℝ≥0∞)) (μ := P)).sub hdiff
    convert! h using 1
    funext z
    change U z = G - (G - U z)
    abel
  have hb : (∫ z, ‖G - U z‖ ^ 2 ∂P) ≤ σ ^ 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg σ)).mp
    rwa [ofReal_integral_eq_lintegral_ofReal hsq (Filter.Eventually.of_forall fun z => sq_nonneg _)]
  exact ⟨MemLp.integrable (by norm_num) hu, (memLp_two_iff_integrable_sq_norm hm).1 hu, hsq, hb⟩

theorem norm_sq_add_bound {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have hp := mul_nonneg (sub_nonneg.mpr h) (add_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y)) (norm_nonneg (x + y)))
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

variable {d m : ℕ} {Z : Set (Data m)} {c : Data m → Data m → ℝ}
  {ℓ : Param d → Data m → ℝ} {gθ : Param d → Data m → Param d}
  {gz : Param d → Data m → Data m} {Lθθ Lzz Lθz Lzθ γ : ℝ}

theorem objective_facts
    (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (P₀ : Measure (Data m)) [IsProbabilityMeasure P₀]
    (hP₀ : P₀ Zᶜ = 0)
    (hint : ∀ θ, Integrable (fun z => robustSurrogate Z ℓ c γ θ z) P₀)
    (σ : ℝ)
    (hvar : ∀ θ, ∫⁻ z, ENNReal.ofReal (‖gradient (robustObjective Z ℓ c γ P₀) θ -
      gradient (fun p => robustSurrogate Z ℓ c γ p z) θ‖ ^ 2) ∂P₀ ≤
      ENNReal.ofReal (σ ^ 2)) :
    (∀ θ, HasGradientAt (robustObjective Z ℓ c γ P₀)
      (gradient (robustObjective Z ℓ c γ P₀) θ) θ) ∧
    (∀ θ, Integrable (fun z => gradient (fun p => robustSurrogate Z ℓ c γ p z) θ) P₀ ∧
      gradient (robustObjective Z ℓ c γ P₀) θ =
        ∫ z, gradient (fun p => robustSurrogate Z ℓ c γ p z) θ ∂P₀) ∧
    (∀ θ θ', ‖gradient (robustObjective Z ℓ c γ P₀) θ -
      gradient (robustObjective Z ℓ c γ P₀) θ'‖ ≤
      Lphi Lθθ Lzz Lθz Lzθ γ * ‖θ - θ'‖) := by
  let U : Param d → Data m → Param d := fun θ z => gradient (fun p => robustSurrogate Z ℓ c γ p z) θ
  let F := robustObjective Z ℓ c γ P₀
  let L := Lphi Lθθ Lzz Lθz Lzθ γ
  have hL : 0 ≤ L := lphi_nonneg hS
  have hz : ∀ᵐ z ∂P₀, z ∈ Z := ae_iff.mpr hP₀
  have hd : ∀ᵐ z ∂P₀, ∀ θ, HasGradientAt (fun p => robustSurrogate Z ℓ c γ p z) (U θ z) θ :=
    hz.mono fun z h θ => surrogate_hasGradient hS θ z h
  have hm : ∀ θ, AEStronglyMeasurable (U θ) P₀ := fun θ =>
    gradient_aestronglyMeasurable P₀ _ U (fun p => (hint p).aestronglyMeasurable) hd θ
  have hi : ∀ θ, Integrable (U θ) P₀ := fun θ =>
    (variance_moments P₀ (U θ) (gradient F θ) σ (hm θ) (hvar θ)).1
  have hder : ∀ θ, HasGradientAt F (∫ z, U θ z ∂P₀) θ := by
    intro θ
    have hbound : ∀ᵐ z ∂P₀, ∀ p ∈ Metric.ball θ 1,
        ‖(InnerProductSpace.toDual ℝ (Param d)) (U p z)‖ ≤ ‖U θ z‖ + L := by
      filter_upwards [hz] with z hzz p hp
      have hl := surrogate_gradient_lipschitz hS p θ z hzz
      have hn : ‖p - θ‖ ≤ 1 := (Metric.mem_ball.mp hp).le
      have hn' := norm_sub_le (U p z - U θ z) (-U θ z)
      have htri : ‖U p z‖ ≤ ‖U p z - U θ z‖ + ‖U θ z‖ := by
        simpa only [sub_neg_eq_add, sub_add_cancel, norm_neg] using hn'
      have hmL := mul_le_mul_of_nonneg_left hn hL
      simpa only [LinearIsometryEquiv.norm_map] using (show ‖U p z‖ ≤ ‖U θ z‖ + L by linarith)
    have ht := hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun θ z => robustSurrogate Z ℓ c γ θ z)
      (F' := fun θ z => (InnerProductSpace.toDual ℝ (Param d)) (U θ z))
      (Metric.ball_mem_nhds θ (by norm_num : (0 : ℝ) < 1))
      (Filter.Eventually.of_forall fun p => (hint p).aestronglyMeasurable) (hint θ)
      ((InnerProductSpace.toDual ℝ (Param d)).continuous.comp_aestronglyMeasurable (hm θ))
      hbound ((hi θ).norm.add (integrable_const L))
      (hd.mono fun z h p _ => (h p).hasFDerivAt)
    change HasFDerivAt F ((InnerProductSpace.toDual ℝ (Param d)) (∫ z, U θ z ∂P₀)) θ
    have he : (∫ z, (InnerProductSpace.toDual ℝ (Param d)) (U θ z) ∂P₀) =
        (InnerProductSpace.toDual ℝ (Param d)) (∫ z, U θ z ∂P₀) :=
      (InnerProductSpace.toDual ℝ (Param d)).toLinearIsometry.integral_comp_comm (U θ)
    rw [he] at ht
    exact ht
  have hmean : ∀ θ, gradient F θ = ∫ z, U θ z ∂P₀ := fun θ => (hder θ).gradient
  refine ⟨fun θ => by rw [hmean θ]; exact hder θ, fun θ => ⟨hi θ, hmean θ⟩, ?_⟩
  intro θ θ'
  rw [hmean θ, hmean θ', ← integral_sub (hi θ) (hi θ')]
  calc
    _ ≤ ∫ z, ‖U θ z - U θ' z‖ ∂P₀ := norm_integral_le_integral_norm _
    _ ≤ ∫ _, L * ‖θ - θ'‖ ∂P₀ := integral_mono_ae ((hi θ).sub (hi θ')).norm
      (integrable_const _) (hz.mono fun z h => surrogate_gradient_lipschitz hS θ θ' z h)
    _ = _ := by simp [L]

end CertDROProof

open MeasureTheory Filter Topology Set
open CertDRO.SGD
open scoped ENNReal NNReal InnerProductSpace

namespace CertDROProof

variable {d m : ℕ} {Z : Set (Data m)} {c : Data m → Data m → ℝ}
  {ℓ : Param d → Data m → ℝ} {gθ : Param d → Data m → Param d}
  {gz : Param d → Data m → Data m} {Lθθ Lzz Lθz Lzθ γ : ℝ}

theorem measurable_oracle_version
    (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    {ε : ℝ} {zhat : Param d → Data m → Data m}
    (hzhat : IsOracle Z ℓ c γ ε zhat)
    (hzhat_meas : Measurable (Function.uncurry zhat)) :
    ∃ Ghat : Param d → Data m → Param d,
      Measurable (Function.uncurry Ghat) ∧
      ∀ θ z, z ∈ Z → Ghat θ z = gθ θ (zhat θ z) := by
  classical
  obtain ⟨zbar, hzbar⟩ := hS.nonempty
  let clip : Param d × Data m → Data m := fun p => if zhat p.1 p.2 ∈ Z then zhat p.1 p.2 else zbar
  have hm : Measurable clip := hzhat_meas.piecewise
    (hS.closed.measurableSet.preimage hzhat_meas) measurable_const
  have hc : ∀ p, clip p ∈ Z := by
    intro p
    dsimp [clip]
    split_ifs with h
    · exact h
    · exact hzbar
  refine ⟨fun θ z => gθ θ (clip (θ,z)), ?_, ?_⟩
  · exact (loss_gradient_continuous hS).measurable.comp (measurable_fst.prodMk (hm.subtype_mk (h := hc)))
  · intro θ z hz
    simp [clip, (hzhat θ z hz).1]

theorem function_quadratic_bound {d : ℕ} (F : Param d → ℝ) (G : Param d → Param d)
    (L : ℝ) (hL : 0 ≤ L) (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ x, ‖F x‖ ≤ A * ‖x‖ ^ 2 + C := by
  refine ⟨L / 2 + ‖G 0‖ / 2, |F 0| + ‖G 0‖ / 2, by positivity, by positivity, ?_⟩
  intro x
  have hm := smooth_model_on Set.univ convex_univ F G L hL
    (fun y _ => hF y) (fun y _ z _ => hG y z) 0 x (mem_univ _) (mem_univ _)
  simp only [sub_zero] at hm
  have hi := abs_real_inner_le_norm (G 0) x
  have hx := abs_le.mp hm
  have hp := mul_nonneg (norm_nonneg (G 0)) (sq_nonneg (‖x‖ - 1))
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [le_abs_self (F 0), neg_abs_le (F 0), (abs_le.mp hi).1, (abs_le.mp hi).2]

theorem gradient_quadratic_bound {d : ℕ} (G : Param d → Param d)
    (L : ℝ) (hL : 0 ≤ L) (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ x, ‖G x‖ ^ 2 ≤ A * ‖x‖ ^ 2 + C := by
  refine ⟨2 * L ^ 2, 2 * ‖G 0‖ ^ 2, by positivity, by positivity, ?_⟩
  intro x
  have hl := hG x 0
  simp only [sub_zero] at hl
  have hs : ‖G x - G 0‖ ^ 2 ≤ (L * ‖x‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).2 hl
  have hn := norm_sq_add_bound (G x - G 0) (G 0)
  simp only [sub_add_cancel] at hn
  nlinarith

theorem oracle_moments {d m : ℕ}
    (P : Measure (Data m)) [IsProbabilityMeasure P]
    (U V : Data m → Param d) (G : Param d) (σ B : ℝ)
    (hU : AEStronglyMeasurable U P) (hV : AEStronglyMeasurable V P)
    (hvar : (∫⁻ z, ENNReal.ofReal (‖G - U z‖ ^ 2) ∂P) ≤ ENNReal.ofReal (σ ^ 2))
    (hbias : ∀ᵐ z ∂P, ‖V z - U z‖ ^ 2 ≤ B) :
    Integrable V P ∧ Integrable (fun z => ‖V z‖ ^ 2) P ∧
      (∫ z, ‖V z‖ ^ 2 ∂P) ≤ 4 * ‖G‖ ^ 2 + 4 * σ ^ 2 + 2 * B := by
  obtain ⟨hiU, hsU, hv, hvb⟩ := variance_moments P U G σ hU hvar
  have hbi : Integrable (fun z => ‖V z - U z‖ ^ 2) P :=
    (integrable_const B).mono' ((hV.sub hU).norm.pow 2)
      (hbias.mono fun z h => by simpa only [Real.norm_eq_abs, abs_sq] using h)
  have hvlp : MemLp V 2 P := by
    have h := ((memLp_two_iff_integrable_sq_norm (hV.sub hU)).2 hbi).add
      ((memLp_two_iff_integrable_sq_norm hU).2 hsU)
    convert! h using 1
    funext z
    simp
  have hvs := (memLp_two_iff_integrable_sq_norm hV).1 hvlp
  have hbb : (∫ z, ‖V z - U z‖ ^ 2 ∂P) ≤ B := by
    simpa using integral_mono_ae hbi (integrable_const B) hbias
  have hpoint : ∀ z, ‖V z‖ ^ 2 ≤ 4 * ‖G‖ ^ 2 + 4 * ‖G - U z‖ ^ 2 + 2 * ‖V z - U z‖ ^ 2 := by
    intro z
    have h₁ := norm_sq_add_bound (V z - U z) (U z)
    have h₂ := norm_sq_add_bound (G - U z) (-G)
    simp only [sub_add_cancel] at h₁
    have he : G - U z + -G = -U z := by abel
    rw [he, norm_neg, norm_neg] at h₂
    linarith
  have hInt := integral_mono_ae hvs
    (((integrable_const (4 * ‖G‖ ^ 2)).add (hv.const_mul 4)).add (hbi.const_mul 2))
    (Filter.Eventually.of_forall hpoint)
  have hci : Integrable (fun z => 4 * ‖G‖ ^ 2 + 4 * ‖G - U z‖ ^ 2) P :=
    (integrable_const _).add (hv.const_mul 4)
  simp only [Pi.add_apply] at hInt
  rw [integral_add hci (hbi.const_mul 2),
    integral_add (integrable_const (4 * ‖G‖ ^ 2)) (hv.const_mul 4)] at hInt
  simp only [integral_const_mul] at hInt
  simp at hInt
  exact ⟨MemLp.integrable (by norm_num) hvlp, hvs, by linarith⟩

theorem fixed_state_descent {d m : ℕ}
    (P : Measure (Data m)) [IsProbabilityMeasure P]
    (F : Param d → ℝ) (G : Param d → Param d) (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (θ : Param d) (U V : Data m → Param d) (σ B α : ℝ)
    (hα : 0 ≤ α) (hstep : L * α ≤ 1)
    (hU : AEStronglyMeasurable U P) (hV : AEStronglyMeasurable V P)
    (hmean : G θ = ∫ z, U z ∂P)
    (hvar : (∫⁻ z, ENNReal.ofReal (‖G θ - U z‖ ^ 2) ∂P) ≤ ENNReal.ofReal (σ ^ 2))
    (hbias : ∀ᵐ z ∂P, ‖V z - U z‖ ^ 2 ≤ B) :
    Integrable (fun z => F (θ - α • V z)) P ∧
      (∫ z, F (θ - α • V z) ∂P) ≤ F θ - α / 2 * ‖G θ‖ ^ 2 + α * B + L * α ^ 2 * σ ^ 2 := by
  obtain ⟨hiU, hsU, hv, hvb⟩ := variance_moments P U (G θ) σ hU hvar
  obtain ⟨hiV, hsV, _⟩ := oracle_moments P U V (G θ) σ B hU hV hvar hbias
  have hbi : Integrable (fun z => ‖V z - U z‖ ^ 2) P :=
    (integrable_const B).mono' ((hV.sub hU).norm.pow 2)
      (hbias.mono fun z h => by simpa only [Real.norm_eq_abs, abs_sq] using h)
  have hstepLp : MemLp (fun z => θ - α • V z) 2 P :=
    (memLp_const θ).sub (((memLp_two_iff_integrable_sq_norm hV).2 hsV).const_smul α)
  have hstepSq := (memLp_two_iff_integrable_sq_norm hstepLp.aestronglyMeasurable).1 hstepLp
  obtain ⟨A, C, _, _, hquad⟩ := function_quadratic_bound F G L hL hF hG
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).differentiableAt.continuousAt
  have hfi : Integrable (fun z => F (θ - α • V z)) P :=
    ((hstepSq.const_mul A).add (integrable_const C)).mono'
      (hcF.comp_aestronglyMeasurable hstepLp.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => hquad _)
  have hiInner : Integrable (fun z => inner ℝ (G θ) (G θ - U z)) P :=
    ((integrable_const (G θ)).sub hiU).const_inner (G θ)
  have hzero : (∫ z, inner ℝ (G θ) (G θ - U z) ∂P) = 0 := by
    have hi : Integrable (fun z => G θ - U z) P := (integrable_const (G θ)).sub hiU
    rw [integral_inner (𝕜 := ℝ) hi (G θ), integral_sub (integrable_const (G θ)) hiU]
    simp [← hmean]
  have hv' : Integrable (fun z => ‖U z - G θ‖ ^ 2) P := by
    simpa only [norm_sub_rev] using hv
  have hbb : (∫ z, ‖V z - U z‖ ^ 2 ∂P) ≤ B := by
    simpa using integral_mono_ae hbi (integrable_const B) hbias
  have hbound := integral_mono_ae hfi
    ((((integrable_const (F θ - α / 2 * ‖G θ‖ ^ 2)).add
      (hiInner.const_mul (α * (1 - L * α)))).add (hbi.const_mul α)).add
      (hv'.const_mul (L * α ^ 2)))
    (Filter.Eventually.of_forall fun z => biased_descent F G L hL hF hG α hα hstep θ (U z) (V z))
  have hi₀ : Integrable (fun z => F θ - α / 2 * ‖G θ‖ ^ 2 +
      α * (1 - L * α) * inner ℝ (G θ) (G θ - U z)) P :=
    (integrable_const _).add (hiInner.const_mul _)
  have hi₁ : Integrable (fun z => F θ - α / 2 * ‖G θ‖ ^ 2 +
      α * (1 - L * α) * inner ℝ (G θ) (G θ - U z) + α * ‖V z - U z‖ ^ 2) P :=
    hi₀.add (hbi.const_mul α)
  simp only [Pi.add_apply] at hbound
  rw [integral_add hi₁ (hv'.const_mul (L * α ^ 2)), integral_add hi₀ (hbi.const_mul α),
    integral_add (integrable_const _) (hiInner.const_mul _)] at hbound
  simp only [integral_const_mul, hzero, mul_zero, add_zero] at hbound
  simp at hbound
  have hvb' : (∫ z, ‖U z - G θ‖ ^ 2 ∂P) ≤ σ ^ 2 := by
    simpa only [norm_sub_rev] using hvb
  refine ⟨hfi, ?_⟩
  have h₁ := mul_le_mul_of_nonneg_left hbb hα
  have h₂ := mul_le_mul_of_nonneg_left hvb' (mul_nonneg hL (sq_nonneg α))
  linarith

end CertDROProof

open MeasureTheory Filter Topology Set
open CertDRO.SGD
open scoped ENNReal NNReal InnerProductSpace

namespace CertDROProof

noncomputable def prefixRun {d m : ℕ} (step : Param d → Data m → Param d)
    (x₀ : Param d) : (n : ℕ) → (Fin n → Data m) → Param d
  | 0, _ => x₀
  | n + 1, ω => step (prefixRun step x₀ n (fun i => ω i.castSucc)) (ω (Fin.last n))

theorem prefix_measurable {d m : ℕ} (step : Param d → Data m → Param d)
    (hs : Measurable (Function.uncurry step)) (x₀ : Param d) (n : ℕ) :
    Measurable (prefixRun step x₀ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact hs.comp ((ih.comp (measurable_pi_lambda _ fun i => measurable_pi_apply i.castSucc)).prodMk
      (measurable_pi_apply (Fin.last n)))

theorem last_deletion_preserving {m : ℕ} (P : Measure (Data m))
    [IsProbabilityMeasure P] (n : ℕ) :
    MeasurePreserving (fun ω : Fin (n + 1) → Data m => fun i : Fin n => ω i.castSucc)
      (Measure.pi fun _ => P) (Measure.pi fun _ => P) := by
  have h := (measurePreserving_snd (μ := P) (ν := Measure.pi fun _ : Fin n => P)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) (Fin.last n))
  convert! h using 1
  funext ω
  funext i
  simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_apply]
  simp [Fin.insertNthEquiv]
  rfl

theorem prefix_preserving {m : ℕ} (P : Measure (Data m)) [IsProbabilityMeasure P]
    {n N : ℕ} (h : n ≤ N) :
    MeasurePreserving (fun ω : Fin N → Data m => fun i : Fin n => ω (i.castLE h))
      (Measure.pi fun _ => P) (Measure.pi fun _ => P) := by
  induction N generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    convert! MeasurePreserving.id (Measure.pi fun _ : Fin 0 => P) using 1
  | succ N ih =>
    by_cases heq : n = N + 1
    · subst n
      convert! MeasurePreserving.id (Measure.pi fun _ : Fin (N + 1) => P) using 1
    · have hn : n ≤ N := by omega
      convert! (ih hn).comp (last_deletion_preserving P N) using 1

theorem prefix_square_integrable {d m : ℕ}
    (P : Measure (Data m)) [IsProbabilityMeasure P]
    (step : Param d → Data m → Param d) (hs : Measurable (Function.uncurry step))
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hi : ∀ x, Integrable (fun z => ‖step x z‖ ^ 2) P)
    (hb : ∀ x, (∫ z, ‖step x z‖ ^ 2 ∂P) ≤ A * ‖x‖ ^ 2 + C)
    (x₀ : Param d) (n : ℕ) :
    Integrable (fun ω => ‖prefixRun step x₀ n ω‖ ^ 2) (Measure.pi fun _ => P) := by
  have _ := hA
  have _ := hC
  induction n with
  | zero =>
    change Integrable (fun _ : Fin 0 → Data m => ‖x₀‖ ^ 2) (Measure.pi fun _ => P)
    exact integrable_const _
  | succ n ih =>
    let f : Data m × (Fin n → Data m) → ℝ :=
      fun q => ‖step (prefixRun step x₀ n q.2) q.1‖ ^ 2
    have hm : Measurable f :=
      (hs.comp (((prefix_measurable step hs x₀ n).comp measurable_snd).prodMk measurable_fst)).norm.pow_const 2
    have ho : Integrable (fun ω => ∫ z, ‖f (z, ω)‖ ∂P) (Measure.pi fun _ => P) := by
      have ha : AEStronglyMeasurable (fun ω => ∫ z, ‖f (z, ω)‖ ∂P) (Measure.pi fun _ => P) :=
        ((hm.comp measurable_swap).aestronglyMeasurable (μ := (Measure.pi fun _ : Fin n => P).prod P)).norm.integral_prod_right'
      apply ((ih.const_mul A).add (integrable_const C)).mono' ha
      filter_upwards [] with ω
      change ‖∫ z, ‖‖step (prefixRun step x₀ n ω) z‖ ^ 2‖ ∂P‖ ≤ A * ‖prefixRun step x₀ n ω‖ ^ 2 + C
      simp only [Real.norm_eq_abs, abs_sq]
      rw [abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      exact hb _
    have hf : Integrable f (P.prod (Measure.pi fun _ : Fin n => P)) :=
      (integrable_prod_iff' hm.aestronglyMeasurable).2
        ⟨Filter.Eventually.of_forall fun ω => hi (prefixRun step x₀ n ω), ho⟩
    have ht := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P)
      (Fin.last n)).integrable_comp_of_integrable hf
    convert! ht using 1
    funext ω
    simp [f, prefixRun, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
    rfl

theorem quadratic_comp_integrable {d m : ℕ}
    {P : Measure (Data m)} [IsProbabilityMeasure P]
    {step : Param d → Data m → Param d} (hs : Measurable (Function.uncurry step))
    (x₀ : Param d) (n : ℕ)
    (hi : Integrable (fun ω => ‖prefixRun step x₀ n ω‖ ^ 2) (Measure.pi fun _ => P))
    (f : Param d → ℝ) (hf : Measurable f) (A C : ℝ)
    (hb : ∀ x, ‖f x‖ ≤ A * ‖x‖ ^ 2 + C) :
    Integrable (fun ω => f (prefixRun step x₀ n ω)) (Measure.pi fun _ => P) := by
  apply ((hi.const_mul A).add (integrable_const C)).mono'
    (hf.comp (prefix_measurable step hs x₀ n)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => hb _

theorem prefix_descent {d m : ℕ}
    (P : Measure (Data m)) [IsProbabilityMeasure P]
    (step : Param d → Data m → Param d) (x₀ : Param d)
    (F H : Param d → ℝ) (α D : ℝ)
    (hF : ∀ n, Integrable (fun ω => F (prefixRun step x₀ n ω)) (Measure.pi fun _ => P))
    (hH : ∀ n, Integrable (fun ω => H (prefixRun step x₀ n ω)) (Measure.pi fun _ => P))
    (hstep : ∀ x, (∫ z, F (step x z) ∂P) ≤ F x - α * H x + D) (n : ℕ) :
    (∫ ω, F (prefixRun step x₀ (n + 1) ω) ∂(Measure.pi fun _ => P)) ≤
      (∫ ω, F (prefixRun step x₀ n ω) ∂(Measure.pi fun _ => P)) -
        α * (∫ ω, H (prefixRun step x₀ n ω) ∂(Measure.pi fun _ => P)) + D := by
  let f : Data m × (Fin n → Data m) → ℝ := fun q => F (step (prefixRun step x₀ n q.2) q.1)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Data m) (Fin.last n)
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) (Fin.last n)
  have hid : f ∘ e = fun ω => F (prefixRun step x₀ (n + 1) ω) := by
    funext ω
    change F (step (prefixRun step x₀ n ((e ω).2)) ((e ω).1)) = _
    congr 2
    · congr 1
      funext i
      simp [e, MeasurableEquiv.piFinSuccAbove]
      rfl
  have hf : Integrable f (P.prod (Measure.pi fun _ : Fin n => P)) :=
    (hp.integrable_comp_emb e.measurableEmbedding).mp (hid.symm ▸ hF (n + 1))
  calc
    _ = ∫ q, f q ∂(P.prod (Measure.pi fun _ : Fin n => P)) := by
      rw [← hid]
      exact hp.integral_comp' f
    _ = ∫ ω, ∫ z, f (z, ω) ∂P ∂(Measure.pi fun _ : Fin n => P) := integral_prod_symm _ hf
    _ ≤ ∫ ω, (F (prefixRun step x₀ n ω) - α * H (prefixRun step x₀ n ω) + D)
        ∂(Measure.pi fun _ : Fin n => P) := by
      exact integral_mono_ae hf.integral_prod_right
        (((hF n).sub ((hH n).const_mul α)).add (integrable_const D))
        (Filter.Eventually.of_forall fun ω => hstep (prefixRun step x₀ n ω))
    _ = _ := by
      have hb : Integrable (fun ω => F (prefixRun step x₀ n ω) - α * H (prefixRun step x₀ n ω))
          (Measure.pi fun _ => P) := (hF n).sub ((hH n).const_mul α)
      rw [integral_add hb (integrable_const D), integral_sub (hF n) ((hH n).const_mul α),
        integral_const_mul]
      simp

end CertDROProof

open MeasureTheory Filter Topology Set
open CertDRO.SGD
open scoped ENNReal NNReal InnerProductSpace

namespace CertDROProof

variable {d m : ℕ} {Z : Set (Data m)} {c : Data m → Data m → ℝ}
  {ℓ : Param d → Data m → ℝ} {gθ : Param d → Data m → Param d}
  {gz : Param d → Data m → Data m} {Lθθ Lzz Lθz Lzθ γ : ℝ}

theorem sgd_average_bound
    (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (P₀ : Measure (Data m)) [IsProbabilityMeasure P₀] (hP₀ : P₀ Zᶜ = 0)
    (hint : ∀ θ, Integrable (fun z => robustSurrogate Z ℓ c γ θ z) P₀)
    (ε : ℝ) (hε : 0 ≤ ε) (zhat : Param d → Data m → Data m)
    (hzhat : IsOracle Z ℓ c γ ε zhat)
    (hzhat_meas : Measurable (Function.uncurry zhat))
    (σ : ℝ) (hσ : 0 < σ)
    (hvar : ∀ θ, ∫⁻ z, ENNReal.ofReal (‖gradient (robustObjective Z ℓ c γ P₀) θ -
      gradient (fun p => robustSurrogate Z ℓ c γ p z) θ‖ ^ 2) ∂P₀ ≤
      ENNReal.ofReal (σ ^ 2))
    (θ₀ : Param d) (ΔF : ℝ) (hΔF_pos : 0 < ΔF)
    (hbdd : BddBelow (Set.range (robustObjective Z ℓ c γ P₀)))
    (hΔF : robustObjective Z ℓ c γ P₀ θ₀ -
      ⨅ θ, robustObjective Z ℓ c γ P₀ θ ≤ ΔF)
    (T : ℕ) (hT : 0 < T) (α : ℝ) (hα : 0 < α)
    (hαL : Lphi Lθθ Lzz Lθz Lzθ γ * α ≤ 1) :
    (T : ENNReal)⁻¹ * ∑ t ∈ Finset.range T,
      ∫⁻ ω, ENNReal.ofReal (‖gradient (robustObjective Z ℓ c γ P₀)
        (run gθ zhat α θ₀ ω t)‖ ^ 2) ∂(Measure.pi fun _ : Fin T => P₀) ≤
    ENNReal.ofReal (4 * Lθz ^ 2 / (γ - Lzz) * ε +
      2 * ΔF / (α * T) + 2 * Lphi Lθθ Lzz Lθz Lzθ γ * α * σ ^ 2) := by
  have _ := hσ
  have _ := hΔF_pos
  let F := robustObjective Z ℓ c γ P₀
  let G := gradient F
  let L := Lphi Lθθ Lzz Lθz Lzθ γ
  let B := 2 * Lθz ^ 2 / (γ - Lzz) * ε
  let U : Param d → Data m → Param d := fun θ z => gradient (fun p => robustSurrogate Z ℓ c γ p z) θ
  have hL : 0 ≤ L := lphi_nonneg hS
  have hB : 0 ≤ B := mul_nonneg (div_nonneg (by positivity) (sub_pos.mpr hS.gamma_gt).le) hε
  have hz : ∀ᵐ z ∂P₀, z ∈ Z := ae_iff.mpr hP₀
  obtain ⟨hF, hmean, hG⟩ := objective_facts hS P₀ hP₀ hint σ hvar
  obtain ⟨V, hVm, hVeq⟩ := measurable_oracle_version hS hzhat hzhat_meas
  have hVa : ∀ θ, AEStronglyMeasurable (V θ) P₀ := fun θ =>
    (hVm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hUa : ∀ θ, AEStronglyMeasurable (U θ) P₀ := fun θ => (hmean θ).1.aestronglyMeasurable
  have hbi : ∀ θ, ∀ᵐ z ∂P₀, ‖V θ z - U θ z‖ ^ 2 ≤ B := by
    intro θ
    filter_upwards [hz] with z hzz
    rw [hVeq θ z hzz]
    exact surrogate_oracle_bias_sq hS hε hzhat θ z hzz
  have hvm : ∀ θ, Integrable (V θ) P₀ ∧ Integrable (fun z => ‖V θ z‖ ^ 2) P₀ ∧
      (∫ z, ‖V θ z‖ ^ 2 ∂P₀) ≤ 4 * ‖G θ‖ ^ 2 + 4 * σ ^ 2 + 2 * B := fun θ =>
    oracle_moments P₀ (U θ) (V θ) (G θ) σ B (hUa θ) (hVa θ) (hvar θ) (hbi θ)
  let step : Param d → Data m → Param d := fun θ z => θ - α • V θ z
  have hstepm : Measurable (Function.uncurry step) := measurable_fst.sub (hVm.const_smul α)
  have hsi : ∀ θ, Integrable (fun z => ‖step θ z‖ ^ 2) P₀ := by
    intro θ
    have hmem : MemLp (step θ) 2 P₀ := (memLp_const θ).sub
      (((memLp_two_iff_integrable_sq_norm (hVa θ)).2 (hvm θ).2.1).const_smul α)
    exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
  obtain ⟨Ag, Cg, hAg, hCg, hgb⟩ := gradient_quadratic_bound G L hL hG
  let A := 2 + 8 * α ^ 2 * Ag
  let C := 8 * α ^ 2 * Cg + 8 * α ^ 2 * σ ^ 2 + 4 * α ^ 2 * B
  have hA : 0 ≤ A := by positivity
  have hC : 0 ≤ C := by positivity
  have hsm : ∀ θ, (∫ z, ‖step θ z‖ ^ 2 ∂P₀) ≤ A * ‖θ‖ ^ 2 + C := by
    intro θ
    have hp : ∀ z, ‖step θ z‖ ^ 2 ≤ 2 * ‖θ‖ ^ 2 + 2 * α ^ 2 * ‖V θ z‖ ^ 2 := by
      intro z
      have hh := norm_sq_add_bound θ (-α • V θ z)
      simpa only [step, sub_eq_add_neg, neg_smul, norm_neg, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs, mul_assoc] using hh
    have hh := integral_mono_ae (hsi θ)
      ((integrable_const (2 * ‖θ‖ ^ 2)).add ((hvm θ).2.1.const_mul (2 * α ^ 2)))
      (Filter.Eventually.of_forall hp)
    simp only [Pi.add_apply] at hh
    rw [integral_add (integrable_const (2 * ‖θ‖ ^ 2)) ((hvm θ).2.1.const_mul (2 * α ^ 2))] at hh
    simp only [integral_const_mul] at hh
    simp at hh
    have hvb := mul_le_mul_of_nonneg_left (hvm θ).2.2 (show 0 ≤ 2 * α ^ 2 by positivity)
    have hgg := mul_le_mul_of_nonneg_left (hgb θ) (show 0 ≤ 8 * α ^ 2 by positivity)
    dsimp [A, C]
    nlinarith
  have hsq : ∀ n, Integrable (fun ω => ‖prefixRun step θ₀ n ω‖ ^ 2) (Measure.pi fun _ => P₀) :=
    prefix_square_integrable P₀ step hstepm A C hA hC hsi hsm θ₀
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun θ => (hF θ).differentiableAt.continuousAt
  have hcG : Continuous G := by
    have hl : LipschitzWith (Real.toNNReal L) G := (lipschitzWith_iff_norm_sub_le).2
      (by simpa only [Real.coe_toNNReal L hL] using hG)
    exact hl.continuous
  obtain ⟨Af, Cf, _, _, hfb⟩ := function_quadratic_bound F G L hL hF hG
  have hFi : ∀ n, Integrable (fun ω => F (prefixRun step θ₀ n ω)) (Measure.pi fun _ => P₀) :=
    fun n => quadratic_comp_integrable hstepm θ₀ n (hsq n) F hcF.measurable Af Cf hfb
  have hGi : ∀ n, Integrable (fun ω => ‖G (prefixRun step θ₀ n ω)‖ ^ 2) (Measure.pi fun _ => P₀) := by
    intro n
    apply quadratic_comp_integrable hstepm θ₀ n (hsq n) (fun θ => ‖G θ‖ ^ 2)
      (hcG.measurable.norm.pow_const 2) Ag Cg
    intro θ
    simpa only [Real.norm_eq_abs, abs_sq] using hgb θ
  let D := α * B + L * α ^ 2 * σ ^ 2
  have hsd : ∀ θ, (∫ z, F (step θ z) ∂P₀) ≤ F θ - α / 2 * ‖G θ‖ ^ 2 + D := fun θ => by
    simpa only [step, D, add_assoc] using (fixed_state_descent P₀ F G L hL hF hG θ (U θ) (V θ) σ B α hα.le hαL
      (hUa θ) (hVa θ) (hmean θ).2 (hvar θ) (hbi θ)).2
  let e : ℕ → ℝ := fun n => ∫ ω, F (prefixRun step θ₀ n ω) ∂(Measure.pi fun _ => P₀)
  let q : ℕ → ℝ := fun n => ∫ ω, ‖G (prefixRun step θ₀ n ω)‖ ^ 2 ∂(Measure.pi fun _ => P₀)
  have hrec : ∀ n, e (n + 1) ≤ e n - α / 2 * q n + D := fun n =>
    prefix_descent P₀ step θ₀ F (fun θ => ‖G θ‖ ^ 2) (α / 2) D hFi hGi hsd n
  have htel : ∀ n, α / 2 * (∑ t ∈ Finset.range n, q t) ≤ F θ₀ - e n + (n : ℝ) * D := by
    intro n
    induction n with
    | zero => simp [e, prefixRun]
    | succ n ih =>
      rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      have hr := hrec n
      nlinarith
  have hlow : (⨅ θ, F θ) ≤ e T := by
    have h := integral_mono_ae (integrable_const (⨅ θ, F θ)) (hFi T)
      (Filter.Eventually.of_forall fun ω => ciInf_le hbdd (prefixRun step θ₀ T ω))
    simpa using h
  have htel' : α / 2 * (∑ t ∈ Finset.range T, q t) ≤ ΔF + (T : ℝ) * D := by
    have hh := htel T
    linarith
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hreal : (T : ℝ)⁻¹ * (∑ t ∈ Finset.range T, q t) ≤
      2 * B + 2 * ΔF / (α * T) + 2 * L * α * σ ^ 2 := by
    calc
      _ = (α / 2 * (∑ t ∈ Finset.range T, q t)) / (α * T / 2) := by field_simp
      _ ≤ (ΔF + (T : ℝ) * D) / (α * T / 2) := div_le_div_of_nonneg_right htel' (by positivity)
      _ = _ := by dsimp [D]; field_simp; ring
  have hrun : ∀ t (ht : t ≤ T) (ω : Fin T → Data m), (∀ i, ω i ∈ Z) →
      run gθ zhat α θ₀ ω t = prefixRun step θ₀ t (fun i => ω (i.castLE ht)) := by
    intro t
    induction t with
    | zero => intros; rfl
    | succ t ih =>
      intro htt ω hω
      have hlt : t < T := by omega
      have hle : t ≤ T := by omega
      calc
        _ = step (run gθ zhat α θ₀ ω t) (ω ⟨t, hlt⟩) := by
          simp only [run, dif_pos hlt, step, hVeq _ _ (hω ⟨t, hlt⟩)]
        _ = _ := by rw [ih hle ω hω]; rfl
  have hω : ∀ᵐ ω ∂(Measure.pi fun _ : Fin T => P₀), ∀ i, ω i ∈ Z :=
    ae_all_iff.mpr fun i => (measurePreserving_eval (fun _ : Fin T => P₀) i).quasiMeasurePreserving.ae hz
  have heq : ∀ t ∈ Finset.range T,
      (∫⁻ ω, ENNReal.ofReal (‖G (run gθ zhat α θ₀ ω t)‖ ^ 2) ∂(Measure.pi fun _ : Fin T => P₀)) =
        ENNReal.ofReal (q t) := by
    intro t htmem
    have hle : t ≤ T := (Finset.mem_range.mp htmem).le
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (‖G (prefixRun step θ₀ t (fun i => ω (i.castLE hle)))‖ ^ 2)
          ∂(Measure.pi fun _ : Fin T => P₀) := lintegral_congr_ae (hω.mono fun ω h => by rw [hrun t hle ω h])
      _ = ∫⁻ ω, ENNReal.ofReal (‖G (prefixRun step θ₀ t ω)‖ ^ 2)
          ∂(Measure.pi fun _ : Fin t => P₀) :=
        (prefix_preserving P₀ hle).lintegral_comp
          (((hcG.measurable.comp (prefix_measurable step hstepm θ₀ t)).norm.pow_const 2).ennreal_ofReal)
      _ = _ := (ofReal_integral_eq_lintegral_ofReal (hGi t)
        (Filter.Eventually.of_forall fun ω => sq_nonneg _)).symm
  have hqn : ∀ t, 0 ≤ q t := fun t => integral_nonneg fun ω => sq_nonneg _
  change (T : ENNReal)⁻¹ * (∑ t ∈ Finset.range T,
    ∫⁻ ω, ENNReal.ofReal (‖G (run gθ zhat α θ₀ ω t)‖ ^ 2)
      ∂(Measure.pi fun _ : Fin T => P₀)) ≤ _
  rw [Finset.sum_congr rfl heq]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => hqn t)]
  rw [← ENNReal.ofReal_natCast T, ← ENNReal.ofReal_inv_of_pos ht, ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
  apply ENNReal.ofReal_le_ofReal
  convert! hreal using 1
  dsimp [B, L]
  ring

end CertDROProof

open MeasureTheory Filter Topology Set
open CertDRO.SGD
open scoped ENNReal NNReal InnerProductSpace

namespace CertDROProof

theorem zero_smooth_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : E → ℝ) (G : E → E) (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ 0 * ‖x - y‖)
    (hbdd : BddBelow (Set.range F)) : ∀ x, G x = 0 := by
  obtain ⟨b, hb⟩ := hbdd
  intro x
  by_contra hn
  have hq : 0 < ‖G x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  let r : ℝ := (F x - b + 1) / ‖G x‖ ^ 2
  have hr : r * ‖G x‖ ^ 2 = F x - b + 1 := div_mul_cancel₀ _ hq.ne'
  have hm := smooth_model_on Set.univ (convex_univ) F G 0 (le_refl 0)
    (fun y _ => hF y) (fun y _ z _ => hG y z) x (x - r • G x) (mem_univ _) (mem_univ _)
  have hl := hb (mem_range_self (x - r • G x))
  simp only [zero_div, zero_mul, sub_sub_cancel_left, inner_neg_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq] at hm
  have hab := abs_le.mp hm
  linarith

theorem balancing_stepsize (L Δ σ : ℝ) (T : ℕ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) (hT : 0 < T)
    (hTL : L * Δ / σ ^ 2 ≤ T) :
    0 < Real.sqrt (Δ / (L * T * σ ^ 2)) ∧
    L * Real.sqrt (Δ / (L * T * σ ^ 2)) ≤ 1 ∧
    2 * Δ / (Real.sqrt (Δ / (L * T * σ ^ 2)) * T) +
      2 * L * Real.sqrt (Δ / (L * T * σ ^ 2)) * σ ^ 2 =
      4 * σ * Real.sqrt (L * Δ / T) := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hsig : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hd : 0 < L * T * σ ^ 2 := by positivity
  let a := Real.sqrt (Δ / (L * T * σ ^ 2))
  have ha : 0 < a := Real.sqrt_pos.2 (div_pos hΔ hd)
  have ha2 : a ^ 2 = Δ / (L * T * σ ^ 2) := Real.sq_sqrt (by positivity)
  have heq : a ^ 2 * (L * T * σ ^ 2) = Δ := (eq_div_iff hd.ne').mp ha2
  have hthreshold : L * Δ ≤ T * σ ^ 2 := (div_le_iff₀ hsig).mp hTL
  have hweighted : (L * a) ^ 2 * (T * σ ^ 2) = L * Δ := by nlinarith [heq]
  have hsq : (L * a) ^ 2 ≤ 1 := by
    apply (mul_le_mul_iff_left₀ (show 0 < (T : ℝ) * σ ^ 2 by positivity)).mp
    nlinarith [hweighted]
  have hstep : L * a ≤ 1 := by nlinarith [sq_nonneg (L * a - 1)]
  have hbalance : Δ / (a * T) = L * a * σ ^ 2 := by
    apply (div_eq_iff (mul_pos ha ht).ne').2
    nlinarith [heq]
  have hroot : Real.sqrt (L * Δ / T) = L * a * σ := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    apply (div_eq_iff ht.ne').2
    nlinarith [heq]
  refine ⟨ha, hstep, ?_⟩
  change 2 * Δ / (a * T) + 2 * L * a * σ ^ 2 = _
  rw [show 2 * Δ / (a * T) = 2 * (Δ / (a * T)) by ring, hbalance, hroot]
  ring

end CertDROProof

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace CertDRO.SGD

open MeasureTheory

/-- Theorem 2 (Convergence of Nonconvex SGD), p. 6. Let Assumptions A and B hold with the ℓ²-norm,
`Θ = ℝ^d`, `γ > Lzz`, and let `F(θ) = E_{P₀}[φ_γ(θ; Z)]`. Let `Δ_F ≥ F(θ⁰) − inf_θ F(θ)`, assume
`E‖∇F(θ) − ∇_θ φ_γ(θ, Z)‖² ≤ σ²` for all `θ`, and run Algorithm 1 with an `ε`-approximate maximization
oracle and constant stepsize `α = √(Δ_F / (L_φ T σ²))`, `L_φ = Lθθ + Lθz Lzθ / (γ − Lzz)`. If
`T ≥ L_φ Δ_F / σ²`, then
`(1/T) Σ_{t=0}^{T−1} E‖∇F(θ^t)‖² − (4 Lθz² / (γ − Lzz)) ε ≤ 4σ √(L_φ Δ_F / T)`
(stated with the `ε`-term moved to the right-hand side, in `ℝ≥0∞`). -/
theorem theorem_2 {d m : ℕ} (Z : Set (Data m)) (c : Data m → Data m → ℝ)
    (ℓ : Param d → Data m → ℝ) (gθ : Param d → Data m → Param d) (gz : Param d → Data m → Data m)
    (Lθθ Lzz Lθz Lzθ γ : ℝ)
    (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (P₀ : Measure (Data m)) [IsProbabilityMeasure P₀] (hP₀ : P₀ Zᶜ = 0)
    (hint : ∀ θ, Integrable (fun z => robustSurrogate Z ℓ c γ θ z) P₀)
    (ε : ℝ) (hε : 0 ≤ ε) (zhat : Param d → Data m → Data m)
    (hzhat : IsOracle Z ℓ c γ ε zhat) (hzhat_meas : Measurable (Function.uncurry zhat))
    (σ : ℝ) (hσ : 0 < σ)
    (hvar : ∀ θ, ∫⁻ z, ENNReal.ofReal (‖gradient (robustObjective Z ℓ c γ P₀) θ -
        gradient (fun θ' => robustSurrogate Z ℓ c γ θ' z) θ‖ ^ 2) ∂P₀ ≤ ENNReal.ofReal (σ ^ 2))
    (θ₀ : Param d) (ΔF : ℝ) (hΔF_pos : 0 < ΔF)
    (hbdd : BddBelow (Set.range (robustObjective Z ℓ c γ P₀)))
    (hΔF : robustObjective Z ℓ c γ P₀ θ₀ - ⨅ θ, robustObjective Z ℓ c γ P₀ θ ≤ ΔF)
    (T : ℕ) (hT : 0 < T) (hTL : Lphi Lθθ Lzz Lθz Lzθ γ * ΔF / σ ^ 2 ≤ T) :
    (T : ENNReal)⁻¹ * ∑ t ∈ Finset.range T,
        ∫⁻ ω, ENNReal.ofReal (‖gradient (robustObjective Z ℓ c γ P₀)
            (run gθ zhat (Real.sqrt (ΔF / (Lphi Lθθ Lzz Lθz Lzθ γ * T * σ ^ 2))) θ₀ ω t)‖ ^ 2)
          ∂(Measure.pi fun _ : Fin T => P₀) ≤
      ENNReal.ofReal (4 * Lθz ^ 2 / (γ - Lzz) * ε
        + 4 * σ * Real.sqrt (Lphi Lθθ Lzz Lθz Lzθ γ * ΔF / T)) := by
  let L := Lphi Lθθ Lzz Lθz Lzθ γ
  have hL : 0 ≤ L := CertDROProof.lphi_nonneg hS
  by_cases hzero : L = 0
  · obtain ⟨hF, _, hG⟩ := CertDROProof.objective_facts hS P₀ hP₀ hint σ hvar
    have hz : ∀ θ, gradient (robustObjective Z ℓ c γ P₀) θ = 0 :=
      CertDROProof.zero_smooth_gradient _ _ hF (by simpa only [← hzero] using hG) hbdd
    simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      ENNReal.ofReal_zero, lintegral_zero, Finset.sum_const_zero, mul_zero]
    exact bot_le
  · have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm hzero)
    obtain ⟨ha, hstep, heq⟩ := CertDROProof.balancing_stepsize L ΔF σ T hLp hΔF_pos hσ hT hTL
    have hb := CertDROProof.sgd_average_bound hS P₀ hP₀ hint ε hε zhat hzhat hzhat_meas
      σ hσ hvar θ₀ ΔF hΔF_pos hbdd hΔF T hT _ ha hstep
    convert! hb using 1
    congr 1
    linarith [heq]

end CertDRO.SGD

open CertDRO.SGD

theorem solution {d m : ℕ} (Z : Set (Data m)) (c : Data m → Data m → ℝ)
    (ℓ : Param d → Data m → ℝ) (gθ : Param d → Data m → Param d) (gz : Param d → Data m → Data m)
    (Lθθ Lzz Lθz Lzθ γ : ℝ)
    (hS : Standing Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ)
    (P₀ : Measure (Data m)) [IsProbabilityMeasure P₀] (hP₀ : P₀ Zᶜ = 0)
    (hint : ∀ θ, Integrable (fun z => robustSurrogate Z ℓ c γ θ z) P₀)
    (ε : ℝ) (hε : 0 ≤ ε) (zhat : Param d → Data m → Data m)
    (hzhat : IsOracle Z ℓ c γ ε zhat) (hzhat_meas : Measurable (Function.uncurry zhat))
    (σ : ℝ) (hσ : 0 < σ)
    (hvar : ∀ θ, ∫⁻ z, ENNReal.ofReal (‖gradient (robustObjective Z ℓ c γ P₀) θ -
        gradient (fun θ' => robustSurrogate Z ℓ c γ θ' z) θ‖ ^ 2) ∂P₀ ≤ ENNReal.ofReal (σ ^ 2))
    (θ₀ : Param d) (ΔF : ℝ) (hΔF_pos : 0 < ΔF)
    (hbdd : BddBelow (Set.range (robustObjective Z ℓ c γ P₀)))
    (hΔF : robustObjective Z ℓ c γ P₀ θ₀ - ⨅ θ, robustObjective Z ℓ c γ P₀ θ ≤ ΔF)
    (T : ℕ) (hT : 0 < T) (hTL : Lphi Lθθ Lzz Lθz Lzθ γ * ΔF / σ ^ 2 ≤ T) :
    (T : ENNReal)⁻¹ * ∑ t ∈ Finset.range T,
        ∫⁻ ω, ENNReal.ofReal (‖gradient (robustObjective Z ℓ c γ P₀)
            (run gθ zhat (Real.sqrt (ΔF / (Lphi Lθθ Lzz Lθz Lzθ γ * T * σ ^ 2))) θ₀ ω t)‖ ^ 2)
          ∂(Measure.pi fun _ : Fin T => P₀) ≤
      ENNReal.ofReal (4 * Lθz ^ 2 / (γ - Lzz) * ε
        + 4 * σ * Real.sqrt (Lphi Lθθ Lzz Lθz Lzθ γ * ΔF / T)) := by
  exact CertDRO.SGD.theorem_2 Z c ℓ gθ gz Lθθ Lzz Lθz Lzθ γ hS P₀ hP₀ hint ε hε zhat hzhat hzhat_meas σ hσ hvar θ₀ ΔF hΔF_pos hbdd hΔF T hT hTL
