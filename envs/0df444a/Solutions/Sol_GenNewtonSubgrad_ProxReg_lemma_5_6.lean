-- Prove2me | solution 1 for GenNewtonSubgrad.ProxReg.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:12:18.544582+00:00
-- url     : https://prove2.me/submissions/eb19fefb-d323-4992-8375-5f69ce948bea

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Theorems.Thm_GenNewtonSubgrad_ProxReg_scalarization_2_11

open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared GenNewtonSubgrad.ProxReg

namespace P2MSumRule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Regular subgradient of a real-valued function. -/
def RS (f : E → ℝ) (y w : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝 y, f y + (⟪w, z - y⟫_ℝ - ε * ‖z - y‖) ≤ f z

lemma rs_iff (f : E → ℝ) (y w : E) :
    IsRegularSubgrad (fun z => ((f z : ℝ) : EReal)) y w ↔ RS f y w := by
  unfold IsRegularSubgrad RS
  simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true, true_and]
  refine forall₂_congr fun ε hε => ?_
  refine Filter.eventually_congr (Eventually.of_forall fun z => ?_)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]

lemma fermatQ {f g : E → ℝ} {y G : E} {C : ℝ} (hC : 0 ≤ C) {N : Set E} (hN : N ∈ 𝓝 y)
    (hmin : ∀ z ∈ N, f y + g y ≤ f z + g z)
    (hg : ∀ z ∈ N, g z - g y ≤ ⟪G, z - y⟫_ℝ + C * ‖z - y‖ ^ 2) : RS f y (-G) := by
  intro ε hε
  have hb : Metric.ball y (ε / (C + 1)) ∈ 𝓝 y := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hN, hb] with z hz hzb
  have h1 := hmin z hz
  have h2 := hg z hz
  have h3 : ‖z - y‖ < ε / (C + 1) := by rwa [Metric.mem_ball, dist_eq_norm] at hzb
  rw [lt_div_iff₀ (by positivity)] at h3
  have hd := norm_nonneg (z - y)
  have h4 : C * ‖z - y‖ ^ 2 ≤ ε * ‖z - y‖ := by
    have : C * ‖z - y‖ ≤ ε := by nlinarith
    nlinarith
  rw [inner_neg_left]
  linarith

lemma quad_id (z a b : E) : ‖z - b‖ ^ 2 - ‖a - b‖ ^ 2 = 2 * ⟪a - b, z - a⟫_ℝ + ‖z - a‖ ^ 2 := by
  have : z - b = (z - a) + (a - b) := by abel
  rw [this, norm_add_sq_real, real_inner_comm]; ring

lemma sqrt_bound (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q) :
    Real.sqrt q ≤ Real.sqrt p + (q - p) / (2 * Real.sqrt p) := by
  have hsp := Real.sqrt_pos.mpr hp
  have h1 := Real.sq_sqrt hq
  have h2 := Real.sq_sqrt hp.le
  have : Real.sqrt q - Real.sqrt p ≤ (q - p) / (2 * Real.sqrt p) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Real.sqrt q - Real.sqrt p)]
  linarith

lemma S_bound (x y z : E) (t : ℝ) (ht : 0 < t) :
    Real.sqrt (‖z - x‖ ^ 2 + t ^ 2) - Real.sqrt (‖y - x‖ ^ 2 + t ^ 2) ≤
      ⟪(Real.sqrt (‖y - x‖ ^ 2 + t ^ 2))⁻¹ • (y - x), z - y⟫_ℝ + ‖z - y‖ ^ 2 / (2 * t) := by
  have hp : 0 < ‖y - x‖ ^ 2 + t ^ 2 := by positivity
  have hb := sqrt_bound _ (‖z - x‖ ^ 2 + t ^ 2) hp (by positivity)
  set s := Real.sqrt (‖y - x‖ ^ 2 + t ^ 2) with hs
  have hts : t ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg ‖y - x‖]
  have hs0 : 0 < s := lt_of_lt_of_le ht hts
  have hq := quad_id z y x
  have e : (‖z - x‖ ^ 2 + t ^ 2 - (‖y - x‖ ^ 2 + t ^ 2)) / (2 * s) =
      s⁻¹ * ⟪y - x, z - y⟫_ℝ + ‖z - y‖ ^ 2 / (2 * s) := by
    rw [show ‖z - x‖ ^ 2 + t ^ 2 - (‖y - x‖ ^ 2 + t ^ 2) = ‖z - x‖ ^ 2 - ‖y - x‖ ^ 2 by ring, hq]
    field_simp; try ring
  rw [e] at hb
  have h3 : ‖z - y‖ ^ 2 / (2 * s) ≤ ‖z - y‖ ^ 2 / (2 * t) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  rw [real_inner_smul_left]
  linarith

lemma rs_bound {f : E → ℝ} {y w : E} {L : ℝ} (hL : 0 ≤ L) {U : Set E} (hU : U ∈ 𝓝 y)
    (hLip : ∀ z ∈ U, f z - f y ≤ L * ‖z - y‖) (hw : RS f y w) : ‖w‖ ≤ L := by
  by_contra hc
  push Not at hc
  have hw0 : 0 < ‖w‖ := lt_of_le_of_lt hL hc
  set ε := (‖w‖ - L) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hev := (show ∀ᶠ z in 𝓝 y, z ∈ U from hU).and (hw ε hε0)
  have hT : Tendsto (fun s : ℝ => y + s • w) (𝓝[>] 0) (𝓝 y) := by
    have : Tendsto (fun s : ℝ => y + s • w) (𝓝 0) (𝓝 (y + (0 : ℝ) • w)) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0)
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨s, ⟨hsU, hs⟩, hs0⟩ := ((hT.eventually hev).and self_mem_nhdsWithin).exists
  have hs0' : 0 < s := hs0
  have h1 := hLip _ hsU
  simp only [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_of_nonneg hs0'.le] at hs h1
  have h2 : s * ‖w‖ ^ 2 - ε * (s * ‖w‖) ≤ L * (s * ‖w‖) := by linarith
  have h3 : 0 < s * ‖w‖ := by positivity
  have h4 : s * ‖w‖ * (‖w‖ - ε - L) ≤ 0 := by nlinarith
  have h5 : 0 < ‖w‖ - ε - L := by rw [hε]; linarith
  nlinarith

lemma ar_fz (F1a F2a F2b f0 I γ k L t na d Sa : ℝ)
    (hmin : F1a + F2b - I + 2 * γ * Sa + k * d ^ 2 ≤ f0 + 2 * γ * t)
    (hsub : f0 + (I - γ * na) ≤ F1a + F2a) (hlip : |F2b - F2a| ≤ L * d)
    (hγS : γ * na ≤ γ * Sa) : γ * na + k * d ^ 2 ≤ L * d + 2 * γ * t := by
  have := (abs_le.mp hlip).1
  linarith

lemma ar_d (k d L : ℝ) (hk : 0 < k) (hd : 0 ≤ d) (hL : 0 < L)
    (h : k * d ^ 2 ≤ L * d + L ^ 2 / k) : d ≤ 2 * L / k := by
  rw [le_div_iff₀ hk]
  by_contra hc
  push Not at hc
  have e : L ^ 2 / k * k = L ^ 2 := by field_simp
  have h2 : k * d ^ 2 * k ≤ L * d * k + L ^ 2 := by
    have := mul_le_mul_of_nonneg_right h hk.le
    rw [add_mul, e] at this; exact this
  nlinarith

variable [ProperSpace E]

lemma fuzzy {f1 f2 : E → ℝ} {x v : E} {L R : ℝ} (hL : 1 ≤ L) (hR : 0 < R)
    (hc1 : ContinuousOn f1 (Metric.ball x R)) (hc2 : ContinuousOn f2 (Metric.ball x R))
    (hf2 : ∀ y ∈ Metric.ball x R, ∀ z ∈ Metric.ball x R, |f2 y - f2 z| ≤ L * ‖y - z‖)
    (hv : RS (fun z => f1 z + f2 z) x v) {η : ℝ} (hη : 0 < η) :
    ∃ a b w1 w2 : E, ‖a - x‖ < η ∧ ‖b - x‖ < η ∧ RS f1 a w1 ∧ RS f2 b w2 ∧
      ‖w1 + w2 - v‖ < η := by
  have hγ0 : 0 < η / 4 := by positivity
  obtain ⟨δ0, hδ0, hδ0'⟩ := Metric.eventually_nhds_iff.mp (hv (η / 4) hγ0)
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = min (min δ0 R) η / 2 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδdef]; exact half_pos (lt_min (lt_min hδ0 hR) hη)
  have hm1 : min (min δ0 R) η ≤ δ0 := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : min (min δ0 R) η ≤ R := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : min (min δ0 R) η ≤ η := min_le_right _ _
  have hδδ0 : δ < δ0 := by rw [hδdef]; linarith
  have hδR : δ < R := by rw [hδdef]; linarith
  have hδη : δ < η := by rw [hδdef]; linarith
  set γ := η / 4 with hγ
  have hL0 : 0 < L := by linarith
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ, k = 8 * L ^ 2 / (γ * δ) + 8 * L / δ + 1 := ⟨_, rfl⟩
  have hA1 : 0 ≤ 8 * L ^ 2 / (γ * δ) := by positivity
  have hA2 : 0 ≤ 8 * L / δ := by positivity
  have hk : 0 < k := by rw [hkdef]; linarith
  have hk1 : 6 * L ^ 2 < k * (γ * δ) := by
    have : 8 * L ^ 2 / (γ * δ) < k := by rw [hkdef]; linarith
    rw [div_lt_iff₀ (by positivity)] at this; nlinarith
  have hk2 : 8 * L < k * δ := by
    have : 8 * L / δ < k := by rw [hkdef]; linarith
    rwa [div_lt_iff₀ hδpos] at this
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = min 1 (L ^ 2 / (2 * γ * k)) := ⟨_, rfl⟩
  have ht : 0 < t := by rw [htdef]; exact lt_min one_pos (by positivity)
  have ht2 : 2 * γ * t ≤ L ^ 2 / k := by
    have : t ≤ L ^ 2 / (2 * γ * k) := by rw [htdef]; exact min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    rw [le_div_iff₀ hk]; nlinarith
  set B := Metric.closedBall x δ with hB
  have hBR : B ⊆ Metric.ball x R := Metric.closedBall_subset_ball hδR
  set S : E → ℝ := fun z => Real.sqrt (‖z - x‖ ^ 2 + t ^ 2) with hS
  set Φ : E × E → ℝ := fun p =>
    f1 p.1 + f2 p.2 - ⟪v, p.1 - x⟫_ℝ + 2 * γ * S p.1 + k * ‖p.1 - p.2‖ ^ 2 with hΦ
  have hcont : ContinuousOn Φ (B ×ˢ B) := by
    have c1 : ContinuousOn (fun p : E × E => f1 p.1) (B ×ˢ B) :=
      (hc1.mono hBR).comp continuous_fst.continuousOn (fun p hp => hp.1)
    have c2 : ContinuousOn (fun p : E × E => f2 p.2) (B ×ˢ B) :=
      (hc2.mono hBR).comp continuous_snd.continuousOn (fun p hp => hp.2)
    have c3 : Continuous fun p : E × E =>
        -⟪v, p.1 - x⟫_ℝ + 2 * γ * S p.1 + k * ‖p.1 - p.2‖ ^ 2 := by
      simp only [hS]; fun_prop
    have := (c1.add c2).add c3.continuousOn
    refine this.congr fun p _ => ?_
    simp only [hΦ, Pi.add_apply]; ring
  obtain ⟨⟨a, b⟩, hab, hmin⟩ := ((isCompact_closedBall x δ).prod (isCompact_closedBall x δ)).exists_isMinOn
    ⟨(x, x), Metric.mem_closedBall_self hδpos.le, Metric.mem_closedBall_self hδpos.le⟩ hcont
  have hmin' : ∀ p ∈ B ×ˢ B, Φ (a, b) ≤ Φ p := fun p hp => isMinOn_iff.mp hmin p hp
  have haB : a ∈ B := hab.1
  have hbB : b ∈ B := hab.2
  have hxB : x ∈ B := Metric.mem_closedBall_self hδpos.le
  have haR := hBR haB
  have hbR := hBR hbB
  -- basic estimates
  have hSx : S x = t := by simp only [hS, sub_self, norm_zero]; simp [Real.sqrt_sq ht.le]
  have h1 := hmin' (x, x) ⟨hxB, hxB⟩
  simp only [hΦ, sub_self, inner_zero_right, norm_zero, hSx] at h1
  have h2 := hδ0' (show dist a x < δ0 by
    rw [Metric.mem_closedBall] at haB; linarith)
  have h3 := hf2 b hbR a haR
  have hSa : ‖a - x‖ ≤ S a := by
    simp only [hS]; apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg t]
  have hγS : γ * ‖a - x‖ ≤ γ * S a := mul_le_mul_of_nonneg_left hSa hγ0.le
  have hmain := ar_fz (f1 a) (f2 a) (f2 b) (f1 x + f2 x) ⟪v, a - x⟫_ℝ γ k L t ‖a - x‖ ‖a - b‖ (S a)
    (by linarith) (by simpa using h2) (by rwa [norm_sub_rev b a] at h3) hγS
  have hγna : 0 ≤ γ * ‖a - x‖ := by positivity
  have hd := ar_d k ‖a - b‖ L hk (norm_nonneg _) hL0 (by linarith)
  have hna : ‖a - x‖ < δ / 2 := by
    have hLd : L * ‖a - b‖ ≤ L * (2 * L / k) := mul_le_mul_of_nonneg_left hd hL0.le
    have e : L * (2 * L / k) = 2 * L ^ 2 / k := by ring
    have h4 : γ * ‖a - x‖ ≤ 3 * L ^ 2 / k := by
      have : 2 * L ^ 2 / k + L ^ 2 / k = 3 * L ^ 2 / k := by ring
      have hkd : 0 ≤ k * ‖a - b‖ ^ 2 := by positivity
      linarith
    have h5 : 3 * L ^ 2 / k < γ * (δ / 2) := by
      rw [div_lt_iff₀ hk]; linarith
    have h6 : γ * ‖a - x‖ < γ * (δ / 2) := lt_of_le_of_lt h4 h5
    exact lt_of_mul_lt_mul_left h6 hγ0.le
  have hdb : ‖a - b‖ < δ / 4 := by
    have : 2 * L / k < δ / 4 := by rw [div_lt_iff₀ hk]; linarith
    linarith
  have hnb : ‖b - x‖ < δ := by
    have : b - x = (b - a) + (a - x) := by abel
    rw [this]
    calc ‖(b - a) + (a - x)‖ ≤ ‖b - a‖ + ‖a - x‖ := norm_add_le _ _
      _ = ‖a - b‖ + ‖a - x‖ := by rw [norm_sub_rev]
      _ < δ := by linarith
  have haball : a ∈ Metric.ball x δ := by rw [Metric.mem_ball, dist_eq_norm]; linarith
  have hbball : b ∈ Metric.ball x δ := by rw [Metric.mem_ball, dist_eq_norm]; exact hnb
  have hballB : Metric.ball x δ ⊆ B := Metric.ball_subset_closedBall
  -- Fermat in a
  set c := 2 * γ / S a with hc
  have hSa0 : 0 < S a := by
    simp only [hS]; apply Real.sqrt_pos.mpr; positivity
  have RS1 : RS f1 a (-(-v + c • (a - x) + (2 * k) • (a - b))) := by
    refine fermatQ (g := fun z => -⟪v, z - x⟫_ℝ + 2 * γ * S z + k * ‖z - b‖ ^ 2)
      (C := γ / t + k) (by positivity) (Metric.isOpen_ball.mem_nhds haball) ?_ ?_
    · intro z hz
      have := hmin' (z, b) ⟨hballB hz, hbB⟩
      simp only [hΦ] at this
      linarith
    · intro z hz
      have hSb : S z - S a ≤ ⟪(S a)⁻¹ • (a - x), z - a⟫_ℝ + ‖z - a‖ ^ 2 / (2 * t) :=
        S_bound x a z t ht
      have hq := quad_id z a b
      have e1 : ⟪-v + c • (a - x) + (2 * k) • (a - b), z - a⟫_ℝ =
          -⟪v, z - a⟫_ℝ + c * ⟪a - x, z - a⟫_ℝ + 2 * k * ⟪a - b, z - a⟫_ℝ := by
        rw [inner_add_left, inner_add_left, inner_neg_left, real_inner_smul_left,
          real_inner_smul_left]
      have e2 : ⟪v, z - x⟫_ℝ - ⟪v, a - x⟫_ℝ = ⟪v, z - a⟫_ℝ := by
        rw [← inner_sub_right]; congr 1; abel
      have e3 : ⟪(S a)⁻¹ • (a - x), z - a⟫_ℝ = (S a)⁻¹ * ⟪a - x, z - a⟫_ℝ :=
        real_inner_smul_left _ _ _
      have e4 : 2 * γ * ((S a)⁻¹ * ⟪a - x, z - a⟫_ℝ) = c * ⟪a - x, z - a⟫_ℝ := by
        rw [hc]; ring
      have e5 : 2 * γ * (‖z - a‖ ^ 2 / (2 * t)) = γ / t * ‖z - a‖ ^ 2 := by ring
      have hq2 : k * ‖z - b‖ ^ 2 - k * ‖a - b‖ ^ 2 =
          2 * k * ⟪a - b, z - a⟫_ℝ + k * ‖z - a‖ ^ 2 := by rw [← mul_sub, hq]; ring
      have hSb2 : 2 * γ * (S z - S a) ≤ c * ⟪a - x, z - a⟫_ℝ + γ / t * ‖z - a‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hSb (by positivity : (0 : ℝ) ≤ 2 * γ)
        rwa [mul_add, e3, e4, e5] at this
      show (-⟪v, z - x⟫_ℝ + 2 * γ * S z + k * ‖z - b‖ ^ 2) -
          (-⟪v, a - x⟫_ℝ + 2 * γ * S a + k * ‖a - b‖ ^ 2) ≤ _
      rw [e1]
      linarith
  -- Fermat in b
  have RS2 : RS f2 b (-((2 * k) • (b - a))) := by
    refine fermatQ (g := fun z => k * ‖z - a‖ ^ 2) (C := k) hk.le
      (Metric.isOpen_ball.mem_nhds hbball) ?_ ?_
    · intro z hz
      have := hmin' (a, z) ⟨haB, hballB hz⟩
      simp only [hΦ] at this
      rw [norm_sub_rev a b, norm_sub_rev a z] at this
      linarith
    · intro z hz
      have hq := quad_id z b a
      have hq2 : k * ‖z - a‖ ^ 2 - k * ‖b - a‖ ^ 2 =
          2 * k * ⟪b - a, z - b⟫_ℝ + k * ‖z - b‖ ^ 2 := by rw [← mul_sub, hq]; ring
      show k * ‖z - a‖ ^ 2 - k * ‖b - a‖ ^ 2 ≤ _
      rw [real_inner_smul_left]
      linarith
  refine ⟨a, b, _, _, by linarith, by linarith, RS1, RS2, ?_⟩
  have e : -(-v + c • (a - x) + (2 * k) • (a - b)) + -((2 * k) • (b - a)) - v = -(c • (a - x)) := by
    rw [show b - a = -(a - b) by abel, smul_neg]; abel
  rw [e, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
  have : c * ‖a - x‖ ≤ 2 * γ := by
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ hSa0]
    exact mul_le_mul_of_nonneg_left hSa (by positivity)
  linarith

lemma lip_abs {f : E → ℝ} {U : Set E} {K : NNReal} (h : LipschitzOnWith K f U) {L : ℝ}
    (hKL : (K : ℝ) ≤ L) : ∀ y ∈ U, ∀ z ∈ U, |f y - f z| ≤ L * ‖y - z‖ := by
  intro y hy z hz
  have := h.dist_le_mul y hy z hz
  rw [Real.dist_eq, dist_eq_norm] at this
  exact this.trans (mul_le_mul_of_nonneg_right hKL (norm_nonneg _))

theorem sum_rule (f1 f2 : E → ℝ) (xbar : E)
    (h1 : ∃ U ∈ 𝓝 xbar, ∃ L, LipschitzOnWith L f1 U)
    (h2 : ∃ U ∈ 𝓝 xbar, ∃ L, LipschitzOnWith L f2 U) :
    LimitingSubdiff (fun z => ((f1 z + f2 z : ℝ) : EReal)) xbar ⊆
      LimitingSubdiff (fun z => ((f1 z : ℝ) : EReal)) xbar +
        LimitingSubdiff (fun z => ((f2 z : ℝ) : EReal)) xbar := by
  obtain ⟨U1, hU1, K1, hK1⟩ := h1
  obtain ⟨U2, hU2, K2, hK2⟩ := h2
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hU1 hU2)
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = max (max (K1 : ℝ) (K2 : ℝ)) 1 := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLdef]; exact le_max_right _ _
  have hL0 : 0 ≤ L := by linarith
  have hK1L : (K1 : ℝ) ≤ L := by rw [hLdef]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hK2L : (K2 : ℝ) ≤ L := by rw [hLdef]; exact (le_max_right _ _).trans (le_max_left _ _)
  have Lip1 := lip_abs (hK1.mono fun y hy => (hRU hy).1) hK1L
  have Lip2 := lip_abs (hK2.mono fun y hy => (hRU hy).2) hK2L
  have cont1 : ContinuousOn f1 (Metric.ball xbar R) := (hK1.mono fun y hy => (hRU hy).1).continuousOn
  have cont2 : ContinuousOn f2 (Metric.ball xbar R) := (hK2.mono fun y hy => (hRU hy).2).continuousOn
  intro v hv
  obtain ⟨-, xs, vs, hxs, -, hvs, hreg⟩ := hv
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hxs.eventually (Metric.ball_mem_nhds xbar (half_pos hR)))
  have hsub : ∀ t : ℕ, Metric.ball (xs (t + N)) (R / 2) ⊆ Metric.ball xbar R := by
    intro t y hy
    have h1 := hN (t + N) (by omega)
    rw [Metric.mem_ball] at hy ⊢
    calc dist y xbar ≤ dist y (xs (t + N)) + dist (xs (t + N)) xbar := dist_triangle _ _ _
      _ < R / 2 + R / 2 := add_lt_add hy h1
      _ = R := by ring
  have hfz : ∀ t : ℕ, ∃ a b w1 w2 : E, ‖a - xs (t + N)‖ < min (1 / ((t : ℝ) + 1)) (R / 4) ∧
      ‖b - xs (t + N)‖ < min (1 / ((t : ℝ) + 1)) (R / 4) ∧ RS f1 a w1 ∧ RS f2 b w2 ∧
      ‖w1 + w2 - vs (t + N)‖ < min (1 / ((t : ℝ) + 1)) (R / 4) := by
    intro t
    exact fuzzy hL1 (half_pos hR) (cont1.mono (hsub t)) (cont2.mono (hsub t))
      (fun y hy z hz => Lip2 y (hsub t hy) z (hsub t hz))
      ((rs_iff (fun z => f1 z + f2 z) _ _).mp (hreg (t + N))) (by positivity)
  choose a b w1 w2 ha hb hw1 hw2 hsum using hfz
  have hmin_le : ∀ t : ℕ, min (1 / ((t : ℝ) + 1)) (R / 4) ≤ 1 / ((t : ℝ) + 1) :=
    fun t => min_le_left _ _
  have haR : ∀ t, Metric.ball (a t) (R / 4) ⊆ Metric.ball xbar R := by
    intro t y hy
    have h1 := hN (t + N) (by omega)
    have h2 : ‖a t - xs (t + N)‖ < R / 4 := lt_of_lt_of_le (ha t) (min_le_right _ _)
    rw [Metric.mem_ball] at hy ⊢
    rw [dist_eq_norm] at h1 hy ⊢
    calc ‖y - xbar‖ = ‖(y - a t) + (a t - xs (t + N)) + (xs (t + N) - xbar)‖ := by
          congr 1; abel
      _ ≤ ‖y - a t‖ + ‖a t - xs (t + N)‖ + ‖xs (t + N) - xbar‖ := norm_add₃_le
      _ < R / 4 + R / 4 + R / 2 := by linarith
      _ = R := by ring
  have hbound : ∀ t, ‖w1 t‖ ≤ L := by
    intro t
    refine rs_bound hL0 (Metric.ball_mem_nhds (a t) (by positivity : (0 : ℝ) < R / 4))
      (fun z hz => ?_) (hw1 t)
    have := Lip1 z (haR t hz) (a t) (haR t (Metric.mem_ball_self (by positivity)))
    exact (le_abs_self _).trans this
  obtain ⟨W1, -, φ, hφ, hW1⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : E)) (r := L))
    (fun t => by rw [Metric.mem_closedBall, dist_zero_right]; exact hbound t)
  have hxsN : Tendsto (fun t => xs (t + N)) atTop (𝓝 xbar) := hxs.comp (tendsto_add_atTop_nat N)
  have hvsN : Tendsto (fun t => vs (t + N)) atTop (𝓝 v) := hvs.comp (tendsto_add_atTop_nat N)
  have hinv : Tendsto (fun t : ℕ => 1 / ((t : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hza : Tendsto (fun t => a t - xs (t + N)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun t => ((ha t).trans_le (hmin_le t)).le) hinv
  have hzb : Tendsto (fun t => b t - xs (t + N)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun t => ((hb t).trans_le (hmin_le t)).le) hinv
  have hzs : Tendsto (fun t => w1 t + w2 t - vs (t + N)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun t => ((hsum t).trans_le (hmin_le t)).le) hinv
  have hat : Tendsto a atTop (𝓝 xbar) := by
    have := hza.add hxsN; simp only [sub_add_cancel, zero_add] at this; exact this
  have hbt : Tendsto b atTop (𝓝 xbar) := by
    have := hzb.add hxsN; simp only [sub_add_cancel, zero_add] at this; exact this
  have hφt := hφ.tendsto_atTop
  have hw2t : Tendsto (fun t => w2 (φ t)) atTop (𝓝 (v - W1)) := by
    have := ((hzs.comp hφt).add (hvsN.comp hφt)).sub hW1
    simp only [zero_add] at this
    refine this.congr fun t => ?_
    simp only [Function.comp]; abel
  have hc1 : ContinuousAt f1 xbar := cont1.continuousAt (Metric.ball_mem_nhds _ hR)
  have hc2 : ContinuousAt f2 xbar := cont2.continuousAt (Metric.ball_mem_nhds _ hR)
  refine ⟨W1, ?_, v - W1, ?_, add_sub_cancel _ _⟩
  · refine ⟨EReal.coe_ne_top _, fun t => a (φ t), fun t => w1 (φ t), hat.comp hφt, ?_, hW1,
      fun t => (rs_iff f1 _ _).mpr (hw1 (φ t))⟩
    exact (continuous_coe_real_ereal.tendsto _).comp (hc1.tendsto.comp (hat.comp hφt))
  · refine ⟨EReal.coe_ne_top _, fun t => b (φ t), fun t => w2 (φ t), hbt.comp hφt, ?_, hw2t,
      fun t => (rs_iff f2 _ _).mpr (hw2 (φ t))⟩
    exact (continuous_coe_real_ereal.tendsto _).comp (hc2.tendsto.comp (hbt.comp hφt))

end P2MSumRule

theorem solution {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xbar : EuclideanSpace ℝ (Fin n)) (hF : ∃ U ∈ 𝓝 xbar, ∃ L, LipschitzOnWith L F U)
    (u₁ u₂ : EuclideanSpace ℝ (Fin m)) :
    coderiv (sv F) xbar (F xbar) (u₁ + u₂) ⊆
      coderiv (sv F) xbar (F xbar) u₁ + coderiv (sv F) xbar (F xbar) u₂ := by
  have hlip : ∀ u : EuclideanSpace ℝ (Fin m),
      ∃ U ∈ 𝓝 xbar, ∃ L, LipschitzOnWith L (fun z => ⟪u, F z⟫_ℝ) U := by
    intro u
    obtain ⟨U, hU, L, hL⟩ := hF
    refine ⟨U, hU, ‖u‖₊ * L, ?_⟩
    have : LipschitzWith ‖u‖₊ (fun w : EuclideanSpace ℝ (Fin m) => ⟪u, w⟫_ℝ) :=
      (innerSL ℝ u).lipschitz.weaken (by
        rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, innerSL_apply_norm])
    exact this.comp_lipschitzOnWith hL
  rw [scalarization_2_11 F xbar hF, scalarization_2_11 F xbar hF, scalarization_2_11 F xbar hF]
  have e : (fun z => ((⟪u₁ + u₂, F z⟫_ℝ : ℝ) : EReal)) =
      fun z => ((⟪u₁, F z⟫_ℝ + ⟪u₂, F z⟫_ℝ : ℝ) : EReal) := by
    funext z; rw [inner_add_left]
  rw [e]
  exact P2MSumRule.sum_rule (fun z => ⟪u₁, F z⟫_ℝ) (fun z => ⟪u₂, F z⟫_ℝ) xbar (hlip u₁) (hlip u₂)
