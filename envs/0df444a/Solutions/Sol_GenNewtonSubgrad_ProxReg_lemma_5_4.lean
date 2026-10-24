-- Prove2me | solution 1 for GenNewtonSubgrad.ProxReg.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:20:47.808704+00:00
-- url     : https://prove2.me/submissions/68b59e68-add0-477e-a555-4716ad85d93a

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis

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

end P2MSumRule

namespace P2MMord

open P2MSumRule

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E']

lemma norm_amgm (q q0 : E') (h : 0 < ‖q0‖) :
    ‖q‖ ≤ ‖q0‖ + ⟪‖q0‖⁻¹ • q0, q - q0⟫_ℝ + ‖q - q0‖ ^ 2 / (2 * ‖q0‖) := by
  have e : ‖q‖ ^ 2 = ‖q0‖ ^ 2 + 2 * ⟪q0, q - q0⟫_ℝ + ‖q - q0‖ ^ 2 := by
    have : q = q0 + (q - q0) := by abel
    conv_lhs => rw [this]
    exact norm_add_sq_real _ _
  rw [real_inner_smul_left]
  have hm : ‖q‖ * (2 * ‖q0‖) ≤ ‖q0‖ ^ 2 + ‖q‖ ^ 2 := by
    nlinarith [sq_nonneg (‖q‖ - ‖q0‖)]
  have h1 : ‖q‖ ≤ (‖q0‖ ^ 2 + ‖q‖ ^ 2) / (2 * ‖q0‖) := by
    rw [le_div_iff₀ (by positivity)]; exact hm
  have e2 : (‖q0‖ ^ 2 + ‖q‖ ^ 2) / (2 * ‖q0‖) =
      ‖q0‖ + ‖q0‖⁻¹ * ⟪q0, q - q0⟫_ℝ + ‖q - q0‖ ^ 2 / (2 * ‖q0‖) := by
    rw [e]; field_simp; ring
  linarith

lemma chain_reg {F : E → E'} {y : E'} {a w : E} (hne : F a ≠ y)
    (hw : RS (fun z => ‖F z - y‖) a w) :
    (w, -(‖F a - y‖⁻¹ • (F a - y))) ∈ regNormal (gph (sv F)) (a, F a) := by
  have hN : 0 < ‖F a - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  refine ⟨by simp [gph, sv], fun ε hε => ?_⟩
  have h1 : ∀ᶠ p in 𝓝 (a, F a),
      ‖F a - y‖ + (⟪w, p.1 - a⟫_ℝ - ε / 2 * ‖p.1 - a‖) ≤ ‖F p.1 - y‖ :=
    (continuous_fst.tendsto (a, F a)).eventually (hw (ε / 2) (half_pos hε))
  have h3 : ∀ᶠ p in 𝓝 (a, F a), ‖p.2 - F a‖ < ε * ‖F a - y‖ := by
    have hb := Metric.ball_mem_nhds (F a) (by positivity : 0 < ε * ‖F a - y‖)
    have := (continuous_snd.tendsto (a, F a)).eventually hb
    filter_upwards [this] with q hq
    rwa [dist_eq_norm] at hq
  filter_upwards [h1, h3] with p hp1 hp2 hpS
  obtain ⟨z, q⟩ := p
  simp only [gph, sv, Set.mem_setOf_eq, Set.mem_singleton_iff] at hpS
  subst hpS
  simp only at hp1 hp2
  have hb := norm_amgm (F z - y) (F a - y) hN
  rw [show F z - y - (F a - y) = F z - F a by abel] at hb
  have hq2 : ‖F z - F a‖ ^ 2 / (2 * ‖F a - y‖) ≤ ε / 2 * ‖F z - F a‖ := by
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hp2.le (norm_nonneg (F z - F a))
    nlinarith
  have hm1 := mul_le_mul_of_nonneg_left (le_max_left ‖z - a‖ ‖F z - F a‖)
    (by positivity : (0 : ℝ) ≤ ε / 2)
  have hm2 := mul_le_mul_of_nonneg_left (le_max_right ‖z - a‖ ‖F z - F a‖)
    (by positivity : (0 : ℝ) ≤ ε / 2)
  show ⟪w, z - a⟫_ℝ + ⟪-(‖F a - y‖⁻¹ • (F a - y)), F z - F a⟫_ℝ ≤
    ε * ‖((z, F z) - (a, F a) : E × E')‖
  rw [Prod.norm_def, inner_neg_left]
  simp only [Prod.fst_sub, Prod.snd_sub]
  linarith

lemma ar_rb (s U X μ g ε I M : ℝ) (hs : 0 < s) (hX : 0 ≤ X) (hg : g = U - μ * X)
    (hε : ε * (μ + 2) = g / 4) (hε0 : 0 ≤ ε) (hsX : s * X ≤ g / 4) (hg0 : 0 < g)
    (key : I + s * U ≤ ε * M) (hI : -(X * (μ * s + s ^ 2)) ≤ I) (hM : M ≤ (μ + 2) * s) :
    False := by
  have h1 := mul_le_mul_of_nonneg_left hM hε0
  have h2 := mul_le_mul_of_nonneg_left hsX hs.le
  nlinarith

lemma reg_bound {F : E → E'} {μ : ℝ} (hμ : 0 < μ) {x : E} {V : Set E'} {δV : ℝ}
    (hδV : 0 < δV) (hV : Metric.ball (F x) δV ⊆ V)
    (hMR : ∀ y ∈ V, {x' | y ∈ sv F x'}.Nonempty ∧
      Metric.infDist x {x' | y ∈ sv F x'} ≤ μ * ‖y - F x‖)
    {xs : E} {u : E'} (hreg : (xs, -u) ∈ regNormal (gph (sv F)) (x, F x)) :
    ‖u‖ ≤ μ * ‖xs‖ := by
  by_contra hc
  push Not at hc
  obtain ⟨g, hg⟩ : ∃ g, g = ‖u‖ - μ * ‖xs‖ := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; linarith
  have hu : 0 < ‖u‖ := by have := mul_nonneg hμ.le (norm_nonneg xs); linarith
  obtain ⟨ε, hε⟩ : ∃ ε, ε = g / (4 * (μ + 2)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεμ : ε * (μ + 2) = g / 4 := by rw [hε]; field_simp
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp (hreg.2 ε hε0)
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ,
      s = min (min 1 (δ / (2 * (μ + 1)))) (min (δV / 2) (g / (4 * (‖xs‖ + 1)))) := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [hsdef]
    exact lt_min (lt_min one_pos (by positivity)) (lt_min (by positivity) (by positivity))
  have hs1 : s ≤ 1 := by rw [hsdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hs2 : s ≤ δ / (2 * (μ + 1)) := by
    rw [hsdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hs3 : s ≤ δV / 2 := by rw [hsdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hs4 : s ≤ g / (4 * (‖xs‖ + 1)) := by
    rw [hsdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hsX : s * ‖xs‖ ≤ g / 4 := by
    rw [le_div_iff₀ (by positivity)] at hs4
    nlinarith [norm_nonneg xs]
  have hs2' : s * (2 * (μ + 1)) ≤ δ := by rwa [le_div_iff₀ (by positivity)] at hs2
  set d : E' := ‖u‖⁻¹ • u with hd
  have hdn : ‖d‖ = 1 := by
    rw [hd, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu.ne']
  set y := F x - s • d with hy
  have hyF' : y - F x = -(s • d) := by rw [hy]; abel
  have hyF : ‖y - F x‖ = s := by
    rw [hyF', norm_neg, norm_smul, hdn, Real.norm_of_nonneg hs0.le, mul_one]
  have hyV : y ∈ V := hV (by rw [Metric.mem_ball, dist_eq_norm, hyF]; linarith)
  obtain ⟨hne, hinf⟩ := hMR y hyV
  have hlt : Metric.infDist x {x' | y ∈ sv F x'} < μ * s + s ^ 2 := by
    rw [hyF] at hinf; nlinarith
  obtain ⟨xn, hxn, hdist⟩ := (Metric.infDist_lt_iff hne).mp hlt
  have hyx : y = F xn := by simpa [sv] using hxn
  have hxnn : ‖xn - x‖ ≤ μ * s + s ^ 2 := by
    rw [← dist_eq_norm, dist_comm]; exact hdist.le
  have hss : s ^ 2 ≤ s := by nlinarith
  have hp : dist (xn, y) (x, F x) < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · rw [dist_eq_norm]; nlinarith
    · rw [dist_eq_norm, hyF]; nlinarith
  have key := hδ' hp (by simp [gph, sv, hyx])
  have hM : max ‖xn - x‖ ‖y - F x‖ ≤ (μ + 2) * s := by
    rw [hyF]; apply max_le <;> nlinarith
  have e1 : ⟪-u, y - F x⟫_ℝ = s * ‖u‖ := by
    rw [hyF', inner_neg_left, inner_neg_right, neg_neg, real_inner_smul_right, hd,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have e2 : -(‖xs‖ * (μ * s + s ^ 2)) ≤ ⟪xs, xn - x⟫_ℝ := by
    have := (abs_le.mp (abs_real_inner_le_norm xs (xn - x))).1
    have := mul_le_mul_of_nonneg_left hxnn (norm_nonneg xs)
    linarith
  have key' : ⟪xs, xn - x⟫_ℝ + s * ‖u‖ ≤ ε * max ‖xn - x‖ ‖y - F x‖ := by
    have k2 : pairInner (xs, -u) ((xn, y) - (x, F x)) ≤ ε * ‖((xn, y) - (x, F x) : E × E')‖ := key
    rw [Prod.norm_def] at k2
    simp only [pairInner, Prod.fst_sub, Prod.snd_sub] at k2
    rw [e1] at k2
    exact k2
  exact ar_rb s ‖u‖ ‖xs‖ μ g ε _ _ hs0 (norm_nonneg _) hg hεμ hε0.le hsX hg0 key' e2 hM

end P2MMord

theorem solution {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xbar : EuclideanSpace ℝ (Fin n)) (hF : ∃ U ∈ 𝓝 xbar, ContinuousOn F U) :
    MetricRegularAround (sv F) xbar (F xbar) ↔
      ∃ c : ℝ, 0 < c ∧ ∃ U ∈ 𝓝 xbar, ∀ x ∈ U, ∀ u : EuclideanSpace ℝ (Fin m),
        ∀ v ∈ coderiv (sv F) x (F x) u, c * ‖u‖ ≤ ‖v‖ := by
  obtain ⟨U0, hU0, hcont⟩ := hF
  constructor
  · rintro ⟨μ, -, hμ, U, hU, V, hV, hMR⟩
    set W := interior U ∩ interior U0 with hW
    have hWo : IsOpen W := isOpen_interior.inter isOpen_interior
    set U' := W ∩ F ⁻¹' interior V with hU'
    have hU'o : IsOpen U' :=
      (hcont.mono (Set.inter_subset_right.trans interior_subset)).isOpen_inter_preimage hWo
        isOpen_interior
    have hx : xbar ∈ U' := ⟨⟨mem_interior_iff_mem_nhds.mpr hU, mem_interior_iff_mem_nhds.mpr hU0⟩,
      mem_interior_iff_mem_nhds.mpr hV⟩
    refine ⟨μ⁻¹, inv_pos.mpr hμ, U', hU'o.mem_nhds hx, fun x hx u v hv => ?_⟩
    obtain ⟨-, zs, as, hzsS, hzs, has, hreg⟩ := hv
    have hz1 : Tendsto (fun k => (zs k).1) atTop (𝓝 x) := (continuous_fst.tendsto _).comp hzs
    have hev := hz1.eventually (hU'o.mem_nhds hx)
    have hb : ∀ᶠ k in atTop, ‖(as k).2‖ ≤ μ * ‖(as k).1‖ := by
      filter_upwards [hev] with k hk
      have hzk : zs k = ((zs k).1, F (zs k).1) := by
        have := hzsS k
        simp only [gph, sv, Set.mem_setOf_eq, Set.mem_singleton_iff] at this
        exact Prod.ext rfl this
      obtain ⟨δV, hδV, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (F (zs k).1) hk.2
      have hak : as k = ((as k).1, -(-(as k).2)) := by simp
      have hr := hreg k
      rw [hzk, hak] at hr
      have := P2MMord.reg_bound hμ hδV (hball.trans interior_subset)
        (fun y hyV => hMR _ (interior_subset hk.1.1) y hyV (F (zs k).1) rfl) hr
      rwa [norm_neg] at this
    have t1 : Tendsto (fun k => ‖(as k).2‖) atTop (𝓝 ‖-u‖) :=
      (continuous_norm.tendsto _).comp ((continuous_snd.tendsto _).comp has)
    have t2 : Tendsto (fun k => μ * ‖(as k).1‖) atTop (𝓝 (μ * ‖v‖)) :=
      ((continuous_norm.tendsto _).comp ((continuous_fst.tendsto _).comp has)).const_mul μ
    have := le_of_tendsto_of_tendsto t1 t2 hb
    rw [norm_neg] at this
    rw [inv_mul_le_iff₀ hμ]
    exact this
  · rintro ⟨c, hc, U, hU, hbd⟩
    obtain ⟨ρ0, hρ0, hρ0U⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hU hU0)
    obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = 2 / c := ⟨_, rfl⟩
    have hμ : 0 < μ := by rw [hμdef]; positivity
    have hμinv : μ⁻¹ = c / 2 := by rw [hμdef]; field_simp
    have hcontB : ContinuousOn F (Metric.ball xbar ρ0) := hcont.mono fun z hz => (hρ0U hz).2
    have hcx : ContinuousAt F xbar := hcontB.continuousAt (Metric.ball_mem_nhds _ hρ0)
    obtain ⟨δF, hδF, hδF'⟩ := Metric.continuousAt_iff.mp hcx (ρ0 / (16 * μ)) (by positivity)
    refine ⟨μ, rfl, hμ, Metric.ball xbar (min (ρ0 / 4) δF),
      Metric.ball_mem_nhds _ (lt_min (by positivity) hδF),
      Metric.ball (F xbar) (ρ0 / (16 * μ)), Metric.ball_mem_nhds _ (by positivity),
      fun x hx y hy w hw => ?_⟩
    rw [sv, Set.mem_singleton_iff] at hw
    subst hw
    have hxb : ‖x - xbar‖ < ρ0 / 4 := by
      rw [Metric.mem_ball, dist_eq_norm] at hx; exact lt_of_lt_of_le hx (min_le_left _ _)
    have hFx : ‖F x - F xbar‖ < ρ0 / (16 * μ) := by
      rw [← dist_eq_norm]; apply hδF'
      rw [Metric.mem_ball] at hx; exact lt_of_lt_of_le hx (min_le_right _ _)
    have hyb : ‖y - F xbar‖ < ρ0 / (16 * μ) := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    suffices hmain : ∃ z, F z = y ∧ ‖z - x‖ ≤ μ * ‖y - F x‖ by
      obtain ⟨z, hz, hzx⟩ := hmain
      have hz' : z ∈ {x' | y ∈ sv F x'} := by simp [sv, hz]
      exact ⟨⟨z, hz'⟩, (Metric.infDist_le_dist_of_mem hz').trans
        (by rw [dist_eq_norm, norm_sub_rev]; exact hzx)⟩
    rcases eq_or_lt_of_le (norm_nonneg (y - F x)) with hr | hr
    · refine ⟨x, ?_, by simp only [sub_self, norm_zero]; positivity⟩
      exact (sub_eq_zero.mp (norm_eq_zero.mp hr.symm)).symm
    set r := ‖y - F x‖ with hrdef
    have hr8 : 2 * μ * r < ρ0 / 4 := by
      have : r ≤ ‖y - F xbar‖ + ‖F x - F xbar‖ := by
        rw [hrdef]
        calc ‖y - F x‖ = ‖(y - F xbar) - (F x - F xbar)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      have h16 : ρ0 / (16 * μ) * (16 * μ) = ρ0 := by field_simp
      nlinarith
    set K := Metric.closedBall x (2 * μ * r) with hK
    have hKB : K ⊆ Metric.ball xbar (ρ0 / 2) := by
      intro z hz
      rw [hK, Metric.mem_closedBall, dist_eq_norm] at hz
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖z - xbar‖ = ‖(z - x) + (x - xbar)‖ := by congr 1; abel
        _ ≤ ‖z - x‖ + ‖x - xbar‖ := norm_add_le _ _
        _ < ρ0 / 2 := by linarith
    have hB2 : Metric.ball xbar (ρ0 / 2) ⊆ Metric.ball xbar ρ0 :=
      Metric.ball_subset_ball (by linarith)
    have hcK : ContinuousOn (fun z => ‖F z - y‖ + μ⁻¹ * ‖z - x‖) K := by
      have h1 : ContinuousOn (fun z => ‖F z - y‖) K :=
        ((hcontB.mono (hKB.trans hB2)).sub continuousOn_const).norm
      exact h1.add (by fun_prop)
    obtain ⟨zs, hzsK, hzmin⟩ := (isCompact_closedBall x (2 * μ * r)).exists_isMinOn
      ⟨x, Metric.mem_closedBall_self (by positivity)⟩ hcK
    have hmin : ∀ z ∈ K, ‖F zs - y‖ + μ⁻¹ * ‖zs - x‖ ≤ ‖F z - y‖ + μ⁻¹ * ‖z - x‖ :=
      fun z hz => isMinOn_iff.mp hzmin z hz
    have h0 := hmin x (Metric.mem_closedBall_self (by positivity))
    simp only [sub_self, norm_zero, mul_zero, add_zero] at h0
    have hzx : ‖zs - x‖ ≤ μ * (r - ‖F zs - y‖) := by
      have : μ⁻¹ * ‖zs - x‖ ≤ r - ‖F zs - y‖ := by rw [hrdef] at *; linarith [norm_sub_rev y (F x)]
      rwa [inv_mul_le_iff₀ hμ] at this
    by_cases hFz : F zs = y
    · refine ⟨zs, hFz, ?_⟩
      rw [hFz, sub_self, norm_zero, sub_zero] at hzx
      exact hzx
    exfalso
    have hN : 0 < ‖F zs - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hFz)
    have hzx' : ‖zs - x‖ ≤ μ * r := by nlinarith
    have hzsB : zs ∈ Metric.ball xbar (ρ0 / 2) := hKB hzsK
    have hczs : ContinuousAt F zs := hcontB.continuousAt (Metric.isOpen_ball.mem_nhds (hB2 hzsB))
    obtain ⟨τ, hτ, hτ'⟩ := Metric.continuousAt_iff.mp hczs ‖F zs - y‖ hN
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = min (μ * r) (ρ0 / 4) := ⟨_, rfl⟩
    have hR : 0 < R := by rw [hRdef]; exact lt_min (by positivity) (by positivity)
    have hRK : Metric.ball zs R ⊆ K := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [hK, Metric.mem_closedBall, dist_eq_norm]
      have : R ≤ μ * r := by rw [hRdef]; exact min_le_left _ _
      calc ‖z - x‖ = ‖(z - zs) + (zs - x)‖ := by congr 1; abel
        _ ≤ ‖z - zs‖ + ‖zs - x‖ := norm_add_le _ _
        _ ≤ 2 * μ * r := by linarith
    have hv : P2MSumRule.RS (fun z => ‖F z - y‖ + μ⁻¹ * ‖z - x‖) zs 0 := by
      intro ε hε
      filter_upwards [Metric.ball_mem_nhds zs hR] with z hz
      have := hmin z (hRK hz)
      rw [inner_zero_left]
      have := norm_nonneg (z - zs)
      nlinarith
    have hc1 : ContinuousOn (fun z => ‖F z - y‖) (Metric.ball zs R) :=
      ((hcontB.mono (hRK.trans (hKB.trans hB2))).sub continuousOn_const).norm
    have hc2 : ContinuousOn (fun z => μ⁻¹ * ‖z - x‖) (Metric.ball zs R) := by fun_prop
    have hL : 1 ≤ max μ⁻¹ 1 := le_max_right _ _
    have hf2 : ∀ y1 ∈ Metric.ball zs R, ∀ z1 ∈ Metric.ball zs R,
        |μ⁻¹ * ‖y1 - x‖ - μ⁻¹ * ‖z1 - x‖| ≤ max μ⁻¹ 1 * ‖y1 - z1‖ := by
      intro y1 _ z1 _
      rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hμ)]
      have h1 := abs_norm_sub_norm_le (y1 - x) (z1 - x)
      rw [show y1 - x - (z1 - x) = y1 - z1 by abel] at h1
      calc μ⁻¹ * |‖y1 - x‖ - ‖z1 - x‖| ≤ μ⁻¹ * ‖y1 - z1‖ :=
            mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hμ).le
        _ ≤ max μ⁻¹ 1 * ‖y1 - z1‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    obtain ⟨a, b, w1, w2, ha, hb, hw1, hw2, hsum⟩ :=
      P2MSumRule.fuzzy (f1 := fun z => ‖F z - y‖) (f2 := fun z => μ⁻¹ * ‖z - x‖) hL hR hc1 hc2 hf2
        hv (η := min (c / 4) (min τ (ρ0 / 4))) (by positivity)
    have ha1 : ‖a - zs‖ < τ := lt_of_lt_of_le ha ((min_le_right _ _).trans (min_le_left _ _))
    have ha2 : ‖a - zs‖ < ρ0 / 4 := lt_of_lt_of_le ha ((min_le_right _ _).trans (min_le_right _ _))
    have hsum' : ‖w1 + w2‖ < c / 4 := by
      have := lt_of_lt_of_le hsum (min_le_left _ _); rwa [sub_zero] at this
    have hw2b : ‖w2‖ ≤ μ⁻¹ := by
      refine P2MSumRule.rs_bound (inv_pos.mpr hμ).le Filter.univ_mem (fun z _ => ?_) hw2
      rw [← mul_sub]
      have h1 := abs_norm_sub_norm_le (z - x) (b - x)
      rw [show z - x - (b - x) = z - b by abel] at h1
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans h1) (inv_pos.mpr hμ).le
    have hw1b : ‖w1‖ < 3 * c / 4 := by
      have : ‖w1‖ ≤ ‖w1 + w2‖ + ‖w2‖ := by
        calc ‖w1‖ = ‖(w1 + w2) - w2‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      rw [hμinv] at hw2b
      linarith
    have hFa : F a ≠ y := by
      intro hFa
      have := hτ' (show dist a zs < τ by rw [dist_eq_norm]; exact ha1)
      rw [hFa, dist_eq_norm, norm_sub_rev] at this
      exact lt_irrefl _ this
    have hreg := P2MMord.chain_reg hFa hw1
    have hcod : w1 ∈ coderiv (sv F) a (F a) (‖F a - y‖⁻¹ • (F a - y)) :=
      ⟨by simp [gph, sv], fun _ => (a, F a), fun _ => _, fun _ => by simp [gph, sv],
        tendsto_const_nhds, tendsto_const_nhds, fun _ => hreg⟩
    have haU : a ∈ U := by
      refine (hρ0U ?_).1
      rw [Metric.mem_ball, dist_eq_norm]
      have : ‖zs - xbar‖ < ρ0 / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hzsB
      calc ‖a - xbar‖ = ‖(a - zs) + (zs - xbar)‖ := by congr 1; abel
        _ ≤ ‖a - zs‖ + ‖zs - xbar‖ := norm_add_le _ _
        _ < ρ0 := by linarith
    have hfin := hbd a haU _ w1 hcod
    have hN' : 0 < ‖F a - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hFa)
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hN'.ne', mul_one] at hfin
    linarith
