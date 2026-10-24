-- Prove2me | solution 1 for GenNewtonSubgrad.ProxReg.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:01:39.910514+00:00
-- url     : https://prove2.me/submissions/01f730ef-7ebc-45ec-9af6-b87a98741949

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope

open Filter Topology
open scoped InnerProductSpace
open NonconvexSplitting.Shared GenNewtonSubgrad.ProxReg

namespace P2MProxCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma ereal_ex {a : EReal} (h1 : a ≠ ⊤) (h2 : a ≠ ⊥) : ∃ c : ℝ, a = c :=
  ⟨a.toReal, (EReal.coe_toReal h1 h2).symm⟩

/-- A "good" pair: the localization in which prox-regularity applies. -/
def Good (φ : E → EReal) (xbar vbar : E) (ε : ℝ) (u v : E) : Prop :=
  ‖u - xbar‖ ≤ ε ∧ ENear (φ u) (φ xbar) ε ∧ v ∈ LimitingSubdiff φ u ∧ ‖v - vbar‖ ≤ ε

/-- Hypomonotonicity of the localized subdifferential. -/
lemma hypo {φ : E → EReal} {xbar vbar : E} {r ε : ℝ} (hreg : IsProxRegularAt φ xbar vbar r ε)
    {u₁ v₁ u₂ v₂ : E} (h1 : Good φ xbar vbar ε u₁ v₁) (h2 : Good φ xbar vbar ε u₂ v₂) :
    -(r * ‖u₁ - u₂‖ ^ 2) ≤ ⟪v₁ - v₂, u₁ - u₂⟫_ℝ := by
  obtain ⟨-, -, -, -, hpr⟩ := hreg
  have m1 : u₁ ∈ Metric.closedBall xbar ε := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact h1.1
  have m2 : u₂ ∈ Metric.closedBall xbar ε := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact h2.1
  have n1 : v₁ ∈ Metric.closedBall vbar ε := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact h1.2.2.2
  have n2 : v₂ ∈ Metric.closedBall vbar ε := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact h2.2.2.2
  have a1 := hpr u₂ m2 u₁ m1 h1.2.1 v₁ ⟨h1.2.2.1, n1⟩
  have a2 := hpr u₁ m1 u₂ m2 h2.2.1 v₂ ⟨h2.2.2.1, n2⟩
  obtain ⟨c1, hc1⟩ := ereal_ex h1.2.1.1 h1.2.1.2.1
  obtain ⟨c2, hc2⟩ := ereal_ex h2.2.1.1 h2.2.1.2.1
  rw [hc1, hc2] at a1 a2
  have b1 : c1 + (⟪v₁, u₂ - u₁⟫_ℝ - r / 2 * ‖u₂ - u₁‖ ^ 2) ≤ c2 := by exact_mod_cast a1
  have b2 : c2 + (⟪v₂, u₁ - u₂⟫_ℝ - r / 2 * ‖u₁ - u₂‖ ^ 2) ≤ c1 := by exact_mod_cast a2
  have e1 : ‖u₂ - u₁‖ = ‖u₁ - u₂‖ := norm_sub_rev _ _
  have e2 : ⟪v₁, u₂ - u₁⟫_ℝ = -⟪v₁, u₁ - u₂⟫_ℝ := by rw [← inner_neg_right, neg_sub]
  rw [e1, e2] at b1
  rw [inner_sub_left]
  linarith

/-- Fermat's rule for the proximal problem. -/
lemma fermat {φ : E → EReal} {lam : ℝ} (hlam : 0 < lam) {x p : E} (hp : p ∈ prox φ lam x)
    (hfin : φ p ≠ ⊤) (hbot : ∀ y, φ y ≠ ⊥) : lam⁻¹ • (x - p) ∈ LimitingSubdiff φ p := by
  refine ⟨hfin, fun _ => p, fun _ => lam⁻¹ • (x - p), tendsto_const_nhds, tendsto_const_nhds,
    tendsto_const_nhds, fun _ => ?_⟩
  refine ⟨hfin, fun ε' hε' => ?_⟩
  have hball : Metric.ball p (2 * lam * ε') ∈ 𝓝 p := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hball] with z hz
  have hmin := hp z
  obtain ⟨c, hc⟩ := ereal_ex hfin (hbot p)
  rcases eq_or_ne (φ z) ⊤ with hz' | hz'
  · rw [hz']; exact le_top
  obtain ⟨d, hd⟩ := ereal_ex hz' (hbot z)
  rw [hc, hd] at hmin ⊢
  have h1 : c + ‖p - x‖ ^ 2 / (2 * lam) ≤ d + ‖z - x‖ ^ 2 / (2 * lam) := by exact_mod_cast hmin
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have hz2 : ‖z - p‖ < 2 * lam * ε' := by rwa [Metric.mem_ball, dist_eq_norm] at hz
  have e1 : z - x = (z - p) + (p - x) := by abel
  have e2 : ‖z - x‖ ^ 2 = ‖z - p‖ ^ 2 + 2 * ⟪z - p, p - x⟫_ℝ + ‖p - x‖ ^ 2 := by
    rw [e1]; exact norm_add_sq_real _ _
  have e3 : ⟪lam⁻¹ • (x - p), z - p⟫_ℝ = -(lam⁻¹ * ⟪z - p, p - x⟫_ℝ) := by
    rw [real_inner_smul_left, real_inner_comm, ← neg_sub p x, inner_neg_right]; ring
  rw [e3]
  have hN : ‖z - p‖ ^ 2 / (2 * lam) ≤ ε' * ‖z - p‖ := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [norm_nonneg (z - p)]
  have e4 : ‖z - x‖ ^ 2 / (2 * lam) =
      ‖z - p‖ ^ 2 / (2 * lam) + lam⁻¹ * ⟪z - p, p - x⟫_ℝ + ‖p - x‖ ^ 2 / (2 * lam) := by
    rw [e2]; field_simp; try ring
  linarith

lemma ar_far (φb A C K M B δ s lam W D Y xb : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hK : 0 < K)
    (hM : M = 2 * A * xb ^ 2 + C + |φb| + K ^ 2 / 2 + 1) (hB : B = 2 * A + M / δ ^ 2)
    (hδ : 0 < δ) (hs : δ < s) (hlam : 0 < lam) (hl1 : lam < 1) (hlB : 8 * lam * B < 1)
    (hW0 : 0 ≤ W) (hW : W < lam * K) (hD : s / 2 ≤ D) (hY0 : 0 ≤ Y) (hY : Y ≤ xb + s)
    (hxb : 0 ≤ xb) :
    φb + W ^ 2 / (2 * lam) < -(A * Y ^ 2) - C + D ^ 2 / (2 * lam) := by
  have hs0 : 0 < s := lt_trans hδ hs
  have hM0 : 0 < M := by rw [hM]; positivity
  have i1 : W ^ 2 / (2 * lam) ≤ K ^ 2 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : W ^ 2 ≤ (lam * K) ^ 2 := pow_le_pow_left₀ hW0 hW.le 2
    nlinarith
  have iY : Y ^ 2 ≤ 2 * xb ^ 2 + 2 * s ^ 2 := by
    have : Y ^ 2 ≤ (xb + s) ^ 2 := pow_le_pow_left₀ hY0 hY 2
    nlinarith [sq_nonneg (xb - s)]
  have iM : M ≤ M / δ ^ 2 * s ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : δ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hδ.le hs.le 2
    nlinarith
  have hD2 : s ^ 2 / 4 ≤ D ^ 2 := by
    have : (s / 2) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (by positivity) hD 2
    nlinarith
  have i2 : 2 * A * s ^ 2 + M < D ^ 2 / (2 * lam) := by
    rw [lt_div_iff₀ (by positivity)]
    have hBs : 2 * A * s ^ 2 + M ≤ B * s ^ 2 := by rw [hB, add_mul]; linarith [iM]
    have : B * s ^ 2 * (2 * lam) < s ^ 2 / 4 := by
      nlinarith [mul_lt_mul_of_pos_right hlB (by positivity : (0:ℝ) < s ^ 2)]
    nlinarith
  have hphi : φb ≤ |φb| := le_abs_self φb
  have hAY : A * Y ^ 2 ≤ A * (2 * xb ^ 2 + 2 * s ^ 2) := mul_le_mul_of_nonneg_left iY hA
  rw [hM] at i2
  nlinarith

lemma ar_p1 (nq nh I1 I2 cp φb lam r W2 : ℝ) (hl : 0 < lam) (hq : 0 ≤ nq) (hh : 0 ≤ nh)
    (hb : φb + (I1 - r / 2 * nq ^ 2) ≤ cp)
    (hm : cp + (nq ^ 2 / (2 * lam) - I1 - I2 / lam + W2 / (2 * lam)) ≤ φb + W2 / (2 * lam))
    (hI2 : I2 ≤ nq * nh) : (1 - lam * r) * nq ≤ 2 * nh := by
  have h1 : nq ^ 2 / (2 * lam) - I2 / lam ≤ r / 2 * nq ^ 2 := by linarith
  have e : nq ^ 2 / (2 * lam) - I2 / lam = (nq ^ 2 - 2 * I2) / (2 * lam) := by
    field_simp; try ring
  rw [e, div_le_iff₀ (by positivity)] at h1
  have h2 : (1 - lam * r) * nq * nq ≤ 2 * nh * nq := by nlinarith
  rcases eq_or_lt_of_le hq with h0 | h0
  · rw [← h0]; linarith
  · exact le_of_mul_le_mul_right h2 h0

lemma ar_p2 (nq nh I1 I2 cp φb lam r W2 vb : ℝ) (hl : 0 < lam) (hq : 0 ≤ nq) (hq1 : nq ≤ 1)
    (hr : 0 < r) (hnh : nh ≤ lam) (hh : 0 ≤ nh)
    (hb : φb + (I1 - r / 2 * nq ^ 2) ≤ cp)
    (hm : cp + (nq ^ 2 / (2 * lam) - I1 - I2 / lam + W2 / (2 * lam)) ≤ φb + W2 / (2 * lam))
    (hI2 : I2 ≤ nq * nh) (hI1 : |I1| ≤ nq * vb) : |cp - φb| ≤ nq * (vb + 1 + r) := by
  have hI2l : I2 / lam ≤ nq := by
    rw [div_le_iff₀ hl]
    have : nq * nh ≤ nq * lam := mul_le_mul_of_nonneg_left hnh hq
    linarith
  have hsq : 0 ≤ nq ^ 2 / (2 * lam) := by positivity
  have hsq1 : nq ^ 2 ≤ nq := by nlinarith
  rw [abs_le] at hI1 ⊢
  obtain ⟨hI1a, hI1b⟩ := hI1
  constructor <;> nlinarith

lemma ar_v (κ nq nh ρ L : ℝ) (hk : 0 < κ) (h1 : κ * nq ≤ 2 * nh) (h2 : nh < ρ)
    (h3 : ρ * (κ + 2) ≤ L) : κ * (nh + nq) < L := by
  nlinarith

variable [ProperSpace E]

theorem core (φ : E → EReal) (xbar vbar : E) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ) (hreg : IsProxRegularAt φ xbar vbar r ε) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∀ τ : ℝ, 0 < τ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Metric.ball (xbar + lam • vbar) ρ,
        (prox φ lam x).Nonempty ∧ ∀ p ∈ prox φ lam x,
          ‖p - xbar‖ < τ ∧ ‖lam⁻¹ • (x - p) - vbar‖ < τ ∧
            Good φ xbar vbar ε p (lam⁻¹ • (x - p)) := by
  obtain ⟨hv, hr, hε, ⟨U, hU, hlsc⟩, hpr⟩ := hreg
  have hfx : φ xbar ≠ ⊤ := hv.1
  obtain ⟨φb, hφb⟩ := ereal_ex hfx (hproper.1 xbar)
  have hself : ENear (φ xbar) (φ xbar) ε :=
    ⟨hfx, hproper.1 xbar, hfx, hproper.1 xbar, by simp [hε]⟩
  have hbase : ∀ y, ‖y - xbar‖ ≤ ε →
      ((φb + (⟪vbar, y - xbar⟫_ℝ - r / 2 * ‖y - xbar‖ ^ 2) : ℝ) : EReal) ≤ φ y := by
    intro y hy
    have := hpr y (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy) xbar
      (Metric.mem_closedBall_self hε.le) hself vbar ⟨hv, Metric.mem_closedBall_self hε.le⟩
    rw [hφb] at this
    rw [EReal.coe_add]; exact this
  obtain ⟨δ₁, hδ₁, hδ₁U⟩ := Metric.mem_nhds_iff.mp hU
  set δ := min (δ₁ / 2) ε with hδdef
  have hδ : 0 < δ := lt_min (by positivity) hε
  have hδε : δ ≤ ε := min_le_right _ _
  have hδU : Metric.closedBall xbar δ ⊆ U := by
    intro y hy
    apply hδ₁U
    rw [Metric.mem_ball]; rw [Metric.mem_closedBall] at hy
    have : δ ≤ δ₁ / 2 := min_le_left _ _
    linarith
  obtain ⟨a, c, hac⟩ := hbdd
  set A := |a| with hA
  set C := |c| with hC
  have hA0 : 0 ≤ A := abs_nonneg a
  have hC0 : 0 ≤ C := abs_nonneg c
  have hlow : ∀ y, ((-(A * ‖y‖ ^ 2) - C : ℝ) : EReal) ≤ φ y := by
    intro y
    refine le_trans ?_ (hac y)
    rw [EReal.coe_le_coe_iff]
    have h1 : a * ‖y‖ ^ 2 ≤ A * ‖y‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self a) (by positivity)
    have h2 : c ≤ C := le_abs_self c
    linarith
  set K := ‖vbar‖ + 1 with hK
  have hK0 : 0 < K := by positivity
  set M := 2 * A * ‖xbar‖ ^ 2 + C + |φb| + K ^ 2 / 2 + 1 with hM
  have hM0 : 0 < M := by positivity
  set B := 2 * A + M / δ ^ 2 with hB
  have hB0 : 0 < B := by positivity
  refine ⟨min (min 1 r⁻¹) (min (δ / (2 * K)) (1 / (8 * B))), ?_, ?_, ?_, ?_⟩
  · refine lt_min (lt_min one_pos (inv_pos.mpr hr)) (lt_min (by positivity) (by positivity))
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_left _ _).trans (min_le_left _ _)
  intro lam hlam hlt τ hτ
  have hl1 : lam < 1 := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_left _ _))
  have hl2 : lam < r⁻¹ := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_right _ _))
  have hl3 : lam < δ / (2 * K) := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _))
  have hl4 : lam < 1 / (8 * B) := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_right _ _))
  have hlr : lam * r < 1 := by
    have := mul_lt_mul_of_pos_right hl2 hr
    rwa [inv_mul_cancel₀ hr.ne'] at this
  set κ := 1 - lam * r with hκ
  have hκ0 : 0 < κ := by linarith
  have hlK : lam * K < δ / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hl3; linarith
  have hlB : 8 * lam * B < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hl4; linarith
  set s₀ := min (min δ 1) (min τ (ε / (2 * (K + r)))) with hs₀
  have hs₀0 : 0 < s₀ := lt_min (lt_min hδ one_pos) (lt_min hτ (by positivity))
  have hs₀δ : s₀ ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hs₀1 : s₀ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hs₀τ : s₀ ≤ τ := (min_le_right _ _).trans (min_le_left _ _)
  have hs₀ε : s₀ * (K + r) ≤ ε / 2 := by
    have : s₀ ≤ ε / (2 * (K + r)) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  set t := min τ ε with ht
  have ht0 : 0 < t := lt_min hτ hε
  set ρ := min (min lam (κ * s₀ / 2)) (lam * t * κ / (κ + 2)) with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min hlam (by positivity)) (by positivity)
  have hρl : ρ ≤ lam := (min_le_left _ _).trans (min_le_left _ _)
  have hρs : ρ ≤ κ * s₀ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hρt : ρ * (κ + 2) ≤ lam * t * κ := by
    have : ρ ≤ lam * t * κ / (κ + 2) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at this
  refine ⟨ρ, hρ0, fun x hx => ?_⟩
  set h := x - (xbar + lam • vbar) with hh
  have hhρ : ‖h‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  have hxdef : x = xbar + (lam • vbar + h) := by rw [hh]; abel
  set w := lam • vbar + h with hw
  have hwn : ‖w‖ < lam * K := by
    calc ‖w‖ ≤ ‖lam • vbar‖ + ‖h‖ := norm_add_le _ _
      _ = lam * ‖vbar‖ + ‖h‖ := by rw [norm_smul, Real.norm_of_nonneg hlam.le]
      _ < lam * ‖vbar‖ + lam := by linarith
      _ = lam * K := by rw [hK]; ring
  have hxbx : xbar - x = -w := by rw [hxdef]; abel
  -- the proximal objective
  have hvalx : φ xbar + ((‖xbar - x‖ ^ 2 / (2 * lam) : ℝ) : EReal) =
      ((φb + ‖w‖ ^ 2 / (2 * lam) : ℝ) : EReal) := by
    rw [hφb, hxbx, norm_neg, EReal.coe_add]
  -- far points are worse than xbar
  have hfar : ∀ y, δ < ‖y - xbar‖ → φ xbar + ((‖xbar - x‖ ^ 2 / (2 * lam) : ℝ) : EReal) <
      φ y + ((‖y - x‖ ^ 2 / (2 * lam) : ℝ) : EReal) := by
    intro y hy
    have hyx : ‖y - xbar‖ / 2 ≤ ‖y - x‖ := by
      have : y - xbar = (y - x) + (x - xbar) := by abel
      have h2 : ‖y - xbar‖ ≤ ‖y - x‖ + ‖x - xbar‖ := by rw [this]; exact norm_add_le _ _
      have h3 : ‖x - xbar‖ = ‖w‖ := by rw [← norm_neg, neg_sub, hxbx, norm_neg]
      linarith
    have hy2 : ‖y‖ ≤ ‖xbar‖ + ‖y - xbar‖ := by
      have : y = (y - xbar) + xbar := by abel
      calc ‖y‖ = ‖(y - xbar) + xbar‖ := by rw [← this]
        _ ≤ ‖y - xbar‖ + ‖xbar‖ := norm_add_le _ _
        _ = ‖xbar‖ + ‖y - xbar‖ := by ring
    have hreal := ar_far φb A C K M B δ ‖y - xbar‖ lam ‖w‖ ‖y - x‖ ‖y‖ ‖xbar‖ hA0 hC0 hK0 hM hB
      hδ hy hlam hl1 hlB (norm_nonneg _) hwn hyx (norm_nonneg _) hy2 (norm_nonneg _)
    rw [hvalx]
    calc ((φb + ‖w‖ ^ 2 / (2 * lam) : ℝ) : EReal)
        < ((-(A * ‖y‖ ^ 2) - C + ‖y - x‖ ^ 2 / (2 * lam) : ℝ) : EReal) := by exact_mod_cast hreal
      _ = ((-(A * ‖y‖ ^ 2) - C : ℝ) : EReal) + ((‖y - x‖ ^ 2 / (2 * lam) : ℝ) : EReal) := by
          rw [EReal.coe_add]
      _ ≤ φ y + ((‖y - x‖ ^ 2 / (2 * lam) : ℝ) : EReal) := by gcongr; exact hlow y
  -- properties of any prox point
  have hprops : ∀ p ∈ prox φ lam x,
      ‖p - xbar‖ < τ ∧ ‖lam⁻¹ • (x - p) - vbar‖ < τ ∧ Good φ xbar vbar ε p (lam⁻¹ • (x - p)) := by
    intro p hp
    have hmin := hp xbar
    have hnear : ‖p - xbar‖ ≤ δ := by
      by_contra hcon
      push Not at hcon
      exact absurd hmin (not_le.mpr (hfar p hcon))
    have hptop : φ p ≠ ⊤ := by
      intro htop
      rw [htop, EReal.top_add_coe, hvalx] at hmin
      exact absurd hmin (not_le.mpr (EReal.coe_lt_top _))
    obtain ⟨cp, hcp⟩ := ereal_ex hptop (hproper.1 p)
    have hb := hbase p (hnear.trans hδε)
    rw [hcp] at hb hmin
    rw [hvalx] at hmin
    have hb' : φb + (⟪vbar, p - xbar⟫_ℝ - r / 2 * ‖p - xbar‖ ^ 2) ≤ cp := by exact_mod_cast hb
    have hmin' : cp + ‖p - x‖ ^ 2 / (2 * lam) ≤ φb + ‖w‖ ^ 2 / (2 * lam) := by
      exact_mod_cast hmin
    set q := p - xbar with hq
    have hpx : p - x = q - w := by rw [hq, hxdef]; abel
    set I1 := ⟪q, vbar⟫_ℝ with hI1
    set I2 := ⟪q, h⟫_ℝ with hI2
    have hI1' : ⟪vbar, q⟫_ℝ = I1 := real_inner_comm _ _
    rw [hI1'] at hb'
    have hdiv : ‖p - x‖ ^ 2 / (2 * lam) =
        ‖q‖ ^ 2 / (2 * lam) - I1 - I2 / lam + ‖w‖ ^ 2 / (2 * lam) := by
      rw [hpx, norm_sub_sq_real, hw, inner_add_right, real_inner_smul_right]
      field_simp; ring
    rw [hdiv] at hmin'
    have hI2le : I2 ≤ ‖q‖ * ‖h‖ := real_inner_le_norm _ _
    have hκq' : κ * ‖q‖ ≤ 2 * ‖h‖ :=
      ar_p1 ‖q‖ ‖h‖ I1 I2 cp φb lam r (‖w‖ ^ 2) hlam (norm_nonneg _) (norm_nonneg _) hb' hmin' hI2le
    have hqs : ‖q‖ < s₀ := by
      have : κ * ‖q‖ < κ * s₀ := by linarith
      exact lt_of_mul_lt_mul_left this hκ0.le
    have hq1 : ‖q‖ ≤ 1 := by linarith
    have hI1abs : |I1| ≤ ‖q‖ * ‖vbar‖ := abs_real_inner_le_norm _ _
    have hcpabs := ar_p2 ‖q‖ ‖h‖ I1 I2 cp φb lam r (‖w‖ ^ 2) ‖vbar‖ hlam (norm_nonneg _) hq1 hr
      (by linarith) (norm_nonneg _) hb' hmin' hI2le hI1abs
    rw [show ‖vbar‖ + 1 + r = K + r by rw [hK]] at hcpabs
    have hqKr : ‖q‖ * (K + r) < ε := by
      have : ‖q‖ * (K + r) ≤ s₀ * (K + r) :=
        mul_le_mul_of_nonneg_right hqs.le (by positivity)
      linarith
    have hENear : ENear (φ p) (φ xbar) ε := by
      refine ⟨hptop, hproper.1 p, hfx, hproper.1 xbar, ?_⟩
      rw [hcp, hφb, EReal.toReal_coe, EReal.toReal_coe]
      linarith
    -- the subgradient
    have hvdef : lam⁻¹ • (x - p) - vbar = lam⁻¹ • (h - q) := by
      have : x - p = lam • vbar + (h - q) := by rw [hxdef, hq, hw]; abel
      rw [this, smul_add, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]; abel
    have hvn : ‖lam⁻¹ • (x - p) - vbar‖ < t := by
      rw [hvdef, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hlam.le)]
      have h1 : ‖h - q‖ ≤ ‖h‖ + ‖q‖ := norm_sub_le _ _
      have h2 : κ * (‖h‖ + ‖q‖) < lam * t * κ := ar_v κ ‖q‖ ‖h‖ ρ _ hκ0 hκq' hhρ hρt
      have h3 : ‖h‖ + ‖q‖ < lam * t := by
        have : κ * (‖h‖ + ‖q‖) < κ * (lam * t) := by linarith
        exact lt_of_mul_lt_mul_left this hκ0.le
      rw [inv_mul_lt_iff₀ hlam]
      linarith
    refine ⟨lt_of_lt_of_le hqs hs₀τ, lt_of_lt_of_le hvn (min_le_left _ _), ?_, hENear,
      fermat hlam hp hptop hproper.1, (lt_of_lt_of_le hvn (min_le_right _ _)).le⟩
    linarith
  refine ⟨?_, hprops⟩
  -- existence of a minimizer
  have hcontg : Continuous fun y : E => ((‖y - x‖ ^ 2 / (2 * lam) : ℝ) : EReal) :=
    continuous_coe_real_ereal.comp (by fun_prop)
  have hlscOn : LowerSemicontinuousOn
      (fun y => φ y + ((‖y - x‖ ^ 2 / (2 * lam) : ℝ) : EReal)) (Metric.closedBall xbar δ) := by
    intro y hy
    apply LowerSemicontinuousAt.lowerSemicontinuousWithinAt
    exact (hlsc y (hδU hy)).add' (hcontg.lowerSemicontinuous.lowerSemicontinuousAt y)
      (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))
  obtain ⟨p, hpB, hpmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    ⟨xbar, Metric.mem_closedBall_self hδ.le⟩ (isCompact_closedBall _ _) hlscOn
  refine ⟨p, fun y => ?_⟩
  by_cases hy : y ∈ Metric.closedBall xbar δ
  · exact isMinOn_iff.mp hpmin y hy
  · rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hy
    exact (isMinOn_iff.mp hpmin xbar (Metric.mem_closedBall_self hδ.le)).trans (hfar y hy).le

lemma prox_hypo {φ : E → EReal} {xbar vbar : E} {r ε lam : ℝ}
    (hreg : IsProxRegularAt φ xbar vbar r ε) (hlam : 0 < lam) {x₁ x₂ p₁ p₂ : E}
    (g1 : Good φ xbar vbar ε p₁ (lam⁻¹ • (x₁ - p₁))) (g2 : Good φ xbar vbar ε p₂ (lam⁻¹ • (x₂ - p₂))) :
    (1 - lam * r) * ‖p₁ - p₂‖ ^ 2 ≤ ⟪p₁ - p₂, x₁ - x₂⟫_ℝ := by
  have H := hypo hreg g1 g2
  have e : lam⁻¹ • (x₁ - p₁) - lam⁻¹ • (x₂ - p₂) = lam⁻¹ • ((x₁ - x₂) - (p₁ - p₂)) := by
    rw [← smul_sub]; congr 1; abel
  rw [e, real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq,
    real_inner_comm] at H
  have H2 := mul_le_mul_of_nonneg_left H hlam.le
  rw [← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at H2
  nlinarith

theorem core2 (φ : E → EReal) (xbar vbar : E) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ) (hreg : IsProxRegularAt φ xbar vbar r ε) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∀ τ : ℝ, 0 < τ → ∃ ρ : ℝ, 0 < ρ ∧ ∃ P : E → E,
        (∀ x ∈ Metric.ball (xbar + lam • vbar) ρ,
          prox φ lam x = {P x} ∧ ‖P x - xbar‖ < τ ∧ ‖lam⁻¹ • (x - P x) - vbar‖ < τ ∧
            Good φ xbar vbar ε (P x) (lam⁻¹ • (x - P x))) ∧
        (∀ x ∈ Metric.ball (xbar + lam • vbar) ρ, ∀ y ∈ Metric.ball (xbar + lam • vbar) ρ,
          (1 - lam * r) * ‖P x - P y‖ ^ 2 ≤ ⟪P x - P y, x - y⟫_ℝ) ∧
        P (xbar + lam • vbar) = xbar := by
  obtain ⟨lam₀, h0, h1, h2, H⟩ := core φ xbar vbar r ε hproper hbdd hreg
  refine ⟨lam₀, h0, h1, h2, fun lam hlam hlt τ hτ => ?_⟩
  have hr : 0 < r := hreg.2.1
  have hlr : lam * r < 1 := by
    have := mul_lt_mul_of_pos_right (lt_of_lt_of_le hlt h1) hr
    rwa [inv_mul_cancel₀ hr.ne'] at this
  obtain ⟨ρ, hρ, Hx⟩ := H lam hlam hlt τ hτ
  classical
  let P : E → E := fun x => if h : (prox φ lam x).Nonempty then h.some else x
  have hP : ∀ x ∈ Metric.ball (xbar + lam • vbar) ρ, P x ∈ prox φ lam x := by
    intro x hx
    have hne := (Hx x hx).1
    simp only [P, dif_pos hne]
    exact hne.some_mem
  have hmono : ∀ x ∈ Metric.ball (xbar + lam • vbar) ρ, ∀ y ∈ Metric.ball (xbar + lam • vbar) ρ,
      ∀ p ∈ prox φ lam x, ∀ q ∈ prox φ lam y,
        (1 - lam * r) * ‖p - q‖ ^ 2 ≤ ⟪p - q, x - y⟫_ℝ := by
    intro x hx y hy p hp q hq
    exact prox_hypo hreg hlam ((Hx x hx).2 p hp).2.2 ((Hx y hy).2 q hq).2.2
  have hx0 : xbar + lam • vbar ∈ Metric.ball (xbar + lam • vbar) ρ := Metric.mem_ball_self hρ
  have huniq : ∀ x ∈ Metric.ball (xbar + lam • vbar) ρ, ∀ p ∈ prox φ lam x, p = P x := by
    intro x hx p hp
    have := hmono x hx x hx p hp (P x) (hP x hx)
    rw [sub_self, inner_zero_right] at this
    have h3 : ‖p - P x‖ ^ 2 ≤ 0 := by
      by_contra hc; push Not at hc; nlinarith
    have : ‖p - P x‖ = 0 := by nlinarith [norm_nonneg (p - P x)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  refine ⟨ρ, hρ, P, fun x hx => ⟨?_, ((Hx x hx).2 (P x) (hP x hx))⟩,
    fun x hx y hy => hmono x hx y hy _ (hP x hx) _ (hP y hy), ?_⟩
  · ext p
    simp only [Set.mem_singleton_iff]
    exact ⟨huniq x hx p, fun h => h ▸ hP x hx⟩
  · -- the base point
    have hv := hreg.1
    have hε := hreg.2.2.1
    have hfx : φ xbar ≠ ⊤ := hv.1
    have gbar : Good φ xbar vbar ε xbar (lam⁻¹ • ((xbar + lam • vbar) - xbar)) := by
      have e : lam⁻¹ • ((xbar + lam • vbar) - xbar) = vbar := by
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
      rw [e]
      exact ⟨by simp [hε.le], ⟨hfx, hproper.1 xbar, hfx, hproper.1 xbar, by simp [hε]⟩, hv,
        by simp [hε.le]⟩
    have := prox_hypo hreg hlam ((Hx _ hx0).2 (P _) (hP _ hx0)).2.2 gbar
    rw [sub_self, inner_zero_right] at this
    have h3 : ‖P (xbar + lam • vbar) - xbar‖ = 0 := by
      have : ‖P (xbar + lam • vbar) - xbar‖ ^ 2 ≤ 0 := by
        by_contra hc; push Not at hc; nlinarith
      nlinarith [norm_nonneg (P (xbar + lam • vbar) - xbar)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)

lemma hasGrad_of_quad [CompleteSpace E] {F : E → ℝ} {g x : E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ x' in 𝓝 x, |F x' - F x - ⟪g, x' - x⟫_ℝ| ≤ C * ‖x' - x‖ ^ 2) :
    HasGradientAt F g x := by
  rw [hasGradientAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hb : Metric.ball x (c / (C + 1)) ∈ 𝓝 x := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [h, hb] with x' h1 h2
  rw [Real.norm_eq_abs]
  have h3 : ‖x' - x‖ < c / (C + 1) := by rwa [Metric.mem_ball, dist_eq_norm] at h2
  rw [lt_div_iff₀ (by positivity)] at h3
  have hd := norm_nonneg (x' - x)
  calc _ ≤ C * ‖x' - x‖ ^ 2 := h1
    _ ≤ c * ‖x' - x‖ := by nlinarith

lemma sdc_nhds {φ : E → EReal} {xbar vbar : E} {ε : ℝ} (hε : 0 < ε) (hfin : φ xbar ≠ ⊤)
    (hbot : φ xbar ≠ ⊥) (hsc : IsSubdiffContinuousAt φ xbar vbar) :
    ∃ η > 0, ∀ u v : E, ‖u - xbar‖ < η → ‖v - vbar‖ < η → v ∈ LimitingSubdiff φ u →
      ENear (φ u) (φ xbar) ε := by
  by_contra hcon
  push Not at hcon
  choose us vs hu hv hs hne using fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  have tu : Tendsto us atTop (𝓝 xbar) := tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun k => norm_nonneg _) (fun k => (hu k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  have tv : Tendsto vs atTop (𝓝 vbar) := tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun k => norm_nonneg _) (fun k => (hv k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  have ht := hsc us vs tu tv hs
  obtain ⟨c, hc⟩ := ereal_ex hfin hbot
  rw [hc] at ht
  have hI : Set.Ioo ((c - ε : ℝ) : EReal) ((c + ε : ℝ) : EReal) ∈ 𝓝 (c : EReal) :=
    Ioo_mem_nhds (by exact_mod_cast (by linarith : c - ε < c))
      (by exact_mod_cast (by linarith : c < c + ε))
  obtain ⟨k, hk⟩ := (ht.eventually hI).exists
  apply hne k
  obtain ⟨h1, h2⟩ := hk
  have hT : φ (us k) ≠ ⊤ := ne_top_of_lt h2
  have hB : φ (us k) ≠ ⊥ := ne_bot_of_gt h1
  obtain ⟨d, hd⟩ := ereal_ex hT hB
  rw [hd] at h1 h2
  have h1' : c - ε < d := by exact_mod_cast h1
  have h2' : d < c + ε := by exact_mod_cast h2
  refine ⟨hT, hB, hfin, hbot, ?_⟩
  rw [hd, hc, EReal.toReal_coe, EReal.toReal_coe, abs_lt]
  constructor <;> linarith

lemma env_eq {φ : E → EReal} {lam : ℝ} {x p : E} (hp : p ∈ prox φ lam x) :
    moreauEnv φ lam x = φ p + ((‖p - x‖ ^ 2 / (2 * lam) : ℝ) : EReal) :=
  le_antisymm (iInf_le _ p) (le_iInf hp)

theorem core3 (φ : E → EReal) (xbar vbar : E) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ) (hreg : IsProxRegularAt φ xbar vbar r ε) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∀ τ : ℝ, 0 < τ → ∃ ρ : ℝ, 0 < ρ ∧ ∃ P : E → E,
        (∀ x ∈ Metric.ball (xbar + lam • vbar) ρ,
          prox φ lam x = {P x} ∧ ‖P x - xbar‖ < τ ∧ ‖lam⁻¹ • (x - P x) - vbar‖ < τ ∧
            Good φ xbar vbar ε (P x) (lam⁻¹ • (x - P x))) ∧
        (∀ x ∈ Metric.ball (xbar + lam • vbar) ρ, ∀ y ∈ Metric.ball (xbar + lam • vbar) ρ,
          (1 - lam * r) * ‖P x - P y‖ ^ 2 ≤ ⟪P x - P y, x - y⟫_ℝ) ∧
        (∀ x ∈ Metric.ball (xbar + lam • vbar) ρ, ∀ y ∈ Metric.ball (xbar + lam • vbar) ρ,
          ‖P x - P y‖ ≤ (1 - lam * r)⁻¹ * ‖x - y‖) ∧
        P (xbar + lam • vbar) = xbar ∧
        (∀ x ∈ Metric.ball (xbar + lam • vbar) ρ, moreauEnv φ lam x ≠ ⊤ ∧ moreauEnv φ lam x ≠ ⊥) ∧
        (∀ x ∈ Metric.ball (xbar + lam • vbar) ρ,
          HasGradientAt (fun z => (moreauEnv φ lam z).toReal) (lam⁻¹ • (x - P x)) x) := by
  obtain ⟨lam₀, h0, h1, h2, H⟩ := core2 φ xbar vbar r ε hproper hbdd hreg
  refine ⟨lam₀, h0, h1, h2, fun lam hlam hlt τ hτ => ?_⟩
  have hr : 0 < r := hreg.2.1
  have hlr : lam * r < 1 := by
    have := mul_lt_mul_of_pos_right (lt_of_lt_of_le hlt h1) hr
    rwa [inv_mul_cancel₀ hr.ne'] at this
  have hκ : 0 < 1 - lam * r := by linarith
  obtain ⟨ρ, hρ, P, HP, Hm, Hb⟩ := H lam hlam hlt τ hτ
  set W := Metric.ball (xbar + lam • vbar) ρ with hW
  have Hlip : ∀ x ∈ W, ∀ y ∈ W, ‖P x - P y‖ ≤ (1 - lam * r)⁻¹ * ‖x - y‖ := by
    intro x hx y hy
    rw [inv_mul_eq_div, le_div_iff₀ hκ]
    have h := Hm x hx y hy
    have hcs := real_inner_le_norm (P x - P y) (x - y)
    rcases eq_or_lt_of_le (norm_nonneg (P x - P y)) with h0 | h0
    · rw [← h0, zero_mul]; exact norm_nonneg _
    · have : ‖P x - P y‖ * (1 - lam * r) * ‖P x - P y‖ ≤ ‖x - y‖ * ‖P x - P y‖ := by nlinarith
      exact le_of_mul_le_mul_right this h0
  -- real-valued envelope on W
  have hfinP : ∀ x ∈ W, ∃ c : ℝ, φ (P x) = c := fun x hx =>
    ereal_ex ((HP x hx).2.2.2.2.1.1) ((HP x hx).2.2.2.2.1.2.1)
  have hPmem : ∀ x ∈ W, P x ∈ prox φ lam x := fun x hx => by
    rw [(HP x hx).1]; exact Set.mem_singleton _
  have henv : ∀ x ∈ W, (moreauEnv φ lam x).toReal =
      (φ (P x)).toReal + ‖P x - x‖ ^ 2 / (2 * lam) := by
    intro x hx
    obtain ⟨c, hc⟩ := hfinP x hx
    rw [env_eq (hPmem x hx), hc, ← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe]
  have hup : ∀ x ∈ W, ∀ x' ∈ W, (moreauEnv φ lam x').toReal ≤
      (φ (P x)).toReal + ‖P x - x'‖ ^ 2 / (2 * lam) := by
    intro x hx x' hx'
    obtain ⟨c, hc⟩ := hfinP x hx
    obtain ⟨c', hc'⟩ := hfinP x' hx'
    have h := iInf_le (fun y => φ y + ((‖y - x'‖ ^ 2 / (2 * lam) : ℝ) : EReal)) (P x)
    have h' : moreauEnv φ lam x' ≤ φ (P x) + ((‖P x - x'‖ ^ 2 / (2 * lam) : ℝ) : EReal) := h
    rw [env_eq (hPmem x' hx'), hc, hc', ← EReal.coe_add, ← EReal.coe_add] at h'
    rw [env_eq (hPmem x' hx'), hc, hc', ← EReal.coe_add, EReal.toReal_coe, EReal.toReal_coe]
    exact_mod_cast h'
  -- one-sided estimate
  have hone : ∀ x ∈ W, ∀ x' ∈ W, (moreauEnv φ lam x').toReal - (moreauEnv φ lam x).toReal -
      ⟪lam⁻¹ • (x - P x), x' - x⟫_ℝ ≤ ‖x' - x‖ ^ 2 / (2 * lam) := by
    intro x hx x' hx'
    have h1 := hup x hx x' hx'
    rw [henv x hx]
    have e : ‖P x - x'‖ ^ 2 = ‖P x - x‖ ^ 2 - 2 * ⟪P x - x, x' - x⟫_ℝ + ‖x' - x‖ ^ 2 := by
      rw [show P x - x' = (P x - x) - (x' - x) by abel]; exact norm_sub_sq_real _ _
    have e2 : ⟪lam⁻¹ • (x - P x), x' - x⟫_ℝ = -(lam⁻¹ * ⟪P x - x, x' - x⟫_ℝ) := by
      rw [real_inner_smul_left, ← neg_sub (P x) x, inner_neg_left]; ring
    rw [e] at h1; rw [e2]
    have e3 : (‖P x - x‖ ^ 2 - 2 * ⟪P x - x, x' - x⟫_ℝ + ‖x' - x‖ ^ 2) / (2 * lam) =
        ‖P x - x‖ ^ 2 / (2 * lam) - lam⁻¹ * ⟪P x - x, x' - x⟫_ℝ + ‖x' - x‖ ^ 2 / (2 * lam) := by
      field_simp; try ring
    linarith
  refine ⟨ρ, hρ, P, HP, Hm, Hlip, Hb, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc⟩ := hfinP x hx
    rw [env_eq (hPmem x hx), hc, ← EReal.coe_add]
    exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  · set C := lam⁻¹ * (1 + (1 - lam * r)⁻¹) + 1 / (2 * lam) with hC
    have hC0 : 0 ≤ C := by positivity
    apply hasGrad_of_quad hC0
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with x' hx'
    have u1 := hone x hx x' hx'
    have u2 := hone x' hx' x hx
    -- lower bound
    have hg : ‖lam⁻¹ • (x' - P x') - lam⁻¹ • (x - P x)‖ ≤
        lam⁻¹ * (1 + (1 - lam * r)⁻¹) * ‖x' - x‖ := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hlam.le)]
      have : ‖x' - P x' - (x - P x)‖ ≤ ‖x' - x‖ + ‖P x' - P x‖ := by
        rw [show x' - P x' - (x - P x) = (x' - x) - (P x' - P x) by abel]; exact norm_sub_le _ _
      have hl := Hlip x' hx' x hx
      have : ‖x' - P x' - (x - P x)‖ ≤ (1 + (1 - lam * r)⁻¹) * ‖x' - x‖ := by linarith
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hlam.le)
    have hcs := abs_real_inner_le_norm (lam⁻¹ • (x' - P x') - lam⁻¹ • (x - P x)) (x' - x)
    have e1 : ⟪lam⁻¹ • (x' - P x'), x - x'⟫_ℝ = -⟪lam⁻¹ • (x' - P x'), x' - x⟫_ℝ := by
      rw [← inner_neg_right, neg_sub]
    have e2 : ‖x - x'‖ = ‖x' - x‖ := norm_sub_rev _ _
    rw [e1, e2] at u2
    rw [inner_sub_left] at hcs
    have hd := norm_nonneg (x' - x)
    have f1 := mul_le_mul_of_nonneg_right hg hd
    have f2 := (abs_le.mp (hcs.trans f1)).1
    have hL : 0 ≤ lam⁻¹ * (1 + (1 - lam * r)⁻¹) * ‖x' - x‖ * ‖x' - x‖ := by positivity
    have q1 : -(C * ‖x' - x‖ ^ 2) = -(lam⁻¹ * (1 + (1 - lam * r)⁻¹) * ‖x' - x‖ * ‖x' - x‖) -
        ‖x' - x‖ ^ 2 / (2 * lam) := by rw [hC]; ring
    have q2 : C * ‖x' - x‖ ^ 2 = lam⁻¹ * (1 + (1 - lam * r)⁻¹) * ‖x' - x‖ * ‖x' - x‖ +
        ‖x' - x‖ ^ 2 / (2 * lam) := by rw [hC]; ring
    rw [abs_le, q1, q2]
    constructor <;> linarith

theorem core4 (φ : E → EReal) (xbar vbar : E) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ)
    (hreg : IsContProxRegularAt φ xbar vbar r ε) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ W V : Set E, IsOpen W ∧ IsOpen V ∧ xbar + lam • vbar ∈ W ∧
        (∀ x ∈ W, (prox φ lam x).Nonempty ∧ ∀ p ∈ prox φ lam x,
          HasGradientAt (fun z => (moreauEnv φ lam z).toReal) (lam⁻¹ • (x - p)) x) ∧
        (∀ x ∈ W, gradient (fun z => (moreauEnv φ lam z).toReal) x ∈ V) ∧
        (∀ x ∈ W, {v | v ∈ V ∧ v ∈ LimitingSubdiff φ (x - lam • v)} =
          {gradient (fun z => (moreauEnv φ lam z).toReal) x}) := by
  have hε : 0 < ε := hreg.1.2.2.1
  have hv := hreg.1.1
  obtain ⟨η, hη, Hη⟩ := sdc_nhds hε hv.1 (hproper.1 xbar) hreg.2
  set m := min η ε with hm
  have hm0 : 0 < m := lt_min hη hε
  obtain ⟨lam₀, h0, h1, hl1, H⟩ := core3 φ xbar vbar r ε hproper hbdd hreg.1
  refine ⟨lam₀, h0, h1, fun lam hlam hlt => ?_⟩
  obtain ⟨ρ, hρ, P, HP, Hm, -, -, -, Hgrad⟩ := H lam hlam hlt (m / 2) (by positivity)
  have hr : 0 < r := hreg.1.2.1
  have hlr : lam * r < 1 := by
    have := mul_lt_mul_of_pos_right (lt_of_lt_of_le hlt h1) hr
    rwa [inv_mul_cancel₀ hr.ne'] at this
  have hκ : 0 < 1 - lam * r := by linarith
  have hlam1 : lam < 1 := lt_of_lt_of_le hlt hl1
  set ρ' := min ρ (m / 2) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ (by positivity)
  have hsub : Metric.ball (xbar + lam • vbar) ρ' ⊆ Metric.ball (xbar + lam • vbar) ρ :=
    Metric.ball_subset_ball (min_le_left _ _)
  refine ⟨Metric.ball (xbar + lam • vbar) ρ', Metric.ball vbar (m / 2), Metric.isOpen_ball,
    Metric.isOpen_ball, Metric.mem_ball_self hρ'0, fun x hx => ?_, fun x hx => ?_,
    fun x hx => ?_⟩
  · have hx' := hsub hx
    refine ⟨⟨P x, by rw [(HP x hx').1]; exact Set.mem_singleton _⟩, fun p hp => ?_⟩
    rw [(HP x hx').1] at hp
    rw [Set.mem_singleton_iff.mp hp]
    exact Hgrad x hx'
  · have hx' := hsub hx
    rw [(Hgrad x hx').gradient, Metric.mem_ball, dist_eq_norm]
    exact (HP x hx').2.2.1
  · have hx' := hsub hx
    rw [(Hgrad x hx').gradient]
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hvV, hvs⟩
      rw [Metric.mem_ball, dist_eq_norm] at hvV
      have hxx : ‖x - (xbar + lam • vbar)‖ < m / 2 := by
        have := hx; rw [Metric.mem_ball, dist_eq_norm] at this
        exact lt_of_lt_of_le this (min_le_right _ _)
      have hu : ‖x - lam • v - xbar‖ < m := by
        have e : x - lam • v - xbar = (x - (xbar + lam • vbar)) - lam • (v - vbar) := by
          rw [smul_sub]; abel
        rw [e]
        calc _ ≤ ‖x - (xbar + lam • vbar)‖ + ‖lam • (v - vbar)‖ := norm_sub_le _ _
          _ = ‖x - (xbar + lam • vbar)‖ + lam * ‖v - vbar‖ := by
              rw [norm_smul, Real.norm_of_nonneg hlam.le]
          _ < m / 2 + 1 * (m / 2) := by
              have : lam * ‖v - vbar‖ ≤ 1 * (m / 2) :=
                mul_le_mul hlam1.le hvV.le (norm_nonneg _) zero_le_one
              linarith
          _ = m := by ring
      have hmη : m ≤ η := min_le_left _ _
      have hmε : m ≤ ε := min_le_right _ _
      have hev : lam⁻¹ • (x - (x - lam • v)) = v := by
        rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
      have gu : Good φ xbar vbar ε (x - lam • v) (lam⁻¹ • (x - (x - lam • v))) := by
        rw [hev]
        exact ⟨by linarith, Hη _ _ (by linarith) (by linarith) hvs, hvs, by linarith⟩
      have := prox_hypo hreg.1 hlam gu (HP x hx').2.2.2
      rw [sub_self, inner_zero_right] at this
      have h3 : ‖x - lam • v - P x‖ = 0 := by
        have : ‖x - lam • v - P x‖ ^ 2 ≤ 0 := by
          by_contra hc; push Not at hc; nlinarith
        nlinarith [norm_nonneg (x - lam • v - P x)]
      have h4 : x - lam • v = P x := sub_eq_zero.mp (norm_eq_zero.mp h3)
      rw [← h4, hev]
    · rintro rfl
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm]; exact (HP x hx').2.2.1
      · have e : x - lam • (lam⁻¹ • (x - P x)) = P x := by
          rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, sub_sub_cancel]
        rw [e]; exact (HP x hx').2.2.2.2.2.1

def Tf (lam : ℝ) : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.fst ℝ E E - lam • ContinuousLinearMap.snd ℝ E E).prod
    (ContinuousLinearMap.snd ℝ E E)

def Ti (lam : ℝ) : E × E →L[ℝ] E × E :=
  (ContinuousLinearMap.fst ℝ E E + lam • ContinuousLinearMap.snd ℝ E E).prod
    (ContinuousLinearMap.snd ℝ E E)

lemma Tf_apply (lam : ℝ) (w : E × E) : Tf lam w = (w.1 - lam • w.2, w.2) := rfl
lemma Ti_apply (lam : ℝ) (w : E × E) : Ti lam w = (w.1 + lam • w.2, w.2) := rfl
lemma Ti_Tf (lam : ℝ) (w : E × E) : Ti lam (Tf lam w) = w := by
  rw [Ti_apply, Tf_apply]; ext <;> simp
lemma Tf_Ti (lam : ℝ) (w : E × E) : Tf lam (Ti lam w) = w := by
  rw [Ti_apply, Tf_apply]; ext <;> simp

def Tadj (lam : ℝ) (a : E × E) : E × E := (a.1, a.2 - lam • a.1)
def Tadj' (lam : ℝ) (a : E × E) : E × E := (a.1, a.2 + lam • a.1)
lemma Tadj_Tadj' (lam : ℝ) (a : E × E) : Tadj lam (Tadj' lam a) = a := by
  simp [Tadj, Tadj']
lemma Tadj'_Tadj (lam : ℝ) (a : E × E) : Tadj' lam (Tadj lam a) = a := by
  simp [Tadj, Tadj']

lemma pair_Tf (lam : ℝ) (a w : E × E) : pairInner a (Tf lam w) = pairInner (Tadj lam a) w := by
  simp only [pairInner, Tf_apply, Tadj, inner_sub_right, inner_sub_left, real_inner_smul_right,
    real_inner_smul_left]
  rw [real_inner_comm w.2 a.1]; ring

lemma regNormal_T {lam : ℝ} {G S O : Set (E × E)} (hO : IsOpen O)
    (hGS : ∀ w ∈ O, w ∈ G ↔ Tf lam w ∈ S) {z : E × E} (hz : z ∈ O) (a : E × E) :
    a ∈ regNormal S (Tf lam z) ↔ Tadj lam a ∈ regNormal G z := by
  constructor
  · rintro ⟨hzS, ha⟩
    refine ⟨(hGS z hz).mpr hzS, fun ε hε => ?_⟩
    have hc : 0 < ‖Tf (E := E) lam‖ + 1 := by positivity
    have h1 := ha (ε / (‖Tf (E := E) lam‖ + 1)) (by positivity)
    have hT : Tendsto (Tf lam) (𝓝 z) (𝓝 (Tf lam z)) := (Tf lam).continuous.tendsto z
    filter_upwards [hT.eventually h1, hO.mem_nhds hz] with w hw hwO hwG
    have := hw ((hGS w hwO).mp hwG)
    rw [← map_sub, pair_Tf] at this
    have hn : ‖Tf lam (w - z)‖ ≤ (‖Tf (E := E) lam‖ + 1) * ‖w - z‖ :=
      ((Tf (E := E) lam).le_opNorm (w - z)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    calc pairInner (Tadj lam a) (w - z) ≤ ε / (‖Tf (E := E) lam‖ + 1) * ‖Tf lam (w - z)‖ := this
      _ ≤ ε / (‖Tf (E := E) lam‖ + 1) * ((‖Tf (E := E) lam‖ + 1) * ‖w - z‖) := by gcongr
      _ = ε * ‖w - z‖ := by field_simp
  · rintro ⟨hzG, ha⟩
    refine ⟨(hGS z hz).mp hzG, fun ε hε => ?_⟩
    have hc : 0 < ‖Ti (E := E) lam‖ + 1 := by positivity
    have h1 := ha (ε / (‖Ti (E := E) lam‖ + 1)) (by positivity)
    have hT : Tendsto (Ti lam) (𝓝 (Tf lam z)) (𝓝 z) := by
      have := (Ti lam).continuous.tendsto (Tf lam z); rwa [Ti_Tf] at this
    have hO' : ∀ᶠ p in 𝓝 (Tf lam z), Ti lam p ∈ O := hT.eventually (hO.mem_nhds hz)
    filter_upwards [hT.eventually h1, hO'] with p hp hpO hpS
    have hpG : Ti lam p ∈ G := (hGS _ hpO).mpr (by rwa [Tf_Ti])
    have h2 := hp hpG
    have e : p - Tf lam z = Tf lam (Ti lam p - z) := by rw [map_sub, Tf_Ti]
    have e2 : Ti lam p - z = Ti lam (p - Tf lam z) := by rw [map_sub, Ti_Tf]
    have hn : ‖Ti lam p - z‖ ≤ (‖Ti (E := E) lam‖ + 1) * ‖p - Tf lam z‖ := by
      rw [e2]; exact ((Ti (E := E) lam).le_opNorm (p - Tf lam z)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    calc pairInner a (p - Tf lam z) = pairInner (Tadj lam a) (Ti lam p - z) := by
          rw [e, pair_Tf]
      _ ≤ ε / (‖Ti (E := E) lam‖ + 1) * ‖Ti lam p - z‖ := h2
      _ ≤ ε / (‖Ti (E := E) lam‖ + 1) * ((‖Ti (E := E) lam‖ + 1) * ‖p - Tf lam z‖) := by gcongr
      _ = ε * ‖p - Tf lam z‖ := by field_simp

lemma limNormal_T {lam : ℝ} {G S O : Set (E × E)} (hO : IsOpen O)
    (hGS : ∀ w ∈ O, w ∈ G ↔ Tf lam w ∈ S) {z : E × E} (hz : z ∈ O) (a : E × E) :
    a ∈ limNormal S (Tf lam z) ↔ Tadj lam a ∈ limNormal G z := by
  have hTadj : Continuous (Tadj lam : E × E → E × E) := by unfold Tadj; fun_prop
  have hTadj' : Continuous (Tadj' lam : E × E → E × E) := by unfold Tadj'; fun_prop
  constructor
  · rintro ⟨hzS, zs, as, hzsS, hzs, has, hreg⟩
    have hws : Tendsto (fun k => Ti lam (zs k)) atTop (𝓝 z) := by
      have := ((Ti lam).continuous.tendsto _).comp hzs; rwa [Ti_Tf] at this
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hws.eventually (hO.mem_nhds hz))
    refine ⟨(hGS z hz).mpr hzS, fun k => Ti lam (zs (k + N)), fun k => Tadj lam (as (k + N)),
      fun k => ?_, hws.comp (tendsto_add_atTop_nat N),
      ((hTadj.tendsto a).comp has).comp (tendsto_add_atTop_nat N), fun k => ?_⟩
    · exact (hGS _ (hN _ (by omega))).mpr (by rw [Tf_Ti]; exact hzsS _)
    · have h := hreg (k + N)
      rw [← Tf_Ti lam (zs (k + N))] at h
      exact (regNormal_T hO hGS (hN _ (by omega)) _).mp h
  · rintro ⟨hzG, ws, bs, hwsG, hws, hbs, hreg⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hws.eventually (hO.mem_nhds hz))
    have hb' : Tendsto (fun k => Tadj' lam (bs k)) atTop (𝓝 a) := by
      have := (hTadj'.tendsto _).comp hbs; rwa [Tadj'_Tadj] at this
    refine ⟨(hGS z hz).mp hzG, fun k => Tf lam (ws (k + N)), fun k => Tadj' lam (bs (k + N)),
      fun k => (hGS _ (hN _ (by omega))).mp (hwsG _), 
      (((Tf lam).continuous.tendsto z).comp hws).comp (tendsto_add_atTop_nat N),
      hb'.comp (tendsto_add_atTop_nat N), fun k => ?_⟩
    have h := hreg (k + N)
    rw [← Tadj_Tadj' lam (bs (k + N))] at h
    exact (regNormal_T hO hGS (hN _ (by omega)) _).mpr h

end P2MProxCore

theorem solution {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar vbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ)
    (hreg : IsContProxRegularAt φ xbar vbar r ε) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ W ∈ 𝓝 (xbar + lam • vbar),
        (∀ x ∈ W, DifferentiableAt ℝ (fun z => (moreauEnv φ lam z).toReal) x) ∧
        ∀ x ∈ W, ∀ v' x' : EuclideanSpace ℝ (Fin n),
          x' ∈ coderiv (sv (gradient (fun z => (moreauEnv φ lam z).toReal))) x
              (gradient (fun z => (moreauEnv φ lam z).toReal) x) v' ↔
            x' ∈ secondSubdiff φ (x - lam • gradient (fun z => (moreauEnv φ lam z).toReal) x)
              (gradient (fun z => (moreauEnv φ lam z).toReal) x) (v' - lam • x') := by
  obtain ⟨lam₀, h0, h1, H⟩ := P2MProxCore.core4 φ xbar vbar r ε hproper hbdd hreg
  refine ⟨lam₀, h0, h1, fun lam hlam hlt => ?_⟩
  obtain ⟨W, V, hWo, hVo, hx0W, Hgrad, HgV, H67⟩ := H lam hlam hlt
  refine ⟨W, hWo.mem_nhds hx0W, fun x hx => ?_, fun x hx v' x' => ?_⟩
  · obtain ⟨⟨p, hp⟩, hg⟩ := Hgrad x hx
    exact (hg p hp).differentiableAt
  · have hGS : ∀ w ∈ W ×ˢ V,
        w ∈ gph (sv (gradient (fun z => (moreauEnv φ lam z).toReal))) ↔
          P2MProxCore.Tf lam w ∈ gph (NonconvexSplitting.Shared.LimitingSubdiff φ) := by
      rintro ⟨y, v⟩ ⟨hy, hv⟩
      simp only [gph, sv, Set.mem_setOf_eq, Set.mem_singleton_iff, P2MProxCore.Tf_apply]
      have h67 := H67 y hy
      constructor
      · intro h
        have hm : v ∈ {v | v ∈ V ∧ v ∈ NonconvexSplitting.Shared.LimitingSubdiff φ (y - lam • v)} := by
          rw [h67]; exact h
        exact hm.2
      · intro h
        have hm : v ∈ ({gradient (fun z => (moreauEnv φ lam z).toReal) y} : Set _) := by
          rw [← h67]; exact ⟨hv, h⟩
        exact hm
    have hz : (x, gradient (fun z => (moreauEnv φ lam z).toReal) x) ∈ W ×ˢ V := ⟨hx, HgV x hx⟩
    have key := P2MProxCore.limNormal_T (hWo.prod hVo) hGS hz (x', -(v' - lam • x'))
    rw [P2MProxCore.Tf_apply] at key
    have hadj : P2MProxCore.Tadj lam (x', -(v' - lam • x')) = (x', -v') := by
      simp only [P2MProxCore.Tadj, Prod.mk.injEq, true_and]; abel
    rw [hadj] at key
    simp only [secondSubdiff, coderiv, Set.mem_setOf_eq]
    exact key.symm
