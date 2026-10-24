-- Prove2me | solution 1 for GenNewtonSubgrad.ProxReg.lemma_6_3_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:52:09.40763+00:00
-- url     : https://prove2.me/submissions/66b7e3f3-0c1f-41c3-97dc-23b396862f14

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

end P2MProxCore

theorem solution {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar vbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ)
    (hreg : IsContProxRegularAt φ xbar vbar r ε) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ W ∈ 𝓝 (xbar + lam • vbar),
        ∃ p : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
          (∀ x ∈ W, prox φ lam x = {p x}) ∧
          (∀ x ∈ W, ∀ y ∈ W, 0 ≤ ⟪p x - p y, x - y⟫_ℝ) ∧
          (∃ L, LipschitzOnWith L p W) ∧
          prox φ lam (xbar + lam • vbar) = {xbar} := by
  obtain ⟨lam₀, h0, h1, -, H⟩ := P2MProxCore.core2 φ xbar vbar r ε hproper hbdd hreg.1
  refine ⟨lam₀, h0, h1, fun lam hlam hlt => ?_⟩
  have hr : 0 < r := hreg.1.2.1
  have hlr : lam * r < 1 := by
    have := mul_lt_mul_of_pos_right (lt_of_lt_of_le hlt h1) hr
    rwa [inv_mul_cancel₀ hr.ne'] at this
  have hκ : 0 < 1 - lam * r := by linarith
  obtain ⟨ρ, hρ, P, HP, Hm, Hb⟩ := H lam hlam hlt 1 one_pos
  refine ⟨Metric.ball (xbar + lam • vbar) ρ, Metric.ball_mem_nhds _ hρ, P,
    fun x hx => (HP x hx).1, fun x hx y hy => ?_, ⟨_, LipschitzOnWith.of_dist_le'
      (K := (1 - lam * r)⁻¹) ?_⟩, ?_⟩
  · have := Hm x hx y hy
    have : 0 ≤ (1 - lam * r) * ‖P x - P y‖ ^ 2 := by positivity
    linarith
  · intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm, inv_mul_eq_div, le_div_iff₀ hκ]
    have h := Hm x hx y hy
    have hcs := real_inner_le_norm (P x - P y) (x - y)
    rcases eq_or_lt_of_le (norm_nonneg (P x - P y)) with h0 | h0
    · rw [← h0, zero_mul]; exact norm_nonneg _
    · have : ‖P x - P y‖ * (1 - lam * r) * ‖P x - P y‖ ≤ ‖x - y‖ * ‖P x - P y‖ := by nlinarith
      exact le_of_mul_le_mul_right this h0
  · rw [(HP _ (Metric.mem_ball_self hρ)).1, Hb]
