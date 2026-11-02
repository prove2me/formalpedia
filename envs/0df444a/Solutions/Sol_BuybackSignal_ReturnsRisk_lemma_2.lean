-- Prove2me | solution 1 for BuybackSignal.ReturnsRisk.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T17:41:45.979596+00:00
-- url     : https://prove2.me/submissions/9fd0b59b-05bb-4ec1-a611-ccc73b3402ff

import Mathlib
import Definitions.Def_BuybackSignal_ReturnsRisk_Model


namespace BBRRSol
open BuybackSignal.ReturnsRisk BuybackSignal.ReturnsRisk.Params

variable (P : Params)

lemma Pi_eq (w r θh θ : ℝ) :
    P.Pi w r θh θ = w * (P.alpha - P.β * w) / 2 +
      P.lamC * P.unsoldLow w r θh P.lam * (w - θ * r) := by
  unfold Params.Pi Params.sR Params.unsoldLow Params.alpha Params.lamC
  ring

lemma unsoldLow_nonneg (w r θh : ℝ) : 0 ≤ P.unsoldLow w r θh P.lam := by
  unfold Params.unsoldLow; positivity

/-- universal bound with the wholesale-price penalty -/
lemma Pi_self_le (hP : P.Standing) (w r θ : ℝ) :
    P.Pi w r θ θ ≤ P.pi0 - P.β / 2 * (w - P.w0) ^ 2 := by
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  rw [Pi_eq]
  have hlc : 0 < P.lamC := by unfold Params.lamC; linarith
  set x := w - θ * r with hx
  unfold Params.unsoldLow
  rcases le_total 0 (P.dAlpha - P.β / P.lam * (w - θ * r)) with hK | hK
  · rw [max_eq_left hK]
    have key : P.pi0 - P.β / 2 * (w - P.w0) ^ 2 -
        (w * (P.alpha - P.β * w) / 2 +
          P.lamC * ((P.dAlpha - P.β / P.lam * x) / 2) * x) =
        P.lamC * P.β / (2 * P.lam) * (x - P.lam * P.dAlpha / (2 * P.β)) ^ 2 := by
      unfold Params.pi0 Params.w0
      field_simp
      ring
    rw [← hx]
    have : 0 ≤ P.lamC * P.β / (2 * P.lam) * (x - P.lam * P.dAlpha / (2 * P.β)) ^ 2 := by
      positivity
    linarith
  · rw [max_eq_right hK]
    have key : P.pi0 - P.β / 2 * (w - P.w0) ^ 2 - w * (P.alpha - P.β * w) / 2 =
        P.lamC * P.lam * P.dAlpha ^ 2 / (8 * P.β) := by
      unfold Params.pi0 Params.w0
      field_simp
      ring
    have : 0 ≤ P.lamC * P.lam * P.dAlpha ^ 2 / (8 * P.β) := by positivity
    simp only [zero_div, mul_zero, zero_mul, add_zero]
    linarith

lemma Pi_self_le_pi0 (hP : P.Standing) (w r θ : ℝ) : P.Pi w r θ θ ≤ P.pi0 := by
  have := Pi_self_le P hP w r θ
  have : 0 ≤ P.β / 2 * (w - P.w0) ^ 2 := by
    have := hP.2.2.1; positivity
  linarith

lemma Pi_diff (w r θh θ θ' : ℝ) :
    P.Pi w r θh θ = P.Pi w r θh θ' + P.lamC * P.unsoldLow w r θh P.lam * (θ' - θ) * r := by
  rw [Pi_eq, Pi_eq]; ring

lemma continuous_Pi (θh θ : ℝ) : Continuous fun c : ℝ × ℝ => P.Pi c.1 c.2 θh θ := by
  unfold Params.Pi Params.sR Params.unsoldLow
  fun_prop

end BBRRSol


namespace BBRRSol
open BuybackSignal.ReturnsRisk BuybackSignal.ReturnsRisk.Params

variable (P : Params)

noncomputable def x0 : ℝ := P.lam * P.dAlpha / (2 * P.β)
noncomputable def aa : ℝ := P.αl / (2 * P.β)
noncomputable def kk : ℝ := P.lamC * P.dTheta / P.θbar
noncomputable def cOf (z : ℝ × ℝ) : ℝ × ℝ := (z.1 + P.w0, (z.1 - z.2 + aa P) / P.θbar)
noncomputable def tc (c : ℝ × ℝ) : ℝ × ℝ := (c.1 - P.w0, c.1 - P.θbar * c.2 - x0 P)

lemma w0_eq (hP : P.Standing) : P.w0 = aa P + x0 P := by
  have hβ := hP.2.2.1
  unfold Params.w0 aa x0 Params.alpha Params.lamC Params.dAlpha
  field_simp; ring

lemma cOf_tc (hP : P.Standing) (c : ℝ × ℝ) : cOf P (tc P c) = c := by
  have hθ : 0 < P.θbar := by obtain ⟨_, _, _, _, _, h6, h7, _⟩ := hP; linarith
  have := w0_eq P hP
  unfold cOf tc
  ext
  · simp
  · simp only
    rw [this]; field_simp; ring

lemma tc_cOf (hP : P.Standing) (z : ℝ × ℝ) : tc P (cOf P z) = z := by
  have hθ : 0 < P.θbar := by obtain ⟨_, _, _, _, _, h6, h7, _⟩ := hP; linarith
  have := w0_eq P hP
  unfold cOf tc
  ext
  · simp
  · simp only
    rw [this]; field_simp; ring

lemma x_cOf (hP : P.Standing) (z : ℝ × ℝ) :
    (cOf P z).1 - P.θbar * (cOf P z).2 = z.2 + x0 P := by
  have hθ : 0 < P.θbar := by obtain ⟨_, _, _, _, _, h6, h7, _⟩ := hP; linarith
  have := w0_eq P hP
  unfold cOf; simp only; rw [this]; field_simp; ring

lemma U_cOf (hP : P.Standing) (z : ℝ × ℝ) (hz : z.2 ≤ x0 P) :
    P.unsoldLow (cOf P z).1 (cOf P z).2 P.θbar P.lam = P.β / (2 * P.lam) * (x0 P - z.2) := by
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  unfold Params.unsoldLow
  rw [x_cOf P ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ z]
  have : P.dAlpha - P.β / P.lam * (z.2 + x0 P) = P.β / P.lam * (x0 P - z.2) := by
    unfold x0; field_simp; ring
  rw [this, max_eq_left]
  · ring
  · have : 0 ≤ x0 P - z.2 := by linarith
    positivity

lemma f_cOf (hP : P.Standing) (z : ℝ × ℝ) (hz : z.2 ≤ x0 P) :
    P.Pi (cOf P z).1 (cOf P z).2 P.θbar P.θbar = P.pi0 - P.β / (2 * P.lam) * P.quad z.1 z.2 := by
  rw [Pi_eq, x_cOf P hP, U_cOf P hP z hz]
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  unfold cOf Params.quad Params.pi0 x0 Params.w0 Params.alpha Params.lamC Params.dAlpha
  simp only
  field_simp
  ring

lemma g_cOf (hP : P.Standing) (z : ℝ × ℝ) (hz : z.2 ≤ x0 P) :
    P.Pi (cOf P z).1 (cOf P z).2 P.θbar P.θlow = P.pi0 - P.β / (2 * P.lam) * P.b6 z.1 z.2 := by
  rw [Pi_diff P _ _ _ _ P.θbar, f_cOf P hP z hz, U_cOf P hP z hz]
  have hθ : 0 < P.θbar := by obtain ⟨_, _, _, _, _, h6, h7, _⟩ := hP; linarith
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  unfold cOf Params.b6 Params.quad x0 aa Params.dTheta
  simp only
  field_simp
  ring

lemma D_eq (hP : P.Standing) :
    P.Pi P.w0 (P.r0 P.θlow) P.θlow P.θbar = P.pi0 - P.β / (2 * P.lam) * P.b7Bound := by
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  have hU : P.unsoldLow P.w0 (P.r0 P.θlow) P.θlow P.lam = P.dAlpha / 4 := by
    unfold Params.unsoldLow Params.w0 Params.r0 Params.alpha Params.lamC Params.dAlpha
    have : P.αh - P.αl - P.β / P.lam * ((P.lam * P.αh + (1 - P.lam) * P.αl) / (2 * P.β) -
        P.θlow * (P.αl / (2 * P.β * P.θlow))) = (P.αh - P.αl) / 2 := by
      field_simp; ring
    rw [this, max_eq_left (by linarith)]; ring
  rw [Pi_eq, hU]
  unfold Params.w0 Params.r0 Params.pi0 Params.b7Bound Params.alpha Params.lamC Params.dAlpha
    Params.dTheta
  field_simp
  ring

lemma low_full (hP : P.Standing) :
    P.Pi P.w0 (P.r0 P.θlow) P.θlow P.θlow = P.pi0 := by
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  have hU : P.unsoldLow P.w0 (P.r0 P.θlow) P.θlow P.lam = P.dAlpha / 4 := by
    unfold Params.unsoldLow Params.w0 Params.r0 Params.alpha Params.lamC Params.dAlpha
    have : P.αh - P.αl - P.β / P.lam * ((P.lam * P.αh + (1 - P.lam) * P.αl) / (2 * P.β) -
        P.θlow * (P.αl / (2 * P.β * P.θlow))) = (P.αh - P.αl) / 2 := by
      field_simp; ring
    rw [this, max_eq_left (by linarith)]; ring
  rw [Pi_eq, hU]
  unfold Params.w0 Params.r0 Params.pi0 Params.alpha Params.lamC Params.dAlpha
  field_simp
  ring

lemma action_cOf (hP : P.Standing) (z : ℝ × ℝ) :
    cOf P z ∈ P.actionSet P.θbar ↔ -x0 P ≤ z.2 ∧ z.2 ≤ z.1 + aa P := by
  have hθ : 0 < P.θbar := by obtain ⟨_, _, _, _, _, h6, h7, _⟩ := hP; linarith
  unfold Params.actionSet
  simp only [Set.mem_setOf_eq]
  have hx := x_cOf P hP z
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    unfold cOf at h1; simp only at h1
    have : 0 ≤ z.1 - z.2 + aa P := by
      by_contra hc; push_neg at hc
      have : (z.1 - z.2 + aa P) / P.θbar < 0 := div_neg_of_neg_of_pos hc hθ
      linarith
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by linarith⟩
    unfold cOf; simp only
    apply div_nonneg (by linarith) hθ.le

end BBRRSol


namespace BBRRSol
open BuybackSignal.ReturnsRisk BuybackSignal.ReturnsRisk.Params Filter Topology

variable (P : Params)

lemma b6_eq (w u : ℝ) : P.b6 w u = P.quad w u + kk P * (w - u + aa P) * (u - x0 P) := by
  unfold Params.b6 kk aa x0; ring

lemma x0_pos (hP : P.Standing) : 0 < x0 P := by
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  unfold x0 Params.dAlpha; have : 0 < P.αh - P.αl := by linarith
  positivity

lemma aa_pos (hP : P.Standing) : 0 < aa P := by
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  unfold aa; positivity

lemma kk_pos (hP : P.Standing) : 0 < kk P := by
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  unfold kk Params.lamC Params.dTheta
  have : 0 < 1 - P.lam := by linarith
  have : 0 < P.θbar - P.θlow := by linarith
  have : 0 < P.θbar := by linarith
  positivity

lemma lamC_pos (hP : P.Standing) : 0 < P.lamC := by
  unfold Params.lamC; linarith [hP.2.2.2.2.1]

/-- the root equation for uDag -/
lemma udag_root (hP : P.Standing) :
    P.θlow * P.uDag ^ 2 + P.dTheta * (aa P + x0 P) * P.uDag - P.dTheta * aa P * x0 P = 0 ∧
    0 < P.uDag := by
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  have hdA : 0 < P.dAlpha := by unfold Params.dAlpha; linarith
  have hdT : 0 < P.dTheta := by unfold Params.dTheta; linarith
  have hal : P.alpha = 2 * P.β * (aa P + x0 P) := by
    unfold aa x0 Params.alpha Params.lamC Params.dAlpha; field_simp; ring
  have hax : P.lam * P.dAlpha * P.αl = 4 * P.β ^ 2 * (aa P * x0 P) := by
    unfold aa x0; field_simp; ring
  have hS0 : 0 ≤ (P.alpha * P.dTheta) ^ 2 + 4 * P.lam * P.dAlpha * P.αl * P.θlow * P.dTheta := by
    positivity
  have hs2 := Real.sq_sqrt hS0
  have hs0 := Real.sqrt_nonneg ((P.alpha * P.dTheta) ^ 2 + 4 * P.lam * P.dAlpha * P.αl * P.θlow * P.dTheta)
  have hu : P.uDag = (-P.alpha * P.dTheta + Real.sqrt ((P.alpha * P.dTheta) ^ 2 +
      4 * P.lam * P.dAlpha * P.αl * P.θlow * P.dTheta)) / (4 * P.β * P.θlow) := rfl
  have hq : (4 * P.β * P.θlow * P.uDag + P.alpha * P.dTheta) ^ 2 =
      (P.alpha * P.dTheta) ^ 2 + 4 * P.lam * P.dAlpha * P.αl * P.θlow * P.dTheta := by
    clear hs0
    generalize Real.sqrt ((P.alpha * P.dTheta) ^ 2 +
      4 * P.lam * P.dAlpha * P.αl * P.θlow * P.dTheta) = t at hu hs2
    rw [hu]; field_simp; linear_combination hs2
  have hgt : 0 < 4 * P.lam * P.dAlpha * P.αl * P.θlow * P.dTheta := by positivity
  refine ⟨?_, ?_⟩
  · rw [hal] at hq
    have h16 : 0 < 16 * P.β ^ 2 * P.θlow := by positivity
    have : 16 * P.β ^ 2 * P.θlow * (P.θlow * P.uDag ^ 2 + P.dTheta * (aa P + x0 P) * P.uDag -
        P.dTheta * aa P * x0 P) = 0 := by linear_combination hq + 4 * P.θlow * P.dTheta * hax
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  · rw [hu]
    apply div_pos _ (by positivity)
    have hal0 : 0 < P.alpha := by unfold Params.alpha Params.lamC; nlinarith
    have : P.alpha * P.dTheta < Real.sqrt ((P.alpha * P.dTheta) ^ 2 +
        4 * P.lam * P.dAlpha * P.αl * P.θlow * P.dTheta) := by
      apply Real.lt_sqrt_of_sq_lt; linarith
    linarith

lemma udag_props (hP : P.Standing) :
    0 < P.uDag ∧ P.uDag < x0 P ∧ P.uDag < aa P ∧ P.b6 0 P.uDag = 0 ∧
    P.quad 0 P.uDag < P.b7Bound := by
  obtain ⟨hr, hpos⟩ := udag_root P hP
  have hx := x0_pos P hP
  have ha := aa_pos P hP
  have hlcp := lamC_pos P hP
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  have hdT : 0 < P.dTheta := by unfold Params.dTheta; linarith
  set u := P.uDag
  have hux : u < x0 P := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg (mul_pos hdT (add_pos ha hx)).le (sub_nonneg.2 hc),
      mul_pos (mul_pos hdT hx) hx, mul_nonneg h3.le (sq_nonneg u)]
  have hua : u < aa P := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg (mul_pos hdT (add_pos ha hx)).le (sub_nonneg.2 hc),
      mul_pos (mul_pos hdT ha) ha, mul_nonneg h3.le (sq_nonneg u)]
  refine ⟨hpos, hux, hua, ?_, ?_⟩
  · have hθ : 0 < P.θbar := by linarith
    have : P.θbar * P.b6 0 u = P.lamC *
        (P.θlow * u ^ 2 + P.dTheta * (aa P + x0 P) * u - P.dTheta * aa P * x0 P) := by
      rw [b6_eq]; unfold Params.quad kk Params.dTheta; field_simp; ring
    rw [hr, mul_zero] at this
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  · have hb : P.b7Bound = P.lamC * P.dTheta * (aa P * x0 P) / P.θlow := by
      unfold Params.b7Bound aa x0; field_simp; ring
    have key : P.θlow * u ^ 2 < P.dTheta * aa P * x0 P := by
      nlinarith [mul_pos hdT (add_pos ha hx)]
    rw [hb, lt_div_iff₀ h3]
    unfold Params.quad
    nlinarith [mul_lt_mul_of_pos_left key hlcp]

lemma udag_feas (hP : P.Standing) : P.TransformedFeasible (0, P.uDag) := by
  obtain ⟨hpos, hux, hua, hb6, hq⟩ := udag_props P hP
  have hx := x0_pos P hP
  unfold Params.TransformedFeasible
  simp only
  refine ⟨?_, ?_, ?_, hb6.symm ▸ le_refl _, hq.le⟩
  · unfold aa at hua; linarith
  · have : -P.lam * P.dAlpha / (2 * P.β) = - x0 P := by unfold x0; ring
    rw [this]; linarith
  · unfold x0 at hux; linarith

lemma feas_iff (z : ℝ × ℝ) : P.TransformedFeasible z ↔
    (z.2 ≤ z.1 + aa P ∧ -x0 P ≤ z.2 ∧ z.2 ≤ x0 P ∧ 0 ≤ P.b6 z.1 z.2 ∧
      P.quad z.1 z.2 ≤ P.b7Bound) := by
  unfold Params.TransformedFeasible aa x0
  have : -P.lam * P.dAlpha / (2 * P.β) = -(P.lam * P.dAlpha / (2 * P.β)) := by ring
  rw [this]

lemma quad_pos_of (hP : P.Standing) (z : ℝ × ℝ) (hb : 0 ≤ P.b6 z.1 z.2) : 0 < P.quad z.1 z.2 := by
  have hl := hP.2.2.2.1
  have hlc := lamC_pos P hP
  unfold Params.quad
  rcases eq_or_ne z.1 0 with h1 | h1
  · rcases eq_or_ne z.2 0 with h2 | h2
    · exfalso
      rw [b6_eq, h1, h2] at hb
      unfold Params.quad at hb
      have := mul_pos (mul_pos (kk_pos P hP) (aa_pos P hP)) (x0_pos P hP)
      nlinarith
    · have := pow_pos (sq_pos_of_ne_zero h2) 1
      positivity
  · have : 0 < z.1 ^ 2 := by positivity
    positivity

lemma ev_pos {φ : ℝ → ℝ} (hφ : Continuous φ) (h0 : 0 < φ 0) :
    ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < φ s :=
  nhdsWithin_le_nhds ((hφ.tendsto 0).eventually (lt_mem_nhds h0))

lemma sol_b6_zero (hP : P.Standing) (z : ℝ × ℝ) (hz : P.IsTransformedSolution z) :
    P.b6 z.1 z.2 = 0 := by
  obtain ⟨hF, hmin⟩ := hz
  have hF' := (feas_iff P z).1 hF
  obtain ⟨hL, hlo, hhi, hb6, hb7⟩ := hF'
  have hqp := quad_pos_of P hP z hb6
  have ha := aa_pos P hP
  by_contra hne
  have hb6p : 0 < P.b6 z.1 z.2 := lt_of_le_of_ne hb6 (Ne.symm hne)
  have e1 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < P.b6 ((1 - s) * z.1) ((1 - s) * z.2) :=
    ev_pos (φ := fun s => P.b6 ((1 - s) * z.1) ((1 - s) * z.2))
      (by unfold Params.b6 Params.quad; fun_prop) (by simpa using hb6p)
  have e2 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < 1 - s :=
    ev_pos (φ := fun s => 1 - s) (by fun_prop) (by norm_num)
  have e3 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s := self_mem_nhdsWithin
  obtain ⟨s, hs1, hs2, hs3⟩ := (e1.and (e2.and e3)).exists
  have hq : P.quad ((1 - s) * z.1) ((1 - s) * z.2) = (1 - s) ^ 2 * P.quad z.1 z.2 := by
    unfold Params.quad; ring
  have hlt : P.quad ((1 - s) * z.1) ((1 - s) * z.2) < P.quad z.1 z.2 := by
    rw [hq]; have : (1 - s) ^ 2 < 1 := by nlinarith
    nlinarith
  have hy : P.TransformedFeasible ((1 - s) * z.1, (1 - s) * z.2) := by
    rw [feas_iff]; simp only
    have hx := x0_pos P hP
    refine ⟨?_, ?_, ?_, hs1.le, by linarith⟩
    · nlinarith
    · nlinarith
    · nlinarith
  have := hmin _ hy
  simp only at this
  linarith

end BBRRSol


namespace BBRRSol
open BuybackSignal.ReturnsRisk BuybackSignal.ReturnsRisk.Params Filter Topology

variable (P : Params)

lemma region (hP : P.Standing) (z : ℝ × ℝ) (hF : P.TransformedFeasible z)
    (hq : P.quad z.1 z.2 ≤ P.quad 0 P.uDag) : z.1 ≤ 0 := by
  obtain ⟨hL, hlo, hhi, hb6, hb7⟩ := (feas_iff P z).1 hF
  obtain ⟨hU, hUx, hUa, hb0, -⟩ := udag_props P hP
  have hk := kk_pos P hP
  have hlc := lamC_pos P hP
  have hl := hP.2.2.2.1
  rw [b6_eq] at hb6 hb0
  unfold Params.quad at hb6 hb0 hq
  set U := P.uDag
  set w := z.1
  set u := z.2
  by_contra hw; push Not at hw
  have hu2 : u ^ 2 ≤ U ^ 2 := by nlinarith [sq_nonneg w]
  have hux : u ≤ U := by nlinarith
  have hux' : -U ≤ u := by nlinarith
  have hA : 0 < aa P - U := by linarith
  have hB : 0 < x0 P - U := by linarith
  have h1 : (aa P - U) * (x0 P - U) ≤ (aa P - u) * (x0 P - u) :=
    mul_le_mul (by linarith) (by linarith) hB.le (by linarith)
  have h2 : 0 < w * (x0 P - u) := mul_pos hw (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h1 hk.le, mul_pos hk h2]

lemma sol_slack (hP : P.Standing) (z : ℝ × ℝ) (hz : P.IsTransformedSolution z) :
    0 < z.1 - z.2 + aa P ∧ -x0 P < z.2 ∧ z.2 < x0 P ∧ P.quad z.1 z.2 < P.b7Bound ∧
    P.quad z.1 z.2 ≤ P.quad 0 P.uDag := by
  have hb := sol_b6_zero P hP z hz
  obtain ⟨hF, hmin⟩ := hz
  obtain ⟨hL, hlo, hhi, hb6, hb7⟩ := (feas_iff P z).1 hF
  obtain ⟨hU, hUx, hUa, hb0, hU7⟩ := udag_props P hP
  have hqm := hmin _ (udag_feas P hP)
  simp only at hqm
  have hlc := lamC_pos P hP
  have hl := hP.2.2.2.1
  have hqp := quad_pos_of P hP z hb6
  refine ⟨?_, ?_, ?_, lt_of_le_of_lt hqm hU7, hqm⟩
  · by_contra hc
    have he : z.1 - z.2 + aa P = 0 := by linarith
    rw [b6_eq, he] at hb; simp at hb; linarith
  · by_contra hc
    have he : z.2 = -x0 P := by linarith
    unfold Params.quad at hqm
    rw [he] at hqm
    have h2 : P.uDag ^ 2 < x0 P ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left h2 hlc, mul_nonneg hl.le (sq_nonneg z.1)]
  · by_contra hc
    have he : z.2 = x0 P := by linarith
    unfold Params.quad at hqm
    rw [he] at hqm
    have h2 : P.uDag ^ 2 < x0 P ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left h2 hlc, mul_nonneg hl.le (sq_nonneg z.1)]

lemma sol_tangent (hP : P.Standing) (z : ℝ × ℝ) (hz : P.IsTransformedSolution z) :
    P.lam * z.1 * (z.1 - 2 * z.2 + aa P + x0 P) + P.lamC * z.2 * (x0 P - z.2) = 0 := by
  have hb := sol_b6_zero P hP z hz
  obtain ⟨hL, hlo, hhi, h7, -⟩ := sol_slack P hP z hz
  obtain ⟨hF, hmin⟩ := hz
  have hk := kk_pos P hP
  set w := z.1
  set u := z.2
  set E := P.lam * w * (w - 2 * u + aa P + x0 P) + P.lamC * u * (x0 P - u)
  by_contra hE
  set G1 := 2 * P.lam * w
  set G2 := 2 * P.lamC * u
  set H1 := 2 * P.lam * w + kk P * (u - x0 P)
  set H2 := 2 * P.lamC * u + kk P * (w - 2 * u + aa P + x0 P)
  have hC : G1 * H2 - G2 * H1 = 2 * kk P * E := by ring
  have hCne : G1 * H2 - G2 * H1 ≠ 0 := by rw [hC]; positivity
  set C := G1 * H2 - G2 * H1
  set d1 := (-H2 - G2) / C
  set d2 := (G1 + H1) / C
  have hGd : G1 * d1 + G2 * d2 = -1 := by
    simp only [d1, d2]; field_simp; ring
  have hHd : H1 * d1 + H2 * d2 = 1 := by
    simp only [d1, d2]; field_simp; ring
  have hqexp : ∀ s, P.quad (w + s * d1) (u + s * d2) =
      P.quad w u + s * (G1 * d1 + G2 * d2) + s ^ 2 * P.quad d1 d2 := by
    intro s; unfold Params.quad; ring
  have hbexp : ∀ s, P.b6 (w + s * d1) (u + s * d2) =
      P.b6 w u + s * (H1 * d1 + H2 * d2) +
        s ^ 2 * (P.quad d1 d2 + kk P * (d1 - d2) * d2) := by
    intro s; rw [b6_eq, b6_eq]; unfold Params.quad; ring
  have e1 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < 1 - s * P.quad d1 d2 :=
    ev_pos (φ := fun s => 1 - s * P.quad d1 d2) (by fun_prop) (by norm_num)
  have e2 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < 1 + s * (P.quad d1 d2 + kk P * (d1 - d2) * d2) :=
    ev_pos (φ := fun s => 1 + s * (P.quad d1 d2 + kk P * (d1 - d2) * d2)) (by fun_prop)
      (by norm_num)
  have e3 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < (w + s * d1) - (u + s * d2) + aa P :=
    ev_pos (φ := fun s => (w + s * d1) - (u + s * d2) + aa P) (by fun_prop) (by simpa using hL)
  have e4 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < (u + s * d2) + x0 P :=
    ev_pos (φ := fun s => (u + s * d2) + x0 P) (by fun_prop) (by simp; linarith)
  have e5 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < x0 P - (u + s * d2) :=
    ev_pos (φ := fun s => x0 P - (u + s * d2)) (by fun_prop) (by simp; linarith)
  have e6 : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s := self_mem_nhdsWithin
  obtain ⟨s, hs1, hs2, hs3, hs4, hs5, hs6⟩ :=
    (e1.and (e2.and (e3.and (e4.and (e5.and e6))))).exists
  have hq' : P.quad (w + s * d1) (u + s * d2) < P.quad w u := by
    rw [hqexp, hGd]; nlinarith
  have hb' : 0 < P.b6 (w + s * d1) (u + s * d2) := by
    rw [hbexp, hHd, hb]; nlinarith
  have hy : P.TransformedFeasible (w + s * d1, u + s * d2) := by
    rw [feas_iff]; simp only
    refine ⟨by linarith, by linarith, by linarith, hb'.le, by linarith⟩
  have := hmin _ hy
  simp only at this
  linarith

lemma sol_signs (hP : P.Standing) (z : ℝ × ℝ) (hz : P.IsTransformedSolution z) :
    z.1 < 0 ∧ 0 < z.2 ∧ 0 < P.lam * z.1 + P.lamC * z.2 ∧ P.b6 z.1 z.2 = 0 := by
  have hb := sol_b6_zero P hP z hz
  have hE := sol_tangent P hP z hz
  obtain ⟨hL, hlo, hhi, h7, hqm⟩ := sol_slack P hP z hz
  have hw0 := region P hP z hz.1 hqm
  have hlc := lamC_pos P hP
  have hl := hP.2.2.2.1
  have hx := x0_pos P hP
  have hw : z.1 < 0 := by
    rcases lt_or_eq_of_le hw0 with h | h
    · exact h
    · exfalso
      rw [h] at hE
      have hu : z.2 = 0 := by
        have : P.lamC * z.2 * (x0 P - z.2) = 0 := by linarith
        rcases mul_eq_zero.1 this with h' | h'
        · rcases mul_eq_zero.1 h' with h'' | h''
          · linarith
          · exact h''
        · linarith
      have := quad_pos_of P hP z (hb ▸ le_refl _)
      rw [h, hu] at this; unfold Params.quad at this; simp at this
  have hM : 0 < x0 P - z.2 := by linarith
  have hML : 0 < (x0 P - z.2) + (z.1 - z.2 + aa P) := by linarith
  have h1 : 0 < P.lamC * z.2 * (x0 P - z.2) := by
    have : P.lam * z.1 * (z.1 - 2 * z.2 + aa P + x0 P) < 0 := by
      have : z.1 - 2 * z.2 + aa P + x0 P = (x0 P - z.2) + (z.1 - z.2 + aa P) := by ring
      rw [this]; have := mul_pos (mul_pos hl (neg_pos.2 hw)) hML
      nlinarith
    linarith
  have hu : 0 < z.2 := by
    by_contra hc; push Not at hc
    have : P.lamC * z.2 * (x0 P - z.2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hlc.le hc) hM.le
    linarith
  refine ⟨hw, hu, ?_, hb⟩
  have key : (P.lam * z.1 + P.lamC * z.2) * (x0 P - z.2) = -(P.lam * z.1) * (z.1 - z.2 + aa P) := by
    linear_combination hE
  have : 0 < (P.lam * z.1 + P.lamC * z.2) * (x0 P - z.2) := by
    rw [key]; exact mul_pos (by nlinarith) hL
  exact pos_of_mul_pos_left this hM.le

end BBRRSol


namespace BBRRSol
open BuybackSignal.ReturnsRisk BuybackSignal.ReturnsRisk.Params Filter Topology

variable (P : Params)

lemma feas4_of_TF (hP : P.Standing) (z : ℝ × ℝ) (hz : P.TransformedFeasible z) :
    P.Feasible4 (cOf P z) ∧
    P.Pi (cOf P z).1 (cOf P z).2 P.θbar P.θbar = P.pi0 - P.β / (2 * P.lam) * P.quad z.1 z.2 := by
  obtain ⟨hL, hlo, hhi, hb6, hb7⟩ := (feas_iff P z).1 hz
  have hβ := hP.2.2.1
  have hl := hP.2.2.2.1
  have hc : 0 < P.β / (2 * P.lam) := by positivity
  have hf := f_cOf P hP z hhi
  refine ⟨⟨(action_cOf P hP z).2 ⟨hlo, hL⟩, ?_, ?_⟩, hf⟩
  · rw [g_cOf P hP z hhi]; nlinarith
  · rw [D_eq P hP, hf]; nlinarith

lemma pi0_x0 (hP : P.Standing) :
    P.pi0 - P.β / (2 * P.lam) * P.quad 0 (x0 P) = P.alpha ^ 2 / (8 * P.β) := by
  have hβ := hP.2.2.1
  have hl := hP.2.2.2.1
  unfold Params.pi0 Params.quad x0
  field_simp; ring

lemma dagger_gt (hP : P.Standing) :
    P.alpha ^ 2 / (8 * P.β) < P.pi0 - P.β / (2 * P.lam) * P.quad 0 P.uDag := by
  rw [← pi0_x0 P hP]
  obtain ⟨hU, hUx, -, -, -⟩ := udag_props P hP
  have hβ := hP.2.2.1
  have hl := hP.2.2.2.1
  have hlc := lamC_pos P hP
  have hc : 0 < P.β / (2 * P.lam) := by positivity
  unfold Params.quad
  have : P.uDag ^ 2 < x0 P ^ 2 := by nlinarith
  nlinarith [mul_lt_mul_of_pos_left this hlc]

/-- any solution of (4) has transformed u-coordinate below x0 -/
lemma sol_u_lt (hP : P.Standing) (c : ℝ × ℝ) (hc : P.IsSolution4 c) : (tc P c).2 < x0 P := by
  obtain ⟨hfd, hfdv⟩ := feas4_of_TF P hP _ (udag_feas P hP)
  have h1 := hc.2 _ hfd
  rw [hfdv] at h1
  have h2 := dagger_gt P hP
  by_contra hcon; push Not at hcon
  have hβ := hP.2.2.1
  have hl := hP.2.2.2.1
  have hU : P.unsoldLow c.1 c.2 P.θbar P.lam = 0 := by
    unfold Params.unsoldLow
    rw [max_eq_right]; · simp
    unfold tc at hcon; simp only at hcon
    have : P.dAlpha = P.β / P.lam * (2 * x0 P) := by unfold x0; field_simp
    rw [this]
    have : 0 < P.β / P.lam := by positivity
    nlinarith
  have h3 := Pi_eq P c.1 c.2 P.θbar P.θbar
  rw [hU] at h3
  have h4 : c.1 * (P.alpha - P.β * c.1) / 2 ≤ P.alpha ^ 2 / (8 * P.β) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [sq_nonneg (2 * P.β * c.1 - P.alpha)]
  simp only [mul_zero, zero_mul, add_zero] at h3
  linarith

lemma sol_TS (hP : P.Standing) (c : ℝ × ℝ) (hc : P.IsSolution4 c) :
    P.IsTransformedSolution (tc P c) := by
  have hu := sol_u_lt P hP c hc
  have hcc := cOf_tc P hP c
  set z := tc P c
  have hβ := hP.2.2.1
  have hl := hP.2.2.2.1
  have hk : 0 < P.β / (2 * P.lam) := by positivity
  obtain ⟨⟨hA, hg, hD⟩, hmax⟩ := hc
  rw [← hcc] at hA hg hD hmax
  have hf := f_cOf P hP z hu.le
  refine ⟨?_, ?_⟩
  · rw [feas_iff]
    obtain ⟨h1, h2⟩ := (action_cOf P hP z).1 hA
    rw [g_cOf P hP z hu.le] at hg
    rw [D_eq P hP, hf] at hD
    refine ⟨h2, h1, hu.le, ?_, ?_⟩
    · nlinarith
    · nlinarith
  · intro y hy
    obtain ⟨hy4, hyv⟩ := feas4_of_TF P hP y hy
    have := hmax _ hy4
    rw [hyv, hf] at this
    nlinarith

lemma sR_eq (w r θh : ℝ) :
    P.sR w r θh P.lam = (P.alpha - P.β * w) / 2 + P.lamC * P.unsoldLow w r θh P.lam := by
  unfold Params.sR Params.unsoldLow Params.alpha Params.lamC; ring

lemma unsoldLow_anti (w r θh w' r' θh' : ℝ) (hl : 0 < P.lam) (hβ : 0 < P.β)
    (h : w - θh * r ≤ w' - θh' * r') :
    P.unsoldLow w' r' θh' P.lam ≤ P.unsoldLow w r θh P.lam := by
  unfold Params.unsoldLow
  have : P.β / P.lam * (w - θh * r) ≤ P.β / P.lam * (w' - θh' * r') :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have := max_le_max (show P.dAlpha - P.β / P.lam * (w' - θh' * r') ≤
    P.dAlpha - P.β / P.lam * (w - θh * r) by linarith) (le_refl (0:ℝ))
  linarith

/-- Lemma B.7: the less risky type's off-path bound -/
lemma B7 (hP : P.Standing) (cs : ℝ × ℝ) (hcs : P.IsSolution4 cs) (c : ℝ × ℝ)
    (hc : c ∈ P.actionSet P.θbar) :
    P.Pi c.1 c.2 P.θlow P.θbar ≤ P.Pi cs.1 cs.2 P.θbar P.θbar := by
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  have hP' : P.Standing := ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩
  have hθ : 0 < P.θbar := by linarith
  have hlc := lamC_pos P hP'
  obtain ⟨⟨hA, hg, hD⟩, hmax⟩ := hcs
  -- any contract in the action set satisfying the low IC is weakly worse than cs
  have key : ∀ c' : ℝ × ℝ, c' ∈ P.actionSet P.θbar →
      P.Pi c'.1 c'.2 P.θbar P.θlow ≤ P.pi0 →
      P.Pi c'.1 c'.2 P.θbar P.θbar ≤ P.Pi cs.1 cs.2 P.θbar P.θbar := by
    intro c' hc' hg'
    by_cases hD' : P.Pi P.w0 (P.r0 P.θlow) P.θlow P.θbar ≤ P.Pi c'.1 c'.2 P.θbar P.θbar
    · exact hmax c' ⟨hc', hg', hD'⟩
    · push Not at hD'; linarith
  obtain ⟨hr, hwr⟩ := hc
  set w := c.1
  set r := c.2
  set te := P.θlow * r / P.θbar
  have hte0 : 0 ≤ te := by positivity
  have hte : P.θbar * te = P.θlow * r := by simp only [te]; field_simp
  have hter : te ≤ r := by
    simp only [te]; rw [div_le_iff₀ hθ]; nlinarith
  have hUnn := unsoldLow_nonneg P w r P.θlow
  have hhc := Pi_diff P w r P.θlow P.θbar P.θlow
  -- h(c) = Π(c|θl,θl) - λc U_l Δθ r
  have hself := Pi_self_le_pi0 P hP' w r P.θlow
  by_cases hcase : P.Pi w te P.θbar P.θlow ≤ P.pi0
  · have hA' : (w, te) ∈ P.actionSet P.θbar := by
      refine ⟨hte0, ?_⟩; simp only; nlinarith
    have := key (w, te) hA' hcase
    simp only at this
    have hUeq : P.unsoldLow w te P.θbar P.lam = P.unsoldLow w r P.θlow P.lam := by
      unfold Params.unsoldLow; rw [hte]
    have e1 := Pi_eq P w te P.θbar P.θbar
    have e2 := Pi_eq P w r P.θlow P.θbar
    rw [hUeq, hte] at e1
    have : P.lamC * P.unsoldLow w r P.θlow P.lam * (w - P.θbar * r) ≤
        P.lamC * P.unsoldLow w r P.θlow P.lam * (w - P.θlow * r) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    linarith
  · push Not at hcase
    have hcont : ContinuousOn (fun t => P.Pi w t P.θbar P.θlow) (Set.Icc 0 te) :=
      ((continuous_Pi P P.θbar P.θlow).comp (Continuous.prodMk continuous_const continuous_id)).continuousOn
    have hg0 : P.Pi w 0 P.θbar P.θlow ≤ P.pi0 := by
      rw [Pi_diff P w 0 P.θbar P.θlow P.θbar]; simp only [mul_zero, add_zero]
      exact Pi_self_le_pi0 P hP' w 0 P.θbar
    obtain ⟨t, ⟨ht0, htte⟩, hgt⟩ := intermediate_value_Icc hte0 hcont ⟨hg0, hcase.le⟩
    simp only at hgt
    have hA' : (w, t) ∈ P.actionSet P.θbar := by
      refine ⟨ht0, ?_⟩; simp only; nlinarith
    have := key (w, t) hA' (by simp only; rw [hgt])
    simp only at this
    have hft := Pi_diff P w t P.θbar P.θbar P.θlow
    rw [hgt] at hft
    have hUle : P.unsoldLow w t P.θbar P.lam ≤ P.unsoldLow w r P.θlow P.lam :=
      unsoldLow_anti P w r P.θlow w t P.θbar hl hβ (by nlinarith)
    have hU0 := unsoldLow_nonneg P w t P.θbar
    have hdt : 0 ≤ P.θbar - P.θlow := by linarith
    have : P.unsoldLow w t P.θbar P.lam * t ≤ P.unsoldLow w r P.θlow P.lam * r :=
      mul_le_mul hUle (by linarith) ht0 hUnn
    have : P.lamC * (P.θbar - P.θlow) * (P.unsoldLow w t P.θbar P.lam * t) ≤
        P.lamC * (P.θbar - P.θlow) * (P.unsoldLow w r P.θlow P.lam * r) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    nlinarith

end BBRRSol


namespace BBRRSol
open BuybackSignal.ReturnsRisk BuybackSignal.ReturnsRisk.Params Filter Topology

variable (P : Params)

lemma exists_sol (hP : P.Standing) : ∃ c : ℝ × ℝ, P.IsSolution4 c := by
  have hβ := hP.2.2.1
  have hθ : 0 < P.θbar := by obtain ⟨_, _, _, _, _, h6, h7, _⟩ := hP; linarith
  obtain ⟨hfd, -⟩ := feas4_of_TF P hP _ (udag_feas P hP)
  set cd := cOf P (0, P.uDag)
  set fd := P.Pi cd.1 cd.2 P.θbar P.θbar
  set S : Set (ℝ × ℝ) := {c | P.Feasible4 c ∧ fd ≤ P.Pi c.1 c.2 P.θbar P.θbar}
  set T := P.pi0 - fd
  set R := 2 * T / P.β + 1
  have hT : 0 ≤ T := by have := Pi_self_le_pi0 P hP cd.1 cd.2 P.θbar; simp only [T]; linarith
  have hR : 0 ≤ R := by simp only [R]; positivity
  have hsub : S ⊆ Set.Icc (P.w0 - R) (P.w0 + R) ×ˢ Set.Icc 0 ((P.w0 + R) / P.θbar) := by
    rintro c ⟨⟨⟨hr, hwr⟩, -, -⟩, hf⟩
    have h1 := Pi_self_le P hP c.1 c.2 P.θbar
    have hsq : (c.1 - P.w0) ^ 2 ≤ 2 * T / P.β := by
      rw [le_div_iff₀ hβ]; simp only [T]; nlinarith
    have habs : |c.1 - P.w0| ≤ R := by
      simp only [R]
      by_contra hc; push Not at hc
      have h0 : 0 ≤ 2 * T / P.β := by positivity
      nlinarith [sq_abs (c.1 - P.w0), abs_nonneg (c.1 - P.w0)]
    rw [abs_le] at habs
    refine ⟨⟨by linarith, by linarith⟩, ⟨hr, ?_⟩⟩
    rw [le_div_iff₀ hθ]; nlinarith
  have hclosed : IsClosed S := by
    have hc1 := continuous_Pi P P.θbar P.θbar
    have hc2 := continuous_Pi P P.θbar P.θlow
    have : S = ({c : ℝ × ℝ | 0 ≤ c.2} ∩ {c | P.θbar * c.2 ≤ c.1}) ∩
        {c | P.Pi c.1 c.2 P.θbar P.θlow ≤ P.pi0} ∩
        {c | P.Pi P.w0 (P.r0 P.θlow) P.θlow P.θbar ≤ P.Pi c.1 c.2 P.θbar P.θbar} ∩
        {c | fd ≤ P.Pi c.1 c.2 P.θbar P.θbar} := by
      ext c; simp only [S, Params.Feasible4, Params.actionSet, Set.mem_setOf_eq, Set.mem_inter_iff]
      tauto
    rw [this]
    refine (((IsClosed.inter ?_ ?_).inter ?_).inter ?_).inter ?_
    · exact isClosed_le continuous_const continuous_snd
    · exact isClosed_le (continuous_const.mul continuous_snd) continuous_fst
    · exact isClosed_le hc2 continuous_const
    · exact isClosed_le continuous_const hc1
    · exact isClosed_le continuous_const hc1
  have hcomp : IsCompact S :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed hsub
  have hne : S.Nonempty := ⟨cd, hfd, le_refl _⟩
  obtain ⟨cs, hcsS, hmax⟩ :=
    hcomp.exists_isMaxOn hne (continuous_Pi P P.θbar P.θbar).continuousOn
  refine ⟨cs, hcsS.1, fun d hd => ?_⟩
  by_cases hdd : fd ≤ P.Pi d.1 d.2 P.θbar P.θbar
  · exact hmax ⟨hd, hdd⟩
  · push Not at hdd; linarith [hcsS.2]

theorem main (P : Params) (hP : P.Standing) :
    (∃ c : ℝ × ℝ, P.IsSolution4 c) ∧
    ∀ c : ℝ × ℝ, P.IsSolution4 c →
      P.IsSeparatingPBE c (P.w0, P.r0 P.θlow) (P.pessimistic c) ∧
      c.1 < P.w0 ∧ c.2 < P.r0 P.θbar ∧
      P.r0 P.θbar < P.r0 P.θlow ∧
      P.sR c.1 c.2 P.θbar P.lam < P.s0 ∧
      P.unsoldLow c.1 c.2 P.θbar P.lam < P.q0 ∧
      P.unsoldHigh (P.sR c.1 c.2 P.θbar P.lam) c.2 P.θbar = 0 := by
  refine ⟨exists_sol P hP, fun c hc => ?_⟩
  have hTS := sol_TS P hP c hc
  obtain ⟨hw, hu, hlin, -⟩ := sol_signs P hP _ hTS
  have hux := sol_u_lt P hP c hc
  have hcc := cOf_tc P hP c
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  have hP' : P.Standing := ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩
  have hθ : 0 < P.θbar := by linarith
  have hx0 := x0_pos P hP'
  set z := tc P c
  have hU : P.unsoldLow c.1 c.2 P.θbar P.lam = P.β / (2 * P.lam) * (x0 P - z.2) := by
    rw [← U_cOf P hP' z hux.le, hcc]
  have hc1 : c.1 = z.1 + P.w0 := by rw [← hcc]; rfl
  have hc2 : P.θbar * c.2 = z.1 - z.2 + aa P := by
    rw [← hcc]; unfold cOf; simp only; field_simp
  have hw0 : c.1 < P.w0 := by linarith
  have hsR : P.sR c.1 c.2 P.θbar P.lam = P.s0 - P.β / (2 * P.lam) * (P.lam * z.1 + P.lamC * z.2) := by
    rw [sR_eq, hU, hc1, w0_eq P hP']
    unfold Params.s0 x0 aa Params.alpha Params.lamC Params.dAlpha
    field_simp; ring
  have hk : 0 < P.β / (2 * P.lam) := by positivity
  refine ⟨?_, hw0, ?_, ?_, ?_, ?_, ?_⟩
  · -- separating PBE
    have hne : c ≠ (P.w0, P.r0 P.θlow) := by
      intro h; rw [h] at hw0; simp at hw0
    have hpc : P.pessimistic c c = P.θbar := by simp [Params.pessimistic]
    have hpl : P.pessimistic c (P.w0, P.r0 P.θlow) = P.θlow := by
      simp only [Params.pessimistic]; rw [if_neg (Ne.symm hne)]
    refine ⟨hne, ?_, hpc, hpl, hc.1.1, ?_, ?_, ?_⟩
    · intro c'; simp only [Params.pessimistic]; split_ifs <;> constructor <;> linarith
    · unfold Params.actionSet Params.r0 Params.w0
      simp only [Set.mem_setOf_eq]
      refine ⟨by positivity, ?_⟩
      have : P.θlow * (P.αl / (2 * P.β * P.θlow)) = P.αl / (2 * P.β) := by field_simp
      rw [this]
      apply div_le_div_of_nonneg_right _ (by positivity)
      unfold Params.alpha Params.lamC; nlinarith
    · intro c' hc' _
      by_cases h : c' = c
      · subst h; rw [hpc]
      · simp only [Params.pessimistic]; rw [if_neg h]
        exact B7 P hP' c hc c' hc'
    · intro c' hc' _
      rw [low_full P hP']
      by_cases h : c' = c
      · subst h; rw [hpc]; exact hc.1.2.1
      · simp only [Params.pessimistic]; rw [if_neg h]
        exact Pi_self_le_pi0 P hP' _ _ _
  · unfold Params.r0
    rw [lt_div_iff₀ (by positivity)]
    have : c.2 * (2 * P.β * P.θbar) = 2 * P.β * (P.θbar * c.2) := by ring
    rw [this, hc2]
    unfold aa
    have : 2 * P.β * (z.1 - z.2 + P.αl / (2 * P.β)) = 2 * P.β * (z.1 - z.2) + P.αl := by
      field_simp
    rw [this]; nlinarith
  · unfold Params.r0
    apply div_lt_div_of_pos_left h1 (by positivity)
    nlinarith
  · rw [hsR]; nlinarith
  · rw [hU]; unfold Params.q0
    have : P.β / (2 * P.lam) * x0 P = P.dAlpha / 4 := by unfold x0; field_simp; ring
    nlinarith
  · unfold Params.unsoldHigh
    rw [max_eq_right]
    rw [hsR]
    have e : P.β * P.θbar * c.2 = P.β * (z.1 - z.2 + aa P) := by rw [← hc2]; ring
    rw [e]
    obtain ⟨-, hlo, -⟩ := (feas_iff P z).1 hTS.1
    unfold Params.s0 aa Params.lamC
    have hx' : x0 P = P.lam * P.dAlpha / (2 * P.β) := rfl
    have : P.lam * P.dAlpha / (2 * P.β) + z.2 ≥ 0 := by rw [← hx']; linarith
    have key : P.αh / 4 - P.β / (2 * P.lam) * (P.lam * z.1 + (1 - P.lam) * z.2) -
        (P.αh - P.β * (z.1 - z.2 + P.αl / (2 * P.β))) / 2 =
        -(P.β / P.lam) / 2 * (P.lam * P.dAlpha / (2 * P.β) + z.2) := by
      unfold Params.dAlpha; field_simp; ring
    rw [key]
    have : 0 ≤ P.β / P.lam / 2 * (P.lam * P.dAlpha / (2 * P.β) + z.2) := by positivity
    linarith

end BBRRSol


namespace BBRRSol
open BuybackSignal.ReturnsRisk BuybackSignal.ReturnsRisk.Params

theorem ms_lemma_2 (P : Params) (hP : P.Standing)
    (θ : ℝ) (hθ : 0 < θ ∧ θ ≤ 1) :
    (P.w0, P.r0 θ) ∈ P.actionSet θ ∧
    P.Pi P.w0 (P.r0 θ) θ θ = P.pi0 ∧
    (∀ c : ℝ × ℝ, c ∈ P.actionSet θ →
      P.Pi c.1 c.2 θ θ ≤ P.Pi P.w0 (P.r0 θ) θ θ) ∧
    P.sR P.w0 (P.r0 θ) θ P.lam = P.s0 ∧
    P.unsoldLow P.w0 (P.r0 θ) θ P.lam = P.q0 ∧
    P.unsoldHigh P.s0 (P.r0 θ) θ = 0 := by
  have hP' := hP
  obtain ⟨h1, h2, hβ, hl, hl1, h3, h4, h5⟩ := hP
  obtain ⟨ht, ht1⟩ := hθ
  have hU : P.unsoldLow P.w0 (P.r0 θ) θ P.lam = P.dAlpha / 4 := by
    unfold Params.unsoldLow Params.w0 Params.r0 Params.alpha Params.lamC Params.dAlpha
    have : P.αh - P.αl - P.β / P.lam * ((P.lam * P.αh + (1 - P.lam) * P.αl) / (2 * P.β) -
        θ * (P.αl / (2 * P.β * θ))) = (P.αh - P.αl) / 2 := by
      field_simp; ring
    rw [this, max_eq_left (by linarith)]; ring
  have hpi : P.Pi P.w0 (P.r0 θ) θ θ = P.pi0 := by
    rw [Pi_eq, hU]
    unfold Params.w0 Params.r0 Params.pi0 Params.alpha Params.lamC Params.dAlpha
    field_simp
    ring
  refine ⟨?_, hpi, ?_, ?_, ?_, ?_⟩
  · unfold Params.actionSet Params.r0 Params.w0
    simp only [Set.mem_setOf_eq]
    refine ⟨by positivity, ?_⟩
    have : θ * (P.αl / (2 * P.β * θ)) = P.αl / (2 * P.β) := by field_simp
    rw [this]
    apply div_le_div_of_nonneg_right _ (by positivity)
    unfold Params.alpha Params.lamC; nlinarith
  · intro c _; rw [hpi]; exact Pi_self_le_pi0 P hP' _ _ _
  · rw [sR_eq, hU]
    unfold Params.s0 Params.w0 Params.alpha Params.lamC Params.dAlpha
    field_simp; ring
  · rw [hU]; rfl
  · unfold Params.unsoldHigh Params.s0 Params.r0
    rw [max_eq_right]
    have : P.αh / 4 - (P.αh - P.β * θ * (P.αl / (2 * P.β * θ))) / 2 = -(P.αh - P.αl) / 4 := by
      field_simp; ring
    rw [this]; linarith

theorem ms_lemma_B_7 (P : Params) (hP : P.Standing)
    (cstar : ℝ × ℝ) (hstar : P.IsSolution4 cstar) :
    ∀ c : ℝ × ℝ, c ∈ P.actionSet P.θbar →
      P.Pi c.1 c.2 P.θlow P.θbar ≤
        P.Pi cstar.1 cstar.2 P.θbar P.θbar :=
  fun c hc => B7 P hP cstar hstar c hc

theorem ms_lemma_B_4 (P : Params) (hP : P.Standing) (z : ℝ × ℝ)
    (hz : P.IsTransformedSolution z) :
    -P.alpha / (2 * P.β) < z.1 ∧
    -P.lam * P.dAlpha / (2 * P.β) < z.2 ∧
    z.2 < P.lam * P.dAlpha / (2 * P.β) := by
  obtain ⟨hL, hlo, hhi, -, -⟩ := sol_slack P hP z hz
  obtain ⟨-, hu, -, -⟩ := sol_signs P hP z hz
  have hx := x0_pos P hP
  have hw0 := w0_eq P hP
  refine ⟨?_, ?_, ?_⟩
  · have : -P.alpha / (2 * P.β) = -P.w0 := by unfold Params.w0; ring
    rw [this, hw0]; linarith
  · have : -P.lam * P.dAlpha / (2 * P.β) = -x0 P := by unfold x0; ring
    rw [this]; exact hlo
  · exact hhi

end BBRRSol

namespace BBRRSol
open BuybackSignal.ReturnsRisk BuybackSignal.ReturnsRisk.Params

theorem ms_lemma_B_6 (P : Params) (hP : P.Standing) (z : ℝ × ℝ)
    (hz : P.IsTransformedSolution z) :
    P.b6 z.1 z.2 = 0 ∧
    P.lamC * z.2 ^ 2 - P.lam * z.1 ^ 2 +
      2 * P.lam * z.1 * z.2 -
      (P.lamC * P.lam * P.dAlpha / (2 * P.β)) * z.2 -
      (P.lam * P.alpha / (2 * P.β)) * z.1 = 0 ∧
    z.1 < 0 ∧ 0 < z.2 ∧
    0 < P.lam * z.1 + P.lamC * z.2 ∧
    P.lam * z.1 + P.lamC * z.2 < P.lamC * P.uDag ∧
    z.1 - z.2 < -P.uDag := by
  obtain ⟨hw, hu, hlin, hb⟩ := sol_signs P hP z hz
  have hE := sol_tangent P hP z hz
  obtain ⟨hL, hlo, hhi, h7, hqm⟩ := sol_slack P hP z hz
  obtain ⟨hU, hUx, hUa, hb0, -⟩ := udag_props P hP
  have hlc := lamC_pos P hP
  have hl := hP.2.2.2.1
  have hk := kk_pos P hP
  have hβ := hP.2.2.1
  -- strict comparison with the point (0, uDag)
  have hqs : P.quad z.1 z.2 < P.quad 0 P.uDag := by
    rcases lt_or_eq_of_le hqm with h | h
    · exact h
    · exfalso
      have hTS : P.IsTransformedSolution (0, P.uDag) := by
        refine ⟨udag_feas P hP, fun y hy => ?_⟩
        have := hz.2 y hy
        simp only; linarith
      have := (sol_signs P hP _ hTS).1
      simp at this
  have hu2 : z.2 < P.uDag := by
    unfold Params.quad at hqs
    by_contra hc; push Not at hc
    have : P.uDag ^ 2 ≤ z.2 ^ 2 := by nlinarith
    nlinarith [mul_nonneg hl.le (sq_nonneg z.1), mul_le_mul_of_nonneg_left this hlc.le]
  refine ⟨hb, ?_, hw, hu, hlin, ?_, ?_⟩
  · have hw0 : P.alpha / (2 * P.β) = aa P + x0 P := by
      rw [← w0_eq P hP]; rfl
    have hx : P.lamC * P.lam * P.dAlpha / (2 * P.β) = P.lamC * x0 P := by
      unfold x0; ring
    have hw1 : P.lam * P.alpha / (2 * P.β) = P.lam * (aa P + x0 P) := by
      rw [← hw0]; ring
    rw [hx, hw1]
    linear_combination -hE
  · nlinarith
  · rw [b6_eq] at hb hb0
    unfold Params.quad at hb hb0 hqs
    have hM : x0 P - z.2 > 0 := by linarith
    have hM' : x0 P - P.uDag < x0 P - z.2 := by linarith
    have hA : 0 < aa P - P.uDag := by linarith
    have h1 : kk P * (z.1 - z.2 + aa P) * (x0 P - z.2) <
        kk P * (aa P - P.uDag) * (x0 P - z.2) := by
      nlinarith [mul_lt_mul_of_pos_left hM' (mul_pos hk hA)]
    have h2 : z.1 - z.2 + aa P < aa P - P.uDag := by
      by_contra hc; push Not at hc
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hk.le) hM.le]
    linarith

end BBRRSol


open BuybackSignal.ReturnsRisk

theorem solution (P : Params) (hP : P.Standing)
    (θ : ℝ) (hθ : 0 < θ ∧ θ ≤ 1) :
    (P.w0, P.r0 θ) ∈ P.actionSet θ ∧
    P.Pi P.w0 (P.r0 θ) θ θ = P.pi0 ∧
    (∀ c : ℝ × ℝ, c ∈ P.actionSet θ →
      P.Pi c.1 c.2 θ θ ≤ P.Pi P.w0 (P.r0 θ) θ θ) ∧
    P.sR P.w0 (P.r0 θ) θ P.lam = P.s0 ∧
    P.unsoldLow P.w0 (P.r0 θ) θ P.lam = P.q0 ∧
    P.unsoldHigh P.s0 (P.r0 θ) θ = 0 :=
  BBRRSol.ms_lemma_2 P hP θ hθ
