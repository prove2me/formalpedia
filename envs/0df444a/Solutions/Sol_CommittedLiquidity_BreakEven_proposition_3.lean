-- Prove2me | solution 1 for CommittedLiquidity.BreakEven.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T12:57:31.438326+00:00
-- url     : https://prove2.me/submissions/7b85ebb9-b7b2-4a43-83c5-1079e2441114

import Mathlib
import Definitions.Def_CommittedLiquidity_BreakEven_Model

set_option autoImplicit false

open CommittedLiquidity.BreakEven

namespace CLBEAux

open CommittedLiquidity.BreakEven.Params

/-- Basic consequences of the standing assumptions. -/
lemma basics (p : Params) (hp : p.Standing) :
    0 < p.D1 ∧ 0 < p.D2 ∧ 1 / 2 < p.q ∧ p.q * p.D1 < p.Plow ∧ p.Plow < p.q * p.D2 ∧
      p.D1 < p.D2 ∧ p.θG < p.D2 ∧ 0 < p.θB ∧ p.θB < p.θG ∧ 0 < p.α ∧ p.α < 1 ∧ p.q < 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ := hp
  have hk : 0 < (1 - p.E - p.F) * p.rD := mul_pos h1 (by linarith)
  have hG := h8 .G
  have hB := h8 .B
  simp only [lower] at hG hB
  have hD1 : p.D1 = p.q * ((1 - p.E - p.F) * p.rD) := by unfold D1; ring
  have hD2 : p.D2 = (1 - p.E - p.F) * p.rD + p.F := rfl
  have hD2pos : 0 < p.D2 := by linarith
  have hq : 1 / 2 < p.q := by
    have : 0 < p.θG / (2 * p.D2) := div_pos (by linarith) (by linarith)
    linarith
  have hD1pos : 0 < p.D1 := by rw [hD1]; exact mul_pos (by linarith) hk
  have hmul : p.D2 + p.θG < 2 * p.q * p.D2 := by
    have e : p.θG / (2 * p.D2) * (2 * p.D2) = p.θG := by field_simp
    have := mul_lt_mul_of_pos_right h10 (by linarith : (0:ℝ) < 2 * p.D2)
    nlinarith
  have hPlow : p.Plow = (p.θB + p.D2) / 2 := rfl
  refine ⟨hD1pos, hD2pos, hq, ?_, ?_, ?_, hG, h4, h5, h6, h7, h3⟩
  · rw [hPlow]
    set k := (1 - p.E - p.F) * p.rD
    rw [hD1] at h9 ⊢
    rw [hD2]
    nlinarith [mul_pos (mul_pos hk (by linarith : (0:ℝ) < 1 - p.q)) (by linarith : (0:ℝ) < 1 + 2 * p.q)]
  · rw [hPlow]; linarith
  · rw [hD2]; linarith

lemma θstar_anti (p : Params) (hp : p.Standing) {P P' : ℝ} (hP : p.q * p.D1 < P)
    (hPP : P < P') : p.θstar P' < p.θstar P := by
  obtain ⟨hD1, hD2, hq, -, -, hD12, -⟩ := basics p hp
  have hqD1 : 0 < p.q * p.D1 := mul_pos (by linarith) hD1
  have hPpos : 0 < P := by linarith
  unfold θstar
  have h1 : 0 < 1 - p.q * p.D1 / P := by
    have : p.q * p.D1 / P < 1 := (div_lt_one hPpos).2 hP
    linarith
  have h2 : p.q * p.D1 / P' < p.q * p.D1 / P := div_lt_div_of_pos_left hqD1 hPpos hPP
  exact div_lt_div_of_pos_left (by linarith) h1 (by linarith)

lemma θstar_at_top (p : Params) (hp : p.Standing) : p.θstar (p.q * p.D2) = p.D2 := by
  obtain ⟨hD1, hD2, hq, -, -, hD12, -⟩ := basics p hp
  unfold θstar
  have hq0 : p.q ≠ 0 := by linarith
  have hD2' : p.D2 ≠ 0 := ne_of_gt hD2
  have : 1 - p.q * p.D1 / (p.q * p.D2) = (p.D2 - p.D1) / p.D2 := by
    field_simp
  rw [this]
  have : p.D2 - p.D1 ≠ 0 := by linarith
  field_simp

lemma θstar_ge (p : Params) (hp : p.Standing) {P : ℝ} (hP : P ∈ Set.Icc p.Plow (p.q * p.D2)) :
    p.D2 ≤ p.θstar P := by
  obtain ⟨-, -, -, hl, -⟩ := basics p hp
  rcases eq_or_lt_of_le hP.2 with h | h
  · rw [h, θstar_at_top p hp]
  · rw [← θstar_at_top p hp]
    exact le_of_lt (θstar_anti p hp (by linarith [hP.1]) h)

lemma θstar_lt_bar (p : Params) (hp : p.Standing) {P : ℝ} (hP : p.Plow ≤ P) :
    p.θstar P < p.θbar := by
  obtain ⟨hD1, hD2, hq, hl, hu, hD12, -, hB, -, -, -, hq1⟩ := basics p hp
  have hbar := hp.2.2.2.2.2.2.2.2.2.2
  have hPlpos : 0 < p.Plow := by nlinarith
  have hle : p.θstar P ≤ p.θstar p.Plow := by
    rcases eq_or_lt_of_le hP with h | h
    · rw [h]
    · exact le_of_lt (θstar_anti p hp hl h)
  refine lt_of_le_of_lt hle (lt_trans ?_ hbar)
  unfold θstar
  have hk : p.D1 = p.q * ((1 - p.E - p.F) * p.rD) := by unfold D1; ring
  have hD2e : p.D2 = (1 - p.E - p.F) * p.rD + p.F := rfl
  set k := (1 - p.E - p.F) * p.rD with hkdef
  set a := p.Plow with ha
  have hkpos0 : 0 < k := by
    have := hp.1; have := hp.2.1; rw [hkdef]; exact mul_pos (by assumption) (by linarith)
  have hDa : p.D1 < a := by
    have hF := hp.2.2.2.2.2.2.2.2.1
    rw [ha]; show p.D1 < (p.θB + p.D2) / 2
    rw [hD2e]; rw [hk] at hF ⊢
    nlinarith [mul_pos hkpos0 (by linarith : (0:ℝ) < 1 - p.q)]
  set x := p.D1 / a with hx
  have hxa : x * a = p.D1 := by rw [hx]; field_simp
  have hx1 : x < 1 := (div_lt_one hPlpos).2 hDa
  have hx0 : 0 < x := div_pos hD1 hPlpos
  have hqx : p.q * p.D1 / a = p.q * x := by rw [hx]; ring
  rw [hqx]
  have e1 : 0 < 1 - p.q * x := by nlinarith
  have e2 : 0 < 1 - x := by linarith
  rw [div_lt_div_iff₀ e1 e2]
  -- k < x * D2
  have hkpos : 0 < k := by
    have := hp.1; have := hp.2.1; rw [hkdef]; exact mul_pos (by assumption) (by linarith)
  have hkx : k < x * p.D2 := by
    have h' : a * (x * p.D2 - k) = k * (p.q * p.D2 - a) := by
      rw [show a * (x * p.D2 - k) = (x * a) * p.D2 - a * k by ring, hxa, hk]; ring
    have : 0 < a * (x * p.D2 - k) := by rw [h']; exact mul_pos hkpos (by linarith)
    have := (pos_iff_pos_of_mul_pos this).1 hPlpos
    linarith
  rw [hk, hD2e] at *
  nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - p.q) (by linarith : (0:ℝ) < x * ((1 - p.E - p.F) * p.rD + p.F) - k)]

/-- Closed form of the regulator payoff. -/
lemma VA_eq (p : Params) (P : ℝ) :
    p.VA P = 2 * p.D1 * P⁻¹ *
      (p.α * ((p.θstar P - p.θG) / (p.θbar - p.θG)) * ((p.θG + p.θstar P) / 2 - P) +
       (1 - p.α) * ((p.θstar P - p.θB) / (p.θbar - p.θB)) * ((p.θB + p.θstar P) / 2 - P)) := by
  unfold VA
  rw [show (Finset.univ : Finset State) = {State.G, State.B} from rfl,
    Finset.sum_pair (by decide), show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} from by decide,
    Finset.sum_pair (by decide), Finset.sum_pair (by decide)]
  simp only [prior, lower, probBelow, πs]
  norm_num
  ring

/-- The per-state term is strictly decreasing along the price path. -/
lemma g_strict (l P P' t t' : ℝ) (hl : 0 < l) (hP : 0 < P) (hPP : P < P') (hP't : P' < t')
    (htt : t' < t) (hlt : l < t') :
    (t' - l) * ((l + t') / 2 - P') * P'⁻¹ < (t - l) * ((l + t) / 2 - P) * P⁻¹ := by
  have hP' : 0 < P' := by linarith
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_lt_div_iff₀ hP' hP]
  nlinarith [mul_pos (mul_pos hP' (by linarith : (0:ℝ) < t - t')) (by linarith : (0:ℝ) < t + t' - 2 * P),
    mul_pos (by linarith : (0:ℝ) < P' - P) (mul_pos (by linarith : (0:ℝ) < t' - l) (by linarith : (0:ℝ) < t' + l))]

lemma VA_anti (p : Params) (hp : p.Standing) :
    StrictAntiOn p.VA (Set.Icc p.Plow (p.q * p.D2)) := by
  obtain ⟨hD1, hD2, hq, hl, hu, hD12, hGD, hB, hBG, ha0, ha1, hq1⟩ := basics p hp
  intro P hP P' hP' hPP
  have hPpos : 0 < P := by nlinarith [hP.1]
  have t1 := θstar_ge p hp hP'
  have t2 := θstar_anti p hp (by linarith [hP.1]) hPP
  have b1 := θstar_lt_bar p hp hP.1
  have hP't : P' < p.θstar P' := by nlinarith [hP'.2]
  rw [VA_eq, VA_eq]
  have cG : 0 < 2 * p.D1 * p.α / (p.θbar - p.θG) := by
    have : 0 < p.θbar - p.θG := by linarith
    positivity
  have cB : 0 < 2 * p.D1 * (1 - p.α) / (p.θbar - p.θB) := by
    have : 0 < p.θbar - p.θB := by linarith
    have : 0 < 1 - p.α := by linarith
    positivity
  have gG := g_strict p.θG P P' (p.θstar P) (p.θstar P') (by linarith) hPpos hPP hP't t2 (by linarith)
  have gB := g_strict p.θB P P' (p.θstar P) (p.θstar P') hB hPpos hPP hP't t2 (by linarith)
  have e : ∀ Q : ℝ, 2 * p.D1 * Q⁻¹ *
      (p.α * ((p.θstar Q - p.θG) / (p.θbar - p.θG)) * ((p.θG + p.θstar Q) / 2 - Q) +
       (1 - p.α) * ((p.θstar Q - p.θB) / (p.θbar - p.θB)) * ((p.θB + p.θstar Q) / 2 - Q)) =
      2 * p.D1 * p.α / (p.θbar - p.θG) * ((p.θstar Q - p.θG) * ((p.θG + p.θstar Q) / 2 - Q) * Q⁻¹) +
      2 * p.D1 * (1 - p.α) / (p.θbar - p.θB) *
        ((p.θstar Q - p.θB) * ((p.θB + p.θstar Q) / 2 - Q) * Q⁻¹) := by
    intro Q; ring
  rw [e, e]
  exact add_lt_add (mul_lt_mul_of_pos_left gG cG) (mul_lt_mul_of_pos_left gB cB)

lemma SYS_anti (p : Params) (hp : p.Standing) :
    StrictAntiOn p.SYS (Set.Icc p.Plow (p.q * p.D2)) := by
  obtain ⟨hD1, hD2, hq, hl, hu, hD12, hGD, hB, hBG, ha0, ha1, hq1⟩ := basics p hp
  intro P hP P' hP' hPP
  have t1 := θstar_ge p hp hP'
  have t2 := θstar_anti p hp (by linarith [hP.1]) hPP
  have b1 := θstar_lt_bar p hp hP.1
  unfold SYS sysOfTheta
  have V : 0 < p.θbar - p.θG := by linarith
  have U : 0 < p.θbar - p.θB := by linarith
  have h1 : (p.θstar P' - p.θG) / (p.θbar - p.θG) < (p.θstar P - p.θG) / (p.θbar - p.θG) :=
    div_lt_div_of_pos_right (by linarith) V
  have h2 : (p.θstar P' - p.θB) / (p.θbar - p.θB) < (p.θstar P - p.θB) / (p.θbar - p.θB) :=
    div_lt_div_of_pos_right (by linarith) U
  have h1' : 0 ≤ (p.θstar P' - p.θG) / (p.θbar - p.θG) := div_nonneg (by linarith) V.le
  have h2' : 0 ≤ (p.θstar P' - p.θB) / (p.θbar - p.θB) := div_nonneg (by linarith) U.le
  have s1 := pow_lt_pow_left₀ h1 h1' (two_ne_zero)
  have s2 := pow_lt_pow_left₀ h2 h2' (two_ne_zero)
  exact add_lt_add (mul_lt_mul_of_pos_left s1 ha0) (mul_lt_mul_of_pos_left s2 (by linarith))

/-- A zero of the buyers' profit gives a linear relation. -/
lemma Pi_zero (p : Params) (M : ℕ) (P : ℝ) (h : p.Pi M P = 0)
    (hden : 0 < (p.θstar P - p.θB) ^ M + p.κ * (p.θstar P - p.θG) ^ M) :
    (p.θstar P - p.θB) ^ M * ((p.θB + p.θstar P) / 2 - P) +
      p.κ * (p.θstar P - p.θG) ^ M * ((p.θG + p.θstar P) / 2 - P) = 0 := by
  unfold Pi ωB ωG πs lower at h
  have e : (p.θstar P - p.θB) ^ M / ((p.θstar P - p.θB) ^ M + p.κ * (p.θstar P - p.θG) ^ M) *
        ((p.θB + p.θstar P) / 2 - P) +
      p.κ * (p.θstar P - p.θG) ^ M / ((p.θstar P - p.θB) ^ M + p.κ * (p.θstar P - p.θG) ^ M) *
        ((p.θG + p.θstar P) / 2 - P) =
      ((p.θstar P - p.θB) ^ M * ((p.θB + p.θstar P) / 2 - P) +
        p.κ * (p.θstar P - p.θG) ^ M * ((p.θG + p.θstar P) / 2 - P)) /
      ((p.θstar P - p.θB) ^ M + p.κ * (p.θstar P - p.θG) ^ M) := by ring
  rw [e, div_eq_zero_iff] at h
  rcases h with h | h
  · exact h
  · exact absurd h (ne_of_gt hden)

lemma sign1 (α u v U V πB πG : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hu : 0 < u) (hv : 0 < v)
    (hV : 0 < V) (hUV : V < U) (hd : πB < πG)
    (h : u * πB + α / (1 - α) * (U / V) ^ 2 * v * πG = 0) :
    α * (v / V) * πG + (1 - α) * (u / U) * πB < 0 := by
  have hU : 0 < U := by linarith
  have h1α : 0 < 1 - α := by linarith
  set K := α / (1 - α) * (U / V) ^ 2 with hK
  have hKpos : 0 < K := by positivity
  have hG : 0 < πG := by
    by_contra hc
    push Not at hc
    have : u * πB < 0 := mul_neg_of_pos_of_neg hu (by linarith)
    have : K * v * πG ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  have hB : πB = -(K * v * πG) / u := by field_simp; linarith
  rw [hB]
  have e : α * (v / V) * πG + (1 - α) * (u / U) * (-(K * v * πG) / u) =
      α * v * πG * (V - U) / V ^ 2 := by
    rw [hK]; field_simp; ring
  rw [e]
  apply div_neg_of_neg_of_pos _ (by positivity)
  exact mul_neg_of_pos_of_neg (by positivity) (by linarith)

lemma sign2 (α u v U V πB πG : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hu : 0 < u) (hv : 0 < v)
    (hV : 0 < V) (hU : 0 < U) (hUV : U * v < V * u) (hd : πB < πG)
    (h : u ^ 2 * πB + α / (1 - α) * (U / V) ^ 2 * v ^ 2 * πG = 0) :
    0 < α * (v / V) * πG + (1 - α) * (u / U) * πB := by
  have h1α : 0 < 1 - α := by linarith
  set K := α / (1 - α) * (U / V) ^ 2 with hK
  have hKpos : 0 < K := by positivity
  have hG : 0 < πG := by
    by_contra hc
    push Not at hc
    have : u ^ 2 * πB < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
    have : K * v ^ 2 * πG ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  have hB : πB = -(K * v ^ 2 * πG) / u ^ 2 := by field_simp; linarith
  rw [hB]
  have e : α * (v / V) * πG + (1 - α) * (u / U) * (-(K * v ^ 2 * πG) / u ^ 2) =
      α * v * πG * (V * u - U * v) / (V ^ 2 * u) := by
    rw [hK]; field_simp; ring
  rw [e]
  apply div_pos _ (by positivity)
  exact mul_pos (by positivity) (by linarith)

end CLBEAux

open CLBEAux in
open CommittedLiquidity.BreakEven in
theorem solution (p : Params) (hp : p.Standing) (P1 P2 : ℝ)
    (hP1 : p.IsBreakEven 1 P1) (hP2 : p.IsBreakEven 2 P2) :
    StrictAntiOn p.SYS (Set.Ico p.Plow (p.q * p.D2)) ∧
    StrictAntiOn p.VA (Set.Ico p.Plow (p.q * p.D2)) ∧
    ∃ PA, (PA ∈ Set.Ioo P2 P1 ∧ p.VA PA = 0) ∧
      (∀ P, P ∈ Set.Ioo P2 P1 → p.VA P = 0 → P = PA) ∧
      PA ∈ {P | P2 ≤ P ∧ 0 ≤ p.VA P ∧ p.D2 ≤ p.θstar P} ∧
      IsMinOn p.SYS {P | P2 ≤ P ∧ 0 ≤ p.VA P ∧ p.D2 ≤ p.θstar P} PA ∧
      p.sysOfTheta (p.θstar PA) < p.sysOfTheta (p.θstar P2) := by
  obtain ⟨hD1, hD2, hq, hl, hu, hD12, hGD, hB, hBG, ha0, ha1, hq1⟩ := basics p hp
  have hVA := VA_anti p hp
  have hSYS := SYS_anti p hp
  have hI1 : P1 ∈ Set.Icc p.Plow (p.q * p.D2) := ⟨hP1.1, hP1.2.1.le⟩
  have hI2 : P2 ∈ Set.Icc p.Plow (p.q * p.D2) := ⟨hP2.1, hP2.2.1.le⟩
  have hPlpos : 0 < p.Plow := by nlinarith
  -- sign of VA at a break-even price
  have common : ∀ P ∈ Set.Icc p.Plow (p.q * p.D2),
      0 < p.θstar P - p.θB ∧ 0 < p.θstar P - p.θG ∧ 0 < p.θbar - p.θG ∧
      p.θbar - p.θG < p.θbar - p.θB ∧ 0 < P ∧ p.θstar P < p.θbar := by
    intro P hP
    have := θstar_ge p hp hP
    have := θstar_lt_bar p hp hP.1
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith [hP.1], this⟩
  have hκ : p.κ = p.α / (1 - p.α) * ((p.θbar - p.θB) / (p.θbar - p.θG)) ^ 2 := rfl
  have hκpos : 0 < p.κ := by
    obtain ⟨-, -, V, UV, -, -⟩ := common P1 hI1
    rw [hκ]
    exact mul_pos (div_pos ha0 (by linarith)) (pow_pos (div_pos (by linarith) V) 2)
  have hVA1 : p.VA P1 < 0 := by
    obtain ⟨u, v, V, UV, hP, hbar⟩ := common P1 hI1
    have hz := Pi_zero p 1 P1 hP1.2.2 (by
      rw [pow_one, pow_one]
      nlinarith [mul_pos hκpos v])
    simp only [pow_one] at hz
    rw [hκ] at hz
    have s := sign1 p.α _ _ _ _ _ _ ha0 ha1 u v V UV
      (by linarith : (p.θB + p.θstar P1) / 2 - P1 < (p.θG + p.θstar P1) / 2 - P1)
      (by linear_combination hz)
    rw [VA_eq]
    have : 0 < 2 * p.D1 * P1⁻¹ := by positivity
    nlinarith [mul_neg_of_pos_of_neg this s]
  have hVA2 : 0 < p.VA P2 := by
    obtain ⟨u, v, V, UV, hP, hbar⟩ := common P2 hI2
    have hz := Pi_zero p 2 P2 hP2.2.2 (by
      have := mul_pos hκpos (pow_pos v 2)
      have := pow_pos u 2
      linarith)
    rw [hκ] at hz
    have hUv : (p.θbar - p.θB) * (p.θstar P2 - p.θG) < (p.θbar - p.θG) * (p.θstar P2 - p.θB) := by
      nlinarith [mul_pos (by linarith : (0:ℝ) < p.θbar - p.θstar P2) (by linarith : (0:ℝ) < p.θG - p.θB)]
    have s := sign2 p.α _ _ _ _ _ _ ha0 ha1 u v V (by linarith) hUv
      (by linarith : (p.θB + p.θstar P2) / 2 - P2 < (p.θG + p.θstar P2) / 2 - P2)
      (by linear_combination hz)
    rw [VA_eq]
    have : 0 < 2 * p.D1 * P2⁻¹ := by positivity
    nlinarith [mul_pos this s]
  have h21 : P2 < P1 := (hVA.lt_iff_gt hI1 hI2).1 (by linarith)
  have hsub : Set.Icc P2 P1 ⊆ Set.Icc p.Plow (p.q * p.D2) :=
    Set.Icc_subset_Icc hI2.1 hI1.2
  -- continuity
  have hcont : ContinuousOn p.VA (Set.Icc P2 P1) := by
    have hpos : ∀ x ∈ Set.Icc P2 P1, 0 < x := fun x hx => by linarith [(hsub hx).1]
    have hden : ∀ x ∈ Set.Icc P2 P1, 1 - p.q * p.D1 / x ≠ 0 := by
      intro x hx
      have hx0 := hpos x hx
      have : p.q * p.D1 / x < 1 := (div_lt_one hx0).2 (by linarith [(hsub hx).1])
      linarith
    have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc P2 P1) :=
      continuousOn_inv₀.mono (fun x hx => ne_of_gt (hpos x hx))
    have hθ : ContinuousOn p.θstar (Set.Icc P2 P1) := by
      unfold Params.θstar
      apply ContinuousOn.div continuousOn_const _ hden
      apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.div continuousOn_const continuousOn_id
      intro x hx; exact ne_of_gt (hpos x hx)
    have e : p.VA = fun P => 2 * p.D1 * P⁻¹ *
      (p.α * ((p.θstar P - p.θG) / (p.θbar - p.θG)) * ((p.θG + p.θstar P) / 2 - P) +
       (1 - p.α) * ((p.θstar P - p.θB) / (p.θbar - p.θB)) * ((p.θB + p.θstar P) / 2 - P)) := by
      funext P; exact VA_eq p P
    rw [e]
    fun_prop
  obtain ⟨PA, hPA, hPA0⟩ : ∃ PA ∈ Set.Icc P2 P1, p.VA PA = 0 :=
    intermediate_value_Icc' h21.le hcont ⟨hVA1.le, hVA2.le⟩
  have hPA2 : PA ≠ P2 := by rintro rfl; linarith
  have hPA1 : PA ≠ P1 := by rintro rfl; linarith
  have hPAo : PA ∈ Set.Ioo P2 P1 :=
    ⟨lt_of_le_of_ne hPA.1 (Ne.symm hPA2), lt_of_le_of_ne hPA.2 hPA1⟩
  have hPAI := hsub hPA
  refine ⟨hSYS.mono Set.Ico_subset_Icc_self, hVA.mono Set.Ico_subset_Icc_self, PA,
    ⟨hPAo, hPA0⟩, ?_, ⟨hPA.1, hPA0.ge, θstar_ge p hp hPAI⟩, ?_, ?_⟩
  · intro P hP hP0
    exact hVA.injOn (hsub (Set.Ioo_subset_Icc_self hP)) hPAI (hP0.trans hPA0.symm)
  · rw [isMinOn_iff]
    intro P hP
    obtain ⟨h1, h2, h3⟩ := hP
    have hPl : p.Plow ≤ P := le_trans hI2.1 h1
    have hPu : P ≤ p.q * p.D2 := by
      by_contra hc
      push Not at hc
      have := θstar_anti p hp (by linarith) hc
      rw [θstar_at_top p hp] at this
      linarith
    have hPI : P ∈ Set.Icc p.Plow (p.q * p.D2) := ⟨hPl, hPu⟩
    have : P ≤ PA := (hVA.le_iff_ge hPAI hPI).1 (by rw [hPA0]; exact h2)
    exact (hSYS.le_iff_ge hPAI hPI).2 this
  · exact hSYS hI2 hPAI hPAo.1
