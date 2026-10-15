-- Prove2me | solution 1 for CommonOwnership.Governance.proposition3_monotone
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-14T19:59:48.593571+00:00
-- url     : https://prove2.me/submissions/bf13c58f-1f25-40ec-9b98-23ae8b506643

import Definitions.Def_CommonOwnership_Governance_Model
namespace CommonOwnership.Governance

lemma co_mstar (β ξ γ : ℝ) (hξ : 0 < ξ) (hγ : ξ < γ) (hβ1 : β ≤ 1)
    (m : ℝ → ℝ) (hm : IsOptMonitoring (quadCost γ) ξ β m) :
    ∀ t ∈ Set.Icc (0:ℝ) β, m t = ξ * t / γ := by
  intro t ht
  obtain ⟨⟨hm0, hm1⟩, hopt⟩ := hm t ht
  have hγ0 : 0 < γ := lt_trans hξ hγ
  have hk0 : 0 ≤ ξ * t / γ := div_nonneg (mul_nonneg hξ.le ht.1) hγ0.le
  have hk1 : ξ * t / γ ≤ 1 := by
    rw [div_le_one hγ0]
    nlinarith [ht.1, ht.2]
  have h := hopt (ξ * t / γ) ⟨hk0, hk1⟩
  unfold monitorObj quadCost at h
  set k := ξ * t / γ with hk
  have hkt : ξ * t = γ * k := by rw [hk]; field_simp
  have h2 : γ * (m t - k) ^ 2 ≤ 0 := by nlinarith
  have h3 : (m t - k) ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos hγ0 hc]
  have h4 : (m t - k) ^ 2 = 0 := le_antisymm h3 (sq_nonneg _)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
  linarith

lemma co_nu (β ξ γ : ℝ) (hξ : 0 < ξ) (hγ : ξ < γ) (hβ1 : β ≤ 1)
    (m : ℝ → ℝ) (hm : IsOptMonitoring (quadCost γ) ξ β m) :
    ∀ s ∈ Set.Icc (0:ℝ) β, nuStar (quadCost γ) m β ξ s =
      ξ ^ 2 / (2 * γ) * (2 * γ * β * (1 - ξ) / ξ ^ 2 + β ^ 2 - s ^ 2) := by
  intro s hs
  have hγ0 : 0 < γ := lt_trans hξ hγ
  have ht : β - s ∈ Set.Icc (0:ℝ) β := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  unfold nuStar quadCost
  rw [co_mstar β ξ γ hξ hγ hβ1 m hm (β - s) ht]
  field_simp
  ring

lemma co_core (β : ℝ) (Q : ℝ → ℝ) (hQ : ∀ s ∈ Set.Icc (0:ℝ) β, 0 < Q s)
    (ν1 ν2 : ℝ → ℝ) (c1 c2 a1 a2 : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2) (ha : a1 < a2)
    (ha1 : 0 < a1)
    (hν1 : ∀ s ∈ Set.Icc (0:ℝ) β, ν1 s = c1 * (a1 + β ^ 2 - s ^ 2))
    (hν2 : ∀ s ∈ Set.Icc (0:ℝ) β, ν2 s = c2 * (a2 + β ^ 2 - s ^ 2))
    (s1 s2 : ℝ) (h1 : IsEqOwnership (fun s => ν1 s * Q s) β s1)
    (h2 : IsEqOwnership (fun s => ν2 s * Q s) β s2) : s1 ≤ s2 := by
  by_contra hc
  push Not at hc
  obtain ⟨hs1, o1⟩ := h1
  obtain ⟨hs2, o2⟩ := h2
  have e1 := o1 s2 hs2
  have e2 := o2 s1 hs1
  simp only at e1 e2
  rw [hν1 s1 hs1, hν1 s2 hs2] at e1
  rw [hν2 s1 hs1, hν2 s2 hs2] at e2
  have q1 := hQ s1 hs1
  have q2 := hQ s2 hs2
  have pos : ∀ s ∈ Set.Icc (0:ℝ) β, ∀ a, 0 < a → 0 < a + β ^ 2 - s ^ 2 := by
    intro s hs a ha
    nlinarith [hs.1, hs.2]
  have f12 := pos s2 hs2 a1 ha1
  have f11 := pos s1 hs1 a1 ha1
  have f21 := pos s1 hs1 a2 (by linarith)
  have f22 := pos s2 hs2 a2 (by linarith)
  set F12 := a1 + β ^ 2 - s2 ^ 2
  set F11 := a1 + β ^ 2 - s1 ^ 2
  set F21 := a2 + β ^ 2 - s1 ^ 2
  set F22 := a2 + β ^ 2 - s2 ^ 2
  have g1 : F12 * Q s2 ≤ F11 * Q s1 := by
    have : c1 * (F12 * Q s2) ≤ c1 * (F11 * Q s1) := by linarith [e1, mul_assoc c1 F12 (Q s2), mul_assoc c1 F11 (Q s1)]
    exact le_of_mul_le_mul_left this hc1
  have g2 : F21 * Q s1 ≤ F22 * Q s2 := by
    have : c2 * (F21 * Q s1) ≤ c2 * (F22 * Q s2) := by linarith [e2, mul_assoc c2 F21 (Q s1), mul_assoc c2 F22 (Q s2)]
    exact le_of_mul_le_mul_left this hc2
  have k1 := mul_le_mul_of_nonneg_left g1 f21.le
  have k2 := mul_le_mul_of_nonneg_left g2 f11.le
  have k3 : (F21 * F12) * Q s2 ≤ (F11 * F22) * Q s2 := by nlinarith
  have k4 : F21 * F12 ≤ F11 * F22 := le_of_mul_le_mul_right k3 q2
  have hsq : s2 ^ 2 < s1 ^ 2 := by nlinarith [hs2.1]
  have : F11 * F22 - F21 * F12 = (a1 - a2) * (s1 ^ 2 - s2 ^ 2) := by
    simp only [F11, F22, F21, F12]; ring
  nlinarith

lemma co_Q (θ β : ℝ) (hθ : 0 < θ) (hβ : 0 < β) (P : ℝ → ℝ)
    (hP : ∀ l ∈ Set.Icc (0:ℝ) 1, 0 < P l) :
    ∀ s ∈ Set.Icc (0:ℝ) β, 0 < P (lam θ β s) := by
  intro s hs
  apply hP
  unfold lam
  have hD : 0 < (β - s) ^ 2 + θ * s ^ 2 := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · subst h; nlinarith
    · nlinarith [sq_nonneg (β - s), mul_pos hθ (mul_pos h h)]
  refine ⟨div_nonneg (by positivity) hD.le, ?_⟩
  rw [div_le_one hD]
  nlinarith [sq_nonneg (β - s)]

theorem proposition3_monotone (θ β : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (P : ℝ → ℝ) (hP : ∀ l ∈ Set.Icc (0:ℝ) 1, 0 < P l) :
    (∀ (ξ₁ ξ₂ γ : ℝ) (m₁ m₂ : ℝ → ℝ) (s₁ s₂ : ℝ),
      0 < ξ₁ → ξ₁ < ξ₂ → ξ₂ < 1 → ξ₂ < γ →
      IsOptMonitoring (quadCost γ) ξ₁ β m₁ → IsOptMonitoring (quadCost γ) ξ₂ β m₂ →
      IsEqOwnership (jointSurplus (quadCost γ) m₁ P θ β ξ₁) β s₁ →
      IsEqOwnership (jointSurplus (quadCost γ) m₂ P θ β ξ₂) β s₂ → s₂ ≤ s₁) ∧
    (∀ (ξ γ₁ γ₂ : ℝ) (m₁ m₂ : ℝ → ℝ) (s₁ s₂ : ℝ),
      0 < ξ → ξ < 1 → ξ < γ₁ → γ₁ < γ₂ →
      IsOptMonitoring (quadCost γ₁) ξ β m₁ → IsOptMonitoring (quadCost γ₂) ξ β m₂ →
      IsEqOwnership (jointSurplus (quadCost γ₁) m₁ P θ β ξ) β s₁ →
      IsEqOwnership (jointSurplus (quadCost γ₂) m₂ P θ β ξ) β s₂ → s₁ ≤ s₂) := by
  have hQ := co_Q θ β hθ hβ P hP
  constructor
  · intro ξ₁ ξ₂ γ m₁ m₂ s₁ s₂ h0 h12 h21 h2γ hm1 hm2 he1 he2
    have hξ2 : 0 < ξ₂ := by linarith
    have hγ0 : 0 < γ := by linarith
    have ha : 2 * γ * β * (1 - ξ₂) / ξ₂ ^ 2 < 2 * γ * β * (1 - ξ₁) / ξ₁ ^ 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have hgb : 0 < 2 * γ * β := by positivity
      have hsq : ξ₁ ^ 2 < ξ₂ ^ 2 := by nlinarith
      have : (1 - ξ₂) * ξ₁ ^ 2 < (1 - ξ₁) * ξ₂ ^ 2 := by nlinarith
      nlinarith [mul_lt_mul_of_pos_left this hgb]
    have ha1 : 0 < 2 * γ * β * (1 - ξ₂) / ξ₂ ^ 2 := by
      apply div_pos _ (by positivity)
      have : 0 < 1 - ξ₂ := by linarith
      positivity
    exact co_core β (fun s => P (lam θ β s)) hQ
      (nuStar (quadCost γ) m₂ β ξ₂) (nuStar (quadCost γ) m₁ β ξ₁) (ξ₂ ^ 2 / (2 * γ)) (ξ₁ ^ 2 / (2 * γ)) _ _
      (by positivity) (by positivity) ha ha1
      (co_nu β ξ₂ γ hξ2 h2γ hβ1 m₂ hm2) (co_nu β ξ₁ γ h0 (by linarith) hβ1 m₁ hm1)
      s₂ s₁ he2 he1
  · intro ξ γ₁ γ₂ m₁ m₂ s₁ s₂ h0 h1 hγ1 h12 hm1 hm2 he1 he2
    have hγ0 : 0 < γ₁ := by linarith
    have hγ2 : 0 < γ₂ := by linarith
    have hb : 0 < β * (1 - ξ) := mul_pos hβ (by linarith)
    have ha : 2 * γ₁ * β * (1 - ξ) / ξ ^ 2 < 2 * γ₂ * β * (1 - ξ) / ξ ^ 2 := by
      apply div_lt_div_of_pos_right _ (by positivity)
      nlinarith
    have ha1 : 0 < 2 * γ₁ * β * (1 - ξ) / ξ ^ 2 := by
      apply div_pos _ (by positivity)
      nlinarith
    exact co_core β (fun s => P (lam θ β s)) hQ
      (nuStar (quadCost γ₁) m₁ β ξ) (nuStar (quadCost γ₂) m₂ β ξ) (ξ ^ 2 / (2 * γ₁)) (ξ ^ 2 / (2 * γ₂)) _ _
      (by positivity) (by positivity) ha ha1
      (co_nu β ξ γ₁ h0 hγ1 hβ1 m₁ hm1) (co_nu β ξ γ₂ h0 (by linarith) hβ1 m₂ hm2)
      s₁ s₂ he1 he2

end CommonOwnership.Governance


-- Platform entry point: restates the target verbatim.
namespace CommonOwnership.Governance

/-- Proposition 3, p. 17: under the quadratic cost (20), the equilibrium level of common
ownership is monotonically decreasing in `ξ` and monotonically increasing in `γ`: every
equilibrium stake at the larger `ξ` is at most every equilibrium stake at the smaller `ξ`
(`γ` fixed), and every equilibrium stake at the larger `γ` is at least every equilibrium
stake at the smaller `γ` (`ξ` fixed). Monitoring is the blockholder's optimum at each
parameter value; industry profit `P(λ)` is one positive function of `λ` shared by both. -/
theorem _root_.solution (θ β : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (P : ℝ → ℝ) (hP : ∀ l ∈ Set.Icc (0:ℝ) 1, 0 < P l) :
    (∀ (ξ₁ ξ₂ γ : ℝ) (m₁ m₂ : ℝ → ℝ) (s₁ s₂ : ℝ),
      0 < ξ₁ → ξ₁ < ξ₂ → ξ₂ < 1 → ξ₂ < γ →
      IsOptMonitoring (quadCost γ) ξ₁ β m₁ → IsOptMonitoring (quadCost γ) ξ₂ β m₂ →
      IsEqOwnership (jointSurplus (quadCost γ) m₁ P θ β ξ₁) β s₁ →
      IsEqOwnership (jointSurplus (quadCost γ) m₂ P θ β ξ₂) β s₂ → s₂ ≤ s₁) ∧
    (∀ (ξ γ₁ γ₂ : ℝ) (m₁ m₂ : ℝ → ℝ) (s₁ s₂ : ℝ),
      0 < ξ → ξ < 1 → ξ < γ₁ → γ₁ < γ₂ →
      IsOptMonitoring (quadCost γ₁) ξ β m₁ → IsOptMonitoring (quadCost γ₂) ξ β m₂ →
      IsEqOwnership (jointSurplus (quadCost γ₁) m₁ P θ β ξ) β s₁ →
      IsEqOwnership (jointSurplus (quadCost γ₂) m₂ P θ β ξ) β s₂ → s₁ ≤ s₂) := by
  apply @CommonOwnership.Governance.proposition3_monotone <;> assumption

end CommonOwnership.Governance
