-- Prove2me | solution 1 for FiniteEnergyPlane.le_div_mul_exp_of_deriv_ge
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T22:01:59.003725+00:00
-- url     : https://prove2.me/submissions/9f775110-79d5-47e9-8389-2291ce60883b

import Mathlib

open Set Filter Topology

namespace FiniteEnergyPlane

/-- If `a → 0` at `+∞` and `a' ≥ -K e^{-βs}` on `(s₀, ∞)`, then `a s ≤ (K/β) e^{-βs}` there. -/
theorem le_div_mul_exp_of_deriv_ge_aux (a a' : ℝ → ℝ) (s₀ K β : ℝ) (hβ : 0 < β)
    (hd : ∀ s > s₀, HasDerivAt a (a' s) s) (ha : Tendsto a atTop (𝓝 0))
    (hineq : ∀ s > s₀, -(K * Real.exp (-(β * s))) ≤ a' s) :
    ∀ s > s₀, a s ≤ K / β * Real.exp (-(β * s)) := by
  set ψ : ℝ → ℝ := fun s => a s - K / β * Real.exp (-(β * s)) with hψ
  have hψd : ∀ s > s₀, HasDerivAt ψ (a' s + K * Real.exp (-(β * s))) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => Real.exp (-(β * s))) (Real.exp (-(β * s)) * (-β)) s := by
      have := ((hasDerivAt_id s).const_mul β).neg.exp
      simpa using this
    have := (hd s hs).sub (h1.const_mul (K / β))
    refine this.congr_deriv ?_
    field_simp
    ring
  have hmono : MonotoneOn ψ (Ioi s₀) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi s₀)
      (fun x hx => (hψd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hψd x (interior_subset hx)).hasDerivWithinAt) ?_
    intro x hx
    rw [interior_Ioi] at hx
    have := hineq x hx
    linarith
  have hψt : Tendsto ψ atTop (𝓝 0) := by
    have h2 : Tendsto (fun s => K / β * Real.exp (-(β * s))) atTop (𝓝 0) := by
      have : Tendsto (fun s => Real.exp (-(β * s))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hβ)
      simpa using this.const_mul (K / β)
    simpa using ha.sub h2
  intro s hs
  have : ψ s ≤ 0 := by
    refine ge_of_tendsto hψt ?_
    filter_upwards [eventually_ge_atTop s] with S hS
    exact hmono hs (lt_of_lt_of_le hs hS) hS
  simp only [hψ] at this
  linarith

lemma kg_hasDerivAt_exp_mul (c s : ℝ) :
    HasDerivAt (fun s => Real.exp (c * s)) (Real.exp (c * s) * c) s := by
  simpa using ((hasDerivAt_id s).const_mul c).exp

/-- If `a → 0` at `+∞` and `a' ≥ |a| - K e^{-βs}` on `(s₀, ∞)` with `β > 0`, then `a` decays
exponentially. -/
theorem abs_le_exp_of_deriv_ge_abs_sub_aux (a a' : ℝ → ℝ) (s₀ K β : ℝ) (hβ : 0 < β)
    (hd : ∀ s > s₀, HasDerivAt a (a' s) s) (ha : Tendsto a atTop (𝓝 0))
    (hineq : ∀ s > s₀, |a s| - K * Real.exp (-(β * s)) ≤ a' s) :
    ∃ κ > 0, ∃ C s₁ : ℝ, ∀ s ≥ s₁, |a s| ≤ C * Real.exp (-(κ * s)) := by
  set κ := min 1 (β / 2) with hκdef
  have hκ : 0 < κ := lt_min one_pos (by linarith)
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκβ : κ < β := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hup := le_div_mul_exp_of_deriv_ge_aux a a' s₀ K β hβ hd ha
    (fun s hs => by have := hineq s hs; have := abs_nonneg (a s); linarith)
  set φ : ℝ → ℝ := fun s => Real.exp (κ * s) * a s -
    K / (β - κ) * Real.exp ((κ - β) * s) with hφ
  have hβκ : 0 < β - κ := by linarith
  have hφd : ∀ s > s₀, HasDerivAt φ (Real.exp (κ * s) * κ * a s + Real.exp (κ * s) * a' s -
      K / (β - κ) * (Real.exp ((κ - β) * s) * (κ - β))) s := by
    intro s hs
    exact ((kg_hasDerivAt_exp_mul κ s).mul (hd s hs)).sub
      ((kg_hasDerivAt_exp_mul (κ - β) s).const_mul _)
  have hsplit : ∀ s, Real.exp ((κ - β) * s) = Real.exp (κ * s) * Real.exp (-(β * s)) := by
    intro s; rw [← Real.exp_add]; ring_nf
  have hmono : MonotoneOn φ (Ioi s₀) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi s₀)
      (fun x hx => (hφd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hφd x (interior_subset hx)).hasDerivWithinAt) ?_
    intro x hx
    rw [interior_Ioi] at hx
    have h1 := hineq x hx
    have h2 : 0 ≤ |a x| + κ * a x := by
      rcases le_or_gt 0 (a x) with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_neg h]; nlinarith
    have he := Real.exp_pos (κ * x)
    have e3 : K / (β - κ) * (Real.exp ((κ - β) * x) * (κ - β)) =
        -(K * Real.exp ((κ - β) * x)) := by field_simp; ring
    rw [e3, hsplit x]
    have : 0 ≤ Real.exp (κ * x) * (κ * a x + a' x + K * Real.exp (-(β * x))) :=
      mul_nonneg he.le (by linarith)
    nlinarith
  set s₁ := max (s₀ + 1) 0 with hs₁
  have hs₁0 : s₀ < s₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hs₁p : 0 ≤ s₁ := le_max_right _ _
  refine ⟨κ, hκ, |K| / β + |φ s₁| + |K| / (β - κ), s₁, fun s hs => ?_⟩
  have hs0 : s₀ < s := lt_of_lt_of_le hs₁0 hs
  have hsp : 0 ≤ s := le_trans hs₁p hs
  have heκ := Real.exp_pos (-(κ * s))
  have hinv : Real.exp (κ * s) * Real.exp (-(κ * s)) = 1 := by
    rw [← Real.exp_add]; simp
  have hU : a s ≤ |K| / β * Real.exp (-(κ * s)) := by
    refine (hup s hs0).trans ?_
    have h1 : Real.exp (-(β * s)) ≤ Real.exp (-(κ * s)) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h2 : K / β ≤ |K| / β := div_le_div_of_nonneg_right (le_abs_self K) hβ.le
    calc K / β * Real.exp (-(β * s)) ≤ |K| / β * Real.exp (-(β * s)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ ≤ |K| / β * Real.exp (-(κ * s)) :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg (abs_nonneg K) hβ.le)
  have hL : -((|φ s₁| + |K| / (β - κ)) * Real.exp (-(κ * s))) ≤ a s := by
    have hm := hmono hs₁0 hs0 hs
    have hE1 : Real.exp ((κ - β) * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hK1 : -(|K| / (β - κ)) ≤ K / (β - κ) * Real.exp ((κ - β) * s) := by
      have hq : 0 ≤ |K| / (β - κ) := div_nonneg (abs_nonneg K) hβκ.le
      have hq2 : -(|K| / (β - κ)) ≤ K / (β - κ) := by
        rw [← neg_div]; exact div_le_div_of_nonneg_right (neg_abs_le K) hβκ.le
      have he0 := (Real.exp_pos ((κ - β) * s)).le
      nlinarith
    have hφs₁ : -|φ s₁| ≤ φ s₁ := neg_abs_le _
    have hm' : φ s₁ ≤ Real.exp (κ * s) * a s - K / (β - κ) * Real.exp ((κ - β) * s) := hm
    have key : -(|φ s₁| + |K| / (β - κ)) ≤ Real.exp (κ * s) * a s := by linarith
    have := mul_le_mul_of_nonneg_right key heκ.le
    have e : Real.exp (κ * s) * a s * Real.exp (-(κ * s)) = a s := by
      rw [mul_comm (Real.exp (κ * s)), mul_assoc, hinv, mul_one]
    rw [e] at this
    linarith
  rw [abs_le]
  constructor
  · have : 0 ≤ |K| / β * Real.exp (-(κ * s)) := by positivity
    nlinarith
  · have : 0 ≤ (|φ s₁| + |K| / (β - κ)) * Real.exp (-(κ * s)) := by positivity
    nlinarith

/-- Window estimate: if `|a| ≤ A e^{-κs}`, `E` is `M`-Lipschitz and `a' ≥ E - K e^{-βs}` on
`(s₀, ∞)` with `κ, β > 0`, then `E` is bounded above by a decaying exponential. -/
theorem le_exp_of_deriv_ge_of_lipschitz_aux (a a' E : ℝ → ℝ) (s₀ A κ M K β : ℝ) (hκ : 0 < κ)
    (hβ : 0 < β) (hd : ∀ s > s₀, HasDerivAt a (a' s) s)
    (ha : ∀ s > s₀, |a s| ≤ A * Real.exp (-(κ * s)))
    (hE : ∀ x > s₀, ∀ y > s₀, |E x - E y| ≤ M * |x - y|)
    (hineq : ∀ s > s₀, E s - K * Real.exp (-(β * s)) ≤ a' s) :
    ∃ κ' > 0, ∃ C s₁ : ℝ, ∀ s ≥ s₁, E s ≤ C * Real.exp (-(κ' * s)) := by
  set κ' := min (κ / 2) β with hκ'
  have hκ'0 : 0 < κ' := lt_min (by linarith) hβ
  set s₁ := max (s₀ + 1) 0 with hs₁
  have hs₁0 : s₀ < s₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hs₁p : 0 ≤ s₁ := le_max_right _ _
  refine ⟨κ', hκ'0, 2 * |A| + |K| + |M|, s₁, fun s hs => ?_⟩
  have hs0 : s₀ < s := lt_of_lt_of_le hs₁0 hs
  have hsp : 0 ≤ s := le_trans hs₁p hs
  set h := Real.exp (-(κ / 2 * s)) with hh
  have hpos : 0 < h := Real.exp_pos _
  have hsq : Real.exp (-(κ * s)) = h * h := by rw [hh, ← Real.exp_add]; ring_nf
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope a a' (show s < s + h by linarith)
    (fun x hx => (hd x (lt_of_lt_of_le hs0 hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => hd x (lt_trans hs0 hx.1))
  have hc0 : s₀ < c := lt_trans hs0 hc.1
  have hAa : ∀ x ≥ s, |a x| ≤ |A| * (h * h) := by
    intro x hx
    refine (ha x (lt_of_lt_of_le hs0 hx)).trans ?_
    rw [← hsq]
    calc A * Real.exp (-(κ * x)) ≤ |A| * Real.exp (-(κ * x)) :=
          mul_le_mul_of_nonneg_right (le_abs_self A) (Real.exp_pos _).le
      _ ≤ |A| * Real.exp (-(κ * s)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (abs_nonneg A)
  have h1 : a' c ≤ 2 * |A| * h := by
    rw [hcd, show s + h - s = h by ring, div_le_iff₀ hpos]
    have := hAa (s + h) (by linarith)
    have := hAa s le_rfl
    have := le_abs_self (a (s + h))
    have := neg_abs_le (a s)
    nlinarith
  have h2 : E s ≤ E c + |M| * h := by
    have hsc : |s - c| ≤ h := by
      rw [abs_sub_comm, abs_of_pos (by linarith [hc.1])]; linarith [hc.2]
    have : M * |s - c| ≤ |M| * h :=
      (mul_le_mul_of_nonneg_right (le_abs_self M) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hsc (abs_nonneg M))
    have := (abs_le.1 (hE s hs0 c hc0)).2
    linarith
  have h3 : E c ≤ a' c + |K| * Real.exp (-(β * s)) := by
    have := hineq c hc0
    have : K * Real.exp (-(β * c)) ≤ |K| * Real.exp (-(β * s)) :=
      (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hc.1])) (abs_nonneg K))
    linarith
  have hh' : h ≤ Real.exp (-(κ' * s)) :=
    Real.exp_le_exp.2 (by have := min_le_left (κ / 2) β; nlinarith)
  have hb' : Real.exp (-(β * s)) ≤ Real.exp (-(κ' * s)) :=
    Real.exp_le_exp.2 (by have := min_le_right (κ / 2) β; nlinarith)
  have := abs_nonneg A; have := abs_nonneg K; have := abs_nonneg M
  nlinarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open Set Filter Topology

theorem solution (a a' : ℝ → ℝ) (s₀ K β : ℝ) (hβ : 0 < β)
    (hd : ∀ s > s₀, HasDerivAt a (a' s) s) (ha : Tendsto a atTop (𝓝 0))
    (hineq : ∀ s > s₀, -(K * Real.exp (-(β * s))) ≤ a' s) :
    ∀ s > s₀, a s ≤ K / β * Real.exp (-(β * s)) :=
  le_div_mul_exp_of_deriv_ge_aux a a' s₀ K β hβ hd ha hineq
