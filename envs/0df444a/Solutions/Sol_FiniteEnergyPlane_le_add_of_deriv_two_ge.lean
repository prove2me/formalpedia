-- Prove2me | solution 1 for FiniteEnergyPlane.le_add_of_deriv_two_ge
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-28T22:46:49.839479+00:00
-- url     : https://prove2.me/submissions/ac1e15af-33b8-49e2-97aa-93ab9c338a94

import Mathlib



/-! One-variable lemmas: doubling from a bounded logarithmic derivative, and a pointwise bound
from semiconvexity plus a primitive. -/

namespace HCWK

open Set

lemma monoOn_Icc_of_deriv (g g' : ℝ → ℝ) (a b : ℝ) (hd : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x)
    (hnn : ∀ x ∈ Icc a b, 0 ≤ g' x) : MonotoneOn g (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hnn x (interior_subset hx))

lemma monoOn_Ici_of_deriv (g g' : ℝ → ℝ) (a : ℝ) (hd : ∀ x ≥ a, HasDerivAt g (g' x) x)
    (hnn : ∀ x ≥ a, 0 ≤ g' x) : MonotoneOn g (Ici a) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hnn x (interior_subset hx))

/-- If `F' = 2D` and `|D| ≤ Λ F` on `[s₀, ∞)`, then `F(σ) ≤ e^{2Λ} F(s)` when `|σ - s| ≤ 1`. -/
lemma doubling (F D : ℝ → ℝ) (s₀ Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hd : ∀ x ≥ s₀, HasDerivAt F (2 * D x) x) (hD : ∀ x ≥ s₀, |D x| ≤ Λ * F x)
    (hF0' : ∀ x ≥ s₀, 0 ≤ F x)
    {s σ : ℝ} (hs : s₀ ≤ s) (hσ : s₀ ≤ σ) (h1 : |σ - s| ≤ 1) :
    F σ ≤ Real.exp (2 * Λ) * F s := by
  have hF0 : 0 ≤ F s := hF0' s hs
  rcases le_total s σ with hsσ | hσs
  · -- `F e^{-2Λx}` is antitone
    have hm := monoOn_Ici_of_deriv (fun x => -(F x * Real.exp (-(2 * Λ * x))))
      (fun x => -((2 * D x) * Real.exp (-(2 * Λ * x)) +
        F x * (Real.exp (-(2 * Λ * x)) * (-(2 * Λ)))))
      s₀ (fun x hx => by
        have h2 : HasDerivAt (fun x => -(2 * Λ * x)) (-(2 * Λ)) x := by
          exact (((hasDerivAt_id' x).const_mul (2 * Λ)).neg).congr_deriv (by ring)
        exact ((hd x hx).mul (h2.exp)).neg)
      (fun x hx => by
        have h1 := (le_abs_self (D x)).trans (hD x hx)
        have he := Real.exp_pos (-(2 * Λ * x))
        have := mul_nonneg he.le (sub_nonneg.2 h1)
        nlinarith)
    have := hm hs hσ hsσ
    simp only [neg_le_neg_iff] at this
    have e1 : Real.exp (-(2 * Λ * σ)) * Real.exp (2 * Λ * σ) = 1 := by
      rw [← Real.exp_add]; simp
    have e2 : Real.exp (-(2 * Λ * s)) * Real.exp (2 * Λ * σ) = Real.exp (2 * Λ * (σ - s)) := by
      rw [← Real.exp_add]; ring_nf
    have hle : Real.exp (2 * Λ * (σ - s)) ≤ Real.exp (2 * Λ) := by
      apply Real.exp_le_exp.2
      have : σ - s ≤ 1 := (le_abs_self _).trans h1
      nlinarith
    have hpos := Real.exp_pos (2 * Λ * σ)
    have := mul_le_mul_of_nonneg_right this hpos.le
    calc F σ = F σ * Real.exp (-(2 * Λ * σ)) * Real.exp (2 * Λ * σ) := by
          rw [mul_assoc, e1, mul_one]
      _ ≤ F s * Real.exp (-(2 * Λ * s)) * Real.exp (2 * Λ * σ) := this
      _ = Real.exp (2 * Λ * (σ - s)) * F s := by rw [mul_assoc, e2, mul_comm]
      _ ≤ Real.exp (2 * Λ) * F s := mul_le_mul_of_nonneg_right hle hF0
  · -- `F e^{2Λx}` is monotone
    have hm := monoOn_Ici_of_deriv (fun x => F x * Real.exp (2 * Λ * x))
      (fun x => (2 * D x) * Real.exp (2 * Λ * x) + F x * (Real.exp (2 * Λ * x) * (2 * Λ)))
      s₀ (fun x hx => by
        have h2 : HasDerivAt (fun x => 2 * Λ * x) (2 * Λ) x := by
          simpa using ((hasDerivAt_id x).const_mul (2 * Λ))
        exact (hd x hx).mul (h2.exp))
      (fun x hx => by
        have h1 := (neg_abs_le (D x)).trans' (neg_le_neg (hD x hx))
        have he := Real.exp_pos (2 * Λ * x)
        have := mul_nonneg he.le (show 0 ≤ D x + Λ * F x by linarith)
        nlinarith)
    have := hm hσ hs hσs
    simp only at this
    have e1 : Real.exp (2 * Λ * σ) * Real.exp (-(2 * Λ * σ)) = 1 := by
      rw [← Real.exp_add]; simp
    have e2 : Real.exp (2 * Λ * s) * Real.exp (-(2 * Λ * σ)) = Real.exp (2 * Λ * (s - σ)) := by
      rw [← Real.exp_add]; ring_nf
    have hle : Real.exp (2 * Λ * (s - σ)) ≤ Real.exp (2 * Λ) := by
      apply Real.exp_le_exp.2
      have : s - σ ≤ 1 := by rw [abs_sub_comm] at h1; exact (le_abs_self _).trans h1
      nlinarith
    have hpos := Real.exp_pos (-(2 * Λ * σ))
    have := mul_le_mul_of_nonneg_right this hpos.le
    calc F σ = F σ * Real.exp (2 * Λ * σ) * Real.exp (-(2 * Λ * σ)) := by
          rw [mul_assoc, e1, mul_one]
      _ ≤ F s * Real.exp (2 * Λ * s) * Real.exp (-(2 * Λ * σ)) := this
      _ = Real.exp (2 * Λ * (s - σ)) * F s := by rw [mul_assoc, e2, mul_comm]
      _ ≤ Real.exp (2 * Λ) * F s := mul_le_mul_of_nonneg_right hle hF0

/-- Pointwise bound on `[s - 1, s + 1]`: if `H'' ≥ -B`, `D' ≥ H - B'` and `|D| ≤ L`, then
`H(s) ≤ L + B / 2 + B'`. -/
lemma window (H H1 H2 D Dd : ℝ → ℝ) (s B B' L : ℝ) (hB : 0 ≤ B)
    (hH : ∀ x ∈ Icc (s - 1) (s + 1), HasDerivAt H (H1 x) x)
    (hH1 : ∀ x ∈ Icc (s - 1) (s + 1), HasDerivAt H1 (H2 x) x)
    (hH2 : ∀ x ∈ Icc (s - 1) (s + 1), -B ≤ H2 x)
    (hDd : ∀ x ∈ Icc (s - 1) (s + 1), HasDerivAt D (Dd x) x)
    (hDH : ∀ x ∈ Icc (s - 1) (s + 1), H x - B' ≤ Dd x)
    (hL : ∀ x ∈ Icc (s - 1) (s + 1), |D x| ≤ L) :
    H s ≤ L + B / 2 + B' := by
  have mp : ∀ x ∈ Icc (0:ℝ) 1, s + x ∈ Icc (s - 1) (s + 1) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have mm : ∀ x ∈ Icc (0:ℝ) 1, s - x ∈ Icc (s - 1) (s + 1) := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have dp : ∀ x : ℝ, HasDerivAt (fun x => s + x) 1 x := fun x => (hasDerivAt_id x).const_add s
  have dm : ∀ x : ℝ, HasDerivAt (fun x => s - x) (-1) x := fun x => (hasDerivAt_id x).const_sub s
  -- `m₁(x) = H₁(s+x) - H₁(s-x) + 2Bx ≥ 0`
  have hm1 := monoOn_Icc_of_deriv (fun x => H1 (s + x) - H1 (s - x) + 2 * B * x)
    (fun x => H2 (s + x) * 1 - H2 (s - x) * (-1) + 2 * B) 0 1
    (fun x hx => by
      have h1 := (hH1 _ (mp x hx)).comp x (dp x)
      have h2 := (hH1 _ (mm x hx)).comp x (dm x)
      have h3 : HasDerivAt (fun x => 2 * B * x) (2 * B) x := by
        simpa using (hasDerivAt_id x).const_mul (2 * B)
      exact (h1.sub h2).add h3)
    (fun x hx => by have := hH2 _ (mp x hx); have := hH2 _ (mm x hx); linarith)
  have m1nn : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ H1 (s + x) - H1 (s - x) + 2 * B * x := by
    intro x hx
    have := hm1 ⟨le_rfl, zero_le_one⟩ hx hx.1
    simpa using this
  -- `m(x) = H(s+x) + H(s-x) - 2H(s) + Bx² ≥ 0`
  have hm := monoOn_Icc_of_deriv (fun x => H (s + x) + H (s - x) - 2 * H s + B * x ^ 2)
    (fun x => H1 (s + x) * 1 + H1 (s - x) * (-1) + B * (2 * x)) 0 1
    (fun x hx => by
      have h1 := (hH _ (mp x hx)).comp x (dp x)
      have h2 := (hH _ (mm x hx)).comp x (dm x)
      have h3 : HasDerivAt (fun x => B * x ^ 2) (B * (2 * x)) x := by
        simpa using ((hasDerivAt_pow 2 x).const_mul B)
      exact ((h1.add h2).sub_const _).add h3)
    (fun x hx => by have := m1nn x hx; linarith)
  have mnn : ∀ x ∈ Icc (0:ℝ) 1, 2 * H s - B ≤ H (s + x) + H (s - x) := by
    intro x hx
    have := hm ⟨le_rfl, zero_le_one⟩ hx hx.1
    simp only [add_zero, sub_zero] at this
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
    nlinarith
  -- `ψ(x) = D(s+x) - D(s-x) - x (2H(s) - B - 2B')` is monotone
  have hψ := monoOn_Icc_of_deriv (fun x => D (s + x) - D (s - x) - x * (2 * H s - B - 2 * B'))
    (fun x => Dd (s + x) * 1 - Dd (s - x) * (-1) - 1 * (2 * H s - B - 2 * B')) 0 1
    (fun x hx => by
      have h1 := (hDd _ (mp x hx)).comp x (dp x)
      have h2 := (hDd _ (mm x hx)).comp x (dm x)
      exact (h1.sub h2).sub ((hasDerivAt_id x).mul_const _))
    (fun x hx => by
      have := hDH _ (mp x hx); have := hDH _ (mm x hx); have := mnn x hx; linarith)
  have := hψ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [add_zero, sub_zero, zero_mul, sub_self, one_mul] at this
  have h1 := hL (s + 1) ⟨by linarith, le_rfl⟩
  have h2 := hL (s - 1) ⟨le_rfl, by linarith⟩
  have := le_abs_self (D (s + 1))
  have := neg_abs_le (D (s - 1))
  linarith

end HCWK

/-- Opens the `FiniteEnergyPlane` namespace for the bundled solution. -/
theorem FiniteEnergyPlane.hcwk_namespace_marker : True := trivial

open FiniteEnergyPlane

open Set

theorem solution (H H1 H2 D Dd : ℝ → ℝ) (s B B' L : ℝ) (hB : 0 ≤ B)
    (hH : ∀ x ∈ Icc (s - 1) (s + 1), HasDerivAt H (H1 x) x)
    (hH1 : ∀ x ∈ Icc (s - 1) (s + 1), HasDerivAt H1 (H2 x) x)
    (hH2 : ∀ x ∈ Icc (s - 1) (s + 1), -B ≤ H2 x)
    (hDd : ∀ x ∈ Icc (s - 1) (s + 1), HasDerivAt D (Dd x) x)
    (hDH : ∀ x ∈ Icc (s - 1) (s + 1), H x - B' ≤ Dd x)
    (hL : ∀ x ∈ Icc (s - 1) (s + 1), |D x| ≤ L) :
    H s ≤ L + B / 2 + B' :=
  HCWK.window H H1 H2 D Dd s B B' L hB hH hH1 hH2 hDd hDH hL
