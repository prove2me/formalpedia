-- Prove2me | solution 1 for FirstOrderOpt.OperatorSliding.gs_convergence_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:01:25.659408+00:00
-- url     : https://prove2.me/submissions/05a97124-3865-46fd-bfc0-73b1d5bf6136

import Mathlib

namespace FirstOrderOpt.OperatorSliding

/-- The step sequence `P t = (1/2)^t` satisfies the recursion with `p ≡ 1`. -/
theorem aux_gscb_Prec (t : ℕ) (ht : 1 ≤ t) :
    ((1 : ℝ) / 2) ^ t = (1 : ℝ) * (1 + (1 : ℝ))⁻¹ * ((1 : ℝ) / 2) ^ (t - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

end FirstOrderOpt.OperatorSliding

open FirstOrderOpt.OperatorSliding

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f h chi Ψ : E → ℝ) (hΨ : ∀ u, Ψ u = f u + h u + chi u)
    (V : E → E → ℝ) (hVnonneg : ∀ a b, 0 ≤ V a b)
    (L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (x0 xstar : E) (hx0 : x0 ∈ X) (hxstar : xstar ∈ X)
    (hxstarOpt : ∀ w ∈ X, Ψ xstar ≤ Ψ w)
    (p θ P : ℕ → ℝ) (hp : ∀ t, 0 < p t) (hP0 : P 0 = 1)
    (hPrec : ∀ t : ℕ, 1 ≤ t → P t = p t * (1 + p t)⁻¹ * P (t - 1))
    (hθ : ∀ t : ℕ, 1 ≤ t → θ t = (P (t - 1) - P t) / ((1 - P t) * P (t - 1)))
    (β γ : ℕ → ℝ) (T : ℕ → ℕ) (hTpos : ∀ k : ℕ, 1 ≤ k → 1 ≤ T k)
    (hγ1 : γ 1 = 1) (hβγ : ∀ k : ℕ, 1 ≤ k → 0 ≤ β k - L * γ k)
    (Γ : ℕ → ℝ) (hΓ1 : Γ 1 = 1) (hΓrec : ∀ k : ℕ, 2 ≤ k → Γ k = (1 - γ k) * Γ (k - 1))
    (hMono : ∀ k : ℕ, 2 ≤ k →
      γ k * β k / (Γ k * (1 - P (T k))) ≤ γ (k - 1) * β (k - 1) / (Γ (k - 1) * (1 - P (T (k - 1)))))
    (xIter xbar : ℕ → E) (hxIter0 : xIter 0 = x0) (hxbar0 : xbar 0 = x0)
    (hRecursion : ∀ w ∈ X, ∀ k : ℕ, 1 ≤ k →
      Ψ (xbar k) - Ψ w ≤ (1 - γ k) * (Ψ (xbar (k - 1)) - Ψ w)
        + γ k * (1 - P (T k))⁻¹ *
          (β k * V (xIter (k - 1)) w - β k * V (xIter k) w
            + M ^ 2 * P (T k) / (2 * β k) * ∑ i ∈ Finset.Icc 1 (T k), (p i ^ 2 * P (i - 1))⁻¹))
    (N : ℕ) (hN : 1 ≤ N),
    Ψ (xbar N) - Ψ xstar ≤
      Γ N * β 1 / (1 - P (T 1)) * V x0 xstar
        + M ^ 2 * Γ N / 2 *
            ∑ k ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc 1 (T k),
              γ k * P (T k) / (Γ k * β k * (1 - P (T k)) * p i ^ 2 * P (i - 1))) := by
  intro H
  -- Counterexample: `E = ℝ`, `X = {0}`, `Ψ = id`, `V = 0`, `L = M = 1`, `p ≡ 1`,
  -- `P t = (1/2)^t`, `β ≡ γ ≡ 1`, `T ≡ 1`, `Γ 1 = 1`, `Γ k = 0` otherwise,
  -- `xIter ≡ 0`, `xbar 0 = 0`, `xbar k = 1/4` for `k ≥ 1`, `N = 2`.
  let P : ℕ → ℝ := fun t => ((1 : ℝ) / 2) ^ t
  let θ : ℕ → ℝ := fun t => (P (t - 1) - P t) / ((1 - P t) * P (t - 1))
  let Γ : ℕ → ℝ := fun k => if k = 1 then 1 else 0
  let xbar : ℕ → ℝ := fun k => if k = 0 then 0 else 1 / 4
  have hΓnn : ∀ k, 0 ≤ Γ k := by
    intro k; by_cases hk : k = 1 <;> simp [Γ, hk]
  have key := H (E := ℝ) ({0} : Set ℝ) (fun u => u) (fun _ => 0) (fun _ => 0) (fun u => u)
    (fun u => by ring) (fun _ _ => 0) (fun _ _ => le_refl _)
    1 1 one_pos one_pos 0 0 rfl rfl
    (fun w hw => by simp only [Set.mem_singleton_iff] at hw; simp [hw])
    (fun _ => 1) θ P (fun _ => one_pos) (by simp [P])
    (fun t ht => aux_gscb_Prec t ht) (fun _ _ => rfl)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ _ => le_refl _)
    rfl (fun _ _ => by norm_num) Γ (by simp [Γ]) ?rec ?mono
    (fun _ => 0) xbar rfl (by simp [xbar]) ?recursion 2 (by norm_num)
  · simp [xbar, Γ] at key
    norm_num at key
  case rec =>
    intro k hk
    have : k ≠ 1 := by omega
    simp [Γ, this]
  case mono =>
    intro k hk
    have : k ≠ 1 := by omega
    have hl : (1 : ℝ) * 1 / (Γ k * (1 - P 1)) = 0 := by simp [Γ, this]
    rw [hl]
    apply div_nonneg (by norm_num)
    apply mul_nonneg (hΓnn _)
    simp [P]; norm_num
  case recursion =>
    intro w hw k hk
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    have : k ≠ 0 := by omega
    simp [xbar, this, P]
    norm_num
