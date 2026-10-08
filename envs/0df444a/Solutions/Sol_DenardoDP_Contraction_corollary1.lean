-- Prove2me | solution 1 for DenardoDP.Contraction.corollary1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:45:44.253977+00:00
-- url     : https://prove2.me/submissions/f7a4fc8d-4985-4264-b8c6-500ed7efadd4

import Mathlib
import Definitions.Def_DenardoDP_Contraction_Model

set_option autoImplicit false

namespace DenardoDP.Contraction.Cor1Aux

open DenardoDP.Contraction

theorem dist_le_of_pt {Ω : Type*} (u w : BFun Ω) (C : ℝ) (hC : 0 ≤ C)
    (hpt : ∀ x, |u x - w x| ≤ C) : dist u w ≤ C := by
  rw [dist_eq_norm]
  refine lp.norm_le_of_forall_le hC (fun x => ?_)
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
  exact hpt x

theorem policy_lip {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ)
    (H : ((x : Ω) → D x) → BFun Ω → BFun Ω) (c : ℝ)
    (hH : IsPolicyOperator h H) (hc : ContractionAssumption h c)
    (δ : (x : Ω) → D x) (u w : BFun Ω) :
    dist (H δ u) (H δ w) ≤ c * dist u w := by
  apply dist_le_of_pt _ _ _ (mul_nonneg hc.1 dist_nonneg)
  intro x
  rw [hH, hH]
  exact hc.2.2 u w x (δ x)

end DenardoDP.Contraction.Cor1Aux

open DenardoDP.Contraction in
theorem solution {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → BFun Ω → ℝ)
    (H : ((x : Ω) → D x) → BFun Ω → BFun Ω)
    (A : BFun Ω → BFun Ω) (c : ℝ)
    (v : ((x : Ω) → D x) → BFun Ω) (vstar : BFun Ω)
    (hH : IsPolicyOperator h H) (hA : IsMaxOperator h A)
    (hc : ContractionAssumption h c)
    (hv : ∀ δ, H δ (v δ) = v δ) (hstar : A vstar = vstar) :
    (∀ ε : ℝ, 0 < ε → ∃ δ : (x : Ω) → D x,
      dist (H δ vstar) vstar ≤ ε * (1 - c)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ δ : (x : Ω) → D x,
      dist (H δ vstar) vstar ≤ ε * (1 - c) → dist (v δ) vstar ≤ ε) ∧
    (∀ δ : (x : Ω) → D x,
      dist (H δ vstar) vstar = 0 → v δ = vstar) := by
  have hc0 := hc.1
  have hc1 := hc.2.1
  have key : ∀ δ : (x : Ω) → D x,
      (1 - c) * dist (v δ) vstar ≤ dist (H δ vstar) vstar := by
    intro δ
    have h1 : dist (v δ) vstar ≤ dist (H δ (v δ)) (H δ vstar) + dist (H δ vstar) vstar := by
      calc dist (v δ) vstar = dist (H δ (v δ)) vstar := by rw [hv δ]
        _ ≤ _ := dist_triangle _ _ _
    have h2 := Cor1Aux.policy_lip h H c hH hc δ (v δ) vstar
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε
    have hpos : 0 < ε * (1 - c) := mul_pos hε (by linarith)
    have hex : ∀ x, ∃ d : D x, vstar x - ε * (1 - c) < h x d vstar ∧ h x d vstar ≤ vstar x := by
      intro x
      have hl := hA vstar x
      rw [hstar] at hl
      obtain ⟨y, ⟨d, rfl⟩, hy1, hy2⟩ := hl.exists_between (by linarith : vstar x - ε * (1 - c) < vstar x)
      exact ⟨d, hy1, hy2⟩
    choose δ hδ using hex
    refine ⟨δ, Cor1Aux.dist_le_of_pt _ _ _ hpos.le (fun x => ?_)⟩
    rw [hH, abs_le]
    obtain ⟨a, b⟩ := hδ x
    constructor <;> linarith
  · intro ε hε δ hδ
    have := key δ
    have h1c : 0 < 1 - c := by linarith
    by_contra hcon
    rw [not_le] at hcon
    nlinarith
  · intro δ hδ
    have := key δ
    rw [hδ] at this
    have h1c : 0 < 1 - c := by linarith
    have : dist (v δ) vstar ≤ 0 := by nlinarith [dist_nonneg (x := v δ) (y := vstar)]
    exact dist_le_zero.mp this
