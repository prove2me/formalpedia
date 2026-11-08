-- Prove2me | solution 1 for ConicBlackwell.lemma_3_2_statement_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:44:39.193949+00:00
-- url     : https://prove2.me/submissions/d9108699-9cb9-4777-9160-bd83a8a0c9b4

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

theorem solution {n : ℕ} (X : Set (E n)) (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X) :
    MoreauProx.Decomposition.IsClosedConvexCone (target X) ∧
      ∀ u ∈ cone (lift (kappa X) '' X), -u ∈ target X := by
  have hlift : ∀ (a b : ℝ) (x y : E n), ⟪lift a x, lift b y⟫ = a * b + ⟪x, y⟫ := by
    intro a b x y
    simp only [lift, PiLp.inner_apply, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
    simp [PiLp.inner_apply, mul_comm]
  have hbdd : BddAbove ((fun x : E n => ‖x‖) '' X) :=
    (hXc.image continuous_norm).bddAbove
  have hnorm : ∀ x ∈ X, ‖x‖ ≤ kappa X := fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
  have hk0 : 0 ≤ kappa X := by
    obtain ⟨x, hx⟩ := hXne
    exact (norm_nonneg x).trans (hnorm x hx)
  constructor
  · refine ⟨⟨0, fun x _ => by simp⟩, ?_, ?_, ?_⟩
    · have : target X = ⋂ x ∈ cone (lift (kappa X) '' X), {θ : E (n + 1) | ⟪θ, x⟫ ≤ 0} := by
        ext θ; simp [target, polar]
      rw [this]
      exact isClosed_biInter (fun x _ => isClosed_le (continuous_id.inner continuous_const)
        continuous_const)
    · intro θ1 h1 θ2 h2 a b ha hb hab x hx
      have e1 := h1 x hx
      have e2 := h2 x hx
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      nlinarith [mul_nonneg ha (by linarith : (0:ℝ) ≤ -⟪θ1, x⟫),
        mul_nonneg hb (by linarith : (0:ℝ) ≤ -⟪θ2, x⟫)]
    · intro θ hθ t ht x hx
      have := hθ x hx
      rw [real_inner_smul_left]
      nlinarith
  · rintro u ⟨α, hα, w, ⟨x, hx, rfl⟩, rfl⟩
    rintro v ⟨β, hβ, w', ⟨x', hx', rfl⟩, rfl⟩
    rw [inner_neg_left, real_inner_smul_left, real_inner_smul_right, hlift]
    have h1 := hnorm x hx
    have h2 := hnorm x' hx'
    have hcs : -(‖x‖ * ‖x'‖) ≤ ⟪x, x'⟫ := by
      have := abs_real_inner_le_norm x x'
      rw [abs_le] at this
      exact this.1
    have hkk : ‖x‖ * ‖x'‖ ≤ kappa X * kappa X :=
      mul_le_mul h1 h2 (norm_nonneg _) hk0
    have hpos : 0 ≤ kappa X * kappa X + ⟪x, x'⟫ := by linarith
    have := mul_nonneg (mul_nonneg hα hβ) hpos
    nlinarith
