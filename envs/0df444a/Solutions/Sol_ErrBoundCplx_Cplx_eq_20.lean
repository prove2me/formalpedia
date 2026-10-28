-- Prove2me | solution 1 for ErrBoundCplx.Cplx.eq_20
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:53:45.239565+00:00
-- url     : https://prove2.me/submissions/6f7a47a8-8b12-47bb-b9ca-b306b410ebd9

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ErrBoundCplx_Cplx_DescentSeq
open MoreauProx.Characterization NonconvexSplitting.ADMMKL
open Filter Topology

open ErrBoundCplx.Cplx in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : GammaZero f) (hmin : IsMinZero f)
    (rbar : ℝ) (φ : ℝ → ℝ) (hφ : IsDesingularizer rbar φ) (hKL : KLOnBand f rbar φ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : ℕ → H) (hx : IsSubgradDescentSeq f a b x)
    (r0 : ℝ) (hx0 : f (x 0) ≤ (r0 : EReal)) (hr0 : r0 < rbar)
    (hpos : ∀ j ≥ 1, 0 < f (x j) ∧ 0 < ‖x j - x (j - 1)‖) :
    ∀ k ≥ 1,
      deriv φ (f (x k)).toReal * ((f (x k)).toReal - (f (x (k + 1))).toReal)
          ≤ φ (f (x k)).toReal - φ (f (x (k + 1))).toReal ∧
        a * ‖x k - x (k + 1)‖ ^ 2 / (b * ‖x (k - 1) - x k‖)
          ≤ deriv φ (f (x k)).toReal * ((f (x k)).toReal - (f (x (k + 1))).toReal) ∧
        a / b * ((2 * ‖x k - x (k + 1)‖ * ‖x k - x (k - 1)‖ - ‖x (k - 1) - x k‖ ^ 2)
            / ‖x k - x (k - 1)‖)
          ≤ a * ‖x k - x (k + 1)‖ ^ 2 / (b * ‖x (k - 1) - x k‖) ∧
        a / b * (2 * ‖x k - x (k + 1)‖ - ‖x (k - 1) - x k‖)
          ≤ a / b * ((2 * ‖x k - x (k + 1)‖ * ‖x k - x (k - 1)‖ - ‖x (k - 1) - x k‖ ^ 2)
            / ‖x k - x (k - 1)‖) := by
  -- all values finite and below r0
  have hbd : ∀ j, f (x j) ≤ (r0 : EReal) := by
    intro j
    induction j with
    | zero => exact hx0
    | succ j ih =>
      have h := hx.2.1 (j + 1) (by omega)
      simp only [Nat.add_sub_cancel] at h
      have hc : (0 : EReal) ≤ ((a * ‖x (j + 1) - x j‖ ^ 2 : ℝ) : EReal) :=
        EReal.coe_nonneg.2 (by positivity)
      exact ((le_add_of_nonneg_right hc).trans h).trans ih
  have hne_top : ∀ j, f (x j) ≠ ⊤ := fun j => ne_top_of_le_ne_top (EReal.coe_ne_top r0) (hbd j)
  have hne_bot : ∀ j, f (x j) ≠ ⊥ := fun j => ne_bot_of_le_ne_bot EReal.zero_ne_bot (hmin.1 _)
  have hcoe : ∀ j, f (x j) = ((f (x j)).toReal : EReal) :=
    fun j => (EReal.coe_toReal (hne_top j) (hne_bot j)).symm
  have hdesc : ∀ k ≥ 1, (f (x k)).toReal + a * ‖x k - x (k - 1)‖ ^ 2 ≤ (f (x (k - 1))).toReal := by
    intro k hk
    have h := hx.2.1 k hk
    rw [hcoe k, hcoe (k - 1), ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    exact h
  have hur : ∀ j, (f (x j)).toReal ≤ r0 := by
    intro j
    have := hbd j
    rw [hcoe j, EReal.coe_le_coe_iff] at this
    exact this
  have hupos : ∀ j ≥ 1, 0 < (f (x j)).toReal := by
    intro j hj
    have := (hpos j hj).1
    rw [hcoe j, EReal.coe_pos] at this
    exact this
  intro k hk
  set fk := (f (x k)).toReal with hfk
  set fk1 := (f (x (k + 1))).toReal with hfk1
  set s := ‖x k - x (k + 1)‖ with hs
  set t := ‖x k - x (k - 1)‖ with ht
  have ht' : ‖x (k - 1) - x k‖ = t := norm_sub_rev _ _
  rw [ht']
  have hfk0 : 0 < fk := hupos k hk
  have hfk10 : 0 < fk1 := hupos (k + 1) (by omega)
  have hfkr : fk < rbar := (hur k).trans_lt hr0
  have hd1 := hdesc (k + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hd1
  rw [norm_sub_rev] at hd1
  -- hd1 : fk1 + a * s ^ 2 ≤ fk
  have hsq : a * s ^ 2 ≤ fk - fk1 := by linarith
  have ht0 : 0 < t := (hpos k hk).2
  have hs0 : 0 ≤ s := norm_nonneg _
  have hdiff : DifferentiableAt ℝ φ fk :=
    (hφ.2.2.2.2.1.differentiableOn one_ne_zero).differentiableAt
      (Ioo_mem_nhds hfk0 hfkr)
  have hdpos : 0 < deriv φ fk := hφ.2.2.2.2.2 fk ⟨hfk0, hfkr⟩
  -- KL bound
  obtain ⟨ω, hω, hωb⟩ := hx.2.2 k hk
  have hKLk : 1 ≤ deriv φ fk * ‖ω‖ := by
    have hlt : f (x k) < (rbar : EReal) := by
      rw [hcoe k]; exact EReal.coe_lt_coe_iff.2 hfkr
    exact hKL (x k) (hpos k hk).1 hlt ω hω
  have hKLt : 1 ≤ deriv φ fk * (b * t) :=
    hKLk.trans (mul_le_mul_of_nonneg_left hωb hdpos.le)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- concavity
    rcases eq_or_lt_of_le (show fk1 ≤ fk by linarith [hsq, mul_nonneg ha.le (sq_nonneg s)]) with h | h
    · rw [h]; simp
    · have hc := hφ.2.1.deriv_le_slope (x := fk1) (y := fk) ⟨hfk10.le, by linarith⟩
        ⟨hfk0.le, hfkr⟩ h hdiff
      rw [slope_def_field, le_div_iff₀ (by linarith)] at hc
      exact hc
  · rw [div_le_iff₀ (by positivity)]
    have h1 : 0 ≤ fk - fk1 := le_trans (by positivity) hsq
    calc a * s ^ 2 ≤ fk - fk1 := hsq
      _ = 1 * (fk - fk1) := (one_mul _).symm
      _ ≤ (deriv φ fk * (b * t)) * (fk - fk1) := mul_le_mul_of_nonneg_right hKLt h1
      _ = deriv φ fk * (fk - fk1) * (b * t) := by ring
  · have e : a / b * ((2 * s * t - t ^ 2) / t) = a * (2 * s * t - t ^ 2) / (b * t) := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ ha.le
    nlinarith [sq_nonneg (s - t)]
  · apply le_of_eq
    congr 1
    field_simp
