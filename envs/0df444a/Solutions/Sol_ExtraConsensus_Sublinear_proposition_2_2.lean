-- Prove2me | solution 1 for ExtraConsensus.Sublinear.proposition_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:05:17.560351+00:00
-- url     : https://prove2.me/submissions/0eb0902e-b263-42a8-912f-0b892bbdedf7

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

open Matrix Filter Topology Asymptotics

open ExtraConsensus.Sublinear in
theorem solution {n : ℕ} (W Wt : Matrix (Fin n) (Fin n) ℝ)
    (hWs : Wᵀ = W) (hWts : Wtᵀ = Wt)
    (hnull : ∀ v : Fin n → ℝ, (W - Wt) *ᵥ v = 0 ↔ ∃ c : ℝ, v = fun _ => c)
    (hnull1 : (1 - Wt) *ᵥ (fun _ => (1 : ℝ)) = 0)
    (hpd : Wt.PosDef) (hpsd1 : ((1 / 2 : ℝ) • (1 + W) - Wt).PosSemidef)
    (hpsd2 : (Wt - W).PosSemidef) :
    (∀ v : Fin n → ℝ, (1 - W) *ᵥ v = 0 ↔ ∃ c : ℝ, v = fun _ => c) ∧
      ∀ μ, IsEigenvalue W μ → -1 < μ ∧ μ ≤ 1 := by
  set A := (1 / 2 : ℝ) • (1 + W) - Wt with hA
  set B := Wt - W with hB
  have hsplit : 1 - W = (2 : ℝ) • A + (2 : ℝ) • B := by
    ext i j
    simp only [hA, hB, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have qA : ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v) := by
    intro v; have := hpsd1.dotProduct_mulVec_nonneg v; rwa [star_trivial] at this
  have qB : ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (B *ᵥ v) := by
    intro v; have := hpsd2.dotProduct_mulVec_nonneg v; rwa [star_trivial] at this
  have hq : ∀ v : Fin n → ℝ, v ⬝ᵥ ((1 - W) *ᵥ v) = 2 * (v ⬝ᵥ (A *ᵥ v)) + 2 * (v ⬝ᵥ (B *ᵥ v)) := by
    intro v
    rw [hsplit, add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
  constructor
  · intro v
    constructor
    · intro h
      have h0 : v ⬝ᵥ ((1 - W) *ᵥ v) = 0 := by rw [h, dotProduct_zero]
      rw [hq] at h0
      have hB0 : v ⬝ᵥ (B *ᵥ v) = 0 := by linarith [qA v, qB v]
      have hBv : B *ᵥ v = 0 := by
        have := (hpsd2.dotProduct_mulVec_zero_iff v).mp
        rw [star_trivial] at this
        exact this hB0
      apply (hnull v).mp
      have : W - Wt = -B := by rw [hB, neg_sub]
      rw [this, neg_mulVec, hBv, neg_zero]
    · rintro ⟨c, rfl⟩
      have h1 : (W - Wt) *ᵥ (fun _ => (1 : ℝ)) = 0 := (hnull _).mpr ⟨1, rfl⟩
      have hc : (fun _ : Fin n => c) = c • (fun _ : Fin n => (1 : ℝ)) := by
        funext i; simp
      have e : (1 : Matrix (Fin n) (Fin n) ℝ) - W = (1 - Wt) - (W - Wt) := by abel
      rw [hc, mulVec_smul, e, sub_mulVec, hnull1, h1, sub_zero, smul_zero]
  · rintro μ ⟨v, hv, hWv⟩
    have hvv : 0 < v ⬝ᵥ v := by
      have := (Matrix.dotProduct_star_self_pos_iff (v := v)).mpr hv
      rwa [star_trivial] at this
    have hWt : 0 < v ⬝ᵥ (Wt *ᵥ v) := by
      have := hpd.dotProduct_mulVec_pos hv
      rwa [star_trivial] at this
    constructor
    · have h := qA v
      have e : v ⬝ᵥ (A *ᵥ v) = (1 / 2) * (v ⬝ᵥ v + μ * (v ⬝ᵥ v)) - v ⬝ᵥ (Wt *ᵥ v) := by
        rw [hA, sub_mulVec, smul_mulVec, add_mulVec, one_mulVec, hWv, dotProduct_sub,
          dotProduct_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      rw [e] at h
      nlinarith
    · have h : 0 ≤ v ⬝ᵥ ((1 - W) *ᵥ v) := by rw [hq]; linarith [qA v, qB v]
      have e : v ⬝ᵥ ((1 - W) *ᵥ v) = v ⬝ᵥ v - μ * (v ⬝ᵥ v) := by
        rw [sub_mulVec, one_mulVec, hWv, dotProduct_sub, dotProduct_smul, smul_eq_mul]
      rw [e] at h
      nlinarith
