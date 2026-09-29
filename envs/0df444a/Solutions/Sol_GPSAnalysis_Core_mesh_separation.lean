-- Prove2me | solution 1 for GPSAnalysis.Core.mesh_separation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:24:49.754835+00:00
-- url     : https://prove2.me/submissions/f794b88b-d86d-4cc9-97aa-d84b441b3e8a

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Mesh

open Matrix

namespace GPSAnalysis.Core

theorem aux_msep_cast {n p : ℕ} (Zbar : Matrix (Fin n) (Fin p) ℤ) (z : Fin p → ℤ) :
    (fun i => ((Zbar *ᵥ z) i : ℝ)) = Zbar.map (fun t : ℤ => (t : ℝ)) *ᵥ (fun j => (z j : ℝ)) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

end GPSAnalysis.Core

open GPSAnalysis.Core
open Matrix

theorem solution {n p : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : IsUnit G.det)
    (Zbar : Matrix (Fin n) (Fin p) ℤ) (xk : Fin n → ℝ) (Δk : ℝ) (hΔk : 0 < Δk)
    (N : AddGroupNorm (Fin n → ℝ)) (hN_smul : ∀ (a : ℝ) (v : Fin n → ℝ), N (a • v) = |a| * N v)
    (hN_int : ∀ z : Fin n → ℤ, z ≠ 0 → 1 ≤ N (fun i => (z i : ℝ)))
    (c : ℝ) (hc : ∀ v : Fin n → ℝ, N (G⁻¹ *ᵥ v) ≤ c * N v) :
    ∀ u ∈ mesh (dirMatrix G Zbar) xk Δk, ∀ v ∈ mesh (dirMatrix G Zbar) xk Δk,
      u ≠ v → Δk / c ≤ N (u - v) := by
  intro u hu v hv huv
  obtain ⟨z1, rfl⟩ := hu
  obtain ⟨z2, rfl⟩ := hv
  set Zr := Zbar.map (fun t : ℤ => (t : ℝ)) with hZr
  set w : Fin n → ℤ := Zbar *ᵥ (fun j => (z1 j : ℤ) - (z2 j : ℤ)) with hw
  have hwcast : (fun i => (w i : ℝ)) = Zr *ᵥ ((fun j => (z1 j : ℝ)) - (fun j => (z2 j : ℝ))) := by
    rw [hw, aux_msep_cast]
    congr 1
    funext j
    simp
  have hdiff : (xk + Δk • (dirMatrix G Zbar *ᵥ fun j => (z1 j : ℝ))) -
      (xk + Δk • (dirMatrix G Zbar *ᵥ fun j => (z2 j : ℝ))) =
      Δk • (G *ᵥ (fun i => (w i : ℝ))) := by
    rw [hwcast, Matrix.mulVec_mulVec, dirMatrix, Matrix.mulVec_sub]
    rw [← hZr]
    simp [smul_sub]
  have hinv : G⁻¹ *ᵥ (Δk • (G *ᵥ (fun i => (w i : ℝ)))) = Δk • (fun i => (w i : ℝ)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hG, Matrix.one_mulVec]
  have hw0 : w ≠ 0 := by
    intro h0
    apply huv
    rw [← sub_eq_zero, hdiff]
    have : (fun i => (w i : ℝ)) = 0 := by
      funext i; simp [h0]
    rw [this]; simp
  have h1 := hN_int w hw0
  have key : Δk ≤ c * N (Δk • (G *ᵥ (fun i => (w i : ℝ)))) := by
    have := hc (Δk • (G *ᵥ (fun i => (w i : ℝ))))
    rw [hinv, hN_smul, abs_of_pos hΔk] at this
    nlinarith
  rw [hdiff]
  have hNnn : 0 ≤ N (Δk • (G *ᵥ (fun i => (w i : ℝ)))) := apply_nonneg N _
  have hcpos : 0 < c := by
    by_contra hcn
    rw [not_lt] at hcn
    nlinarith
  rw [div_le_iff₀ hcpos]
  linarith
