-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.Dec.of_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:41.562966+00:00
-- url     : https://prove2.me/submissions/5ee739f9-c968-4a59-a2f3-ad70e1329d12

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.CholeskyDecomposition
open Matrix
open scoped ComplexOrder MatrixOrder
variable {n : ℕ}
variable {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ}
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
namespace Dec
theorem _root_.solution {H V : Matrix (Fin n) (Fin n) ℂ} (hV : Vᴴ * V = 1) (h : Dec (Vᴴ * H * V)) : Dec H := by
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.1 hV
  have c1 : ∀ X : Matrix (Fin n) (Fin n) ℂ, Vᴴ * (V * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  have c2 : ∀ X : Matrix (Fin n) (Fin n) ℂ, V * (Vᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hV', Matrix.one_mul]
  have hVu : V ∈ Matrix.unitaryGroup (Fin n) ℂ := mem_unitaryGroup_iff'.2 hV
  have hVu' : Vᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := Unitary.star_mem hVu
  have back : ∀ x : Matrix (Fin n) (Fin n) ℂ, xᴴ * (Vᴴ * H * V) * x = Vᴴ * H * V →
      (V * x * Vᴴ)ᴴ * H * (V * x * Vᴴ) = H := by
    intro x hx
    calc (V * x * Vᴴ)ᴴ * H * (V * x * Vᴴ) = V * (xᴴ * (Vᴴ * H * V) * x) * Vᴴ := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = H := by rw [hx]; simp only [Matrix.mul_assoc, c2, hV', Matrix.mul_one]
  obtain ⟨U, hU, h⟩ := h
  refine ⟨V * U, mul_mem hVu hU, fun g hg => ?_⟩
  obtain ⟨k, hk, s, hkH, hsH, hks, hs⟩ := h (Vᴴ * g * V) (by
    calc (Vᴴ * g * V)ᴴ * (Vᴴ * H * V) * (Vᴴ * g * V) = Vᴴ * (gᴴ * H * g) * V := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, c2]
      _ = _ := by rw [hg])
  refine ⟨V * k * Vᴴ, mul_mem (mul_mem hVu hk) hVu', V * s * Vᴴ, back k hkH, back s hsH, ?_, ?_⟩
  · calc g = V * (Vᴴ * g * V) * Vᴴ := by simp only [Matrix.mul_assoc, c2, hV', Matrix.mul_one]
      _ = _ := by rw [hks]; simp only [Matrix.mul_assoc, c1]
  · have : (V * U)ᴴ * (V * s * Vᴴ) * (V * U) = Uᴴ * s * U := by
      simp only [conjTranspose_mul, Matrix.mul_assoc, c1]
    rw [this]; exact hs
end Dec
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
