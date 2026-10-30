-- Prove2me | solution 1 for DerivativeChainContinuation.exists_first_eigenvector_basis
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:18:03.917776+00:00
-- url     : https://prove2.me/submissions/69a7c74e-edda-4a42-b060-3a45231ccde6

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


theorem solution (n : ℕ) (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    ∃ (μ : ℂ) (b : OrthonormalBasis (Fin (n+1)) ℂ (EuclideanSpace ℂ (Fin (n+1)))),
      A.toEuclideanLin (b 0) = μ • b 0 := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A.toEuclideanLin
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  let w := ((‖v‖⁻¹ : ℝ) : ℂ) • v
  have hwn : ‖w‖ = 1 := by
    simp [w, norm_smul, Complex.norm_real, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v),
      norm_ne_zero_iff.mpr hv0]
  have hw : A.toEuclideanLin w = μ • w := by
    calc
      A.toEuclideanLin w = ((‖v‖⁻¹ : ℝ) : ℂ) • A.toEuclideanLin v :=
        A.toEuclideanLin.map_smul _ _
      _ = μ • w := by rw [hv.apply_eq_smul]; exact smul_comm _ _ _
  have hon : Orthonormal ℂ (({0} : Set (Fin (n+1))).domRestrict (fun _ => w)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hwn
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ (Fin (n+1))) = Fintype.card (Fin (n+1)))
  refine ⟨μ, b, ?_⟩
  rw [hb 0 (by simp)]
  exact hw
