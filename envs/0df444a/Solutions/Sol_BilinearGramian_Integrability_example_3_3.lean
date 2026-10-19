-- Prove2me | solution 1 for BilinearGramian.Integrability.example_3_3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-18T09:33:01.951084+00:00
-- url     : https://prove2.me/submissions/d38ba425-594a-407c-82f3-9f48db6cf279

import Theorems.Thm_BilinearGramian_Integrability_controllable
import Theorems.Thm_BilinearGramian_Integrability_jacobian_not_symm

open Matrix BilinearGramian.Integrability
open scoped Topology

private theorem gradient_matrix_symm
    (F : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (a : Fin 2 → ℝ) (E : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hF : HasFDerivAt F (Matrix.toLin' M).toContinuousLinearMap a)
    (hE : ∀ᶠ y in 𝓝 a, HasGradientAt E (WithLp.toLp 2 (F y)) (WithLp.toLp 2 y)) :
    M.IsSymm := by
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap
  let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] StrongDual ℝ (EuclideanSpace ℝ (Fin 2)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).toContinuousLinearEquiv.toContinuousLinearMap
  let R := (T.precomp ℝ).comp (D.comp T)
  have h1 : ∀ᶠ y in 𝓝 a, HasFDerivAt (fun z => E (T z)) (R (F y)) y := by
    filter_upwards [hE] with y hy
    exact hy.hasFDerivAt.comp y T.hasFDerivAt
  have h2 := R.hasFDerivAt.comp a hF
  have hs := second_derivative_symmetric_of_eventually h1 h2
  change Mᵀ = M
  ext i j
  have hh := hs (Pi.single i 1) (Pi.single j 1)
  simpa [R, D, T, ContinuousLinearMap.comp_apply, EuclideanSpace.inner_toLp_toLp,
    EuclideanSpace.inner_single_right,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Pi.single_apply, Matrix.transpose_apply] using hh

theorem solution (ν : ℝ) (hν : ν ≠ 0) (Pt : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (hPt : ∀ x, IsLinGramian exA (fun _ : Fin 1 => exN ν) exB x (Pt x)) :
    IsControllable exA exB ∧
      ∀ ε > 0, ¬ ∃ E : EuclideanSpace ℝ (Fin 2) → ℝ,
        ∀ x : EuclideanSpace ℝ (Fin 2), 0 < ‖x‖ → ‖x‖ < ε →
          HasGradientAt E (WithLp.toLp 2 ((Pt x.ofLp)⁻¹ *ᵥ x.ofLp)) x := by
  refine ⟨controllable, ?_⟩
  intro ε hε ⟨E, hE⟩
  have hc : Continuous (fun ξ : ℝ => ‖WithLp.toLp 2 (ξ • (![1, 1] : Fin 2 → ℝ))‖) := by
    fun_prop
  have hn : ∀ᶠ ξ : ℝ in 𝓝 0,
      ‖WithLp.toLp 2 (ξ • (![1, 1] : Fin 2 → ℝ))‖ < ε :=
    hc.continuousAt.eventually (gt_mem_nhds (by simpa using hε))
  have hz : ∀ᶠ ξ : ℝ in 𝓝 0, 1 + ν * ξ ≠ 0 :=
    (show ContinuousAt (fun ξ : ℝ => 1 + ν * ξ) 0 by fun_prop).eventually_ne (by norm_num)
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp (hn.and hz)
  let ξ := δ / 2
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hb := hd (show ξ ∈ Metric.ball (0 : ℝ) δ by
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hξ]
    dsimp [ξ]; linarith)
  have hj := jacobian_not_symm ν ξ (mul_ne_zero hν (ne_of_gt hξ)) hb.2 Pt hPt
  apply hj.2
  apply gradient_matrix_symm _ _ _ E hj.1
  have hnonzero : WithLp.toLp 2 (ξ • (![1, 1] : Fin 2 → ℝ)) ≠ 0 := by
    intro h
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h
    exact (ne_of_gt hξ) (by simpa using hh)
  have hnorm : 0 < ‖WithLp.toLp 2 (ξ • (![1, 1] : Fin 2 → ℝ))‖ := norm_pos_iff.mpr hnonzero
  have hc' : Continuous (fun y : Fin 2 → ℝ => ‖WithLp.toLp 2 y‖) := by fun_prop
  have hevent : ∀ᶠ y in 𝓝 (ξ • (![1, 1] : Fin 2 → ℝ)),
      0 < ‖WithLp.toLp 2 y‖ ∧ ‖WithLp.toLp 2 y‖ < ε :=
    (hc'.continuousAt.eventually (lt_mem_nhds hnorm)).and
      (hc'.continuousAt.eventually (gt_mem_nhds hb.1))
  filter_upwards [hevent] with y hy
  exact hE (WithLp.toLp 2 y) hy.1 hy.2

#print axioms solution
