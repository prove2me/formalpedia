-- Prove2me | solution 1 for CompactOperators.exists_positive_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:20:53.637132+00:00
-- url     : https://prove2.me/submissions/67fe7787-f8b5-49bf-b709-6f58e6fd3d11

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Lp.lpHolder

universe u v

theorem solution {𝕜 : Type v} [RCLike 𝕜] {ι : Type u}
    (d : ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (hd₀ : ∀ i, 0 ≤ d i) (hdK : ∀ i, d i ≤ K) :
    ∃ D : lp (fun _ : ι => 𝕜) 2 →L[𝕜] lp (fun _ : ι => 𝕜) 2,
      D.IsPositive ∧ ∀ x i, D x i = (d i : 𝕜) * x i := by
  classical
  let S : lp (fun _ : ι => 𝕜) 2 →L[𝕜] lp (fun _ : ι => 𝕜) 2 :=
    lp.mapCLM 2 (fun i => ContinuousLinearMap.lsmul 𝕜 𝕜 ((Real.sqrt (d i) : ℝ) : 𝕜))
      (Real.sqrt_nonneg K) (fun i => by
        calc
          _ ≤ ‖((Real.sqrt (d i) : ℝ) : 𝕜)‖ := ContinuousLinearMap.opNorm_lsmul_apply_le _
          _ = Real.sqrt (d i) := by simp [Real.sqrt_nonneg]
          _ ≤ Real.sqrt K := Real.sqrt_le_sqrt (hdK i))
  have hS (x : lp (fun _ : ι => 𝕜) 2) (i : ι) :
      S x i = (Real.sqrt (d i) : 𝕜) * x i := by
    simp [S]
  have hsingle (i : ι) : S (lp.single 2 i (1 : 𝕜)) =
      Real.sqrt (d i) • lp.single 2 i (1 : 𝕜) := by
    ext j
    by_cases h : j = i
    · subst j; simp [hS, RCLike.real_smul_eq_coe_mul]
    · simp [hS, lp.single_apply, h]
  refine ⟨S.adjoint.comp S, ContinuousLinearMap.isPositive_adjoint_comp_self S, ?_⟩
  intro x i
  have hh := ContinuousLinearMap.adjoint_inner_right S (lp.single 2 i (1 : 𝕜)) (S x)
  rw [hsingle, RCLike.real_smul_eq_coe_smul (K := 𝕜), inner_smul_left,
    lp.inner_single_left, lp.inner_single_left] at hh
  simp only [RCLike.inner_apply, map_one, one_mul, hS, RCLike.conj_ofReal] at hh
  have hs : (Real.sqrt (d i) : 𝕜) * (Real.sqrt (d i) : 𝕜) = (d i : 𝕜) := by
    rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hd₀ i)]
  simpa [ContinuousLinearMap.comp_apply, ← mul_assoc, hs] using hh
