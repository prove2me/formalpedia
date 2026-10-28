-- Prove2me | solution 1 for CountingMatroid.Analysis.CubicTensorRayleighContraction.cubic_tensor_rayleigh_contraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:09:26.208429+00:00
-- url     : https://prove2.me/submissions/76608031-0587-4012-ae57-876526d36a07

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_CountingMatroid_Analysis_ConnectedRayleighHyperplane_connected_rayleigh_hyperplane
import Theorems.Thm_CountingMatroid_Analysis_NonnegativeContractionLimit_nonnegative_contraction_limit

namespace CountingMatroid.Analysis.CubicTensorRayleighContraction
end CountingMatroid.Analysis.CubicTensorRayleighContraction
namespace CountingMatroid.Analysis.NonnegativeContractionLimit
end CountingMatroid.Analysis.NonnegativeContractionLimit
namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
namespace CountingMatroid.Analysis.ConnectedRayleighHyperplane
end CountingMatroid.Analysis.ConnectedRayleighHyperplane
namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane
end CountingMatroid.Analysis.QuadraticSignatureHyperplane
set_option autoImplicit false

/-!
The analytic local-to-global step for a symmetric nonnegative cubic tensor.
Its combinatorial input is expressed as connectivity across every cut of
active coordinates, independently of the exchange-support proof. Positive
contractions inherit this connectivity, and the slice reverse inequalities
supply the divided Rayleigh bound for the connected spectral theorem.
The contraction-limit theorem extends the result to zero coordinates.
-/

namespace CountingMatroid.Analysis.CubicTensorRayleighContraction
end CountingMatroid.Analysis.CubicTensorRayleighContraction
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CubicTensorRayleighContraction

open scoped BigOperators
open QuadraticNonpositiveHyperplane

/-- INTERNAL: The spectral part of cubic contraction closure. A nonnegative
symmetric tensor with connected active support and the slice reverse
Cauchy–Schwarz inequalities has at most one positive contraction direction.
The cut hypothesis replaces exchange support only after the parent proves
it from that support. It is not an assumption added to the paper's claim.
TEXLINE: main.tex:340-347 -/
theorem solution {σ : Type} [Fintype σ] [DecidableEq σ]
    [Invertible (2 : ℝ)]
    (T : σ → σ → σ → ℚ) (hT : ∀ s i j, 0 ≤ T s i j)
    (hswap : ∀ s i j, T s i j = T i s j)
    (hlast : ∀ s i j, T s i j = T s j i)
    (hcross : ∀ U : Set σ,
      (∃ s i j, T s i j ≠ 0 ∧ s ∈ U) →
      (∃ s i j, T s i j ≠ 0 ∧ s ∉ U) →
      ∃ s i j, T s i j ≠ 0 ∧ i ∈ U ∧ j ∉ U)
    (hreverse : ∀ (s : σ) (e v : σ → ℝ),
      0 < Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ)) e →
      Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ)) v *
        Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ)) e ≤
      ((Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))).associated e v) ^ 2)
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    HasNonpositiveHyperplane (∑ s, (d s : ℝ) •
      Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))) := by
  classical
  let Q (s : σ) := Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))
  apply NonnegativeContractionLimit.nonnegative_contraction_limit Q _ d hd
  intro w hw
  let A : Matrix σ σ ℝ := fun i j => ∑ s, (w s : ℝ) * (T s i j : ℝ)
  have hA : ∀ i j, 0 ≤ A i j := by
    intro i j
    exact Finset.sum_nonneg (fun s _ =>
      mul_nonneg (by exact_mod_cast (hw s).le) (by exact_mod_cast hT s i j))
  have hsym : ∀ i j, A i j = A j i := by
    intro i j
    simp only [A, hlast]
  have hsupport (i j : σ) : A i j ≠ 0 ↔ ∃ s, T s i j ≠ 0 := by
    constructor
    · intro hij
      obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
      refine ⟨s, ?_⟩
      intro ht
      apply hs
      simp [ht]
    · rintro ⟨s, hs⟩
      have hp : 0 < (w s : ℝ) * (T s i j : ℝ) :=
        mul_pos (by exact_mod_cast hw s)
          (by exact_mod_cast lt_of_le_of_ne (hT s i j) (Ne.symm hs))
      exact ne_of_gt (hp.trans_le (Finset.single_le_sum
        (fun t _ => show 0 ≤ (w t : ℝ) * (T t i j : ℝ) from
          mul_nonneg (by exact_mod_cast (hw t).le) (by exact_mod_cast hT t i j)) (Finset.mem_univ s)))
  have hquad (M : Matrix σ σ ℝ) (v : σ → ℝ) :
      M.toQuadraticForm' v = ∑ i, ∑ j, v i * (v j * M i j) := by
    rw [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply]
    simp only [smul_eq_mul]
  have hQapply (s : σ) (v : σ → ℝ) :
      Q s v = ∑ i, ∑ j, v i * (v j * (T s i j : ℝ)) :=
    hquad (fun i j => (T s i j : ℝ)) v
  have heq : Matrix.toQuadraticForm' A = ∑ s, (w s : ℝ) • Q s := by
    ext v
    simp only [sum_apply, smul_apply, smul_eq_mul]
    rw [hquad]
    simp only [hQapply, A]
    simp only [Finset.mul_sum]
    conv_lhs =>
      enter [2, i]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← heq]
  refine ConnectedRayleighHyperplane.connected_rayleigh_hyperplane A hA hsym
    ?_ (fun s => (w s : ℝ)) (fun s => by exact_mod_cast hw s) ?_
  · intro U hin hout
    have hinside : ∃ s i j, T s i j ≠ 0 ∧ s ∈ U := by
      obtain ⟨i, j, hij, hi⟩ := hin
      obtain ⟨s, hs⟩ := (hsupport i j).mp hij
      exact ⟨i, s, j, by rwa [hswap i s j], hi⟩
    have houtside : ∃ s i j, T s i j ≠ 0 ∧ s ∉ U := by
      obtain ⟨i, j, hij, hi⟩ := hout
      obtain ⟨s, hs⟩ := (hsupport i j).mp hij
      exact ⟨i, s, j, by rwa [hswap i s j], hi⟩
    obtain ⟨s, i, j, hs, hi, hj⟩ := hcross U hinside houtside
    exact ⟨i, j, (hsupport i j).mpr ⟨s, hs⟩, hi, hj⟩
  · intro v
    let e : σ → ℝ := fun i => (w i : ℝ)
    have he (i : σ) : 0 < e i := by
      change 0 < (w i : ℝ)
      exact_mod_cast hw i
    let B (s : σ) : LinearMap.BilinMap ℝ (σ → ℝ) ℝ := Matrix.toLinearMap₂' ℝ (fun i j => (T s i j : ℝ))
    have hBapply (s : σ) (u v : σ → ℝ) :
        B s u v = ∑ i, ∑ j, u i * (v j * (T s i j : ℝ)) := by
      simpa only [smul_eq_mul] using
        (Matrix.toLinearMap₂'_apply (R := ℝ) (fun i j => (T s i j : ℝ)) u v)
    have hBsym (s : σ) (u v : σ → ℝ) : B s u v = B s v u := by
      rw [hBapply, hBapply, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hlast s j i]
      ring
    have hassociated (s : σ) (u v : σ → ℝ) :
        (Q s).associated u v = B s u v := by
      change (QuadraticMap.associatedHom ℝ (B s).toQuadraticMap) u v = B s u v
      rw [QuadraticMap.associated_left_inverse ℝ (hBsym s)]
    have hBe (s : σ) (v : σ → ℝ) : B s e v = A.mulVec v s := by
      rw [hBapply]
      change (∑ i, ∑ j, e i * (v j * (T s i j : ℝ))) =
        ∑ j, (∑ i, e i * (T i s j : ℝ)) * v j
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hswap s i j]
      ring
    have hQe (s : σ) : Q s e = A.mulVec e s := by
      rw [← hBe s e]
      exact (QuadraticMap.associated_eq_self_apply ℝ (Q s) e).symm.trans
        (hassociated s e e)

    have hslice (s : σ) : Q s v ≤ (A.mulVec v s) ^ 2 / A.mulVec e s := by
      have hn : 0 ≤ Q s e := by
        rw [hQapply]
        exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
          mul_nonneg (he i).le (mul_nonneg (he j).le (by exact_mod_cast hT s i j))))
      by_cases hp : 0 < Q s e
      · rw [← hQe s, le_div_iff₀ hp]
        have hr : Q s v * Q s e ≤ ((Q s).associated e v) ^ 2 := hreverse s e v hp
        rwa [hassociated, hBe] at hr
      · have hz : Q s e = 0 := le_antisymm (le_of_not_gt hp) hn
        have hsum : (∑ i, ∑ j, e i * (e j * (T s i j : ℝ))) = 0 := by
          rw [← hQapply, hz]
        have hzero (i j : σ) : (T s i j : ℝ) = 0 := by
          have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
            Finset.sum_nonneg (fun j _ => mul_nonneg (he i).le
              (mul_nonneg (he j).le (by exact_mod_cast hT s i j))))).mp hsum
            i (Finset.mem_univ i)
          have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
            mul_nonneg (he i).le
              (mul_nonneg (he j).le (by exact_mod_cast hT s i j)))).mp hi
            j (Finset.mem_univ j)
          simpa only [mul_eq_zero, (he i).ne', (he j).ne', false_or] using hij
        have hvzero : Q s v = 0 := by
          simp only [hQapply, hzero, mul_zero, Finset.sum_const_zero]
        rw [hvzero, ← hQe s, hz]
        simp
    rw [heq]
    simp only [sum_apply, smul_apply, smul_eq_mul]
    change (∑ s, e s * Q s v) ≤ ∑ s, e s * (A.mulVec v s) ^ 2 / A.mulVec e s
    apply Finset.sum_le_sum
    intro s _
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hslice s) (he s).le
