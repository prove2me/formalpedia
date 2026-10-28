-- Prove2me | solution 1 for FunctionalInequalities.Analysis.ae_weak_matrix_inverse_derivative_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:37:58.317314+00:00
-- url     : https://prove2.me/submissions/52ebf395-88ea-4b5a-aeb2-a60bdafb4ff1

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_congr_ae_readable
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_of_locally_bounded_readable
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_finsetSum_mul_readable
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_contDiff_readable

section
noncomputable section
open MeasureTheory
open scoped ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- Weak derivatives are unique almost everywhere. -/
theorem FunctionalInequalities.Analysis.HasWeakDerivAlong.ae_eq {f g₁ g₂ : E → ℝ} {v : E} (h₁ : HasWeakDerivAlong f g₁ v)
    (h₂ : HasWeakDerivAlong f g₂ v) : g₁ =ᵐ[(volume : Measure E)] g₂ := by
  apply ae_eq_of_integral_contDiff_smul_eq h₁.2.1 h₂.2.1
  intro ψ hψ hψc
  have hψ' : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have e₁ := h₁.2.2 ψ hψ' hψc
  have e₂ := h₂.2.2 ψ hψ' hψc
  have e : (∫ x, g₁ x * ψ x ∂(volume : Measure E)) =
      ∫ x, g₂ x * ψ x ∂(volume : Measure E) := by
    linarith
  simpa only [smul_eq_mul, mul_comm] using e
end
universe u
end
end

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology BigOperators
section WeakMatrixInverse
open MeasureTheory Set Matrix
open scoped ContDiff Topology
/-- The given weak derivatives of a locally bounded inverse pair satisfy the
inverse formula almost everywhere; no classical differentiability is assumed. -/
theorem solution {d m : ℕ}
    {A R DA DR : EuclideanSpace ℝ (Fin d) → Matrix (Fin m) (Fin m) ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hR : ∀ i j, FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => R x i j) (fun x => DR x i j) v)
    (hA_top : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => A x i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hR_top : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => R x i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hDR2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DR x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hRA : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), R x * A x = 1) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      DR x = -(R x * DA x * R x) := by
  classical
  have hentry (i j : Fin m) :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
        (DR x * A x + R x * DA x) i j = 0 := by
    have hp (a : Fin m) :=
      (hR i a).mul_of_locally_bounded_readable (hA a j)
        (hR_top i a) (hA_top a j) (hDR2 i a) (hDA2 a j)
    have hs :=
      FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetSum_mul_readable
        (Finset.univ : Finset (Fin m)) (fun _ => (1 : ℝ))
        (fun a _ => (hp a).1)
        (fun a _ => (hp a).2)
    have hw :
        FunctionalInequalities.Analysis.HasWeakDerivAlong
          (fun x => (R x * A x) i j)
          (fun x => (DR x * A x + R x * DA x) i j) v := by
      simpa only [one_mul, Matrix.mul_apply, Matrix.add_apply,
        Finset.sum_add_distrib] using hs.1
    have hc :
        FunctionalInequalities.Analysis.HasWeakDerivAlong
          (fun _ : EuclideanSpace ℝ (Fin d) =>
            (1 : Matrix (Fin m) (Fin m) ℝ) i j)
          (fun _ => (0 : ℝ)) v := by
      simpa using
        (FunctionalInequalities.Analysis.hasWeakDerivAlong_of_contDiff_readable
          (f := fun _ : EuclideanSpace ℝ (Fin d) =>
            (1 : Matrix (Fin m) (Fin m) ℝ) i j)
          contDiff_const v)
    have he :
        (fun x => (R x * A x) i j) =ᵐ[
          (volume : Measure (EuclideanSpace ℝ (Fin d)))]
        (fun _ => (1 : Matrix (Fin m) (Fin m) ℝ) i j) :=
      hRA.mono (fun _ hx => congrArg (fun B => B i j) hx)
    exact (hw.congr_ae_readable he Filter.EventuallyEq.rfl).ae_eq hc
  have hall :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
        ∀ i j, (DR x * A x + R x * DA x) i j = 0 :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hentry i j))
  filter_upwards [hRA, hall] with x hx hentries
  have hzero : DR x * A x + R x * DA x = 0 := by
    ext i j
    exact hentries i j
  have hAR : A x * R x = 1 := mul_eq_one_comm.mp hx
  apply eq_neg_of_add_eq_zero_left
  calc
    DR x + R x * DA x * R x =
        (DR x * A x + R x * DA x) * R x := by
      rw [add_mul, mul_assoc (DR x) (A x) (R x), hAR, mul_one]
    _ = 0 := by rw [hzero, zero_mul]
