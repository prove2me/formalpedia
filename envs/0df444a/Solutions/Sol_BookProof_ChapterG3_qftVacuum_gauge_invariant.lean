-- Prove2me | solution 1 for BookProof.ChapterG3.qftVacuum_gauge_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T13:41:09.733804+00:00
-- url     : https://prove2.me/submissions/5ccd559b-b256-46e2-af80-17cd0a9ece8c

-- Generated from ChapterG3.lean — solution of BookProof.ChapterG3.qftVacuum_gauge_invariant
import Mathlib
import Definitions.Def_ChapterG3
open BookProof.ChapterG3
open BookProof.ChapterG3.PhysHSGaussian



open MeasureTheory
open scoped ENNReal



variable {X : Type*}

variable {X : Type*}


/-! gaussianE_rotation_invariant: inlined from `BookProof/PhysHSGaussian/Part1.lean`, because the
published `Def_ChapterG3` bundle carries only `gaussianE` itself. -/

open MeasureTheory Set Filter ProbabilityTheory

instance PhysHSGaussian.gaussianE_isProbability (k : ℕ) : IsProbabilityMeasure (gaussianE k) := by
  constructor ; norm_num [ gaussianE ];
  rw [ Measure.map_apply ] <;> norm_num;
  exact MeasurableEquiv.measurable _

/-
The standard Gaussian on Euclidean space is invariant under linear isometries.
-/
theorem PhysHSGaussian.gaussianE_rotation_invariant (k : ℕ)
    (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    (gaussianE k).map L = gaussianE k := by
  apply MeasureTheory.Measure.ext_of_charFun;
  -- By definition of $gaussianE$, we know that its characteristic function is given by
  -- $\exp(-\|t\|^2 / 2)$.
  have h_char_gaussian : ∀ t : EuclideanSpace ℝ (Fin k), charFun (gaussianE k) t = Complex.exp
    (-‖t‖^2 / 2) := by
    intro t
    unfold gaussianE;
    rw [ charFun ];
    rw [ MeasureTheory.integral_map ];
    · -- The integral of the exponential of the inner product factors as the product of the
      -- componentwise integrals.
      have h_prod : ∫ x : Fin k → ℝ, Complex.exp (Complex.I * ∑ i, x i * t i) ∂Measure.pi (fun _ =>
        ProbabilityTheory.gaussianReal 0 1) = ∏ i, ∫ x : ℝ, Complex.exp (Complex.I * x * t i)
        ∂ProbabilityTheory.gaussianReal 0 1 := by
        have h_prod : ∀ (f : Fin k → ℝ → ℂ), (∫ x : Fin k → ℝ, ∏ i, f i (x i) ∂Measure.pi (fun _ =>
          ProbabilityTheory.gaussianReal 0 1)) = ∏ i, ∫ x : ℝ, f i x ∂ProbabilityTheory.gaussianReal
          0 1 := by
          intro f;
          rw [ ← MeasureTheory.integral_fintype_prod_eq_prod ];
        convert h_prod ( fun i x => Complex.exp ( Complex.I * x * t i ) ) using 3
        norm_num [ Complex.exp_sum, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]
      -- The integral of the exponential of the inner product is the product of the integrals of the
      -- exponentials of the components, which is the characteristic function of the Gaussian
      -- measure.
      have h_char : ∀ i : Fin k, ∫ x : ℝ, Complex.exp (Complex.I * x * t i)
        ∂ProbabilityTheory.gaussianReal 0 1 = Complex.exp (-t i ^ 2 / 2) := by
        intro i;
        have := @ProbabilityTheory.charFun_gaussianReal 0 1 ( t i );
        convert this using 1 <;> norm_num [ charFun ]
        · ring_nf
          ac_rfl
        · ring
      convert h_prod using 1;
      · norm_num [ mul_comm, inner ];
      · simp_all? +decide [ EuclideanSpace.norm_eq ];
        norm_cast
        norm_num [ ← Finset.sum_div _ _ _, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _
          ]
        rw [ ← Real.exp_sum ] ; norm_num [ neg_div, Finset.sum_div _ _ _ ];
    · exact Measurable.aemeasurable ( by exact MeasurableEquiv.measurable _ );
    · fun_prop;
  ext t; simp? +decide [ charFun ] ; ring;
  rw [ MeasureTheory.integral_map ];
  · -- Since $L$ is a linear isometry, we have
    -- $\langle L(x), t \rangle = \langle x, L^{-1}(t) \rangle$.
    have h_inner : ∀ x : EuclideanSpace ℝ (Fin k), inner ℝ (L x) t = inner ℝ x (L.symm t) := by
      intro x; exact (by
      rw [ ← L.inner_map_map x ( L.symm t ), L.apply_symm_apply ]);
    have := h_char_gaussian ( L.symm t ) ; simp_all +decide [ charFun ] ;
  · exact L.continuous.aemeasurable;
  · fun_prop (disch := norm_num)

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ)
    (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    (qftVacuum k).map L = qftVacuum k := PhysHSGaussian.gaussianE_rotation_invariant k L
