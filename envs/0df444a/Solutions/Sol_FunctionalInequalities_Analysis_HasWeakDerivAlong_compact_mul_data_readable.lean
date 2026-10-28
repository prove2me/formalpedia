-- Prove2me | solution 1 for FunctionalInequalities.Analysis.HasWeakDerivAlong.compact_mul_data_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:50.25698+00:00
-- url     : https://prove2.me/submissions/3125ab00-0d92-4467-acf6-08123829c5f3

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
import Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_contDiff_readable
import Theorems.Thm_FunctionalInequalities_Analysis_memLp_mul_of_hasCompactSupport_readable

noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section SharedCompactLocalTools
open MeasureTheory Set Filter
open scoped ContDiff RealInnerProductSpace Topology
/-- Multiplying a weak derivative pair `(f, df)` along `v` by a compactly supported C1 function `ψ`, with `df` L2 and
`f` essentially bounded on compact sets, gives the weak derivative of `ψ f`, compact supports and a globally L2 derivative. -/
theorem solution {n : ℕ}
    {f df : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (h : FunctionalInequalities.Analysis.HasWeakDerivAlong f df v)
    (hdf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => ψ x * f x)
      (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) v ∧
    HasCompactSupport (fun x => ψ x * f x) ∧
    HasCompactSupport (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) ∧
    MemLp (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hdψ : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdψc : HasCompactSupport (fun x => fderiv ℝ ψ x v) :=
    hψc.fderiv_apply ℝ v
  have hf2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
    intro S hS
    let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hf S hS).mono_exponent le_top
  refine ⟨h.mul_contDiff_readable hψ hψc, hψc.mul_right, ?_, ?_⟩
  · exact hψc.mul_right.add hdψc.mul_right
  · exact (FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_readable hψ.continuous hψc hdf).add (FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_readable hdψ hdψc hf2)
