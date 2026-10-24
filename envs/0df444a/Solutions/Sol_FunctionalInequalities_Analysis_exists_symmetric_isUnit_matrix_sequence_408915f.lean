-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_symmetric_isUnit_matrix_sequence_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:40:44.629606+00:00
-- url     : https://prove2.me/submissions/20e6ba8b-dceb-48a8-97aa-f3ac400906b5

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NoncommRing

noncomputable section
open scoped MatrixOrder
noncomputable section
open Matrix Filter Set
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
set_option maxHeartbeats 300000 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) :
    ∃ seq : ℕ → Matrix ι ι ℝ,
      (∀ k, (seq k).IsSymm ∧ IsUnit (seq k)) ∧ Tendsto seq atTop (𝓝 A) := by
  classical
  have hex (k : ℕ) : ∃ r : ℝ, r ∈ Set.Ioo 0 (1 / ((k : ℝ) + 1)) ∧ r ∉ spectrum ℝ A := by
    have he : 0 < 1 / ((k : ℝ) + 1) := by positivity
    exact ((Set.Ioo_infinite he).sdiff A.finite_real_spectrum).nonempty
  choose r hr using hex
  have hlim : Tendsto r atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun k => (hr k).1.1.le) (fun k => (hr k).1.2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun k => A - r k • (1 : Matrix ι ι ℝ), ?_, ?_⟩
  · intro k
    refine ⟨hA.sub (Matrix.isSymm_one.smul (r k)), ?_⟩
    simpa only [Algebra.algebraMap_eq_smul_one, neg_sub] using
      (spectrum.notMem_iff.mp (hr k).2).neg
  · simpa only [zero_smul, sub_zero] using
      (tendsto_const_nhds.sub (hlim.smul_const (1 : Matrix ι ι ℝ)))
