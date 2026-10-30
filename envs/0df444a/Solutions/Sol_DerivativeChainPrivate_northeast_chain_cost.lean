-- Prove2me | solution 1 for DerivativeChainPrivate.northeast_chain_cost
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T02:43:20.973978+00:00
-- url     : https://prove2.me/submissions/dee778cd-3ec5-4fdb-8502-04ecefb41a77

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate







theorem chainCost_eq_sum_range {n : ℕ} (f : ℕ → ℂ) :
    chainCost (fun i : Fin n => f i.val) =
      ∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖ := by
  unfold chainCost
  exact Fin.sum_univ_eq_sum_range (fun i => ‖f (i + 1) - f i‖) (n - 1)





end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



open DerivativeChainPrivate in
theorem solution (n : ℕ) (z : ℕ → ℂ)
    (hre : ∀ i < n - 1, (z i).re ≤ (z (i + 1)).re)
    (him : ∀ i < n - 1, (z i).im ≤ (z (i + 1)).im) :
    chainCost (fun i : Fin n => z i.val) ≤
      Real.sqrt 2 * ‖z (n - 1) - z 0‖ := by
  have hstep (i : ℕ) (hi : i < n - 1) :
      ‖z (i + 1) - z i‖ ≤
        ((z (i + 1)).re - (z i).re) + ((z (i + 1)).im - (z i).im) := by
    simpa only [Complex.sub_re, Complex.sub_im,
      abs_of_nonneg (sub_nonneg.mpr (hre i hi)),
      abs_of_nonneg (sub_nonneg.mpr (him i hi))] using
      Complex.norm_le_abs_re_add_abs_im (z (i + 1) - z i)
  have hsum : chainCost (fun i : Fin n => z i.val) ≤
      ((z (n - 1)).re - (z 0).re) + ((z (n - 1)).im - (z 0).im) := by
    rw [chainCost_eq_sum_range]
    calc
      _ ≤ ∑ i ∈ Finset.range (n - 1),
          (((z (i + 1)).re - (z i).re) + ((z (i + 1)).im - (z i).im)) :=
        Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)
      _ = _ := by rw [Finset.sum_add_distrib,
          Finset.sum_range_sub (fun i => (z i).re),
          Finset.sum_range_sub (fun i => (z i).im)]
  apply hsum.trans
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Complex.sq_norm (z (n - 1) - z 0)
  have hdiff := sq_nonneg (((z (n - 1)).re - (z 0).re) -
    ((z (n - 1)).im - (z 0).im))
  rw [Complex.normSq_apply] at hn
  simp only [Complex.sub_re, Complex.sub_im] at hn
  have hp := mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg (z (n - 1) - z 0))
  nlinarith only [hs, hn, hdiff, hp]
