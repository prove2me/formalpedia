-- Prove2me | solution 1 for Formalism.LogFactorialMertensBounds.sum_log_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:26.163581+00:00
-- url     : https://prove2.me/submissions/f4caa408-6ffc-47d9-817e-e68d31e515a4

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
noncomputable section
open Formalism
open Formalism.LogFactorialMertensBounds
namespace Formalism.LogFactorialMertensBounds
theorem _root_.solution (k : ℕ) :
    ∑ n ∈ Finset.Ioc 0 k, Real.log n = ∑ n ∈ Finset.Ioc 0 k, Λ n * ((k / n : ℕ) : ℝ) := by
  have h1 : ∀ n ∈ Finset.Ioc 0 k, Real.log n = ∑ d ∈ n.divisors, Λ d :=
    fun n _ => ArithmeticFunction.vonMangoldt_sum.symm
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := Finset.Ioc 0 k) (s' := fun d => (Finset.Ioc 0 k).filter (d ∣ ·))]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]
  · intro n d
    simp only [Finset.mem_Ioc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h0, hk⟩, hd, -⟩
      have hle := Nat.le_of_dvd h0 hd
      have hpos := Nat.pos_of_dvd_of_pos hd h0
      exact ⟨⟨⟨h0, hk⟩, hd⟩, hpos, by omega⟩
    · rintro ⟨⟨⟨h0, hk⟩, hd⟩, -, -⟩
      exact ⟨⟨h0, hk⟩, hd, by omega⟩
end Formalism.LogFactorialMertensBounds
