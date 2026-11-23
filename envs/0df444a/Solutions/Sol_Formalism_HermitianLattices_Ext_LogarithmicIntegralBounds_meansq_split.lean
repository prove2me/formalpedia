-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.meansq_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:27.513942+00:00
-- url     : https://prove2.me/submissions/613d458f-54c4-4bde-993a-a18437d315fd

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMainB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (r : ℕ → ℕ → ℕ) (A : ℕ → ℕ → ℝ)
    (P η : ℝ) (hP : 0 ≤ P) (hη : 0 ≤ η) (nstar : ℕ)
    (hA : ∀ n ∈ I, ∀ n' ∈ I, A n n' ≤ P)
    (hA' : ∀ n ∈ I, ∀ n' ∈ I, r n n' ≠ 1 → r n n' ≠ nstar → A n n' ≤ η * P) :
    ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * A n n' ≤
      ((∑ n ∈ I, ∑ n' ∈ I, if r n n' = 1 then c n * c n' else 0) +
        (∑ n ∈ I, ∑ n' ∈ I, if r n n' = nstar then c n * c n' else 0) + η * (∑ n ∈ I, c n) ^ 2) * P := by
  have hpt : ∀ n ∈ I, ∀ n' ∈ I, c n * c n' * A n n' ≤
      ((if r n n' = 1 then c n * c n' else 0) + (if r n n' = nstar then c n * c n' else 0) +
        η * (c n * c n')) * P := by
    intro n hn n' hn'
    have hcc : 0 ≤ c n * c n' := mul_nonneg (hc n) (hc n')
    have hAP := mul_le_mul_of_nonneg_left (hA n hn n' hn') hcc
    have hηP : 0 ≤ η * (c n * c n') * P := mul_nonneg (mul_nonneg hη hcc) hP
    have hccP : 0 ≤ c n * c n' * P := mul_nonneg hcc hP
    split_ifs with h1 h2 h2
    · linarith
    · linarith
    · linarith
    · have hA2 := mul_le_mul_of_nonneg_left (hA' n hn n' hn' h1 h2) hcc
      linarith
  calc ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * A n n'
      ≤ ∑ n ∈ I, ∑ n' ∈ I, ((if r n n' = 1 then c n * c n' else 0) +
          (if r n n' = nstar then c n * c n' else 0) + η * (c n * c n')) * P :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun n' hn' => hpt n hn n' hn'
    _ = _ := by
        rw [sq, Finset.sum_mul_sum]
        simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
