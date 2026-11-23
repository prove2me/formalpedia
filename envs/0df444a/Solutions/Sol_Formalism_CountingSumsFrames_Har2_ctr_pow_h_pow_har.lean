-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.ctr_pow_h_pow_har
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:52.07419+00:00
-- url     : https://prove2.me/submissions/a359c161-3f96-4868-b464-7f80b7739dda

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctr_h_pow_har
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.CountingSumsFrames
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
private theorem mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero {A B : ℕ} {f : PolXY K k} :
    f ∈ HarAB K k A B ↔ f ∈ PolAB K k A B ∧ ctrF K k f = 0 := Iff.rfl
end Har2
open Har2
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
end Har2
end Formalism.CountingSumsFrames
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution (hk : 1 ≤ k) {a b : ℕ} {w : PolXY K k} (hw : w ∈ HarAB K k a b) (m : ℕ) :
    ∀ i : ℕ, (ctrF K k ^ m) (hXY K k ^ i * w) =
      ((i.descFactorial m * (a + b + k + i - 1).descFactorial m : ℕ) : K) • (hXY K k ^ (i - m) * w) := by
  obtain ⟨h1, h2⟩ := mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 hw
  induction m with
  | zero => intro i; simp
  | succ m ih =>
    intro i
    rw [pow_succ, Module.End.mul_apply]
    rcases i with _ | j
    · rw [pow_zero, one_mul, h2, map_zero, Nat.zero_descFactorial_succ, zero_mul, Nat.cast_zero,
        zero_smul]
    · rw [ctr_h_pow_har j hw, map_smul, ih j, smul_smul, Nat.add_sub_add_right]
      congr 1
      have hN : a + b + k + (j + 1) - 1 = (a + b + k + j - 1) + 1 := by omega
      rw [hN, Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ]
      have hN2 : a + b + k + j - 1 + 1 = a + b + k + j := by omega
      rw [hN2]
      push_cast
      ring
end Formalism.CountingSumsFrames.Har2
