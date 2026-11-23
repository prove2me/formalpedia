-- Prove2me | solution 1 for Bl.IterateZero.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:23.244331+00:00
-- url     : https://prove2.me/submissions/5a1a3d50-9abd-4e1d-8442-150ed3eaaf2f

import Mathlib
import Definitions.Def_Lemmata_IterateZero_IterZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.IterateZero
private lemma iter_zero (k : Nat) (g : Complex → Complex) (A : Real) (hg : Differentiable Complex g)
    (hb : ∀ t : Complex, ‖g t‖ ≤ A * (1 + ‖t‖) ^ k) (n : Nat) (hn : k < n) :
    iteratedDeriv n g 0 = 0 := by
  have hA : 0 ≤ A := by
    have := hb 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at this
    exact le_trans (norm_nonneg _) this
  have key : ∀ R : Real, 1 ≤ R → ‖iteratedDeriv n g 0‖ ≤ (n.factorial * A * 2 ^ k) / R := by
    intro R hR
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
    have h1 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) (C := A * (1 + R) ^ k)
      (f := g) n hR0 hg.diffContOnCl (by
        intro z hz
        have hz' : ‖z‖ = R := by simpa using hz
        simpa [hz'] using hb z)
    refine le_trans h1 ?_
    rw [div_le_div_iff₀ (pow_pos hR0 n) hR0]
    have hf : (0 : Real) ≤ n.factorial := Nat.cast_nonneg _
    have e1 : (1 + R) ^ k ≤ (2 * R) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    have e2 : R ^ (k + 1) ≤ R ^ n := pow_le_pow_right₀ hR hn
    calc (n.factorial : Real) * (A * (1 + R) ^ k) * R ≤ n.factorial * (A * (2 * R) ^ k) * R := by
          gcongr
      _ = n.factorial * A * 2 ^ k * R ^ (k + 1) := by rw [mul_pow, pow_succ]; ring
      _ ≤ n.factorial * A * 2 ^ k * R ^ n := by gcongr
  have ht : Filter.Tendsto (fun R : Real => (n.factorial * A * 2 ^ k) / R) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have : ‖iteratedDeriv n g 0‖ ≤ 0 :=
    ge_of_tendsto ht (Filter.eventually_atTop.2 ⟨1, key⟩)
  exact norm_le_zero_iff.mp this
end Bl.IterateZero
end

set_option autoImplicit false
open Bl Bl.IterateZero
namespace Bl.IterateZero
theorem _root_.solution :
  ∀ (k : Nat) (g : Complex → Complex) (A : Real),
  Differentiable.{0, 0, 0} Complex g →
    (∀ (t : Complex),
        LE.le.{0} (Norm.norm.{0} (g t))
          (HMul.hMul.{0, 0, 0} A (HPow.hPow.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} 1 (Norm.norm.{0} t)) k))) →
      Exists.{1} fun (P : Polynomial.{0} Complex) ↦
        And (LE.le.{0} (Polynomial.natDegree.{0} P) k) (∀ (t : Complex), Eq.{1} (g t) (Polynomial.eval.{0} t P)) := by
  intro k g A hg hb
  refine ⟨∑ n ∈ Finset.range (k + 1),
    Polynomial.C ((n.factorial : Complex)⁻¹ * iteratedDeriv n g 0) * Polynomial.X ^ n, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro n hn
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ n)
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
  · intro t
    have hs := Complex.hasSum_taylorSeries_of_entire hg 0 t
    have hz : ∀ n ∉ Finset.range (k + 1),
        (n.factorial : Complex)⁻¹ • (t - 0) ^ n • iteratedDeriv n g 0 = 0 := by
      intro n hn
      rw [iter_zero k g A hg hb n (by simpa using hn), smul_zero, smul_zero]
    rw [hs.unique (hasSum_sum_of_ne_finset_zero hz), Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl ?_
    intro n _
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      sub_zero, smul_eq_mul]
    ring
end Bl.IterateZero
