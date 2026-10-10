-- Prove2me | solution 1 for BookProof.MixedLinearEsa.hasDerivAt_polyPhase_line
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T22:04:12.611433+00:00
-- url     : https://prove2.me/submissions/712d56b9-9052-4853-bf7e-d1e0ebbb8a3c

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.hasDerivAt_polyPhase_line
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavine
open BookProof.MixedLinearEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (c : ℕ → ℝ) (n : ℕ) {m : V} (hm : m ≠ 0) (x : V) :
    HasDerivAt (fun t : ℝ => polyPhase c n m (x + t • m)) (-(polyPotential c n m x)) 0 := by

  have hD0 : (‖m‖ : ℝ) ^ 2 ≠ 0 := by positivity
  have hline : ∀ t : ℝ, (inner ℝ (x + t • m) m : ℝ) = (inner ℝ x m : ℝ) + t * ‖m‖ ^ 2 := by
    intro t
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hfun : (fun t : ℝ => polyPhase c n m (x + t • m))
      = fun t : ℝ => ∑ i ∈ Finset.range n,
          -(c i * ((inner ℝ x m : ℝ) + t * ‖m‖ ^ 2) ^ (i + 1) / ((i + 1) * ‖m‖ ^ 2)) := by
    funext t
    unfold polyPhase
    exact Finset.sum_congr rfl fun i _ => by rw [hline t]
  rw [hfun]
  have hbase : HasDerivAt (fun t : ℝ => (inner ℝ x m : ℝ) + t * ‖m‖ ^ 2) (‖m‖ ^ 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (‖m‖ ^ 2)).const_add (inner ℝ x m : ℝ)
  have hterm : ∀ i ∈ Finset.range n,
      HasDerivAt (fun t : ℝ => -(c i * ((inner ℝ x m : ℝ) + t * ‖m‖ ^ 2) ^ (i + 1)
        / ((i + 1) * ‖m‖ ^ 2))) (-(c i * (inner ℝ x m : ℝ) ^ i)) 0 := by
    intro i _
    have h1 : HasDerivAt (fun t : ℝ => ((inner ℝ x m : ℝ) + t * ‖m‖ ^ 2) ^ (i + 1))
        (((i : ℝ) + 1) * ((inner ℝ x m : ℝ)) ^ i * ‖m‖ ^ 2) 0 := by
      have h := hbase.pow (i + 1)
      simp only [Nat.cast_add, Nat.cast_one, zero_mul, add_zero, Nat.add_sub_cancel] at h
      exact h
    have h2 := ((h1.const_mul (c i)).div_const (((i : ℝ) + 1) * ‖m‖ ^ 2)).neg
    have hi0 : ((i : ℝ) + 1) ≠ 0 := by positivity
    have hD : ((i : ℝ) + 1) * ‖m‖ ^ 2 ≠ 0 := mul_ne_zero hi0 hD0
    convert h2 using 1
    all_goals first | rfl | (rw [neg_inj, eq_div_iff hD]; ring) | (field_simp; ring) | trace_state
  have hsum := HasDerivAt.sum hterm
  have hfe : (∑ i ∈ Finset.range n, fun t : ℝ =>
        -(c i * ((inner ℝ x m : ℝ) + t * ‖m‖ ^ 2) ^ (i + 1) / (((i : ℝ) + 1) * ‖m‖ ^ 2)))
      = fun t : ℝ => ∑ i ∈ Finset.range n,
        -(c i * ((inner ℝ x m : ℝ) + t * ‖m‖ ^ 2) ^ (i + 1) / (((i : ℝ) + 1) * ‖m‖ ^ 2)) :=
    funext fun t => by simp
  rw [hfe] at hsum
  convert hsum using 1
  all_goals first | rfl | (simp [polyPotential, Finset.sum_neg_distrib]; done) | trace_state
