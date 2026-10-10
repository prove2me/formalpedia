-- Prove2me | solution 1 for BookProof.MixedLinearEsa.hasDerivAt_gaugePhase_line
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:59:55.564088+00:00
-- url     : https://prove2.me/submissions/e762264b-4385-4f3a-b63c-984e5974ad81

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.hasDerivAt_gaugePhase_line
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
theorem solution (b m : V) (hm : m ≠ 0) (x : V) :
    HasDerivAt (fun t : ℝ => gaugePhase b m (x + t • m)) (-(inner ℝ x b : ℝ)) 0 := by

  set A : ℝ := inner ℝ x b with hA
  set B : ℝ := inner ℝ m b with hB
  set C : ℝ := inner ℝ x m with hC
  set D : ℝ := ‖m‖ ^ 2 with hD
  have hD0 : D ≠ 0 := by positivity
  have hbm : (inner ℝ b m : ℝ) = B := (real_inner_comm b m).symm
  have hfun : (fun t : ℝ => gaugePhase b m (x + t • m))
      = fun t : ℝ => (-(A + t * B)) * (C + t * D) / D + B * (C + t * D) ^ 2 / (2 * D ^ 2) := by
    funext t
    rw [gaugePhase, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hbm, real_inner_self_eq_norm_sq]
    simp only [hA, hB, hC, hD]
    ring
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => A + t * B) B 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const B).const_add A
  have h1n : HasDerivAt (fun t : ℝ => -(A + t * B)) (-B) 0 := h1.neg
  have h2 : HasDerivAt (fun t : ℝ => C + t * D) D 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const D).const_add C
  have h3 := ((h1n.mul h2).div_const D).add (((h2.pow 2).const_mul B).div_const (2 * D ^ 2))
  simp only [Nat.cast_ofNat] at h3
  convert h3 using 1
  all_goals first | rfl | (field_simp; ring) | trace_state
