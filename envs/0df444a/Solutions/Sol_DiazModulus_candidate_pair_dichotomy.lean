-- Prove2me | solution 1 for DiazModulus.candidate_pair_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-04T18:55:45.080612+00:00
-- url     : https://prove2.me/submissions/0b39dd48-6509-41f0-adbb-4f8334f89973

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Diaz_pair_dichotomy_exclusive
import Theorems.Thm_DiazModulus_log_pair_rigid_of_trdeg_one
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_Transcendence_trdeg_adjoin_le_one_of_isAlgebraic_adjoin
import Theorems.Thm_Transcendence_isAlgebraic_adjoin_of_not_algebraicIndependent_pair

open Complex ComplexConjugate

namespace R4_candidate_pair_dichotomy

/-- `w w̄ = |w|²` is algebraic when `|w|` is. -/
theorem mul_conj_alg {w : ℂ} (hw : IsAlgebraic ℚ ((‖w‖ : ℝ) : ℂ)) :
    IsAlgebraic ℚ (w * conj w) := by
  have h : w * conj w = ((‖w‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [h]; exact hw.pow 2

/-- If `w ≠ 0` is algebraic over `ℚ[u]` and `|w|` is algebraic, then so is `w̄ = |w|² / w`. -/
theorem conj_alg_adjoin {u w : ℂ} (hw0 : w ≠ 0) (hw : IsAlgebraic ℚ ((‖w‖ : ℝ) : ℂ))
    (hwu : IsAlgebraic (Algebra.adjoin ℚ ({u} : Set ℂ)) w) :
    IsAlgebraic (Algebra.adjoin ℚ ({u} : Set ℂ)) (conj w) :=
  IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hw0) hwu
    ((mul_conj_alg hw).extendScalars (algebraMap ℚ _).injective)

end R4_candidate_pair_dichotomy

/- (→) is `Diaz.pair_dichotomy_exclusive`, since `u ū = |u|²` is algebraic.
(←) `u` is transcendental by Hermite–Lindemann, so a dependent pair `u, v` has `v` algebraic over
`ℚ[u]`; so are `ū = |u|²/u` and `v̄ = |v|²/v`. Hence `trdeg ℚ(u, v, ū, v̄) ≤ 1`, and the rigidity
of logarithm pairs in transcendence degree one, applied with `u ū = (1/m) v v̄`, gives
`v ∈ ℚ u ∪ ℚ ū`; the multiplier is non-zero because `v ≠ 0`. -/
open DiazModulus R4_candidate_pair_dichotomy in
theorem solution (u v : ℂ) (hu : IsCandidate u) (hv : IsCandidate v)
    (m : ℚ) (hm : v * conj v = (m : ℂ) * (u * conj u)) :
    ((∃ c : ℚ, c ≠ 0 ∧ v = (c : ℂ) * u) ∨ (∃ c : ℚ, c ≠ 0 ∧ v = (c : ℂ) * conj u)) ↔
      ¬ AlgebraicIndependent ℚ ![u, v] := by
  obtain ⟨hu0, hun, hue⟩ := hu
  obtain ⟨hv0, hvn, hve⟩ := hv
  refine ⟨Diaz.pair_dichotomy_exclusive (mul_conj_alg hun), fun hdep => ?_⟩
  -- `u` is transcendental (Hermite–Lindemann), so `v` is algebraic over `ℚ[u]`
  have hvu := Transcendence.isAlgebraic_adjoin_of_not_algebraicIndependent_pair
    (fun h => hermite_lindemann_holds u hu0 h hue) hdep
  have huu : IsAlgebraic (Algebra.adjoin ℚ ({u} : Set ℂ)) u :=
    isAlgebraic_algebraMap (⟨u, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin ℚ ({u} : Set ℂ))
  have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({u, v, conj u, conj v} : Set ℂ)) ≤ 1 := by
    refine Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin u _ ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    exacts [huu, hvu, conj_alg_adjoin hu0 hun huu, conj_alg_adjoin hv0 hvn hvu]
  have hm0 : (m : ℂ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hm
    exact mul_ne_zero hv0 ((map_ne_zero _).2 hv0) hm
  obtain ⟨q, hq⟩ := log_pair_rigid_of_trdeg_one u v hu0 hv0 hue hve (1 / m)
    (by rw [hm]; push_cast; field_simp) htr
  have hq0 : q ≠ 0 := by
    rintro rfl
    rcases hq with h | h <;> simp only [Rat.cast_zero, zero_mul] at h <;> exact hv0 h
  exact hq.imp (fun h => ⟨q, hq0, h⟩) (fun h => ⟨q, hq0, h⟩)

#print axioms solution
