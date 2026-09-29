-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.mem_of_mk_sum_C_mul_X_mem_span_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0d178433-5ff9-57d8-9d0d-4226ea660053

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_mem_of_mk_sum_C_mul_X_mem_span_sq

set_option autoImplicit false
set_option maxHeartbeats 3200000

open MvPowerSeries

theorem solution
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] (I : Ideal W)
    (t : W) (ht : t ∈ I) (f u v : MvPowerSeries (Fin 2) W)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (a : Fin 2 → W)
    (h : Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u})
        (∑ ii : Fin 2, MvPowerSeries.C (a ii) * MvPowerSeries.X ii) ∈
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 0),
        Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C t * v - f * u}) (MvPowerSeries.X 1)}) ^ 2) :
    ∀ ii : Fin 2, a ii ∈ I := by
  classical
  intro ii
  set JX : Ideal (MvPowerSeries (Fin 2) W) := Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} with hJX
  set rel : MvPowerSeries (Fin 2) W := MvPowerSeries.C t * v - f * u with hrel
  set lin : MvPowerSeries (Fin 2) W := ∑ ii : Fin 2, MvPowerSeries.C (a ii) * MvPowerSeries.X ii with hlin

  have hJmap : Ideal.span {Ideal.Quotient.mk (Ideal.span {rel}) (MvPowerSeries.X 0),
      Ideal.Quotient.mk (Ideal.span {rel}) (MvPowerSeries.X 1)} = JX.map (Ideal.Quotient.mk (Ideal.span {rel})) := by
    rw [hJX, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  have h' : Ideal.Quotient.mk (Ideal.span {rel}) lin ∈ (JX ^ 2).map (Ideal.Quotient.mk (Ideal.span {rel})) := by
    rw [Ideal.map_pow, ← hJmap]; exact h
  obtain ⟨g, hg, hgl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h'
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hgl
  obtain ⟨k, hk⟩ := hgl

  set n : Fin 2 →₀ ℕ := Finsupp.single ii 1 with hn
  have hn1 : n 0 + n 1 < 2 := by
    rw [hn]; fin_cases ii <;> simp
  have hcoeff_pow2 : ∀ p ∈ JX ^ 2, MvPowerSeries.coeff n p = 0 := by
    intro p hp
    exact (MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W 2 p).mp (by rw [hJX] at hp; exact hp) n hn1

  have hX0 : (X 0 : MvPowerSeries (Fin 2) W) ∈ JX := by rw [hJX]; exact Ideal.subset_span (by simp)
  have hX1 : (X 1 : MvPowerSeries (Fin 2) W) ∈ JX := by rw [hJX]; exact Ideal.subset_span (by simp)
  have hq1 : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
  have hDF : DrinfeldCurve.LocalChart.drinfeldForm q W ∈ JX ^ 2 := by
    unfold DrinfeldCurve.LocalChart.drinfeldForm
    refine Ideal.sub_mem _ ?_ ?_
    · rw [pow_two]; exact Ideal.mul_mem_mul hX0 (Ideal.pow_mem_of_mem JX hX1 q hq1)
    · rw [pow_two]; exact Ideal.mul_mem_mul (Ideal.pow_mem_of_mem JX hX0 q hq1) hX1
  have hf2 : f ∈ JX ^ 2 := by
    have h1 : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈ JX ^ 2 := by
      rw [hJX]; exact Ideal.pow_le_pow_right (by omega) hf
    have : f = (f - DrinfeldCurve.LocalChart.drinfeldForm q W) + DrinfeldCurve.LocalChart.drinfeldForm q W := by ring
    rw [this]; exact Ideal.add_mem _ h1 hDF

  have hclin : MvPowerSeries.coeff n lin = a ii := by
    rw [hlin, Fin.sum_univ_two, map_add, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
      MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, hn]
    fin_cases ii <;> simp [Finsupp.single_eq_single_iff]
  have hcg : MvPowerSeries.coeff n g = 0 := hcoeff_pow2 g hg
  have hcfu : MvPowerSeries.coeff n (k * (f * u)) = 0 := by
    apply hcoeff_pow2
    have : k * (f * u) = (k * u) * f := by ring
    rw [this]; exact Ideal.mul_mem_left _ _ hf2

  have hlin' : lin = g - MvPowerSeries.C t * (k * v) + k * (f * u) := by
    have := hk
    rw [hrel] at this
    have : lin = g - k * (MvPowerSeries.C t * v - f * u) := by rw [this]; ring
    rw [this]; ring
  have key : a ii = 0 - t * MvPowerSeries.coeff n (k * v) + 0 := by
    rw [← hclin, hlin', map_add, map_sub, hcg, hcfu, MvPowerSeries.coeff_C_mul]
  rw [key, zero_sub, add_zero]
  exact I.neg_mem (I.mul_mem_right _ ht)

end S_DrinfeldCurve_LocalChart_mem_of_mk_sum_C_mul_X_mem_span_sq
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_mem_of_mk_sum_C_mul_X_mem_span_sq (solution)
