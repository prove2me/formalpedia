-- Prove2me | solution 1 for Deformation.PLoc.wPartialSum_adicEval_add_sub_sub_algebraMap_mul_sum_mem_powSub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/dd5e863f-10ab-58be-b361-61dafe691fb5

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_Dieudonne_FontaineFunctor
import Theorems.Thm_MvFormalGroup_adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq
import Theorems.Thm_add_pow_prime_pow_eq_add_mul_add_mul_of_ne_two_or_two_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_PLoc_wPartialSum_adicEval_add_sub_sub_algebraMap_mul_sum_mem_powSub

set_option autoImplicit false

open MvPowerSeries

universe u v

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (d : ℕ)
    (a : Fin d → ℕ → MvPowerSeries (Fin d) 𝓞)
    (ha : ∀ i n, MvPowerSeries.constantCoeff (a i n) = 0)
    (Da : Fin d → ℕ → Fin d → MvPowerSeries (Fin d) 𝓞)
    (hDa : ∀ (i : Fin d) (n : ℕ) (j : Fin d) (m : Fin d →₀ ℕ),
      (Da i n j).coeff m = ((m j + 1 : ℕ) : 𝓞) * (a i n).coeff (m + Finsupp.single j 1))
    (g : Type v) [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]
    (x : Fin d → g) (hx : ∀ j, x j ∈ (Ideal.span {(p : g)}).radical)
    (r : ℕ) (hr : 1 ≤ r) (h2 : p ≠ 2 ∨ 2 ≤ r) (y : Fin d → g) (i : Fin d) (N : ℕ) :
    Deformation.PLoc.wPartialSum p
        (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (fun j => x j + (p : g) ^ r * y j) (a i n)) N
      - Deformation.PLoc.wPartialSum p
        (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (a i n)) N
      - algebraMap g (Localization.Away (p : g)) ((p : g) ^ r *
          ∑ j : Fin d, (∑ n ∈ Finset.range N,
            MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (a i n) ^ (p ^ n - 1) *
              MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (Da i n j)) * y j)
      ∈ Deformation.PLoc.powSub p g (r + 1) := by
  classical
  have _ha := ha
  set J : Ideal g := Ideal.span {(p : g)} with hJ
  set P := Localization.Away (p : g) with hP
  let x' : Fin d → g := fun j => x j + (p : g) ^ r * y j
  let z : Fin d → g := fun j => (p : g) ^ r * y j
  have hz : ∀ j, z j ∈ J.radical := fun j =>
    Ideal.le_radical (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem J (Ideal.mem_span_singleton_self _) r hr))
  have hzsq : (Ideal.span (Set.range z)) ^ 2 ≤ Ideal.span {((p : g) ^ r) ^ 2} := by
    rw [← Ideal.span_singleton_pow]
    refine Ideal.pow_right_mono ?_ 2
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

  set u : ℕ → g := fun n => MvFormalGroup.adicEval J x (a i n) with hu
  set D : ℕ → Fin d → g := fun n j => MvFormalGroup.adicEval J x (Da i n j) with hD

  have hterm : ∀ n : ℕ,
      Deformation.PLoc.invPow p g n * algebraMap g P (MvFormalGroup.adicEval J x' (a i n) ^ p ^ n)
        - Deformation.PLoc.invPow p g n * algebraMap g P (u n ^ p ^ n)
        - algebraMap g P ((p : g) ^ r * ∑ j : Fin d, (u n ^ (p ^ n - 1) * D n j) * y j)
        ∈ Deformation.PLoc.powSub p g (r + 1) := by
    intro n

    have hT := MvFormalGroup.adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq J (a i n) (Da i n)
      (hDa i n) x z hx hz
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp (hzsq hT)
    have hx' : MvFormalGroup.adicEval J x' (a i n) = u n + (p : g) ^ r *
        (∑ j : Fin d, D n j * y j + (p : g) ^ r * e) := by
      have h0 : MvFormalGroup.adicEval J x' (a i n) = MvFormalGroup.adicEval J (x + z) (a i n) := rfl
      rw [h0]
      have h1 : MvFormalGroup.adicEval J (x + z) (a i n) =
          u n + ∑ j : Fin d, D n j * z j + e * ((p : g) ^ r) ^ 2 := by
        rw [he]; simp only [hu, hD]; ring
      rw [h1, mul_add, Finset.mul_sum]
      simp only [z]
      ring_nf
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_; ring

    obtain ⟨w, hw⟩ := add_pow_prime_pow_eq_add_mul_add_mul_of_ne_two_or_two_le p n r hr h2 (u n)
      (∑ j : Fin d, D n j * y j + (p : g) ^ r * e)
    rw [hx', hw]

    have e1 : Deformation.PLoc.invPow p g n * algebraMap g P ((p : g) ^ (n + r) *
        (u n ^ (p ^ n - 1) * (∑ j : Fin d, D n j * y j + (p : g) ^ r * e))) =
        algebraMap g P ((p : g) ^ r * (u n ^ (p ^ n - 1) * (∑ j : Fin d, D n j * y j + (p : g) ^ r * e))) := by
      rw [map_mul, ← mul_assoc, Deformation.PLoc.invPow_mul_algebraMap_pow_add, ← map_mul]
    have e2 : Deformation.PLoc.invPow p g n * algebraMap g P ((p : g) ^ (n + r + 1) * w) =
        algebraMap g P ((p : g) ^ (r + 1) * w) := by
      rw [map_mul, ← mul_assoc, show n + r + 1 = n + (r + 1) by ring,
        Deformation.PLoc.invPow_mul_algebraMap_pow_add, ← map_mul]
    have e5 : (p : g) ^ r * (u n ^ (p ^ n - 1) * (∑ j : Fin d, D n j * y j + (p : g) ^ r * e)) =
        (p : g) ^ r * ∑ j : Fin d, (u n ^ (p ^ n - 1) * D n j) * y j
          + (p : g) ^ (2 * r) * (u n ^ (p ^ n - 1) * e) := by
      have hS : u n ^ (p ^ n - 1) * ∑ j : Fin d, D n j * y j = ∑ j : Fin d, (u n ^ (p ^ n - 1) * D n j) * y j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [mul_add, ← hS, two_mul, pow_add]
      ring
    have key : Deformation.PLoc.invPow p g n * algebraMap g P
          (u n ^ p ^ n + (p : g) ^ (n + r) * u n ^ (p ^ n - 1) * (∑ j : Fin d, D n j * y j + (p : g) ^ r * e)
            + (p : g) ^ (n + r + 1) * w)
        - Deformation.PLoc.invPow p g n * algebraMap g P (u n ^ p ^ n)
        - algebraMap g P ((p : g) ^ r * ∑ j : Fin d, (u n ^ (p ^ n - 1) * D n j) * y j)
        = algebraMap g P ((p : g) ^ (2 * r) * (u n ^ (p ^ n - 1) * e))
          + algebraMap g P ((p : g) ^ (r + 1) * w) := by
      rw [show u n ^ p ^ n + (p : g) ^ (n + r) * u n ^ (p ^ n - 1) * (∑ j : Fin d, D n j * y j + (p : g) ^ r * e)
            + (p : g) ^ (n + r + 1) * w
          = u n ^ p ^ n + ((p : g) ^ (n + r) * (u n ^ (p ^ n - 1) * (∑ j : Fin d, D n j * y j + (p : g) ^ r * e))
            + (p : g) ^ (n + r + 1) * w) by ring, map_add (algebraMap g P), mul_add, map_add, mul_add, e1, e2,
        e5, map_add]
      ring
    rw [key]
    refine Submodule.add_mem _ ?_ (Deformation.PLoc.algebraMap_pow_mul_mem_powSub p (r + 1) _)
    exact Deformation.PLoc.powSub_le_powSub_of_le p (show r + 1 ≤ 2 * r by omega)
      (Deformation.PLoc.algebraMap_pow_mul_mem_powSub p (2 * r) _)

  have hsum : Deformation.PLoc.wPartialSum p (fun n => MvFormalGroup.adicEval J x' (a i n)) N
      - Deformation.PLoc.wPartialSum p (fun n => MvFormalGroup.adicEval J x (a i n)) N
      - algebraMap g P ((p : g) ^ r * ∑ j : Fin d, (∑ n ∈ Finset.range N, u n ^ (p ^ n - 1) * D n j) * y j)
      = ∑ n ∈ Finset.range N,
        (Deformation.PLoc.invPow p g n * algebraMap g P (MvFormalGroup.adicEval J x' (a i n) ^ p ^ n)
          - Deformation.PLoc.invPow p g n * algebraMap g P (u n ^ p ^ n)
          - algebraMap g P ((p : g) ^ r * ∑ j : Fin d, (u n ^ (p ^ n - 1) * D n j) * y j)) := by
    have hlin : (p : g) ^ r * ∑ j : Fin d, (∑ n ∈ Finset.range N, u n ^ (p ^ n - 1) * D n j) * y j =
        ∑ n ∈ Finset.range N, (p : g) ^ r * ∑ j : Fin d, (u n ^ (p ^ n - 1) * D n j) * y j := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [hlin, map_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rfl
  show Deformation.PLoc.wPartialSum p (fun n => MvFormalGroup.adicEval J x' (a i n)) N
      - Deformation.PLoc.wPartialSum p (fun n => MvFormalGroup.adicEval J x (a i n)) N
      - algebraMap g P ((p : g) ^ r * ∑ j : Fin d, (∑ n ∈ Finset.range N, u n ^ (p ^ n - 1) * D n j) * y j)
      ∈ Deformation.PLoc.powSub p g (r + 1)
  rw [hsum]
  exact Submodule.sum_mem _ fun n _ => hterm n

end S_Deformation_PLoc_wPartialSum_adicEval_add_sub_sub_algebraMap_mul_sum_mem_powSub
end P2MW
export P2MW.S_Deformation_PLoc_wPartialSum_adicEval_add_sub_sub_algebraMap_mul_sum_mem_powSub (solution)
