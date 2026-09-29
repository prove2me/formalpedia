-- Prove2me | solution 1 for Deformation.PLoc.wPartialSum_adicEval_add_sub_sub_algebraMap_mul_add_mem_powSub_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7f704ef5-5f77-5ff1-a721-c27e06de06d2

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_Dieudonne_FontaineFunctor
import Theorems.Thm_MvFormalGroup_adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq
import Theorems.Thm_add_two_mul_pow_two_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_PLoc_wPartialSum_adicEval_add_sub_sub_algebraMap_mul_add_mem_powSub_two

set_option autoImplicit false

open MvPowerSeries

universe u v

namespace StepNTwo

private theorem sq_sum_eq {A : Type*} [CommRing A] {ι : Type*} (s : Finset ι) (c : ι → A) :
    ∃ t : A, (∑ j ∈ s, c j) ^ 2 = ∑ j ∈ s, c j ^ 2 + 2 * t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert b s hb IH =>
    obtain ⟨t, ht⟩ := IH
    refine ⟨t + c b * ∑ j ∈ s, c j, ?_⟩
    rw [Finset.sum_insert hb, Finset.sum_insert hb, add_sq, ht]
    ring

end StepNTwo

open StepNTwo in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp2 : p = 2) (d : ℕ)
    (a : Fin d → ℕ → MvPowerSeries (Fin d) 𝓞)
    (ha : ∀ i n, MvPowerSeries.constantCoeff (a i n) = 0)
    (Da : Fin d → ℕ → Fin d → MvPowerSeries (Fin d) 𝓞)
    (hDa : ∀ (i : Fin d) (n : ℕ) (j : Fin d) (m : Fin d →₀ ℕ),
      (Da i n j).coeff m = ((m j + 1 : ℕ) : 𝓞) * (a i n).coeff (m + Finsupp.single j 1))
    (g : Type v) [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]
    (x : Fin d → g) (hx : ∀ j, x j ∈ (Ideal.span {(p : g)}).radical)
    (y : Fin d → g) (i : Fin d) (N : ℕ) :
    Deformation.PLoc.wPartialSum p
        (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (fun j => x j + (p : g) * y j) (a i n)) N
      - Deformation.PLoc.wPartialSum p
        (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (a i n)) N
      - algebraMap g (Localization.Away (p : g)) ((p : g) *
          (∑ j : Fin d, (∑ n ∈ Finset.range N,
              MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (a i n) ^ (p ^ n - 1) *
                MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (Da i n j)) * y j
            + ∑ j : Fin d, (∑ n ∈ Finset.Ico 1 N,
              MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (a i n) ^ (p ^ n - 2) *
                MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (Da i n j) ^ 2) * y j ^ 2))
      ∈ Deformation.PLoc.powSub p g 2 := by
  classical
  have _ha := ha
  subst hp2
  set J : Ideal g := Ideal.span {((2 : ℕ) : g)} with hJ
  have two : (2 : g) = ((2 : ℕ) : g) := by norm_num
  let x' : Fin d → g := fun j => x j + ((2 : ℕ) : g) * y j
  let z : Fin d → g := fun j => ((2 : ℕ) : g) * y j
  have hz : ∀ j, z j ∈ J.radical := fun j =>
    Ideal.le_radical (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hzsq : (Ideal.span (Set.range z)) ^ 2 ≤ Ideal.span {(((2 : ℕ) : g)) ^ 2} := by
    rw [← Ideal.span_singleton_pow]
    refine Ideal.pow_right_mono ?_ 2
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  set u : ℕ → g := fun n => MvFormalGroup.adicEval J x (a i n) with hu
  set D : ℕ → Fin d → g := fun n j => MvFormalGroup.adicEval J x (Da i n j) with hD

  have hTaylor : ∀ n, ∃ e : g, MvFormalGroup.adicEval J x' (a i n) =
      u n + ((2 : ℕ) : g) * ∑ j : Fin d, D n j * y j + ((2 : ℕ) : g) ^ 2 * e := by
    intro n
    have hT := MvFormalGroup.adicEval_add_sub_adicEval_sub_sum_mul_mem_span_sq J (a i n) (Da i n)
      (hDa i n) x z hx hz
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp (hzsq hT)
    refine ⟨e, ?_⟩
    have h0 : MvFormalGroup.adicEval J x' (a i n) = MvFormalGroup.adicEval J (x + z) (a i n) := rfl
    rw [h0]
    have h1 : MvFormalGroup.adicEval J (x + z) (a i n) =
        u n + ∑ j : Fin d, D n j * z j + e * (((2 : ℕ) : g)) ^ 2 := by
      rw [he]; simp only [hu, hD]; ring
    rw [h1, Finset.mul_sum]
    have : ∑ j : Fin d, D n j * z j = ∑ j : Fin d, ((2 : ℕ) : g) * (D n j * y j) :=
      Finset.sum_congr rfl fun j _ => by simp only [z]; ring
    rw [this]
    ring

  have hterm0 : Deformation.PLoc.invPow 2 g 0 *
        algebraMap g (Localization.Away ((2 : ℕ) : g)) (MvFormalGroup.adicEval J x' (a i 0) ^ 2 ^ 0)
      - Deformation.PLoc.invPow 2 g 0 * algebraMap g (Localization.Away ((2 : ℕ) : g)) (u 0 ^ 2 ^ 0)
      - algebraMap g (Localization.Away ((2 : ℕ) : g))
          (((2 : ℕ) : g) * ∑ j : Fin d, (u 0 ^ (2 ^ 0 - 1) * D 0 j) * y j)
      ∈ Deformation.PLoc.powSub 2 g 2 := by
    obtain ⟨e, he⟩ := hTaylor 0
    rw [Deformation.PLoc.invPow_zero, one_mul, one_mul, pow_zero, pow_one, pow_one, he, ← map_sub, ← map_sub]
    have : u 0 + ((2 : ℕ) : g) * ∑ j : Fin d, D 0 j * y j + ((2 : ℕ) : g) ^ 2 * e - u 0
        - ((2 : ℕ) : g) * ∑ j : Fin d, (u 0 ^ (1 - 1) * D 0 j) * y j = (((2 : ℕ) : g)) ^ 2 * e := by
      simp only [Nat.sub_self, pow_zero, one_mul]
      ring
    rw [this]
    exact Deformation.PLoc.algebraMap_pow_mul_mem_powSub 2 2 _

  have hterm : ∀ n, 1 ≤ n →
      Deformation.PLoc.invPow 2 g n *
          algebraMap g (Localization.Away ((2 : ℕ) : g)) (MvFormalGroup.adicEval J x' (a i n) ^ 2 ^ n)
        - Deformation.PLoc.invPow 2 g n * algebraMap g (Localization.Away ((2 : ℕ) : g)) (u n ^ 2 ^ n)
        - algebraMap g (Localization.Away ((2 : ℕ) : g)) (((2 : ℕ) : g) *
            (∑ j : Fin d, (u n ^ (2 ^ n - 1) * D n j) * y j
              + ∑ j : Fin d, (u n ^ (2 ^ n - 2) * D n j ^ 2) * y j ^ 2))
        ∈ Deformation.PLoc.powSub 2 g 2 := by
    intro n hn
    obtain ⟨e, he⟩ := hTaylor n
    set S : g := ∑ j : Fin d, D n j * y j with hS
    obtain ⟨t, ht⟩ := StepNTwo.sq_sum_eq (Finset.univ : Finset (Fin d)) (fun j => D n j * y j)
    obtain ⟨w, hw⟩ := add_two_mul_pow_two_pow_eq n hn (u n) (S + ((2 : ℕ) : g) * e)
    simp only [two] at hw
    have he' : MvFormalGroup.adicEval J x' (a i n) = u n + ((2 : ℕ) : g) * (S + ((2 : ℕ) : g) * e) := by
      rw [he]; ring
    rw [he', hw]
    have e1 : Deformation.PLoc.invPow 2 g n * algebraMap g (Localization.Away ((2 : ℕ) : g))
        (((2 : ℕ) : g) ^ (n + 1) *
          (u n ^ (2 ^ n - 1) * (S + ((2 : ℕ) : g) * e) + u n ^ (2 ^ n - 2) * (S + ((2 : ℕ) : g) * e) ^ 2)) =
        algebraMap g (Localization.Away ((2 : ℕ) : g)) (((2 : ℕ) : g) ^ 1 *
          (u n ^ (2 ^ n - 1) * (S + ((2 : ℕ) : g) * e) + u n ^ (2 ^ n - 2) * (S + ((2 : ℕ) : g) * e) ^ 2)) := by
      rw [map_mul, ← mul_assoc, Deformation.PLoc.invPow_mul_algebraMap_pow_add, ← map_mul]
    have e2 : Deformation.PLoc.invPow 2 g n * algebraMap g (Localization.Away ((2 : ℕ) : g))
        (((2 : ℕ) : g) ^ (n + 2) * w) =
        algebraMap g (Localization.Away ((2 : ℕ) : g)) (((2 : ℕ) : g) ^ 2 * w) := by
      rw [map_mul, ← mul_assoc, Deformation.PLoc.invPow_mul_algebraMap_pow_add, ← map_mul]

    have hsq : S ^ 2 = ∑ j : Fin d, D n j ^ 2 * y j ^ 2 + 2 * t := by
      rw [hS, ht]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    have hlin : u n ^ (2 ^ n - 1) * S = ∑ j : Fin d, (u n ^ (2 ^ n - 1) * D n j) * y j := by
      rw [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have hquad : u n ^ (2 ^ n - 2) * ∑ j : Fin d, D n j ^ 2 * y j ^ 2 =
        ∑ j : Fin d, (u n ^ (2 ^ n - 2) * D n j ^ 2) * y j ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have key : Deformation.PLoc.invPow 2 g n * algebraMap g (Localization.Away ((2 : ℕ) : g))
          (u n ^ 2 ^ n + ((2 : ℕ) : g) ^ (n + 1) * (u n ^ (2 ^ n - 1) * (S + ((2 : ℕ) : g) * e)
            + u n ^ (2 ^ n - 2) * (S + ((2 : ℕ) : g) * e) ^ 2) + ((2 : ℕ) : g) ^ (n + 2) * w)
        - Deformation.PLoc.invPow 2 g n * algebraMap g (Localization.Away ((2 : ℕ) : g)) (u n ^ 2 ^ n)
        - algebraMap g (Localization.Away ((2 : ℕ) : g)) (((2 : ℕ) : g) *
            (∑ j : Fin d, (u n ^ (2 ^ n - 1) * D n j) * y j
              + ∑ j : Fin d, (u n ^ (2 ^ n - 2) * D n j ^ 2) * y j ^ 2))
        = algebraMap g (Localization.Away ((2 : ℕ) : g)) (((2 : ℕ) : g) ^ 2 *
            (u n ^ (2 ^ n - 1) * e + u n ^ (2 ^ n - 2) * (t + 2 * S * e + 2 * e ^ 2) + w)) := by
      rw [map_add (algebraMap g _), map_add (algebraMap g _), mul_add, mul_add, e1, e2,
        add_assoc, add_sub_cancel_left, ← map_add, ← map_sub]
      congr 1
      rw [← hlin, ← hquad]
      have hexp : (S + ((2 : ℕ) : g) * e) ^ 2 =
          ∑ j : Fin d, D n j ^ 2 * y j ^ 2 + 2 * t + 2 * ((2 : ℕ) : g) * S * e + ((2 : ℕ) : g) ^ 2 * e ^ 2 := by
        rw [add_sq, hsq]; ring
      rw [hexp, ← two]
      ring
    rw [key]
    exact Deformation.PLoc.algebraMap_pow_mul_mem_powSub 2 2 _

  show Deformation.PLoc.wPartialSum 2 (fun n => MvFormalGroup.adicEval J x' (a i n)) N
      - Deformation.PLoc.wPartialSum 2 (fun n => MvFormalGroup.adicEval J x (a i n)) N
      - algebraMap g (Localization.Away ((2 : ℕ) : g)) (((2 : ℕ) : g) *
          (∑ j : Fin d, (∑ n ∈ Finset.range N, u n ^ (2 ^ n - 1) * D n j) * y j
            + ∑ j : Fin d, (∑ n ∈ Finset.Ico 1 N, u n ^ (2 ^ n - 2) * D n j ^ 2) * y j ^ 2))
      ∈ Deformation.PLoc.powSub 2 g 2
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Deformation.PLoc.wPartialSum_zero, Finset.range_zero, Finset.Ico_eq_empty_of_le (Nat.zero_le 1),
      Finset.sum_empty, zero_mul, Finset.sum_const_zero, add_zero, mul_zero, map_zero, sub_self]
    exact Submodule.zero_mem _
  have hA : ∑ j : Fin d, (∑ n ∈ Finset.range N, u n ^ (2 ^ n - 1) * D n j) * y j =
      ∑ j : Fin d, (u 0 ^ (2 ^ 0 - 1) * D 0 j) * y j
        + ∑ n ∈ Finset.Ico 1 N, ∑ j : Fin d, (u n ^ (2 ^ n - 1) * D n j) * y j := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN]
  have hB : ∑ j : Fin d, (∑ n ∈ Finset.Ico 1 N, u n ^ (2 ^ n - 2) * D n j ^ 2) * y j ^ 2 =
      ∑ n ∈ Finset.Ico 1 N, ∑ j : Fin d, (u n ^ (2 ^ n - 2) * D n j ^ 2) * y j ^ 2 := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hL : ((2 : ℕ) : g) * (∑ j : Fin d, (∑ n ∈ Finset.range N, u n ^ (2 ^ n - 1) * D n j) * y j
        + ∑ j : Fin d, (∑ n ∈ Finset.Ico 1 N, u n ^ (2 ^ n - 2) * D n j ^ 2) * y j ^ 2)
      = ((2 : ℕ) : g) * ∑ j : Fin d, (u 0 ^ (2 ^ 0 - 1) * D 0 j) * y j
        + ∑ n ∈ Finset.Ico 1 N, ((2 : ℕ) : g) * (∑ j : Fin d, (u n ^ (2 ^ n - 1) * D n j) * y j
            + ∑ j : Fin d, (u n ^ (2 ^ n - 2) * D n j ^ 2) * y j ^ 2) := by
    rw [hA, hB, ← Finset.mul_sum, Finset.sum_add_distrib]
    ring
  have hW : ∀ b : ℕ → g, Deformation.PLoc.wPartialSum 2 b N =
      Deformation.PLoc.invPow 2 g 0 * algebraMap g (Localization.Away ((2 : ℕ) : g)) (b 0 ^ 2 ^ 0)
        + ∑ n ∈ Finset.Ico 1 N, Deformation.PLoc.invPow 2 g n *
          algebraMap g (Localization.Away ((2 : ℕ) : g)) (b n ^ 2 ^ n) := by
    intro b
    rw [Deformation.PLoc.wPartialSum, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN]
  rw [hL, hW, hW, map_add, map_sum]
  have hre : ∀ (A0 B0 C0 : Localization.Away ((2 : ℕ) : g)) (A B C : ℕ → Localization.Away ((2 : ℕ) : g)),
      A0 + ∑ n ∈ Finset.Ico 1 N, A n - (B0 + ∑ n ∈ Finset.Ico 1 N, B n) - (C0 + ∑ n ∈ Finset.Ico 1 N, C n)
        = (A0 - B0 - C0) + ∑ n ∈ Finset.Ico 1 N, (A n - B n - C n) := by
    intro A0 B0 C0 A B C
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  rw [hre]
  refine Submodule.add_mem _ hterm0 (Submodule.sum_mem _ fun n hn => ?_)
  exact hterm n (Finset.mem_Ico.mp hn).1

end S_Deformation_PLoc_wPartialSum_adicEval_add_sub_sub_algebraMap_mul_add_mem_powSub_two
end P2MW
export P2MW.S_Deformation_PLoc_wPartialSum_adicEval_add_sub_sub_algebraMap_mul_add_mem_powSub_two (solution)
