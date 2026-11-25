-- Prove2me | solution 1 for Erdos654Proof.noFourConcyclic_axes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:31:39.956435+00:00
-- url     : https://prove2.me/submissions/0f3d7243-53c4-4e72-88ea-686a8163757f

module
public import Mathlib
public import Definitions.Def_Erdos654Palomar_Solution
public import Theorems.Thm_Erdos654Proof_dist_sq
public import Theorems.Thm_Erdos654Proof_ext_two
public import Theorems.Thm_Erdos654Proof_axis0_sum
public import Theorems.Thm_Erdos654Proof_axis1_sum

set_option autoImplicit true
@[expose] public section
public section
open scoped EuclideanGeometry Finset
open Filter Finset EuclideanGeometry
open Erdos654Proof
namespace Erdos654Proof
theorem _root_.solution : NoFourConcyclic (XAxis ∪ YAxis) := by
  intro T hT h4 ⟨c, r, hcr⟩
  have hTfin : T.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hXfin : (T ∩ XAxis).Finite := hTfin.subset Set.inter_subset_left
  have hYfin : (T ∩ YAxis).Finite := hTfin.subset Set.inter_subset_left
  have hX : (T ∩ XAxis).ncard ≤ 2 := by
    by_contra! h
    obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := (Set.two_lt_ncard_iff hXfin).1 h
    have h1 := axis0_sum ha.2.1 hb.2.1 hab (hcr a ha.1) (hcr b hb.1)
    have h2 := axis0_sum ha.2.1 hd.2.1 had (hcr a ha.1) (hcr d hd.1)
    exact hbd (ext_two (by linarith) (hb.2.1.trans hd.2.1.symm))
  have hY : (T ∩ YAxis).ncard ≤ 2 := by
    by_contra! h
    obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ := (Set.two_lt_ncard_iff hYfin).1 h
    have h1 := axis1_sum ha.2.1 hb.2.1 hab (hcr a ha.1) (hcr b hb.1)
    have h2 := axis1_sum ha.2.1 hd.2.1 had (hcr a ha.1) (hcr d hd.1)
    exact hbd (ext_two (hb.2.1.trans hd.2.1.symm) (by linarith))
  have hdisj : Disjoint (T ∩ XAxis) (T ∩ YAxis) := by
    rw [Set.disjoint_left]
    rintro P ⟨-, hP1, -⟩ ⟨-, -, b, hb⟩
    rw [hP1] at hb
    have : ((2 * b + 1 : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by push_cast; linarith
    have := Int.cast_injective this
    omega
  have hsplit : T.ncard = (T ∩ XAxis).ncard + (T ∩ YAxis).ncard := by
    rw [← Set.ncard_union_eq hdisj hXfin hYfin, ← Set.inter_union_distrib_left,
      Set.inter_eq_left.2 hT]
  obtain ⟨p, q, hp, hq, hpq⟩ := (Set.one_lt_ncard_iff hXfin).1 (by omega)
  obtain ⟨u, v, hu, hv, huv⟩ := (Set.one_lt_ncard_iff hYfin).1 (by omega)
  have s1 := axis0_sum hp.2.1 hq.2.1 hpq (hcr p hp.1) (hcr q hq.1)
  have s2 := axis1_sum hu.2.1 hv.2.1 huv (hcr u hu.1) (hcr v hv.1)
  have e1 := dist_sq p c
  have e2 := dist_sq u c
  rw [hcr p hp.1, hp.2.1] at e1
  rw [hcr u hu.1, hu.2.1] at e2
  have key : p 0 * q 0 = u 1 * v 1 := by linear_combination p 0 * s1 - u 1 * s2 + e1 - e2
  obtain ⟨a, ha⟩ := hp.2.2
  obtain ⟨b, hb⟩ := hq.2.2
  obtain ⟨a', ha'⟩ := hu.2.2
  obtain ⟨b', hb'⟩ := hv.2.2
  rw [ha, hb, ha', hb'] at key
  have hZ : 2 * a * (2 * b) = (2 * a' + 1) * (2 * b' + 1) := by
    have : ((2 * a * (2 * b) : ℤ) : ℝ) = ((2 * a' + 1) * (2 * b' + 1) : ℤ) := by
      push_cast; linarith
    exact Int.cast_injective this
  have hodd : Odd ((2 * a' + 1) * (2 * b' + 1)) := Odd.mul ⟨a', rfl⟩ ⟨b', rfl⟩
  have heven : Even (2 * a * (2 * b)) := ⟨a * (2 * b), by ring⟩
  rw [hZ] at heven
  exact (Int.not_even_iff_odd.2 hodd) heven
end Erdos654Proof
