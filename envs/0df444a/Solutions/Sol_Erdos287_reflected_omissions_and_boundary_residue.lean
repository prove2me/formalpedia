-- Prove2me | solution 1 for Erdos287.reflected_omissions_and_boundary_residue
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:52:01.200722+00:00
-- url     : https://prove2.me/submissions/fe5d30f1-fae1-4d37-b422-4097f58bb568

import Mathlib

open Finset

set_option autoImplicit false

private theorem inverse_sum_of_reflection (S : Finset ℕ) (m M p : ℕ)
    [Fact p.Prime] (hp : 2 < p) (hcenter : p ∣ m + M)
    (hS : S ⊆ Icc m M) (href : ∀ n ∈ S, m + M - n ∈ S) :
    (∑ n ∈ S, (n : ZMod p)⁻¹) = 0 := by
  let reflect (n : ℕ) := m + M - n
  have hle (n : ℕ) (hn : n ∈ S) : n ≤ m + M := by
    have h := (mem_Icc.mp (hS hn)).2
    omega
  have hback (n : ℕ) (hn : n ∈ S) : reflect (reflect n) = n := by
    have h := hle n hn
    dsimp [reflect]
    omega
  have himage : S.image reflect = S := by
    ext n
    constructor
    · intro hn
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hn
      exact href x hx
    · intro hn
      exact mem_image.mpr ⟨reflect n, href n hn, hback n hn⟩
  have hinj : Set.InjOn reflect (↑S : Set ℕ) := by
    intro a ha b hb h
    rw [← hback a ha, ← hback b hb, h]
  have hflip (n : ℕ) (hn : n ∈ S) : (reflect n : ZMod p) = -(n : ZMod p) := by
    have hnat : reflect n + n = m + M := Nat.sub_add_cancel (hle n hn)
    apply eq_neg_of_add_eq_zero_left
    rw [← Nat.cast_add, hnat]
    exact (ZMod.natCast_eq_zero_iff (m + M) p).mpr hcenter
  let v : ZMod p := ∑ n ∈ S, (n : ZMod p)⁻¹
  have hneg : v = -v := calc
    v = ∑ n ∈ S.image reflect, (n : ZMod p)⁻¹ := by rw [himage]
    _ = ∑ n ∈ S, (reflect n : ZMod p)⁻¹ := by rw [sum_image hinj]
    _ = ∑ n ∈ S, -((n : ZMod p)⁻¹) := sum_congr rfl fun n hn => by rw [hflip n hn, inv_neg]
    _ = -v := by rw [sum_neg_distrib]
  have htwo : (2 : ZMod p) ≠ 0 := by
    have hd : ¬ p ∣ 2 := fun h => (not_le_of_gt hp) (Nat.le_of_dvd (by decide) h)
    simpa using (ZMod.natCast_eq_zero_iff 2 p).not.mpr hd
  have hz : (2 : ZMod p) * v = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp hneg
  exact (mul_eq_zero.mp hz).resolve_left htwo

/-- On a reflected interval, symmetric omitted pairs cancel. The inverse
sum of the unmatched omissions minus the selected sum outside the interval
is the negative of the full selected inverse sum. -/
theorem solution (D : Finset ℕ) (m M p : ℕ) (hp : p.Prime) (hodd : 2 < p)
    (hcenter : p ∣ m + M) :
    let U := (Finset.Icc m M).filter (fun n => ¬ p ∣ n)
    let H := U \ D
    let R := D \ U
    (∑ n ∈ H, (n : ZMod p)⁻¹) - (∑ n ∈ R, (n : ZMod p)⁻¹) =
        -(∑ n ∈ D, (n : ZMod p)⁻¹) ∧
      (∑ n ∈ H.filter (fun n => m + M - n ∉ H), (n : ZMod p)⁻¹) -
        (∑ n ∈ R, (n : ZMod p)⁻¹) = -(∑ n ∈ D, (n : ZMod p)⁻¹) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  intro U H R
  let reflect (n : ℕ) := m + M - n
  let inv (n : ℕ) := (n : ZMod p)⁻¹
  have hUsub : U ⊆ Icc m M := filter_subset _ _
  have hHI : H ⊆ Icc m M := (sdiff_subset : H ⊆ U).trans hUsub
  have hstep (n : ℕ) (hn : n ∈ U) : reflect n ∈ U := by
    obtain ⟨hint, hu⟩ := mem_filter.mp hn
    obtain ⟨hlow, hhigh⟩ := mem_Icc.mp hint
    have heq : reflect n + n = m + M := Nat.sub_add_cancel (by omega)
    refine mem_filter.mpr ⟨mem_Icc.mpr (by dsimp [reflect]; omega), ?_⟩
    intro hd
    apply hu
    exact (Nat.dvd_add_right hd).mp (heq.symm ▸ hcenter)
  have hU0 := inverse_sum_of_reflection U m M p hodd hcenter hUsub hstep
  let J := D ∩ U
  have hUdiff : U \ J = H := by
    ext n
    by_cases hn : n ∈ U <;> simp [J, H, hn]
  have hDdiff : D \ J = R := by
    ext n
    by_cases hn : n ∈ D <;> simp [J, R, hn]
  have hHS : (∑ n ∈ H, inv n) + ∑ n ∈ J, inv n = 0 := by
    have h := sum_sdiff (f := inv) (show J ⊆ U from inter_subset_right)
    rw [hUdiff] at h
    exact h.trans hU0
  have hRS : (∑ n ∈ R, inv n) + ∑ n ∈ J, inv n = ∑ n ∈ D, inv n := by
    have h := sum_sdiff (f := inv) (show J ⊆ D from inter_subset_left)
    rw [hDdiff] at h
    exact h
  have hHneg : (∑ n ∈ H, inv n) - (∑ n ∈ R, inv n) = -(∑ n ∈ D, inv n) := calc
    _ = ((∑ n ∈ H, inv n) + ∑ n ∈ J, inv n) -
        ((∑ n ∈ R, inv n) + ∑ n ∈ J, inv n) := by ring
    _ = _ := by rw [hHS, hRS, zero_sub]
  refine ⟨hHneg, ?_⟩
  let symmetric := H.filter (fun n => reflect n ∈ H)
  have hsym_sub : symmetric ⊆ Icc m M := (filter_subset _ _).trans hHI
  have hsym_ref (n : ℕ) (hn : n ∈ symmetric) : reflect n ∈ symmetric := by
    obtain ⟨hnH, hrefH⟩ := mem_filter.mp hn
    have hnI := (mem_Icc.mp (hHI hnH)).2
    exact mem_filter.mpr ⟨hrefH, by
      have hback : reflect (reflect n) = n := by dsimp [reflect]; omega
      simpa only [hback] using hnH⟩
  have hsym0 := inverse_sum_of_reflection symmetric m M p hodd hcenter hsym_sub hsym_ref
  have hsplit := sum_filter_add_sum_filter_not H (fun n => reflect n ∈ H) inv
  rw [show H.filter (fun n => reflect n ∈ H) = symmetric from rfl, hsym0, zero_add] at hsplit
  change (∑ n ∈ H.filter (fun n => ¬ reflect n ∈ H), inv n) - (∑ n ∈ R, inv n) =
    -(∑ n ∈ D, inv n)
  exact (congrArg (fun z : ZMod p => z - ∑ n ∈ R, inv n) hsplit).trans hHneg

