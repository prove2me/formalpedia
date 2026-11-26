-- Prove2me | solution 1 for Erdos287.crt_compress_cofactor_sums_by_residue_counts
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T17:39:06.023156+00:00
-- url     : https://prove2.me/submissions/19c785cc-56ef-4754-8ff8-761739517606

import Mathlib

open Finset

set_option autoImplicit false

/-- Explicit residue dictionaries and a bound on the total cleared mass
compress all nonempty subset sums, even when coordinate supports overlap. -/
theorem solution (U I : Finset ℕ) (q w R : ℕ → ℕ) (K : ℕ)
    (hq : ∀ i ∈ I, 0 < q i)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (q i).Coprime (q j))
    (hbound : (∑ x ∈ U, w x) ≤ K * ∏ i ∈ I, q i)
    (hR : ∀ i ∈ I,
      ((U.filter (fun x => ¬ q i ∣ w x)).powerset.image
        (fun T => (∑ x ∈ T, w x) % q i)).card ≤ R i) :
    ∃ F : Finset (Finset ℕ),
      (∀ T ∈ F, T ⊆ U ∧ T.Nonempty) ∧
      (∀ T ⊆ U, T.Nonempty → ∃ V ∈ F, (∑ x ∈ V, w x) = ∑ x ∈ T, w x) ∧
      F.card ≤ (K + 1) * ∏ i ∈ I, R i := by
  classical
  let L := ∏ i ∈ I, q i
  have hL0 : 0 < L := prod_pos (fun i hi => hq i hi)
  let support (i : ℕ) := U.filter (fun x => ¬ q i ∣ w x)
  let num (T : Finset ℕ) := ∑ x ∈ T, w x
  let residues (i : ℕ) := (support i).powerset.image (fun T => num T % q i)
  let totals := (U.powerset.filter Finset.Nonempty).image num
  have hrepr (z : ℕ) (hz : z ∈ totals) : ∃ T ⊆ U, T.Nonempty ∧ num T = z := by
    obtain ⟨T, ht, he⟩ := mem_image.mp hz
    exact ⟨T, mem_powerset.mp (mem_filter.mp ht).1, (mem_filter.mp ht).2, he⟩
  have hres (T : Finset ℕ) (hTU : T ⊆ U) (i : ℕ) : num T % q i ∈ residues i := by
    let V := T ∩ support i
    have hdiv : q i ∣ num (T \ V) := by
      apply dvd_sum
      intro x hx
      obtain ⟨hxT, hxV⟩ := mem_sdiff.mp hx
      by_contra hn
      exact hxV (mem_inter.mpr ⟨hxT, mem_filter.mpr ⟨hTU hxT, hn⟩⟩)
    have hs : num (T \ V) + num V = num T := sum_sdiff inter_subset_left
    refine mem_image.mpr ⟨V, mem_powerset.mpr inter_subset_right, ?_⟩
    rw [← hs, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, zero_add, Nat.mod_mod]
  let encode (z : ℕ) : ℕ × (∀ i ∈ I, ℕ) := (z / L, fun i _ => z % q i)
  have htarget : Set.MapsTo encode (↑totals : Set ℕ)
      (↑(range (K + 1) ×ˢ I.pi residues) : Set _) := by
    intro z hz
    obtain ⟨T, hTU, _, rfl⟩ := hrepr z hz
    refine mem_product.mpr ⟨mem_range.mpr ?_, mem_pi.mpr (fun i _ => hres T hTU i)⟩
    have hnum : num T ≤ K * L := (sum_le_sum_of_subset hTU).trans hbound
    apply Nat.lt_succ_of_le
    exact (Nat.div_le_div_right hnum).trans_eq (Nat.mul_div_cancel K hL0)
  have hinj : Function.Injective encode := by
    intro x y hxy
    have hdiv : (L : ℤ) ∣ (y : ℤ) - (x : ℤ) := by
      unfold L
      rw [Nat.cast_prod]
      refine Finset.prod_dvd_of_coprime ?_ ?_
      · intro i hi j hj hij
        exact Nat.isCoprime_iff_coprime.mpr (hcop i hi j hj hij)
      · intro i hi
        have heq : x % q i = y % q i :=
          congrArg (fun r : ℕ × (∀ j ∈ I, ℕ) => r.2 i hi) hxy
        exact Nat.modEq_iff_dvd.mp heq
    have hmod : x % L = y % L := Nat.modEq_iff_dvd.mpr hdiv
    have hquot : x / L = y / L := congrArg Prod.fst hxy
    calc
      x = x % L + L * (x / L) := (Nat.mod_add_div x L).symm
      _ = y % L + L * (y / L) := by rw [hmod, hquot]
      _ = y := Nat.mod_add_div y L
  choose! V hVU hVN hV using hrepr
  let F := totals.image V
  refine ⟨F, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hT
    exact ⟨hVU z hz, hVN z hz⟩
  · intro T hTU hT
    have hz : num T ∈ totals := mem_image.mpr ⟨T, mem_filter.mpr ⟨mem_powerset.mpr hTU, hT⟩, rfl⟩
    exact ⟨V (num T), mem_image.mpr ⟨num T, hz, rfl⟩, hV (num T) hz⟩
  · have hpi : (I.pi residues).card = ∏ i ∈ I, (residues i).card := Multiset.card_pi _ _
    calc
      F.card ≤ totals.card := card_image_le
      _ ≤ (range (K + 1) ×ˢ I.pi residues).card :=
        card_le_card_of_injOn encode htarget hinj.injOn
      _ ≤ (K + 1) * ∏ i ∈ I, R i := by
        rw [card_product, card_range, hpi]
        exact Nat.mul_le_mul_left _ (prod_le_prod' hR)

