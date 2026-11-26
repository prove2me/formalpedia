-- Prove2me | solution 1 for Erdos287.cofactor_subset_sums_compress_by_coprime_residues
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T07:32:32.267408+00:00
-- url     : https://prove2.me/submissions/d4cd68c4-a367-4a4e-8b72-9a31ad6588ef

import Mathlib

open Finset

set_option autoImplicit false

/-- The quotient by the common denominator and its coprime residue
coordinates determine a cleared numerator. Each coordinate only sees the
weights that are nonzero in that modulus. -/
theorem solution (U I : Finset ℕ) (q w : ℕ → ℕ) (L : ℕ)
    (hL : L = ∏ i ∈ I, q i) (hq : ∀ i ∈ I, 0 < q i)
    (hcop : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (q i).Coprime (q j))
    (hw : ∀ x ∈ U, w x ≤ L) :
    ∃ F : Finset (Finset ℕ),
      (∀ T ∈ F, T ⊆ U ∧ T.Nonempty) ∧
      (∀ T ⊆ U, T.Nonempty → ∃ V ∈ F, (∑ x ∈ V, w x) = ∑ x ∈ T, w x) ∧
      F.card ≤ (U.card + 1) * ∏ i ∈ I,
        min (q i) (2 ^ (U.filter (fun x => ¬ q i ∣ w x)).card) := by
  classical
  have hL0 : 0 < L := hL.symm ▸ (prod_pos (fun i hi => hq i hi))
  let support (i : ℕ) := U.filter (fun x => ¬ q i ∣ w x)
  let num (T : Finset ℕ) := ∑ x ∈ T, w x
  let residues (i : ℕ) := (support i).powerset.image (fun T => num T % q i)
  let totals := (U.powerset.filter Finset.Nonempty).image num
  have hrepr (z : ℕ) (hz : z ∈ totals) : ∃ T ⊆ U, T.Nonempty ∧ num T = z := by
    obtain ⟨T, ht, he⟩ := mem_image.mp hz
    exact ⟨T, mem_powerset.mp (mem_filter.mp ht).1, (mem_filter.mp ht).2, he⟩
  have hres (T : Finset ℕ) (hTU : T ⊆ U) (i : ℕ) : num T % q i ∈ residues i := by
    let V := T ∩ support i
    have hsub : V ⊆ T := inter_subset_left
    have hdvd : q i ∣ num (T \ V) := by
      apply dvd_sum
      intro x hx
      obtain ⟨hxT, hxV⟩ := mem_sdiff.mp hx
      by_contra hn
      exact hxV (mem_inter.mpr ⟨hxT, mem_filter.mpr ⟨hTU hxT, hn⟩⟩)
    have hs : num (T \ V) + num V = num T := sum_sdiff hsub
    refine mem_image.mpr ⟨V, mem_powerset.mpr inter_subset_right, ?_⟩
    rw [← hs, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, zero_add, Nat.mod_mod]
  let encode (z : ℕ) : ℕ × (∀ i ∈ I, ℕ) := (z / L, fun i _ => z % q i)
  have htarg : Set.MapsTo encode (↑totals : Set ℕ)
      (↑(range (U.card + 1) ×ˢ I.pi residues) : Set _) := by
    intro z hz
    obtain ⟨T, hTU, _, rfl⟩ := hrepr z hz
    refine mem_product.mpr ⟨mem_range.mpr ?_, mem_pi.mpr (fun i _ => hres T hTU i)⟩
    have hnum : num T ≤ L * U.card := calc
        num T ≤ ∑ _ ∈ T, L := sum_le_sum (fun x hx => hw x (hTU hx))
        _ = L * T.card := by simp [mul_comm]
        _ ≤ L * U.card := Nat.mul_le_mul_left _ (card_le_card hTU)
    change num T / L < U.card + 1
    apply Nat.lt_succ_of_le
    exact (Nat.div_le_div_right hnum).trans_eq (Nat.mul_div_cancel_left _ hL0)
  have hinj : Function.Injective encode := by
    intro x y hxy
    have hdiv : (L : ℤ) ∣ (y : ℤ) - (x : ℤ) := by
      rw [hL, Nat.cast_prod]
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
  have hcount (i : ℕ) (hi : i ∈ I) :
      (residues i).card ≤ min (q i) (2 ^ (support i).card) := by
    apply le_min
    · have hsub : residues i ⊆ range (q i) := by
        intro b hb
        obtain ⟨T, _, rfl⟩ := mem_image.mp hb
        exact mem_range.mpr (Nat.mod_lt _ (hq i hi))
      simpa only [card_range] using card_le_card hsub
    · exact card_image_le.trans (by rw [card_powerset])
  have hpi : (I.pi residues).card = ∏ i ∈ I, (residues i).card := Multiset.card_pi _ _
  choose! V hVU hVN hV using hrepr
  let F := totals.image V
  refine ⟨F, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hT
    exact ⟨hVU z hz, hVN z hz⟩
  · intro T hTU hT
    have hz : num T ∈ totals := mem_image.mpr ⟨T, mem_filter.mpr ⟨mem_powerset.mpr hTU, hT⟩, rfl⟩
    exact ⟨V (num T), mem_image.mpr ⟨num T, hz, rfl⟩, hV (num T) hz⟩
  · calc
      F.card ≤ totals.card := card_image_le
      _ ≤ (range (U.card + 1) ×ˢ I.pi residues).card :=
        card_le_card_of_injOn encode htarg hinj.injOn
      _ ≤ (U.card + 1) * ∏ i ∈ I, min (q i) (2 ^ (support i).card) := by
        rw [card_product, card_range, hpi]
        exact Nat.mul_le_mul_left _ (prod_le_prod' hcount)

