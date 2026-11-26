-- Prove2me | solution 1 for Erdos287.cofactor_translation_residues
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:41:20.677857+00:00
-- url     : https://prove2.me/submissions/29d75a92-41fe-4136-8556-56819383ae86

import Mathlib
import Theorems.Thm_Erdos287_cofactor_cut_congruence

open Finset Polynomial

set_option autoImplicit false

private noncomputable def numeratorPolynomial (p : ℕ) (T : Finset ℕ) : (ZMod p)[X] :=
  ∑ a ∈ T, ∏ b ∈ T.erase a, (X + C (b : ZMod p))

private theorem numeratorPolynomial_bound {p : ℕ} (hp : p.Prime) (T : Finset ℕ)
    (ht : T.Nonempty) (hcard : T.card < p) :
    numeratorPolynomial p T ≠ 0 ∧ (numeratorPolynomial p T).natDegree ≤ T.card - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  let f (b : ℕ) : (ZMod p)[X] := X + C (b : ZMod p)
  let A (a : ℕ) := ∏ b ∈ T.erase a, f b
  have hdegree (a : ℕ) (ha : a ∈ T) : (A a).natDegree = T.card - 1 := by
    change (∏ b ∈ T.erase a, f b).natDegree = T.card - 1
    rw [natDegree_prod_of_monic (T.erase a) f (fun b _ => monic_X_add_C (b : ZMod p))]
    simp only [f, natDegree_X_add_C]
    simp [card_erase_of_mem ha]
  have hmonic (a : ℕ) : (A a).Monic :=
    monic_prod_of_monic _ f (fun b _ => monic_X_add_C (b : ZMod p))
  have hlead (a : ℕ) (ha : a ∈ T) : (A a).coeff (T.card - 1) = 1 := by
    rw [← hdegree a ha, Monic.coeff_natDegree (hmonic a)]
  have hcoeff : (numeratorPolynomial p T).coeff (T.card - 1) = (T.card : ZMod p) := by
    change (∑ a ∈ T, A a).coeff (T.card - 1) = _
    rw [finsetSum_coeff]
    calc
      _ = ∑ _a ∈ T, (1 : ZMod p) := sum_congr rfl hlead
      _ = _ := by simp
  have hneq : (T.card : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff T.card p).mp hz
    exact hcard.not_ge (Nat.le_of_dvd (card_pos.mpr ht) hd)
  refine ⟨fun hz => hneq (hcoeff.symm.trans (by simp [hz])), ?_⟩
  exact natDegree_sum_le_of_forall_le T A (fun a ha => (hdegree a ha).le)

private theorem numeratorPolynomial_eq_zero_of_layer
    (D T : Finset ℕ) (p e c : ℕ) (hp : p.Prime) (he : 1 ≤ e) (hc : 0 < c)
    (hpos : ∀ n ∈ D, 0 < n) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hshape : T.image (fun d => (c + d) * p ^ e) = D.filter (fun n => p ^ e ∣ n)) :
    (numeratorPolynomial p T).eval (c : ZMod p) = 0 := by
  let q := p ^ e
  change T.image (fun d => (c + d) * q) = D.filter (fun n => q ∣ n) at hshape
  have hq : 0 < q := pow_pos hp.pos e
  let L := ∏ d ∈ T, (c + d)
  have hL (n : ℕ) (hn : n ∈ D) (hd : q ∣ n) : n / q ∣ L := by
    have hmem : n ∈ T.image (fun d => (c + d) * q) := hshape.symm ▸ mem_filter.mpr ⟨hn, hd⟩
    obtain ⟨d, hdt, rfl⟩ := mem_image.mp hmem
    rw [Nat.mul_div_cancel _ hq]
    exact dvd_prod_of_mem _ hdt
  have hcong := Erdos287.cofactor_cut_congruence D p e L 0 hp he hpos hsum hL (by simp)
  simp only [zero_add, pow_one] at hcong
  change p ∣ ∑ n ∈ D.filter (fun n => q ∣ n), L / (n / q) at hcong
  rw [← hshape, sum_image (fun a _ b _ hab =>
    Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_right hq hab))] at hcong
  have hterm (d : ℕ) (hd : d ∈ T) :
      L / (((c + d) * q) / q) = ∏ b ∈ T.erase d, (c + b) := by
    rw [Nat.mul_div_cancel _ hq]
    exact Nat.div_eq_of_eq_mul_left (by omega) (prod_erase_mul T (fun b => c + b) hd).symm
  have hdiv : p ∣ ∑ a ∈ T, ∏ b ∈ T.erase a, (c + b) :=
    (sum_congr rfl hterm) ▸ hcong
  have heval : (numeratorPolynomial p T).eval (c : ZMod p) =
      ((∑ a ∈ T, ∏ b ∈ T.erase a, (c + b) : ℕ) : ZMod p) := by
    simp [numeratorPolynomial, eval_finsetSum, eval_prod]
  rw [heval]
  exact (ZMod.natCast_eq_zero_iff _ p).mpr hdiv

/-- A family of allowed prime-power cofactor offset sets can support a
nonempty layer at only a bounded set of translation residues. -/
theorem solution (p : ℕ) (hp : p.Prime) :
  (∀ (D T : Finset ℕ) (e c : ℕ), 1 ≤ e → 0 < c →
    (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
    T.image (fun d => (c + d) * p ^ e) = D.filter (fun n => p ^ e ∣ n) →
    (∑ a ∈ T, ∏ b ∈ T.erase a, ((c : ZMod p) + b)) = 0) ∧
  ∀ (F : Finset (Finset ℕ)), (∀ T ∈ F, T.card < p) →
    ∃ R : Finset (ZMod p),
      R.card ≤ ∑ T ∈ F, (T.card - 1) ∧
      (∀ x : ZMod p, x ∈ R ↔ ∃ T ∈ F, T.Nonempty ∧
        (∑ a ∈ T, ∏ b ∈ T.erase a, (x + (b : ZMod p))) = 0) ∧
      ∀ (D : Finset ℕ) (e c : ℕ), 1 ≤ e → 0 < c →
        (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
        ∀ T ∈ F,
          T.image (fun d => (c + d) * p ^ e) = D.filter (fun n => p ^ e ∣ n) →
          T.Nonempty → (c : ZMod p) ∈ R := by
  constructor
  · intro D T e c he hc hpos hsum hshape
    simpa [numeratorPolynomial, eval_finsetSum, eval_prod] using
      numeratorPolynomial_eq_zero_of_layer D T p e c hp he hc hpos hsum hshape
  intro F hsmall
  classical
  have : Fact p.Prime := ⟨hp⟩
  let G := F.filter Finset.Nonempty
  let Z (T : Finset ℕ) := (numeratorPolynomial p T).roots.toFinset
  let R := G.biUnion Z
  have hTB (T : Finset ℕ) (hT : T ∈ G) :
      numeratorPolynomial p T ≠ 0 ∧ (numeratorPolynomial p T).natDegree ≤ T.card - 1 :=
    numeratorPolynomial_bound hp T (mem_filter.mp hT).2 (hsmall T (mem_filter.mp hT).1)
  have hmem (T : Finset ℕ) (hT : T ∈ G) (x : ZMod p) :
      x ∈ Z T ↔ (∑ a ∈ T, ∏ b ∈ T.erase a, (x + (b : ZMod p))) = 0 := by
    dsimp only [Z]
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (hTB T hT).1]
    simp [Polynomial.IsRoot, numeratorPolynomial, eval_finsetSum, eval_prod]
  refine ⟨R, ?_, ?_, ?_⟩
  · calc
      R.card ≤ ∑ T ∈ G, (Z T).card := card_biUnion_le
      _ ≤ ∑ T ∈ G, (T.card - 1) := sum_le_sum (fun T hT =>
        (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans (hTB T hT).2))
      _ ≤ ∑ T ∈ F, (T.card - 1) := sum_le_sum_of_subset (filter_subset _ _)
  · intro x
    constructor
    · intro hx
      obtain ⟨T, hT, hxT⟩ := mem_biUnion.mp hx
      exact ⟨T, (mem_filter.mp hT).1, (mem_filter.mp hT).2, (hmem T hT x).mp hxT⟩
    · rintro ⟨T, hT, hne, hxT⟩
      have hg : T ∈ G := mem_filter.mpr ⟨hT, hne⟩
      exact mem_biUnion.mpr ⟨T, hg, (hmem T hg x).mpr hxT⟩
  · intro D e c he hc hpos hsum T hT hshape hne
    have hg : T ∈ G := mem_filter.mpr ⟨hT, hne⟩
    have hroot := numeratorPolynomial_eq_zero_of_layer D T p e c hp he hc hpos hsum hshape
    exact mem_biUnion.mpr ⟨T, hg, Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots (hTB T hg).1).mpr hroot)⟩

