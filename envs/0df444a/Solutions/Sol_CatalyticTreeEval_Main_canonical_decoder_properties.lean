-- Prove2me | solution 1 for CatalyticTreeEval.Main.canonical_decoder_properties
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T02:29:13.829367+00:00
-- url     : https://prove2.me/submissions/753acb83-68be-4cf8-aa7c-ca09caed058f

import Definitions.Def_CatalyticTreeEval_DecoderCRT

set_option autoImplicit false



set_option autoImplicit false

namespace CatalyticTreeEval.CRT

theorem modulus_pos {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p) :
    0 < Main.modulus p := by
  exact Finset.prod_pos (fun i _ => (hp.2.1 i).pos)

theorem project_val {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    (z : ZMod (Main.modulus p)) (i : Fin t) : project p i z = (z.val : ZMod (p i)) := by
  letI : NeZero (Main.modulus p) := ⟨(modulus_pos p hp).ne'⟩
  exact ZMod.cast_eq_val z

theorem project_crtLift {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    (y : (i : Fin t) → ZMod (p i)) (i : Fin t) :
    project p i (crtLift p hp y) = y i := by
  letI : NeZero (p i) := ⟨(hp.2.1 i).ne_zero⟩
  change project p i (((crtRepresentative p hp y).val : ℕ) : ZMod (Main.modulus p)) = y i
  rw [map_natCast]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).2
    ((crtRepresentative p hp y).property i (Finset.mem_univ i))).trans (ZMod.natCast_zmod_val (y i))

theorem project_eq_natCast_iff {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    (z : ZMod (Main.modulus p)) (i : Fin t) (n : ℕ) (hn : n < p i) :
    project p i z = (n : ZMod (p i)) ↔ z.val % p i = n := by
  rw [project_val p hp, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hn]

theorem mem_canonical_iff {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    (z : ZMod (Main.modulus p)) :
    z ∈ Main.canonical p (Main.modulus p) ↔ ∀ i, project p i z = 0 ∨ project p i z = 1 := by
  change (∀ i, z.val % p i = 0 ∨ z.val % p i = 1) ↔ _
  constructor
  · intro h i
    simpa only [← project_eq_natCast_iff p hp z i 0 (hp.2.1 i).pos,
      ← project_eq_natCast_iff p hp z i 1 (hp.2.1 i).one_lt, Nat.cast_zero, Nat.cast_one] using h i
  · intro h i
    rcases h i with hi | hi
    · exact Or.inl ((project_eq_natCast_iff p hp z i 0 (hp.2.1 i).pos).1
        (by simpa only [Nat.cast_zero] using hi))
    · exact Or.inr ((project_eq_natCast_iff p hp z i 1 (hp.2.1 i).one_lt).1
        (by simpa only [Nat.cast_one] using hi))

theorem project_eq_zero {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    (z : ZMod (Main.modulus p)) (hz : ∀ i, project p i z = 0) : z = 0 := by
  letI : NeZero (Main.modulus p) := ⟨(modulus_pos p hp).ne'⟩
  have hco : (List.finRange t).Pairwise (fun i j => Nat.Coprime (p i) (p j)) := by
    apply (List.nodup_finRange t).pairwise_of_forall_ne
    intro i hi j hj hij
    exact (Nat.coprime_primes (hp.2.1 i) (hp.2.1 j)).2 (fun h => hij (hp.2.2 h))
  have hdiv : ∀ i, p i ∣ z.val := by
    intro i
    apply (ZMod.natCast_eq_zero_iff z.val (p i)).1
    rw [← project_val p hp]
    exact hz i
  have hmod : z.val ≡ 0 [MOD Main.modulus p] := by
    have hmod' := (Nat.modEq_list_map_prod_iff hco).2
      (fun i _ => Nat.modEq_zero_iff_dvd.2 (hdiv i))
    have hprod : Main.modulus p = ((List.finRange t).map p).prod := Fin.prod_univ_def p
    exact Eq.mpr (congrArg (fun n : ℕ => Nat.ModEq n z.val 0) hprod) hmod'
  have hcast : (z.val : ZMod (Main.modulus p)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (Nat.modEq_zero_iff_dvd.1 hmod)
  simpa only [ZMod.natCast_zmod_val] using hcast

theorem project_injective {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    {a b : ZMod (Main.modulus p)} (h : ∀ i, project p i a = project p i b) : a = b := by
  apply sub_eq_zero.mp
  apply project_eq_zero p hp
  intro i
  rw [map_sub, h i, sub_self]

end CatalyticTreeEval.CRT


set_option autoImplicit false

namespace CatalyticTreeEval.DecoderConstruction

theorem localTerm_sum {R : Type} [CommRing R] [DecidableEq R] (z : R) :
    ∑ c : Fin 3, localTerm c z =
      -(if z = -2 then 1 else 0) +
      ((if z = 0 then 1 else 0) + (if z = -1 then 1 else 0)) -
      (if z = 1 then 1 else 0) := by
  classical
  simp [Fin.sum_univ_succ, localTerm]
  ring

theorem local_normalization {R : Type} [CommRing R] [DecidableEq R]
    (h1 : (1 : R) ≠ 0) (h2 : (2 : R) ≠ 0) :
    ∑ c : Fin 3, localTerm c (0 : R) = 1 := by
  classical
  rw [localTerm_sum]
  have hneg1 : (0 : R) ≠ -1 := by
    intro h
    apply h1
    linear_combination h
  have hneg2 : (0 : R) ≠ -2 := by
    intro h
    apply h2
    linear_combination h
  simp [hneg1, hneg2, Ne.symm h1]

theorem local_cancel_one {R : Type} [CommRing R] [DecidableEq R] (z : R) :
    ∑ c : Fin 3, localTerm c (z + (c.val : R)) = 0 := by
  classical
  have h1 : z + 1 = 0 ↔ z = -1 := by
    constructor <;> intro h <;> linear_combination h
  have h2 : z + 1 = -1 ↔ z = -2 := by
    constructor <;> intro h <;> linear_combination h
  have h3 : z + 2 = 1 ↔ z = -1 := by
    constructor <;> intro h <;> linear_combination h
  norm_num [Fin.sum_univ_succ, localTerm]
  simp only [h1, h2, h3]
  ring

theorem local_cancel_two {R : Type} [CommRing R] [DecidableEq R] (z : R) :
    ∑ c : Fin 3, localTerm c (z + 2 * (c.val : R)) = 0 := by
  classical
  have h1 : z + 2 = 0 ↔ z = -2 := by
    constructor <;> intro h <;> linear_combination h
  have h2 : z + 2 = -1 ↔ z = -3 := by
    constructor <;> intro h <;> linear_combination h
  have h3 : z + 4 = 1 ↔ z = -3 := by
    constructor <;> intro h <;> linear_combination h
  norm_num [Fin.sum_univ_succ, localTerm]
  simp only [h1, h2, h3]
  ring

end CatalyticTreeEval.DecoderConstruction


set_option autoImplicit false

namespace CatalyticTreeEval.DecoderConstruction

theorem ternaryIndex_digit (t : ℕ) (j : Fin (3 ^ t)) (i : Fin t) :
    (ternaryIndex t j i).val = j.val / 3 ^ i.val % 3 := rfl

theorem ternaryIndex_rank (t : ℕ) (β : Fin t → Fin 3) :
    ((ternaryIndex t).symm β).val = ∑ i, (β i).val * 3 ^ i.val :=
  finFunctionFinEquiv_apply β

theorem tensorValue_sum {t m : ℕ} {p : Fin t → ℕ}
    (proj : (i : Fin t) → ZMod m →+* ZMod (p i))
    (lift : ((i : Fin t) → ZMod (p i)) → ZMod m)
    (hlift : ∀ y i, proj i (lift y) = y i) (a z : ZMod m) :
    ∑ β : Fin t → Fin 3,
      tensorValue proj β (z + a * lift (fun i => ((β i).val : ZMod (p i)))) =
    ∏ i, ∑ c : Fin 3, localTerm c (proj i z + proj i a * (c.val : ZMod (p i))) := by
  classical
  unfold tensorValue
  simp only [map_add, map_mul, hlift]
  exact (Fintype.prod_sum (fun i : Fin t => fun c : Fin 3 =>
    localTerm c (proj i z + proj i a * (c.val : ZMod (p i))))).symm

theorem tensorDecoder_sum {t m : ℕ} {p : Fin t → ℕ}
    (proj : (i : Fin t) → ZMod m →+* ZMod (p i))
    (lift : ((i : Fin t) → ZMod (p i)) → ZMod m)
    (hlift : ∀ y i, proj i (lift y) = y i) (a z : ZMod m) :
    ∑ j, (tensorDecoder proj lift).term j (z + a * (tensorDecoder proj lift).shift j) =
      ((∏ i, ∑ c : Fin 3,
        localTerm c (proj i z + proj i a * (c.val : ZMod (p i)))) : ℤ) := by
  classical
  change (∑ j : Fin (3 ^ t),
    (tensorValue proj (ternaryIndex t j)
      (z + a * lift (fun i => ((ternaryIndex t j i).val : ZMod (p i)))) : ZMod m)) = _
  rw [← Int.cast_sum]
  apply congrArg (fun n : ℤ => (n : ZMod m))
  calc
    _ = ∑ β : Fin t → Fin 3,
        tensorValue proj β (z + a * lift (fun i => ((β i).val : ZMod (p i)))) :=
      (ternaryIndex t).sum_comp (fun β =>
        tensorValue proj β (z + a * lift (fun i => ((β i).val : ZMod (p i)))))
    _ = _ := tensorValue_sum proj lift hlift a z

/-- The tensor construction only needs a local nonzero score in {1,2} to
annihilate the global decoder sum. -/
theorem tensorDecoder_cancel {t m : ℕ} {p : Fin t → ℕ}
    (proj : (i : Fin t) → ZMod m →+* ZMod (p i))
    (lift : ((i : Fin t) → ZMod (p i)) → ZMod m)
    (hlift : ∀ y i, proj i (lift y) = y i)
    (a z : ZMod m) (ha : ∃ i, proj i a = 1 ∨ proj i a = 2) :
    ∑ j, (tensorDecoder proj lift).term j (z + a * (tensorDecoder proj lift).shift j) = 0 := by
  classical
  rw [tensorDecoder_sum proj lift hlift]
  obtain ⟨i, hi⟩ := ha
  have hz : (∑ c : Fin 3,
      localTerm c (proj i z + proj i a * (c.val : ZMod (p i)))) = 0 := by
    rcases hi with hi | hi
    · simpa [hi] using local_cancel_one (proj i z)
    · simpa [hi] using local_cancel_two (proj i z)
  have hp : (∏ j, ∑ c : Fin 3,
      localTerm c (proj j z + proj j a * (c.val : ZMod (p j)))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hz
  simp [hp]

theorem tensorDecoder_normalization {t m : ℕ} {p : Fin t → ℕ}
    (proj : (i : Fin t) → ZMod m →+* ZMod (p i))
    (lift : ((i : Fin t) → ZMod (p i)) → ZMod m)
    (hlift : ∀ y i, proj i (lift y) = y i)
    (hodd : ∀ i, (1 : ZMod (p i)) ≠ 0 ∧ (2 : ZMod (p i)) ≠ 0) :
    ∑ j, (tensorDecoder proj lift).term j 0 = 1 := by
  classical
  have h := tensorDecoder_sum proj lift hlift (0 : ZMod m) 0
  simp only [zero_mul, zero_add, map_zero, add_zero] at h
  rw [h]
  have hp : (∏ i, ∑ c : Fin 3, localTerm c (0 : ZMod (p i))) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    exact local_normalization (hodd i).1 (hodd i).2
  simp [hp]

/-- Correctness of the complete 3^t-term decoder from its CRT interface and
the source's local score condition. -/
theorem tensorDecoder_isDecoder {t m : ℕ} {p : Fin t → ℕ}
    (proj : (i : Fin t) → ZMod m →+* ZMod (p i))
    (lift : ((i : Fin t) → ZMod (p i)) → ZMod m)
    (hlift : ∀ y i, proj i (lift y) = y i)
    (hodd : ∀ i, (1 : ZMod (p i)) ≠ 0 ∧ (2 : ZMod (p i)) ≠ 0)
    (A : Set (ZMod m)) (hzero : 0 ∈ A)
    (hdetect : ∀ a ∈ A, a ≠ 0 → ∃ i, proj i a = 1 ∨ proj i a = 2) :
    Main.IsDecoder A (tensorDecoder proj lift) := by
  refine ⟨hzero, ?_, tensorDecoder_normalization proj lift hlift hodd⟩
  intro a ha hne z
  exact tensorDecoder_cancel proj lift hlift a z (hdetect a ha hne)

end CatalyticTreeEval.DecoderConstruction


set_option autoImplicit false

namespace CatalyticTreeEval.DecoderConstruction

open CatalyticTreeEval.CRT

/-- CRT identifies the canonical sumset with componentwise residues 0, 1, 2. -/
theorem mem_sumset_canonical_iff_project {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p)
    (a : ZMod (Main.modulus p)) :
    a ∈ Main.sumset (Main.canonical p (Main.modulus p)) ↔
      ∀ i, project p i a = 0 ∨ project p i a = 1 ∨ project p i a = 2 := by
  classical
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩ i
    have hxi := (mem_canonical_iff p hp x).1 hx i
    have hyi := (mem_canonical_iff p hp y).1 hy i
    rw [map_add]
    rcases hxi with hx | hx <;> rcases hyi with hy | hy
    · exact Or.inl (by simp [hx, hy])
    · exact Or.inr (Or.inl (by simp [hx, hy]))
    · exact Or.inr (Or.inl (by simp [hx, hy]))
    · exact Or.inr (Or.inr (by simp [hx, hy]; ring))
  · intro h
    let u : (i : Fin t) → ZMod (p i) := fun i => if project p i a = 0 then 0 else 1
    let v : (i : Fin t) → ZMod (p i) := fun i =>
      if project p i a = 0 then 0 else if project p i a = 1 then 0 else 1
    refine ⟨crtLift p hp u, ?_, crtLift p hp v, ?_, ?_⟩
    · apply (mem_canonical_iff p hp _).2
      intro i
      rw [project_crtLift]
      dsimp [u]
      split <;> simp
    · apply (mem_canonical_iff p hp _).2
      intro i
      rw [project_crtLift]
      by_cases h0 : project p i a = 0
      · exact Or.inl (by simp [v, h0])
      by_cases h1 : project p i a = 1
      · exact Or.inl (by simp [v, h0, h1])
      exact Or.inr (by simp [v, h0, h1])
    · apply project_injective p hp
      intro i
      rw [map_add, project_crtLift, project_crtLift]
      dsimp [u, v]
      by_cases h0 : project p i a = 0
      · simp [h0]
      by_cases h1 : project p i a = 1
      · simp [h0, h1]
      have h2 : project p i a = 2 := by rcases h i with h | h | h <;> simp_all
      simp only [if_neg h0, if_neg h1]
      norm_num [h2]

theorem oddPrime_gt_two {p : ℕ} (hp : Nat.Prime p) (hodd : Odd p) : 2 < p := by
  have hne : p ≠ 2 := by
    intro h
    obtain ⟨k, hk⟩ := hodd
    omega
  have := hp.two_le
  omega

theorem small_natCast_ne_zero {p n : ℕ} (hn : 0 < n) (hlt : n < p) : (n : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).1 h
  have := Nat.le_of_dvd hn hd
  omega

theorem canonical_decoder_correct {t : ℕ} (p : Fin t → ℕ) (hp : Main.OddPrimeData p) :
    Main.IsDecoder (Main.sumset (Main.canonical p (Main.modulus p)))
      (canonicalDecoder p hp.1) := by
  classical
  apply tensorDecoder_isDecoder (project p) (crtLift p hp.1) (project_crtLift p hp.1)
  · intro i
    have hpi := oddPrime_gt_two (hp.1.2.1 i) (hp.2 i)
    exact ⟨by simpa using small_natCast_ne_zero (p := p i) (n := 1) (by omega) (by omega),
      by simpa using small_natCast_ne_zero (p := p i) (n := 2) (by omega) hpi⟩
  · refine ⟨0, ?_, 0, ?_, by simp⟩ <;> simp [Main.canonical]
  · intro a ha hne
    have hscore := (mem_sumset_canonical_iff_project p hp.1 a).1 ha
    by_contra h
    push_neg at h
    apply hne
    apply project_eq_zero p hp.1
    intro i
    rcases hscore i with hi | hi | hi
    · exact hi
    · exact False.elim ((h i).1 hi)
    · exact False.elim ((h i).2 hi)

end CatalyticTreeEval.DecoderConstruction


set_option autoImplicit false

namespace CatalyticTreeEval.DecoderConstruction

open CatalyticTreeEval.CRT

theorem modulus_gt_one {t : ℕ} (p : Fin t → ℕ) (hp : Main.PrimeData p) :
    1 < Main.modulus p := by
  let i : Fin t := ⟨0, hp.1⟩
  have hdiv : p i ∣ Main.modulus p := Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  exact (hp.2.1 i).one_lt.trans_le (Nat.le_of_dvd (modulus_pos p hp) hdiv)

theorem canonical_noncancelling {t : ℕ} (p : Fin t → ℕ) (hp : Main.OddPrimeData p) :
    Main.Noncancelling (Main.canonical p (Main.modulus p)) := by
  intro x hx y hy hsum
  have hlocal : ∀ i, project p i x = 0 ∧ project p i y = 0 := by
    intro i
    have hpi := oddPrime_gt_two (hp.1.2.1 i) (hp.2 i)
    have h1 : (1 : ZMod (p i)) ≠ 0 := by
      simpa using small_natCast_ne_zero (p := p i) (n := 1) (by omega) (by omega)
    have h2 : (2 : ZMod (p i)) ≠ 0 := by
      simpa using small_natCast_ne_zero (p := p i) (n := 2) (by omega) hpi
    have hzero : project p i x + project p i y = 0 := by
      rw [← map_add, hsum, map_zero]
    rcases (mem_canonical_iff p hp.1 x).1 hx i with hxi | hxi <;>
      rcases (mem_canonical_iff p hp.1 y).1 hy i with hyi | hyi
    · exact ⟨hxi, hyi⟩
    · exfalso
      apply h1
      simpa [hxi, hyi] using hzero
    · exfalso
      apply h1
      simpa [hxi, hyi] using hzero
    · exfalso
      apply h2
      simpa only [hxi, hyi, one_add_one_eq_two] using hzero
  exact ⟨project_eq_zero p hp.1 x (fun i => (hlocal i).1),
    project_eq_zero p hp.1 y (fun i => (hlocal i).2)⟩

theorem mem_sumset_canonical_iff {t : ℕ} (p : Fin t → ℕ) (hp : Main.OddPrimeData p)
    (a : ZMod (Main.modulus p)) :
    a ∈ Main.sumset (Main.canonical p (Main.modulus p)) ↔
      ∀ i, a.val % p i = 0 ∨ a.val % p i = 1 ∨ a.val % p i = 2 := by
  rw [mem_sumset_canonical_iff_project p hp.1]
  apply forall_congr'
  intro i
  have hpi := oddPrime_gt_two (hp.1.2.1 i) (hp.2 i)
  constructor
  · rintro (h | h | h)
    · exact Or.inl ((project_eq_natCast_iff p hp.1 a i 0 (by omega)).1
        (by simpa only [Nat.cast_zero] using h))
    · exact Or.inr (Or.inl ((project_eq_natCast_iff p hp.1 a i 1 (by omega)).1
        (by simpa only [Nat.cast_one] using h)))
    · exact Or.inr (Or.inr ((project_eq_natCast_iff p hp.1 a i 2 hpi).1
        (by simpa only [Nat.cast_ofNat] using h)))
  · rintro (h | h | h)
    · exact Or.inl (by simpa only [Nat.cast_zero] using
        (project_eq_natCast_iff p hp.1 a i 0 (by omega)).2 h)
    · exact Or.inr (Or.inl (by simpa only [Nat.cast_one] using
        (project_eq_natCast_iff p hp.1 a i 1 (by omega)).2 h))
    · exact Or.inr (Or.inr (by simpa only [Nat.cast_ofNat] using
        (project_eq_natCast_iff p hp.1 a i 2 hpi).2 h))

/-- The full algebraic content of Lemma 3.19: the decoder is explicit and has
exactly `3^t` slots, and the canonical sumset has the source's residue description.
Only the timed printing claim remains to complete the published milestone. -/
theorem canonical_decoder_algebra {t : ℕ} (p : Fin t → ℕ) (hp : Main.OddPrimeData p) :
    ∃ (k : ℕ) (D : Main.Decoder (Main.modulus p) k), k ≤ 3 ^ t ∧
      (∀ z : ZMod (Main.modulus p), z ∈ Main.sumset (Main.canonical p (Main.modulus p)) ↔
        ∀ i, z.val % p i = 0 ∨ z.val % p i = 1 ∨ z.val % p i = 2) ∧
      Main.IsDecoder (Main.sumset (Main.canonical p (Main.modulus p))) D :=
  ⟨3 ^ t, canonicalDecoder p hp.1, le_rfl, mem_sumset_canonical_iff p hp,
    canonical_decoder_correct p hp⟩

end CatalyticTreeEval.DecoderConstruction


open CatalyticTreeEval.Main CatalyticTreeEval.DecoderConstruction

theorem solution {t : ℕ} (p : Fin t → ℕ) (hp : OddPrimeData p) :
    (∀ z : ZMod (modulus p), z ∈ sumset (canonical p (modulus p)) ↔
      ∀ i, z.val % p i = 0 ∨ z.val % p i = 1 ∨ z.val % p i = 2) ∧
    IsDecoder (sumset (canonical p (modulus p))) (canonicalDecoder p hp.1) ∧
    Noncancelling (canonical p (modulus p)) :=
  ⟨mem_sumset_canonical_iff p hp, canonical_decoder_correct p hp, canonical_noncancelling p hp⟩
