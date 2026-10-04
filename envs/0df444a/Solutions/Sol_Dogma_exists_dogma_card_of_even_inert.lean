-- Prove2me | solution 1 for Dogma.exists_dogma_card_of_even_inert
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T03:33:45.841851+00:00
-- url     : https://prove2.me/submissions/1cd54ac4-a2eb-4ee0-965c-50777b6cb21b

import Mathlib

set_option autoImplicit false

namespace DogmaGen

structure IsDogma {D : Type} (star : D → D → D) : Prop where
  rc : ∀ x y z : D, star x z = star y z → x = y
  idt : ∀ x y : D, star (star x y) y = star y x

def HasDogma (n : ℕ) : Prop :=
  ∃ (D : Type) (star : D → D → D), Nat.card D = n ∧ IsDogma star

lemma hasDogma_one : HasDogma 1 :=
  ⟨Unit, fun _ _ => (), by simp, ⟨fun _ _ _ _ => Subsingleton.elim _ _, fun _ _ => rfl⟩⟩

lemma hasDogma_mul {a b : ℕ} (ha : HasDogma a) (hb : HasDogma b) : HasDogma (a * b) := by
  obtain ⟨A, sa, hca, da⟩ := ha
  obtain ⟨B, sb, hcb, db⟩ := hb
  refine ⟨A × B, fun x y => (sa x.1 y.1, sb x.2 y.2), ?_, ?_, ?_⟩
  · rw [Nat.card_prod, hca, hcb]
  · intro x y z h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (da.rc _ _ _ h.1) (db.rc _ _ _ h.2)
  · intro x y
    simp only [Prod.mk.injEq]
    exact ⟨da.idt _ _, db.idt _ _⟩

lemma hasDogma_of_ring (R : Type) [CommRing R] (α : R) (h : α ^ 2 + α = 1) :
    HasDogma (Nat.card R) := by
  refine ⟨R, fun x y => α * x + α ^ 2 * y, rfl, ?_, ?_⟩
  · intro x y z hxy
    have h1 : α * x = α * y := by
      have := congrArg (fun t => t - α ^ 2 * z) hxy
      simpa using this
    have h2 : (α + 1) * (α * x) = (α + 1) * (α * y) := by rw [h1]
    have h3 : (α + 1) * α = 1 := by linear_combination h
    calc x = ((α + 1) * α) * x := by rw [h3, one_mul]
      _ = (α + 1) * (α * x) := by ring
      _ = (α + 1) * (α * y) := h2
      _ = ((α + 1) * α) * y := by ring
      _ = y := by rw [h3, one_mul]
  · intro x y
    linear_combination (α * y) * h

/-- Order `m²` for every `m`: the operation `(φ x + φ² y)` on `R × R`, `R = ZMod m`, with `φ² = 1 - φ`. -/
def sqStar {R : Type} [CommRing R] (x y : R × R) : R × R :=
  (x.2 + (y.1 - y.2), x.1 - x.2 + (2 * y.2 - y.1))

lemma isDogma_sqStar (R : Type) [CommRing R] : IsDogma (sqStar (R := R)) := by
  refine ⟨?_, ?_⟩
  · intro x y z h
    simp only [sqStar, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have a2 : x.2 = y.2 := by linear_combination h1
    have a1 : x.1 = y.1 := by linear_combination h2 + a2
    exact Prod.ext a1 a2
  · intro x y
    simp only [sqStar, Prod.mk.injEq]
    constructor <;> ring

lemma hasDogma_sq (m : ℕ) (hm : 0 < m) : HasDogma (m * m) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  refine ⟨ZMod m × ZMod m, sqStar, ?_, isDogma_sqStar (ZMod m)⟩
  rw [Nat.card_prod, Nat.card_zmod]


lemma isSquare_cast_mod5 (p : ℕ) (h : p % 5 = 1 ∨ p % 5 = 4) : IsSquare ((p : ℕ) : ZMod 5) := by
  have hmod : ((p % 5 : ℕ) : ZMod 5) = (p : ZMod 5) := ZMod.natCast_mod p 5
  rcases h with h | h
  · rw [h] at hmod
    rw [← hmod]
    exact ⟨1, by decide⟩
  · rw [h] at hmod
    rw [← hmod]
    exact ⟨2, by decide⟩

lemma hasDogma_five : HasDogma 5 := by
  have := hasDogma_of_ring (ZMod 5) 2 (by decide)
  simpa using this

lemma exists_alpha (p : ℕ) [Fact p.Prime] (h : p % 5 = 1 ∨ p % 5 = 4) :
    ∃ α : ZMod p, α ^ 2 + α = 1 := by
  have hp2 : p ≠ 2 := by omega
  have hsq := isSquare_cast_mod5 p h
  have h5 : IsSquare ((5 : ℕ) : ZMod p) := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) hp2).mp hsq
  obtain ⟨s, hs⟩ := h5
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h2
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    have hp := (Fact.out : p.Prime).two_le
    omega
  refine ⟨(s - 1) / 2, ?_⟩
  push_cast at hs
  field_simp
  linear_combination (-1 : ZMod p) * hs

lemma hasDogma_prime_good (p : ℕ) (hp : p.Prime) (hg : p = 5 ∨ p % 5 = 1 ∨ p % 5 = 4) :
    HasDogma p := by
  rcases hg with rfl | h
  · exact hasDogma_five
  · haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨α, hα⟩ := exists_alpha p h
    have := hasDogma_of_ring (ZMod p) α hα
    simpa using this


lemma fact_mul_apply (a b q : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization q = a.factorization q + b.factorization q := by
  rw [Nat.factorization_mul ha hb]; rfl

lemma fact_prime_apply (p q : ℕ) (hp : p.Prime) :
    p.factorization q = if p = q then 1 else 0 := by
  rw [hp.factorization, Finsupp.single_apply]

theorem hasDogma_of_even_inert :
    ∀ n : ℕ, 0 < n → (∀ p : ℕ, p.Prime → (p % 5 = 2 ∨ p % 5 = 3) → Even (n.factorization p)) →
      HasDogma n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hcrit
    by_cases hn1 : n = 1
    · subst hn1; exact hasDogma_one
    have hp : n.minFac.Prime := Nat.minFac_prime hn1
    obtain ⟨k, hk⟩ := Nat.minFac_dvd n
    set p := n.minFac with hpdef
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0] at hk; omega
      · exact h0
    have hp0 : p ≠ 0 := hp.ne_zero
    by_cases hgood : p = 5 ∨ p % 5 = 1 ∨ p % 5 = 4
    · have hklt : k < n := by
        have := hp.two_le
        nlinarith
      have hkc : ∀ q : ℕ, q.Prime → (q % 5 = 2 ∨ q % 5 = 3) → Even (k.factorization q) := by
        intro q hq hq5
        have hne : p ≠ q := by
          intro h; subst h; omega
        have := hcrit q hq hq5
        rw [hk, fact_mul_apply p k q hp0 hk0.ne', fact_prime_apply p q hp, if_neg hne, zero_add] at this
        exact this
      rw [hk]
      exact hasDogma_mul (hasDogma_prime_good p hp hgood) (ih k hklt hk0 hkc)
    · have hinert : p % 5 = 2 ∨ p % 5 = 3 := by
        have h5 : p % 5 ≠ 0 := by
          intro h0
          have : 5 ∣ p := Nat.dvd_of_mod_eq_zero h0
          have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp this
          omega
        omega
      have hev := hcrit p hp hinert
      have hpos : 0 < n.factorization p :=
        hp.factorization_pos_of_dvd hn.ne' (Nat.minFac_dvd n)
      have h2 : 2 ≤ n.factorization p := by
        obtain ⟨r, hr⟩ := hev
        omega
      have hdvd : p ^ 2 ∣ n := (hp.pow_dvd_iff_le_factorization hn.ne').mpr h2
      obtain ⟨m, hm⟩ := hdvd
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0] at hm; omega
        · exact h0
      have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp0
      have hmlt : m < n := by
        have := hp.two_le
        have h4 : 4 ≤ p ^ 2 := by nlinarith
        nlinarith
      have hmc : ∀ q : ℕ, q.Prime → (q % 5 = 2 ∨ q % 5 = 3) → Even (m.factorization q) := by
        intro q hq hq5
        have := hcrit q hq hq5
        have hpp : (p ^ 2).factorization q = if p = q then 2 else 0 := by
          rw [Nat.factorization_pow, Finsupp.smul_apply, fact_prime_apply p q hp]
          split_ifs <;> simp
        rw [hm, fact_mul_apply (p ^ 2) m q hp2 hm0.ne', hpp] at this
        by_cases hpq : p = q
        · rw [if_pos hpq] at this
          obtain ⟨r, hr⟩ := this
          exact ⟨r - 1, by omega⟩
        · rw [if_neg hpq, zero_add] at this
          exact this
      have hmd := ih m hmlt hm0 hmc
      have : n = p * p * m := by rw [hm]; ring
      rw [this]
      exact hasDogma_mul (hasDogma_sq p hp.pos) hmd

end DogmaGen

theorem solution (n : ℕ) (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → (p % 5 = 2 ∨ p % 5 = 3) → Even (n.factorization p)) :
    ∃ (D : Type) (star : D → D → D), Nat.card D = n ∧
      (∀ x y z : D, star x z = star y z → x = y) ∧
      ∀ x y : D, star (star x y) y = star y x := by
  obtain ⟨D, star, hc, hd⟩ := DogmaGen.hasDogma_of_even_inert n hn h
  exact ⟨D, star, hc, hd.rc, hd.idt⟩


