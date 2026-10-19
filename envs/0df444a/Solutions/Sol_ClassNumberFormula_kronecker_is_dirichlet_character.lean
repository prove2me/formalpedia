-- Prove2me | solution 1 for ClassNumberFormula.kronecker_is_dirichlet_character
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:52:58.216088+00:00
-- url     : https://prove2.me/submissions/3089f82d-fd3f-4682-b271-a75630a4b996

import Mathlib
import Definitions.Def_ClassNumberFormula_Kronecker

namespace CNKR
open ClassNumberFormula

lemma mk_char (N : ℕ) (hN : 1 < N) (f : ℕ → ℤ) (h1 : f 1 = 1)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hper : ∀ n, f (n % N) = f n)
    (hz : ∀ n, ¬ n.Coprime N → f n = 0) :
    ∃ χ : DirichletCharacter ℂ N, ∀ n : ℕ, χ n = (f n : ℂ) := by
  haveI : Fact (1 < N) := ⟨hN⟩
  let χ : MulChar (ZMod N) ℂ := {
    toFun := fun x => (f x.val : ℂ)
    map_one' := by simp only [ZMod.val_one, h1, Int.cast_one]
    map_mul' := by
      intro x y
      simp only [ZMod.val_mul, hper, hmul, Int.cast_mul]
    map_nonunit' := by
      intro x hx
      have : ¬ x.val.Coprime N := by
        intro hc
        apply hx
        rw [← ZMod.natCast_zmod_val x]
        exact (ZMod.isUnit_iff_coprime x.val N).mpr hc
      simp only [hz _ this, Int.cast_zero] }
  refine ⟨χ, fun n => ?_⟩
  show (f (n : ZMod N).val : ℂ) = f n
  rw [ZMod.val_natCast, hper]

lemma kron_zero (d : ℤ) (hd : d ≠ 1 ∧ d ≠ -1) : kroneckerSymbol d 0 = 0 := by
  simp [kroneckerSymbol, hd.1, hd.2]

lemma kron_pos (d : ℤ) (n : ℕ) (hn : n ≠ 0) :
    kroneckerSymbol d n = kroneckerTwo d ^ (n.factorization 2) * jacobiSym d (ordCompl[2] n) := by
  simp [kroneckerSymbol, hn]

lemma kron_mul (d : ℤ) (hd : d ≠ 1 ∧ d ≠ -1) (a b : ℕ) :
    kroneckerSymbol d (a * b) = kroneckerSymbol d a * kroneckerSymbol d b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [kron_zero d hd]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [kron_zero d hd]
  rw [kron_pos d _ (Nat.mul_ne_zero ha.ne' hb.ne'), kron_pos d _ ha.ne', kron_pos d _ hb.ne',
    Nat.ordCompl_mul, Nat.factorization_mul ha.ne' hb.ne', Finsupp.add_apply, pow_add,
    jacobiSym.mul_right' _ (Nat.ordCompl_pos 2 ha.ne').ne' (Nat.ordCompl_pos 2 hb.ne').ne']
  ring

lemma kron_one (d : ℤ) : kroneckerSymbol d 1 = 1 := by
  rw [kron_pos d 1 one_ne_zero]; simp

lemma ordCompl_odd (n : ℕ) (hn : n ≠ 0) : Odd (ordCompl[2] n) :=
  Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hn))

lemma fact_zero_of_odd (n : ℕ) (hn : n % 2 = 1) : n.factorization 2 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (by omega)

lemma ordCompl_of_odd (n : ℕ) (hn : n % 2 = 1) : ordCompl[2] n = n := by
  rw [fact_zero_of_odd n hn, pow_zero, Nat.div_one]

lemma caseB (m : ℤ) (hm4 : m % 4 = 2 ∨ m % 4 = 3) :
    ∃ χ : DirichletCharacter ℂ (4 * m).natAbs, ∀ n : ℕ,
      χ n = (kroneckerSymbol (4 * m) n : ℂ) := by
  have hm0 : m ≠ 0 := by rintro rfl; omega
  have hd : (4 * m) ≠ 1 ∧ (4 * m) ≠ -1 := ⟨by omega, by omega⟩
  have htwo : kroneckerTwo (4 * m) = 0 := by
    unfold kroneckerTwo
    have : ∀ k : ZMod 8, ZMod.χ₈ (4 * k) = 0 := by decide
    push_cast
    exact_mod_cast this _
  have hform : ∀ n : ℕ, kroneckerSymbol (4 * m) n = if n % 2 = 0 then 0 else jacobiSym m n := by
    intro n
    split_ifs with hn
    · rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact kron_zero _ hd
      · rw [kron_pos _ _ hpos.ne', htwo]
        have : n.factorization 2 ≠ 0 :=
          (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos.ne' (by omega)).ne'
        rw [zero_pow this, zero_mul]
    · have hn1 : n % 2 = 1 := by omega
      rw [kron_pos _ _ (by omega), fact_zero_of_odd n hn1]
      simp only [pow_zero, one_mul, Nat.div_one]
      rw [jacobiSym.mul_left]
      have h4 : jacobiSym 4 n = 1 := by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
        apply jacobiSym.sq_one'
        have : Nat.Coprime 2 n := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hn1)
        simpa [Int.gcd] using this
      rw [h4, one_mul]
  have hN : (4 * m).natAbs = 4 * m.natAbs := by rw [Int.natAbs_mul]; rfl
  rw [hN]
  apply mk_char (4 * m.natAbs) (by have := Int.natAbs_pos.mpr hm0; omega)
    (fun n => kroneckerSymbol (4 * m) n) (kron_one _) (kron_mul _ hd)
  · intro n
    simp only [hform]
    have hpar : n % (4 * m.natAbs) % 2 = n % 2 := by
      rw [Nat.mod_mod_of_dvd n (dvd_mul_of_dvd_left (by norm_num) _)]
    rw [hpar]
    split_ifs with h
    · rfl
    · have hodd : Odd n := Nat.odd_iff.mpr (by omega)
      rw [jacobiSym.mod_right m hodd]
  · intro n hcop
    simp only [hform]
    split_ifs with h
    · rfl
    · rw [jacobiSym.eq_zero_iff]
      refine ⟨by omega, ?_⟩
      intro hg
      apply hcop
      have h1 : Nat.Coprime n m.natAbs := by
        rw [Nat.coprime_comm]; rwa [Int.gcd, Int.natAbs_natCast] at hg
      have h2 : Nat.Coprime n 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by omega)))
      exact Nat.Coprime.mul_right h2 h1

/-- reciprocity for `d ≡ 1 mod 4` (either sign) -/
lemma recip (d : ℤ) (hd : d % 4 = 1) (n : ℕ) (hn : Odd n) :
    jacobiSym d n = jacobiSym n d.natAbs := by
  rcases Int.natAbs_eq d with h | h
  · have he4 : d.natAbs % 4 = 1 := by omega
    conv_lhs => rw [h]
    rw [jacobiSym.quadratic_reciprocity_one_mod_four he4 hn]
  · have he4 : d.natAbs % 4 = 3 := by omega
    conv_lhs => rw [h]
    rw [jacobiSym.neg _ hn, jacobiSym.quadratic_reciprocity (Nat.odd_iff.mpr (by omega)) hn,
      pow_mul, ZMod.neg_one_pow_div_two_of_three_mod_four he4]
    have hn4 : n % 4 = 1 ∨ n % 4 = 3 := by have := Nat.odd_iff.mp hn; omega
    rcases hn4 with h' | h'
    · rw [ZMod.χ₄_nat_one_mod_four h', ZMod.neg_one_pow_div_two_of_one_mod_four h']; ring
    · rw [ZMod.χ₄_nat_three_mod_four h', ZMod.neg_one_pow_div_two_of_three_mod_four h']; ring

lemma chi8_eq (d : ℤ) : ZMod.χ₈ (d : ZMod 8) = ZMod.χ₈ ((d.natAbs : ℕ) : ZMod 8) := by
  have hc : ((d.natAbs : ℕ) : ZMod 8) = (((d.natAbs : ℕ) : ℤ) : ZMod 8) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq d with h | h
  · rw [hc, ← h]
  · have : (((d.natAbs : ℕ) : ℤ) : ZMod 8) = -(d : ZMod 8) := by
      conv_rhs => rw [h]
      push_cast; ring
    rw [hc, this]
    have key : ∀ x : ZMod 8, ZMod.χ₈ (-x) = ZMod.χ₈ x := by decide
    rw [key]

lemma caseA (d : ℤ) (hd4 : d % 4 = 1) (hd1 : d ≠ 1) :
    ∃ χ : DirichletCharacter ℂ d.natAbs, ∀ n : ℕ, χ n = (kroneckerSymbol d n : ℂ) := by
  have hd : d ≠ 1 ∧ d ≠ -1 := ⟨hd1, by rintro rfl; norm_num at hd4⟩
  set e := d.natAbs with he
  have he1 : 1 < e := by
    have : e ≠ 0 := by rw [he]; intro h; rw [Int.natAbs_eq_zero] at h; rw [h] at hd4; norm_num at hd4
    have : e ≠ 1 := by
      rw [he]; intro h
      rcases Int.natAbs_eq_iff.mp h with h' | h' <;> simp_all
    omega
  have heodd : Odd e := by rw [he]; exact Int.natAbs_odd.mpr (Int.odd_iff.mpr (by omega))
  have hform : ∀ n : ℕ, kroneckerSymbol d n = jacobiSym n e := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [kron_zero d hd]; push_cast; rw [jacobiSym.zero_left he1]
    · rw [kron_pos d n hpos.ne']
      have hsplit : n = 2 ^ n.factorization 2 * ordCompl[2] n :=
        (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
      conv_rhs => rw [hsplit]
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_two heodd,
        recip d hd4 _ (ordCompl_odd n hpos.ne'), kroneckerTwo, chi8_eq]
  apply mk_char e he1 (fun n => kroneckerSymbol d n) (kron_one _) (kron_mul _ hd)
  · intro n
    simp only [hform]
    push_cast
    rw [← jacobiSym.mod_left]
  · intro n hcop
    simp only [hform]
    rw [jacobiSym.eq_zero_iff]
    refine ⟨by omega, ?_⟩
    simpa [Int.gcd] using hcop

theorem main (d : ℤ) (hd : IsFundamentalDiscriminant d) :
    ∃ χ : DirichletCharacter ℂ d.natAbs, ∀ n : ℕ, χ n = (kroneckerSymbol d n : ℂ) := by
  obtain ⟨hd1, ⟨hd4, _⟩ | ⟨m, rfl, hm4, _⟩⟩ := hd
  · exact caseA d hd4 hd1
  · exact caseB m hm4

end CNKR

open ClassNumberFormula in
theorem solution (d : ℤ) (hd : IsFundamentalDiscriminant d) :
    ∃ χ : DirichletCharacter ℂ d.natAbs, ∀ n : ℕ, χ n = (kroneckerSymbol d n : ℂ) :=
  CNKR.main d hd
