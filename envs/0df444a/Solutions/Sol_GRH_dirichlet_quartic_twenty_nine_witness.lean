-- Prove2me | solution 1 for GRH.dirichlet_quartic_twenty_nine_witness
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:45:55.780106+00:00
-- url     : https://prove2.me/submissions/35e3161e-ee5b-441a-bd80-18c7bf182c98

import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Complex
open scoped ComplexConjugate

private abbrev GPair := ℤ × ℤ
private def zval (u : GPair) : ℂ := ⟨u.1,u.2⟩
private def gmul (a b : GPair) : GPair := (a.1*b.1-a.2*b.2,a.1*b.2+a.2*b.1)
private lemma zmul (a b : GPair) : zval (gmul a b)=zval a*zval b := by
  apply Complex.ext <;> simp [zval,gmul,Complex.mul_re,Complex.mul_im]

private def table : Array GPair := #[⟨0,0⟩, ⟨1,0⟩, ⟨0,1⟩, ⟨0,1⟩, ⟨-1,0⟩, ⟨-1,0⟩, ⟨-1,0⟩, ⟨1,0⟩, ⟨0,-1⟩, ⟨-1,0⟩, ⟨0,-1⟩, ⟨0,1⟩,
  ⟨0,-1⟩, ⟨-1,0⟩, ⟨0,1⟩, ⟨0,-1⟩, ⟨1,0⟩, ⟨0,1⟩, ⟨0,-1⟩, ⟨0,1⟩, ⟨1,0⟩, ⟨0,1⟩, ⟨-1,0⟩, ⟨1,0⟩,
  ⟨1,0⟩, ⟨1,0⟩, ⟨0,-1⟩, ⟨0,-1⟩, ⟨-1,0⟩]
private def coeff29 (a : ZMod 29) : GPair := (table[a.val]?).getD 0
private def logTable : Array ℕ := #[0, 0, 1, 5, 2, 22, 6, 12, 3, 10, 23, 25,
  7, 18, 13, 27, 4, 21, 11, 9, 24, 17, 26, 20,
  8, 16, 19, 15, 14]
private lemma logs : ∀ a : ZMod 29, a≠0 → (2:ZMod 29)^((logTable[a.val]?).getD 0)=a := by decide +kernel
private theorem productTable : ∀ a b : ZMod 29, coeff29 (a*b)=gmul (coeff29 a) (coeff29 b) := by
  decide +kernel

private noncomputable def gamma : DirichletCharacter ℂ 29 where
  toFun := fun a => zval (coeff29 a)
  map_one' := by change zval (1,0)=1;apply Complex.ext <;> norm_num [zval]
  map_mul' := fun a b => by rw [productTable a b,zmul]
  map_nonunit' := by
    intro a ha
    have e : a=0 := by
      by_contra h
      have nz : a.val≠0 := by intro he;apply h;rw [← ZMod.natCast_zmod_val a,he];rfl
      have cop : ∀ r : Fin 29, r.val≠0 → r.val.Coprime 29 := by decide +kernel
      have um := (ZMod.isUnit_iff_coprime a.val 29).2 (cop ⟨a.val,ZMod.val_lt a⟩ nz)
      exact ha (by simpa only [ZMod.natCast_zmod_val] using um)
    subst a
    change zval (0,0)=0
    apply Complex.ext <;> norm_num [zval]

private lemma determined (χ η : DirichletCharacter ℂ 29) (h : χ 2=η 2) : χ=η := by
  apply DFunLike.ext
  intro a
  by_cases ha : a=0
  · subst a
    have hzero : ¬ IsUnit (0 : ZMod 29) := by decide
    rw [MulChar.map_nonunit χ hzero,MulChar.map_nonunit η hzero]
  · have e := logs a ha
    conv_lhs => rw [← e,map_pow,h]
    rw [← map_pow,e]

/-- Exactly two primitive characters at conductor 29 send two to i or minus i.
They are distinct inverses of each other. -/
theorem solution : ∃ χ : DirichletCharacter ℂ 29, χ.IsPrimitive ∧ χ 2=Complex.I ∧
    χ⁻¹.IsPrimitive ∧ χ⁻¹ 2= -Complex.I ∧ χ≠χ⁻¹ ∧
    ∀ ψ : DirichletCharacter ℂ 29, (ψ 2=Complex.I ∨ ψ 2= -Complex.I) ↔ (ψ=χ ∨ ψ=χ⁻¹) := by
  let χ := gamma
  have hval : χ 2=I := by
    change zval (0,1)=I
    apply Complex.ext <;> norm_num [zval]
  have hinv : χ⁻¹ 2= -I := by rw [← MulChar.star_apply'];change conj (χ 2)= -I; rw [hval,conj_I]
  have hne : χ≠1 := by
    intro e
    rw [e,MulChar.one_apply (x:=(2:ZMod 29)) ((ZMod.isUnit_iff_coprime 2 29).2 (by decide))] at hval
    simpa using congrArg Complex.im hval
  have prime : Nat.Prime 29 := by decide
  have hprim : χ.IsPrimitive := ((Nat.dvd_prime prime).1 (DirichletCharacter.conductor_dvd_level χ)).resolve_left
    (fun h => hne (DirichletCharacter.eq_one_iff_conductor_eq_one.2 h))
  have pinv : χ⁻¹.IsPrimitive := by change χ⁻¹.conductor=29;rw [DirichletCharacter.conductor_inv];exact hprim
  refine ⟨χ,hprim,hval,pinv,hinv,?_,?_⟩
  · intro e
    have b : χ 2=χ⁻¹ 2 := congrArg (fun t : DirichletCharacter ℂ 29 => t 2) e
    rw [hval,hinv] at b
    have contradiction := congrArg Complex.im b
    norm_num at contradiction
  · intro ψ
    constructor
    · rintro (h|h)
      · exact Or.inl (determined ψ χ (h.trans hval.symm))
      · exact Or.inr (determined ψ χ⁻¹ (h.trans hinv.symm))
    · rintro (rfl|rfl)
      · exact Or.inl hval
      · exact Or.inr hinv
