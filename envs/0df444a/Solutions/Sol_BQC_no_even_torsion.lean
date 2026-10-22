-- Prove2me | solution 1 for BQC.no_even_torsion
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:10:47.431305+00:00
-- url     : https://prove2.me/submissions/f964fa30-cb7c-4f8f-8300-d872c6876247

import Mathlib
import Definitions.Def_BQC_alg
import Definitions.Def_BQC_tor
open BQC

abbrev g74n_M := Multiplicative (Fin 3 → ℤ)

/-- order-3 automorphism (a,b,c) ↦ (-b, a-b, c) -/
def g74n_Badd : (Fin 3 → ℤ) ≃+ (Fin 3 → ℤ) where
  toFun z := ![-z 1, z 0 - z 1, z 2]
  invFun z := ![z 1 - z 0, -z 0, z 2]
  left_inv z := by ext i; fin_cases i <;> simp
  right_inv z := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring

def g74n_B : MulAut g74n_M := AddEquiv.toMultiplicative g74n_Badd

/-- negation -/
def g74n_N : MulAut g74n_M := AddEquiv.toMultiplicative (AddEquiv.neg (Fin 3 → ℤ))

lemma g74n_B_apply (z : g74n_M) :
    g74n_B z = Multiplicative.ofAdd ![-(Multiplicative.toAdd z) 1,
      (Multiplicative.toAdd z) 0 - (Multiplicative.toAdd z) 1, (Multiplicative.toAdd z) 2] := rfl

lemma g74n_N_apply (z : g74n_M) :
    g74n_N z = Multiplicative.ofAdd (-(Multiplicative.toAdd z)) := rfl

lemma g74n_B3 : g74n_B ^ 3 = 1 := by
  ext z i
  fin_cases i <;> simp [pow_succ, MulAut.mul_apply, g74n_B_apply] <;> ring

lemma g74n_N2 : g74n_N ^ 2 = 1 := by
  ext z i
  simp [pow_succ, MulAut.mul_apply, g74n_N_apply]

def g74n_hom (q : ℕ) [NeZero q] (A : MulAut g74n_M) (hA : A ^ q = 1) :
    Multiplicative (ZMod q) →* MulAut g74n_M where
  toFun g := A ^ (Multiplicative.toAdd g).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul]
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hA, pow_add]

def g74n_phi3 : Multiplicative (ZMod 3) →* MulAut g74n_M := g74n_hom 3 g74n_B g74n_B3
def g74n_phi2 : Multiplicative (ZMod 2) →* MulAut g74n_M := g74n_hom 2 g74n_N g74n_N2

lemma g74n_phi3_0 : g74n_phi3 (Multiplicative.ofAdd 0) = 1 := by
  show g74n_B ^ (0 : ZMod 3).val = 1; rw [show (0 : ZMod 3).val = 0 from rfl, pow_zero]
lemma g74n_phi3_1 : g74n_phi3 (Multiplicative.ofAdd 1) = g74n_B := by
  show g74n_B ^ (1 : ZMod 3).val = _; rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]
lemma g74n_phi3_2 : g74n_phi3 (Multiplicative.ofAdd 2) = g74n_B * g74n_B := by
  show g74n_B ^ (2 : ZMod 3).val = _; rw [show (2 : ZMod 3).val = 2 from rfl, pow_two]
lemma g74n_phi2_0 : g74n_phi2 (Multiplicative.ofAdd 0) = 1 := by
  show g74n_N ^ (0 : ZMod 2).val = 1; rw [show (0 : ZMod 2).val = 0 from rfl, pow_zero]
lemma g74n_phi2_1 : g74n_phi2 (Multiplicative.ofAdd 1) = g74n_N := by
  show g74n_N ^ (1 : ZMod 2).val = _; rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]

lemma g74n_cases3 (g : Multiplicative (ZMod 3)) :
    g = Multiplicative.ofAdd 0 ∨ g = Multiplicative.ofAdd 1 ∨ g = Multiplicative.ofAdd 2 := by
  induction g using Multiplicative.rec with | ofAdd g => ?_
  fin_cases g
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

lemma g74n_cases2 (g : Multiplicative (ZMod 2)) :
    g = Multiplicative.ofAdd 0 ∨ g = Multiplicative.ofAdd 1 := by
  induction g using Multiplicative.rec with | ofAdd g => ?_
  fin_cases g
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma g74n_phi3_inj : Function.Injective g74n_phi3 := by
  intro a b h
  have h0 := congrArg (fun σ : MulAut g74n_M => Multiplicative.toAdd (σ (Multiplicative.ofAdd ![1, 0, 0])) 0) h
  have h1 := congrArg (fun σ : MulAut g74n_M => Multiplicative.toAdd (σ (Multiplicative.ofAdd ![1, 0, 0])) 1) h
  rcases g74n_cases3 a with rfl | rfl | rfl <;> rcases g74n_cases3 b with rfl | rfl | rfl <;>
    first | rfl | (simp [g74n_phi3_0, g74n_phi3_1, g74n_phi3_2, MulAut.mul_apply, g74n_B_apply] at h0 h1)

lemma g74n_phi2_inj : Function.Injective g74n_phi2 := by
  intro a b h
  have h0 := congrArg (fun σ : MulAut g74n_M => Multiplicative.toAdd (σ (Multiplicative.ofAdd ![1, 0, 0])) 0) h
  rcases g74n_cases2 a with rfl | rfl <;> rcases g74n_cases2 b with rfl | rfl <;>
    first | rfl | (simp [g74n_phi2_0, g74n_phi2_1, MulAut.mul_apply, g74n_N_apply] at h0)

lemma g74n_phi3_fix2 (g : Multiplicative (ZMod 3)) (z : g74n_M) :
    Multiplicative.toAdd (g74n_phi3 g z) 2 = Multiplicative.toAdd z 2 := by
  rcases g74n_cases3 g with rfl | rfl | rfl <;>
    simp [g74n_phi3_0, g74n_phi3_1, g74n_phi3_2, MulAut.mul_apply, g74n_B_apply]

/-- split world over an injective action -/
def g74n_split {P : Type} [Group P] [Fintype P] (φ : P →* MulAut g74n_M)
    (hφ : Function.Injective φ) : CryWorld 3 (g74n_M ⋊[φ] P) P where
  inj := SemidirectProduct.inl
  proj := SemidirectProduct.rightHom
  inj_inj := fun _ _ h => SemidirectProduct.inl_injective h
  proj_surj := fun f => ⟨SemidirectProduct.inr f, by simp⟩
  ex := fun p => by
    constructor
    · intro h
      refine ⟨Multiplicative.toAdd p.left, ?_⟩
      ext
      · simp
      · simpa using h.symm
    · rintro ⟨z, rfl⟩; simp
  hol := φ
  hol_conj := fun p z => by
    refine ⟨Multiplicative.toAdd (φ p.right (Multiplicative.ofAdd z)), ?_, by simp⟩
    ext
    · simp [mul_comm]
    · simp
  hol_inj := fun _ _ h => hφ h

theorem solution : ¬ (∀ {n : Nat} {Q S : Type} [Group Q] [Group S] [Fintype S]
    (W : BraidQuotient n Q S) (hn : 3 ≤ n), NoEvenTorsion Q) := by
  intro H
  have h := H (n := 3) (g74n_split g74n_phi2 g74n_phi2_inj) le_rfl
  set g : g74n_M ⋊[g74n_phi2] Multiplicative (ZMod 2) :=
    SemidirectProduct.inr (Multiplicative.ofAdd 1) with hg
  have hg2 : g ^ 2 = 1 := by
    rw [hg, ← map_pow]
    have : (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by decide
    rw [this, map_one]
  obtain ⟨k, -, hk, hgk⟩ := h g ⟨2, by norm_num, hg2⟩
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul, hg2, one_pow, one_mul, hg] at hgk
  have := SemidirectProduct.inr_injective (hgk.trans (map_one _).symm)
  exact absurd this (by decide)
