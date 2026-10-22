-- Prove2me | solution 1 for BQC.conjugacy_cycle_type
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:26:42.179053+00:00
-- url     : https://prove2.me/submissions/a8364d4c-cade-4fa2-a4e6-43fa59700774

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

abbrev g74n_G3 := g74n_M ⋊[g74n_phi3] Multiplicative (ZMod 3)

def g74n_T : Subgroup g74n_G3 where
  carrier := {p | ((Multiplicative.toAdd p.left 2 : ℤ) : ZMod 3) = Multiplicative.toAdd p.right}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      toAdd_mul, Pi.add_apply, g74n_phi3_fix2, Int.cast_add] at *
    rw [ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, SemidirectProduct.inv_left, SemidirectProduct.inv_right,
      toAdd_inv, g74n_phi3_fix2, Pi.neg_apply, Int.cast_neg] at *
    rw [ha]

def g74n_D : (Fin 3 → ℤ) →+ (Fin 3 → ℤ) :=
  AddMonoidHom.mk' (fun z => ![z 0, z 1, 3 * z 2]) (by
    intro a b; ext i; fin_cases i <;> simp; ring)

lemma g74n_D_apply (z : Fin 3 → ℤ) : g74n_D z = ![z 0, z 1, 3 * z 2] := rfl

lemma g74n_commD (g : Multiplicative (ZMod 3)) (z : Fin 3 → ℤ) :
    g74n_phi3 g (Multiplicative.ofAdd (g74n_D z)) =
      Multiplicative.ofAdd (g74n_D (Multiplicative.toAdd (g74n_phi3 g (Multiplicative.ofAdd z)))) := by
  rcases g74n_cases3 g with rfl | rfl | rfl <;>
  · ext i; fin_cases i <;>
      simp [g74n_phi3_1, g74n_phi3_2, MulAut.mul_apply, g74n_B_apply, g74n_D_apply]

def g74n_injG : g74n_M →* g74n_G3 :=
  SemidirectProduct.inl.comp (AddMonoidHom.toMultiplicative g74n_D)

lemma g74n_injG_apply (z : Fin 3 → ℤ) :
    g74n_injG (Multiplicative.ofAdd z) = SemidirectProduct.inl (Multiplicative.ofAdd (g74n_D z)) := rfl

def g74n_W3 : CryWorld 3 g74n_T (Multiplicative (ZMod 3)) where
  inj := g74n_injG.codRestrict g74n_T (by
    intro z
    change (((g74n_D (Multiplicative.toAdd z)) 2 : ℤ) : ZMod 3) = Multiplicative.toAdd (1 : Multiplicative (ZMod 3))
    have h3 : (3 : ZMod 3) = 0 := by decide
    simp [g74n_D_apply, h3])
  proj := SemidirectProduct.rightHom.comp g74n_T.subtype
  inj_inj := by
    intro x y h
    have h1 := congrArg (fun p : g74n_T => Multiplicative.toAdd (p : g74n_G3).left) h
    simp only [MonoidHom.codRestrict_apply] at h1
    have h2 : ∀ x : g74n_M, Multiplicative.toAdd (g74n_injG x).left = g74n_D (Multiplicative.toAdd x) := fun _ => rfl
    rw [h2, h2] at h1
    have : Multiplicative.toAdd x = Multiplicative.toAdd y := by
      ext i
      have := congrFun h1 i
      fin_cases i <;> simpa [g74n_D_apply] using this
    exact this
  proj_surj := by
    intro f
    refine ⟨⟨⟨Multiplicative.ofAdd ![0, 0, ((Multiplicative.toAdd f).val : ℤ)], f⟩, ?_⟩, rfl⟩
    show (((Multiplicative.toAdd (Multiplicative.ofAdd ![(0:ℤ), 0, ((Multiplicative.toAdd f).val : ℤ)])) 2 : ℤ) : ZMod 3) = _
    simp
  ex := by
    intro p
    constructor
    · intro h
      have hr : (p : g74n_G3).right = 1 := h
      have hm := p.2
      change ((Multiplicative.toAdd (p : g74n_G3).left 2 : ℤ) : ZMod 3) = Multiplicative.toAdd (p : g74n_G3).right at hm
      rw [hr, toAdd_one, ZMod.intCast_zmod_eq_zero_iff_dvd] at hm
      refine ⟨![Multiplicative.toAdd (p : g74n_G3).left 0, Multiplicative.toAdd (p : g74n_G3).left 1,
        Multiplicative.toAdd (p : g74n_G3).left 2 / 3], ?_⟩
      apply Subtype.ext
      simp only [MonoidHom.codRestrict_apply, g74n_injG_apply]
      ext
      · rename_i i
        have hm' : (3 : ℤ) ∣ Multiplicative.toAdd (p : g74n_G3).left 2 := by exact_mod_cast hm
        fin_cases i <;> simp [g74n_D_apply, Int.mul_ediv_cancel' hm']
      · simp [hr]
    · rintro ⟨z, rfl⟩
      rfl
  hol := g74n_phi3
  hol_conj := by
    intro p z
    refine ⟨Multiplicative.toAdd (g74n_phi3 (p : g74n_G3).right (Multiplicative.ofAdd z)), ?_, by simp⟩
    apply Subtype.ext
    simp only [MonoidHom.codRestrict_apply, g74n_injG_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← g74n_commD]
    ext
    · simp [mul_comm]
    · simp
  hol_inj := fun _ _ h => g74n_phi3_inj h

lemma g74n_W3_proj (b : g74n_T) : g74n_W3.proj b = (b : g74n_G3).right := rfl

lemma g74n_nolift (b : g74n_T) (hb : g74n_W3.proj b = Multiplicative.ofAdd 1) : b ^ 3 ≠ 1 := by
  intro h3
  rw [g74n_W3_proj] at hb
  have hm := b.2
  change ((Multiplicative.toAdd (b : g74n_G3).left 2 : ℤ) : ZMod 3) = Multiplicative.toAdd (b : g74n_G3).right at hm
  rw [hb, toAdd_ofAdd] at hm
  have h4 : ((b : g74n_G3) ^ 3).left = 1 := by
    rw [← Subgroup.coe_pow, h3]; rfl
  have h5 := congrArg (fun v : g74n_M => Multiplicative.toAdd v 2) h4
  simp only [pow_succ, pow_zero, one_mul, SemidirectProduct.mul_left, toAdd_mul, Pi.add_apply,
    g74n_phi3_fix2, toAdd_one, Pi.zero_apply] at h5
  have h6 : Multiplicative.toAdd (b : g74n_G3).left 2 = 0 := by omega
  rw [h6] at hm
  exact absurd hm (by decide)

abbrev g74n_t : Multiplicative (ZMod 3) := Multiplicative.ofAdd 1

lemma g74n_t2 : g74n_t ^ 2 ≠ 1 := by decide
lemma g74n_t1 : g74n_t ^ 1 ≠ 1 := by decide
lemma g74n_t3 : g74n_t ^ 3 = 1 := by decide

lemma g74n_Bsymm (z : g74n_M) : g74n_B.symm z = g74n_B (g74n_B z) := by
  apply g74n_B.injective
  rw [MulEquiv.apply_symm_apply]
  ext i
  fin_cases i <;> simp [g74n_B_apply] <;> ring

theorem solution : ¬ (∀ {n : Nat} {Q S : Type} [Group Q] [Group S] [Fintype S]
    (W : BraidQuotient n Q S) (k : Nat) (hk : 3 ≤ k) (hodd : Odd k)
    (x y : Q) (hx : ExactOrder k x) (hy : ExactOrder k y),
    (∃ c : Q, c * x * c⁻¹ = y) ↔
      (∃ s : S, s * W.proj x * s⁻¹ = W.proj y)) := by
  intro H
  let x : g74n_G3 := SemidirectProduct.inr g74n_t
  let y : g74n_G3 := SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 0]) * SemidirectProduct.inr g74n_t
  have hpow : ∀ (p : g74n_G3) (j : ℕ), (p ^ j).right = p.right ^ j := fun p j =>
    map_pow SemidirectProduct.rightHom p j
  have hx : ExactOrder 3 x := by
    refine ⟨?_, ?_⟩
    · show (SemidirectProduct.inr g74n_t) ^ 3 = 1
      rw [← map_pow, g74n_t3, map_one]
    · intro j hj hj3 h
      have := congrArg SemidirectProduct.right h
      rw [hpow] at this
      interval_cases j
      · exact g74n_t1 this
      · exact g74n_t2 this
  have hy : ExactOrder 3 y := by
    refine ⟨?_, ?_⟩
    · ext i
      · fin_cases i <;>
          simp [y, pow_succ, g74n_phi3_1, g74n_phi3_2, MulAut.mul_apply, g74n_B_apply]
      · rw [hpow]; exact congrArg Multiplicative.toAdd (by simpa [y] using g74n_t3)
    · intro j hj hj3 h
      have := congrArg SemidirectProduct.right h
      rw [hpow] at this
      simp only [y, SemidirectProduct.mul_right, SemidirectProduct.right_inl,
        SemidirectProduct.right_inr, one_mul] at this
      interval_cases j
      · exact g74n_t1 this
      · exact g74n_t2 this
  have key := (H (n := 3) (g74n_split g74n_phi3 g74n_phi3_inj) 3 le_rfl ⟨1, rfl⟩ x y hx hy).2
    ⟨1, by simp [g74n_split, x, y]⟩
  obtain ⟨c, hc⟩ := key
  obtain ⟨u, r⟩ := c
  have h0 := congrArg (fun p : g74n_G3 => Multiplicative.toAdd p.left 0) hc
  have h1 := congrArg (fun p : g74n_G3 => Multiplicative.toAdd p.left 1) hc
  rcases g74n_cases3 r with rfl | rfl | rfl <;>
    simp [x, y, g74n_phi3_1, g74n_phi3_2, MulAut.mul_apply, g74n_B_apply] at h0 h1 <;>
    (try simp [g74n_Bsymm, g74n_B_apply, Matrix.vecHead, Matrix.vecTail] at h0 h1) <;> omega
