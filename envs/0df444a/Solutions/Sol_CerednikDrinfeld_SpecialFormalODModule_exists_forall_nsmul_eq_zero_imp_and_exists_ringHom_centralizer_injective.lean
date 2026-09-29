-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/02da463c-fbc0-5c71-9b1d-0fe1766f1474

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_LubinTateModule
import Definitions.Def_CerednikDrinfeld_StandardFormalODModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_standard_existsUnique_eq_add_mul
import Theorems.Thm_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul
import Theorems.Thm_MvFormalGroup_CartierModule_map_injective_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

noncomputable section

open CerednikDrinfeld

namespace P2mKcE0

variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p] (j : Zp2 p →+* k)

local notation "𝕆" => Zp2 p
local notation "σ" => (WittVector.frobenius : Zp2 p →+* Zp2 p)

abbrev Φ₀ : SpecialFormalODModule p j := SpecialFormalODModule.standard j

abbrev S : Subring (MvFormalGroup.End (Φ₀ j).F) :=
  Subring.centralizer (Set.range (Φ₀ j).toFormalODModule.actEnd ∪ {(Φ₀ j).toFormalODModule.varpiEnd})

theorem torsionFree (f : MvFormalGroup.CartierModule p (Φ₀ j).F) (hf : p • f = 0) : f = 0 := by
  have hfin : Module.Finite k (MvPowerSeries (Fin 2) k ⧸
      Ideal.span (Set.range (MvFormalGroup.Hom.toPowerSeries ((p : ℕ) : MvFormalGroup.End (Φ₀ j).F)))) := by
    rw [MvFormalGroup.End.toPowerSeries_natCast, ← FormalODModule.act_natCast]
    exact (Φ₀ j).hasHeight.1
  have hinj := MvFormalGroup.CartierModule.map_injective_of_finite_quotient p (Φ₀ j).F (Φ₀ j).F _ hfin
  apply hinj
  have h1 : MvFormalGroup.CartierModule.map ((p : ℕ) : MvFormalGroup.End (Φ₀ j).F) f = p • f := by
    rw [← MvFormalGroup.CartierModule.endAct_natCast]; rfl
  rw [h1, hf, map_zero]

structure Dat where
  A : 𝕆 →+* S j
  Ψ : S j
  Ψ_mul_Ψ : Ψ * Ψ = A ((p : 𝕆) ^ 2)
  Ψ_mul_A : ∀ a, Ψ * A a = A (σ a) * Ψ
  coords : ∀ e : S j, ∃! ac : 𝕆 × 𝕆, e = A ac.1 + A ac.2 * Ψ
  r : 𝕆 →+* Matrix (Fin 2) (Fin 2) ℤ_[p]
  Sm : Matrix (Fin 2) (Fin 2) ℤ_[p]
  Sm_mul_Sm : Sm * Sm = 1
  Sm_mul_r : ∀ a, Sm * r a = r (σ a) * Sm
  indep : ∀ a c, r a + r c * Sm = 0 → a = 0 ∧ c = 0
  span : ∀ M, ∃ a c, M = r a + r c * Sm

theorem nonempty_dat : Nonempty (Dat j) := by
  obtain ⟨A, Ψ, -, -, h1, h2, h3⟩ :=
    SpecialFormalODModule.exists_ringHom_centralizer_standard_existsUnique_eq_add_mul p j
  obtain ⟨r, Sm, g1, g2, g3, g4⟩ :=
    WittVector.exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul p
  exact ⟨⟨A, Ψ, h1, h2, h3, r, Sm, g1, g2, g3, g4⟩⟩

variable {j}
variable (d : Dat j)

def crd (e : S j) : 𝕆 × 𝕆 := (d.coords e).exists.choose

theorem crd_spec (e : S j) : e = d.A (crd d e).1 + d.A (crd d e).2 * d.Ψ := (d.coords e).exists.choose_spec

theorem crd_eq {e : S j} {a c : 𝕆} (h : e = d.A a + d.A c * d.Ψ) : crd d e = (a, c) :=
  (d.coords e).unique (crd_spec d e) h

theorem add4_perm {M : Type*} [AddCommMonoid M] (x y z w : M) : x + y + (z + w) = x + w + (y + z) := by
  abel

theorem add4_perm' {M : Type*} [AddCommMonoid M] (x y z w : M) : x + y + (z + w) = x + z + (y + w) := by
  abel

abbrev R : Type u := MvFormalGroup.End (Φ₀ j).F

def A' : 𝕆 →+* R (j := j) := (S j).subtype.comp d.A

def Ψ' : R (j := j) := d.Ψ

theorem A'_apply (a : 𝕆) : A' d a = (d.A a : R (j := j)) := rfl

theorem Ψ'_def : Ψ' d = (d.Ψ : R (j := j)) := rfl

theorem Ψ'_mul_Ψ' : Ψ' d * Ψ' d = A' d ((p : 𝕆) ^ 2) := congrArg Subtype.val d.Ψ_mul_Ψ

theorem Ψ'_mul_A' (a : 𝕆) : Ψ' d * A' d a = A' d (σ a) * Ψ' d := congrArg Subtype.val (d.Ψ_mul_A a)

theorem coe_pres (a c : 𝕆) : ((d.A a + d.A c * d.Ψ : S j) : R (j := j)) = A' d a + A' d c * Ψ' d := rfl

theorem mul_pres (a c a' c' : 𝕆) :
    (A' d a + A' d c * Ψ' d) * (A' d a' + A' d c' * Ψ' d) =
      A' d (a * a' + (p : 𝕆) ^ 2 * (c * σ c')) + A' d (a * c' + c * σ a') * Ψ' d := by
  have e2 : A' d a * (A' d c' * Ψ' d) = A' d (a * c') * Ψ' d := by rw [← mul_assoc, ← map_mul]
  have e3 : A' d c * Ψ' d * A' d a' = A' d (c * σ a') * Ψ' d := by
    rw [mul_assoc, Ψ'_mul_A', ← mul_assoc, ← map_mul]
  have e4 : A' d c * Ψ' d * (A' d c' * Ψ' d) = A' d ((p : 𝕆) ^ 2 * (c * σ c')) := by
    rw [mul_assoc, ← mul_assoc (Ψ' d), Ψ'_mul_A' d c', mul_assoc, Ψ'_mul_Ψ', ← map_mul, ← map_mul]
    congr 1; ring
  have e1 : A' d a * A' d a' = A' d (a * a') := (map_mul _ _ _).symm
  rw [add_mul, mul_add, mul_add, e1, e2, e3, e4, map_add, map_add, add_mul]
  exact add4_perm (M := R (j := j)) _ _ _ _

theorem crd_one : crd d 1 = (1, 0) :=
  crd_eq d (Subtype.ext (by rw [coe_pres, map_one, map_zero, zero_mul, add_zero]; rfl))

theorem crd_mul (e e' : S j) :
    crd d (e * e') = ((crd d e).1 * (crd d e').1 + (p : 𝕆) ^ 2 * ((crd d e).2 * σ (crd d e').2),
      (crd d e).1 * (crd d e').2 + (crd d e).2 * σ (crd d e').1) :=
  crd_eq d (Subtype.ext (by
    rw [coe_pres, ← mul_pres, ← coe_pres, ← coe_pres, ← crd_spec, ← crd_spec]; rfl))

theorem crd_add (e e' : S j) : crd d (e + e') = ((crd d e).1 + (crd d e').1, (crd d e).2 + (crd d e').2) :=
  crd_eq d (Subtype.ext (by
    rw [coe_pres, map_add, map_add, add_mul, ← add4_perm', ← coe_pres, ← coe_pres, ← crd_spec, ← crd_spec]
    rfl))

theorem crd_zero : crd d 0 = (0, 0) :=
  crd_eq d (Subtype.ext (by rw [coe_pres, map_zero, zero_mul, add_zero]; rfl))

def ιM : Matrix (Fin 2) (Fin 2) ℤ_[p] →+* Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  (PadicInt.Coe.ringHom (p := p)).mapMatrix

theorem ιM_apply (M : Matrix (Fin 2) (Fin 2) ℤ_[p]) : ιM M = M.map ((↑) : ℤ_[p] → ℚ_[p]) := rfl

theorem ιM_injective : Function.Injective (ιM (p := p)) := fun M N h =>
  Matrix.map_injective Subtype.coe_injective h

def θ₀ (e : S j) : Matrix (Fin 2) (Fin 2) ℤ_[p] := d.r (crd d e).1 + d.r ((p : 𝕆) * (crd d e).2) * d.Sm

theorem θ₀_pres (a c : 𝕆) : θ₀ d (d.A a + d.A c * d.Ψ) = d.r a + d.r ((p : 𝕆) * c) * d.Sm := by
  rw [θ₀, crd_eq d rfl]

theorem frobenius_natCast_mul (c : 𝕆) : σ ((p : 𝕆) * c) = (p : 𝕆) * σ c := by
  rw [map_mul, map_natCast]

theorem θ₀_mul (e e' : S j) : θ₀ d (e * e') = θ₀ d e * θ₀ d e' := by
  rw [θ₀, crd_mul, θ₀, θ₀]
  dsimp only
  set a := (crd d e).1
  set c := (crd d e).2
  set a' := (crd d e').1
  set c' := (crd d e').2
  have f2 : d.r a * (d.r ((p : 𝕆) * c') * d.Sm) = d.r (a * ((p : 𝕆) * c')) * d.Sm := by
    rw [← mul_assoc, ← map_mul]
  have f3 : d.r ((p : 𝕆) * c) * d.Sm * d.r a' = d.r ((p : 𝕆) * c * σ a') * d.Sm := by
    rw [mul_assoc, d.Sm_mul_r, ← mul_assoc, ← map_mul]
  have f4 : d.r ((p : 𝕆) * c) * d.Sm * (d.r ((p : 𝕆) * c') * d.Sm) =
      d.r ((p : 𝕆) * c * ((p : 𝕆) * σ c')) := by
    rw [mul_assoc, ← mul_assoc d.Sm, d.Sm_mul_r, mul_assoc, d.Sm_mul_Sm, mul_one, ← map_mul,
      frobenius_natCast_mul]
  have hX : a * a' + (p : 𝕆) ^ 2 * (c * σ c') = a * a' + (p : 𝕆) * c * ((p : 𝕆) * σ c') := by ring
  have hY : (p : 𝕆) * (a * c' + c * σ a') = a * ((p : 𝕆) * c') + (p : 𝕆) * c * σ a' := by ring
  rw [add_mul, mul_add (d.r a), mul_add (d.r ((p : 𝕆) * c) * d.Sm), f2, f3, f4, hX, hY, map_add, map_add,
    add_mul, ← map_mul d.r a a']
  exact (add4_perm (M := Matrix (Fin 2) (Fin 2) ℤ_[p]) _ _ _ _).symm

theorem θ₀_one : θ₀ d 1 = 1 := by
  rw [θ₀, crd_one]
  simp only [map_one, mul_zero, map_zero, zero_mul, add_zero]

theorem θ₀_add (e e' : S j) : θ₀ d (e + e') = θ₀ d e + θ₀ d e' := by
  rw [θ₀, crd_add, θ₀, θ₀]
  simp only [map_add, mul_add, add_mul]
  abel

theorem θ₀_zero : θ₀ d 0 = 0 := by
  rw [θ₀, crd_zero]
  simp only [map_zero, mul_zero, zero_mul, add_zero]

def θ : S j →+* Matrix (Fin 2) (Fin 2) ℚ_[p] where
  toFun e := ιM (θ₀ d e)
  map_one' := by rw [θ₀_one, map_one]
  map_mul' e e' := by rw [θ₀_mul, map_mul]
  map_zero' := by rw [θ₀_zero, map_zero]
  map_add' e e' := by rw [θ₀_add, map_add]

theorem θ_apply (e : S j) : θ d e = ιM (θ₀ d e) := rfl

theorem p_ne_zero : (p : 𝕆) ≠ 0 := by
  intro h
  have := congrArg (fun x : 𝕆 => x.coeff 1) h
  simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at this
  exact one_ne_zero this

theorem θ_injective : Function.Injective (θ d) := by
  rw [injective_iff_map_eq_zero]
  intro e he
  rw [θ_apply, ← (ιM (p := p)).map_zero] at he
  have h0 := ιM_injective he
  rw [θ₀] at h0
  obtain ⟨ha, hc⟩ := d.indep _ _ h0
  have hc' : (crd d e).2 = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · exact absurd h p_ne_zero
    · exact h
  rw [crd_spec d e, ha, hc']
  exact Subtype.ext (by rw [coe_pres, map_zero, zero_mul, add_zero]; rfl)

theorem natCast_mul_eq_smul {R : Type*} [Semiring R] [Algebra ℚ_[p] R] (M : R) :
    (p : ℚ_[p]) • M = (p : R) * M := by
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem sandwich_left (M : Matrix (Fin 2) (Fin 2) ℤ_[p]) :
    ∃ e, θ d e = (p : ℚ_[p]) ^ 1 • M.map ((↑) : ℤ_[p] → ℚ_[p]) := by
  obtain ⟨a, c, hM⟩ := d.span M
  refine ⟨d.A ((p : 𝕆) * a) + d.A c * d.Ψ, ?_⟩
  rw [θ_apply, θ₀_pres, pow_one, ← ιM_apply, natCast_mul_eq_smul, ← map_natCast (ιM (p := p)) p,
    ← map_mul, hM, mul_add, map_mul, map_natCast, map_mul, map_natCast, mul_assoc]

theorem sandwich_right (e : S j) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℤ_[p], (p : ℚ_[p]) ^ 1 • θ d e = M.map ((↑) : ℤ_[p] → ℚ_[p]) := by
  refine ⟨(p : Matrix (Fin 2) (Fin 2) ℤ_[p]) * θ₀ d e, ?_⟩
  rw [θ_apply, pow_one, natCast_mul_eq_smul, ← ιM_apply, map_mul, map_natCast]

end P2mKcE0

end

open P2mKcE0 CerednikDrinfeld in

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) :
    ∃ Φ₀ : CerednikDrinfeld.SpecialFormalODModule p j,
      (∀ f : MvFormalGroup.CartierModule p Φ₀.F, p • f = 0 → f = 0) ∧
      ∃ θ : Subring.centralizer
            (Set.range Φ₀.toFormalODModule.actEnd ∪ {Φ₀.toFormalODModule.varpiEnd}) →+*
          Matrix (Fin 2) (Fin 2) ℚ_[p],
        Function.Injective θ ∧
        ∃ m : ℕ,
          (∀ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
            ∃ e, θ e = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
          (∀ e, ∃ M : Matrix (Fin 2) (Fin 2) ℤ_[p],
            (p : ℚ_[p]) ^ m • θ e = M.map ((↑) : ℤ_[p] → ℚ_[p])) := by
  obtain ⟨d⟩ := nonempty_dat j
  exact ⟨SpecialFormalODModule.standard j, torsionFree j, P2mKcE0.θ d, θ_injective d, 1,
    sandwich_left d, sandwich_right d⟩

end S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective (solution)
