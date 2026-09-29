-- Prove2me | solution 1 for CohCarrier.exists_gamma0_heckeTlower_eq_heckeT_diamondRaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/157290e2-14da-5807-9280-c2e61045b710

import Mathlib
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Fricke
import Theorems.Thm_CohCarrier_heckeT_apply_eq_sumEquiv
import Theorems.Thm_CohCarrier_frickeH1_heckeTlower_eq_heckeT_frickeH1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_gamma0_heckeTlower_eq_heckeT_diamondRaw

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open CongruenceSubgroup
open scoped MatrixGroups

namespace CohCarrier
p2m_export "CohCarrier" "rep cls slip heckeTlower mem_Gamma0Upper gamma0Units val_gamma0Units GammaH mem_GammaH_iff H1 conjUpperMat GammaHUpper dvd_of_mem_GammaHUpper conjL heckeT conjHom diamondRaw frickeMat N_dvd_of_mem_GammaH frickeHom coe_frickeHom frickeHom_frickeHom frickeH1 frickeH1_apply frickeH1_frickeH1 heckeT_apply_eq_sumEquiv frickeH1_heckeTlower_eq_heckeT_frickeH1"
namespace LowerSym
p2m_open "CohCarrier"

section RepChange

variable {Γ : Type*} [Group Γ] (S : Subgroup Γ) {V : Type*} [AddCommGroup V]

theorem cls_mul (g γ : Γ) : cls S (g * γ) = Quotient.map' (· * γ)
    (fun a b h => by
      rw [QuotientGroup.rightRel_apply] at h ⊢
      simpa [mul_assoc] using h) (cls S g) := rfl

theorem rep_mul_mul_inv_mem (t : Quotient (QuotientGroup.rightRel S) → Γ) (ht : ∀ c, cls S (t c) = c)
    (c : Quotient (QuotientGroup.rightRel S)) (γ : Γ) :
    t c * γ * (t (cls S (t c * γ)))⁻¹ ∈ S := by
  have h : QuotientGroup.rightRel S (t (cls S (t c * γ))) (t c * γ) :=
    Quotient.exact' ((ht _).trans rfl)
  rw [QuotientGroup.rightRel_apply] at h
  simpa [mul_assoc] using h

theorem sum_slip_eq_sum_of_reps (ψ : Additive S →+ V) (γ : Γ)
    (X : Finset (Quotient (QuotientGroup.rightRel S)))
    (hX : ∀ c ∈ X, cls S (rep S c * γ) ∈ X)
    (hXsurj : ∀ c ∈ X, ∃ c₀ ∈ X, cls S (rep S c₀ * γ) = c)
    (t : Quotient (QuotientGroup.rightRel S) → Γ) (ht : ∀ c, cls S (t c) = c) :
    ∑ c ∈ X, ψ (Additive.ofMul (slip S c γ)) =
      ∑ c ∈ X, ψ (Additive.ofMul (⟨t c * γ * (t (cls S (t c * γ)))⁻¹, rep_mul_mul_inv_mem S t ht c γ⟩ : S)) := by

  have hu : ∀ c, t c * (rep S c)⁻¹ ∈ S := fun c => by
    have h : QuotientGroup.rightRel S (t c) (rep S c) :=
      Quotient.exact' (by rw [show Quotient.mk'' (t c) = cls S (t c) from rfl, ht]; simp [rep])
    rw [QuotientGroup.rightRel_apply] at h
    simpa using S.inv_mem h
  let u : Quotient (QuotientGroup.rightRel S) → S := fun c => ⟨t c * (rep S c)⁻¹, hu c⟩

  have hperm : ∀ c, cls S (t c * γ) = cls S (rep S c * γ) := fun c => by
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]

    have h1 : rep S c * γ * (t c * γ)⁻¹ = (t c * (rep S c)⁻¹)⁻¹ := by group
    rw [h1]
    exact S.inv_mem (hu c)

  have hfac : ∀ c, (⟨t c * γ * (t (cls S (t c * γ)))⁻¹, rep_mul_mul_inv_mem S t ht c γ⟩ : S) =
      u c * slip S c γ * (u (cls S (rep S c * γ)))⁻¹ := fun c => by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, u, slip, hperm c, mul_inv_rev, inv_inv]
    group
  simp_rw [hfac]
  simp only [ofMul_mul, ofMul_inv, map_add, map_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

  have hbij : ∑ c ∈ X, ψ (Additive.ofMul (u (cls S (rep S c * γ)))) = ∑ c ∈ X, ψ (Additive.ofMul (u c)) := by
    apply Finset.sum_nbij (fun c => cls S (rep S c * γ)) hX
    ·
      intro c₁ h₁ c₂ h₂ h
      have e1 : cls S (rep S c₁) = c₁ := by simp [rep, cls]
      have e2 : cls S (rep S c₂) = c₂ := by simp [rep, cls]
      rw [← e1, ← e2]
      apply Quotient.sound'
      have h' : QuotientGroup.rightRel S (rep S c₁ * γ) (rep S c₂ * γ) := Quotient.exact' h
      rw [QuotientGroup.rightRel_apply] at h' ⊢
      simpa [mul_assoc] using h'
    · exact fun c hc => by simpa using hXsurj c hc
    · intro c _; rfl
  rw [hbij]
  abel

end RepChange

section Assembly

variable {Γ : Type*} [Group Γ] (S : Subgroup Γ)

theorem cls_rep (c : Quotient (QuotientGroup.rightRel S)) : cls S (rep S c) = c := by simp [rep, cls]

theorem cls_mul_eq_of_cls_eq {g g' : Γ} (h : cls S g = cls S g') (γ : Γ) : cls S (g * γ) = cls S (g' * γ) := by
  apply Quotient.sound'
  have h' : QuotientGroup.rightRel S g g' := Quotient.exact' h
  rw [QuotientGroup.rightRel_apply] at h' ⊢
  simpa [mul_assoc] using h'

theorem cls_rep_mul (g γ : Γ) : cls S (rep S (cls S g) * γ) = cls S (g * γ) :=
  cls_mul_eq_of_cls_eq S (cls_rep S _) γ

end Assembly

section Mats

variable (N q : ℕ) [NeZero N] [NeZero q] (H : Subgroup (ZMod N)ˣ)

def kMat (hcop : Nat.Coprime N q) : SL(2, ℤ) :=
  ⟨!![(q : ℤ) * Nat.gcdB N q, -Nat.gcdA N q; N, 1], by
    rw [Matrix.det_fin_two_of]
    have h := Nat.gcd_eq_gcd_ab N q
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    push_cast at h
    linear_combination -h⟩

@[scoped simp] theorem kMat_apply_00 (hcop : Nat.Coprime N q) : (kMat N q hcop) 0 0 = (q : ℤ) * Nat.gcdB N q := rfl
@[scoped simp] theorem kMat_apply_01 (hcop : Nat.Coprime N q) : (kMat N q hcop) 0 1 = -Nat.gcdA N q := rfl
@[scoped simp] theorem kMat_apply_10 (hcop : Nat.Coprime N q) : (kMat N q hcop) 1 0 = N := rfl
@[scoped simp] theorem kMat_apply_11 (hcop : Nat.Coprime N q) : (kMat N q hcop) 1 1 = 1 := rfl

theorem kMat_mem (hcop : Nat.Coprime N q) : kMat N q hcop ∈ GammaH N H := by
  have h0 : kMat N q hcop ∈ Gamma0 N := by
    rw [Gamma0_mem]; show ((N : ℤ) : ZMod N) = 0; simp
  refine mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have e : gamma0Units N ⟨kMat N q hcop, h0⟩ = 1 := by
    apply Units.ext; rw [val_gamma0Units, Units.val_one]
    show ((1 : ℤ) : ZMod N) = 1; exact Int.cast_one
  rw [e]; exact H.one_mem

def kElt (hcop : Nat.Coprime N q) : ↥(GammaH N H) := ⟨kMat N q hcop, kMat_mem N q H hcop⟩
@[scoped simp] theorem coe_kElt (hcop : Nat.Coprime N q) : ((kElt N q H hcop : ↥(GammaH N H)) : SL(2, ℤ)) = kMat N q hcop := rfl

def tMat (hcop : Nat.Coprime N q) : SL(2, ℤ) :=
  ⟨!![(q : ℤ), Nat.gcdA N q; -(N : ℤ), Nat.gcdB N q], by
    rw [Matrix.det_fin_two_of]
    have h := Nat.gcd_eq_gcd_ab N q
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    push_cast at h
    linear_combination -h⟩

@[scoped simp] theorem tMat_apply_00 (hcop : Nat.Coprime N q) : (tMat N q hcop) 0 0 = (q : ℤ) := rfl
@[scoped simp] theorem tMat_apply_01 (hcop : Nat.Coprime N q) : (tMat N q hcop) 0 1 = Nat.gcdA N q := rfl
@[scoped simp] theorem tMat_apply_10 (hcop : Nat.Coprime N q) : (tMat N q hcop) 1 0 = -(N : ℤ) := rfl
@[scoped simp] theorem tMat_apply_11 (hcop : Nat.Coprime N q) : (tMat N q hcop) 1 1 = Nat.gcdB N q := rfl

theorem tMat_mem_Gamma0 (hcop : Nat.Coprime N q) : tMat N q hcop ∈ Gamma0 N := by
  rw [Gamma0_mem]; show ((-(N : ℤ) : ℤ) : ZMod N) = 0; simp

theorem key_identity (hcop : Nat.Coprime N q) (s : SL(2, ℤ)) (hs : (q : ℤ) ∣ s 0 1) (hN : (N : ℤ) ∣ s 1 0)
    (hF : (N : ℤ) ∣ (conjUpperMat q s hs) 1 0)
    (hK : (q : ℤ) ∣ (kMat N q hcop * frickeMat N s hN * (kMat N q hcop)⁻¹) 0 1) :
    tMat N q hcop * conjUpperMat q (kMat N q hcop * frickeMat N s hN * (kMat N q hcop)⁻¹) hK * (tMat N q hcop)⁻¹ =
      frickeMat N (conjUpperMat q s hs) hF := by
  obtain ⟨b', hb'⟩ := hs
  obtain ⟨c', hc'⟩ := hN
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hdet := Matrix.SpecialLinearGroup.det_coe s
  rw [Matrix.det_fin_two] at hdet
  have hbez := Nat.gcd_eq_gcd_ab N q
  rw [Nat.Coprime.gcd_eq_one hcop] at hbez
  push_cast at hbez
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [conjUpperMat, frickeMat, kMat, tMat, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [hb', hc'] at *
  have e1 : (q : ℤ) * b' / q = b' := by rw [mul_comm]; exact Int.mul_ediv_cancel b' hq0
  have e2 : (N : ℤ) * c' / N = c' := by rw [mul_comm]; exact Int.mul_ediv_cancel c' hN0
  have e3 : (N : ℤ) * c' * q / N = c' * q := by
    rw [show (N : ℤ) * c' * q = (c' * q) * N by ring]; exact Int.mul_ediv_cancel _ hN0
  have e4 : (((q : ℤ) * Nat.gcdB N q * s 1 1 + Nat.gcdA N q * (N * (q * b'))) * Nat.gcdA N q +
      (-((q : ℤ) * Nat.gcdB N q * c') + -(Nat.gcdA N q * s 0 0)) * (q * Nat.gcdB N q)) / q =
      (Nat.gcdB N q * s 1 1 + Nat.gcdA N q * (N * b')) * Nat.gcdA N q +
        (-(Nat.gcdB N q * c') + -(Nat.gcdA N q * s 0 0) * 0 - Nat.gcdA N q * s 0 0 * 0) * (q * Nat.gcdB N q) * 0 +
        (-(Nat.gcdB N q * c') * q + -(Nat.gcdA N q * s 0 0)) * Nat.gcdB N q := by
    rw [show ((q : ℤ) * Nat.gcdB N q * s 1 1 + Nat.gcdA N q * (N * (q * b'))) * Nat.gcdA N q +
      (-((q : ℤ) * Nat.gcdB N q * c') + -(Nat.gcdA N q * s 0 0)) * (q * Nat.gcdB N q) =
      (q : ℤ) * ((Nat.gcdB N q * s 1 1 + Nat.gcdA N q * (N * b')) * Nat.gcdA N q +
        (-(Nat.gcdB N q * c') * q + -(Nat.gcdA N q * s 0 0)) * Nat.gcdB N q) by ring]
    rw [Int.mul_ediv_cancel_left _ hq0]
    ring
  fin_cases i <;> fin_cases j <;> simp [e1, e2, e3, e4] <;>
    first
    | (linear_combination (-(1 + ((N : ℤ) * Nat.gcdA N q + (q : ℤ) * Nat.gcdB N q)) * (-((N : ℤ) * b'))) * hbez)
    | (linear_combination (-(1 + ((N : ℤ) * Nat.gcdA N q + (q : ℤ) * Nat.gcdB N q)) * ((s : Matrix (Fin 2) (Fin 2) ℤ) 0 0)) * hbez)
    | (linear_combination (-(1 + ((N : ℤ) * Nat.gcdA N q + (q : ℤ) * Nat.gcdB N q)) * ((s : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) * hbez)
    | (linear_combination (-(1 + ((N : ℤ) * Nat.gcdA N q + (q : ℤ) * Nat.gcdB N q)) * (-(c' * (q : ℤ)))) * hbez)

end Mats

section Main

variable {N q : ℕ} [NeZero N] [NeZero q] {H : Subgroup (ZMod N)ˣ} (hcop : Nat.Coprime N q)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem kconj_frickeHom_mem (u : ↥(GammaHUpper N H q)) :
    kElt N q H hcop * frickeHom N H (u : ↥(GammaH N H)) * (kElt N q H hcop)⁻¹ ∈ GammaHUpper N H q := by
  rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper]
  obtain ⟨b', hb'⟩ := dvd_of_mem_GammaHUpper N H q u
  have hN := N_dvd_of_mem_GammaH N H (u : ↥(GammaH N H))
  obtain ⟨c', hc'⟩ := hN
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have e2 : (N : ℤ) * c' / N = c' := by rw [mul_comm]; exact Int.mul_ediv_cancel c' hN0
  show (((((kElt N q H hcop * frickeHom N H (u : ↥(GammaH N H)) * (kElt N q H hcop)⁻¹ : ↥(GammaH N H)) : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q) = 0
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_kElt, coe_frickeHom, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, frickeMat, kMat,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hu01 : ((u : ↥(GammaH N H)) : SL(2, ℤ)) 0 1 = q * b' := hb'
  have hu10 : ((u : ↥(GammaH N H)) : SL(2, ℤ)) 1 0 = N * c' := hc'
  simp only [hu01, hu10, e2]
  exact ⟨(Nat.gcdB N q * ((u : ↥(GammaH N H)) : SL(2, ℤ)) 1 1 + Nat.gcdA N q * (N * b')) * Nat.gcdA N q +
      (-(Nat.gcdB N q * c') * q + -(Nat.gcdA N q * ((u : ↥(GammaH N H)) : SL(2, ℤ)) 0 0)) * Nat.gcdB N q, by ring⟩

theorem kconj_frickeHom_mem_iff [Fact q.Prime] (x : ↥(GammaH N H)) :
    kElt N q H hcop * frickeHom N H x * (kElt N q H hcop)⁻¹ ∈ GammaHUpper N H q ↔ x ∈ GammaHUpper N H q := by
  rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper, Subgroup.mem_subgroupOf, mem_Gamma0Upper]
  obtain ⟨c', hc'⟩ := N_dvd_of_mem_GammaH N H x
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have e2 : (N : ℤ) * c' / N = c' := by rw [mul_comm]; exact Int.mul_ediv_cancel c' hN0
  have hbez := Nat.gcd_eq_gcd_ab N q
  rw [Nat.Coprime.gcd_eq_one hcop] at hbez
  have hbez' := congrArg (Int.cast : ℤ → ZMod q) hbez
  push_cast at hbez'
  rw [ZMod.natCast_self, zero_mul, add_zero] at hbez'

  show (((((kElt N q H hcop * frickeHom N H x * (kElt N q H hcop)⁻¹ : ↥(GammaH N H)) : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q) = 0 ↔
    ((((x : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q) = 0
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_kElt, coe_frickeHom, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, frickeMat, kMat,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  have hx10 : ((x : SL(2, ℤ)) : SL(2, ℤ)) 1 0 = N * c' := hc'
  simp only [hx10, e2]
  push_cast
  rw [ZMod.natCast_self]
  have key : ((q : ZMod q) = 0) := ZMod.natCast_self q
  constructor
  · intro h

    have h' : ((Nat.gcdA N q : ℤ) : ZMod q) ^ 2 * (N : ZMod q) * ((((x : SL(2, ℤ)) 0 1 : ℤ)) : ZMod q) = 0 := by
      linear_combination h
    have hgA : IsUnit (((Nat.gcdA N q : ℤ) : ZMod q)) :=
      IsUnit.of_mul_eq_one (N : ZMod q) (by linear_combination hbez'.symm)
    have hNu : IsUnit (N : ZMod q) :=
      IsUnit.of_mul_eq_one (((Nat.gcdA N q : ℤ) : ZMod q)) (by linear_combination hbez'.symm)
    have hu : IsUnit (((Nat.gcdA N q : ℤ) : ZMod q) ^ 2 * (N : ZMod q)) := (hgA.pow 2).mul hNu
    exact (hu.mul_right_eq_zero).mp h'
  · intro h
    rw [h]
    ring

variable [Fact q.Prime]

noncomputable def beta (c : Quotient (QuotientGroup.rightRel (GammaHUpper N H q))) :
    Quotient (QuotientGroup.rightRel (GammaHUpper N H q)) :=
  cls (GammaHUpper N H q) (kElt N q H hcop * frickeHom N H (rep (GammaHUpper N H q) c))

theorem cls_kFr_eq_iff (x y : ↥(GammaH N H)) :
    cls (GammaHUpper N H q) (kElt N q H hcop * frickeHom N H x) = cls (GammaHUpper N H q) (kElt N q H hcop * frickeHom N H y) ↔
      cls (GammaHUpper N H q) x = cls (GammaHUpper N H q) y := by
  constructor
  · intro h
    apply Quotient.sound'
    have h' := Quotient.exact' h
    rw [QuotientGroup.rightRel_apply] at h' ⊢
    rw [show kElt N q H hcop * frickeHom N H y * (kElt N q H hcop * frickeHom N H x)⁻¹ =
      kElt N q H hcop * frickeHom N H (y * x⁻¹) * (kElt N q H hcop)⁻¹ by rw [map_mul, map_inv]; group] at h'
    exact (kconj_frickeHom_mem_iff hcop _).mp h'
  · intro h
    apply Quotient.sound'
    have h' := Quotient.exact' h
    rw [QuotientGroup.rightRel_apply] at h' ⊢
    rw [show kElt N q H hcop * frickeHom N H y * (kElt N q H hcop * frickeHom N H x)⁻¹ =
      kElt N q H hcop * frickeHom N H (y * x⁻¹) * (kElt N q H hcop)⁻¹ by rw [map_mul, map_inv]; group]
    exact (kconj_frickeHom_mem_iff hcop _).mpr h'

theorem beta_bijective : Function.Bijective (beta (N := N) (q := q) (H := H) hcop) := by
  rw [← Finite.injective_iff_bijective]
  intro c₁ c₂ h
  have := (cls_kFr_eq_iff hcop _ _).mp h
  rwa [cls_rep, cls_rep] at this

theorem slip_mul_rep {Γ : Type*} [Group Γ] (S : Subgroup Γ) (c : Quotient (QuotientGroup.rightRel S)) (γ : Γ) :
    ((slip S c γ : ↥S) : Γ) * rep S (cls S (rep S c * γ)) = rep S c * γ := by
  simp [slip]

theorem cls_mul_of_mem {Γ : Type*} [Group Γ] (S : Subgroup Γ) {u : Γ} (hu : u ∈ S) (g : Γ) :
    cls S (u * g) = cls S g := by
  apply Quotient.sound'
  rw [QuotientGroup.rightRel_apply]
  simpa [mul_assoc] using S.inv_mem hu

theorem main {A : Type} [AddCommGroup A] (φ : H1 N H A) :
    heckeTlower N H q A φ = heckeT N H q A (diamondRaw N H A ⟨tMat N q hcop, tMat_mem_Gamma0 N q hcop⟩ φ) := by
  classical
  set τ : Gamma0 N := ⟨tMat N q hcop, tMat_mem_Gamma0 N q hcop⟩ with hτ
  set U := GammaHUpper N H q with hU
  have eLow : heckeTlower N H q A φ = frickeH1 N H A (heckeT N H q A (frickeH1 N H A φ)) := by
    rw [← frickeH1_heckeTlower_eq_heckeT_frickeH1 N H q A φ, frickeH1_frickeH1]
  rw [eLow]
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨γ, rfl⟩ : ∃ γ, Additive.ofMul γ = x := ⟨Additive.toMul x, rfl⟩
  set γF := frickeHom N H γ with hγF

  have eL : frickeH1 N H A (heckeT N H q A (frickeH1 N H A φ)) (Additive.ofMul γ) =
      ∑ c : Quotient (QuotientGroup.rightRel U), φ (Additive.ofMul (frickeHom N H (conjL N H q (slip U c γF)))) := by
    rw [frickeH1_apply, heckeT_apply_eq_sumEquiv N H q (Equiv.refl _) _ γF]
    rfl

  let ψ : Additive ↥U →+ A := (φ.comp (MonoidHom.toAdditive (conjHom N H τ))).comp (MonoidHom.toAdditive (conjL N H q))
  have eR : heckeT N H q A (diamondRaw N H A τ φ) (Additive.ofMul γ) =
      ∑ b : Quotient (QuotientGroup.rightRel U), ψ (Additive.ofMul (slip U b γ)) := by
    rw [heckeT_apply_eq_sumEquiv N H q (Equiv.refl _) _ γ]
    rfl
  rw [eL, eR]

  let e := Equiv.ofBijective (beta (N := N) (q := q) (H := H) hcop) (beta_bijective hcop)
  let T : Quotient (QuotientGroup.rightRel U) → ↥(GammaH N H) := fun b =>
    kElt N q H hcop * frickeHom N H (rep U (e.symm b))
  have hTe : ∀ c, T (e c) = kElt N q H hcop * frickeHom N H (rep U c) := fun c => by
    simp only [T, Equiv.symm_apply_apply]
  have ht : ∀ b, cls U (T b) = b := fun b => by
    obtain ⟨c, rfl⟩ := e.surjective b
    rw [hTe]
    rfl
  have key := sum_slip_eq_sum_of_reps U ψ γ Finset.univ (fun c _ => Finset.mem_univ _)
    (fun c _ => ⟨cls U (rep U c * γ⁻¹), Finset.mem_univ _, by rw [cls_rep_mul, inv_mul_cancel_right, cls_rep]⟩) T ht
  rw [key, ← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun b _ => ?_
  set c := e.symm b with hc
  have hTb : T b = kElt N q H hcop * frickeHom N H (rep U c) := rfl
  have hFr : frickeHom N H (rep U c) * γ =
      frickeHom N H ((slip U c γF : ↥U) : ↥(GammaH N H)) * frickeHom N H (rep U (cls U (rep U c * γF))) := by
    rw [← map_mul, slip_mul_rep, map_mul, hγF, frickeHom_frickeHom]

  have hnext : cls U (T b * γ) = e (cls U (rep U c * γF)) := by
    rw [hTb, mul_assoc, hFr, ← mul_assoc,
      show kElt N q H hcop * frickeHom N H ((slip U c γF : ↥U) : ↥(GammaH N H)) * frickeHom N H (rep U (cls U (rep U c * γF))) =
        (kElt N q H hcop * frickeHom N H ((slip U c γF : ↥U) : ↥(GammaH N H)) * (kElt N q H hcop)⁻¹) *
          (kElt N q H hcop * frickeHom N H (rep U (cls U (rep U c * γF)))) by group,
      cls_mul_of_mem U (kconj_frickeHom_mem hcop _)]
    rfl
  have hval : T b * γ * (T (cls U (T b * γ)))⁻¹ =
      kElt N q H hcop * frickeHom N H ((slip U c γF : ↥U) : ↥(GammaH N H)) * (kElt N q H hcop)⁻¹ := by
    rw [hnext, hTe, hTb, mul_assoc (kElt N q H hcop) (frickeHom N H (rep U c)) γ, hFr]
    group
  have hmem : kElt N q H hcop * frickeHom N H ((slip U c γF : ↥U) : ↥(GammaH N H)) * (kElt N q H hcop)⁻¹ ∈ U :=
    kconj_frickeHom_mem hcop _
  have hel : (⟨T b * γ * (T (cls U (T b * γ)))⁻¹, rep_mul_mul_inv_mem U T ht _ γ⟩ : ↥U) = ⟨_, hmem⟩ :=
    Subtype.ext hval
  rw [hel]
  show φ (Additive.ofMul (frickeHom N H (conjL N H q (slip U c γF)))) = φ (Additive.ofMul (conjHom N H τ (conjL N H q ⟨_, hmem⟩)))
  congr 2
  apply Subtype.ext
  exact (key_identity N q hcop _ (dvd_of_mem_GammaHUpper N H q (slip U c γF))
    (N_dvd_of_mem_GammaH N H ((slip U c γF : ↥U) : ↥(GammaH N H)))
    (N_dvd_of_mem_GammaH N H (conjL N H q (slip U c γF)))
    (dvd_of_mem_GammaHUpper N H q ⟨_, hmem⟩)).symm

end Main

end CohCarrier.LowerSym
p2m_reactivate "P2MW.S_CohCarrier_exists_gamma0_heckeTlower_eq_heckeT_diamondRaw.CohCarrier P2MW.S_CohCarrier_exists_gamma0_heckeTlower_eq_heckeT_diamondRaw.CohCarrier.LowerSym"
p2m_reactivate "P2MW.S_CohCarrier_exists_gamma0_heckeTlower_eq_heckeT_diamondRaw.CohCarrier"

open _root_.CohCarrier _root_.P2MW.S_CohCarrier_exists_gamma0_heckeTlower_eq_heckeT_diamondRaw.CohCarrier CongruenceSubgroup in
open scoped MatrixGroups in

theorem solution
    {N q : ℕ} [NeZero N] [NeZero q] {A : Type} [AddCommGroup A]
    (hq : q.Prime) (hqN : ¬ q ∣ N) (H : Subgroup (ZMod N)ˣ) :
    ∃ τ : Gamma0 N, ((((τ : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) = q) ∧
      ∀ φ : H1 N H A, heckeTlower N H q A φ = heckeT N H q A (diamondRaw N H A τ φ) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hcop : Nat.Coprime N q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm
  exact ⟨⟨CohCarrier.LowerSym.tMat N q hcop, CohCarrier.LowerSym.tMat_mem_Gamma0 N q hcop⟩, by simp [CohCarrier.LowerSym.tMat],
    fun φ => CohCarrier.LowerSym.main hcop φ⟩

end S_CohCarrier_exists_gamma0_heckeTlower_eq_heckeT_diamondRaw
end P2MW
export P2MW.S_CohCarrier_exists_gamma0_heckeTlower_eq_heckeT_diamondRaw (solution)
