-- Prove2me | solution 1 for CohCarrier.exists_gamma0_heckeT_iDeg_interchange_diamondRaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d82ea284-9e57-5019-92ff-1561b7343bdb

import Mathlib
import Definitions.Def_CohCarrier_Lower
import Theorems.Thm_CohCarrier_heckeT_apply_eq_sumEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_gamma0_heckeT_iDeg_interchange_diamondRaw

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open CongruenceSubgroup
open scoped MatrixGroups

namespace CohCarrier
p2m_export "CohCarrier" "rep cls slip uMat_apply_00 uMat_apply_01 uElt coe_uElt mul_inv_apply_01 rightRel_mk_eq_mk_iff coe_iotaDeg_one iotaDeg_one_mem_GammaHUpper_iff πCoset πCoset_mk gamma0Units val_gamma0Units GammaH mem_GammaH_iff GammaH_le_Gamma0 H1 conjUpperMat GammaHUpper dvd_of_mem_GammaHUpper conjL heckeT conjHom diamondRaw conjLowerMat LevelLE iotaDeg iDeg' heckeT_apply_eq_sumEquiv"
namespace DiamondInterchange
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

section ExtraCoset

variable {N : ℕ} (q : ℕ) [NeZero q]

def sigmaMat (w : SL(2, ℤ)) (hw : (q : ℤ) ∣ w 0 0) : SL(2, ℤ) :=
  ⟨!![w 0 0 / q, w 0 1; w 1 0, q * w 1 1], by
    rw [Matrix.det_fin_two_of]
    have hdet := Matrix.SpecialLinearGroup.det_coe w
    rw [Matrix.det_fin_two] at hdet
    have h1 : w 0 0 / q * (q * w 1 1) = w 0 0 * w 1 1 := by
      rw [← mul_assoc, Int.ediv_mul_cancel hw]
    rw [h1]
    exact hdet⟩

@[scoped simp] theorem sigmaMat_apply_00 (w : SL(2, ℤ)) (hw : (q : ℤ) ∣ w 0 0) : (sigmaMat q w hw) 0 0 = w 0 0 / q := rfl
@[scoped simp] theorem sigmaMat_apply_01 (w : SL(2, ℤ)) (hw : (q : ℤ) ∣ w 0 0) : (sigmaMat q w hw) 0 1 = w 0 1 := rfl
@[scoped simp] theorem sigmaMat_apply_10 (w : SL(2, ℤ)) (hw : (q : ℤ) ∣ w 0 0) : (sigmaMat q w hw) 1 0 = w 1 0 := rfl
@[scoped simp] theorem sigmaMat_apply_11 (w : SL(2, ℤ)) (hw : (q : ℤ) ∣ w 0 0) : (sigmaMat q w hw) 1 1 = q * w 1 1 := rfl

theorem sigmaMat_mem_Gamma0 (w : SL(2, ℤ)) (hw : (q : ℤ) ∣ w 0 0) (hw0 : w ∈ Gamma0 N) :
    sigmaMat q w hw ∈ Gamma0 N := by
  rw [Gamma0_mem] at hw0 ⊢
  exact hw0

theorem conjUpperMat_conj_eq (w γ : SL(2, ℤ)) (hw : (q : ℤ) ∣ w 0 0) (hγ : (q : ℤ) ∣ γ 1 0)
    (hb : (q : ℤ) ∣ (w * γ * w⁻¹) 0 1) :
    conjUpperMat q (w * γ * w⁻¹) hb = sigmaMat q w hw * conjLowerMat q γ hγ * (sigmaMat q w hw)⁻¹ := by
  obtain ⟨a', ha'⟩ := hw
  obtain ⟨c', hc'⟩ := hγ
  have hq : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hdw := Matrix.SpecialLinearGroup.det_coe w
  have hdγ := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdw hdγ
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [conjUpperMat, conjLowerMat, sigmaMat, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  rw [ha', hc'] at *
  have e1 : (q : ℤ) * a' / q = a' := by rw [mul_comm]; exact Int.mul_ediv_cancel a' hq
  have e2 : (q : ℤ) * c' / q = c' := by rw [mul_comm]; exact Int.mul_ediv_cancel c' hq
  fin_cases i <;> fin_cases j <;> simp [e1, e2]
  · ring
  · have hnum : (-((↑q * a' * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (w : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (↑q * c')) * (w : Matrix (Fin 2) (Fin 2) ℤ) 0 1) +
        (↑q * a' * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + (w : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) * (↑q * a')) =
        (q : ℤ) * (-((a' * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (w : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * c') * (w : Matrix (Fin 2) (Fin 2) ℤ) 0 1) +
          (a' * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * ↑q) + (w : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) * a') := by ring
    rw [hnum, Int.mul_ediv_cancel_left _ hq]
  · ring
  · ring

end ExtraCoset

section Cosets

variable (N : ℕ) (H : Subgroup (ZMod N)ˣ) (q : ℕ) [NeZero q]

def wMat (hcop : Nat.Coprime N q) : SL(2, ℤ) :=
  ⟨!![(q : ℤ) * Nat.gcdB N q, -Nat.gcdA N q; N, 1], by
    rw [Matrix.det_fin_two_of]
    have h := Nat.gcd_eq_gcd_ab N q
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    push_cast at h
    linear_combination -h⟩

@[scoped simp] theorem wMat_apply_00 (hcop : Nat.Coprime N q) : (wMat N q hcop) 0 0 = (q : ℤ) * Nat.gcdB N q := rfl
@[scoped simp] theorem wMat_apply_01 (hcop : Nat.Coprime N q) : (wMat N q hcop) 0 1 = -Nat.gcdA N q := rfl
@[scoped simp] theorem wMat_apply_10 (hcop : Nat.Coprime N q) : (wMat N q hcop) 1 0 = N := rfl
@[scoped simp] theorem wMat_apply_11 (hcop : Nat.Coprime N q) : (wMat N q hcop) 1 1 = 1 := rfl

theorem wMat_mem_GammaH (hcop : Nat.Coprime N q) : wMat N q hcop ∈ GammaH N H := by
  have h0 : wMat N q hcop ∈ Gamma0 N := by
    rw [Gamma0_mem]; show ((N : ℤ) : ZMod N) = 0; simp
  refine mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have e : gamma0Units N ⟨wMat N q hcop, h0⟩ = 1 := by
    apply Units.ext; rw [val_gamma0Units, Units.val_one]
    show ((1 : ℤ) : ZMod N) = 1; exact Int.cast_one
  rw [e]; exact H.one_mem

def wElt (hcop : Nat.Coprime N q) : ↥(GammaH N H) := ⟨wMat N q hcop, wMat_mem_GammaH N H q hcop⟩

@[scoped simp] theorem coe_wElt (hcop : Nat.Coprime N q) : ((wElt N H q hcop : ↥(GammaH N H)) : SL(2, ℤ)) = wMat N q hcop := rfl

theorem gcdA_ne_zero (hcop : Nat.Coprime N q) (hq1 : q ≠ 1) : ((Nat.gcdA N q : ℤ) : ZMod q) ≠ 0 := by
  intro h0
  have h := Nat.gcd_eq_gcd_ab N q
  rw [Nat.Coprime.gcd_eq_one hcop] at h
  have h' := congrArg (Int.cast : ℤ → ZMod q) h
  push_cast at h'
  rw [h0, ZMod.natCast_self] at h'
  simp only [mul_zero, zero_mul, add_zero] at h'
  haveI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq1
  exact one_ne_zero h'

variable [Fact q.Prime]

theorem mk_eq_mk_wElt_iff (hcop : Nat.Coprime N q) (hq1 : q ≠ 1) (g : ↥(GammaH N H)) :
    (Quotient.mk'' g : Quotient (QuotientGroup.rightRel (GammaHUpper N H q))) = Quotient.mk'' (wElt N H q hcop) ↔
      (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod q) = 0 := by
  rw [rightRel_mk_eq_mk_iff, mul_inv_apply_01]
  simp only [coe_wElt, wMat_apply_00, wMat_apply_01]
  push_cast
  rw [ZMod.natCast_self, zero_mul, zero_mul, neg_zero, zero_add, neg_mul, neg_eq_zero,
    mul_eq_zero]
  exact ⟨fun h => h.resolve_left (gcdA_ne_zero N q hcop hq1), fun h => Or.inr h⟩

theorem mk_eq_mk_uElt_iff (j : ℤ) (g : ↥(GammaH N H)) :
    (Quotient.mk'' g : Quotient (QuotientGroup.rightRel (GammaHUpper N H q))) = Quotient.mk'' (uElt N H j) ↔
      (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod q) = (j : ZMod q) * (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod q) := by
  rw [rightRel_mk_eq_mk_iff, mul_inv_apply_01]
  simp only [coe_uElt, uMat_apply_00, uMat_apply_01]
  push_cast
  rw [one_mul, neg_add_eq_zero, eq_comm]

noncomputable def cosetEquiv (hcop : Nat.Coprime N q) :
    Option (ZMod q) ≃ Quotient (QuotientGroup.rightRel (GammaHUpper N H q)) := by
  have hq1 : q ≠ 1 := (Fact.out : q.Prime).ne_one
  refine Equiv.ofBijective (fun o => Option.casesOn o (Quotient.mk'' (wElt N H q hcop))
    (fun j => Quotient.mk'' (uElt N H (j.val : ℤ)))) ⟨?_, ?_⟩
  · rintro (_ | j) (_ | j') h
    · rfl
    · exfalso
      have h' := ((mk_eq_mk_wElt_iff N H q hcop hq1 _).mp h.symm)
      simp [coe_uElt] at h'
    · exfalso
      have h' := ((mk_eq_mk_wElt_iff N H q hcop hq1 _).mp h)
      simp [coe_uElt] at h'
    · have h' := (mk_eq_mk_uElt_iff N H q (j'.val : ℤ) _).mp h
      simp only [coe_uElt, uMat_apply_00, uMat_apply_01, Int.cast_one, mul_one, ZMod.intCast_cast,
        ZMod.natCast_val, ZMod.cast_id', id_eq] at h'
      rw [h']
  · intro c
    induction c using Quotient.inductionOn' with
    | h g =>
      by_cases h0 : (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod q) = 0
      · exact ⟨none, ((mk_eq_mk_wElt_iff N H q hcop hq1 g).mpr h0).symm⟩
      · refine ⟨some ((((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod q) * (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod q)⁻¹), ?_⟩
        show (Quotient.mk'' (uElt N H _) : Quotient (QuotientGroup.rightRel (GammaHUpper N H q))) = Quotient.mk'' g
        rw [eq_comm, mk_eq_mk_uElt_iff]
        simp only [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id', id_eq]
        exact (inv_mul_cancel_right₀ (show (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod q) ≠ 0 from h0) _).symm

end Cosets

section TwoLevels

variable {N q : ℕ} [NeZero N] [NeZero q] [NeZero (N * q)] [Fact q.Prime]
  {H : Subgroup (ZMod N)ˣ} {H' : Subgroup (ZMod (N * q))ˣ}
  (h₁ : LevelLE N (N * q) H H' 1) (hcop : Nat.Coprime N q)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem coe00_ne_zero (g : ↥(GammaH (N * q) H')) : ((((g : SL(2, ℤ)) 0 0 : ℤ)) : ZMod q) ≠ 0 := by
  intro h0
  have hdet := Matrix.SpecialLinearGroup.det_coe (g : SL(2, ℤ))
  rw [Matrix.det_fin_two] at hdet
  have hc : ((((g : SL(2, ℤ)) 1 0 : ℤ)) : ZMod q) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hg0 : ((g : SL(2, ℤ)) : SL(2, ℤ)) ∈ Gamma0 (N * q) := (mem_GammaH_iff.mp g.2).1
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg0
    exact dvd_trans (by exact_mod_cast dvd_mul_left q N) hg0
  have h' := congrArg (Int.cast : ℤ → ZMod q) hdet
  push_cast at h'
  rw [h0, hc] at h'
  simp at h'

theorem πCoset_ne_mk_wElt (c' : Quotient (QuotientGroup.rightRel (GammaHUpper (N * q) H' q))) :
    πCoset h₁ q c' ≠ Quotient.mk'' (wElt N H q hcop) := by
  induction c' using Quotient.inductionOn' with
  | h g =>
    rw [πCoset_mk, Ne, mk_eq_mk_wElt_iff N H q hcop (Fact.out : q.Prime).ne_one, coe_iotaDeg_one]
    exact coe00_ne_zero g

theorem πCoset_injective : Function.Injective (πCoset h₁ q : _ → Quotient (QuotientGroup.rightRel (GammaHUpper N H q))) := by
  intro x y hxy
  induction x using Quotient.inductionOn' with
  | h x =>
    induction y using Quotient.inductionOn' with
    | h y =>
      rw [πCoset_mk, πCoset_mk] at hxy
      apply Quotient.sound'
      have h := Quotient.exact' hxy
      rw [QuotientGroup.rightRel_apply] at h ⊢
      rw [← map_inv, ← map_mul, iotaDeg_one_mem_GammaHUpper_iff] at h
      exact h

theorem mk_wElt_mul_iotaDeg (γ' : ↥(GammaH (N * q) H')) :
    (Quotient.mk'' (wElt N H q hcop * iotaDeg N (N * q) H H' 1 h₁ γ') :
      Quotient (QuotientGroup.rightRel (GammaHUpper N H q))) = Quotient.mk'' (wElt N H q hcop) := by
  rw [mk_eq_mk_wElt_iff N H q hcop (Fact.out : q.Prime).ne_one]
  simp only [Subgroup.coe_mul, coe_wElt, coe_iotaDeg_one, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, wMat_apply_00, wMat_apply_01]
  have hc : ((((γ' : SL(2, ℤ)) 1 0 : ℤ)) : ZMod q) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hg0 : ((γ' : SL(2, ℤ)) : SL(2, ℤ)) ∈ Gamma0 (N * q) := (mem_GammaH_iff.mp γ'.2).1
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg0
    exact dvd_trans (by exact_mod_cast dvd_mul_left q N) hg0
  push_cast
  rw [hc, ZMod.natCast_self]
  ring

theorem iotaDeg_uElt (j : ℤ) : iotaDeg N (N * q) H H' 1 h₁ (uElt (N * q) H' j) = uElt N H j :=
  Subtype.ext (by rw [coe_iotaDeg_one]; rfl)

noncomputable def optEquiv : Option (Quotient (QuotientGroup.rightRel (GammaHUpper (N * q) H' q))) ≃
    Quotient (QuotientGroup.rightRel (GammaHUpper N H q)) := by
  refine Equiv.ofBijective (fun o => Option.casesOn o (Quotient.mk'' (wElt N H q hcop)) (fun c' => πCoset h₁ q c'))
    ⟨?_, ?_⟩
  · rintro (_ | x) (_ | y) h
    · rfl
    · exact absurd h.symm (πCoset_ne_mk_wElt h₁ hcop y)
    · exact absurd h (πCoset_ne_mk_wElt h₁ hcop x)
    · rw [πCoset_injective h₁ h]
  · intro c
    induction c using Quotient.inductionOn' with
    | h g =>
      by_cases h0 : (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod q) = 0
      · exact ⟨none, ((mk_eq_mk_wElt_iff N H q hcop (Fact.out : q.Prime).ne_one g).mpr h0).symm⟩
      · refine ⟨some (Quotient.mk'' (uElt (N * q) H'
          (((((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod q) * (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod q)⁻¹).val : ℤ))), ?_⟩
        show πCoset h₁ q _ = _
        rw [πCoset_mk, iotaDeg_uElt, eq_comm, mk_eq_mk_uElt_iff]
        simp only [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id', id_eq]
        exact (inv_mul_cancel_right₀ (show (((g : SL(2, ℤ)) 0 0 : ℤ) : ZMod q) ≠ 0 from h0) _).symm

@[scoped simp] theorem optEquiv_none : optEquiv h₁ hcop none = Quotient.mk'' (wElt N H q hcop) := rfl
@[scoped simp] theorem optEquiv_some (c') : optEquiv h₁ hcop (some c') = πCoset h₁ q c' := rfl

end TwoLevels

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

end CohCarrier.DiamondInterchange
p2m_reactivate "P2MW.S_CohCarrier_exists_gamma0_heckeT_iDeg_interchange_diamondRaw.CohCarrier P2MW.S_CohCarrier_exists_gamma0_heckeT_iDeg_interchange_diamondRaw.CohCarrier.DiamondInterchange"
p2m_reactivate "P2MW.S_CohCarrier_exists_gamma0_heckeT_iDeg_interchange_diamondRaw.CohCarrier"

open _root_.CohCarrier _root_.P2MW.S_CohCarrier_exists_gamma0_heckeT_iDeg_interchange_diamondRaw.CohCarrier CohCarrier.DiamondInterchange CongruenceSubgroup in
open scoped MatrixGroups in
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex in

theorem solution
    {N q : ℕ} [NeZero N] [NeZero q] {A : Type} [AddCommGroup A] [NeZero (N * q)]
    (hqp : q.Prime) (hqN : ¬ q ∣ N)
    (H : Subgroup (ZMod N)ˣ) (H' : Subgroup (ZMod (N * q))ˣ)
    (h₁ : LevelLE N (N * q) H H' 1) (hq : LevelLE N (N * q) H H' q) :
    ∃ σ : Gamma0 N, ((((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = q) ∧
      ∀ φ : H1 N H A,
        heckeT (N * q) H' q A (iDeg' N (N * q) H H' 1 A h₁ φ)
          = iDeg' N (N * q) H H' 1 A h₁ (heckeT N H q A φ)
              - iDeg' N (N * q) H H' q A hq (diamondRaw N H A σ φ) := by
  haveI : Fact q.Prime := ⟨hqp⟩
  have hcop : Nat.Coprime N q := ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqN).symm
  have hw : (q : ℤ) ∣ (wMat N q hcop) 0 0 := ⟨Nat.gcdB N q, rfl⟩
  have hw0 : wMat N q hcop ∈ Gamma0 N := GammaH_le_Gamma0 H (wMat_mem_GammaH N H q hcop)
  let σ : Gamma0 N := ⟨sigmaMat q (wMat N q hcop) hw, sigmaMat_mem_Gamma0 q _ hw hw0⟩
  refine ⟨σ, by simp [σ, sigmaMat], fun φ => ?_⟩

  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨γ', rfl⟩ : ∃ γ', Additive.ofMul γ' = x := ⟨Additive.toMul x, rfl⟩
  set S := GammaHUpper N H q with hS
  set S' := GammaHUpper (N * q) H' q with hS'
  set γ := iotaDeg N (N * q) H H' 1 h₁ γ' with hγ
  let ψ : Additive ↥S →+ A := φ.comp (MonoidHom.toAdditive (conjL N H q))

  have eL : heckeT (N * q) H' q A (iDeg' N (N * q) H H' 1 A h₁ φ) (Additive.ofMul γ') =
      ∑ c' : Quotient (QuotientGroup.rightRel S'),
        φ (Additive.ofMul (iotaDeg N (N * q) H H' 1 h₁ (conjL (N * q) H' q (slip S' c' γ')))) :=
    heckeT_apply_eq_sumEquiv (N * q) H' q (Equiv.refl _) _ γ'
  have eT : iDeg' N (N * q) H H' 1 A h₁ (heckeT N H q A φ) (Additive.ofMul γ') =
      ψ (Additive.ofMul (slip S (Quotient.mk'' (wElt N H q hcop)) γ)) +
        ∑ c' : Quotient (QuotientGroup.rightRel S'), ψ (Additive.ofMul (slip S (πCoset h₁ q c') γ)) := by
    change heckeT N H q A φ (Additive.ofMul γ) = _
    rw [heckeT_apply_eq_sumEquiv N H q (optEquiv h₁ hcop) φ γ, Fintype.sum_option]
    rfl
  have eD : iDeg' N (N * q) H H' q A hq (diamondRaw N H A σ φ) (Additive.ofMul γ') =
      φ (Additive.ofMul (conjHom N H σ (iotaDeg N (N * q) H H' q hq γ'))) := rfl
  have hγcoe : ((γ : ↥(GammaH N H)) : SL(2, ℤ)) = (γ' : SL(2, ℤ)) := coe_iotaDeg_one h₁ γ'
  have hstab : cls S ((wElt N H q hcop : ↥(GammaH N H)) * γ) = Quotient.mk'' (wElt N H q hcop) :=
    mk_wElt_mul_iotaDeg h₁ hcop γ'

  have e1 : ψ (Additive.ofMul (slip S (Quotient.mk'' (wElt N H q hcop)) γ)) =
      φ (Additive.ofMul (conjHom N H σ (iotaDeg N (N * q) H H' q hq γ'))) := by
    classical
    let t : Quotient (QuotientGroup.rightRel S) → ↥(GammaH N H) := fun c =>
      if c = Quotient.mk'' (wElt N H q hcop) then (wElt N H q hcop : ↥(GammaH N H)) else rep S c
    have ht : ∀ c, cls S (t c) = c := fun c => by
      by_cases hc : c = Quotient.mk'' (wElt N H q hcop)
      · simp only [t, hc, if_true]
        try rfl
      · simp only [t, hc, if_false]
        exact cls_rep S c
    have htw : t (Quotient.mk'' (wElt N H q hcop)) = wElt N H q hcop := by simp [t]
    have key := sum_slip_eq_sum_of_reps S ψ γ {Quotient.mk'' (wElt N H q hcop)}
      (fun c hc => by
        rw [Finset.mem_singleton] at hc ⊢
        rw [hc, show (Quotient.mk'' (wElt N H q hcop) : Quotient (QuotientGroup.rightRel S)) = cls S (wElt N H q hcop) from rfl,
          cls_rep_mul, hstab])
      (fun c hc => ⟨Quotient.mk'' (wElt N H q hcop), Finset.mem_singleton_self _, by
        rw [Finset.mem_singleton] at hc
        rw [hc, show (Quotient.mk'' (wElt N H q hcop) : Quotient (QuotientGroup.rightRel S)) = cls S (wElt N H q hcop) from rfl,
          cls_rep_mul, hstab]⟩)
      t ht
    rw [Finset.sum_singleton, Finset.sum_singleton] at key
    rw [key]

    have hmem : (wElt N H q hcop : ↥(GammaH N H)) * γ * (wElt N H q hcop : ↥(GammaH N H))⁻¹ ∈ S := by
      have := rep_mul_mul_inv_mem S t ht (Quotient.mk'' (wElt N H q hcop)) γ
      rwa [htw, hstab, htw] at this
    have hel : (⟨t (Quotient.mk'' (wElt N H q hcop)) * γ * (t (cls S (t (Quotient.mk'' (wElt N H q hcop)) * γ)))⁻¹,
        rep_mul_mul_inv_mem S t ht _ γ⟩ : ↥S) = ⟨_, hmem⟩ := by
      apply Subtype.ext
      simp only [htw, hstab]
    rw [hel]

    show φ (Additive.ofMul (conjL N H q ⟨_, hmem⟩)) = _
    congr 2
    apply Subtype.ext
    change conjUpperMat q (((wElt N H q hcop : ↥(GammaH N H)) * γ * (wElt N H q hcop : ↥(GammaH N H))⁻¹ : ↥(GammaH N H)) : SL(2, ℤ))
        (dvd_of_mem_GammaHUpper N H q ⟨_, hmem⟩) =
      (σ : SL(2, ℤ)) * conjLowerMat q (γ' : SL(2, ℤ)) (hq.dvd_entry γ') * (σ : SL(2, ℤ))⁻¹
    have hb : (q : ℤ) ∣ ((wMat N q hcop) * (γ' : SL(2, ℤ)) * (wMat N q hcop)⁻¹) 0 1 := by
      have := dvd_of_mem_GammaHUpper N H q ⟨_, hmem⟩
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, hγcoe] using this
    convert conjUpperMat_conj_eq q (wMat N q hcop) (γ' : SL(2, ℤ)) hw (hq.dvd_entry γ') hb using 2
    · simp [Subgroup.coe_mul, Subgroup.coe_inv, hγcoe]

  have hconj : ∀ (X Y : SL(2, ℤ)) (hX : (q : ℤ) ∣ X 0 1) (hY : (q : ℤ) ∣ Y 0 1), X = Y →
      conjUpperMat q X hX = conjUpperMat q Y hY := by
    rintro X Y hX hY rfl; rfl
  have e2 : ∑ c' : Quotient (QuotientGroup.rightRel S'), ψ (Additive.ofMul (slip S (πCoset h₁ q c') γ)) =
      ∑ c' : Quotient (QuotientGroup.rightRel S'),
        φ (Additive.ofMul (iotaDeg N (N * q) H H' 1 h₁ (conjL (N * q) H' q (slip S' c' γ')))) := by
    classical
    have hinj : Set.InjOn (πCoset h₁ q) (Finset.univ : Finset (Quotient (QuotientGroup.rightRel S'))) :=
      (πCoset_injective h₁).injOn
    let X : Finset (Quotient (QuotientGroup.rightRel S)) := Finset.univ.image (πCoset h₁ q)
    let t : Quotient (QuotientGroup.rightRel S) → ↥(GammaH N H) := fun c =>
      Option.casesOn ((optEquiv h₁ hcop).symm c) (wElt N H q hcop : ↥(GammaH N H))
        (fun c' => iotaDeg N (N * q) H H' 1 h₁ (rep S' c'))
    have htsome : ∀ c', t (πCoset h₁ q c') = iotaDeg N (N * q) H H' 1 h₁ (rep S' c') := fun c' => by
      have : (optEquiv h₁ hcop).symm (πCoset h₁ q c') = some c' := by
        rw [Equiv.symm_apply_eq]; rfl
      simp only [t, this]
    have hclsι : ∀ g' : ↥(GammaH (N * q) H'), cls S (iotaDeg N (N * q) H H' 1 h₁ g') = πCoset h₁ q (cls S' g') :=
      fun g' => (πCoset_mk h₁ q g').symm
    have ht : ∀ c, cls S (t c) = c := fun c => by
      rcases hoc : (optEquiv h₁ hcop).symm c with _ | c'
      · have hc : c = Quotient.mk'' (wElt N H q hcop) := by
          have := ((optEquiv h₁ hcop).symm_apply_eq.mp hoc); simpa using this
        simp only [t, hoc]
        exact hc.symm
      · have hc : c = πCoset h₁ q c' := by
          have := ((optEquiv h₁ hcop).symm_apply_eq.mp hoc); simpa using this
        simp only [t, hoc]
        rw [hclsι, cls_rep, hc]
    have hX : ∀ c ∈ X, cls S (rep S c * γ) ∈ X := by
      intro c hc
      obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hc
      induction c' using Quotient.inductionOn' with
      | h g' =>
        refine Finset.mem_image.mpr ⟨Quotient.mk'' (g' * γ'), Finset.mem_univ _, ?_⟩
        rw [πCoset_mk, πCoset_mk, map_mul]
        exact (cls_rep_mul S _ _).symm
    have hXsurj : ∀ c ∈ X, ∃ c₀ ∈ X, cls S (rep S c₀ * γ) = c := by
      intro c hc
      obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hc
      induction c' using Quotient.inductionOn' with
      | h g' =>
        refine ⟨πCoset h₁ q (Quotient.mk'' (g' * γ'⁻¹)), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
        rw [πCoset_mk, πCoset_mk, show (Quotient.mk'' (iotaDeg N (N * q) H H' 1 h₁ (g' * γ'⁻¹)) : Quotient (QuotientGroup.rightRel S)) =
          cls S (iotaDeg N (N * q) H H' 1 h₁ (g' * γ'⁻¹)) from rfl, cls_rep_mul, map_mul, map_inv,
          inv_mul_cancel_right]
        try rfl
    have key := sum_slip_eq_sum_of_reps S ψ γ X hX hXsurj t ht
    rw [← Finset.sum_image (f := fun c => ψ (Additive.ofMul (slip S c γ))) hinj]
    change ∑ c ∈ X, ψ (Additive.ofMul (slip S c γ)) = _
    rw [key, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun c' _ => ?_

    have hval : t (πCoset h₁ q c') * γ * (t (cls S (t (πCoset h₁ q c') * γ)))⁻¹ =
        iotaDeg N (N * q) H H' 1 h₁ (slip S' c' γ' : ↥(GammaH (N * q) H')) := by
      rw [htsome, ← map_mul, hclsι, htsome, ← map_inv, ← map_mul]
      rfl
    have hmem2 : iotaDeg N (N * q) H H' 1 h₁ (slip S' c' γ' : ↥(GammaH (N * q) H')) ∈ S := by
      rw [← hval]; exact rep_mul_mul_inv_mem S t ht _ γ
    have hel : (⟨t (πCoset h₁ q c') * γ * (t (cls S (t (πCoset h₁ q c') * γ)))⁻¹, rep_mul_mul_inv_mem S t ht _ γ⟩ : ↥S) =
        ⟨iotaDeg N (N * q) H H' 1 h₁ (slip S' c' γ' : ↥(GammaH (N * q) H')), hmem2⟩ :=
      Subtype.ext hval
    rw [hel]
    show φ (Additive.ofMul (conjL N H q ⟨_, hmem2⟩)) = _
    congr 2
    apply Subtype.ext
    rw [coe_iotaDeg_one]
    exact hconj _ _ (dvd_of_mem_GammaHUpper N H q ⟨_, hmem2⟩) (dvd_of_mem_GammaHUpper (N * q) H' q (slip S' c' γ'))
      (coe_iotaDeg_one h₁ _)

  rw [eL, AddMonoidHom.sub_apply, eT, eD, e1, e2]
  abel

end S_CohCarrier_exists_gamma0_heckeT_iDeg_interchange_diamondRaw
end P2MW
export P2MW.S_CohCarrier_exists_gamma0_heckeT_iDeg_interchange_diamondRaw (solution)
