-- Prove2me | solution 1 for CuspForm.petersson_heckeTLin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/473f94a8-afd5-5cfb-baeb-5baf547b5584

import Definitions.Def_CuspForm_Petersson
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_AutomorphicForm_ModularFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_petersson_heckeTLin

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace AlliAux1R6

theorem mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem mapGL_injective : Function.Injective
    (fun s : SL(2, ℤ) => (Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ)) := by
  intro s t h
  apply Subtype.ext
  ext i j
  have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  simpa [mapGL_coe_eq, Matrix.map_apply] using this

theorem mem_Gamma0_iff_dvd (M : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma0 M ↔ (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem mul_apply_10 (A B : SL(2, ℤ)) :
    ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (B : Matrix (Fin 2) (Fin 2) ℤ) 0 0
        + (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (B : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem Gamma0_mul_le (N p : ℕ) :
    CongruenceSubgroup.Gamma0 (N * p) ≤ CongruenceSubgroup.Gamma0 N := by
  intro γ hγ
  rw [mem_Gamma0_iff_dvd] at hγ ⊢
  push_cast at hγ
  exact (dvd_mul_right (N : ℤ) p).trans hγ

structure Bez (N p : ℕ) where
  u : ℤ
  v : ℤ
  huv : (p : ℤ) * u - N * v = 1

theorem Bez.nonempty {N p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) : Nonempty (Bez N p) := by
  have hc : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  obtain ⟨a, b, h⟩ := Nat.isCoprime_iff_coprime.mpr hc
  exact ⟨⟨a, -b, by linear_combination h⟩⟩

namespace Bez

variable {N p : ℕ} (Z : Bez N p)

def γ₁ : SL(2, ℤ) := ⟨!![(p : ℤ) * Z.u, Z.v; N, 1], by
  rw [Matrix.det_fin_two_of]; linear_combination Z.huv⟩

def γ₂ : SL(2, ℤ) := ⟨!![Z.u, Z.v; N, p], by
  rw [Matrix.det_fin_two_of]; linear_combination Z.huv⟩

theorem γ₁_coe : ((Z.γ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![(p : ℤ) * Z.u, Z.v; N, 1] := rfl
theorem γ₂_coe : ((Z.γ₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![Z.u, Z.v; N, p] := rfl

theorem γ₁_mem : Z.γ₁ ∈ CongruenceSubgroup.Gamma0 N := by
  rw [mem_Gamma0_iff_dvd, γ₁_coe]; simp

theorem γ₂_mem : Z.γ₂ ∈ CongruenceSubgroup.Gamma0 N := by
  rw [mem_Gamma0_iff_dvd, γ₂_coe]; simp

def r : Option (Fin p) → SL(2, ℤ)
  | none => 1
  | some j => Z.γ₂ * ModularGroup.T ^ ((j : ℕ) : ℤ)

theorem r_mem (i : Option (Fin p)) : Z.r i ∈ CongruenceSubgroup.Gamma0 N := by
  cases i with
  | none => exact one_mem _
  | some j =>
    refine mul_mem Z.γ₂_mem ?_
    rw [mem_Gamma0_iff_dvd, ModularGroup.coe_T_zpow]
    simp

theorem T_zpow_coe (t : ℤ) :
    ((ModularGroup.T ^ t : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, t; 0, 1] :=
  ModularGroup.coe_T_zpow t

theorem lowerLeft_γ₂_T_mul (t : ℤ) (γ : SL(2, ℤ)) :
    ((Z.γ₂ * ModularGroup.T ^ t * γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = N * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + t * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
        + p * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [mul_apply_10, Matrix.SpecialLinearGroup.coe_mul, γ₂_coe, T_zpow_coe, Matrix.mul_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

theorem lowerLeft_γ₂_T_γ₂_inv (t : ℤ) :
    ((Z.γ₂ * ModularGroup.T ^ t * Z.γ₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = -((N : ℤ) * N * t) := by
  rw [lowerLeft_γ₂_T_mul, Matrix.SpecialLinearGroup.coe_inv, γ₂_coe, Matrix.adjugate_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

theorem lowerLeft_γ₂_T_inv (t : ℤ) :
    (((Z.γ₂ * ModularGroup.T ^ t)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(N : ℤ) := by
  rw [mul_inv_rev, ← zpow_neg, mul_apply_10, Matrix.SpecialLinearGroup.coe_inv, γ₂_coe, T_zpow_coe,
    Matrix.adjugate_fin_two]
  simp

theorem N_ne_zero (hpN : ¬ p ∣ N) : N ≠ 0 := fun h => hpN (h ▸ dvd_zero p)

variable (hp : p.Prime) (hpN : ¬ p ∣ N)
include hp hpN

theorem coprime_int : IsCoprime (N : ℤ) (p : ℤ) :=
  (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN)).symm

theorem not_Np_dvd_N : ¬ ((N * p : ℕ) : ℤ) ∣ (N : ℤ) := by
  intro h
  have hN := N_ne_zero hpN
  have h' : N * p ∣ N := by exact_mod_cast h
  have : N * p ≤ N * 1 := by rw [mul_one]; exact Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h'
  have := Nat.le_of_mul_le_mul_left this (Nat.pos_of_ne_zero hN)
  exact absurd this (by have := hp.one_lt; omega)

theorem exists_r_mul_mem (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ i, Z.r i * γ ∈ CongruenceSubgroup.Gamma0 (N * p) := by
  haveI := Fact.mk hp
  have hN : (N : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := (mem_Gamma0_iff_dvd N γ).mp hγ
  by_cases hc : (p : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  · refine ⟨none, ?_⟩
    show 1 * γ ∈ _
    rw [one_mul, mem_Gamma0_iff_dvd]
    push_cast
    exact (coprime_int hp hpN).mul_dvd hN hc
  ·
    set a : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
    set c : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
    have hc0 : (c : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    set j0 : ZMod p := -(a : ZMod p) / (c : ZMod p) with hj0
    refine ⟨some ⟨j0.val, ZMod.val_lt j0⟩, ?_⟩
    show Z.γ₂ * ModularGroup.T ^ ((j0.val : ℕ) : ℤ) * γ ∈ _
    rw [mem_Gamma0_iff_dvd, lowerLeft_γ₂_T_mul]
    push_cast
    refine (coprime_int hp hpN).mul_dvd ?_ ?_
    · exact Dvd.dvd.add (dvd_mul_right _ _) ((hN).mul_left _)
    · refine Dvd.dvd.add (Dvd.dvd.mul_left ?_ _) (dvd_mul_right _ _)
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, hj0]
      field_simp
      ring

theorem r_mul_r_inv_mem (i i' : Option (Fin p))
    (h : Z.r i * (Z.r i')⁻¹ ∈ CongruenceSubgroup.Gamma0 (N * p)) : i = i' := by
  rw [mem_Gamma0_iff_dvd] at h
  cases i with
  | none =>
    cases i' with
    | none => rfl
    | some j' =>
      exfalso
      refine not_Np_dvd_N hp hpN ?_
      have : Z.r none * (Z.r (some j'))⁻¹ = (Z.γ₂ * ModularGroup.T ^ ((j' : ℕ) : ℤ))⁻¹ :=
        one_mul _
      rw [this, lowerLeft_γ₂_T_inv] at h
      exact (dvd_neg.mp h)
  | some j =>
    cases i' with
    | none =>
      exfalso
      refine not_Np_dvd_N hp hpN ?_
      have : Z.r (some j) * (Z.r none)⁻¹ = Z.γ₂ * ModularGroup.T ^ ((j : ℕ) : ℤ) * 1 := by
        show Z.γ₂ * ModularGroup.T ^ ((j : ℕ) : ℤ) * (1 : SL(2, ℤ))⁻¹ = _
        rw [inv_one]
      rw [this, lowerLeft_γ₂_T_mul] at h
      simpa using h
    | some j' =>
      congr 1
      apply Fin.ext
      have hj := j.isLt
      have hj' := j'.isLt
      have : Z.r (some j) * (Z.r (some j'))⁻¹
          = Z.γ₂ * ModularGroup.T ^ (((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ)) * Z.γ₂⁻¹ := by
        show Z.γ₂ * ModularGroup.T ^ ((j : ℕ) : ℤ) * (Z.γ₂ * ModularGroup.T ^ ((j' : ℕ) : ℤ))⁻¹ = _
        rw [mul_inv_rev, ← zpow_neg, zpow_sub]
        group
      rw [this, lowerLeft_γ₂_T_γ₂_inv] at h
      push_cast at h
      have h1 : (p : ℤ) ∣ (N : ℤ) * N * (((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ)) :=
        (Dvd.intro_left _ rfl : (p : ℤ) ∣ (N : ℤ) * p).trans (dvd_neg.mp h)
      have h2 : (p : ℤ) ∣ ((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ) := by
        have hcop : IsCoprime ((N : ℤ) * N) (p : ℤ) :=
          (coprime_int hp hpN).mul_left (coprime_int hp hpN)
        exact hcop.symm.dvd_of_dvd_mul_left h1
      have h3 : ((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ) = 0 :=
        Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_lt]; constructor <;> omega)
      omega

end Bez

section unfold

variable {Γ Λ : Subgroup SL(2, ℤ)} (hΛΓ : Λ ≤ Γ)
  {ι : Type*} (r : ι → SL(2, ℤ)) (hr : ∀ i, r i ∈ Γ)
  (hex : ∀ γ ∈ Γ, ∃ i, r i * γ ∈ Λ) (huniq : ∀ i i', r i * (r i')⁻¹ ∈ Λ → i = i')

def eMap (r : ι → SL(2, ℤ)) (x : (SL(2, ℤ) ⧸ Γ) × ι) : SL(2, ℤ) ⧸ Λ :=
  QuotientGroup.mk (x.1.out * (r x.2)⁻¹)

include hΛΓ hr hex huniq in
theorem eMap_bijective : Function.Bijective (eMap (Γ := Γ) (Λ := Λ) r) := by
  constructor
  · rintro ⟨q, i⟩ ⟨q', i'⟩ h
    have hmem : r i * q.out⁻¹ * q'.out * (r i')⁻¹ ∈ Λ := by
      have := QuotientGroup.eq.mp h
      simpa [mul_assoc, mul_inv_rev] using this
    have hqq : q = q' := by
      have hΓ : q.out⁻¹ * q'.out ∈ Γ := by
        have h1 : (r i)⁻¹ * (r i * q.out⁻¹ * q'.out * (r i')⁻¹) * r i' ∈ Γ :=
          mul_mem (mul_mem (inv_mem (hr i)) (hΛΓ hmem)) (hr i')
        simpa [mul_assoc] using h1
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      exact QuotientGroup.eq.mpr hΓ
    subst hqq
    have : r i * (r i')⁻¹ ∈ Λ := by simpa using hmem
    rw [huniq i i' this]
  · intro y
    set σ := y.out
    set q : SL(2, ℤ) ⧸ Γ := QuotientGroup.mk σ
    have hγ : q.out⁻¹ * σ ∈ Γ := by
      rw [← QuotientGroup.eq]
      exact QuotientGroup.out_eq' q
    obtain ⟨i, hi⟩ := hex _ hγ
    refine ⟨(q, i), ?_⟩
    rw [← QuotientGroup.out_eq' y]
    show QuotientGroup.mk (q.out * (r i)⁻¹) = QuotientGroup.mk σ
    rw [QuotientGroup.eq]
    simpa [mul_assoc, mul_inv_rev] using hi

variable [Fintype (SL(2, ℤ) ⧸ Γ)] [Fintype (SL(2, ℤ) ⧸ Λ)] [Fintype ι]

include hΛΓ hr hex huniq in

theorem unfold_sum {X : Type*} [AddCommMonoid X] (Φ : ℍ → X)
    (hΦ : ∀ h ∈ Λ, ∀ x : ℍ, Φ (h • x) = Φ x) (τ : ℍ) :
    ∑ q' : SL(2, ℤ) ⧸ Λ, Φ ((q'.out⁻¹ : SL(2, ℤ)) • τ)
      = ∑ q : SL(2, ℤ) ⧸ Γ, ∑ i, Φ ((r i * q.out⁻¹ : SL(2, ℤ)) • τ) := by
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective (eMap (Γ := Γ) (Λ := Λ) r)
    (eMap_bijective hΛΓ r hr hex huniq) _ _ fun x => ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Λ (x.1.out * (r x.2)⁻¹)
  show Φ ((r x.2 * x.1.out⁻¹ : SL(2, ℤ)) • τ) = Φ (((eMap r x).out⁻¹ : SL(2, ℤ)) • τ)
  rw [eMap, hh, mul_inv_rev, mul_inv_rev, inv_inv, mul_smul ((h : SL(2, ℤ))⁻¹) (r x.2 * x.1.out⁻¹) τ,
    hΦ _ (inv_mem h.2)]

end unfold

section hecke

variable {N p : ℕ} (Z : Bez N p)

def Sc (p : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℝ :=
  upperTriangularGL p 0 p (by exact_mod_cast Nat.mul_ne_zero hp hp)

theorem slash_Sc (k : ℤ) {p : ℕ} (hp : p ≠ 0) (f : ℍ → ℂ) :
    f ∣[k] Sc p hp = ((p : ℂ) ^ (k - 2)) • f := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hdet : ((Sc p hp).det : ℝ) = ((p * p : ℕ) : ℝ) := by
    push_cast
    simp [Sc, Matrix.det_fin_two_of]
  have hdetpos : 0 < ((Sc p hp).det : ℝ) := by rw [hdet]; positivity
  have hσ : UpperHalfPlane.σ (Sc p hp) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, if_pos hdetpos]
  funext τ
  have hdenom : UpperHalfPlane.denom (Sc p hp) τ = p := by
    simp [UpperHalfPlane.denom, Sc]
  have hsmul : (Sc p hp • τ : ℍ) = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos, hdenom]
    simp [UpperHalfPlane.num, Sc, hpC]
  rw [ModularForm.slash_apply, hσ, hdet, hdenom, hsmul, Pi.smul_apply, smul_eq_mul]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  push_cast
  rw [show ((p : ℂ) * p) = (p : ℂ) ^ (2 : ℤ) by rw [zpow_two], ← zpow_mul, mul_assoc,
    ← zpow_add₀ hpC, show (2 : ℤ) * (k - 1) + -k = k - 2 by ring, mul_comm]

set_option linter.unnecessarySeqFocus false in

theorem heckeDiagMatrix_mul_γ₂ (hp : p ≠ 0) :
    heckeDiagMatrix p * (Matrix.SpecialLinearGroup.mapGL ℝ Z.γ₂ : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ Z.γ₁ : GL (Fin 2) ℝ) * heckeMatrix p 0 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeDiagMatrix hp, val_heckeMatrix hp, mapGL_coe_eq,
    mapGL_coe_eq, Bez.γ₂_coe, Bez.γ₁_coe]
  ext i k; fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] <;> ring

theorem heckeMatrix_eq (hp : p ≠ 0) (j : ℕ) :
    heckeMatrix p j
      = heckeMatrix p 0 * (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (j : ℤ)) :
          GL (Fin 2) ℝ) := by
  apply Units.ext
  rw [Units.val_mul, val_heckeMatrix hp, val_heckeMatrix hp, mapGL_coe_eq, Bez.T_zpow_coe]
  ext i k; fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]

theorem heckeMatrix_zero_mul_heckeDiagMatrix (hp : p ≠ 0) :
    heckeMatrix p 0 * heckeDiagMatrix p = Sc p hp := by
  apply Units.ext
  rw [Units.val_mul, val_heckeMatrix hp, val_heckeDiagMatrix hp]
  show _ = ((upperTriangularGL (p : ℝ) 0 p _ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [val_upperTriangularGL]
  ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable {k : ℤ}

theorem slash_mem (g : CuspForm (CongruenceSubgroup.Gamma0 N) k) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ⇑g ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g :=
  SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)

theorem slash_heckeMatrix_eq (hp : p ≠ 0) (g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (j : ℕ) :
    ⇑g ∣[k] heckeMatrix p j
      = (⇑g ∣[k] heckeDiagMatrix p) ∣[k]
          (Matrix.SpecialLinearGroup.mapGL ℝ (Z.γ₂ * ModularGroup.T ^ (j : ℤ)) : GL (Fin 2) ℝ) := by
  have hM0 : heckeMatrix p 0
      = (Matrix.SpecialLinearGroup.mapGL ℝ Z.γ₁ : GL (Fin 2) ℝ)⁻¹ * heckeDiagMatrix p
          * (Matrix.SpecialLinearGroup.mapGL ℝ Z.γ₂ : GL (Fin 2) ℝ) := by
    rw [mul_assoc, heckeDiagMatrix_mul_γ₂ Z hp, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [heckeMatrix_eq hp j, hM0, map_mul, ← map_inv]
  simp only [SlashAction.slash_mul, slash_mem g (inv_mem Z.γ₁_mem)]

theorem heckeT_eq_sum_r (hp : p ≠ 0) (g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    heckeT k p ⇑g
      = ∑ i : Option (Fin p), (⇑g ∣[k] heckeDiagMatrix p) ∣[k]
          (Matrix.SpecialLinearGroup.mapGL ℝ (Z.r i) : GL (Fin 2) ℝ) := by
  rw [heckeT_eq_heckeU_add, heckeU_def, Fintype.sum_option, add_comm, Finset.sum_range]
  congr 1
  · show _ = (⇑g ∣[k] heckeDiagMatrix p) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ 1 : GL (Fin 2) ℝ)
    rw [map_one, SlashAction.slash_one]
  · exact Finset.sum_congr rfl fun j _ => slash_heckeMatrix_eq Z hp g j

end hecke

section petpt

variable {N p : ℕ} {k : ℤ}

theorem petersson_smul_right (k : ℤ) (f g : ℍ → ℂ) (c : ℂ) (τ : ℍ) :
    UpperHalfPlane.petersson k f (c • g) τ = c * UpperHalfPlane.petersson k f g τ := by
  simp only [UpperHalfPlane.petersson, Pi.smul_apply, smul_eq_mul]; ring

theorem petersson_sum_right {ι : Type*} (s : Finset ι) (k : ℤ) (f : ℍ → ℂ) (g : ι → ℍ → ℂ)
    (τ : ℍ) : UpperHalfPlane.petersson k f (∑ i ∈ s, g i) τ
      = ∑ i ∈ s, UpperHalfPlane.petersson k f (g i) τ := by
  simp only [UpperHalfPlane.petersson, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]

theorem petersson_smul_SL (k : ℤ) (F G : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.petersson k F G (γ • τ)
      = UpperHalfPlane.petersson k (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ))
          (G ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ :=
  (UpperHalfPlane.petersson_slash_SL k F G γ τ).symm

theorem mapGL_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) • τ = γ • τ :=
  (MulAction.compHom_smul_def _ γ τ).symm

variable (Z : Bez N p) (hp : p.Prime) (hpN : ¬ p ∣ N)
include hp hpN

def κ : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ Z.γ₂ : GL (Fin 2) ℝ) * heckeDiagMatrix p

omit hp hpN in
theorem κ_def : κ Z = (Matrix.SpecialLinearGroup.mapGL ℝ Z.γ₂ : GL (Fin 2) ℝ) * heckeDiagMatrix p := rfl

omit hpN in

theorem petersson_transport (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    UpperHalfPlane.petersson k (⇑f ∣[k] heckeDiagMatrix p) ⇑g τ
      = UpperHalfPlane.petersson k ⇑f (⇑g ∣[k] heckeDiagMatrix p) (κ Z • τ) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
  set α : GL (Fin 2) ℝ := heckeDiagMatrix p with hα
  set H : ℍ → ℂ := ⇑g ∣[k] heckeMatrix p 0 with hH

  have hR : UpperHalfPlane.petersson k ⇑f (⇑g ∣[k] α) (κ Z • τ)
      = UpperHalfPlane.petersson k ⇑f H (α • τ) := by
    rw [κ_def, mul_smul, mapGL_smul, petersson_smul_SL, slash_mem f Z.γ₂_mem, ← SlashAction.slash_mul,
      heckeDiagMatrix_mul_γ₂ Z hp0, SlashAction.slash_mul, slash_mem g Z.γ₁_mem]

  have hg : (⇑g : ℍ → ℂ) = ((p : ℂ) ^ (2 - k)) • (H ∣[k] α) := by
    rw [hH, ← SlashAction.slash_mul, heckeMatrix_zero_mul_heckeDiagMatrix hp0, slash_Sc k hp0,
      smul_smul, ← zpow_add₀ hpC, show (2 - k) + (k - 2) = 0 by ring, zpow_zero, one_smul]
  have hL : UpperHalfPlane.petersson k (⇑f ∣[k] α) ⇑g τ
      = UpperHalfPlane.petersson k ⇑f H (α • τ) := by
    rw [hg, petersson_smul_right, UpperHalfPlane.petersson_slash, σ_heckeDiagMatrix,
      det_heckeDiagMatrix hp0]
    simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
    rw [← mul_assoc, ← zpow_add₀ hpC, show (2 - k) + (k - 2) = 0 by ring, zpow_zero, one_mul]
  rw [hL, hR]

end petpt

section adjraise

theorem one_mul_dvd {N p : ℕ} : 1 * N ∣ N * p := ⟨p, by ring⟩
theorem p_mul_dvd {N p : ℕ} : p * N ∣ N * p := ⟨1, by ring⟩

scoped instance fintypeQuot (M : ℕ) [NeZero M] : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M) :=
  haveI : Finite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

variable {N p : ℕ} {k : ℤ} [NeZero N] [NeZero (N * p)] (Z : Bez N p) (hp : p.Prime) (hpN : ¬ p ∣ N)
include Z hp hpN

theorem integrand_heckeT (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    CuspForm.peterssonIntegrand f (CuspForm.heckeTLin k hp hpN g) τ
      = CuspForm.peterssonIntegrand
          (FreyPackage.ModMCarrier.rescaleLin (one_mul_dvd (N := N) (p := p)) k f)
          (FreyPackage.ModMCarrier.rescaleLin (p_mul_dvd (N := N) (p := p)) k g) τ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set F := FreyPackage.ModMCarrier.rescaleLin (one_mul_dvd (N := N) (p := p)) k f with hF
  set G := FreyPackage.ModMCarrier.rescaleLin (p_mul_dvd (N := N) (p := p)) k g with hG
  have hFc : (⇑F : ℍ → ℂ) = ⇑f := by
    rw [hF, FreyPackage.ModMCarrier.coe_rescaleLin_apply]
    have : heckeDiagMatrix 1 = 1 := by
      apply Units.ext; rw [val_heckeDiagMatrix one_ne_zero, Units.val_one]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [this, SlashAction.slash_one]
  have hGc : (⇑G : ℍ → ℂ) = ⇑g ∣[k] heckeDiagMatrix p := by
    rw [hG, FreyPackage.ModMCarrier.coe_rescaleLin_apply]

  unfold CuspForm.peterssonIntegrand
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]

  have hΛ : ∀ q' : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 (N * p),
      UpperHalfPlane.petersson k (⇑F ∣[k] (q'.out⁻¹ : SL(2, ℤ))) (⇑G ∣[k] (q'.out⁻¹ : SL(2, ℤ))) τ
        = UpperHalfPlane.petersson k ⇑F ⇑G ((q'.out⁻¹ : SL(2, ℤ)) • τ) := fun q' =>
    UpperHalfPlane.petersson_slash_SL k _ _ _ τ
  have hΓ : ∀ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      UpperHalfPlane.petersson k (⇑f ∣[k] (q.out⁻¹ : SL(2, ℤ)))
          (⇑(CuspForm.heckeTLin k hp hpN g) ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ
        = ∑ i : Option (Fin p), UpperHalfPlane.petersson k ⇑F ⇑G ((Z.r i * q.out⁻¹ : SL(2, ℤ)) • τ) := by
    intro q
    rw [UpperHalfPlane.petersson_slash_SL, CuspForm.coe_heckeTLin_apply, heckeT_eq_sum_r Z hp.ne_zero,
      petersson_sum_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul, petersson_smul_SL k ⇑F ⇑G (Z.r i), hFc, hGc, slash_mem f (Z.r_mem i)]
  simp_rw [hΛ, hΓ]
  exact (unfold_sum (Gamma0_mul_le N p) Z.r Z.r_mem (Z.exists_r_mul_mem hp hpN)
    (Z.r_mul_r_inv_mem hp hpN) (UpperHalfPlane.petersson k ⇑F ⇑G) (fun h hh x => by
      rw [petersson_smul_SL, slash_mem F hh, slash_mem G hh]) τ).symm

theorem petersson_heckeT_right (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f (CuspForm.heckeTLin k hp hpN g)
      = CuspForm.petersson
          (FreyPackage.ModMCarrier.rescaleLin (one_mul_dvd (N := N) (p := p)) k f)
          (FreyPackage.ModMCarrier.rescaleLin (p_mul_dvd (N := N) (p := p)) k g) := by
  have h : CuspForm.peterssonIntegrand f (CuspForm.heckeTLin k hp hpN g)
      = CuspForm.peterssonIntegrand
          (FreyPackage.ModMCarrier.rescaleLin (one_mul_dvd (N := N) (p := p)) k f)
          (FreyPackage.ModMCarrier.rescaleLin (p_mul_dvd (N := N) (p := p)) k g) :=
    funext (integrand_heckeT Z hp hpN f g)
  rw [CuspForm.petersson_def, CuspForm.petersson_def, h]

end adjraise

theorem mp_smul_SL (γ : SL(2, ℤ)) : MeasurePreserving (fun x : ℍ => γ • x) volume volume := by
  have hemb : MeasurableEmbedding (fun w : ℍ => γ • w) :=
    (Homeomorph.smul γ (α := ℍ)).measurableEmbedding
  exact ⟨hemb.measurable, by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, Set.preimage_smul,
      FLT.HyperbolicMeasure.volume_smul_sl2z]⟩

theorem mp_smul_GL (g : GL (Fin 2) ℝ) : MeasurePreserving (fun x : ℍ => g • x) volume volume := by
  have hemb : MeasurableEmbedding (fun w : ℍ => g • w) :=
    (Homeomorph.smul g (α := ℍ)).measurableEmbedding
  exact ⟨hemb.measurable, by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, Set.preimage_smul,
      FLT.HyperbolicMeasure.volume_smul_gl]⟩

theorem measurable_smul_SL (γ : SL(2, ℤ)) : Measurable (fun x : ℍ => γ • x) :=
  (continuous_const_smul γ).measurable

theorem measurable_smul_GL (g : GL (Fin 2) ℝ) : Measurable (fun x : ℍ => g • x) :=
  (continuous_const_smul g).measurable

section weight

variable (Λ : Subgroup SL(2, ℤ))

def splitEquiv : SL(2, ℤ) ≃ (SL(2, ℤ) ⧸ Λ) × Λ where
  toFun σ := (QuotientGroup.mk σ, ⟨(QuotientGroup.mk σ : SL(2, ℤ) ⧸ Λ).out⁻¹ * σ, by
    rw [← QuotientGroup.eq]; exact QuotientGroup.out_eq' _⟩)
  invFun x := x.1.out * x.2
  left_inv σ := by simp
  right_inv := by
    rintro ⟨q, h⟩
    have hq : (QuotientGroup.mk (q.out * (h : SL(2, ℤ))) : SL(2, ℤ) ⧸ Λ) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.out_eq']
    refine Prod.ext hq (Subtype.ext ?_)
    simp only [hq]
    rw [inv_mul_cancel_left]

theorem splitEquiv_symm_apply (x : (SL(2, ℤ) ⧸ Λ) × Λ) :
    (splitEquiv Λ).symm x = x.1.out * x.2 := rfl

theorem tsum_SL_eq (F : SL(2, ℤ) → ℝ≥0∞) :
    ∑' σ : SL(2, ℤ), F σ = ∑' q : SL(2, ℤ) ⧸ Λ, ∑' h : Λ, F (q.out * (h : SL(2, ℤ))) := by
  rw [← (splitEquiv Λ).symm.tsum_eq, ENNReal.tsum_prod']
  rfl

theorem tsum_SL_inv (F : SL(2, ℤ) → ℝ≥0∞) : ∑' σ : SL(2, ℤ), F σ = ∑' σ : SL(2, ℤ), F σ⁻¹ :=
  ((Equiv.inv SL(2, ℤ)).tsum_eq F).symm

theorem tsum_Λ_inv (F : Λ → ℝ≥0∞) : ∑' h : Λ, F h = ∑' h : Λ, F h⁻¹ :=
  ((Equiv.inv Λ).tsum_eq F).symm

variable [Fintype (SL(2, ℤ) ⧸ Λ)]

def wt (x : ℍ) : ℝ≥0∞ :=
  ∑ q : SL(2, ℤ) ⧸ Λ, (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) ((q.out : SL(2, ℤ)) • x)

theorem measurable_wt : Measurable (wt Λ) := by
  refine Finset.measurable_sum _ fun q _ => ?_
  exact (measurable_const.indicator ModularGroup.isClosed_fd.measurableSet).comp
    (measurable_smul_SL _)

theorem indicator_smul (σ : SL(2, ℤ)) (x : ℍ) :
    (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (σ • x)
      = (σ⁻¹ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  by_cases h : σ • x ∈ (𝒟 : Set ℍ)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_inv_smul_set_iff.mpr h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (Set.mem_inv_smul_set_iff.mp h'))]

theorem tsum_wt_smul {x : ℍ} (hx : x ∈ FLT.ModularFundamentalDomain.goodSet) :
    ∑' h : Λ, wt Λ ((h : SL(2, ℤ)) • x) = 2 := by
  calc ∑' h : Λ, wt Λ ((h : SL(2, ℤ)) • x)
      = ∑' h : Λ, ∑' q : SL(2, ℤ) ⧸ Λ,
          (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) ((q.out : SL(2, ℤ)) • (h : SL(2, ℤ)) • x) :=
        tsum_congr fun h => by rw [wt, tsum_fintype]
    _ = ∑' q : SL(2, ℤ) ⧸ Λ, ∑' h : Λ,
          (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) ((q.out : SL(2, ℤ)) • (h : SL(2, ℤ)) • x) :=
        ENNReal.tsum_comm
    _ = ∑' q : SL(2, ℤ) ⧸ Λ, ∑' h : Λ,
          (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (((q.out : SL(2, ℤ)) * h) • x) :=
        tsum_congr fun q => tsum_congr fun h => by rw [mul_smul]
    _ = ∑' σ : SL(2, ℤ), (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (σ • x) :=
        (tsum_SL_eq Λ (fun σ => (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (σ • x))).symm
    _ = ∑' σ : SL(2, ℤ), (σ⁻¹ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) x :=
        tsum_congr fun σ => indicator_smul σ x
    _ = ∑' σ : SL(2, ℤ), (σ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) x := by
        rw [tsum_SL_inv (fun σ => (σ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) x)]
    _ = 2 := FLT.ModularFundamentalDomain.tsum_indicator_smul_fd hx

theorem ae_tsum_wt_smul : ∀ᵐ x : ℍ, ∑' h : Λ, wt Λ ((h : SL(2, ℤ)) • x) = 2 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp FLT.ModularFundamentalDomain.volume_compl_goodSet]
    with x hx
  exact tsum_wt_smul Λ (by simpa using hx)

theorem tsum_G_eq (U w : ℍ → ℝ≥0∞) (hUinv : ∀ h ∈ Λ, ∀ x : ℍ, U (h • x) = U x) (x : ℍ)
    (hwt : ∀ q : SL(2, ℤ) ⧸ Λ, ∑' h : Λ, w ((h : SL(2, ℤ)) • (q.out⁻¹ : SL(2, ℤ)) • x) = 2) :
    ∑' σ : SL(2, ℤ), U (σ • x) * w (σ • x)
      = 2 * ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) := by
  calc ∑' σ : SL(2, ℤ), U (σ • x) * w (σ • x)
      = ∑' σ : SL(2, ℤ), U (σ⁻¹ • x) * w (σ⁻¹ • x) :=
        tsum_SL_inv (fun σ => U (σ • x) * w (σ • x))
    _ = ∑' q : SL(2, ℤ) ⧸ Λ, ∑' h : Λ,
          U (((q.out : SL(2, ℤ)) * h)⁻¹ • x) * w (((q.out : SL(2, ℤ)) * h)⁻¹ • x) :=
        tsum_SL_eq Λ (fun σ => U (σ⁻¹ • x) * w (σ⁻¹ • x))
    _ = ∑' q : SL(2, ℤ) ⧸ Λ, ∑' h : Λ,
          U ((q.out⁻¹ : SL(2, ℤ)) • x) * w (((h⁻¹ : Λ) : SL(2, ℤ)) • (q.out⁻¹ : SL(2, ℤ)) • x) := by
        refine tsum_congr fun q => tsum_congr fun h => ?_
        have h1 : ((q.out : SL(2, ℤ)) * h)⁻¹ • x = ((h⁻¹ : Λ) : SL(2, ℤ)) • (q.out⁻¹ : SL(2, ℤ)) • x := by
          rw [mul_inv_rev, mul_smul, Subgroup.coe_inv]
        rw [h1, hUinv _ (h⁻¹).2]
    _ = ∑' q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) *
          ∑' h : Λ, w (((h⁻¹ : Λ) : SL(2, ℤ)) • (q.out⁻¹ : SL(2, ℤ)) • x) :=
        tsum_congr fun q => ENNReal.tsum_mul_left
    _ = ∑' q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) * 2 := by
        refine tsum_congr fun q => ?_
        rw [← tsum_Λ_inv Λ (fun h => w ((h : SL(2, ℤ)) • (q.out⁻¹ : SL(2, ℤ)) • x)), hwt q]
    _ = 2 * ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) := by
        rw [ENNReal.tsum_mul_right, tsum_fintype, mul_comm]

theorem weight_lintegral (U w : ℍ → ℝ≥0∞) (hU : Measurable U) (hw : Measurable w)
    (hUinv : ∀ h ∈ Λ, ∀ x : ℍ, U (h • x) = U x)
    (hwt : ∀ᵐ x : ℍ, ∑' h : Λ, w ((h : SL(2, ℤ)) • x) = 2) :
    ∫⁻ x, U x * w x = ∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) := by
  have hm : Measurable fun x => U x * w x := hU.mul hw

  have hae : ∀ᵐ x : ℍ, ∀ q : SL(2, ℤ) ⧸ Λ,
      ∑' h : Λ, w ((h : SL(2, ℤ)) • (q.out⁻¹ : SL(2, ℤ)) • x) = 2 := by
    haveI : Countable (SL(2, ℤ) ⧸ Λ) := inferInstance
    rw [ae_all_iff]
    intro q
    exact (mp_smul_SL (q.out⁻¹ : SL(2, ℤ))).quasiMeasurePreserving.ae
      (p := fun y : ℍ => ∑' h : Λ, w ((h : SL(2, ℤ)) • y) = 2) hwt
  have hA : ∑' γ : SL(2, ℤ), ∫⁻ x in (𝒟 : Set ℍ), U (γ • x) * w (γ • x) = 2 * ∫⁻ z, U z * w z :=
    FLT.ModularFundamentalDomain.tsum_setLIntegral_fd_smul (fun x => U x * w x) hm
  have hB : ∑' γ : SL(2, ℤ), ∫⁻ x in (𝒟 : Set ℍ), U (γ • x) * w (γ • x)
      = ∫⁻ x in (𝒟 : Set ℍ), ∑' γ : SL(2, ℤ), U (γ • x) * w (γ • x) :=
    (lintegral_tsum fun γ =>
      ((hm.comp (measurable_smul_SL γ) : Measurable fun x => U (γ • x) * w (γ • x))).aemeasurable).symm
  have hC : ∫⁻ x in (𝒟 : Set ℍ), ∑' γ : SL(2, ℤ), U (γ • x) * w (γ • x)
      = ∫⁻ x in (𝒟 : Set ℍ), 2 * ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hae] with x hx
    exact tsum_G_eq Λ U w hUinv x hx
  have hmeasS : Measurable fun x : ℍ => ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) :=
    Finset.measurable_sum _ fun q _ =>
      (hU.comp (measurable_smul_SL _) : Measurable fun x => U ((q.out⁻¹ : SL(2, ℤ)) • x))
  have hD : ∫⁻ x in (𝒟 : Set ℍ), 2 * ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x)
      = 2 * ∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) :=
    lintegral_const_mul 2 hmeasS
  have key : (2 : ℝ≥0∞) * ∫⁻ x, U x * w x
      = 2 * ∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) := by
    rw [← hA, hB, hC, hD]
  exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).mp key

theorem cvn_lintegral (κ : GL (Fin 2) ℝ) (c : Λ ≃ Λ)
    (hc : ∀ h : Λ, κ * (Matrix.SpecialLinearGroup.mapGL ℝ (h : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((c h : Λ) : SL(2, ℤ)) : GL (Fin 2) ℝ) * κ)
    (U : ℍ → ℝ≥0∞) (hU : Measurable U) (hUinv : ∀ h ∈ Λ, ∀ x : ℍ, U (h • x) = U x) :
    ∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ Λ, U (κ • (q.out⁻¹ : SL(2, ℤ)) • x)
      = ∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) := by

  have hact : ∀ (γ : SL(2, ℤ)) (x : ℍ),
      γ • x = (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) • x := fun γ x =>
    MulAction.compHom_smul_def _ γ x

  have hUκinv : ∀ h ∈ Λ, ∀ x : ℍ, U (κ • h • x) = U (κ • x) := by
    intro h hh x
    rw [hact, ← mul_smul, hc ⟨h, hh⟩, mul_smul, ← hact, hUinv _ (c ⟨h, hh⟩).2]

  have h1 := weight_lintegral Λ (fun x => U (κ • x)) (wt Λ) (hU.comp (measurable_smul_GL κ))
    (measurable_wt Λ) hUκinv (ae_tsum_wt_smul Λ)

  have h2 : ∫⁻ x, U (κ • x) * wt Λ x = ∫⁻ y, U y * wt Λ (κ⁻¹ • y) := by
    have hmeas : Measurable fun y : ℍ => U y * wt Λ (κ⁻¹ • y) :=
      hU.mul ((measurable_wt Λ).comp (measurable_smul_GL κ⁻¹))
    have := (mp_smul_GL κ).lintegral_comp hmeas
    simpa only [inv_smul_smul] using this

  have hwt' : ∀ᵐ y : ℍ, ∑' h : Λ, wt Λ (κ⁻¹ • (h : SL(2, ℤ)) • y) = 2 := by
    have hT : ∀ᵐ y : ℍ, ∑' h : Λ, wt Λ ((h : SL(2, ℤ)) • κ⁻¹ • y) = 2 :=
      (mp_smul_GL κ⁻¹).quasiMeasurePreserving.ae
        (p := fun z : ℍ => ∑' h : Λ, wt Λ ((h : SL(2, ℤ)) • z) = 2) (ae_tsum_wt_smul Λ)
    filter_upwards [hT] with y hy
    rw [← hy, ← c.tsum_eq (fun h : Λ => wt Λ (κ⁻¹ • (h : SL(2, ℤ)) • y))]
    refine tsum_congr fun h => ?_

    show wt Λ (κ⁻¹ • ((c h : Λ) : SL(2, ℤ)) • y) = wt Λ ((h : SL(2, ℤ)) • κ⁻¹ • y)
    congr 1
    rw [hact, hact, ← mul_smul, ← mul_smul]
    congr 1
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hc h, ← mul_assoc, inv_mul_cancel, one_mul]
  have h3 := weight_lintegral Λ U (fun y => wt Λ (κ⁻¹ • y)) hU
    ((measurable_wt Λ).comp (measurable_smul_GL κ⁻¹)) hUinv hwt'
  rw [← h3, ← h2, h1]

end weight

section glue

variable {L : ℕ} {k : ℤ}

def dens (H : CuspForm (CongruenceSubgroup.Gamma0 L) k) (x : ℍ) : ℝ := ‖H x‖ ^ 2 * x.im ^ k

theorem dens_nonneg (H : CuspForm (CongruenceSubgroup.Gamma0 L) k) (x : ℍ) : 0 ≤ dens H x :=
  mul_nonneg (sq_nonneg _) (zpow_nonneg x.im_pos.le _)

theorem petersson_self_eq_dens (H : CuspForm (CongruenceSubgroup.Gamma0 L) k) (x : ℍ) :
    UpperHalfPlane.petersson k ⇑H ⇑H x = ((dens H x : ℝ) : ℂ) := by
  unfold UpperHalfPlane.petersson dens
  rw [Complex.conj_mul' (H x)]
  push_cast
  ring

theorem continuous_dens (H : CuspForm (CongruenceSubgroup.Gamma0 L) k) : Continuous (dens H) := by
  unfold dens
  refine ((continuous_norm.comp H.holo'.continuous).pow 2).mul ?_
  exact (UpperHalfPlane.continuous_im.zpow₀ k fun x => Or.inl (x.im_pos.ne'))

theorem dens_bounded [NeZero L] (H : CuspForm (CongruenceSubgroup.Gamma0 L) k) :
    ∃ C, ∀ x, dens H x ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k
    (CongruenceSubgroup.Gamma0 L : Subgroup (GL (Fin 2) ℝ)) H H
  refine ⟨C, fun x => ?_⟩
  have := hC x
  rw [petersson_self_eq_dens, Complex.norm_real, Real.norm_of_nonneg (dens_nonneg H x)] at this
  exact this

theorem dens_smul_of_mem (H : CuspForm (CongruenceSubgroup.Gamma0 L) k) {h : SL(2, ℤ)}
    (hh : h ∈ CongruenceSubgroup.Gamma0 L) (x : ℍ) : dens H (h • x) = dens H x := by
  have := UpperHalfPlane.petersson_slash_SL k ⇑H ⇑H h x
  rw [show (⇑H ∣[k] h) = ⇑H from SlashInvariantFormClass.slash_action_eq H _
      (Subgroup.mem_map_of_mem _ hh), petersson_self_eq_dens, petersson_self_eq_dens] at this
  exact_mod_cast this.symm

variable [NeZero L]

def cosum (g : GL (Fin 2) ℝ) (Φ : ℍ → ℂ) (x : ℍ) : ℂ :=
  ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 L, Φ (g • (q.out⁻¹ : SL(2, ℤ)) • x)

theorem cosum_add (g : GL (Fin 2) ℝ) (Φ Ψ : ℍ → ℂ) :
    cosum (L := L) g (Φ + Ψ) = cosum (L := L) g Φ + cosum (L := L) g Ψ := by
  funext x; simp [cosum, Finset.sum_add_distrib]

theorem cosum_smul (g : GL (Fin 2) ℝ) (c : ℂ) (Φ : ℍ → ℂ) :
    cosum (L := L) g (c • Φ) = c • cosum (L := L) g Φ := by
  funext x; simp [cosum, Finset.mul_sum]

theorem integral_cosum_self (κ : GL (Fin 2) ℝ)
    (c : CongruenceSubgroup.Gamma0 L ≃ CongruenceSubgroup.Gamma0 L)
    (hc : ∀ h : CongruenceSubgroup.Gamma0 L,
      κ * (Matrix.SpecialLinearGroup.mapGL ℝ (h : SL(2, ℤ)) : GL (Fin 2) ℝ)
        = (Matrix.SpecialLinearGroup.mapGL ℝ ((c h : CongruenceSubgroup.Gamma0 L) : SL(2, ℤ)) :
            GL (Fin 2) ℝ) * κ)
    (H : CuspForm (CongruenceSubgroup.Gamma0 L) k) :
    ∫ x in (𝒟 : Set ℍ), cosum (L := L) κ (UpperHalfPlane.petersson k ⇑H ⇑H) x
      = ∫ x in (𝒟 : Set ℍ), cosum (L := L) 1 (UpperHalfPlane.petersson k ⇑H ⇑H) x := by

  have hre : ∀ g : GL (Fin 2) ℝ, (cosum (L := L) g (UpperHalfPlane.petersson k ⇑H ⇑H))
      = fun x => ((∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 L,
          dens H (g • (q.out⁻¹ : SL(2, ℤ)) • x) : ℝ) : ℂ) := by
    intro g; funext x
    simp only [cosum, petersson_self_eq_dens, Complex.ofReal_sum]

  have hmeas : ∀ g : GL (Fin 2) ℝ, Measurable fun x : ℍ =>
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 L, dens H (g • (q.out⁻¹ : SL(2, ℤ)) • x) := by
    intro g
    refine Finset.measurable_sum _ fun q _ => ?_
    exact (continuous_dens H).measurable.comp ((measurable_smul_GL g).comp (measurable_smul_SL _))
  have hnn : ∀ (g : GL (Fin 2) ℝ) (x : ℍ),
      0 ≤ ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 L, dens H (g • (q.out⁻¹ : SL(2, ℤ)) • x) :=
    fun g x => Finset.sum_nonneg fun q _ => dens_nonneg H _

  have hred : ∀ g : GL (Fin 2) ℝ,
      ∫ x in (𝒟 : Set ℍ), cosum (L := L) g (UpperHalfPlane.petersson k ⇑H ⇑H) x
        = ((∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 L,
            ENNReal.ofReal (dens H (g • (q.out⁻¹ : SL(2, ℤ)) • x))).toReal : ℂ) := by
    intro g
    rw [hre g, integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (hnn g)) (hmeas g).aestronglyMeasurable]
    congr 2
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun q _ => dens_nonneg H _]
  rw [hred κ, hred 1]
  congr 2
  have hU : Measurable fun x => ENNReal.ofReal (dens H x) :=
    ENNReal.measurable_ofReal.comp (continuous_dens H).measurable
  have := cvn_lintegral (CongruenceSubgroup.Gamma0 L) κ c hc (fun x => ENNReal.ofReal (dens H x)) hU
    (fun h hh x => by simp only [dens_smul_of_mem H hh])
  simpa only [one_smul] using this

theorem petersson_polarization (F G : ℍ → ℂ) (x : ℍ) :
    UpperHalfPlane.petersson k F G x
      = (4 : ℂ)⁻¹ * (UpperHalfPlane.petersson k (G + F) (G + F) x
          + Complex.I * UpperHalfPlane.petersson k (G + Complex.I • F) (G + Complex.I • F) x
          - UpperHalfPlane.petersson k (G - F) (G - F) x
          - Complex.I * UpperHalfPlane.petersson k (G - Complex.I • F) (G - Complex.I • F) x) := by
  simp only [UpperHalfPlane.petersson, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    map_add, map_sub, map_mul, Complex.conj_I]
  linear_combination (-(1 / 2 : ℂ) * ((starRingEnd ℂ) (G x) * F x - (starRingEnd ℂ) (F x) * G x)
    * ((x.im : ℂ)) ^ k) * Complex.I_sq

theorem integral_cosum_pair (κ : GL (Fin 2) ℝ)
    (c : CongruenceSubgroup.Gamma0 L ≃ CongruenceSubgroup.Gamma0 L)
    (hc : ∀ h : CongruenceSubgroup.Gamma0 L,
      κ * (Matrix.SpecialLinearGroup.mapGL ℝ (h : SL(2, ℤ)) : GL (Fin 2) ℝ)
        = (Matrix.SpecialLinearGroup.mapGL ℝ ((c h : CongruenceSubgroup.Gamma0 L) : SL(2, ℤ)) :
            GL (Fin 2) ℝ) * κ)
    (F G : CuspForm (CongruenceSubgroup.Gamma0 L) k) :
    ∫ x in (𝒟 : Set ℍ), cosum (L := L) κ (UpperHalfPlane.petersson k ⇑F ⇑G) x
      = ∫ x in (𝒟 : Set ℍ), cosum (L := L) 1 (UpperHalfPlane.petersson k ⇑F ⇑G) x := by

  have hint : ∀ (g : GL (Fin 2) ℝ) (H : CuspForm (CongruenceSubgroup.Gamma0 L) k),
      Integrable (cosum (L := L) g (UpperHalfPlane.petersson k ⇑H ⇑H))
        (volume.restrict (𝒟 : Set ℍ)) := by
    intro g H
    obtain ⟨C, hC⟩ := dens_bounded H
    have hmeas : Measurable (cosum (L := L) g (UpperHalfPlane.petersson k ⇑H ⇑H)) := by
      refine Finset.measurable_sum _ fun q _ => ?_
      exact (UpperHalfPlane.petersson_continuous k H.holo'.continuous H.holo'.continuous).measurable.comp
        ((measurable_smul_GL g).comp (measurable_smul_SL _))
    refine Measure.integrableOn_of_bounded
      (M := ∑ _q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 L, C)
      FLT.FundamentalDomainVolume.volume_fd_lt_top.ne hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [petersson_self_eq_dens, Complex.norm_real, Real.norm_of_nonneg (dens_nonneg H _)]
    exact hC _

  set H0 : CuspForm (CongruenceSubgroup.Gamma0 L) k := G + F
  set H1 : CuspForm (CongruenceSubgroup.Gamma0 L) k := G + Complex.I • F
  set H2 : CuspForm (CongruenceSubgroup.Gamma0 L) k := G - F
  set H3 : CuspForm (CongruenceSubgroup.Gamma0 L) k := G - Complex.I • F
  have hc0 : (⇑H0 : ℍ → ℂ) = ⇑G + ⇑F := CuspForm.coe_add _ _
  have hc1 : (⇑H1 : ℍ → ℂ) = ⇑G + Complex.I • ⇑F := by
    rw [CuspForm.coe_add, CuspForm.IsGLPos.coe_smul]
  have hc2 : (⇑H2 : ℍ → ℂ) = ⇑G - ⇑F := CuspForm.coe_sub _ _
  have hc3 : (⇑H3 : ℍ → ℂ) = ⇑G - Complex.I • ⇑F := by
    rw [CuspForm.coe_sub, CuspForm.IsGLPos.coe_smul]

  have hexp : ∀ g : GL (Fin 2) ℝ, cosum (L := L) g (UpperHalfPlane.petersson k ⇑F ⇑G)
      = fun x => (4 : ℂ)⁻¹ * (cosum (L := L) g (UpperHalfPlane.petersson k ⇑H0 ⇑H0) x
          + Complex.I * cosum (L := L) g (UpperHalfPlane.petersson k ⇑H1 ⇑H1) x
          - cosum (L := L) g (UpperHalfPlane.petersson k ⇑H2 ⇑H2) x
          - Complex.I * cosum (L := L) g (UpperHalfPlane.petersson k ⇑H3 ⇑H3) x) := by
    intro g; funext x
    simp only [cosum, hc0, hc1, hc2, hc3, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by rw [petersson_polarization]
  have hI : ∀ g : GL (Fin 2) ℝ,
      ∫ x in (𝒟 : Set ℍ), cosum (L := L) g (UpperHalfPlane.petersson k ⇑F ⇑G) x
        = (4 : ℂ)⁻¹ * ((∫ x in (𝒟 : Set ℍ), cosum (L := L) g (UpperHalfPlane.petersson k ⇑H0 ⇑H0) x)
          + Complex.I * (∫ x in (𝒟 : Set ℍ), cosum (L := L) g (UpperHalfPlane.petersson k ⇑H1 ⇑H1) x)
          - (∫ x in (𝒟 : Set ℍ), cosum (L := L) g (UpperHalfPlane.petersson k ⇑H2 ⇑H2) x)
          - Complex.I * (∫ x in (𝒟 : Set ℍ), cosum (L := L) g (UpperHalfPlane.petersson k ⇑H3 ⇑H3) x)) := by
    intro g
    have iA := hint g H0
    have iB := (hint g H1).const_mul Complex.I
    have iC := hint g H2
    have iD := (hint g H3).const_mul Complex.I
    have iAB : Integrable (fun x => cosum (L := L) g (UpperHalfPlane.petersson k ⇑H0 ⇑H0) x
        + Complex.I * cosum (L := L) g (UpperHalfPlane.petersson k ⇑H1 ⇑H1) x)
        (volume.restrict (𝒟 : Set ℍ)) := iA.add iB
    have iABC : Integrable (fun x => cosum (L := L) g (UpperHalfPlane.petersson k ⇑H0 ⇑H0) x
        + Complex.I * cosum (L := L) g (UpperHalfPlane.petersson k ⇑H1 ⇑H1) x
        - cosum (L := L) g (UpperHalfPlane.petersson k ⇑H2 ⇑H2) x)
        (volume.restrict (𝒟 : Set ℍ)) := iAB.sub iC
    rw [hexp g, integral_const_mul]
    congr 1
    rw [integral_sub iABC iD, integral_sub iAB iC, integral_add iA iB, integral_const_mul,
      integral_const_mul]
  rw [hI κ, hI 1, integral_cosum_self κ c hc H0, integral_cosum_self κ c hc H1,
    integral_cosum_self κ c hc H2, integral_cosum_self κ c hc H3]

end glue

section conjugation

variable {N p : ℕ} (Z : Bez N p)

namespace Bez

def K : Matrix (Fin 2) (Fin 2) ℤ := !![(p : ℤ) * Z.u, Z.v; N * p, p]

def Kadj : Matrix (Fin 2) (Fin 2) ℤ := !![(p : ℤ), -Z.v; -(N * p), p * Z.u]

theorem K_mul_Kadj : Z.K * Z.Kadj = !![(p : ℤ), 0; 0, p] := by
  rw [K, Kadj, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Fin.isValue, Fin.mk_one, Fin.zero_eta]
  · linear_combination (p : ℤ) * Z.huv
  · ring
  · ring
  · linear_combination (p : ℤ) * Z.huv

theorem Kadj_mul_K : Z.Kadj * Z.K = !![(p : ℤ), 0; 0, p] := by
  rw [K, Kadj, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Fin.isValue, Fin.mk_one, Fin.zero_eta]
  · linear_combination (p : ℤ) * Z.huv
  · ring
  · ring
  · linear_combination (p : ℤ) * Z.huv

theorem scalar_eq (p : ℕ) : (!![(p : ℤ), 0; 0, p] : Matrix (Fin 2) (Fin 2) ℤ) = (p : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem det_K : Z.K.det = p := by
  rw [K, Matrix.det_fin_two_of]; linear_combination (p : ℤ) * Z.huv

theorem det_Kadj : Z.Kadj.det = p := by
  rw [Kadj, Matrix.det_fin_two_of]; linear_combination (p : ℤ) * Z.huv

theorem smul_cancel {p : ℕ} (hp : p ≠ 0) {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (h : (p : ℤ) • A = (p : ℤ) • B) : A = B := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hp0 this

section entries

variable (h : CongruenceSubgroup.Gamma0 (N * p))

def ea : ℤ := ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
def eb : ℤ := ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1
def ec : ℤ := ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
def ed : ℤ := ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1

def et : ℤ := ec h / ((N * p : ℕ) : ℤ)

theorem et_spec : ((N * p : ℕ) : ℤ) * et h = ec h :=
  Int.mul_ediv_cancel' ((mem_Gamma0_iff_dvd _ _).mp h.2)

theorem eta : (((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = !![ea h, eb h; ec h, ed h] :=
  Matrix.eta_fin_two _

theorem det_entries : ea h * ed h - eb h * ec h = 1 := by
  have := Matrix.SpecialLinearGroup.det_coe (h : SL(2, ℤ))
  rw [eta, Matrix.det_fin_two_of] at this
  exact this

end entries

def Xmat (h : CongruenceSubgroup.Gamma0 (N * p)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(p : ℤ) * Z.u * ea h + Z.v * ec h - N * p * Z.u * eb h - N * Z.v * ed h,
      -(Z.u * ea h * Z.v) - Z.v ^ 2 * N * et h + p * Z.u ^ 2 * eb h + Z.u * Z.v * ed h;
    (p : ℤ) * (N * ea h + ec h - N * N * eb h - N * ed h),
      -(N * ea h * Z.v) - ec h * Z.v + N * p * eb h * Z.u + p * ed h * Z.u]

def Ymat (h : CongruenceSubgroup.Gamma0 (N * p)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![((p : ℤ) * ea h - Z.v * ec h) * Z.u + (p * eb h - Z.v * ed h) * N,
      ea h * Z.v - Z.v ^ 2 * N * et h + p * eb h - Z.v * ed h;
    (p : ℤ) * (-(N * ea h * Z.u) + Z.u ^ 2 * ec h - N * N * eb h + N * Z.u * ed h),
      (-(N * ea h) + Z.u * ec h) * Z.v + (-(N * eb h) + Z.u * ed h) * p]

theorem smul_Xmat (h : CongruenceSubgroup.Gamma0 (N * p)) :
    (p : ℤ) • Z.Xmat h = Z.K * ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Z.Kadj := by
  have ht := et_spec h
  push_cast at ht
  rw [eta, K, Kadj, Xmat, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.smul_apply, smul_eq_mul, Fin.isValue, Fin.mk_one, Fin.zero_eta]
  · ring
  · linear_combination (-(Z.v ^ 2) : ℤ) * ht
  · ring
  · ring

theorem smul_Ymat (h : CongruenceSubgroup.Gamma0 (N * p)) :
    (p : ℤ) • Z.Ymat h = Z.Kadj * ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Z.K := by
  have ht := et_spec h
  push_cast at ht
  rw [eta, K, Kadj, Ymat, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.smul_apply, smul_eq_mul, Fin.isValue, Fin.mk_one, Fin.zero_eta]
  · ring
  · linear_combination (-(Z.v ^ 2) : ℤ) * ht
  · ring
  · ring

variable (hp : p.Prime)
include hp

theorem Xmat_mul_K (h : CongruenceSubgroup.Gamma0 (N * p)) :
    Z.Xmat h * Z.K = Z.K * ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  apply smul_cancel hp.ne_zero
  rw [← smul_mul_assoc, smul_Xmat, Matrix.mul_assoc, Matrix.mul_assoc, Kadj_mul_K, scalar_eq,
    mul_smul_comm, Matrix.mul_one, mul_smul_comm]

theorem K_mul_Ymat (h : CongruenceSubgroup.Gamma0 (N * p)) :
    Z.K * Z.Ymat h = ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Z.K := by
  apply smul_cancel hp.ne_zero
  rw [← mul_smul_comm, smul_Ymat, ← Matrix.mul_assoc, ← Matrix.mul_assoc, K_mul_Kadj, scalar_eq,
    smul_mul_assoc, Matrix.one_mul, smul_mul_assoc]

theorem det_Xmat (h : CongruenceSubgroup.Gamma0 (N * p)) : (Z.Xmat h).det = 1 := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 := congrArg Matrix.det (Z.smul_Xmat h)
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, det_K, det_Kadj,
    Matrix.SpecialLinearGroup.det_coe, Fintype.card_fin] at h1
  have : (p : ℤ) ^ 2 * (Z.Xmat h).det = (p : ℤ) ^ 2 * 1 := by rw [h1]; ring
  exact mul_left_cancel₀ (pow_ne_zero 2 hp0) this

theorem det_Ymat (h : CongruenceSubgroup.Gamma0 (N * p)) : (Z.Ymat h).det = 1 := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 := congrArg Matrix.det (Z.smul_Ymat h)
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, det_K, det_Kadj,
    Matrix.SpecialLinearGroup.det_coe, Fintype.card_fin] at h1
  have : (p : ℤ) ^ 2 * (Z.Ymat h).det = (p : ℤ) ^ 2 * 1 := by rw [h1]; ring
  exact mul_left_cancel₀ (pow_ne_zero 2 hp0) this

omit hp in
theorem Xmat_mem (h : CongruenceSubgroup.Gamma0 (N * p)) :
    ((N * p : ℕ) : ℤ) ∣ Z.Xmat h 1 0 := by
  have ht := et_spec h
  push_cast at ht
  refine ⟨ea h - N * eb h - ed h + p * et h, ?_⟩
  simp only [Xmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  push_cast
  linear_combination (-(p : ℤ)) * ht

omit hp in
theorem Ymat_mem (h : CongruenceSubgroup.Gamma0 (N * p)) :
    ((N * p : ℕ) : ℤ) ∣ Z.Ymat h 1 0 := by
  have ht := et_spec h
  push_cast at ht
  refine ⟨-(ea h * Z.u) - N * eb h + Z.u * ed h + Z.u ^ 2 * p * et h, ?_⟩
  simp only [Ymat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  push_cast
  linear_combination (-(p * Z.u ^ 2 : ℤ)) * ht

def cX (h : CongruenceSubgroup.Gamma0 (N * p)) : CongruenceSubgroup.Gamma0 (N * p) :=
  ⟨⟨Z.Xmat h, Z.det_Xmat hp h⟩, (mem_Gamma0_iff_dvd _ _).mpr (Z.Xmat_mem h)⟩

def cY (h : CongruenceSubgroup.Gamma0 (N * p)) : CongruenceSubgroup.Gamma0 (N * p) :=
  ⟨⟨Z.Ymat h, Z.det_Ymat hp h⟩, (mem_Gamma0_iff_dvd _ _).mpr (Z.Ymat_mem h)⟩

theorem cX_coe (h : CongruenceSubgroup.Gamma0 (N * p)) :
    (((Z.cX hp h : CongruenceSubgroup.Gamma0 (N * p)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = Z.Xmat h := rfl

theorem cY_coe (h : CongruenceSubgroup.Gamma0 (N * p)) :
    (((Z.cY hp h : CongruenceSubgroup.Gamma0 (N * p)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = Z.Ymat h := rfl

def conjEquiv : CongruenceSubgroup.Gamma0 (N * p) ≃ CongruenceSubgroup.Gamma0 (N * p) where
  toFun := Z.cX hp
  invFun := Z.cY hp
  left_inv h := by
    apply Subtype.ext; apply Subtype.ext
    rw [cY_coe]

    apply smul_cancel hp.ne_zero
    have h1 : Z.K * Z.Ymat (Z.cX hp h) = Z.K * ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [Z.K_mul_Ymat hp, cX_coe, Z.Xmat_mul_K hp]
    have h2 := congrArg (fun M => Z.Kadj * M) h1
    simp only [← Matrix.mul_assoc, Kadj_mul_K, scalar_eq, smul_mul_assoc, Matrix.one_mul] at h2
    exact h2
  right_inv h := by
    apply Subtype.ext; apply Subtype.ext
    rw [cX_coe]
    apply smul_cancel hp.ne_zero
    have h1 : Z.Xmat (Z.cY hp h) * Z.K = ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Z.K := by
      rw [Z.Xmat_mul_K hp, cY_coe, Z.K_mul_Ymat hp]
    have h2 := congrArg (fun M => M * Z.Kadj) h1
    simp only [Matrix.mul_assoc, K_mul_Kadj, scalar_eq, mul_smul_comm, Matrix.mul_one] at h2
    exact h2

omit hp in

theorem κ_val (hp0 : p ≠ 0) :
    ((κ Z : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = Z.K.map (Int.castRingHom ℝ) := by
  rw [κ_def, Units.val_mul, mapGL_coe_eq, γ₂_coe, val_heckeDiagMatrix hp0, K]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
  all_goals ring

theorem κ_mul (h : CongruenceSubgroup.Gamma0 (N * p)) :
    κ Z * (Matrix.SpecialLinearGroup.mapGL ℝ (h : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((Z.conjEquiv hp h : CongruenceSubgroup.Gamma0 (N * p)) :
          SL(2, ℤ)) : GL (Fin 2) ℝ) * κ Z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, κ_val Z hp.ne_zero, mapGL_coe_eq, mapGL_coe_eq]
  show Z.K.map (Int.castRingHom ℝ) * ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ)
    = (Z.Xmat h).map (algebraMap ℤ ℝ) * Z.K.map (Int.castRingHom ℝ)
  have e : (algebraMap ℤ ℝ : ℤ →+* ℝ) = Int.castRingHom ℝ := rfl
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, Z.Xmat_mul_K hp]

end Bez

end conjugation

section assembly

variable {N p : ℕ} {k : ℤ}

theorem integrand_conj {M : ℕ} [NeZero M] (f g : CuspForm (CongruenceSubgroup.Gamma0 M) k) (τ : ℍ) :
    starRingEnd ℂ (CuspForm.peterssonIntegrand g f τ) = CuspForm.peterssonIntegrand f g τ := by
  unfold CuspForm.peterssonIntegrand
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [UpperHalfPlane.petersson, map_mul, starRingEnd_self_apply, map_zpow₀, Complex.conj_ofReal]
  ring

theorem petersson_conj {M : ℕ} [NeZero M] (f g : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    starRingEnd ℂ (CuspForm.petersson g f) = CuspForm.petersson f g := by
  rw [CuspForm.petersson_def, CuspForm.petersson_def, ← integral_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun τ => integrand_conj f g τ)

theorem petersson_swap [NeZero N] [NeZero (N * p)] (Z : Bez N p) (hp : p.Prime)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson
        (FreyPackage.ModMCarrier.rescaleLin (p_mul_dvd (N := N) (p := p)) k f)
        (FreyPackage.ModMCarrier.rescaleLin (one_mul_dvd (N := N) (p := p)) k g)
      = CuspForm.petersson
        (FreyPackage.ModMCarrier.rescaleLin (one_mul_dvd (N := N) (p := p)) k f)
        (FreyPackage.ModMCarrier.rescaleLin (p_mul_dvd (N := N) (p := p)) k g) := by
  have h1 : heckeDiagMatrix 1 = 1 := by
    apply Units.ext; rw [val_heckeDiagMatrix one_ne_zero, Units.val_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  set Fp := FreyPackage.ModMCarrier.rescaleLin (p_mul_dvd (N := N) (p := p)) k f with hFp'
  set G1 := FreyPackage.ModMCarrier.rescaleLin (one_mul_dvd (N := N) (p := p)) k g with hG1'
  set F1 := FreyPackage.ModMCarrier.rescaleLin (one_mul_dvd (N := N) (p := p)) k f with hF1'
  set Gp := FreyPackage.ModMCarrier.rescaleLin (p_mul_dvd (N := N) (p := p)) k g with hGp'
  have hFp : (⇑Fp : ℍ → ℂ) = ⇑f ∣[k] heckeDiagMatrix p := by
    rw [hFp', FreyPackage.ModMCarrier.coe_rescaleLin_apply]
  have hG1 : (⇑G1 : ℍ → ℂ) = ⇑g := by
    rw [hG1', FreyPackage.ModMCarrier.coe_rescaleLin_apply, h1, SlashAction.slash_one]
  have hF1 : (⇑F1 : ℍ → ℂ) = ⇑f := by
    rw [hF1', FreyPackage.ModMCarrier.coe_rescaleLin_apply, h1, SlashAction.slash_one]
  have hGp : (⇑Gp : ℍ → ℂ) = ⇑g ∣[k] heckeDiagMatrix p := by
    rw [hGp', FreyPackage.ModMCarrier.coe_rescaleLin_apply]
  have hL : CuspForm.peterssonIntegrand Fp G1
      = cosum (L := N * p) (κ Z) (UpperHalfPlane.petersson k ⇑F1 ⇑Gp) := by
    funext x
    unfold CuspForm.peterssonIntegrand cosum
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [UpperHalfPlane.petersson_slash_SL, hFp, hG1, hF1, hGp]
    exact petersson_transport Z hp f g _
  have hR : CuspForm.peterssonIntegrand F1 Gp
      = cosum (L := N * p) 1 (UpperHalfPlane.petersson k ⇑F1 ⇑Gp) := by
    funext x
    unfold CuspForm.peterssonIntegrand cosum
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [UpperHalfPlane.petersson_slash_SL, one_smul]
  rw [CuspForm.petersson_def, CuspForm.petersson_def, hL, hR]
  exact integral_cosum_pair (κ Z) (Z.conjEquiv hp) (Z.κ_mul hp) F1 Gp

theorem main_adjoint (hp : p.Prime) (hpN : ¬ p ∣ N) (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (CuspForm.heckeTLin k hp hpN f) g
      = CuspForm.petersson f (CuspForm.heckeTLin k hp hpN g) := by
  haveI : NeZero N := ⟨Bez.N_ne_zero hpN⟩
  haveI : NeZero (N * p) := ⟨Nat.mul_ne_zero (NeZero.ne N) hp.ne_zero⟩
  obtain ⟨Z⟩ := Bez.nonempty hp hpN
  rw [← petersson_conj (CuspForm.heckeTLin k hp hpN f) g, petersson_heckeT_right Z hp hpN g f,
    petersson_conj, petersson_swap Z hp f g, ← petersson_heckeT_right Z hp hpN f g]

end assembly

end AlliAux1R6
p2m_reactivate "P2MW.S_CuspForm_petersson_heckeTLin.AlliAux1R6"

theorem solution {N : ℕ} {k : ℤ} {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (CuspForm.heckeTLin k hp hpN f) g =
      CuspForm.petersson f (CuspForm.heckeTLin k hp hpN g) :=
  AlliAux1R6.main_adjoint hp hpN f g

end
end S_CuspForm_petersson_heckeTLin
end P2MW
export P2MW.S_CuspForm_petersson_heckeTLin (solution)
