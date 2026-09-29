-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_semilinear_linearPart_transport_of_forall_specialLinearGroup_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/bae84dcc-6ff5-522d-9a46-2b3cfe74724f

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_MvPowerSeries_mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt
import Theorems.Thm_RingHom_eq_of_forall_exists_sub_mem_pow_of_comp_eq
import Theorems.Thm_IsDiscreteValuationRing_exists_ringEquiv_forall_apply_eq_comp_of_forall_exists_sub_mem_maximalIdeal
import Theorems.Thm_DrinfeldCurve_LocalChart_ringEquiv_apply_mk_X_mem_span_of_comp_eq_of_isUnit_det_one_sub
import Theorems.Thm_DrinfeldCurve_LocalChart_exists_linearPart_conj_ringEquiv_of_apply_mk_X_mem_span
import Theorems.Thm_DrinfeldCurve_LocalChart_mem_of_mk_sum_C_mul_X_mem_span_sq
import Theorems.Thm_Matrix_exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_semilinear_linearPart_transport_of_forall_specialLinearGroup_of_dense

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open MvPowerSeries
open scoped MatrixGroups

namespace CoreAux

variable {W : Type} [CommRing W]

theorem mem_spanX_iff (g : MvPowerSeries (Fin 2) W) :
    g ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} ↔ constantCoeff g = 0 := by
  have h := MvPowerSeries.mem_span_X_pow_iff_forall_coeff_eq_zero_of_degree_lt W 1 g
  rw [pow_one] at h
  rw [h]
  constructor
  · intro H
    have := H 0 (by simp)
    simpa [coeff_zero_eq_constantCoeff_apply] using this
  · intro H n hn
    have hn0 : n = 0 := by
      ext i; fin_cases i <;> simp <;> omega
    subst hn0
    simpa [coeff_zero_eq_constantCoeff_apply] using H

theorem constantCoeff_eq_zero_of_sub_drinfeldForm_mem (q : ℕ) [Fact q.Prime] (f : MvPowerSeries (Fin 2) W)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}) ^ (q + 2)) :
    constantCoeff f = 0 := by
  have h1 : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} :=
    Ideal.pow_le_self (by omega) hf
  rw [mem_spanX_iff, map_sub] at h1
  have : constantCoeff (DrinfeldCurve.LocalChart.drinfeldForm q W) = 0 := by
    simp [DrinfeldCurve.LocalChart.drinfeldForm, map_sub, map_mul, map_pow, constantCoeff_X,
      (Fact.out : q.Prime).ne_zero]
  rw [this, sub_zero] at h1
  exact h1

theorem mk_C_mem_maximalIdeal [IsLocalRing W] (t : W) (ht : t ∈ IsLocalRing.maximalIdeal W)
    (f u v : MvPowerSeries (Fin 2) W) (hf0 : constantCoeff f = 0)
    [IsLocalRing (MvPowerSeries (Fin 2) W ⧸ Ideal.span {C t * v - f * u})]
    (w : W) (hw : w ∈ IsLocalRing.maximalIdeal W) :
    Ideal.Quotient.mk (Ideal.span {C t * v - f * u}) (C w) ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) W ⧸ Ideal.span {C t * v - f * u}) := by
  classical
  set K : Ideal W := Ideal.span {t * constantCoeff v} with hK
  let π₀ : MvPowerSeries (Fin 2) W →+* W ⧸ K := (Ideal.Quotient.mk K).comp constantCoeff
  have hπ₀I : ∀ g ∈ Ideal.span {C t * v - f * u}, π₀ g = 0 := by
    intro g hg
    rw [Ideal.mem_span_singleton] at hg
    obtain ⟨g', rfl⟩ := hg
    show Ideal.Quotient.mk K (constantCoeff ((C t * v - f * u) * g')) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, map_mul, map_mul, constantCoeff_C, hf0, zero_mul,
      sub_zero]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  let π : (MvPowerSeries (Fin 2) W ⧸ Ideal.span {C t * v - f * u}) →+* W ⧸ K :=
    Ideal.Quotient.lift _ π₀ hπ₀I
  have hπC : π (Ideal.Quotient.mk _ (C w)) = Ideal.Quotient.mk K w := by
    show Ideal.Quotient.mk K (constantCoeff (C w)) = _; rw [constantCoeff_C]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' : IsUnit (Ideal.Quotient.mk K w) := by rw [← hπC]; exact hu.map π

  obtain ⟨w', hw'⟩ := hu'.exists_right_inv
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w'
  rw [← map_mul, ← map_one (Ideal.Quotient.mk K), Ideal.Quotient.eq, hK, Ideal.mem_span_singleton] at hw'
  obtain ⟨c, hc⟩ := hw'
  have h1 : (1 : W) = w * z - t * constantCoeff v * c := by rw [← hc]; ring
  have hmem : (1 : W) ∈ IsLocalRing.maximalIdeal W := by
    rw [h1]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hw) (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ht))
  exact (IsLocalRing.maximalIdeal.isMaximal W).ne_top ((Ideal.eq_top_iff_one _).mpr hmem)

theorem mem_maximalIdeal_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) : e x ∈ IsLocalRing.maximalIdeal S := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu; exact hx (by simpa using hu.map e.symm)

end CoreAux

namespace CoreAux

theorem isUnit_det_one_sub {W : Type} [CommRing W] [IsLocalRing W] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (hqW : (q : W) ∈ IsLocalRing.maximalIdeal W)
    (M : Matrix (Fin 2) (Fin 2) W) (G : Matrix (Fin 2) (Fin 2) ℤ)
    (hMG : ∀ ii jj : Fin 2, M ii jj - ((G ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W)
    (hG : ∀ ii jj : Fin 2, ((G ii jj : ℤ) : ZMod q) = (-1 : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj) :
    IsUnit (1 - M).det := by
  classical
  have hp : q.Prime := Fact.out
  set r := IsLocalRing.residue W with hr
  have hrq : r (q : W) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hqW
  haveI : CharP (IsLocalRing.ResidueField W) q := by
    have h0 : ((q : ℕ) : IsLocalRing.ResidueField W) = 0 := by rw [← map_natCast r]; exact hrq
    exact ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp h0)
  have h2 : (2 : IsLocalRing.ResidueField W) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : IsLocalRing.ResidueField W) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (IsLocalRing.ResidueField W) q] at this
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)

  have hentry : ∀ ii jj : Fin 2, r ((1 - M) ii jj) = (2 : IsLocalRing.ResidueField W) * (1 : Matrix (Fin 2) (Fin 2) (IsLocalRing.ResidueField W)) ii jj := by
    intro ii jj
    have hGij := hG ii jj

    have hdiv : (q : ℤ) ∣ G ii jj + (if ii = jj then 1 else 0) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hGij, Matrix.neg_apply, Matrix.one_apply]
      split_ifs <;> simp
    obtain ⟨m, hm⟩ := hdiv
    have hGW : ((G ii jj : ℤ) : W) + (if ii = jj then 1 else 0) ∈ IsLocalRing.maximalIdeal W := by
      have : ((G ii jj : ℤ) : W) + (if ii = jj then 1 else 0) = ((G ii jj + (if ii = jj then 1 else 0) : ℤ) : W) := by
        push_cast; split_ifs <;> simp
      rw [this, hm]; push_cast
      exact Ideal.mul_mem_right _ _ hqW
    have hsum : (1 - M) ii jj - 2 * (1 : Matrix (Fin 2) (Fin 2) W) ii jj =
        -(M ii jj - ((G ii jj : ℤ) : W)) - (((G ii jj : ℤ) : W) + (if ii = jj then 1 else 0)) := by
      rw [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> ring
    have hmem : (1 - M) ii jj - 2 * (1 : Matrix (Fin 2) (Fin 2) W) ii jj ∈ IsLocalRing.maximalIdeal W := by
      rw [hsum]; exact Ideal.sub_mem _ ((IsLocalRing.maximalIdeal W).neg_mem (hMG ii jj)) hGW
    have := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hmem
    change r ((1 - M) ii jj) = r (2 * (1 : Matrix (Fin 2) (Fin 2) W) ii jj) at this
    rw [this, map_mul, map_ofNat, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hmap : r.mapMatrix (1 - M) = (2 : IsLocalRing.ResidueField W) • (1 : Matrix (Fin 2) (Fin 2) (IsLocalRing.ResidueField W)) := by
    ext ii jj
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hentry, Matrix.smul_apply, smul_eq_mul]
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hmap, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_fin]
  exact pow_ne_zero _ h2

end CoreAux

open CoreAux

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (hqA : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (t : A) (ht : t ∈ IsLocalRing.maximalIdeal A)

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] (σ₀ : A →+* W₀)
    (hσϖ₀ : IsLocalRing.maximalIdeal W₀ = Ideal.span {σ₀ ϖ})
    (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀) (hu₀ : IsUnit u₀) (hv₀ : IsUnit v₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ (q + 2))
    [IsLocalRing (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀})]

    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W] (σ : A →+* W)
    (hσϖ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    [IsLocalRing (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u})]
    [IsHausdorff (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u})) (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u})]

    (β : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀}) ≃+* (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u}))
    (D : Type) [CommRing D] (ψ₀ : D →+* (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀})) (ψ : D →+* (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u}))

    (τ : D →+* D) (σA : A ≃+* A) (x : A) (N : Matrix (Fin 2) (Fin 2) ℕ)
    (θ₀ : (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀}) ≃+* (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀})) (σW₀ : W₀ ≃+* W₀) (ct₀ : W₀) (M₀ : Matrix (Fin 2) (Fin 2) W₀) :
    let S₀ := (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀})
    let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ t) * v - f * u})
    let mk₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ t) * v₀ - f₀ * u₀})
    let mk : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ t) * v - f * u})
    let J₀ : Ideal S₀ := Ideal.span {mk₀ (MvPowerSeries.X 0), mk₀ (MvPowerSeries.X 1)}
    let J : Ideal S := Ideal.span {mk (MvPowerSeries.X 0), mk (MvPowerSeries.X 1)}

    (∀ a : A, β (mk₀ (MvPowerSeries.C (σ₀ a))) = mk (MvPowerSeries.C (σ a))) →

    (∀ w : W₀, ∃ a : A, mk₀ (MvPowerSeries.C (w - σ₀ a)) ∈ IsLocalRing.maximalIdeal S₀) →
    (∀ w : W, ∃ a : A, mk (MvPowerSeries.C (w - σ a)) ∈ IsLocalRing.maximalIdeal S) →

    (∀ d : D, β (ψ₀ d) = ψ d) →
    (∀ (s : S₀) (n : ℕ), ∃ d : D, s - ψ₀ d ∈ (IsLocalRing.maximalIdeal S₀) ^ n) →

    (∀ g : SL(2, ZMod q), ∃ (G : Matrix (Fin 2) (Fin 2) ℤ) (τg : D →+* D)
        (θ₀g : S₀ ≃+* S₀) (θg : S ≃+* S) (M₀g : Matrix (Fin 2) (Fin 2) W₀) (Mg : Matrix (Fin 2) (Fin 2) W),
      (∀ ii jj : Fin 2, ((G ii jj : ℤ) : ZMod q) = ((g : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj) ∧
      (∀ d : D, θ₀g (ψ₀ d) = ψ₀ (τg d)) ∧ (∀ d : D, θg (ψ d) = ψ (τg d)) ∧
      (∀ w : W₀, θ₀g (mk₀ (MvPowerSeries.C w)) = mk₀ (MvPowerSeries.C w)) ∧
      (∀ w : W, θg (mk (MvPowerSeries.C w)) = mk (MvPowerSeries.C w)) ∧
      (∀ jj : Fin 2, θ₀g (mk₀ (MvPowerSeries.X jj)) -
          mk₀ (∑ ii : Fin 2, MvPowerSeries.C (M₀g ii jj) * MvPowerSeries.X ii) ∈ J₀ ^ 2) ∧
      (∀ jj : Fin 2, θg (mk (MvPowerSeries.X jj)) -
          mk (∑ ii : Fin 2, MvPowerSeries.C (Mg ii jj) * MvPowerSeries.X ii) ∈ J ^ 2) ∧
      (∀ ii jj : Fin 2, M₀g ii jj - ((G ii jj : ℤ) : W₀) ∈ IsLocalRing.maximalIdeal W₀) ∧
      (∀ ii jj : Fin 2, Mg ii jj - ((G ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W)) →

    (∀ d : D, θ₀ (ψ₀ d) = ψ₀ (τ d)) →
    (∀ a : A, σW₀ (σ₀ a) = σ₀ (σA a)) →
    (∀ w : W₀, σW₀ w - w ∈ IsLocalRing.maximalIdeal W₀) →
    (∀ w : W₀, θ₀ (mk₀ (MvPowerSeries.C w)) = mk₀ (MvPowerSeries.C (σW₀ w))) →
    (∀ jj : Fin 2, θ₀ (mk₀ (MvPowerSeries.X jj)) -
        mk₀ (∑ ii : Fin 2, MvPowerSeries.C (M₀ ii jj) * MvPowerSeries.X ii) ∈ J₀ ^ 2) →
    (ct₀ - σ₀ x ∈ IsLocalRing.maximalIdeal W₀) →
    (∀ ii jj : Fin 2, M₀ ii jj - ct₀ * ((N ii jj : ℕ) : W₀) ∈ IsLocalRing.maximalIdeal W₀) →

    ∃ (θ : S ≃+* S) (σW : W ≃+* W) (ct : W) (M : Matrix (Fin 2) (Fin 2) W),
      (∀ d : D, θ (ψ d) = ψ (τ d)) ∧
      (∀ a : A, σW (σ a) = σ (σA a)) ∧
      (∀ w : W, σW w - w ∈ IsLocalRing.maximalIdeal W) ∧
      (∀ w : W, θ (mk (MvPowerSeries.C w)) = mk (MvPowerSeries.C (σW w))) ∧
      (∀ jj : Fin 2, θ (mk (MvPowerSeries.X jj)) -
          mk (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈ J ^ 2) ∧
      (ct - σ x ∈ IsLocalRing.maximalIdeal W) ∧
      (∀ ii jj : Fin 2, M ii jj - ct * ((N ii jj : ℕ) : W) ∈ IsLocalRing.maximalIdeal W) := by
  intro S₀ S mk₀ mk J₀ J hβσ hres₀ hres hβψ hdense hfam h₁ h₂ h₃ h₄ h₅ h₆ h₇
  classical
  have hp : q.Prime := Fact.out

  have hσt : σ t ∈ IsLocalRing.maximalIdeal W := by
    rw [hϖ, Ideal.mem_span_singleton] at ht; obtain ⟨a, rfl⟩ := ht
    rw [map_mul, hσϖ]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hσ₀t : σ₀ t ∈ IsLocalRing.maximalIdeal W₀ := by
    rw [hϖ, Ideal.mem_span_singleton] at ht; obtain ⟨a, rfl⟩ := ht
    rw [map_mul, hσϖ₀]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hσ𝔪 : ∀ a ∈ IsLocalRing.maximalIdeal A, σ a ∈ IsLocalRing.maximalIdeal W := by
    intro a ha; rw [hϖ, Ideal.mem_span_singleton] at ha; obtain ⟨b, rfl⟩ := ha
    rw [map_mul, hσϖ]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hσ₀𝔪 : ∀ a ∈ IsLocalRing.maximalIdeal A, σ₀ a ∈ IsLocalRing.maximalIdeal W₀ := by
    intro a ha; rw [hϖ, Ideal.mem_span_singleton] at ha; obtain ⟨b, rfl⟩ := ha
    rw [map_mul, hσϖ₀]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hqW : (q : W) ∈ IsLocalRing.maximalIdeal W := by simpa using hσ𝔪 _ hqA
  have hqW₀ : (q : W₀) ∈ IsLocalRing.maximalIdeal W₀ := by simpa using hσ₀𝔪 _ hqA
  have hf0 : constantCoeff f = 0 := constantCoeff_eq_zero_of_sub_drinfeldForm_mem q f hf
  have hf₀0 : constantCoeff f₀ = 0 := constantCoeff_eq_zero_of_sub_drinfeldForm_mem q f₀ hf₀

  have hβ𝔪 : ∀ s ∈ IsLocalRing.maximalIdeal S₀, β s ∈ IsLocalRing.maximalIdeal S :=
    fun s hs => mem_maximalIdeal_of_ringEquiv β s hs
  have hmkC : ∀ w ∈ IsLocalRing.maximalIdeal W, mk (C w) ∈ IsLocalRing.maximalIdeal S :=
    fun w hw => mk_C_mem_maximalIdeal (σ t) hσt f u v hf0 w hw
  have hmkC₀ : ∀ w ∈ IsLocalRing.maximalIdeal W₀, mk₀ (C w) ∈ IsLocalRing.maximalIdeal S₀ :=
    fun w hw => mk_C_mem_maximalIdeal (σ₀ t) hσ₀t f₀ u₀ v₀ hf₀0 w hw

  have hres₀' : ∀ w : W₀, ∃ a : A, w - σ₀ a ∈ IsLocalRing.maximalIdeal W₀ := by
    intro w; obtain ⟨a, ha⟩ := hres₀ w; refine ⟨a, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
    exact fun hu => ha ((hu.map C).map mk₀)
  have hres' : ∀ w : W, ∃ a : A, w - σ a ∈ IsLocalRing.maximalIdeal W := by
    intro w; obtain ⟨a, ha⟩ := hres w; refine ⟨a, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
    exact fun hu => ha ((hu.map C).map mk)
  obtain ⟨βW, hβW, hβWσ⟩ :=
    IsDiscreteValuationRing.exists_ringEquiv_forall_apply_eq_comp_of_forall_exists_sub_mem_maximalIdeal
      A W₀ W S (IsLocalRing.maximalIdeal S) ϖ hϖ σ₀ hσϖ₀ hres₀' σ hσϖ hres'
      ((β : S₀ →+* S).comp (mk₀.comp C)) (mk.comp C)
      (fun w hw => hβ𝔪 _ (hmkC₀ w hw)) (fun w hw => hmkC w hw) (fun a => hβσ a)

  have hβW' : ∀ w : W₀, β (mk₀ (C w)) = mk (C (βW w)) := fun w => hβW w
  have hβW𝔪 : ∀ w ∈ IsLocalRing.maximalIdeal W₀, βW w ∈ IsLocalRing.maximalIdeal W :=
    fun w hw => mem_maximalIdeal_of_ringEquiv βW w hw
  have hβWsymm : ∀ w : W, β.symm (mk (C w)) = mk₀ (C (βW.symm w)) := by
    intro w; apply β.injective; rw [RingEquiv.apply_symm_apply, hβW', RingEquiv.apply_symm_apply]

  choose G τg θ₀g θg M₀g Mg hG hθ₀ψ hθψ hθ₀W hθW hlin₀g hling hM₀G hMG using hfam
  have hint : ∀ (g : SL(2, ZMod q)) (s : S₀), β (θ₀g g s) = θg g (β s) := by
    intro g
    have key := RingHom.eq_of_forall_exists_sub_mem_pow_of_comp_eq D S₀ S ψ₀ (IsLocalRing.maximalIdeal S₀)
      hdense (IsLocalRing.maximalIdeal S)
      ((θg g : S →+* S).comp (β : S₀ →+* S)) ((β : S₀ →+* S).comp (θ₀g g : S₀ →+* S₀))
      (fun x hx => mem_maximalIdeal_of_ringEquiv (θg g) _ (hβ𝔪 x hx))
      (fun x hx => hβ𝔪 _ (mem_maximalIdeal_of_ringEquiv (θ₀g g) x hx))
      (by ext d; simp only [RingHom.comp_apply, RingHom.coe_coe, hβψ, hθψ, hθ₀ψ])
    intro s
    have := congrArg (fun φ : S₀ →+* S => φ s) key
    simpa using this.symm

  set g₀ : SL(2, ZMod q) := -1 with hg₀
  have hG₀ : ∀ ii jj : Fin 2, ((G g₀ ii jj : ℤ) : ZMod q) = (-1 : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj := by
    intro ii jj; rw [hG g₀ ii jj, hg₀, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  have hdet₀ : IsUnit (1 - M₀g g₀).det := isUnit_det_one_sub q hq2 hqW₀ (M₀g g₀) (G g₀) (hM₀G g₀) hG₀
  have hdet₁ : IsUnit (1 - Mg g₀).det := isUnit_det_one_sub q hq2 hqW (Mg g₀) (G g₀) (hMG g₀) hG₀

  have hXJ : ∀ ii : Fin 2, mk (X ii) ∈ J := by
    intro ii; fin_cases ii
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)
  have hXJ₀ : ∀ ii : Fin 2, mk₀ (X ii) ∈ J₀ := by
    intro ii; fin_cases ii
    · exact Ideal.subset_span (by simp)
    · exact Ideal.subset_span (by simp)
  have hsumJ : ∀ (N : Matrix (Fin 2) (Fin 2) W) (jj : Fin 2), mk (∑ ii : Fin 2, C (N ii jj) * X ii) ∈ J := by
    intro N jj; rw [map_sum]
    exact Ideal.sum_mem _ (fun ii _ => by rw [map_mul]; exact Ideal.mul_mem_left _ _ (hXJ ii))
  have hsumJ₀ : ∀ (N : Matrix (Fin 2) (Fin 2) W₀) (jj : Fin 2), mk₀ (∑ ii : Fin 2, C (N ii jj) * X ii) ∈ J₀ := by
    intro N jj; rw [map_sum]
    exact Ideal.sum_mem _ (fun ii _ => by rw [map_mul]; exact Ideal.mul_mem_left _ _ (hXJ₀ ii))
  have hθJ₁ : ∀ jj : Fin 2, θg g₀ (mk (X jj)) ∈ J := by
    intro jj
    have h1 := Ideal.pow_le_self (two_ne_zero) (hling g₀ jj)
    have : θg g₀ (mk (X jj)) = (θg g₀ (mk (X jj)) - mk (∑ ii : Fin 2, C (Mg g₀ ii jj) * X ii)) +
        mk (∑ ii : Fin 2, C (Mg g₀ ii jj) * X ii) := by ring
    rw [this]; exact Ideal.add_mem _ h1 (hsumJ _ jj)
  have hθJ₀ : ∀ jj : Fin 2, θ₀g g₀ (mk₀ (X jj)) ∈ J₀ := by
    intro jj
    have h1 := Ideal.pow_le_self (two_ne_zero) (hlin₀g g₀ jj)
    have : θ₀g g₀ (mk₀ (X jj)) = (θ₀g g₀ (mk₀ (X jj)) - mk₀ (∑ ii : Fin 2, C (M₀g g₀ ii jj) * X ii)) +
        mk₀ (∑ ii : Fin 2, C (M₀g g₀ ii jj) * X ii) := by ring
    rw [this]; exact Ideal.add_mem _ h1 (hsumJ₀ _ jj)
  have hint' : ∀ s : S, β.symm (θg g₀ s) = θ₀g g₀ (β.symm s) := by
    intro s; apply β.injective
    rw [RingEquiv.apply_symm_apply, hint g₀, RingEquiv.apply_symm_apply]
  have hβJ : ∀ jj : Fin 2, β (mk₀ (X jj)) ∈ J :=
    DrinfeldCurve.LocalChart.ringEquiv_apply_mk_X_mem_span_of_comp_eq_of_isUnit_det_one_sub q
      W₀ (σ₀ t) f₀ u₀ v₀ hf₀ W (σ t) hσt f u v hf β βW hβW' (θ₀g g₀) (θg g₀) (hint g₀) (hθW g₀) hθJ₁
      (M₀g g₀) (hlin₀g g₀) hdet₀
  have hβJ' : ∀ jj : Fin 2, β.symm (mk (X jj)) ∈ J₀ :=
    DrinfeldCurve.LocalChart.ringEquiv_apply_mk_X_mem_span_of_comp_eq_of_isUnit_det_one_sub q
      W (σ t) f u v hf W₀ (σ₀ t) hσ₀t f₀ u₀ v₀ hf₀ β.symm βW.symm hβWsymm (θg g₀) (θ₀g g₀) hint' (hθ₀W g₀) hθJ₀
      (Mg g₀) (hling g₀) hdet₁

  set κ := IsLocalRing.ResidueField W with hκ
  set r : W →+* κ := IsLocalRing.residue W with hr
  have hrr : ∀ a b : W, r a = r b ↔ a - b ∈ IsLocalRing.maximalIdeal W := by
    intro a b; rw [← sub_eq_zero, ← map_sub, hr, IsLocalRing.residue_eq_zero_iff]
  have hR : ∀ P Q : Matrix (Fin 2) (Fin 2) W, (∀ ii jj : Fin 2, P ii jj - Q ii jj ∈ IsLocalRing.maximalIdeal W) →
      r.mapMatrix P = r.mapMatrix Q := by
    intro P Q h; ext ii jj
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply]
    exact (hrr _ _).mpr (h ii jj)
  have hR' : ∀ P Q : Matrix (Fin 2) (Fin 2) W, r.mapMatrix P = r.mapMatrix Q →
      ∀ ii jj : Fin 2, P ii jj - Q ii jj ∈ IsLocalRing.maximalIdeal W := by
    intro P Q h ii jj
    have := congrArg (fun X : Matrix (Fin 2) (Fin 2) κ => X ii jj) h
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at this
    exact (hrr _ _).mp this

  have hLPU : ∀ (θx : S) (P Q : Matrix (Fin 2) (Fin 2) W) (jj : Fin 2),
      θx - mk (∑ ii : Fin 2, C (P ii jj) * X ii) ∈ J ^ 2 →
      θx - mk (∑ ii : Fin 2, C (Q ii jj) * X ii) ∈ J ^ 2 →
      ∀ ii : Fin 2, P ii jj - Q ii jj ∈ IsLocalRing.maximalIdeal W := by
    intro θx P Q jj hP hQ
    have hdiff : mk (∑ ii : Fin 2, C (P ii jj - Q ii jj) * X ii) ∈ J ^ 2 := by
      have : mk (∑ ii : Fin 2, C (P ii jj - Q ii jj) * X ii) =
          (θx - mk (∑ ii : Fin 2, C (Q ii jj) * X ii)) - (θx - mk (∑ ii : Fin 2, C (P ii jj) * X ii)) := by
        simp only [map_sum, map_mul, map_sub, sub_mul, Finset.sum_sub_distrib]; ring
      rw [this]; exact Ideal.sub_mem _ hQ hP
    exact DrinfeldCurve.LocalChart.mem_of_mk_sum_C_mul_X_mem_span_sq q W (IsLocalRing.maximalIdeal W) (σ t) hσt
      f u v hf (fun ii => P ii jj - Q ii jj) hdiff

  have hT3 : ∀ g : SL(2, ZMod q), ∃ (Bg : Matrix (Fin 2) (Fin 2) W) (B'g : Matrix (Fin 2) (Fin 2) W₀),
      (∀ jj : Fin 2, β (mk₀ (X jj)) - mk (∑ ii : Fin 2, C (Bg ii jj) * X ii) ∈ J ^ 2) ∧
      r.mapMatrix (Bg * B'g.map βW) = 1 ∧
      r.mapMatrix (Mg g) = r.mapMatrix Bg * r.mapMatrix ((M₀g g).map βW) * r.mapMatrix (B'g.map βW) := by
    intro g
    obtain ⟨Bg, B'g, M', hBg, hBB', -, hlinM', hconj⟩ :=
      DrinfeldCurve.LocalChart.exists_linearPart_conj_ringEquiv_of_apply_mk_X_mem_span q
        W₀ (σ₀ t) hσ₀t f₀ u₀ v₀ hf₀ W (σ t) hσt f u v hf β βW hβW' hβJ hβJ' (θ₀g g) (RingEquiv.refl W₀)
        (fun w => by simp) (fun w => by simpa using hθ₀W g w) (M₀g g) (hlin₀g g)
    refine ⟨Bg, B'g, hBg, ?_, ?_⟩
    · rw [← map_one r.mapMatrix]; exact hR _ _ hBB'
    ·
      have hθ' : ∀ jj : Fin 2, (β.symm.trans ((θ₀g g).trans β)) (mk (X jj)) = θg g (mk (X jj)) := by
        intro jj
        rw [RingEquiv.trans_apply, RingEquiv.trans_apply, hint g, RingEquiv.apply_symm_apply]
      have hMM' : ∀ ii jj : Fin 2, Mg g ii jj - M' ii jj ∈ IsLocalRing.maximalIdeal W := by
        intro ii jj
        refine hLPU (θg g (mk (X jj))) (Mg g) M' jj (hling g jj) ?_ ii
        have := hlinM' jj
        rwa [hθ'] at this
      rw [← map_mul, ← map_mul]
      apply hR
      intro ii jj
      have : Mg g ii jj - (Bg * (M₀g g).map βW * B'g.map βW) ii jj =
          (Mg g ii jj - M' ii jj) + (M' ii jj - (Bg * (M₀g g).map βW * B'g.map βW) ii jj) := by ring
      rw [this]; exact Ideal.add_mem _ (hMM' ii jj) (hconj ii jj)
  choose Bfam B'fam hBfam hBB'fam hconjfam using hT3

  set Gbar : SL(2, ZMod q) → Matrix (Fin 2) (Fin 2) κ := fun g => r.mapMatrix ((G g).map (Int.cast : ℤ → W)) with hGbar
  have hRMg : ∀ g, r.mapMatrix (Mg g) = Gbar g := by
    intro g; rw [hGbar]; exact hR _ _ (fun ii jj => by simpa [Matrix.map_apply] using hMG g ii jj)
  have hRM₀g : ∀ g, r.mapMatrix ((M₀g g).map βW) = Gbar g := by
    intro g; rw [hGbar]
    exact hR _ _ (fun ii jj => by
      simp only [Matrix.map_apply]
      have := hβW𝔪 _ (hM₀G g ii jj)
      rwa [map_sub, map_intCast] at this)

  set P : Matrix (Fin 2) (Fin 2) κ := r.mapMatrix (Bfam g₀) with hP
  have hPg : ∀ g, r.mapMatrix (Bfam g) = P := by
    intro g; rw [hP]
    exact hR _ _ (fun ii jj => hLPU (β (mk₀ (X jj))) (Bfam g) (Bfam g₀) jj (hBfam g jj) (hBfam g₀ jj) ii)
  have hPQ : ∀ g, P * r.mapMatrix ((B'fam g).map βW) = 1 := by
    intro g; rw [← hPg g, ← map_mul]; exact hBB'fam g
  have hQP : ∀ g, r.mapMatrix ((B'fam g).map βW) * P = 1 := fun g => mul_eq_one_comm.mp (hPQ g)
  have hcomm : ∀ g, P * Gbar g = Gbar g * P := by
    intro g
    have h1 : Gbar g = P * Gbar g * r.mapMatrix ((B'fam g).map βW) := by
      calc Gbar g = r.mapMatrix (Mg g) := (hRMg g).symm
        _ = r.mapMatrix (Bfam g) * r.mapMatrix ((M₀g g).map βW) * r.mapMatrix ((B'fam g).map βW) := hconjfam g
        _ = P * Gbar g * r.mapMatrix ((B'fam g).map βW) := by rw [hPg g, hRM₀g g]
    calc P * Gbar g = P * Gbar g * (r.mapMatrix ((B'fam g).map βW) * P) := by rw [hQP g, mul_one]
      _ = (P * Gbar g * r.mapMatrix ((B'fam g).map βW)) * P := by simp only [mul_assoc]
      _ = Gbar g * P := by rw [← h1]

  haveI : CharP κ q := by
    have h0 : ((q : ℕ) : κ) = 0 := by
      rw [← map_natCast r, hr, IsLocalRing.residue_eq_zero_iff]; exact hqW
    exact ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp h0)
  let φ : ZMod q →+* κ := ZMod.castHom (dvd_refl q) κ
  have hφG : ∀ g : SL(2, ZMod q), ((g : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)).map φ = Gbar g := by
    intro g; ext ii jj
    rw [Matrix.map_apply, ← hG g ii jj, map_intCast, hGbar]
    simp [Matrix.map_apply]
  have hPdet : P.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (hPQ g₀)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  obtain ⟨a, ha⟩ := Matrix.exists_eq_smul_one_of_forall_specialLinearGroup_mul_eq_smul_mul q κ φ P hPdet
    (fun γ => ⟨1, by rw [one_smul, hφG, hcomm]⟩)
  have ha0 : a ≠ 0 := by
    intro h; apply hPdet; rw [ha, h, zero_smul, Matrix.det_zero]

  obtain ⟨BI, B'I, M, hBI, hBB'I, hsemi, hlinM, hconjM⟩ :=
    DrinfeldCurve.LocalChart.exists_linearPart_conj_ringEquiv_of_apply_mk_X_mem_span q
      W₀ (σ₀ t) hσ₀t f₀ u₀ v₀ hf₀ W (σ t) hσt f u v hf β βW hβW' hβJ hβJ' θ₀ σW₀ h₃ h₄ M₀ h₅
  have hPI : r.mapMatrix BI = P := by
    rw [hP]; exact hR _ _ (fun ii jj => hLPU (β (mk₀ (X jj))) BI (Bfam g₀) jj (hBI jj) (hBfam g₀ jj) ii)
  have hQI : r.mapMatrix (B'I.map βW) = a⁻¹ • (1 : Matrix (Fin 2) (Fin 2) κ) := by
    have h1 : P * r.mapMatrix (B'I.map βW) = 1 := by
      rw [← hPI, ← map_mul, ← map_one r.mapMatrix]; exact hR _ _ hBB'I
    rw [ha, smul_mul_assoc, one_mul] at h1
    have := congrArg (fun X : Matrix (Fin 2) (Fin 2) κ => a⁻¹ • X) h1
    simp only [smul_smul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this

  set Nbar : Matrix (Fin 2) (Fin 2) κ := N.map (Nat.cast : ℕ → κ) with hNbar
  have hRM₀ : r.mapMatrix (M₀.map βW) = r (βW ct₀) • Nbar := by
    ext ii jj
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply, Matrix.smul_apply, hNbar, Matrix.map_apply,
      smul_eq_mul, ← map_natCast r, ← map_mul]
    apply (hrr _ _).mpr
    have := hβW𝔪 _ (h₇ ii jj)
    rwa [map_sub, map_mul, map_natCast] at this
  have hRM : r.mapMatrix M = r (βW ct₀) • Nbar := by
    have h1 : r.mapMatrix M = r.mapMatrix (BI * M₀.map βW * B'I.map βW) := hR _ _ hconjM
    rw [h1, map_mul, map_mul, hPI, hQI, hRM₀, ha]
    ext ii jj
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, Matrix.smul_apply]
    rw [mul_comm (r (βW ct₀)) a, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
  refine ⟨β.symm.trans (θ₀.trans β), βW.symm.trans (σW₀.trans βW), βW ct₀, M, ?_, ?_, ?_, hsemi, hlinM, ?_, ?_⟩
  · intro dd
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, ← hβψ dd, RingEquiv.symm_apply_apply, h₁, hβψ]
  · intro a'
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply]
    have : βW.symm (σ a') = σ₀ a' := by rw [← hβWσ a', RingEquiv.symm_apply_apply]
    rw [this, h₂, hβWσ]
  · intro w
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply]
    have := hβW𝔪 _ (h₃ (βW.symm w))
    rwa [map_sub, RingEquiv.apply_symm_apply] at this
  · have := hβW𝔪 _ h₆
    rwa [map_sub, hβWσ] at this
  · intro ii jj
    apply (hrr _ _).mp
    have := congrArg (fun X : Matrix (Fin 2) (Fin 2) κ => X ii jj) hRM
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, hNbar, smul_eq_mul] at this
    rw [this, map_mul, map_natCast]

end S_DrinfeldCurve_LocalChart_exists_semilinear_linearPart_transport_of_forall_specialLinearGroup_of_dense
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_semilinear_linearPart_transport_of_forall_specialLinearGroup_of_dense (solution)
