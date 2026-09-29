-- Prove2me | solution 1 for CerednikDrinfeld.Omega.natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/29cf8850-1821-5b93-be06-aff85ee8671e

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_OmegaTubes
import Theorems.Thm_CerednikDrinfeld_Omega_exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube
import Theorems.Thm_CerednikDrinfeld_Omega_sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow
import Theorems.Thm_CerednikDrinfeld_Omega_v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star
import Theorems.Thm_CerednikDrinfeld_Omega_pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq
import Theorems.Thm_CerednikDrinfeld_BruhatTits_adj_stdVertex_iff_eq_smul_of_uniformizer
import Theorems.Thm_CerednikDrinfeld_Omega_natCard_dvd_of_isUnit_of_forall_apply_smul_eq_of_v_apply_eq_mul_zpow
import Theorems.Thm_CerednikDrinfeld_Omega_affinoid_nonempty_of_exists_finset_cover
import Theorems.Thm_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford CerednikDrinfeld.BruhatTits LT.LatticeTree MulAction

noncomputable section

namespace HarmV0

section Frame

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀]
variable {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem algebraMap_R_ne_zero {x : R} (hx : x ≠ 0) : algebraMap R K₀ x ≠ 0 :=
  fun h => hx (IsFractionRing.injective R K₀ (by rw [h, map_zero]))

theorem algebraMap_ne_zero_of_ne_zero {x : R} (hx : x ≠ 0) : algebraMap K₀ K (algebraMap R K₀ x) ≠ 0 := by
  rw [map_ne_zero_iff _ (algebraMap K₀ K).injective]
  exact algebraMap_R_ne_zero hx

theorem p_pos {ϖ : R} (hϖ : Irreducible ϖ) : 0 < Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) :=
  (Valuation.pos_iff _).2 (algebraMap_ne_zero_of_ne_zero hϖ.ne_zero)

theorem eq_of_mul_eq_one_of_le_one {a b : Γ₀} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  by_contra hlt
  push Not at hlt
  have : a * b < 1 := by
    calc a * b ≤ a * 1 := mul_le_mul_right hb a
      _ < 1 := by rw [mul_one]; exact hlt
  exact this.ne h

theorem v_unit_eq_one (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (u : Rˣ) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) = 1 := by
  have h := hint (u : R)
  have h' := hint ((u⁻¹ : Rˣ) : R)
  have hprod : Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) *
      Valued.v (algebraMap K₀ K (algebraMap R K₀ ((u⁻¹ : Rˣ) : R))) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one]
  exact eq_of_mul_eq_one_of_le_one h h' hprod

theorem exists_v_eq_zpow {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (a : K₀) (ha : a ≠ 0) :
    ∃ e : ℤ, Valued.v (algebraMap K₀ K a) = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ e := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact ha (by rw [map_zero, zero_div])
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨n', u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  refine ⟨(n : ℤ) - n', ?_⟩
  have hp0 := (p_pos (K₀ := K₀) (K := K) hϖ).ne'
  simp only [map_div₀, map_mul, map_pow, v_unit_eq_one hint, one_mul]
  rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast]

theorem p_lt_one {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (ϖ₁ : PseudoUniformizer K₀ K) : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) < 1 := by
  refine lt_of_le_of_ne (hint ϖ) fun h => ?_
  have hne : ϖ₁.ϖ ≠ 0 := by
    intro h0
    have := ϖ₁.pos
    rw [h0, map_zero, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨e, he⟩ := exists_v_eq_zpow hϖ hint ϖ₁.ϖ hne
  rw [h, one_zpow] at he
  exact absurd ϖ₁.lt_one (by rw [he]; exact lt_irrefl 1)

theorem hunif_of_frame {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (ϖ₁ : PseudoUniformizer K₀ K) (hϖ₁ : ϖ₁.ϖ = algebraMap R K₀ ϖ) (a : K₀) :
    Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ₁.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a) := by
  by_cases ha : a = 0
  · left; rw [ha, map_zero, map_zero]; exact zero_le'
  obtain ⟨e, he⟩ := exists_v_eq_zpow hϖ hint a ha
  have hp0 := p_pos (K₀ := K₀) (K := K) hϖ
  have hp1 := p_lt_one hϖ hint ϖ₁
  rcases le_or_gt 1 e with h1 | h1
  · left
    rw [he, hϖ₁]
    calc Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ e
        ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ (1 : ℤ) := (zpow_right_strictAnti₀ hp0 hp1).antitone h1
      _ = _ := zpow_one _
  · right
    rw [he]
    have he0 : e ≤ 0 := by omega
    rcases he0.lt_or_eq with he0 | he0
    · exact (one_lt_zpow_of_neg₀ hp0 hp1 he0).le
    · rw [he0, zpow_zero]

theorem v_eq_one_of_not_dvd {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) {r : R} (hr : ¬ ϖ ∣ r) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ r)) = 1 := by
  have hr0 : r ≠ 0 := by rintro rfl; exact hr (dvd_zero ϖ)
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
  have hk : k = 0 := by
    by_contra hk
    exact hr (Dvd.dvd.mul_left (dvd_pow_self ϖ hk) _)
  subst hk
  rw [pow_zero, mul_one]
  exact v_unit_eq_one hint u

variable [DecidableEq K₀]

variable (R K₀) in

def repFinset (ϖ : R) [Fintype (R ⧸ Ideal.span {ϖ})] : Finset K₀ :=
  Finset.univ.image fun x : R ⧸ Ideal.span {ϖ} => algebraMap R K₀ (Quotient.out x)

theorem rep_injective (ϖ : R) :
    Function.Injective fun x : R ⧸ Ideal.span {ϖ} => algebraMap R K₀ (Quotient.out x) := by
  intro x y h
  have h' : (Quotient.out x : R) = Quotient.out y := IsFractionRing.injective R K₀ h
  rw [← Ideal.Quotient.mk_out x, ← Ideal.Quotient.mk_out y, h']

theorem sum_repFinset (ϖ : R) [Fintype (R ⧸ Ideal.span {ϖ})] (m : K₀ → ℤ) :
    ∑ t ∈ repFinset R K₀ ϖ, m t = ∑ x : R ⧸ Ideal.span {ϖ}, m (algebraMap R K₀ (Quotient.out x)) := by
  rw [repFinset, Finset.sum_image fun x _ y _ h => rep_injective ϖ h]

theorem repFinset_le_one (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (ϖ : R) [Fintype (R ⧸ Ideal.span {ϖ})] :
    ∀ t ∈ repFinset R K₀ ϖ, Valued.v (algebraMap K₀ K t) ≤ 1 := by
  intro t ht
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
  exact hint _

theorem out_mk_sub_mem (ϖ r : R) : r - Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) r) ∈ Ideal.span {ϖ} := by
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]

theorem dvd_sub_out_mk (ϖ r : R) : ϖ ∣ r - Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) r) :=
  Ideal.mem_span_singleton.1 (out_mk_sub_mem ϖ r)

theorem repFinset_cov {ϖ : R} (hϖ : Irreducible ϖ) [Fintype (R ⧸ Ideal.span {ϖ})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (ϖ₁ : PseudoUniformizer K₀ K) :
    ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 →
      ∃ t ∈ repFinset R K₀ ϖ, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1 := by
  intro a ha
  obtain ⟨r, hr⟩ := hv a ha
  refine ⟨algebraMap R K₀ (Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) r)),
    Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
  obtain ⟨s, hs⟩ := dvd_sub_out_mk ϖ r
  rw [← hr, ← map_sub, ← map_sub, hs, map_mul, map_mul, Valuation.map_mul]
  calc _ ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) * 1 := mul_le_mul_right (hint s) _
    _ < 1 := by rw [mul_one]; exact p_lt_one hϖ hint ϖ₁

theorem repFinset_sep {ϖ : R} (hϖ : Irreducible ϖ) [Fintype (R ⧸ Ideal.span {ϖ})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) :
    ∀ t ∈ repFinset R K₀ ϖ, ∀ t' ∈ repFinset R K₀ ϖ, t ≠ t' →
      1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t') := by
  intro t ht t' ht' hne
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 ht'
  have hxy : x ≠ y := by rintro rfl; exact hne rfl
  have hnd : ¬ ϖ ∣ Quotient.out x - Quotient.out y := by
    intro hd
    apply hxy
    rw [← Ideal.Quotient.mk_out x, ← Ideal.Quotient.mk_out y]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hd)
  rw [← map_sub, ← map_sub, v_eq_one_of_not_dvd hϖ hint hnd]

end Frame

section Matrices

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]

def nMat (π : K₀) (hπ : π ≠ 0) : GL (Fin 2) K₀ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, π] (by
    rw [Matrix.det_fin_two_of]; simpa using hπ)

def sMat (t : K₀) : GL (Fin 2) K₀ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![t, 1; 1, 0] (by rw [Matrix.det_fin_two_of]; simp)

def tMat (t : K₀) : GL (Fin 2) K₀ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, 1] (by rw [Matrix.det_fin_two_of]; simp)

def jMat : GL (Fin 2) K₀ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : K₀), 1; 1, 0] (by rw [Matrix.det_fin_two_of]; simp)

theorem coe_nMat (π : K₀) (hπ : π ≠ 0) : ((nMat π hπ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = !![1, 0; 0, π] := rfl
theorem coe_sMat (t : K₀) : ((sMat t : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = !![t, 1; 1, 0] := rfl

variable (K₀)

theorem zero_not_mem_upperHalfPlane : (0 : K) ∉ upperHalfPlane K₀ K := by
  rw [mem_upperHalfPlane_iff]; push Not; exact ⟨0, map_zero _⟩

theorem ne_zero_of_mem {z : K} (hz : z ∈ upperHalfPlane K₀ K) : z ≠ 0 := by
  rintro rfl; exact zero_not_mem_upperHalfPlane K₀ hz

theorem inv_mem_upperHalfPlane {z : K} (hz : z ∈ upperHalfPlane K₀ K) : z⁻¹ ∈ upperHalfPlane K₀ K := by
  rw [mem_upperHalfPlane_iff] at hz ⊢
  intro a ha
  exact hz a⁻¹ (by rw [map_inv₀, ha, inv_inv])

theorem sub_mem_upperHalfPlane {z : K} (hz : z ∈ upperHalfPlane K₀ K) (t : K₀) :
    z - algebraMap K₀ K t ∈ upperHalfPlane K₀ K := by
  rw [mem_upperHalfPlane_iff] at hz ⊢
  intro a ha
  exact hz (a + t) (by rw [map_add, ha, sub_add_cancel])

theorem add_mem_upperHalfPlane {z : K} (hz : z ∈ upperHalfPlane K₀ K) (t : K₀) :
    z + algebraMap K₀ K t ∈ upperHalfPlane K₀ K := by
  simpa using sub_mem_upperHalfPlane K₀ hz (-t)

theorem pmoebius_nMat (π : K₀) (hπ : π ≠ 0) {z : K} (hz : z ∈ upperHalfPlane K₀ K) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk (nMat π hπ)) z = z * (algebraMap K₀ K π)⁻¹ := by
  have h00 : (nMat π hπ : GL (Fin 2) K₀) 0 0 = 1 := by
    show (!![1, 0; 0, π] : Matrix (Fin 2) (Fin 2) K₀) 0 0 = 1; simp
  have h01 : (nMat π hπ : GL (Fin 2) K₀) 0 1 = 0 := by
    show (!![1, 0; 0, π] : Matrix (Fin 2) (Fin 2) K₀) 0 1 = 0; simp
  have h10 : (nMat π hπ : GL (Fin 2) K₀) 1 0 = 0 := by
    show (!![1, 0; 0, π] : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0; simp
  have h11 : (nMat π hπ : GL (Fin 2) K₀) 1 1 = π := by
    show (!![1, 0; 0, π] : Matrix (Fin 2) (Fin 2) K₀) 1 1 = π; simp
  rw [pmoebius_mk K₀ _ z (moebius_denom_ne_zero_of_mem K₀ hz _), moebius, h10, h11, h00, h01, map_zero, map_one,
    zero_mul, zero_add, one_mul, add_zero, div_eq_mul_inv]

theorem pmoebius_sMat (t : K₀) {z : K} (hz : z ∈ upperHalfPlane K₀ K) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk (sMat t)) z = algebraMap K₀ K t + z⁻¹ := by
  have h00 : (sMat t : GL (Fin 2) K₀) 0 0 = t := by
    show (!![t, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K₀) 0 0 = t; simp
  have h01 : (sMat t : GL (Fin 2) K₀) 0 1 = 1 := by
    show (!![t, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K₀) 0 1 = 1; simp
  have h10 : (sMat t : GL (Fin 2) K₀) 1 0 = 1 := by
    show (!![t, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 1; simp
  have h11 : (sMat t : GL (Fin 2) K₀) 1 1 = 0 := by
    show (!![t, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K₀) 1 1 = 0; simp
  have hz0 := ne_zero_of_mem K₀ hz
  rw [pmoebius_mk K₀ _ z (moebius_denom_ne_zero_of_mem K₀ hz _), moebius, h10, h11, h00, h01, map_zero, map_one,
    one_mul, add_zero, add_div, mul_div_cancel_right₀ _ hz0, one_div]

theorem pmoebius_tMat (t : K₀) {z : K} (hz : z ∈ upperHalfPlane K₀ K) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk (tMat t)) z = z + algebraMap K₀ K t := by
  have h00 : (tMat t : GL (Fin 2) K₀) 0 0 = 1 := by
    show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K₀) 0 0 = 1; simp
  have h01 : (tMat t : GL (Fin 2) K₀) 0 1 = t := by
    show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K₀) 0 1 = t; simp
  have h10 : (tMat t : GL (Fin 2) K₀) 1 0 = 0 := by
    show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 0; simp
  have h11 : (tMat t : GL (Fin 2) K₀) 1 1 = 1 := by
    show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) K₀) 1 1 = 1; simp
  rw [pmoebius_mk K₀ _ z (moebius_denom_ne_zero_of_mem K₀ hz _), moebius, h10, h11, h00, h01, map_zero, map_one,
    one_mul, zero_mul, zero_add, div_one]

theorem pmoebius_jMat {z : K} (hz : z ∈ upperHalfPlane K₀ K) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk (jMat (K₀ := K₀))) z = z⁻¹ := by
  have h00 : (jMat : GL (Fin 2) K₀) 0 0 = 0 := by
    show (!![(0 : K₀), 1; 1, 0] : Matrix (Fin 2) (Fin 2) K₀) 0 0 = 0; simp
  have h01 : (jMat : GL (Fin 2) K₀) 0 1 = 1 := by
    show (!![(0 : K₀), 1; 1, 0] : Matrix (Fin 2) (Fin 2) K₀) 0 1 = 1; simp
  have h10 : (jMat : GL (Fin 2) K₀) 1 0 = 1 := by
    show (!![(0 : K₀), 1; 1, 0] : Matrix (Fin 2) (Fin 2) K₀) 1 0 = 1; simp
  have h11 : (jMat : GL (Fin 2) K₀) 1 1 = 0 := by
    show (!![(0 : K₀), 1; 1, 0] : Matrix (Fin 2) (Fin 2) K₀) 1 1 = 0; simp
  rw [pmoebius_mk K₀ _ z (moebius_denom_ne_zero_of_mem K₀ hz _), moebius, h10, h11, h00, h01, map_zero, map_one,
    one_mul, add_zero, zero_mul, zero_add, one_div]

theorem coe_mk_smul (g : GL (Fin 2) K₀) (z : ↥(upperHalfPlane K₀ K)) :
    ((Matrix.ProjGenLinGroup.mk g • z : ↥(upperHalfPlane K₀ K)) : K) = pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) (z : K) :=
  rfl

end Matrices

section Analytic

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "Ω" => upperHalfPlane K₀ K

theorem isUnit_smul (ϖ₁ : PseudoUniformizer K₀ K) (P : PGL(2, K₀)) {F : ↥(holRing ϖ₁)} (hF : IsUnit F) :
    IsUnit (P • F) :=
  hF.map (MulSemiringAction.toRingHom (PGL(2, K₀)) ↥(holRing ϖ₁) P)

theorem inv_smul_apply (ϖ₁ : PseudoUniformizer K₀ K) (P : PGL(2, K₀)) (F : ↥(holRing ϖ₁)) (z : ↥Ω) :
    ((P⁻¹ • F : ↥(holRing ϖ₁)) : ↥Ω → K) z = (F : ↥Ω → K) (P • z) := by
  rw [coe_smul_holRing_apply, inv_inv]

section Laws

variable [CompleteSpace K] [IsAlgClosed K]

theorem exists_law_sub (ϖ₁ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ₁.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F) (t : K₀) :
    ∃ (c : Γ₀) (m : ℤ), ∀ z : ↥Ω,
      Valued.v (algebraMap K₀ K ϖ₁.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t) →
      Valued.v ((z : K) - algebraMap K₀ K t) < 1 →
        Valued.v ((F : ↥Ω → K) z) = c * Valued.v ((z : K) - algebraMap K₀ K t) ^ m := by
  set P : PGL(2, K₀) := Matrix.ProjGenLinGroup.mk (tMat t) with hP
  obtain ⟨c, m, h⟩ := CerednikDrinfeld.Omega.exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube K₀ K ϖ₁ hrk hunif
    (P⁻¹ • F) (isUnit_smul ϖ₁ P⁻¹ hF)
  refine ⟨c, m, fun z h1 h2 => ?_⟩
  have hmem : (z : K) - algebraMap K₀ K t ∈ stdEdgeTube ϖ₁ := ⟨sub_mem_upperHalfPlane K₀ z.2 t, h1, h2⟩
  have hz := h _ hmem
  rw [inv_smul_apply] at hz
  have hpt : (P • (⟨(z : K) - algebraMap K₀ K t, hmem.1⟩ : ↥Ω) : ↥Ω) = z := by
    apply Subtype.ext
    rw [hP, coe_mk_smul, pmoebius_tMat K₀ t hmem.1, sub_add_cancel]
  rwa [hpt] at hz

theorem exists_law_inv (ϖ₁ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ₁.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F) :
    ∃ (c : Γ₀) (m : ℤ), ∀ z : ↥Ω,
      Valued.v (algebraMap K₀ K ϖ₁.ϖ) < (Valued.v (z : K))⁻¹ → (Valued.v (z : K))⁻¹ < 1 →
        Valued.v ((F : ↥Ω → K) z) = c * (Valued.v (z : K))⁻¹ ^ m := by
  set P : PGL(2, K₀) := Matrix.ProjGenLinGroup.mk (jMat (K₀ := K₀)) with hP
  obtain ⟨c, m, h⟩ := CerednikDrinfeld.Omega.exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube K₀ K ϖ₁ hrk hunif
    (P⁻¹ • F) (isUnit_smul ϖ₁ P⁻¹ hF)
  refine ⟨c, m, fun z h1 h2 => ?_⟩
  have hmem : (z : K)⁻¹ ∈ stdEdgeTube ϖ₁ :=
    ⟨inv_mem_upperHalfPlane K₀ z.2, by rw [map_inv₀]; exact h1, by rw [map_inv₀]; exact h2⟩
  have hz := h _ hmem
  rw [inv_smul_apply] at hz
  have hpt : (P • (⟨(z : K)⁻¹, hmem.1⟩ : ↥Ω) : ↥Ω) = z := by
    apply Subtype.ext
    rw [hP, coe_mk_smul, pmoebius_jMat K₀ hmem.1, inv_inv]
  rw [hpt] at hz
  rw [hz, map_inv₀]

theorem exists_star (ϖ₁ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ₁.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    (hTsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t'))
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F) :
    ∃ (μ : K₀ → ℤ) (c₀ : Γ₀), ∀ z : ↥Ω,
      (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ₁.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t)) →
      Valued.v (z : K) < (Valued.v (algebraMap K₀ K ϖ₁.ϖ))⁻¹ →
        Valued.v ((F : ↥Ω → K) z) = c₀ * ∏ t ∈ T, Valued.v ((z : K) - algebraMap K₀ K t) ^ (μ t) := by
  choose c μ hμ using fun t : K₀ => exists_law_sub ϖ₁ hrk hunif F hF t
  obtain ⟨cInf, mInf, hInf⟩ := exists_law_inv ϖ₁ hrk hunif F hF
  obtain ⟨-, c₀, hstar⟩ := CerednikDrinfeld.Omega.sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow K₀ K ϖ₁ hrk hunif
    T hT hTcov hTsep F hF μ mInf (fun t _ => ⟨c t, hμ t⟩) ⟨cInf, hInf⟩
  exact ⟨μ, c₀, hstar⟩

end Laws

theorem mem_upperHalfPlane_of_star (ϖ₁ : PseudoUniformizer K₀ K)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ₁.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    {z : K} (h1 : ∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ₁.ϖ) < Valued.v (z - algebraMap K₀ K t))
    (h2 : Valued.v z < (Valued.v (algebraMap K₀ K ϖ₁.ϖ))⁻¹) : z ∈ upperHalfPlane K₀ K := by
  rw [mem_upperHalfPlane_iff]
  rintro a rfl
  by_cases hva : Valued.v (algebraMap K₀ K a) ≤ 1
  · obtain ⟨t, ht, hlt⟩ := hTcov a hva
    have hgt := h1 t ht
    rcases hunif (a - t) with h | h
    · rw [map_sub] at h; exact (not_lt.2 h) hgt
    · rw [map_sub] at h; exact (not_lt.2 h) hlt
  · push Not at hva
    have ha0 : algebraMap K₀ K a ≠ 0 := by
      intro h0; rw [h0, map_zero] at hva; exact not_lt.2 zero_le' hva
    have ha0' : a ≠ 0 := fun h => ha0 (by rw [h, map_zero])
    have hpos : 0 < Valued.v (algebraMap K₀ K a) := (Valuation.pos_iff _).2 ha0
    rcases hunif a⁻¹ with h | h
    · rw [map_inv₀, map_inv₀] at h
      have : (Valued.v (algebraMap K₀ K ϖ₁.ϖ))⁻¹ ≤ Valued.v (algebraMap K₀ K a) := (inv_le_comm₀ hpos ϖ₁.pos).1 h
      exact (not_lt.2 this) h2
    · rw [map_inv₀, map_inv₀, one_le_inv₀ hpos] at h
      exact (not_lt.2 h) hva

theorem v_sub_eq_one_of_mem_affinoid_zero (ϖ₁ : PseudoUniformizer K₀ K) {u : K} (hu : u ∈ affinoid ϖ₁ 0)
    (t : K₀) (ht : Valued.v (algebraMap K₀ K t) ≤ 1) : Valued.v (u - algebraMap K₀ K t) = 1 := by
  rw [mem_affinoid_iff'] at hu
  refine le_antisymm ?_ (by simpa using hu.2 t)
  refine (Valuation.map_sub _ _ _).trans (max_le (by simpa using hu.1) ht)

theorem v_le_one_of_mem_affinoid_zero (ϖ₁ : PseudoUniformizer K₀ K) {u : K} (hu : u ∈ affinoid ϖ₁ 0) : Valued.v u ≤ 1 := by
  rw [mem_affinoid_iff'] at hu; simpa using hu.1

theorem star_of_mem_affinoid_zero (ϖ₁ : PseudoUniformizer K₀ K) (T : Finset K₀)
    (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1) {u : K} (hu : u ∈ affinoid ϖ₁ 0) :
    (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ₁.ϖ) < Valued.v (u - algebraMap K₀ K t)) ∧
      Valued.v u < (Valued.v (algebraMap K₀ K ϖ₁.ϖ))⁻¹ := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [v_sub_eq_one_of_mem_affinoid_zero ϖ₁ hu t (hT t ht)]; exact ϖ₁.lt_one
  · exact (v_le_one_of_mem_affinoid_zero ϖ₁ hu).trans_lt ((one_lt_inv₀ ϖ₁.pos).2 ϖ₁.lt_one)

theorem v_apply_eq_const_of_star (ϖ₁ : PseudoUniformizer K₀ K) (T : Finset K₀)
    (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (F : ↥(holRing ϖ₁)) (μ : K₀ → ℤ) (c₀ : Γ₀)
    (hstar : ∀ z : ↥Ω,
      (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ₁.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t)) →
      Valued.v (z : K) < (Valued.v (algebraMap K₀ K ϖ₁.ϖ))⁻¹ →
        Valued.v ((F : ↥Ω → K) z) = c₀ * ∏ t ∈ T, Valued.v ((z : K) - algebraMap K₀ K t) ^ (μ t))
    (u : K) (hu : u ∈ affinoid ϖ₁ 0) :
    Valued.v ((F : ↥Ω → K) ⟨u, affinoid_subset_upperHalfPlane ϖ₁ 0 hu⟩) = c₀ := by
  obtain ⟨h1, h2⟩ := star_of_mem_affinoid_zero ϖ₁ T hT hu
  rw [hstar ⟨u, affinoid_subset_upperHalfPlane ϖ₁ 0 hu⟩ h1 h2]
  have : ∏ t ∈ T, Valued.v (u - algebraMap K₀ K t) ^ (μ t) = 1 :=
    Finset.prod_eq_one fun t ht => by rw [v_sub_eq_one_of_mem_affinoid_zero ϖ₁ hu t (hT t ht), one_zpow]
  simp only [this, mul_one]

theorem edge_step [IsAlgClosed K] [CompleteSpace K] (ϖ₁ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K ϖ₁.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (T : Finset K₀) (hT : ∀ t ∈ T, Valued.v (algebraMap K₀ K t) ≤ 1)
    (hTcov : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < 1)
    (hTsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 1 ≤ Valued.v (algebraMap K₀ K t - algebraMap K₀ K t'))
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F) (μ : K₀ → ℤ) (c₀ : Γ₀)
    (hstar : ∀ z : ↥Ω,
      (∀ t ∈ T, Valued.v (algebraMap K₀ K ϖ₁.ϖ) < Valued.v ((z : K) - algebraMap K₀ K t)) →
      Valued.v (z : K) < (Valued.v (algebraMap K₀ K ϖ₁.ϖ))⁻¹ →
        Valued.v ((F : ↥Ω → K) z) = c₀ * ∏ t ∈ T, Valued.v ((z : K) - algebraMap K₀ K t) ^ (μ t))
    (N : GL (Fin 2) K₀)
    (hN : ∀ z : ↥Ω, ((Matrix.ProjGenLinGroup.mk N • z : ↥Ω) : K) = (z : K) * (algebraMap K₀ K ϖ₁.ϖ)⁻¹)
    (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0) :
    Valued.v ((F : ↥Ω → K) (Matrix.ProjGenLinGroup.mk N • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
      Valued.v ((F : ↥Ω → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
        Valued.v (algebraMap K₀ K ϖ₁.ϖ) ^ (-(∑ t ∈ T, μ t)) := by
  classical
  set P : PGL(2, K₀) := Matrix.ProjGenLinGroup.mk N with hP

  obtain ⟨μ', c₀', hstar'⟩ := exists_star ϖ₁ hrk hunif T hT hTcov hTsep (P⁻¹ • F) (isUnit_smul ϖ₁ P⁻¹ hF)

  let Ft : K → K := fun x => if hx : x ∈ upperHalfPlane K₀ K then (F : ↥Ω → K) ⟨x, hx⟩ else 0
  have hFt : ∀ (x : K) (hx : x ∈ upperHalfPlane K₀ K), Ft x = (F : ↥Ω → K) ⟨x, hx⟩ := fun x hx => by
    simp only [Ft, dif_pos hx]
  have hΩ := affinoid_subset_upperHalfPlane ϖ₁ 0
  have key := CerednikDrinfeld.Omega.v_apply_mul_inv_eq_mul_zpow_neg_sum_of_star K₀ K ϖ₁ hunif T hT hTcov hTsep Ft c₀ c₀' μ μ'
    (fun z h1 h2 => by
      have hz := mem_upperHalfPlane_of_star ϖ₁ hunif T hTcov h1 h2
      rw [hFt z hz]
      exact hstar ⟨z, hz⟩ h1 h2)
    (fun z h1 h2 => by
      have hz := mem_upperHalfPlane_of_star ϖ₁ hunif T hTcov h1 h2
      have h := hstar' ⟨z, hz⟩ h1 h2
      rw [inv_smul_apply] at h
      have hmem : z * (algebraMap K₀ K ϖ₁.ϖ)⁻¹ ∈ upperHalfPlane K₀ K := by
        rw [← hN ⟨z, hz⟩]; exact (P • (⟨z, hz⟩ : ↥Ω)).2
      have hpt : (P • (⟨z, hz⟩ : ↥Ω) : ↥Ω) = ⟨z * (algebraMap K₀ K ϖ₁.ϖ)⁻¹, hmem⟩ := Subtype.ext (hN ⟨z, hz⟩)
      rw [hFt _ hmem, ← hpt]
      exact h)
    w w' hw hw'
  have hmem : w * (algebraMap K₀ K ϖ₁.ϖ)⁻¹ ∈ upperHalfPlane K₀ K := by
    rw [← hN ⟨w, hΩ hw⟩]; exact (P • (⟨w, hΩ hw⟩ : ↥Ω)).2
  have hpt : (P • (⟨w, hΩ hw⟩ : ↥Ω) : ↥Ω) = ⟨w * (algebraMap K₀ K ϖ₁.ϖ)⁻¹, hmem⟩ := Subtype.ext (hN ⟨w, hΩ hw⟩)
  rw [hFt _ hmem, hFt _ (hΩ hw'), ← hpt] at key
  exact key

end Analytic

end HarmV0

namespace TSDA

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "Ω" => upperHalfPlane K₀ K

theorem v_moebius_eq_of_iwahori (ϖ₁ : PseudoUniformizer K₀ K) (a b c d : K)
    (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ Valued.v (algebraMap K₀ K ϖ₁.ϖ)) (hc : Valued.v c ≤ 1) (hd : Valued.v d ≤ 1)
    (hdet : Valued.v (a * d - b * c) = 1) {z : K} (hz : z ∈ stdEdgeTube ϖ₁) :
    c * z + d ≠ 0 ∧ Valued.v ((a * z + b) / (c * z + d)) = Valued.v z := by
  obtain ⟨-, hz1, hz2⟩ := hz
  have hq1 : Valued.v (algebraMap K₀ K ϖ₁.ϖ) < 1 := ϖ₁.lt_one

  have hbc : Valued.v (b * c) < 1 := by
    rw [map_mul]
    calc Valued.v b * Valued.v c ≤ Valued.v (algebraMap K₀ K ϖ₁.ϖ) * 1 := mul_le_mul' hb hc
      _ < 1 := by rw [mul_one]; exact hq1
  have had : Valued.v (a * d) = 1 := by
    by_contra hne
    have hlt : Valued.v (a * d) < 1 := lt_of_le_of_ne (by rw [map_mul]; exact mul_le_one' ha hd) hne
    have := Valuation.map_sub_lt _ hlt hbc
    rw [hdet] at this
    exact lt_irrefl _ this
  have ha1 : Valued.v a = 1 := by
    apply le_antisymm ha
    by_contra h; rw [not_le] at h
    have : Valued.v (a * d) < 1 := by rw [map_mul]; exact mul_lt_one_of_lt_of_le h hd
    rw [had] at this; exact lt_irrefl _ this
  have hd1 : Valued.v d = 1 := by
    apply le_antisymm hd
    by_contra h; rw [not_le] at h
    have : Valued.v (a * d) < 1 := by rw [map_mul, mul_comm]; exact mul_lt_one_of_lt_of_le h ha
    rw [had] at this; exact lt_irrefl _ this

  have hnum : Valued.v (a * z + b) = Valued.v z := by
    rw [Valuation.map_add_eq_of_lt_left]
    · rw [map_mul, ha1, one_mul]
    · rw [map_mul, ha1, one_mul]; exact lt_of_le_of_lt hb hz1
  have hden : Valued.v (c * z + d) = 1 := by
    rw [Valuation.map_add_eq_of_lt_right, hd1]
    rw [hd1, map_mul, mul_comm]
    exact mul_lt_one_of_lt_of_le hz2 hc
  have hden0 : c * z + d ≠ 0 := (Valuation.ne_zero_iff _).mp (by rw [hden]; exact one_ne_zero)
  exact ⟨hden0, by rw [map_div₀, hnum, hden, div_one]⟩

end TSDA

namespace TSDA

open HarmV0

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀]
variable {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem scalarGL_mul_apply (c : K₀ˣ) (g : GL (Fin 2) K₀) (i j : Fin 2) :
    ((scalarGL c * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) i j = (c : K₀) * g i j := by
  rw [Units.val_mul, scalarGL_coe, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul]

theorem det_scalarGL_mul (c : K₀ˣ) (g : GL (Fin 2) K₀) :
    ((scalarGL c * g : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀).det =
      (c : K₀) ^ 2 * (g : Matrix (Fin 2) (Fin 2) K₀).det := by
  rw [Units.val_mul, scalarGL_coe, Matrix.smul_mul, Matrix.one_mul, Matrix.det_smul, Fintype.card_fin]

theorem coe_sMat_zero_mul_nMat (π : K₀) (hπ : π ≠ 0) :
    ((sMat (0 : K₀) * nMat π hπ : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = !![0, π; 1, 0] := by
  rw [Units.val_mul, coe_sMat, coe_nMat]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [DecidableEq K] in
theorem eq_of_sq_eq_sq {x y : Γ₀} (h : x ^ 2 = y ^ 2) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd h (ne_of_lt (by rw [sq, sq]; exact mul_lt_mul'' hlt hlt zero_le' zero_le'))
  · exact heq
  · exact absurd h (ne_of_gt (by rw [sq, sq]; exact mul_lt_mul'' hgt hgt zero_le' zero_le'))

theorem iwahori {ϖ : R} (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (ϖ₁ : PseudoUniformizer K₀ K) (hϖ₁ : ϖ₁.ϖ = algebraMap R K₀ ϖ) (hϖ0 : algebraMap R K₀ ϖ ≠ 0)
    (g : GL (Fin 2) K₀) (h0 : g • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀)
    (h1 : g • ((sMat (0 : K₀) * nMat (algebraMap R K₀ ϖ) hϖ0) • LT.LatticeTree.stdVertex R K₀) =
      (sMat (0 : K₀) * nMat (algebraMap R K₀ ϖ) hϖ0) • LT.LatticeTree.stdVertex R K₀) :
    ∀ z : K, z ∈ stdEdgeTube ϖ₁ →
      pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) z ∈ stdEdgeTube ϖ₁ ∧
        Valued.v (pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) z) = Valued.v z := by
  set d : GL (Fin 2) K₀ := sMat (0 : K₀) * nMat (algebraMap R K₀ ϖ) hϖ0 with hd

  rw [BruhatTits.gl_smul_def, LT.LatticeTree.Vertex.act_stdVertex_eq_iff] at h0
  obtain ⟨c₀, M, hM⟩ := h0
  have h1' : (d⁻¹ * g * d) • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀ := by
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  rw [BruhatTits.gl_smul_def, LT.LatticeTree.Vertex.act_stdVertex_eq_iff] at h1'
  obtain ⟨c₁, M', hM'⟩ := h1'

  have hent : ∀ i j, algebraMap R K₀ (M i j) = (c₀ : K₀) * g i j := fun i j => by
    have := congrArg (fun A : GL (Fin 2) K₀ => (A : Matrix (Fin 2) (Fin 2) K₀) i j) hM
    simp only [Matrix.GeneralLinearGroup.map_apply] at this
    rw [this, scalarGL_mul_apply]

  have hmapdet : ∀ N : GL (Fin 2) R, algebraMap R K₀ ((N : Matrix (Fin 2) (Fin 2) R).det) =
      ((Matrix.GeneralLinearGroup.map (algebraMap R K₀) N : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀).det := fun N => by
    rw [RingHom.map_det]; rfl
  have hvdet : ∀ N : GL (Fin 2) R, Valued.v (algebraMap K₀ K (algebraMap R K₀ ((N : Matrix (Fin 2) (Fin 2) R).det))) = 1 :=
    fun N => by rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact v_unit_eq_one hint _
  have hgdet0 : Valued.v (algebraMap K₀ K (g : Matrix (Fin 2) (Fin 2) K₀).det) ≠ 0 := by
    rw [Valuation.ne_zero_iff, map_ne_zero]; exact Matrix.GeneralLinearGroup.det_ne_zero g
  have hconjdet : ((d⁻¹ * g * d : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀).det = (g : Matrix (Fin 2) (Fin 2) K₀).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul,
      mul_right_comm, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hvc : Valued.v (algebraMap K₀ K c₀) = Valued.v (algebraMap K₀ K c₁) := by
    apply eq_of_sq_eq_sq
    have e0 := hvdet M
    rw [hmapdet, hM, det_scalarGL_mul, map_mul, map_pow, map_mul, map_pow] at e0
    have e1 := hvdet M'
    rw [hmapdet, hM', det_scalarGL_mul, hconjdet, map_mul, map_pow, map_mul, map_pow] at e1
    exact mul_right_cancel₀ hgdet0 (e0.trans e1.symm)
  have hc₁v0 : Valued.v (algebraMap K₀ K c₁) ≠ 0 := by
    rw [Valuation.ne_zero_iff, map_ne_zero]; exact c₁.ne_zero

  have h01 : algebraMap R K₀ ϖ * algebraMap R K₀ (M' 1 0) = (c₁ : K₀) * g 0 1 := by
    have e : d * Matrix.GeneralLinearGroup.map (algebraMap R K₀) M' = scalarGL c₁ * g * d := by
      rw [hM', ← mul_assoc, ← scalarGL_mul_comm c₁ d]; group
    have e00 := congrArg (fun A : GL (Fin 2) K₀ => (A : Matrix (Fin 2) (Fin 2) K₀) 0 0) e
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map_apply] at e00
    rw [hd, coe_sMat_zero_mul_nMat] at e00
    simp only [scalarGL_coe, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      smul_eq_mul, mul_one, mul_zero, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val'] at e00
    linear_combination e00

  have hb : Valued.v (algebraMap K₀ K (algebraMap R K₀ (M 0 1))) ≤ Valued.v (algebraMap K₀ K ϖ₁.ϖ) := by
    rw [hent, map_mul, map_mul, hvc]
    have : Valued.v (algebraMap K₀ K c₁) * Valued.v (algebraMap K₀ K (g 0 1)) =
        Valued.v (algebraMap K₀ K ϖ₁.ϖ) * Valued.v (algebraMap K₀ K (algebraMap R K₀ (M' 1 0))) := by
      rw [← map_mul, ← map_mul, ← h01, map_mul, map_mul, hϖ₁]
    rw [this]
    exact mul_le_of_le_one_right' (hint _)

  intro z hz
  have hzΩ : z ∈ upperHalfPlane K₀ K := hz.1
  have hmk : Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (algebraMap R K₀) M) := by
    rw [hM, map_mul, ← scalar_eq_scalarGL, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
  have hform : pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) z =
      (algebraMap K₀ K (algebraMap R K₀ (M 0 0)) * z + algebraMap K₀ K (algebraMap R K₀ (M 0 1))) /
        (algebraMap K₀ K (algebraMap R K₀ (M 1 0)) * z + algebraMap K₀ K (algebraMap R K₀ (M 1 1))) := by
    rw [hmk, pmoebius_mk K₀ _ z (moebius_denom_ne_zero_of_mem K₀ hzΩ _), moebius]
    simp only [Matrix.GeneralLinearGroup.map_apply]
  have hdet : Valued.v (algebraMap K₀ K (algebraMap R K₀ (M 0 0)) * algebraMap K₀ K (algebraMap R K₀ (M 1 1)) -
      algebraMap K₀ K (algebraMap R K₀ (M 0 1)) * algebraMap K₀ K (algebraMap R K₀ (M 1 0))) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_sub, ← map_sub, ← Matrix.det_fin_two]
    exact hvdet M
  obtain ⟨-, hv⟩ := v_moebius_eq_of_iwahori ϖ₁ _ _ _ _ (hint _) hb (hint _) (hint _) hdet hz
  rw [hform]
  refine ⟨⟨?_, ?_, ?_⟩, hv⟩
  · rw [← hform]; exact pmoebius_mem_upperHalfPlane K₀ hzΩ _
  · rw [hv]; exact hz.2.1
  · rw [hv]; exact hz.2.2

end TSDA

open HarmV0 in
theorem jump_std
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hϖ₁ : ϖ₁.ϖ = algebraMap R K₀ ϖ)
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F)
    (c : Γ₀) (mt : ℤ)
    (hcm : ∀ (z : K) (hz : z ∈ stdEdgeTube ϖ₁),
      Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨z, hz.1⟩) = c * Valued.v z ^ mt)
    (hϖ0 : algebraMap R K₀ ϖ ≠ 0)
    (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0) :
    Valued.v ((F : ↥(upperHalfPlane K₀ K) → K)
        (Matrix.ProjGenLinGroup.mk (sMat (0 : K₀) * nMat (algebraMap R K₀ ϖ) hϖ0) •
          ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
      Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
        Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ mt := by
  classical
  letI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _

  have hpϖ : Valued.v (algebraMap K₀ K ϖ₁.ϖ) = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) := by rw [hϖ₁]
  have hunif := hunif_of_frame (K := K) hϖ hint ϖ₁ hϖ₁
  set T : Finset K₀ := repFinset R K₀ ϖ with hTdef
  have hT := repFinset_le_one (K := K) hint ϖ
  have hTcov := repFinset_cov (K := K) hϖ hint hv ϖ₁
  have hTsep := repFinset_sep (K := K) hϖ hint
  have hΩ := affinoid_subset_upperHalfPlane ϖ₁ 0

  set n : GL (Fin 2) K₀ := nMat (algebraMap R K₀ ϖ) hϖ0 with hndef
  set s : R → GL (Fin 2) K₀ := fun t => sMat (algebraMap R K₀ t) with hsdef
  obtain ⟨hadjn, hsfix, hnbrs, hcong, hne⟩ :=
    CerednikDrinfeld.BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer R K₀ ϖ hϖ n rfl s (fun t => rfl)
  have hn : ∀ z : ↥(upperHalfPlane K₀ K),
      ((Matrix.ProjGenLinGroup.mk n • z : ↥(upperHalfPlane K₀ K)) : K) = (z : K) * (algebraMap K₀ K ϖ₁.ϖ)⁻¹ := fun z => by
    rw [coe_mk_smul, hndef, pmoebius_nMat K₀ _ hϖ0 z.2, hϖ₁]
  have hs0 : s 0 = sMat (0 : K₀) := by show sMat (algebraMap R K₀ 0) = sMat 0; rw [map_zero]

  choose cF mF hmF using fun t : K₀ => exists_law_sub ϖ₁ hrk hunif F hF t
  obtain ⟨cInf, mInf, hInf⟩ := exists_law_inv ϖ₁ hrk hunif F hF
  obtain ⟨hsumF, c₀, hstarF⟩ := CerednikDrinfeld.Omega.sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow K₀ K ϖ₁ hrk
    hunif T hT hTcov hTsep F hF mF mInf (fun t _ => ⟨cF t, hmF t⟩) ⟨cInf, hInf⟩
  have hfibre : ∀ (u : K) (hu : u ∈ affinoid ϖ₁ 0), Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨u, hΩ hu⟩) = c₀ :=
    fun u hu => v_apply_eq_const_of_star ϖ₁ T hT F mF c₀ hstarF u hu

  set P0 : PGL(2, K₀) := Matrix.ProjGenLinGroup.mk (s 0) with hP0
  set F0 : ↥(holRing ϖ₁) := P0⁻¹ • F with hF0def
  have hF0 : IsUnit F0 := isUnit_smul ϖ₁ P0⁻¹ hF
  have hF0_apply : ∀ z : ↥(upperHalfPlane K₀ K),
      (F0 : ↥(upperHalfPlane K₀ K) → K) z = (F : ↥(upperHalfPlane K₀ K) → K) (P0 • z) := fun z => inv_smul_apply ϖ₁ P0 F z
  choose c0 m0 hm0 using fun t : K₀ => exists_law_sub ϖ₁ hrk hunif F0 hF0 t
  have hInf0 : ∃ c' : Γ₀, ∀ z : ↥(upperHalfPlane K₀ K),
      Valued.v (algebraMap K₀ K ϖ₁.ϖ) < (Valued.v (z : K))⁻¹ → (Valued.v (z : K))⁻¹ < 1 →
        Valued.v ((F0 : ↥(upperHalfPlane K₀ K) → K) z) = c' * (Valued.v (z : K))⁻¹ ^ mt := by
    refine ⟨c, fun z h1 h2 => ?_⟩
    rw [hF0_apply]
    have hval : ((P0 • z : ↥(upperHalfPlane K₀ K)) : K) = (z : K)⁻¹ := by
      rw [hP0, coe_mk_smul, hs0, pmoebius_sMat K₀ _ z.2, map_zero, zero_add]
    have hmem : (z : K)⁻¹ ∈ stdEdgeTube ϖ₁ := by
      refine ⟨?_, ?_, ?_⟩
      · rw [← hval]; exact (P0 • z).2
      · rw [map_inv₀]; exact h1
      · rw [map_inv₀]; exact h2
    have hpt : (P0 • z : ↥(upperHalfPlane K₀ K)) = ⟨(z : K)⁻¹, hmem.1⟩ := Subtype.ext hval
    rw [hpt, hcm _ hmem, map_inv₀]
  obtain ⟨hsum0, c₀0, hstar0⟩ := CerednikDrinfeld.Omega.sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow K₀ K ϖ₁
    hrk hunif T hT hTcov hTsep F0 hF0 m0 mt (fun t _ => ⟨c0 t, hm0 t⟩) hInf0
  have h := edge_step ϖ₁ hrk hunif T hT hTcov hTsep F0 hF0 m0 c₀0 hstar0 n hn w w' hw hw'
  rw [hpϖ, show -(∑ t ∈ T, m0 t) = mt by omega, hF0_apply, hF0_apply, ← mul_smul, hP0,
    ← map_mul] at h

  have hu' : pmoebius K₀ (Matrix.ProjGenLinGroup.mk (s 0)) w' ∈ affinoid ϖ₁ 0 :=
    CerednikDrinfeld.Omega.pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq R K₀ K hint hv ϖ₁ (s 0) (hsfix 0) hw'
  have hpt : (Matrix.ProjGenLinGroup.mk (s 0) • (⟨w', hΩ hw'⟩ : ↥(upperHalfPlane K₀ K)) : ↥(upperHalfPlane K₀ K)) =
      ⟨_, hΩ hu'⟩ := Subtype.ext rfl
  rw [hpt, hfibre _ hu', ← hfibre w' hw'] at h
  rw [hs0, hndef] at h
  exact h

namespace TSDA

open HarmV0

variable {K₀ : Type} [Field K₀]

theorem sMat_zero_mul_self : (sMat (0 : K₀) * sMat 0 : GL (Fin 2) K₀) = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_sMat, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end TSDA

section Assembly

open HarmV0 TSDA

theorem TSDA.std_case
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hϖ₁ : ϖ₁.ϖ = algebraMap R K₀ ϖ)
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F) (hϖ0 : algebraMap R K₀ ϖ ≠ 0)
    (H : Subgroup PGL(2, K₀)) [Finite ↥H]
    (hH0 : ∀ h ∈ H, h • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀)
    (hHd : ∀ h ∈ H, h • ((sMat (0 : K₀) * nMat (algebraMap R K₀ ϖ) hϖ0) • LT.LatticeTree.stdVertex R K₀) =
      (sMat (0 : K₀) * nMat (algebraMap R K₀ ϖ) hϖ0) • LT.LatticeTree.stdVertex R K₀)
    (htame : Valued.v ((Nat.card ↥H : ℕ) : K) = 1)
    (hinv : ∀ h ∈ H, ∀ z : ↥(upperHalfPlane K₀ K),
      (F : ↥(upperHalfPlane K₀ K) → K) (h • z) = (F : ↥(upperHalfPlane K₀ K) → K) z)
    (m : ℤ)
    (hm : ∀ (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
        Valued.v ((F : ↥(upperHalfPlane K₀ K) → K)
            ((Matrix.ProjGenLinGroup.mk (sMat (0 : K₀) * nMat (algebraMap R K₀ ϖ) hϖ0)) •
              ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
          Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
            Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ m) :
    ((Nat.card ↥H : ℕ) : ℤ) ∣ m := by
  have hunif := hunif_of_frame (K := K) hϖ hint ϖ₁ hϖ₁

  obtain ⟨c, mt, hcm⟩ := CerednikDrinfeld.Omega.exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube K₀ K ϖ₁ hrk hunif F hF
  have hHtube : ∀ h ∈ H, ∀ z : K, z ∈ stdEdgeTube ϖ₁ →
      pmoebius K₀ h z ∈ stdEdgeTube ϖ₁ ∧ Valued.v (pmoebius K₀ h z) = Valued.v z := by
    intro h hh
    induction h using Matrix.ProjGenLinGroup.induction_on with
    | _ g =>
    exact TSDA.iwahori hϖ hint ϖ₁ hϖ₁ hϖ0 g (hH0 _ hh) (hHd _ hh)
  have hdiv := CerednikDrinfeld.Omega.natCard_dvd_of_isUnit_of_forall_apply_smul_eq_of_v_apply_eq_mul_zpow K₀ K ϖ₁ hrk hunif
    H (fun h hh z hz => (hHtube h hh z hz).1) (fun h hh z hz => (hHtube h hh z hz).2) htame F hF
    (fun h hh z _ => hinv h hh z) c mt hcm

  obtain ⟨w₀, hw₀⟩ := CerednikDrinfeld.Omega.affinoid_nonempty_of_exists_finset_cover K₀ K ϖ₁ 0
    (CerednikDrinfeld.Omega.forall_exists_finset_v_sub_lt_pow_of_finite_quotient R K₀ ϖ hϖ K hint hv hq ϖ₁ 0)
  have hj := jump_std R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hϖ₁ F hF c mt hcm hϖ0 w₀ w₀ hw₀ hw₀
  have hm₀ := hm w₀ w₀ hw₀ hw₀

  have hF0 : Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    intro h0
    obtain ⟨u, hu⟩ := hF
    have := congrArg (fun G : ↥(holRing ϖ₁) => (G : ↥(upperHalfPlane K₀ K) → K) ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩)
      u.mul_inv
    rw [hu] at this
    change (F : ↥(upperHalfPlane K₀ K) → K) _ * _ = (1 : ↥(upperHalfPlane K₀ K) → K) _ at this
    rw [h0, zero_mul, Pi.one_apply] at this
    exact zero_ne_one this
  have hqz : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ m = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ mt :=
    mul_left_cancel₀ hF0 (hm₀.symm.trans hj)
  have hmeq : m = mt := (zpow_right_strictAnti₀ (p_pos (K := K) hϖ) (p_lt_one (K := K) hϖ hint ϖ₁)).injective hqz
  rw [hmeq]; exact hdiv

theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hϖ₁ : ϖ₁.ϖ = algebraMap R K₀ ϖ)
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F)
    (y : LT.LatticeTree.Vertex R K₀) (hy : (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) y)
    (H : Subgroup PGL(2, K₀)) [Finite ↥H]
    (hH0 : ∀ h ∈ H, h • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀)
    (hHy : ∀ h ∈ H, h • y = y)
    (htame : Valued.v ((Nat.card ↥H : ℕ) : K) = 1)
    (hinv : ∀ h ∈ H, ∀ z : ↥(upperHalfPlane K₀ K),
      (F : ↥(upperHalfPlane K₀ K) → K) (h • z) = (F : ↥(upperHalfPlane K₀ K) → K) z)
    (m : ℤ)
    (hm : ∀ (g : GL (Fin 2) K₀), g • LT.LatticeTree.stdVertex R K₀ = y →
      ∀ (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
        Valued.v ((F : ↥(upperHalfPlane K₀ K) → K)
            ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
          Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
            Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ m) :
    ((Nat.card ↥H : ℕ) : ℤ) ∣ m := by
  classical
  set v₀ := LT.LatticeTree.stdVertex R K₀ with hv₀
  have hϖ0 : algebraMap R K₀ ϖ ≠ 0 := algebraMap_R_ne_zero hϖ.ne_zero
  set n : GL (Fin 2) K₀ := nMat (algebraMap R K₀ ϖ) hϖ0 with hndef
  set s : R → GL (Fin 2) K₀ := fun t => sMat (algebraMap R K₀ t) with hsdef
  set d : GL (Fin 2) K₀ := sMat (0 : K₀) * n with hddef
  obtain ⟨hadjn, hsfix, hnbrs, hcong, hne⟩ :=
    CerednikDrinfeld.BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer R K₀ ϖ hϖ n rfl s (fun t => rfl)
  have hs0 : s 0 = sMat (0 : K₀) := by rw [hsdef]; simp only [map_zero]
  have hs0fix : sMat (0 : K₀) • v₀ = v₀ := by rw [← hs0]; exact hsfix 0

  obtain ⟨k, hk0, hky⟩ : ∃ k : GL (Fin 2) K₀, k • v₀ = v₀ ∧ (k * d) • v₀ = y := by
    rcases hnbrs y hy with rfl | ⟨t, rfl⟩
    · refine ⟨sMat 0, hs0fix, ?_⟩
      rw [hddef, ← mul_assoc, sMat_zero_mul_self, one_mul]
    · refine ⟨s t * sMat 0, by rw [mul_smul, hs0fix, hsfix], ?_⟩
      rw [hddef, mul_assoc, ← mul_assoc (sMat 0), sMat_zero_mul_self, one_mul]

  set P : PGL(2, K₀) := Matrix.ProjGenLinGroup.mk k with hP
  set e : PGL(2, K₀) ≃* PGL(2, K₀) := MulAut.conj P⁻¹ with he
  set H' : Subgroup PGL(2, K₀) := H.map (e : PGL(2, K₀) →* PGL(2, K₀)) with hH'
  have eH : ↥H ≃* ↥H' := MulEquiv.subgroupMap e H
  haveI : Finite ↥H' := Finite.of_equiv _ eH.toEquiv
  have hcard : Nat.card ↥H' = Nat.card ↥H := (Nat.card_congr eH.toEquiv).symm
  have hmemH' : ∀ h' ∈ H', ∃ h ∈ H, h' = P⁻¹ * h * P := by
    intro h' hh'
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hh'
    exact ⟨h, hh, by rw [he]; simp [MulAut.conj_apply]⟩
  have hPv : P • v₀ = v₀ := by rw [hP, CerednikDrinfeld.BruhatTits.pgl_mk_smul]; exact hk0
  have hPd : P • (d • v₀) = y := by
    rw [hP, CerednikDrinfeld.BruhatTits.pgl_mk_smul, ← mul_smul]; exact hky
  set F' : ↥(holRing ϖ₁) := P⁻¹ • F with hF'
  have hF'u : IsUnit F' := isUnit_smul ϖ₁ P⁻¹ hF
  have hF'ap : ∀ z : ↥(upperHalfPlane K₀ K), (F' : ↥(upperHalfPlane K₀ K) → K) z =
      (F : ↥(upperHalfPlane K₀ K) → K) (P • z) := fun z => inv_smul_apply ϖ₁ P F z

  have hH0' : ∀ h' ∈ H', h' • v₀ = v₀ := by
    intro h' hh'
    obtain ⟨h, hh, rfl⟩ := hmemH' h' hh'
    rw [mul_smul, mul_smul, hPv, hH0 h hh, inv_smul_eq_iff, hPv]
  have hHd' : ∀ h' ∈ H', h' • (d • v₀) = d • v₀ := by
    intro h' hh'
    obtain ⟨h, hh, rfl⟩ := hmemH' h' hh'
    rw [mul_smul, mul_smul, hPd, hHy h hh, inv_smul_eq_iff, hPd]
  have htame' : Valued.v ((Nat.card ↥H' : ℕ) : K) = 1 := by rw [hcard]; exact htame
  have hinv' : ∀ h' ∈ H', ∀ z : ↥(upperHalfPlane K₀ K),
      (F' : ↥(upperHalfPlane K₀ K) → K) (h' • z) = (F' : ↥(upperHalfPlane K₀ K) → K) z := by
    intro h' hh' z
    obtain ⟨h, hh, rfl⟩ := hmemH' h' hh'
    rw [hF'ap, hF'ap, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_smul]
    exact hinv h hh _
  have hm' : ∀ (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
      Valued.v ((F' : ↥(upperHalfPlane K₀ K) → K)
          ((Matrix.ProjGenLinGroup.mk (sMat (0 : K₀) * nMat (algebraMap R K₀ ϖ) hϖ0)) •
            ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
        Valued.v ((F' : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
          Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ m := by
    intro w w' hw hw'
    have hu : pmoebius K₀ (Matrix.ProjGenLinGroup.mk k) w' ∈ affinoid ϖ₁ 0 :=
      CerednikDrinfeld.Omega.pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq R K₀ K hint hv ϖ₁ k hk0 hw'
    have h1 := hm (k * d) hky w (pmoebius K₀ (Matrix.ProjGenLinGroup.mk k) w') hw hu
    rw [hF'ap, hF'ap, ← mul_smul, hP, ← map_mul]
    rw [← hddef]
    convert h1 using 2
    rfl
  have hstd := TSDA.std_case R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hϖ₁ F' hF'u hϖ0 H' hH0'
    (by rw [← hndef, ← hddef]; exact hHd') htame' hinv' m (by rw [← hndef, ← hddef]; exact hm')
  rw [hcard] at hstd
  exact hstd

end Assembly

end
end S_CerednikDrinfeld_Omega_natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_natCard_dvd_of_v_apply_smul_eq_mul_zpow_of_forall_smul_eq (solution)
