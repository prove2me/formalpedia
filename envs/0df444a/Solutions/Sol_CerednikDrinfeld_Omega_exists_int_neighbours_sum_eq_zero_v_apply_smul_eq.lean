-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_int_neighbours_sum_eq_zero_v_apply_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/750e952a-09f7-539d-97b5-8a284feb3643

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_int_neighbours_sum_eq_zero_v_apply_smul_eq

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

open HarmV0 in
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
    (F : ↥(holRing ϖ₁)) (hF : IsUnit F) :
    ∃ m : LT.LatticeTree.Vertex R K₀ → ℤ,
      (∀ S : Finset (LT.LatticeTree.Vertex R K₀),
        (∀ y, y ∈ S ↔ (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) y) → ∑ y ∈ S, m y = 0) ∧
      ∀ (y : LT.LatticeTree.Vertex R K₀), (BruhatTits.tree R K₀).Adj (LT.LatticeTree.stdVertex R K₀) y →
        ∀ (g : GL (Fin 2) K₀), g • LT.LatticeTree.stdVertex R K₀ = y →
          ∀ (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
            Valued.v ((F : ↥(upperHalfPlane K₀ K) → K)
                ((Matrix.ProjGenLinGroup.mk g) • ⟨w, affinoid_subset_upperHalfPlane ϖ₁ 0 hw⟩)) =
              Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w', affinoid_subset_upperHalfPlane ϖ₁ 0 hw'⟩) *
                Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ (m y) := by
  classical
  letI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _

  have hpϖ : Valued.v (algebraMap K₀ K ϖ₁.ϖ) = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) := by rw [hϖ₁]
  have hunif := hunif_of_frame (K := K) hϖ hint ϖ₁ hϖ₁
  set T : Finset K₀ := repFinset R K₀ ϖ with hTdef
  have hT := repFinset_le_one (K := K) hint ϖ
  have hTcov := repFinset_cov (K := K) hϖ hint hv ϖ₁
  have hTsep := repFinset_sep (K := K) hϖ hint
  have hϖ0 : algebraMap R K₀ ϖ ≠ 0 := algebraMap_R_ne_zero hϖ.ne_zero
  have hΩ := affinoid_subset_upperHalfPlane ϖ₁ 0

  set n : GL (Fin 2) K₀ := nMat (algebraMap R K₀ ϖ) hϖ0 with hndef
  set s : R → GL (Fin 2) K₀ := fun t => sMat (algebraMap R K₀ t) with hsdef
  obtain ⟨hadjn, hsfix, hnbrs, hcong, hne⟩ :=
    CerednikDrinfeld.BruhatTits.adj_stdVertex_iff_eq_smul_of_uniformizer R K₀ ϖ hϖ n rfl s (fun t => rfl)
  have hn : ∀ z : ↥(upperHalfPlane K₀ K),
      ((Matrix.ProjGenLinGroup.mk n • z : ↥(upperHalfPlane K₀ K)) : K) = (z : K) * (algebraMap K₀ K ϖ₁.ϖ)⁻¹ := fun z => by
    rw [coe_mk_smul, hndef, pmoebius_nMat K₀ _ hϖ0 z.2, hϖ₁]

  choose cF mF hmF using fun t : K₀ => exists_law_sub ϖ₁ hrk hunif F hF t
  obtain ⟨cInf, mInf, hInf⟩ := exists_law_inv ϖ₁ hrk hunif F hF
  obtain ⟨hsumF, c₀, hstarF⟩ := CerednikDrinfeld.Omega.sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow K₀ K ϖ₁ hrk
    hunif T hT hTcov hTsep F hF mF mInf (fun t _ => ⟨cF t, hmF t⟩) ⟨cInf, hInf⟩
  have hfibre : ∀ (u : K) (hu : u ∈ affinoid ϖ₁ 0), Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨u, hΩ hu⟩) = c₀ :=
    fun u hu => v_apply_eq_const_of_star ϖ₁ T hT F mF c₀ hstarF u hu
  have key_n : ∀ (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
      Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) (Matrix.ProjGenLinGroup.mk n • ⟨w, hΩ hw⟩)) =
        Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w', hΩ hw'⟩) *
          Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ mInf := by
    intro w w' hw hw'
    have h := edge_step ϖ₁ hrk hunif T hT hTcov hTsep F hF mF c₀ hstarF n hn w w' hw hw'
    rw [hpϖ] at h
    rw [h, show mInf = -(∑ t ∈ T, mF t) by omega]

  have key_s : ∀ (τ : R) (w w' : K) (hw : w ∈ affinoid ϖ₁ 0) (hw' : w' ∈ affinoid ϖ₁ 0),
      Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) (Matrix.ProjGenLinGroup.mk (s τ * n) • ⟨w, hΩ hw⟩)) =
        Valued.v ((F : ↥(upperHalfPlane K₀ K) → K) ⟨w', hΩ hw'⟩) *
          Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ mF (algebraMap R K₀ τ) := by
    intro τ w w' hw hw'
    set Pτ : PGL(2, K₀) := Matrix.ProjGenLinGroup.mk (s τ) with hPτ
    set Fτ : ↥(holRing ϖ₁) := Pτ⁻¹ • F with hFτdef
    have hFτ : IsUnit Fτ := isUnit_smul ϖ₁ Pτ⁻¹ hF
    have hFτ_apply : ∀ z : ↥(upperHalfPlane K₀ K),
        (Fτ : ↥(upperHalfPlane K₀ K) → K) z = (F : ↥(upperHalfPlane K₀ K) → K) (Pτ • z) := fun z => inv_smul_apply ϖ₁ Pτ F z

    choose cτ mτ hmτ using fun t : K₀ => exists_law_sub ϖ₁ hrk hunif Fτ hFτ t
    have hInfτ : ∃ c : Γ₀, ∀ z : ↥(upperHalfPlane K₀ K),
        Valued.v (algebraMap K₀ K ϖ₁.ϖ) < (Valued.v (z : K))⁻¹ → (Valued.v (z : K))⁻¹ < 1 →
          Valued.v ((Fτ : ↥(upperHalfPlane K₀ K) → K) z) = c * (Valued.v (z : K))⁻¹ ^ mF (algebraMap R K₀ τ) := by
      refine ⟨cF (algebraMap R K₀ τ), fun z h1 h2 => ?_⟩
      rw [hFτ_apply]
      have hval : ((Pτ • z : ↥(upperHalfPlane K₀ K)) : K) = algebraMap K₀ K (algebraMap R K₀ τ) + (z : K)⁻¹ := by
        rw [hPτ, coe_mk_smul, hsdef]; exact pmoebius_sMat K₀ _ z.2
      have hsub : ((Pτ • z : ↥(upperHalfPlane K₀ K)) : K) - algebraMap K₀ K (algebraMap R K₀ τ) = (z : K)⁻¹ := by
        rw [hval, add_sub_cancel_left]
      have h := hmF (algebraMap R K₀ τ) (Pτ • z)
      rw [hsub, map_inv₀] at h
      exact h h1 h2
    obtain ⟨hsumτ, c₀τ, hstarτ⟩ := CerednikDrinfeld.Omega.sum_add_eq_zero_of_isUnit_of_forall_v_apply_eq_mul_zpow K₀ K ϖ₁
      hrk hunif T hT hTcov hTsep Fτ hFτ mτ (mF (algebraMap R K₀ τ)) (fun t _ => ⟨cτ t, hmτ t⟩) hInfτ
    have h := edge_step ϖ₁ hrk hunif T hT hTcov hTsep Fτ hFτ mτ c₀τ hstarτ n hn w w' hw hw'
    rw [hpϖ, show -(∑ t ∈ T, mτ t) = mF (algebraMap R K₀ τ) by omega, hFτ_apply, hFτ_apply, ← mul_smul, hPτ,
      ← map_mul] at h

    have hu' : pmoebius K₀ (Matrix.ProjGenLinGroup.mk (s τ)) w' ∈ affinoid ϖ₁ 0 :=
      CerednikDrinfeld.Omega.pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq R K₀ K hint hv ϖ₁ (s τ) (hsfix τ) hw'
    have hpt : (Matrix.ProjGenLinGroup.mk (s τ) • (⟨w', hΩ hw'⟩ : ↥(upperHalfPlane K₀ K)) : ↥(upperHalfPlane K₀ K)) =
        ⟨_, hΩ hu'⟩ := Subtype.ext rfl
    rw [hpt, hfibre _ hu', ← hfibre w' hw'] at h
    exact h

  set v₀ := LT.LatticeTree.stdVertex R K₀ with hv₀
  let dir : R ⧸ Ideal.span {ϖ} → LT.LatticeTree.Vertex R K₀ := fun x => (s (Quotient.out x) * n) • v₀
  have hdir_inj : Function.Injective dir := by
    intro x y h
    have hd : ϖ ∣ Quotient.out x - Quotient.out y := (hcong _ _).1 h
    rw [← Ideal.Quotient.mk_out x, ← Ideal.Quotient.mk_out y]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hd)
  have hdir_ne : ∀ x, dir x ≠ n • v₀ := fun x h => hne _ h.symm
  have hdir_mk : ∀ t : R, (s t * n) • v₀ = dir (Ideal.Quotient.mk (Ideal.span {ϖ}) t) := fun t =>
    (hcong _ _).2 (dvd_sub_out_mk ϖ t)
  have hdir_adj : ∀ x, (BruhatTits.tree R K₀).Adj v₀ (dir x) := fun x => by
    have h := Mumford.GraphAction.smul_adj (𝒯 := BruhatTits.tree R K₀) (s (Quotient.out x)) hadjn
    rwa [hsfix, ← mul_smul] at h
  let mV : LT.LatticeTree.Vertex R K₀ → ℤ := fun y =>
    if y = n • v₀ then mInf else if h : ∃ x, dir x = y then mF (algebraMap R K₀ (Quotient.out h.choose)) else 0
  have hmV_n : mV (n • v₀) = mInf := by simp only [mV, if_pos rfl]
  have hmV_dir : ∀ x, mV (dir x) = mF (algebraMap R K₀ (Quotient.out x)) := by
    intro x
    have hex : ∃ x', dir x' = dir x := ⟨x, rfl⟩
    simp only [mV, if_neg (hdir_ne x), dif_pos hex]
    rw [hdir_inj hex.choose_spec]
  refine ⟨mV, fun S hS => ?_, fun y hy g hg w w' hw hw' => ?_⟩
  ·
    have hSeq : S = insert (n • v₀) (Finset.univ.image dir) := by
      ext y
      rw [hS y, Finset.mem_insert, Finset.mem_image]
      constructor
      · intro hadj
        rcases hnbrs y hadj with h | ⟨t, rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨_, Finset.mem_univ _, (hdir_mk t).symm⟩
      · rintro (rfl | ⟨x, -, rfl⟩)
        · exact hadjn
        · exact hdir_adj x
    have hnot : n • v₀ ∉ Finset.univ.image dir := by
      rw [Finset.mem_image]
      rintro ⟨x, -, hx⟩
      exact hdir_ne x hx
    rw [hSeq, Finset.sum_insert hnot, Finset.sum_image fun x _ y _ h => hdir_inj h, hmV_n]
    simp only [hmV_dir]
    rw [← sum_repFinset ϖ mF, ← hTdef]
    omega
  ·
    have hy' := hnbrs y hy

    have reduce : ∀ g₁ : GL (Fin 2) K₀, g₁ • v₀ = y →
        ∃ (u : K) (hu : u ∈ affinoid ϖ₁ 0),
          (Matrix.ProjGenLinGroup.mk g • (⟨w, hΩ hw⟩ : ↥(upperHalfPlane K₀ K)) : ↥(upperHalfPlane K₀ K)) =
            Matrix.ProjGenLinGroup.mk g₁ • ⟨u, hΩ hu⟩ := by
      intro g₁ hg₁
      have hh : (g₁⁻¹ * g) • v₀ = v₀ := by rw [mul_smul, hg, ← hg₁, inv_smul_smul]
      have hu := CerednikDrinfeld.Omega.pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq R K₀ K hint hv ϖ₁ (g₁⁻¹ * g) hh hw
      refine ⟨_, hu, ?_⟩
      rw [show Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk g₁ * Matrix.ProjGenLinGroup.mk (g₁⁻¹ * g) by
        rw [← map_mul, mul_inv_cancel_left], mul_smul]
      rfl
    rcases hy' with rfl | ⟨t, rfl⟩
    · obtain ⟨u, hu, hgu⟩ := reduce n rfl
      rw [hgu, key_n u w' hu hw', hmV_n]
    ·
      obtain ⟨u, hu, hgu⟩ := reduce (s (Quotient.out (Ideal.Quotient.mk (Ideal.span {ϖ}) t)) * n) (hdir_mk t).symm
      rw [hgu, key_s _ u w' hu hw', hdir_mk t, hmV_dir]

end
end S_CerednikDrinfeld_Omega_exists_int_neighbours_sum_eq_zero_v_apply_smul_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_int_neighbours_sum_eq_zero_v_apply_smul_eq (solution)
