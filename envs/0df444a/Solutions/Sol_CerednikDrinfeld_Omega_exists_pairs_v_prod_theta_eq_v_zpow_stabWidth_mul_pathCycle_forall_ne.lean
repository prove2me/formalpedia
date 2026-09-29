-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/471d771e-0abc-5470-af28-dedb469f48f5

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_OmegaTubes
import Mathlib
import Theorems.Thm_CerednikDrinfeld_Omega_exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube
import Theorems.Thm_CerednikDrinfeld_Omega_v_apply_eq_and_v_apply_eq_mul_zpow_of_isUnit_of_forall_mem_stdEdgeTube
import Theorems.Thm_CerednikDrinfeld_Omega_v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta
import Theorems.Thm_CerednikDrinfeld_Omega_theta_mul_theta_basePoint
import Theorems.Thm_CerednikDrinfeld_Omega_exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted
import Theorems.Thm_CerednikDrinfeld_Omega_pmoebius_mem_affinoid_zero_of_smul_stdVertex_eq
import Theorems.Thm_CerednikDrinfeld_Omega_holRing_eq_and_affinoid_zero_eq

import Theorems.Thm_CerednikDrinfeld_Omega_affinoid_nonempty_of_exists_finset_cover
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_BruhatTits_exists_smul_stdVertex_eq_fst_and_mul_smul_stdVertex_eq_snd
import Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint
import Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_mul_theta_eq_theta
import Theorems.Thm_CerednikDrinfeld_Omega_theta_self_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq CerednikDrinfeld.Mumford.walkOverlap_nil_right CerednikDrinfeld.Mumford.walkOverlap_nil_left LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega CerednikDrinfeld.Mumford"

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

theorem v_sub_eq_one_of_mem_affinoid_zero (ϖ₁ : PseudoUniformizer K₀ K) {u : K} (hu : u ∈ affinoid ϖ₁ 0)
    (t : K₀) (ht : Valued.v (algebraMap K₀ K t) ≤ 1) : Valued.v (u - algebraMap K₀ K t) = 1 := by
  rw [mem_affinoid_iff'] at hu
  refine le_antisymm ?_ (by simpa using hu.2 t)
  refine (Valuation.map_sub _ _ _).trans (max_le (by simpa using hu.1) ht)

theorem v_le_one_of_mem_affinoid_zero (ϖ₁ : PseudoUniformizer K₀ K) {u : K} (hu : u ∈ affinoid ϖ₁ 0) : Valued.v u ≤ 1 := by
  rw [mem_affinoid_iff'] at hu; simpa using hu.1

end Analytic

end HarmV0

namespace TRV

theorem exists_v_translate_eq_mul_zpow
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (P : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hunif : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K P.ϖ) ∨ 1 ≤ Valued.v (algebraMap K₀ K a))
    (U : ↥(holRing P)) (hU : IsUnit U) (g : PGL(2, K₀)) :
    ∃ (c : Γ₀) (m : ℤ), c ≠ 0 ∧ ∀ (ζ : K) (hζ : ζ ∈ stdEdgeTube P),
      Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) (g • ⟨ζ, hζ.1⟩)) = c * Valued.v ζ ^ m := by

  have hV : IsUnit (g⁻¹ • U : ↥(holRing P)) := by
    obtain ⟨W, hW⟩ := hU.exists_right_inv
    refine IsUnit.of_mul_eq_one (b := g⁻¹ • W) ?_
    rw [← smul_mul', hW, smul_one]
  obtain ⟨c, m, hcm⟩ := CerednikDrinfeld.Omega.exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube K₀ K P hrk hunif
    (g⁻¹ • U) hV
  have hval : ∀ (ζ : K) (hζ : ζ ∈ stdEdgeTube P),
      Valued.v ((U : ↥(upperHalfPlane K₀ K) → K) (g • ⟨ζ, hζ.1⟩)) = c * Valued.v ζ ^ m := by
    intro ζ hζ
    have := hcm ζ hζ
    rw [coe_smul_holRing_apply, inv_inv] at this
    exact this
  refine ⟨c, m, ?_, hval⟩

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (algebraMap K₀ K P.ϖ)
  have hvs2 : Valued.v s * Valued.v s = Valued.v (algebraMap K₀ K P.ϖ) := by rw [← map_mul, ← hs]
  have hp0 : 0 < Valued.v (algebraMap K₀ K P.ϖ) := P.pos
  have hp1 : Valued.v (algebraMap K₀ K P.ϖ) < 1 := P.lt_one
  have hs1 : Valued.v s < 1 := by
    by_contra h; rw [not_lt] at h
    have : (1 : Γ₀) ≤ Valued.v s * Valued.v s := one_le_mul h h
    rw [hvs2] at this; exact absurd hp1 (not_lt.mpr this)
  have hs0 : Valued.v (algebraMap K₀ K P.ϖ) < Valued.v s := by
    by_contra h; rw [not_lt] at h
    have h2 : Valued.v s * Valued.v s ≤ Valued.v s * 1 := mul_le_mul' le_rfl hs1.le
    rw [hvs2, mul_one] at h2
    have := le_antisymm h2 h
    rw [this] at hvs2
    have hs' : Valued.v s ≠ 0 := by rw [← this]; exact hp0.ne'
    have : Valued.v s = 1 := by
      have := hvs2; rwa [mul_eq_left₀ hs'] at this
    exact absurd hs1 (by rw [this]; exact lt_irrefl 1)
  have hsT : s ∈ stdEdgeTube P := by
    refine ⟨?_, hs0, hs1⟩
    rw [mem_upperHalfPlane_iff]
    rintro a rfl
    rcases hunif a with h | h
    · exact absurd hs0 (not_lt.mpr h)
    · exact absurd hs1 (not_lt.mpr h)
  intro hc
  have h0 := hval s hsT
  rw [hc, zero_mul, Valuation.zero_iff] at h0
  obtain ⟨W, hW⟩ := hU.exists_right_inv
  have := congrArg (fun u : ↥(holRing P) => (u : ↥(upperHalfPlane K₀ K) → K) (g • ⟨s, hsT.1⟩)) hW
  simp only [Subring.coe_mul, Subring.coe_one, Pi.mul_apply, Pi.one_apply] at this
  rw [h0, zero_mul] at this
  exact zero_ne_one this

end TRV

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Mumford.ActsThrough Mumford.pathCycle Mumford.GraphAction Mumford.QuotEdge Mumford.QuotVert Mumford.stabWidth tree BruhatTits.tree Omega.exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube Omega.v_apply_eq_and_v_apply_eq_mul_zpow_of_isUnit_of_forall_mem_stdEdgeTube Omega.v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta Omega.theta_mul_theta_basePoint Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul Omega.isDiscrete_of_finite_stabilizer_stdVertex Omega.holRing_eq_and_affinoid_zero_eq Omega.affinoid_nonempty_of_exists_finset_cover BruhatTits.exists_smul_stdVertex_eq_fst_and_mul_smul_stdVertex_eq_snd Omega.theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint Omega.theta_pmoebius_mul_theta_eq_theta Omega.theta_self_eq_one"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid affinoid_subset_upperHalfPlane affinoid_mono mem_affinoid_iff' IsExhausted holRing exists_mapsTo_affinoid coe_smul_holRing_apply moebius pmoebius pmoebius_mk upperHalfPlane mem_upperHalfPlane_iff moebius_denom_ne_zero_of_mem pmoebius_mem_upperHalfPlane pmoebius_one pmoebius_mul theta ThetaMultipliable IsDiscrete stdEdgeTube exists_v_apply_eq_mul_zpow_of_isUnit_of_mem_stdEdgeTube v_apply_eq_and_v_apply_eq_mul_zpow_of_isUnit_of_forall_mem_stdEdgeTube v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta theta_mul_theta_basePoint exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul isDiscrete_of_finite_stabilizer_stdVertex thetaMultipliable_of_isDiscrete_of_isExhausted holRing_eq_and_affinoid_zero_eq affinoid_nonempty_of_exists_finset_cover finite_setOf_pmoebius_mem_affinoid theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint theta_pmoebius_mul_theta_eq_theta theta_self_eq_one"
namespace GlobalCurrent
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

section PUTree

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀] {ϖ : R}
  {K : Type} [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_algebraMap_units_eq_one
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (u : Rˣ) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) = 1 := by
  apply le_antisymm (hint u)
  have h1 : algebraMap K₀ K (algebraMap R K₀ (u : R)) * algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  calc (1 : Γ₀) = Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) *
        Valued.v (algebraMap K₀ K (algebraMap R K₀ (↑u⁻¹ : R))) := by rw [← Valuation.map_mul, h1, Valuation.map_one]
    _ ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ (u : R))) * 1 := mul_le_mul_right (hint _) _
    _ = _ := mul_one _

theorem algebraMap_ne_zero_of_irreducible (hϖ : Irreducible ϖ) : algebraMap R K₀ ϖ ≠ 0 := fun h =>
  hϖ.ne_zero ((IsFractionRing.to_map_eq_zero_iff (K := K₀)).mp h)

theorem v_algebraMap_pos (hϖ : Irreducible ϖ) : 0 < Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) :=
  lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff _).mpr
    ((map_ne_zero _).mpr (algebraMap_ne_zero_of_irreducible hϖ))))

theorem v_algebraMap_lt_one (hϖ : Irreducible ϖ)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) < 1 := by
  by_contra h
  rw [not_lt] at h
  have hϖ0 := algebraMap_ne_zero_of_irreducible (K₀ := K₀) hϖ
  have hle : Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)⁻¹) ≤ 1 := by
    rw [map_inv₀, Valuation.map_inv, inv_le_one₀ (v_algebraMap_pos hϖ)]
    exact h
  obtain ⟨b, hb⟩ := hv _ hle
  apply hϖ.not_isUnit
  refine isUnit_iff_exists_inv.mpr ⟨b, ?_⟩
  apply IsFractionRing.injective R K₀
  rw [map_mul, hb, map_one, mul_inv_cancel₀ hϖ0]

theorem exists_v_algebraMap_eq_zpow (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1) (a : K₀) (ha : a ≠ 0) :
    ∃ k : ℤ, Valued.v (algebraMap K₀ K a) = Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k := by
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ ha
  refine ⟨k, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, Valuation.map_mul, map_zpow₀,
    v_algebraMap_units_eq_one hint, one_mul]

theorem v_algebraMap_le_or_one_le (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (a : K₀) :
    Valued.v (algebraMap K₀ K a) ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ∨
      1 ≤ Valued.v (algebraMap K₀ K a) := by
  by_cases ha : a = 0
  · left; rw [ha, map_zero, Valuation.map_zero]; exact zero_le'
  obtain ⟨k, hk⟩ := exists_v_algebraMap_eq_zpow hϖ hint a ha
  rw [hk]
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have h1 := (v_algebraMap_lt_one hϖ hv).le
  rcases le_or_gt k 0 with hk0 | hk0
  · exact Or.inr (one_le_zpow_of_nonpos₀ h0 h1 hk0)
  · left
    calc Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ k
        ≤ Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ h0 h1 (by omega)
      _ = _ := zpow_one _

theorem exists_pow_le_v_algebraMap_le (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) (a : K₀) (ha : a ≠ 0) :
    ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ Valued.v (algebraMap K₀ K a) ∧
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)))⁻¹ ^ N := by
  obtain ⟨k, hk⟩ := exists_v_algebraMap_eq_zpow hϖ hint a ha
  have h0 := v_algebraMap_pos (K₀ := K₀) (K := K) hϖ
  have h1 := (v_algebraMap_lt_one hϖ hv).le
  refine ⟨k.natAbs, ?_, ?_⟩
  · rw [hk, ← zpow_natCast]
    exact zpow_le_zpow_right_of_le_one₀ h0 h1 (Int.le_natAbs)
  · rw [hk, inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right_of_le_one₀ h0 h1 (by rw [Int.natCast_natAbs]; exact neg_abs_le k)

def treePseudoUniformizer (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    PseudoUniformizer K₀ K where
  ϖ := algebraMap R K₀ ϖ
  pos := v_algebraMap_pos hϖ
  lt_one := v_algebraMap_lt_one hϖ hv
  scale := exists_pow_le_v_algebraMap_le hϖ hint hv

@[scoped simp] theorem treePseudoUniformizer_ϖ (hϖ : Irreducible ϖ)
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a) :
    (treePseudoUniformizer hϖ hint hv).ϖ = algebraMap R K₀ ϖ := rfl

end PUTree

end CerednikDrinfeld.Omega.GlobalCurrent
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega.GlobalCurrent"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega"
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld"

namespace EPVgen

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
  {G : Type} [Group G]

theorem finite_setOf_mem_affinoid_and_exists_pmoebius_eq
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (g : PGL(2, K₀)) (n : ℕ) {y : K} (hy : y ∈ upperHalfPlane K₀ K) :
    {ζ : K | ζ ∈ affinoid ϖ n ∧ ∃ γ : G, pmoebius K₀ (ρ γ) y = pmoebius K₀ g ζ}.Finite := by
  obtain ⟨m, hm⟩ := exists_mapsTo_affinoid ϖ g n
  obtain ⟨m', hm'⟩ := hex y hy
  set N := max m m' with hN
  have hyN : y ∈ affinoid ϖ N := affinoid_mono ϖ (le_max_right _ _) hm'
  have hfin := finite_setOf_pmoebius_mem_affinoid ϖ ρ hρ N hyN
  refine (hfin.image fun γ => pmoebius K₀ g⁻¹ (pmoebius K₀ (ρ γ) y)).subset ?_
  rintro ζ ⟨hζ, γ, hγ⟩
  have hζΩ : ζ ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ n hζ
  refine ⟨γ, ?_, ?_⟩
  · show pmoebius K₀ (ρ γ) y ∈ affinoid ϖ N
    rw [hγ]; exact affinoid_mono ϖ (le_max_left _ _) (hm hζ)
  · show pmoebius K₀ g⁻¹ (pmoebius K₀ (ρ γ) y) = ζ
    rw [hγ, ← pmoebius_mul K₀ hζΩ, inv_mul_cancel, pmoebius_one]

theorem exists_mem_ball_forall_ne
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (g : PGL(2, K₀)) (n : ℕ) {x₀ c : K} (hc : c ≠ 0)
    (hball : ∀ ζ : K, Valued.v (ζ - x₀) < Valued.v c → ζ ∈ affinoid ϖ n)
    (Y : Finset K) (hY : ∀ y ∈ Y, y ∈ upperHalfPlane K₀ K) (B : Finset K) :
    ∃ ζ : K, Valued.v (ζ - x₀) < Valued.v c ∧ ζ ∉ B ∧
      ∀ y ∈ Y, ∀ γ : G, pmoebius K₀ (ρ γ) y ≠ pmoebius K₀ g ζ := by
  classical

  have hbad : {ζ : K | ζ ∈ affinoid ϖ n ∧ ∃ y ∈ Y, ∃ γ : G, pmoebius K₀ (ρ γ) y = pmoebius K₀ g ζ}.Finite := by
    refine (Set.Finite.biUnion (Finset.finite_toSet Y) fun y hy =>
      finite_setOf_mem_affinoid_and_exists_pmoebius_eq ϖ hex ρ hρ g n (hY y hy)).subset ?_
    rintro ζ ⟨hζ, y, hy, γ, hγ⟩
    exact Set.mem_biUnion hy ⟨hζ, γ, hγ⟩

  have hp0 : algebraMap K₀ K ϖ.ϖ ≠ 0 := (Valuation.ne_zero_iff _).1 ϖ.pos.ne'
  have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) < 1 := ϖ.lt_one
  let s : ℕ → K := fun k => x₀ + c * algebraMap K₀ K ϖ.ϖ ^ (k + 1)
  have hs_inj : Function.Injective s := by
    intro i j hij
    have h1 := mul_left_cancel₀ hc (add_left_cancel hij)
    have h2 : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (i + 1) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (j + 1) := by
      have := congrArg (Valued.v (R := K) (Γ₀ := Γ₀)) h1
      simpa only [Valuation.map_pow] using this
    exact Nat.succ_injective (pow_right_injective₀ ϖ.pos hp1.ne h2)
  have hs_ball : ∀ k, Valued.v (s k - x₀) < Valued.v c := fun k => by
    show Valued.v (x₀ + c * algebraMap K₀ K ϖ.ϖ ^ (k + 1) - x₀) < Valued.v c
    rw [add_sub_cancel_left, map_mul, map_pow]
    exact mul_lt_of_lt_one_right ((Valuation.pos_iff _).2 hc) (pow_lt_one₀ zero_le' hp1 (Nat.succ_ne_zero k))
  have hinf : {ζ : K | Valued.v (ζ - x₀) < Valued.v c}.Infinite :=
    Set.infinite_of_injective_forall_mem hs_inj hs_ball
  obtain ⟨ζ, hζ, hζnot⟩ := (hinf.diff (hbad.union (Finset.finite_toSet B))).nonempty
  refine ⟨ζ, hζ, fun hB => hζnot (Or.inr hB), fun y hy γ hγ => hζnot (Or.inl ⟨hball ζ hζ, y, hy, γ, hγ⟩)⟩

end EPVgen
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega.GlobalCurrent"

namespace PLaux

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_eq_one_of_mem_affinoid_zero (ϖ₁ : PseudoUniformizer K₀ K) {w : K} (hw : w ∈ affinoid ϖ₁ 0) : Valued.v w = 1 := by
  rw [mem_affinoid_iff'] at hw
  simp only [pow_zero] at hw
  exact le_antisymm hw.1 (by simpa using hw.2 0)

theorem inv_mem_affinoid_zero (ϖ₁ : PseudoUniformizer K₀ K) {w : K} (hw : w ∈ affinoid ϖ₁ 0) : w⁻¹ ∈ affinoid ϖ₁ 0 := by
  have hw0 : Valued.v w = 1 := v_eq_one_of_mem_affinoid_zero ϖ₁ hw
  rw [mem_affinoid_iff'] at hw ⊢
  simp only [pow_zero] at hw ⊢
  obtain ⟨hw1, hw2⟩ := hw
  have hwne : w ≠ 0 := fun h => by rw [h, map_zero] at hw0; exact zero_ne_one hw0
  refine ⟨by rw [map_inv₀, hw0, inv_one], fun a => ?_⟩
  by_cases ha : Valued.v (algebraMap K₀ K a) < 1
  · have : Valued.v (algebraMap K₀ K a) < Valued.v w⁻¹ := by rw [map_inv₀, hw0, inv_one]; exact ha
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg]; exact this),
      map_inv₀, hw0, inv_one]
  · rw [not_lt] at ha
    have ha0 : algebraMap K₀ K a ≠ 0 := fun h => by rw [h, map_zero] at ha; exact absurd ha (not_le.mpr zero_lt_one)
    have e : w⁻¹ - algebraMap K₀ K a = -(algebraMap K₀ K a * w⁻¹) * (w - algebraMap K₀ K a⁻¹) := by
      rw [map_inv₀]; field_simp; ring
    rw [e, map_mul, Valuation.map_neg, map_mul, map_inv₀, hw0, inv_one, mul_one]
    exact one_le_mul ha (hw2 a⁻¹)

theorem add_mem_affinoid_zero (ϖ₁ : PseudoUniformizer K₀ K) {w : K} (hw : w ∈ affinoid ϖ₁ 0)
    (t : K₀) (ht : Valued.v (algebraMap K₀ K t) ≤ 1) : w + algebraMap K₀ K t ∈ affinoid ϖ₁ 0 := by
  rw [mem_affinoid_iff'] at hw ⊢
  simp only [pow_zero] at hw ⊢
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨(Valuation.map_add _ _ _).trans (max_le hw1 ht), fun a => ?_⟩
  have e : w + algebraMap K₀ K t - algebraMap K₀ K a = w - algebraMap K₀ K (a - t) := by rw [map_sub]; ring
  rw [e]; exact hw2 (a - t)

theorem smul_mem_upperHalfPlane {z : K} (hz : z ∈ upperHalfPlane K₀ K) (c : K₀) (hc : c ≠ 0) :
    algebraMap K₀ K c * z ∈ upperHalfPlane K₀ K := by
  rw [mem_upperHalfPlane_iff] at hz ⊢
  intro a ha
  apply hz (a / c)
  rw [map_div₀, ha, mul_div_cancel_left₀ _ ((map_ne_zero _).mpr hc)]

theorem ball_subset_affinoid (ϖ₁ : PseudoUniformizer K₀ K) (n : ℕ) {z₁ : K} (hz₁ : z₁ ∈ affinoid ϖ₁ n) :
    ∀ ζ : K, Valued.v (ζ - z₁) < Valued.v (algebraMap K₀ K (ϖ₁.ϖ ^ n)) → ζ ∈ affinoid ϖ₁ n := by
  intro ζ hζ
  rw [map_pow, map_pow] at hζ
  obtain ⟨h1, h2⟩ := (mem_affinoid_iff' ϖ₁ n z₁).1 hz₁
  rw [mem_affinoid_iff']
  have hp1 : Valued.v (algebraMap K₀ K ϖ₁.ϖ) ≤ 1 := ϖ₁.lt_one.le
  have hle : Valued.v (algebraMap K₀ K ϖ₁.ϖ) ^ n ≤ (Valued.v (algebraMap K₀ K ϖ₁.ϖ))⁻¹ ^ n :=
    (pow_le_one₀ zero_le' hp1).trans (one_le_pow₀ ((one_le_inv₀ ϖ₁.pos).2 hp1))
  refine ⟨?_, fun a => ?_⟩
  · have e : ζ = (ζ - z₁) + z₁ := by ring
    rw [e]; exact (Valuation.map_add _ _ _).trans (max_le (hζ.le.trans hle) h1)
  · have e : ζ - algebraMap K₀ K a = (z₁ - algebraMap K₀ K a) + (ζ - z₁) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ (hζ.trans_le (h2 a))]; exact h2 a

end PLaux
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega.GlobalCurrent"

open HarmV0 in
theorem PAIRLAW.v_theta_pair
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁) [IsDomain ↥(holRing ϖ₁)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)
    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    (htame : ∀ w : LT.LatticeTree.Vertex R K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer G w) : ℕ) : K) = 1)
    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    [DecidableEq (LT.LatticeTree.Vertex R K₀)]
    (hϖ0 : algebraMap R K₀ ϖ ≠ 0) (g : GL (Fin 2) K₀) (t : R)
    (p₁ : (BruhatTits.tree R K₀).Walk (g • LT.LatticeTree.stdVertex R K₀)
            ((g * sMat (algebraMap R K₀ t) * nMat (algebraMap R K₀ ϖ) hϖ0) • LT.LatticeTree.stdVertex R K₀))
    {z₁ : K} (hz₁ : z₁ ∈ upperHalfPlane K₀ K) (β : G) :
    ∃ m : ℤ,
      Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ m =
        Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^
          (-(∑ e : E, ((stabWidth G (BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
              pathCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) (LT.LatticeTree.stdVertex R K₀) β e *
              walkCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) p₁ e)) ∧
      ∀ (ζ ζ' : K), ζ ∈ upperHalfPlane K₀ K → ζ' ∈ upperHalfPlane K₀ K →
        Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) < Valued.v ζ → Valued.v ζ < 1 →
        Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) < Valued.v ζ' → Valued.v ζ' < 1 →
        (∀ γ : G, pmoebius K₀ (ρ γ) z₁ ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t))) ζ) →
        (∀ γ : G, pmoebius K₀ (ρ γ) z₁ ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t))) ζ') →
        Valued.v (theta ρ z₁ (pmoebius K₀ (ρ β) z₁)
            (pmoebius K₀ (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t))) ζ)
            (pmoebius K₀ (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t))) ζ')) * Valued.v ζ ^ m =
          Valued.v ζ' ^ m := by
  classical
  haveI : Fintype (R ⧸ Ideal.span {ϖ}) := Fintype.ofFinite _

  set qK : K := algebraMap K₀ K (algebraMap R K₀ ϖ) with hqK
  set q : Γ₀ := Valued.v qK with hqdef
  have hq0 : 0 < q := CerednikDrinfeld.Omega.GlobalCurrent.v_algebraMap_pos hϖ
  have hq1 : q < 1 := CerednikDrinfeld.Omega.GlobalCurrent.v_algebraMap_lt_one hϖ hv
  have hqne : q ≠ 0 := hq0.ne'
  have hqK0 : qK ≠ 0 := (Valuation.pos_iff _).mp hq0
  have ht'1 : Valued.v (algebraMap K₀ K (algebraMap R K₀ t)) ≤ 1 := hint t
  have hΩ0 : ∀ {u : K}, u ∈ affinoid ϖ₁ 0 → u ∈ upperHalfPlane K₀ K := fun hu => affinoid_subset_upperHalfPlane ϖ₁ 0 hu
  have hρmul : ∀ (γ δ : G) (z : K), z ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ (γ * δ)) z = pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ δ) z) := by
    intro γ δ z hz; rw [map_mul, pmoebius_mul K₀ hz]

  have hdisc : IsDiscrete K ρ := by
    refine CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex R K₀ ϖ hϖ K hint hv hq ρ ?_
    have hset : {γ : G | ρ γ • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀} =
        ((MulAction.stabilizer G (LT.LatticeTree.stdVertex R K₀) : Subgroup G) : Set G) := by
      ext γ
      simp only [Set.mem_setOf_eq, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      rw [← hρ γ (LT.LatticeTree.stdVertex R K₀)]
    rw [hset]
    haveI := hfin (LT.LatticeTree.stdVertex R K₀)
    exact Set.toFinite _

  set P : PseudoUniformizer K₀ K := CerednikDrinfeld.Omega.GlobalCurrent.treePseudoUniformizer (K := K) hϖ hint hv with hPdef
  have hP : P.ϖ = algebraMap R K₀ ϖ := rfl
  obtain ⟨hhol, haff⟩ := CerednikDrinfeld.Omega.holRing_eq_and_affinoid_zero_eq ϖ₁ P
  have hunifP := hunif_of_frame (K := K) hϖ hint P hP

  obtain ⟨n₁, hn₁⟩ := hex z₁ hz₁
  obtain ⟨a₀, ha₀ball, -, ha₀Y⟩ := EPVgen.exists_mem_ball_forall_ne ϖ₁ hex ρ hdisc (1 : PGL(2, K₀)) n₁
    (x₀ := z₁) (c := algebraMap K₀ K (ϖ₁.ϖ ^ n₁))
    (by rw [map_pow]; exact pow_ne_zero _ ((map_ne_zero _).mpr (fun h0 => by have := ϖ₁.pos; rw [h0, map_zero, map_zero] at this; exact lt_irrefl _ this)))
    (PLaux.ball_subset_affinoid ϖ₁ n₁ hn₁) ({z₁} : Finset K) (by intro y hy; rw [Finset.mem_singleton] at hy; rw [hy]; exact hz₁) ∅
  simp only [pmoebius_one, Finset.mem_singleton, forall_eq] at ha₀Y
  have ha₀ : a₀ ∈ upperHalfPlane K₀ K :=
    affinoid_subset_upperHalfPlane ϖ₁ n₁ (PLaux.ball_subset_affinoid ϖ₁ n₁ hn₁ a₀ ha₀ball)
  have hz₁a₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₁ ≠ a₀ := ha₀Y

  obtain ⟨U, hU, -, hUθ, -⟩ := CerednikDrinfeld.Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
    K₀ K ϖ₁ hex ρ hdisc hz₁ ha₀ hz₁a₀ β

  let UP : ↥(holRing P) := ⟨(U : ↥(upperHalfPlane K₀ K) → K), hhol ▸ U.2⟩
  have hUP : IsUnit UP := by
    obtain ⟨V, hUV⟩ := hU.exists_right_inv
    refine isUnit_iff_exists_inv.mpr ⟨⟨(V : ↥(upperHalfPlane K₀ K) → K), hhol ▸ V.2⟩, ?_⟩
    have h1 := congrArg Subtype.val hUV
    exact Subtype.ext h1
  obtain ⟨c, m, hc0, hlaw⟩ := TRV.exists_v_translate_eq_mul_zpow K₀ K P hrk hunifP UP hUP (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t)))

  set f : ↥(holRing P) := (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t)))⁻¹ • UP with hf
  have hfU : IsUnit f := isUnit_smul P _ hUP
  have hcm : ∀ (z : K) (hz : z ∈ stdEdgeTube P), Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) ⟨z, hz.1⟩) = c * Valued.v z ^ m := by
    intro z hz
    rw [hf, inv_smul_apply]
    exact hlaw z hz
  obtain ⟨hfib0, hfib1⟩ := CerednikDrinfeld.Omega.v_apply_eq_and_v_apply_eq_mul_zpow_of_isUnit_of_forall_mem_stdEdgeTube
    P hrk hunifP (repFinset R K₀ ϖ) (repFinset_le_one hint ϖ) (repFinset_cov hϖ hint hv P) (repFinset_sep hϖ hint)
    f hfU c m hcm

  obtain ⟨w₀, hw₀⟩ : (affinoid ϖ₁ 0).Nonempty := by
    refine CerednikDrinfeld.Omega.affinoid_nonempty_of_exists_finset_cover K₀ K ϖ₁ 0 ⟨repFinset R K₀ ϖ, fun a ha => ?_⟩
    rw [pow_zero] at ha ⊢
    exact repFinset_cov hϖ hint hv ϖ₁ a ha
  have hw₀P : w₀ ∈ affinoid P 0 := haff ▸ hw₀
  have hw₀Ω : w₀ ∈ upperHalfPlane K₀ K := hΩ0 hw₀
  have hw₀ne : w₀ ≠ 0 := ne_zero_of_mem K₀ hw₀Ω

  have hFTW := CerednikDrinfeld.Omega.v_apply_smul_mul_zpow_sum_stabWidth_mul_pathCycle_mul_walkCycle_eq_of_isUnit_of_eq_theta
    R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hex ρ hρ hfin τ hτ hadj htame eE hz₁ ha₀ hz₁a₀ β U hU hUθ
    g (g * sMat (algebraMap R K₀ t) * nMat (algebraMap R K₀ ϖ) hϖ0) w₀ w₀ hw₀ hw₀ p₁

  have htail_mem : w₀ - algebraMap K₀ K (algebraMap R K₀ t) ∈ affinoid P 0 := by
    have := PLaux.add_mem_affinoid_zero P hw₀P (-(algebraMap R K₀ t)) (by rw [map_neg, Valuation.map_neg]; exact ht'1)
    rw [map_neg, ← sub_eq_add_neg] at this; exact this
  have htail_pt : (Matrix.ProjGenLinGroup.mk g • ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩ : ↥(upperHalfPlane K₀ K)) =
      Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t)) • ⟨w₀ - algebraMap K₀ K (algebraMap R K₀ t), sub_mem_upperHalfPlane K₀ hw₀Ω (algebraMap R K₀ t)⟩ := by
    apply Subtype.ext
    rw [coe_mk_smul, coe_mk_smul, map_mul, pmoebius_mul K₀ (sub_mem_upperHalfPlane K₀ hw₀Ω (algebraMap R K₀ t)),
      pmoebius_tMat K₀ (algebraMap R K₀ t) (sub_mem_upperHalfPlane K₀ hw₀Ω (algebraMap R K₀ t)), sub_add_cancel]
  have hval_tail : Valued.v ((U : ↥(upperHalfPlane K₀ K) → K)
      (Matrix.ProjGenLinGroup.mk g • ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩)) = c := by
    rw [htail_pt]
    have := hfib0 ⟨w₀ - algebraMap K₀ K (algebraMap R K₀ t), sub_mem_upperHalfPlane K₀ hw₀Ω (algebraMap R K₀ t)⟩ htail_mem
    rw [hf, inv_smul_apply] at this
    exact this

  have hhead_Ω : qK * w₀⁻¹ ∈ upperHalfPlane K₀ K :=
    PLaux.smul_mem_upperHalfPlane (inv_mem_upperHalfPlane K₀ hw₀Ω) _ hϖ0
  have hhead_mem : (algebraMap K₀ K P.ϖ)⁻¹ * (qK * w₀⁻¹) ∈ affinoid P 0 := by
    rw [show algebraMap K₀ K P.ϖ = qK from rfl, ← mul_assoc, inv_mul_cancel₀ hqK0, one_mul]
    exact PLaux.inv_mem_affinoid_zero P hw₀P
  have hhead_pt : (Matrix.ProjGenLinGroup.mk (g * sMat (algebraMap R K₀ t) * nMat (algebraMap R K₀ ϖ) hϖ0) •
        ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩ : ↥(upperHalfPlane K₀ K)) =
      Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t)) • ⟨qK * w₀⁻¹, hhead_Ω⟩ := by
    apply Subtype.ext
    have h1 : pmoebius K₀ (Matrix.ProjGenLinGroup.mk (nMat (algebraMap R K₀ ϖ) hϖ0)) w₀ ∈ upperHalfPlane K₀ K :=
      pmoebius_mem_upperHalfPlane K₀ hw₀Ω _
    have h1' : w₀ * (algebraMap K₀ K (algebraMap R K₀ ϖ))⁻¹ ∈ upperHalfPlane K₀ K := by
      rw [← pmoebius_nMat K₀ _ hϖ0 hw₀Ω]; exact h1
    rw [coe_mk_smul, coe_mk_smul, map_mul, map_mul, map_mul, pmoebius_mul K₀ hw₀Ω, pmoebius_mul K₀ h1,
      pmoebius_mul K₀ hhead_Ω, pmoebius_nMat K₀ _ hϖ0 hw₀Ω, pmoebius_sMat K₀ (algebraMap R K₀ t) h1',
      pmoebius_tMat K₀ (algebraMap R K₀ t) hhead_Ω]
    congr 1
    rw [hqK, mul_inv, inv_inv, add_comm, mul_comm]
  have hval_head : Valued.v ((U : ↥(upperHalfPlane K₀ K) → K)
      (Matrix.ProjGenLinGroup.mk (g * sMat (algebraMap R K₀ t) * nMat (algebraMap R K₀ ϖ) hϖ0) •
        ⟨w₀, affinoid_subset_upperHalfPlane ϖ₁ 0 hw₀⟩)) = c * q ^ m := by
    rw [hhead_pt]
    have := hfib1 ⟨qK * w₀⁻¹, hhead_Ω⟩ hhead_mem
    rw [hf, inv_smul_apply] at this
    exact this

  have hexp : q ^ m = q ^ (-(∑ e : E, ((stabWidth G (BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
      pathCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) (LT.LatticeTree.stdVertex R K₀) β e *
      walkCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) p₁ e)) := by
    rw [hval_head, hval_tail, mul_assoc] at hFTW
    have h1 := mul_left_cancel₀ hc0 (hFTW.trans (mul_one c).symm)
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left h1
  refine ⟨m, hexp, ?_⟩

  intro ζ ζ' hζΩ hζ'Ω hζ1 hζ2 hζ'1 hζ'2 hgζ hgζ'
  have hζT : ζ ∈ stdEdgeTube P := ⟨hζΩ, hζ1, hζ2⟩
  have hζ'T : ζ' ∈ stdEdgeTube P := ⟨hζ'Ω, hζ'1, hζ'2⟩
  have haΩ : pmoebius K₀ (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t))) ζ ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hζΩ _
  have hbΩ : pmoebius K₀ (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t))) ζ' ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hζ'Ω _
  have hUa : (U : ↥(upperHalfPlane K₀ K) → K) (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t)) • ⟨ζ, hζΩ⟩) =
      theta ρ z₁ (pmoebius K₀ (ρ β) z₁) a₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t))) ζ) :=
    hUθ _ (fun ⟨γ, hγ⟩ => hgζ γ hγ)
  have hUb : (U : ↥(upperHalfPlane K₀ K) → K) (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t)) • ⟨ζ', hζ'Ω⟩) =
      theta ρ z₁ (pmoebius K₀ (ρ β) z₁) a₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t))) ζ') :=
    hUθ _ (fun ⟨γ, hγ⟩ => hgζ' γ hγ)
  have hva : Valued.v (theta ρ z₁ (pmoebius K₀ (ρ β) z₁) a₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t))) ζ)) = c * Valued.v ζ ^ m := by
    rw [← hUa]; exact hlaw ζ hζT
  have hvb : Valued.v (theta ρ z₁ (pmoebius K₀ (ρ β) z₁) a₀ (pmoebius K₀ (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t))) ζ')) = c * Valued.v ζ' ^ m := by
    rw [← hUb]; exact hlaw ζ' hζ'T
  have hzb : ∀ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ β) z₁) ≠ pmoebius K₀ (Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ t))) ζ :=
    fun γ => by rw [← hρmul γ β z₁ hz₁]; exact hgζ (γ * β)
  have hcoc := CerednikDrinfeld.Omega.theta_mul_theta_basePoint ρ hgζ hzb
    (thetaMultipliable_of_isDiscrete_of_isExhausted ϖ₁ hex ρ hdisc hz₁ (pmoebius_mem_upperHalfPlane K₀ hz₁ _) ha₀ haΩ)
    (thetaMultipliable_of_isDiscrete_of_isExhausted ϖ₁ hex ρ hdisc hz₁ (pmoebius_mem_upperHalfPlane K₀ hz₁ _) haΩ hbΩ)
  have hv := congrArg Valued.v hcoc
  rw [map_mul, hva, hvb, mul_assoc] at hv
  have hv' := mul_left_cancel₀ hc0 hv
  rw [mul_comm] at hv'
  exact hv'

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega.GlobalCurrent"

open MulAction

namespace EPVkit

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem exists_root_window [IsAlgClosed K] (π t : K) (hπ0 : π ≠ 0) (hπ1 : v π < 1)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, v π ^ N ≤ ε) (ht : t ≠ 0) :
    ∃ (k : ℕ) (s r : K), 0 < k ∧ r * r = π ∧ s ^ k = t ∧
      v π < v r ∧ v r < 1 ∧ v π < v (s * r) ∧ v (s * r) < 1 := by
  have hvπ : 0 < v π := (Valuation.pos_iff _).2 hπ0
  have hvt : 0 < v t := (Valuation.pos_iff _).2 ht

  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq π (by norm_num : 0 < 2)
  have hr2 : v r ^ 2 = v π := by rw [← map_pow, hr]
  have hr0 : 0 < v r := by
    rcases eq_or_lt_of_le (zero_le' : 0 ≤ v r) with h | h
    · exfalso; rw [← h, zero_pow two_ne_zero] at hr2; exact hvπ.ne' hr2.symm
    · exact h
  have hr1 : v r < 1 := by
    by_contra h; push Not at h
    have : 1 ≤ v r ^ 2 := one_le_pow₀ h
    rw [hr2] at this; exact absurd hπ1 (not_lt.2 this)
  have hπr : v π < v r := by
    rw [← hr2, pow_two]; exact mul_lt_of_lt_one_left hr0 hr1

  obtain ⟨N₁, hN₁⟩ := hq (v t) hvt.ne'
  obtain ⟨N₂, hN₂⟩ := hq (v t)⁻¹ (inv_ne_zero hvt.ne')
  set N := max N₁ N₂ with hN
  have hle1 : v π ^ N ≤ v t := (pow_le_pow_right_of_le_one' hπ1.le (le_max_left _ _)).trans hN₁
  have hle2 : v π ^ N ≤ (v t)⁻¹ := (pow_le_pow_right_of_le_one' hπ1.le (le_max_right _ _)).trans hN₂
  set k := 2 * N + 1 with hk
  have hkpos : 0 < k := by omega
  have hρk : v r ^ k = v π ^ N * v r := by rw [hk, pow_succ, pow_mul, hr2]
  have hlow : v r ^ k < v t := by
    rw [hρk]; exact (mul_lt_of_lt_one_right (pow_pos hvπ N) hr1).trans_le hle1
  have hupp : v t < (v r)⁻¹ ^ k := by
    rw [inv_pow, hρk, mul_inv, ← inv_pow]
    have h1 : v t ≤ (v π ^ N)⁻¹ := by rwa [le_inv_comm₀ hvt (pow_pos hvπ N)]
    calc v t ≤ (v π)⁻¹ ^ N := by rwa [inv_pow]
      _ < (v π)⁻¹ ^ N * (v r)⁻¹ := lt_mul_of_one_lt_right (pow_pos (inv_pos.2 hvπ) N) (one_lt_inv₀ hr0 |>.2 hr1)

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq t hkpos
  have hsk : v s ^ k = v t := by rw [← map_pow, hs]
  have hs_low : v r < v s := by
    by_contra h; push Not at h
    have : v s ^ k ≤ v r ^ k := pow_le_pow_left' h k
    rw [hsk] at this; exact absurd hlow (not_lt.2 this)
  have hs_upp : v s < (v r)⁻¹ := by
    by_contra h; push Not at h
    have : (v r)⁻¹ ^ k ≤ v s ^ k := pow_le_pow_left' h k
    rw [hsk] at this; exact absurd hupp (not_lt.2 this)
  refine ⟨k, s, r, hkpos, by rw [← pow_two, hr], hs, hπr, hr1, ?_, ?_⟩
  · rw [map_mul, ← hr2, pow_two]; exact mul_lt_mul_of_pos_right hs_low hr0
  · rw [map_mul]; calc v s * v r < (v r)⁻¹ * v r := mul_lt_mul_of_pos_right hs_upp hr0
      _ = 1 := inv_mul_cancel₀ hr0.ne'

end EPVkit
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega.GlobalCurrent"

namespace EPVcol

variable {G : Type} [Group G] {W : Type} [MulAction G W] {𝒯 : SimpleGraph W} [GraphAction G 𝒯]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem quotEdge_eq_iff (d d' : 𝒯.Dart) :
    (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯) = Quotient.mk _ d' ↔ ∃ g : G, g • d' = d := by
  rw [Quotient.eq]; exact MulAction.orbitRel_apply.trans MulAction.mem_orbit_iff

theorem exists_smul_eq_out (d : 𝒯.Dart) :
    ∃ g : G, g • d = (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯).out := by
  have h := Quotient.out_eq (Quotient.mk (orbitRel G 𝒯.Dart) d : QuotEdge G 𝒯)
  exact (quotEdge_eq_iff _ _).1 h

theorem sum_mul_dartIndex_out
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)] {E : Type} [Fintype E] (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (F : E → ℤ) (e : E) :
    (∑ e' : E, F e' * dartIndex 𝒯 (eE e').1 (eE e).1.out) = F e := by
  classical
  have hcls : (Quotient.mk (orbitRel G 𝒯.Dart) (eE e).1.out : QuotEdge G 𝒯) = (eE e).1 := Quotient.out_eq _

  have hrev : ∀ e' : E, (Quotient.mk (orbitRel G 𝒯.Dart) (eE e).1.out.symm : QuotEdge G 𝒯) ≠ (eE e').1 := by
    intro e' heq
    have h0 : τ (eE e).1.out.fst = 0 := (eE e).2
    have h0' : τ (eE e').1.out.fst = 0 := (eE e').2
    have h1 : τ (eE e).1.out.snd ≠ 0 := fun h => hadj _ _ (eE e).1.out.adj (h0.trans h.symm)
    obtain ⟨g, hg⟩ := exists_smul_eq_out (G := G) (eE e).1.out.symm
    rw [heq] at hg

    have hfst : (g • (eE e).1.out.symm).fst = (eE e').1.out.fst := by rw [hg]
    rw [smul_dart_fst] at hfst
    have : τ (eE e).1.out.symm.fst = 0 := by rw [← hτ g, hfst]; exact h0'
    exact h1 this
  have hidx : ∀ e' : E, dartIndex 𝒯 (eE e').1 (eE e).1.out = if e' = e then 1 else 0 := by
    intro e'
    rw [dartIndex, hcls, if_neg (hrev e')]
    by_cases h : e' = e
    · subst h; simp
    · rw [if_neg, if_neg h]; · simp
      intro heq; exact h (eE.injective (Subtype.ext heq.symm))
  simp_rw [hidx]
  simp [Finset.sum_ite_eq']

end EPVcol
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega.GlobalCurrent"

theorem EPVaux.theta_pair_eq
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    (hΘ : ∀ {x y : K}, x ∈ upperHalfPlane K₀ K → y ∈ upperHalfPlane K₀ K →
      ∀ w ∈ upperHalfPlane K₀ K, ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ x y w z)
    {a b z₀ z₁ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz₁ : z₁ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (hz₁a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₁) (hz₁b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₁)
    (haz₁ : ∀ γ : G, pmoebius K₀ (ρ γ) z₁ ≠ a) (β : G) :
    theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) = theta ρ z₁ (pmoebius K₀ (ρ β) z₁) a b := by
  have hβz₁ : pmoebius K₀ (ρ β) z₁ ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hz₁ (ρ β)
  rw [← CerednikDrinfeld.Omega.theta_pmoebius_basePoint_eq_theta_pmoebius_basePoint ρ ha hb hz₀ hz₁ hz₀a hz₀b hz₁a hz₁b
    (fun w hw z hz => hΘ ha hb w hw z hz) β]
  have hself : theta ρ z₁ (pmoebius K₀ (ρ β) z₁) a a = 1 := by
    refine CerednikDrinfeld.Omega.theta_self_eq_one ρ haz₁ (fun γ => ?_)
    rw [← pmoebius_mul K₀ hz₁, ← map_mul]
    exact haz₁ (γ * β)
  have h4 := CerednikDrinfeld.Omega.theta_pmoebius_mul_theta_eq_theta ρ ha hb hz₁ ha hz₁a hz₁b haz₁ β
    (hΘ ha hb z₁ hz₁ _ hβz₁) (hΘ hz₁ hβz₁ a ha a ha)
  rw [hself, mul_one] at h4
  exact h4

namespace EPVgen

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
  {G : Type} [Group G]

theorem exists_pair_generic
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (h : PGL(2, K₀)) {r s : K} (hr : r ≠ 0) (hs : s ≠ 0)
    (n₁ n₂ : ℕ)
    (hball₁ : ∀ ζ : K, Valued.v (ζ - r) < Valued.v r → ζ ∈ affinoid ϖ n₁)
    (hball₂ : ∀ ζ : K, Valued.v (ζ - s * r) < Valued.v (s * r) → ζ ∈ affinoid ϖ n₂)
    (Y : Finset K) (hY : ∀ y ∈ Y, y ∈ upperHalfPlane K₀ K) :
    ∃ ζ : K, Valued.v (ζ - r) < Valued.v r ∧
      (∀ y ∈ Y, ∀ γ : G, pmoebius K₀ (ρ γ) y ≠ pmoebius K₀ h ζ) ∧
      (∀ y ∈ Y, ∀ γ : G, pmoebius K₀ (ρ γ) y ≠ pmoebius K₀ h (s * ζ)) := by
  classical

  have hbad₂ : {ζ' : K | ζ' ∈ affinoid ϖ n₂ ∧ ∃ y ∈ Y, ∃ γ : G, pmoebius K₀ (ρ γ) y = pmoebius K₀ h ζ'}.Finite := by
    refine (Set.Finite.biUnion (Finset.finite_toSet Y) fun y hy =>
      finite_setOf_mem_affinoid_and_exists_pmoebius_eq ϖ hex ρ hρ h n₂ (hY y hy)).subset ?_
    rintro ζ' ⟨hζ', y, hy, γ, hγ⟩
    exact Set.mem_biUnion hy ⟨hζ', γ, hγ⟩
  set B : Finset K := (hbad₂.image (fun ζ' : K => s⁻¹ * ζ')).toFinset with hB
  obtain ⟨ζ, hζ, hζB, hζ1⟩ := exists_mem_ball_forall_ne ϖ hex ρ hρ h n₁ (x₀ := r) (c := r) hr hball₁ Y hY B
  refine ⟨ζ, hζ, hζ1, ?_⟩
  intro y hy γ hγ
  apply hζB
  rw [hB, Set.Finite.mem_toFinset]
  refine ⟨s * ζ, ⟨hball₂ _ ?_, y, hy, γ, hγ⟩, ?_⟩
  · rw [← mul_sub, map_mul, map_mul]
    exact mul_lt_mul_of_pos_left hζ ((Valuation.pos_iff _).2 hs)
  · show s⁻¹ * (s * ζ) = ζ
    rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

end EPVgen
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne.CerednikDrinfeld.Omega.GlobalCurrent"

open EPVkit EPVcol HarmV0 CerednikDrinfeld.Omega.GlobalCurrent in
theorem solution
    (R K₀ : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
    [IsFractionRing R K₀] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ K (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ 1 → IsLocalization.IsInteger R a)
    (hq : ∀ ε : Γ₀, ε ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) ^ N ≤ ε)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (ϖ₁ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ₁) [IsDomain ↥(holRing ϖ₁)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R K₀)]
    [CerednikDrinfeld.Mumford.GraphAction G (CerednikDrinfeld.BruhatTits.tree R K₀)]
    (hρ : CerednikDrinfeld.Mumford.ActsThrough (LT.LatticeTree.Vertex R K₀) ρ)

    (hfin : ∀ w : LT.LatticeTree.Vertex R K₀, Finite (MulAction.stabilizer G w))
    [Finite (CerednikDrinfeld.Mumford.QuotVert G (LT.LatticeTree.Vertex R K₀))]
    (τ : LT.LatticeTree.Vertex R K₀ → ZMod 2) (hτ : ∀ (g : G) (w : LT.LatticeTree.Vertex R K₀), τ (g • w) = τ w)
    (hadj : ∀ u w : LT.LatticeTree.Vertex R K₀, (CerednikDrinfeld.BruhatTits.tree R K₀).Adj u w → τ u ≠ τ w)
    (htame : ∀ w : LT.LatticeTree.Vertex R K₀, Valued.v ((Nat.card ↥(MulAction.stabilizer G w) : ℕ) : K) = 1)

    (z₀ : K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)

    [DecidableEq (CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀))]
    {E : Type} [Fintype E]
    (eE : E ≃ {e : CerednikDrinfeld.Mumford.QuotEdge G (CerednikDrinfeld.BruhatTits.tree R K₀) // τ e.out.fst = 0})
    (e : E) (t : K) (ht : t ≠ 0)

    (S : Finset ↥(upperHalfPlane K₀ K)) :
    ∃ (n : ℕ) (a b : Fin n → K),
      (∀ i, a i ∈ upperHalfPlane K₀ K) ∧ (∀ i, b i ∈ upperHalfPlane K₀ K) ∧
      (∀ i (γ : G), pmoebius K₀ (ρ γ) (a i) ≠ z₀) ∧ (∀ i (γ : G), pmoebius K₀ (ρ γ) (b i) ≠ z₀) ∧
      (∀ s ∈ S, ∀ i (δ : G), a i ≠ pmoebius K₀ (ρ δ) (s : K) ∧ b i ≠ pmoebius K₀ (ρ δ) (s : K)) ∧
      ∀ β : G, Valued.v (∏ i, theta ρ (a i) (b i) z₀ (pmoebius K₀ (ρ β) z₀)) =
        Valued.v t ^ (((CerednikDrinfeld.Mumford.stabWidth G (CerednikDrinfeld.BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
          CerednikDrinfeld.Mumford.pathCycle (CerednikDrinfeld.BruhatTits.tree R K₀) (fun e' => (eE e').1)
            (LT.LatticeTree.stdVertex R K₀) β e) := by
  classical

  set πK : K := algebraMap K₀ K (algebraMap R K₀ ϖ) with hπK
  set q : Γ₀ := Valued.v πK with hqdef
  have hϖ0 : algebraMap R K₀ ϖ ≠ 0 := algebraMap_ne_zero_of_irreducible hϖ
  have hq0 : 0 < q := v_algebraMap_pos hϖ
  have hq1 : q < 1 := v_algebraMap_lt_one hϖ hv
  have hπ0 : πK ≠ 0 := (Valuation.ne_zero_iff _).1 hq0.ne'
  have hqinj : Function.Injective (fun k : ℤ => q ^ k) := zpow_right_injective₀ hq0 hq1.ne
  have hunifq : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ q ∨ 1 ≤ Valued.v (algebraMap K₀ K a) :=
    v_algebraMap_le_or_one_le hϖ hint hv
  have hwinΩ : ∀ z : K, q < Valued.v z → Valued.v z < 1 → z ∈ upperHalfPlane K₀ K := by
    intro z h1 h2
    rw [mem_upperHalfPlane_iff]
    rintro a rfl
    rcases hunifq a with h | h
    · exact absurd h1 (not_lt.2 h)
    · exact absurd h2 (not_lt.2 h)
  have hwin_ne : ∀ (z : K) (a : K₀), q < Valued.v z → Valued.v z < 1 → Valued.v z ≠ Valued.v (algebraMap K₀ K a) := by
    intro z a h1 h2 h
    rcases hunifq a with h' | h'
    · exact absurd h1 (not_lt.2 (h ▸ h'))
    · exact absurd h2 (not_lt.2 (h ▸ h'))
  have hball_aff : ∀ x : K, q < Valued.v x → Valued.v x < 1 →
      ∃ n : ℕ, ∀ ζ : K, Valued.v (ζ - x) < Valued.v x → ζ ∈ affinoid ϖ₁ n := by
    intro x hx1 hx2
    obtain ⟨n, hn⟩ := hex x (hwinΩ x hx1 hx2)
    refine ⟨n, fun ζ hζ => ?_⟩
    rw [mem_affinoid_iff'] at hn ⊢
    have hvζ : Valued.v ζ = Valued.v x := by
      have e : ζ = x + (ζ - x) := by ring
      rw [e]; exact Valuation.map_add_eq_of_lt_left _ hζ
    refine ⟨hvζ ▸ hn.1, fun a => ?_⟩
    have hxa : Valued.v (ζ - x) < Valued.v (x - algebraMap K₀ K a) := by
      refine hζ.trans_le ?_
      rcases lt_or_gt_of_ne (hwin_ne x a hx1 hx2) with h | h
      · rw [Valuation.map_sub_eq_of_lt_right _ h]; exact h.le
      · rw [Valuation.map_sub_eq_of_lt_left _ h]
    have e : ζ - algebraMap K₀ K a = (x - algebraMap K₀ K a) + (ζ - x) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ hxa]
    exact hn.2 a
  have hdisc : IsDiscrete K ρ := by
    refine isDiscrete_of_finite_stabilizer_stdVertex R K₀ ϖ hϖ K hint hv hq ρ ?_
    have : {γ : G | ρ γ • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀}
        = (stabilizer G (LT.LatticeTree.stdVertex R K₀) : Set G) := by
      ext γ; simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_stabilizer_iff, hρ γ]
    rw [this]; exact Set.toFinite _
  have hΘ : ∀ {a b : K}, a ∈ upperHalfPlane K₀ K → b ∈ upperHalfPlane K₀ K →
      ∀ w ∈ upperHalfPlane K₀ K, ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ a b w z :=
    fun ha hb w hw z hz => thetaMultipliable_of_isDiscrete_of_isExhausted ϖ₁ hex ρ hdisc ha hb hw hz
  have havoid : ∀ {y x : K}, x ∈ upperHalfPlane K₀ K → (∀ γ : G, pmoebius K₀ (ρ γ) y ≠ x) →
      ∀ γ : G, pmoebius K₀ (ρ γ) x ≠ y := by
    intro y x hx h γ hγ
    apply h γ⁻¹
    rw [← hγ, ← pmoebius_mul K₀ hx, map_inv, inv_mul_cancel, pmoebius_one]

  set d : (BruhatTits.tree R K₀).Dart := (eE e).1.out with hd
  obtain ⟨g, tR, hfst, hsnd⟩ :=
    CerednikDrinfeld.BruhatTits.exists_smul_stdVertex_eq_fst_and_mul_smul_stdVertex_eq_snd R K₀ ϖ hϖ
      (nMat (algebraMap R K₀ ϖ) hϖ0) (coe_nMat _ _) (fun t => sMat (algebraMap R K₀ t)) (fun t => coe_sMat _) d
  have hadj₁ : (BruhatTits.tree R K₀).Adj (g • LT.LatticeTree.stdVertex R K₀)
      ((g * sMat (algebraMap R K₀ tR) * nMat (algebraMap R K₀ ϖ) hϖ0) • LT.LatticeTree.stdVertex R K₀) := by
    rw [hfst, hsnd]; exact d.adj
  let p₁ : (BruhatTits.tree R K₀).Walk (g • LT.LatticeTree.stdVertex R K₀)
      ((g * sMat (algebraMap R K₀ tR) * nMat (algebraMap R K₀ ϖ) hϖ0) • LT.LatticeTree.stdVertex R K₀) :=
    SimpleGraph.Walk.cons hadj₁ SimpleGraph.Walk.nil
  have hdart : (⟨(g • LT.LatticeTree.stdVertex R K₀,
      (g * sMat (algebraMap R K₀ tR) * nMat (algebraMap R K₀ ϖ) hϖ0) • LT.LatticeTree.stdVertex R K₀), hadj₁⟩ :
      (BruhatTits.tree R K₀).Dart) = d := by
    ext <;> simp [hfst, hsnd]
  have hsum1 : ∀ β : G,
      (∑ e' : E, ((stabWidth G (BruhatTits.tree R K₀) (eE e').1 : ℕ) : ℤ) *
          pathCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) (LT.LatticeTree.stdVertex R K₀) β e' *
          walkCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) p₁ e')
        = ((stabWidth G (BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
          pathCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) (LT.LatticeTree.stdVertex R K₀) β e := by
    intro β
    have hw : ∀ e' : E, walkCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) p₁ e' =
        dartIndex (BruhatTits.tree R K₀) (eE e').1 d := by
      intro e'
      show walkCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) (SimpleGraph.Walk.cons hadj₁ SimpleGraph.Walk.nil) e' = _
      rw [walkCycle_cons, walkCycle_nil, Pi.zero_apply, add_zero, hdart]
    simp_rw [hw]
    exact sum_mul_dartIndex_out τ hτ hadj eE (fun e' => ((stabWidth G (BruhatTits.tree R K₀) (eE e').1 : ℕ) : ℤ) *
      pathCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) (LT.LatticeTree.stdVertex R K₀) β e') e
  set hP : PGL(2, K₀) := Matrix.ProjGenLinGroup.mk (g * tMat (algebraMap R K₀ tR)) with hhP

  obtain ⟨k, s, r, hk, hr2, hsk, hqr, hr1, hqsr, hsr1⟩ := exists_root_window πK t hπ0 hq1 hq ht
  have hr0 : r ≠ 0 := fun h => by rw [h, Valuation.map_zero] at hqr; exact absurd hqr (not_lt.2 zero_le')
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_pow hk.ne'] at hsk; exact ht hsk.symm
  have hrΩ := hwinΩ r hqr hr1
  have hsrΩ := hwinΩ (s * r) hqsr hsr1
  obtain ⟨n₁, hball₁⟩ := hball_aff r hqr hr1
  obtain ⟨n₂, hball₂⟩ := hball_aff (s * r) hqsr hsr1

  set Y : Finset K := insert z₀ (S.image (fun s : ↥(upperHalfPlane K₀ K) => (s : K))) with hY
  have hYΩ : ∀ y ∈ Y, y ∈ upperHalfPlane K₀ K := by
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hz₀
    · obtain ⟨s', -, rfl⟩ := Finset.mem_image.1 hy; exact s'.2
  obtain ⟨ζ, hζr, hζY, hsζY⟩ := EPVgen.exists_pair_generic ϖ₁ hex ρ hdisc hP hr0 hs0 n₁ n₂ hball₁ hball₂ Y hYΩ
  have hvζ : Valued.v ζ = Valued.v r := by
    have e1 : ζ = r + (ζ - r) := by ring
    rw [e1]; exact Valuation.map_add_eq_of_lt_left _ hζr
  have hvsζ : Valued.v (s * ζ) = Valued.v (s * r) := by rw [map_mul, map_mul, hvζ]
  have hζΩ : ζ ∈ upperHalfPlane K₀ K := hwinΩ ζ (hvζ ▸ hqr) (hvζ ▸ hr1)
  have hsζΩ : s * ζ ∈ upperHalfPlane K₀ K := hwinΩ (s * ζ) (hvsζ ▸ hqsr) (hvsζ ▸ hsr1)

  set a : K := pmoebius K₀ hP (s * ζ) with haP
  set b : K := pmoebius K₀ hP ζ with hbP
  have ha : a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hsζΩ hP
  have hb : b ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hζΩ hP
  have hz₀a' : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ a := hsζY z₀ (Finset.mem_insert_self _ _)
  have hz₀b' : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ b := hζY z₀ (Finset.mem_insert_self _ _)
  have hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀ := havoid ha hz₀a'
  have hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀ := havoid hb hz₀b'
  have hSa : ∀ s' ∈ S, ∀ δ : G, a ≠ pmoebius K₀ (ρ δ) (s' : K) := fun s' hs' δ h =>
    hsζY (s' : K) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hs')) δ h.symm
  have hSb : ∀ s' ∈ S, ∀ δ : G, b ≠ pmoebius K₀ (ρ δ) (s' : K) := fun s' hs' δ h =>
    hζY (s' : K) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hs')) δ h.symm

  obtain ⟨ζ₁, hζ₁r, hζ₁Y, -⟩ := EPVgen.exists_pair_generic ϖ₁ hex ρ hdisc hP hr0 hs0 n₁ n₂ hball₁ hball₂ {a, b}
    (by intro y hy; rcases Finset.mem_insert.1 hy with rfl | hy; · exact ha
        · rw [Finset.mem_singleton] at hy; rw [hy]; exact hb)
  have hvζ₁ : Valued.v ζ₁ = Valued.v r := by
    have e1 : ζ₁ = r + (ζ₁ - r) := by ring
    rw [e1]; exact Valuation.map_add_eq_of_lt_left _ hζ₁r
  have hζ₁Ω : ζ₁ ∈ upperHalfPlane K₀ K := hwinΩ ζ₁ (hvζ₁ ▸ hqr) (hvζ₁ ▸ hr1)
  set z₁ : K := pmoebius K₀ hP ζ₁ with hz₁P
  have hz₁ : z₁ ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hζ₁Ω hP
  have hz₁a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₁ := hζ₁Y a (Finset.mem_insert_self _ _)
  have hz₁b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₁ := hζ₁Y b (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have haz₁ : ∀ γ : G, pmoebius K₀ (ρ γ) z₁ ≠ a := havoid hz₁ hz₁a
  have hbz₁ : ∀ γ : G, pmoebius K₀ (ρ γ) z₁ ≠ b := havoid hz₁ hz₁b

  have hval : ∀ β : G, Valued.v (theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀)) =
      Valued.v s ^ (((stabWidth G (BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
        pathCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) (LT.LatticeTree.stdVertex R K₀) β e) := by
    intro β
    set M : ℤ := ((stabWidth G (BruhatTits.tree R K₀) (eE e).1 : ℕ) : ℤ) *
        pathCycle (BruhatTits.tree R K₀) (fun e' => (eE e').1) (LT.LatticeTree.stdVertex R K₀) β e with hM
    obtain ⟨m, hm, hlaw⟩ := PAIRLAW.v_theta_pair R K₀ ϖ hϖ K hint hv hq hrk ϖ₁ hex ρ hρ hfin τ hτ hadj htame eE
      hϖ0 g tR p₁ hz₁ β
    rw [hsum1 β] at hm
    have hmM : m = -M := hqinj hm
    have h1 := hlaw (s * ζ) ζ hsζΩ hζΩ (hvsζ ▸ hqsr) (hvsζ ▸ hsr1) (hvζ ▸ hqr) (hvζ ▸ hr1) haz₁ hbz₁
    rw [EPVaux.theta_pair_eq ρ hΘ ha hb hz₀ hz₁ hz₀a hz₀b hz₁a hz₁b haz₁ β]

    have hvζ0 : Valued.v ζ ≠ 0 := by rw [hvζ]; exact (hq0.trans hqr).ne'
    have hvs0 : Valued.v s ≠ 0 := (Valuation.ne_zero_iff _).2 hs0
    rw [Valuation.map_mul, mul_zpow, ← mul_assoc] at h1

    have hζm : Valued.v ζ ^ m ≠ 0 := zpow_ne_zero _ hvζ0
    have h2 : Valued.v (theta ρ z₁ (pmoebius K₀ (ρ β) z₁) a b) * Valued.v s ^ m = 1 :=
      (mul_left_eq_self₀.1 h1).resolve_right hζm
    rw [eq_inv_of_mul_eq_one_left h2, hmM, zpow_neg, inv_inv]

  refine ⟨k, fun _ => a, fun _ => b, fun _ => ha, fun _ => hb, fun _ γ => hz₀a γ, fun _ γ => hz₀b γ,
    fun s' hs' _ δ => ⟨hSa s' hs' δ, hSb s' hs' δ⟩, fun β => ?_⟩
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow, hval β, ← hsk, map_pow,
    ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

end S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_pairs_v_prod_theta_eq_v_zpow_stabWidth_mul_pathCycle_forall_ne (solution)
