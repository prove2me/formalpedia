-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_forall_exists_smul_mem_affinoid_of_relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/152af240-b221-5826-b89c-ade4e90d4052

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_CerednikDrinfeld_Ribbon
import Theorems.Thm_CerednikDrinfeld_Omega_isSchottky_map_of_relIndex_ne_zero_of_forall_isOfFinOrder
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_smul_eq_of_forall_exists_smul_mem_affinoid
import Mathlib
import Theorems.Thm_CerednikDrinfeld_Mumford_exists_monoidHom_ker_eq_typePreserving_and_index_dvd_two
import Theorems.Thm_CerednikDrinfeld_BruhatTits_tree_connected_and_colorable_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_forall_exists_smul_mem_affinoid_of_relIndex_ne_zero
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford CerednikDrinfeld.BruhatTits LT.LatticeTree

noncomputable section

namespace P2mKcLiouvInv

section Powers

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

theorem algebraMap_varpi_ne_zero : algebraMap K₀ K ϖ.ϖ ≠ 0 := fun h => by
  have := ϖ.pos
  rw [h, map_zero] at this
  exact lt_irrefl _ this

theorem varpi_ne_zero : ϖ.ϖ ≠ 0 := fun h => algebraMap_varpi_ne_zero ϖ (by rw [h, map_zero])

theorem p_le_one : Valued.v (algebraMap K₀ K ϖ.ϖ) ≤ 1 := ϖ.lt_one.le

theorem one_le_P : 1 ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := (one_le_inv₀ ϖ.pos).2 (p_le_one ϖ)

theorem p_pow_anti {i j : ℕ} (h : i ≤ j) :
    Valued.v (algebraMap K₀ K ϖ.ϖ) ^ j ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ i :=
  pow_le_pow_right_of_le_one' (p_le_one ϖ) h

theorem P_pow_mono {i j : ℕ} (h : i ≤ j) :
    (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ i ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ j :=
  pow_le_pow_right₀ (one_le_P ϖ) h

theorem P_pow_mul_p_pow (i : ℕ) :
    (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ i * Valued.v (algebraMap K₀ K ϖ.ϖ) ^ i = 1 := by
  rw [← mul_pow, inv_mul_cancel₀ ϖ.pos.ne', one_pow]

theorem p_pow_le_one (i : ℕ) : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ i ≤ 1 := pow_le_one₀ zero_le' (p_le_one ϖ)

theorem one_le_P_pow (i : ℕ) : 1 ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ i := one_le_pow₀ (one_le_P ϖ)

theorem pow_succ_lt_pow (n : ℕ) :
    Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n := by
  rw [pow_succ]
  exact mul_lt_of_lt_one_right (pow_pos ϖ.pos n) ϖ.lt_one

end Powers

section LocFin

variable {R₀ K₀ : Type} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Field K₀] [Algebra R₀ K₀]
  [IsFractionRing R₀ K₀]
variable {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem hfin_of_finite_residueField [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)
    (ϖ : PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ) (n : ℕ) :
    ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n := by
  classical
  set p : Γ₀ := Valued.v (algebraMap K₀ K ϖ.ϖ) with hp
  have hp0 : 0 < p := ϖ.pos
  have hp1 : p < 1 := ϖ.lt_one
  set k : ℕ := n + (n + 1) with hk
  have hmax : IsLocalRing.maximalIdeal R₀ = Ideal.span {ϖ₀} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).1 hϖ₀
  haveI : Finite (R₀ ⧸ Ideal.span {ϖ₀ ^ k}) :=
    IsLocalRing.finite_quotient_iff.2 ⟨k, by rw [hmax, Ideal.span_singleton_pow]⟩
  letI : Fintype (R₀ ⧸ Ideal.span {ϖ₀ ^ k}) := Fintype.ofFinite _
  have hϖn0 : (ϖ.ϖ : K₀) ^ n ≠ 0 := pow_ne_zero n (varpi_ne_zero ϖ)
  refine ⟨Finset.univ.image fun c : R₀ ⧸ Ideal.span {ϖ₀ ^ k} => algebraMap R₀ K₀ (Quotient.out c) / ϖ.ϖ ^ n,
    fun a ha => ?_⟩

  have hint' : Valued.v (algebraMap K₀ K (ϖ.ϖ ^ n * a)) ≤ 1 := by
    rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]
    calc p ^ n * Valued.v (algebraMap K₀ K a) ≤ p ^ n * (p⁻¹) ^ n := mul_le_mul_right ha _
      _ = 1 := by rw [mul_comm, P_pow_mul_p_pow]
  obtain ⟨r, hr⟩ := (hR₀ _).2 hint'
  set c : R₀ ⧸ Ideal.span {ϖ₀ ^ k} := Ideal.Quotient.mk _ r with hc
  have hcs : r - Quotient.out c ∈ Ideal.span {ϖ₀ ^ k} := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
  obtain ⟨r'', hr''⟩ := Ideal.mem_span_singleton.1 hcs
  refine ⟨algebraMap R₀ K₀ (Quotient.out c) / ϖ.ϖ ^ n, Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩, ?_⟩

  have haeq : a = algebraMap R₀ K₀ r / ϖ.ϖ ^ n := by
    rw [eq_div_iff hϖn0, mul_comm, hr]
  have hat : a - algebraMap R₀ K₀ (Quotient.out c) / ϖ.ϖ ^ n = ϖ.ϖ ^ (n + 1) * algebraMap R₀ K₀ r'' := by
    rw [haeq, ← sub_div, ← map_sub, hr'', div_eq_iff hϖn0, map_mul, map_pow, hϖ, hk]
    ring
  have hint : Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ r'')) ≤ 1 := (hR₀ _).1 ⟨r'', rfl⟩
  rw [← map_sub, hat, map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]
  calc p ^ (n + 1) * Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ r''))
      ≤ p ^ (n + 1) * 1 := mul_le_mul_right hint _
    _ < p ^ n := by rw [mul_one]; exact pow_succ_lt_pow ϖ n

end LocFin

section Cover

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

theorem exists_nearest
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {n : ℕ} {z : K} (hz : z ∈ affinoid ϖ n) :
    ∃ a₀ : K₀, (∀ a : K₀, Valued.v (z - algebraMap K₀ K a₀) ≤ Valued.v (z - algebraMap K₀ K a)) ∧
      Valued.v (z - algebraMap K₀ K a₀) ≤ Valued.v z := by
  classical
  obtain ⟨T, hT⟩ := hfin n
  obtain ⟨hz1, hz2⟩ := (mem_affinoid_iff' ϖ n z).1 hz
  set S : Finset K₀ := insert 0 T with hS
  obtain ⟨a₀, ha₀S, hmin⟩ := Finset.exists_min_image S (fun t => Valued.v (z - algebraMap K₀ K t))
    ⟨0, Finset.mem_insert_self 0 T⟩
  have h0 : Valued.v (z - algebraMap K₀ K a₀) ≤ Valued.v z := by
    have := hmin 0 (Finset.mem_insert_self 0 T)
    rwa [map_zero, sub_zero] at this
  refine ⟨a₀, fun a => ?_, h0⟩
  rcases le_or_gt (Valued.v (algebraMap K₀ K a)) ((Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n) with ha | ha
  · obtain ⟨t, htT, hat⟩ := hT a ha

    have hlt : Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < Valued.v (z - algebraMap K₀ K a) :=
      lt_of_lt_of_le hat (hz2 a)
    have heq : Valued.v (z - algebraMap K₀ K t) = Valued.v (z - algebraMap K₀ K a) := by
      have : z - algebraMap K₀ K t = (z - algebraMap K₀ K a) + (algebraMap K₀ K a - algebraMap K₀ K t) := by ring
      rw [this]
      exact Valuation.map_add_eq_of_lt_left _ hlt
    exact (hmin t (Finset.mem_insert_of_mem htT)).trans heq.le
  ·
    have hza : Valued.v z < Valued.v (algebraMap K₀ K a) := lt_of_le_of_lt hz1 ha
    have heq : Valued.v (z - algebraMap K₀ K a) = Valued.v (algebraMap K₀ K a) :=
      Valuation.map_sub_eq_of_lt_right _ hza
    rw [heq]
    exact h0.trans hza.le

theorem exists_sub_div_mem_affinoid_one
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {n : ℕ} {z : K} (hz : z ∈ affinoid ϖ n) :
    ∃ a₀ c : K₀, c ≠ 0 ∧ (z - algebraMap K₀ K a₀) / algebraMap K₀ K c ∈ affinoid ϖ 1 := by
  classical
  obtain ⟨a₀, hmin, hle⟩ := exists_nearest ϖ hfin hz
  obtain ⟨hz1, hz2⟩ := (mem_affinoid_iff' ϖ n z).1 hz
  set p : Γ₀ := Valued.v (algebraMap K₀ K ϖ.ϖ) with hp
  set d : Γ₀ := Valued.v (z - algebraMap K₀ K a₀) with hd

  have hdlo : p ^ n ≤ d := hz2 a₀
  have hdhi : d ≤ p⁻¹ ^ n := hle.trans hz1
  have hd0 : 0 < d := lt_of_lt_of_le (pow_pos ϖ.pos n) hdlo
  set d' : Γ₀ := p ^ n * d with hd'
  have hd'1 : d' ≤ 1 := by
    calc d' ≤ p ^ n * p⁻¹ ^ n := mul_le_mul_right hdhi _
      _ = 1 := by rw [mul_comm, P_pow_mul_p_pow]
  have hd'lo : p ^ (2 * n) ≤ d' := by
    rw [two_mul, pow_add]; exact mul_le_mul_right hdlo _

  set m : ℕ := Nat.findGreatest (fun m => d' ≤ p ^ m) (2 * n) with hm
  have hm1 : d' ≤ p ^ m := by
    have := Nat.findGreatest_spec (P := fun m => d' ≤ p ^ m) (Nat.zero_le (2 * n))
      (by show d' ≤ p ^ 0; rw [pow_zero]; exact hd'1)
    exact this
  have hm2 : p ^ (m + 1) < d' := by
    by_contra hge
    push Not at hge
    rcases lt_or_ge m (2 * n) with hlt | hge'
    · have := Nat.findGreatest_is_greatest (P := fun m => d' ≤ p ^ m) (Nat.lt_succ_self m) (Nat.succ_le_of_lt hlt)
      exact this hge
    ·
      have hmle : m ≤ 2 * n := Nat.findGreatest_le _
      have hmeq : m = 2 * n := le_antisymm hmle hge'
      rw [hmeq] at hge
      exact absurd (lt_of_le_of_lt hge (pow_succ_lt_pow ϖ (2 * n))) (not_lt.2 hd'lo)

  have hϖ0 : (ϖ.ϖ : K₀) ≠ 0 := varpi_ne_zero ϖ
  set c : K₀ := ϖ.ϖ ^ m / ϖ.ϖ ^ n with hc
  have hc0 : c ≠ 0 := div_ne_zero (pow_ne_zero _ hϖ0) (pow_ne_zero _ hϖ0)
  have hcK0 : algebraMap K₀ K c ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hvc : Valued.v (algebraMap K₀ K c) = p ^ m / p ^ n := by
    rw [hc, map_div₀, map_pow, map_pow, map_div₀, Valuation.map_pow, Valuation.map_pow]
  have hpn0 : p ^ n ≠ 0 := pow_ne_zero _ ϖ.pos.ne'
  have hpm0 : 0 < p ^ m := pow_pos ϖ.pos m
  have hvc0 : 0 < Valued.v (algebraMap K₀ K c) := by rw [hvc]; exact div_pos hpm0 (pow_pos ϖ.pos n)
  set w : K := (z - algebraMap K₀ K a₀) / algebraMap K₀ K c with hw
  have hvw : Valued.v w = d' / p ^ m := by
    rw [hw, map_div₀, hvc, ← hd, hd', div_div_eq_mul_div, mul_comm]
  have hvw1 : Valued.v w ≤ 1 := by rw [hvw, div_le_one₀ hpm0]; exact hm1
  have hvwp : p < Valued.v w := by
    rw [hvw, lt_div_iff₀ hpm0, mul_comm, ← pow_succ]; exact hm2
  refine ⟨a₀, c, hc0, ?_⟩
  rw [mem_affinoid_iff']
  refine ⟨hvw1.trans (by rw [pow_one]; exact one_le_P ϖ), fun b => ?_⟩

  have hsub : w - algebraMap K₀ K b = (z - algebraMap K₀ K (a₀ + c * b)) / algebraMap K₀ K c := by
    rw [hw, eq_div_iff hcK0, sub_mul, div_mul_cancel₀ _ hcK0, map_add, map_mul]; ring
  rw [pow_one, hsub, map_div₀, le_div_iff₀ hvc0]
  calc p * Valued.v (algebraMap K₀ K c) ≤ Valued.v w * Valued.v (algebraMap K₀ K c) := mul_le_mul_left hvwp.le _
    _ = d := by rw [hw, map_div₀, div_mul_cancel₀ _ hvc0.ne']
    _ ≤ Valued.v (z - algebraMap K₀ K (a₀ + c * b)) := hmin _

end Cover

section Stab

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

theorem row_lower {m : ℕ} {w : K} (hw : w ∈ affinoid ϖ m) (x y γ δ : K₀)
    (hγ : Valued.v (algebraMap K₀ K γ) ≤ 1) (hδ : Valued.v (algebraMap K₀ K δ) ≤ 1)
    (hdet : 1 ≤ Valued.v (algebraMap K₀ K (x * δ - y * γ))) :
    Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (2 * m) ≤ Valued.v (algebraMap K₀ K x * w + algebraMap K₀ K y) := by
  set p : Γ₀ := Valued.v (algebraMap K₀ K ϖ.ϖ) with hp
  obtain ⟨hw1, hw2⟩ := (mem_affinoid_iff' ϖ m w).1 hw
  have hpm1 : p ^ m ≤ 1 := p_pow_le_one ϖ m
  have hp2m : p ^ (2 * m) ≤ p ^ m := p_pow_anti ϖ (by omega)

  have hmax : 1 ≤ max (Valued.v (algebraMap K₀ K x)) (Valued.v (algebraMap K₀ K y)) := by
    have h1 : Valued.v (algebraMap K₀ K (x * δ - y * γ)) ≤
        max (Valued.v (algebraMap K₀ K x) * Valued.v (algebraMap K₀ K δ))
          (Valued.v (algebraMap K₀ K y) * Valued.v (algebraMap K₀ K γ)) := by
      rw [map_sub, map_mul, map_mul, ← Valuation.map_mul, ← Valuation.map_mul]
      exact Valuation.map_sub _ _ _
    refine hdet.trans (h1.trans (max_le_max ?_ ?_))
    · exact mul_le_of_le_one_right' hδ
    · exact mul_le_of_le_one_right' hγ
  by_cases hx0 : x = 0
  ·
    have hy : 1 ≤ Valued.v (algebraMap K₀ K y) := by
      rw [hx0, map_zero, map_zero] at hmax
      simpa using hmax
    rw [hx0, map_zero, zero_mul, zero_add]
    exact (hp2m.trans hpm1).trans hy
  · have hx0' : algebraMap K₀ K x ≠ 0 := by rwa [ne_eq, map_eq_zero]
    have hvx0 : 0 < Valued.v (algebraMap K₀ K x) := zero_lt_iff.2 (by rwa [ne_eq, map_eq_zero])

    have hlin : Valued.v (algebraMap K₀ K x) * p ^ m ≤ Valued.v (algebraMap K₀ K x * w + algebraMap K₀ K y) := by
      have : algebraMap K₀ K x * w + algebraMap K₀ K y = algebraMap K₀ K x * (w - algebraMap K₀ K (-(y / x))) := by
        rw [map_neg, map_div₀, sub_neg_eq_add, mul_add, mul_div_cancel₀ _ hx0']
      rw [this, Valuation.map_mul]
      exact mul_le_mul_right (hw2 _) _
    rcases le_or_gt 1 (Valued.v (algebraMap K₀ K x)) with hx1 | hx1
    ·
      calc p ^ (2 * m) ≤ p ^ m := hp2m
        _ ≤ Valued.v (algebraMap K₀ K x) * p ^ m := le_mul_of_one_le_left' hx1
        _ ≤ _ := hlin
    ·
      have hy : 1 ≤ Valued.v (algebraMap K₀ K y) := by
        rcases le_max_iff.1 hmax with h | h
        · exact absurd h (not_le.2 hx1)
        · exact h
      rcases lt_or_ge (Valued.v (algebraMap K₀ K x * w)) (Valued.v (algebraMap K₀ K y)) with hlt | hge
      · rw [Valuation.map_add_eq_of_lt_right _ hlt]
        exact (hp2m.trans hpm1).trans hy
      ·
        have h1 : (1 : Γ₀) ≤ Valued.v (algebraMap K₀ K x) * p⁻¹ ^ m :=
          hy.trans (hge.trans (by rw [Valuation.map_mul]; exact mul_le_mul_right hw1 _))
        have h2 : p ^ m ≤ Valued.v (algebraMap K₀ K x) := by
          calc p ^ m = 1 * p ^ m := (one_mul _).symm
            _ ≤ (Valued.v (algebraMap K₀ K x) * p⁻¹ ^ m) * p ^ m := mul_le_mul_left h1 _
            _ = Valued.v (algebraMap K₀ K x) := by rw [mul_assoc, P_pow_mul_p_pow, mul_one]
        calc p ^ (2 * m) = p ^ m * p ^ m := by rw [two_mul, pow_add]
          _ ≤ Valued.v (algebraMap K₀ K x) * p ^ m := mul_le_mul_left h2 _
          _ ≤ _ := hlin

theorem row_upper {m : ℕ} {w : K} (hw : Valued.v w ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m) (x y : K₀)
    (hx : Valued.v (algebraMap K₀ K x) ≤ 1) (hy : Valued.v (algebraMap K₀ K y) ≤ 1) :
    Valued.v (algebraMap K₀ K x * w + algebraMap K₀ K y) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m := by
  refine (Valuation.map_add _ _ _).trans (max_le ?_ (hy.trans (one_le_P_pow ϖ m)))
  rw [Valuation.map_mul]
  calc Valued.v (algebraMap K₀ K x) * Valued.v w ≤ 1 * (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m :=
        mul_le_mul' hx hw
    _ = _ := one_mul _

theorem moebius_mem_affinoid_of_integral {m : ℕ} {w : K} (hw : w ∈ affinoid ϖ m) (g : GL (Fin 2) K₀)
    (hint : ∀ i j : Fin 2, Valued.v (algebraMap K₀ K (g i j)) ≤ 1)
    (hdet : Valued.v (algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀))) = 1) :
    moebius K₀ K g w ∈ affinoid ϖ (3 * m) := by
  set p : Γ₀ := Valued.v (algebraMap K₀ K ϖ.ϖ) with hp
  obtain ⟨hw1, hw2⟩ := (mem_affinoid_iff' ϖ m w).1 hw
  have hwΩ : w ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ m hw
  set a := g 0 0 with ha; set b := g 0 1 with hb; set c := g 1 0 with hc; set d := g 1 1 with hd
  have hdet' : Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀) = a * d - b * c := by rw [Matrix.det_fin_two]
  have hcd : algebraMap K₀ K c * w + algebraMap K₀ K d ≠ 0 := moebius_denom_ne_zero_of_mem K₀ hwΩ g
  rw [moebius]

  have hden_lo : p ^ (2 * m) ≤ Valued.v (algebraMap K₀ K c * w + algebraMap K₀ K d) := by
    refine row_lower ϖ hw c d (-a) (-b) ?_ ?_ ?_
    · rw [map_neg, Valuation.map_neg]; exact hint 0 0
    · rw [map_neg, Valuation.map_neg]; exact hint 0 1
    · have : c * -b - d * -a = a * d - b * c := by ring
      rw [this, ← hdet', hdet]
  have hden_up : Valued.v (algebraMap K₀ K c * w + algebraMap K₀ K d) ≤ p⁻¹ ^ m :=
    row_upper ϖ hw1 c d (hint 1 0) (hint 1 1)
  have hden_pos : 0 < Valued.v (algebraMap K₀ K c * w + algebraMap K₀ K d) :=
    lt_of_lt_of_le (pow_pos ϖ.pos _) hden_lo
  have hnum_up : Valued.v (algebraMap K₀ K a * w + algebraMap K₀ K b) ≤ p⁻¹ ^ m :=
    row_upper ϖ hw1 a b (hint 0 0) (hint 0 1)
  rw [mem_affinoid_iff']
  constructor
  ·
    rw [map_div₀, div_le_iff₀ hden_pos]
    refine hnum_up.trans ?_
    calc p⁻¹ ^ m = p⁻¹ ^ (3 * m) * p ^ (2 * m) := by
          rw [show 3 * m = m + 2 * m by ring, pow_add, mul_assoc, P_pow_mul_p_pow, mul_one]
      _ ≤ p⁻¹ ^ (3 * m) * Valued.v (algebraMap K₀ K c * w + algebraMap K₀ K d) := mul_le_mul_right hden_lo _
  · intro t

    have hsub : (algebraMap K₀ K a * w + algebraMap K₀ K b) / (algebraMap K₀ K c * w + algebraMap K₀ K d) -
        algebraMap K₀ K t =
        (algebraMap K₀ K (a - t * c) * w + algebraMap K₀ K (b - t * d)) /
          (algebraMap K₀ K c * w + algebraMap K₀ K d) := by
      rw [eq_div_iff hcd, sub_mul, div_mul_cancel₀ _ hcd, map_sub, map_sub, map_mul, map_mul]; ring
    have hnum_lo : p ^ (2 * m) ≤ Valued.v (algebraMap K₀ K (a - t * c) * w + algebraMap K₀ K (b - t * d)) := by
      refine row_lower ϖ hw (a - t * c) (b - t * d) c d (hint 1 0) (hint 1 1) ?_
      have : (a - t * c) * d - (b - t * d) * c = a * d - b * c := by ring
      rw [this, ← hdet', hdet]
    rw [hsub, map_div₀, le_div_iff₀ hden_pos]
    calc p ^ (3 * m) * Valued.v (algebraMap K₀ K c * w + algebraMap K₀ K d) ≤ p ^ (3 * m) * p⁻¹ ^ m :=
          mul_le_mul_right hden_up _
      _ = p ^ (2 * m) := by
          rw [show 3 * m = 2 * m + m by ring, pow_add, mul_assoc, mul_comm (p ^ m), P_pow_mul_p_pow, mul_one]
      _ ≤ _ := hnum_lo

end Stab

section TreeSide

variable {R₀ K₀ : Type} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Field K₀] [Algebra R₀ K₀]
  [IsFractionRing R₀ K₀]
variable {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

theorem v_det_map_eq_one
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)
    (A : GL (Fin 2) R₀) :
    Valued.v (algebraMap K₀ K
      (Matrix.det ((Matrix.GeneralLinearGroup.map (algebraMap R₀ K₀) A : GL (Fin 2) K₀) :
        Matrix (Fin 2) (Fin 2) K₀))) = 1 := by
  have hD : Matrix.det ((Matrix.GeneralLinearGroup.map (algebraMap R₀ K₀) A : GL (Fin 2) K₀) :
      Matrix (Fin 2) (Fin 2) K₀) = algebraMap R₀ K₀ (Matrix.det (A : Matrix (Fin 2) (Fin 2) R₀)) := by
    have h := Matrix.GeneralLinearGroup.map_det (f := algebraMap R₀ K₀) A
    have h' := congrArg (fun u : K₀ˣ => (u : K₀)) h
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h'
  have hprod : Matrix.det (A : Matrix (Fin 2) (Fin 2) R₀) * Matrix.det ((A⁻¹ : GL (Fin 2) R₀) : Matrix (Fin 2) (Fin 2) R₀)
      = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have h1 : Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ (Matrix.det (A : Matrix (Fin 2) (Fin 2) R₀)))) ≤ 1 :=
    (hR₀ _).1 ⟨_, rfl⟩
  have h2 : Valued.v (algebraMap K₀ K (algebraMap R₀ K₀
      (Matrix.det ((A⁻¹ : GL (Fin 2) R₀) : Matrix (Fin 2) (Fin 2) R₀)))) ≤ 1 :=
    (hR₀ _).1 ⟨_, rfl⟩
  have h12 : Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ (Matrix.det (A : Matrix (Fin 2) (Fin 2) R₀)))) *
      Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ (Matrix.det ((A⁻¹ : GL (Fin 2) R₀) : Matrix (Fin 2) (Fin 2) R₀)))) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, ← map_mul, hprod, map_one, map_one, map_one]
  rw [hD]
  refine le_antisymm h1 ?_
  by_contra hlt
  push Not at hlt
  have : Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ (Matrix.det (A : Matrix (Fin 2) (Fin 2) R₀)))) *
      Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ (Matrix.det ((A⁻¹ : GL (Fin 2) R₀) : Matrix (Fin 2) (Fin 2) R₀)))) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  exact this.ne h12

theorem pmoebius_mem_affinoid_of_smul_stdVertex_eq
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)
    (h : PGL(2, K₀)) (hh : h • LT.LatticeTree.stdVertex R₀ K₀ = LT.LatticeTree.stdVertex R₀ K₀)
    {m : ℕ} {w : K} (hw : w ∈ affinoid ϖ m) :
    pmoebius K₀ h w ∈ affinoid ϖ (3 * m) := by
  induction h using Matrix.ProjGenLinGroup.induction_on with
  | _ g =>

  have hh' : Vertex.act g (LT.LatticeTree.stdVertex R₀ K₀) = LT.LatticeTree.stdVertex R₀ K₀ := hh
  rw [Vertex.act_stdVertex_eq_iff] at hh'
  obtain ⟨c, A, hA⟩ := hh'

  have hmk : Matrix.ProjGenLinGroup.mk g =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (algebraMap R₀ K₀) A : GL (Fin 2) K₀) := by
    rw [hA, map_mul, ← scalar_eq_scalarGL, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
  have hwΩ : w ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ m hw
  rw [hmk, pmoebius_mk K₀ _ w (moebius_denom_ne_zero_of_mem K₀ hwΩ _)]
  refine moebius_mem_affinoid_of_integral ϖ hw _ (fun i j => ?_) (v_det_map_eq_one hR₀ A)
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact (hR₀ _).1 ⟨_, rfl⟩

end TreeSide

section Cocompact

variable {R₀ K₀ : Type} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Field K₀] [Algebra R₀ K₀]
  [IsFractionRing R₀ K₀]
variable {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

theorem exists_forall_exists_smul_mem_affinoid [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)
    (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ) (hex : IsExhausted ϖ)
    (H : Subgroup PGL(2, K₀))
    (hH : Finite (QuotVert ↥H (LT.LatticeTree.Vertex R₀ K₀))) :
    ∃ N : ℕ, ∀ z : ↥(upperHalfPlane K₀ K), ∃ η ∈ H, ((η • z : ↥(upperHalfPlane K₀ K)) : K) ∈ affinoid ϖ N := by
  classical
  have hfin := hfin_of_finite_residueField (K := K) hR₀ ϖ ϖ₀ hϖ₀ hϖ
  set v₀ : LT.LatticeTree.Vertex R₀ K₀ := LT.LatticeTree.stdVertex R₀ K₀ with hv₀
  letI : Fintype (QuotVert ↥H (LT.LatticeTree.Vertex R₀ K₀)) := Fintype.ofFinite _

  let cls : PGL(2, K₀) → QuotVert ↥H (LT.LatticeTree.Vertex R₀ K₀) :=
    fun g => Quotient.mk (MulAction.orbitRel ↥H (LT.LatticeTree.Vertex R₀ K₀)) (g • v₀)

  let rep : QuotVert ↥H (LT.LatticeTree.Vertex R₀ K₀) → PGL(2, K₀) :=
    fun q => if hq : ∃ g, cls g = q then hq.choose else 1
  have hrep : ∀ g : PGL(2, K₀), cls (rep (cls g)) = cls g := fun g => by
    have hq : ∃ g', cls g' = cls g := ⟨g, rfl⟩
    simp only [rep, dif_pos hq]
    exact hq.choose_spec

  let sh : QuotVert ↥H (LT.LatticeTree.Vertex R₀ K₀) → ℕ :=
    fun q => (exists_mapsTo_affinoid ϖ (rep q) 3).choose
  have hsh : ∀ q, Set.MapsTo (pmoebius K₀ (rep q)) (affinoid ϖ 3) (affinoid ϖ (sh q)) :=
    fun q => (exists_mapsTo_affinoid ϖ (rep q) 3).choose_spec
  refine ⟨Finset.univ.sup sh, fun z => ?_⟩

  obtain ⟨n, hzn⟩ := hex z z.2
  obtain ⟨a₀, c, hc0, hw⟩ := exists_sub_div_mem_affinoid_one ϖ hfin hzn
  set w : K := ((z : K) - algebraMap K₀ K a₀) / algebraMap K₀ K c with hwdef
  have hwΩ : w ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ 1 hw
  have hcK : algebraMap K₀ K c ≠ 0 := by rwa [ne_eq, map_eq_zero]
  let gm : GL (Fin 2) K₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, a₀; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simpa using hc0)
  set g : PGL(2, K₀) := Matrix.ProjGenLinGroup.mk gm with hg
  have hgw : pmoebius K₀ g w = (z : K) := by
    have hden : algebraMap K₀ K (gm 1 0) * w + algebraMap K₀ K (gm 1 1) ≠ 0 :=
      moebius_denom_ne_zero_of_mem K₀ hwΩ gm
    rw [hg, pmoebius_mk K₀ gm w hden, moebius]
    simp only [gm, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.val_mk',
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val', map_zero, map_one, zero_mul, zero_add, div_one]
    rw [hwdef, mul_div_cancel₀ _ hcK, sub_add_cancel]

  set q := cls g with hq
  have hcls : cls (rep q) = cls g := hrep g
  have hrel : (MulAction.orbitRel ↥H (LT.LatticeTree.Vertex R₀ K₀)) (rep q • v₀) (g • v₀) := Quotient.exact hcls
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨η, hη⟩ := hrel

  refine ⟨(η : PGL(2, K₀)), η.2, ?_⟩
  set h : PGL(2, K₀) := (rep q)⁻¹ * (η : PGL(2, K₀)) * g with hh
  have hhv : h • v₀ = v₀ := by
    have hη' : ((η : PGL(2, K₀)) * g) • v₀ = rep q • v₀ := by
      rw [mul_smul]; exact hη
    rw [hh, mul_assoc, mul_smul, hη', inv_smul_smul]
  have hηg : (η : PGL(2, K₀)) * g = rep q * h := by rw [hh]; group

  have hcoe : ((((η : PGL(2, K₀)) • z : ↥(upperHalfPlane K₀ K)) : K)) = pmoebius K₀ (rep q) (pmoebius K₀ h w) := by
    rw [coe_smul_upperHalfPlane, ← hgw, ← pmoebius_mul K₀ hwΩ, hηg, pmoebius_mul K₀ hwΩ]
  rw [hcoe]
  have h3 : pmoebius K₀ h w ∈ affinoid ϖ 3 := by
    have := pmoebius_mem_affinoid_of_smul_stdVertex_eq ϖ hR₀ h hhv hw
    simpa using this
  exact affinoid_mono ϖ (Finset.le_sup (Finset.mem_univ q)) (hsh q h3)

end Cocompact

end P2mKcLiouvInv

end

namespace P2mWs50Cocpt

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

theorem finite_quotVert_map
    {R₀ K₀ : Type} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Field K₀] [Algebra R₀ K₀]
    [IsFractionRing R₀ K₀]
    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R₀ K₀)]
    [Mumford.GraphAction G (BruhatTits.tree R₀ K₀)]
    (hact : Mumford.ActsThrough (LT.LatticeTree.Vertex R₀ K₀) ρ)
    (Γ : Subgroup G)
    [Fintype (Mumford.QuotVert Γ (LT.LatticeTree.Vertex R₀ K₀))]
    (Γ'' : Subgroup G) (hle : Γ'' ≤ Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    (hidx : Γ''.relIndex (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) ≠ 0) :
    Finite (Mumford.QuotVert ↥(Γ''.map ρ) (LT.LatticeTree.Vertex R₀ K₀)) := by
  classical

  obtain ⟨hconn, hbip⟩ := CerednikDrinfeld.BruhatTits.tree_connected_and_colorable_two R₀ K₀
  obtain ⟨-, hdvd⟩ := CerednikDrinfeld.Mumford.exists_monoidHom_ker_eq_typePreserving_and_index_dvd_two
    (G := G) (BruhatTits.tree R₀ K₀) hconn hbip (LT.LatticeTree.stdVertex R₀ K₀)
  have htp0 : (Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)).index ≠ 0 :=
    fun h0 => by rw [h0] at hdvd; exact absurd (Nat.eq_zero_of_zero_dvd hdvd) two_ne_zero
  have h2 : (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)).relIndex Γ ≠ 0 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact fun h0 => htp0 (Subgroup.index_eq_zero_of_relIndex_eq_zero h0)
  have hle' : Γ'' ≤ Γ := hle.trans inf_le_left
  have hΓ : Γ''.relIndex Γ ≠ 0 := Subgroup.relIndex_ne_zero_trans hidx h2
  haveI : (Γ''.subgroupOf Γ).FiniteIndex := ⟨hΓ⟩

  let φ : Mumford.QuotVert Γ (LT.LatticeTree.Vertex R₀ K₀) × (↥Γ ⧸ Γ''.subgroupOf Γ) → Mumford.QuotVert ↥(Γ''.map ρ) (LT.LatticeTree.Vertex R₀ K₀) :=
    fun qc => Quotient.mk _ ((((qc.2.out : ↥Γ) : G))⁻¹ • qc.1.out)
  refine Finite.of_surjective φ fun x => ?_
  induction x using Quotient.inductionOn with
  | h u =>

  set q : Mumford.QuotVert Γ (LT.LatticeTree.Vertex R₀ K₀) := Quotient.mk (MulAction.orbitRel ↥Γ (LT.LatticeTree.Vertex R₀ K₀)) u with hq
  have hrep : q.out ∈ MulAction.orbit ↥Γ u := MulAction.orbitRel_apply.mp (Quotient.mk_out u)
  obtain ⟨γ₁, hγ₁⟩ := MulAction.mem_orbit_iff.mp hrep
  have hγ₁' : ((γ₁ : ↥Γ) : G) • u = q.out := hγ₁

  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (s := Γ''.subgroupOf Γ) γ₁
  set c : ↥Γ ⧸ Γ''.subgroupOf Γ := QuotientGroup.mk γ₁ with hc
  have hhG : (((h : ↥(Γ''.subgroupOf Γ)) : ↥Γ) : G) ∈ Γ'' := Subgroup.mem_subgroupOf.mp h.2
  have hcoe : ((c.out : ↥Γ) : G) = ((γ₁ : ↥Γ) : G) * (((h : ↥(Γ''.subgroupOf Γ)) : ↥Γ) : G) := by
    have := congrArg (fun x : ↥Γ => (x : G)) hh
    simpa using this
  refine ⟨(q, c), ?_⟩

  show Quotient.mk _ ((((c.out : ↥Γ) : G))⁻¹ • q.out) = Quotient.mk _ u
  apply Quotient.sound
  refine MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr
    ⟨⟨ρ ((((h : ↥(Γ''.subgroupOf Γ)) : ↥Γ) : G))⁻¹, Subgroup.mem_map.2 ⟨_, Γ''.inv_mem hhG, rfl⟩⟩, ?_⟩)
  show ρ ((((h : ↥(Γ''.subgroupOf Γ)) : ↥Γ) : G))⁻¹ • u = (((c.out : ↥Γ) : G))⁻¹ • q.out
  rw [← hact, hcoe, mul_inv_rev, mul_smul, ← hγ₁', inv_smul_smul]

end P2mWs50Cocpt

open P2mKcLiouvInv P2mWs50Cocpt in
theorem solution

    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)

    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R₀ K₀)]
    [Mumford.GraphAction G (BruhatTits.tree R₀ K₀)]
    (hact : Mumford.ActsThrough (LT.LatticeTree.Vertex R₀ K₀) ρ)

    (Γ : Subgroup G)
    [Fintype (Mumford.QuotVert Γ (LT.LatticeTree.Vertex R₀ K₀))]
    (Γ'' : Subgroup G) (hle : Γ'' ≤ Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    (hidx : Γ''.relIndex (Γ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) ≠ 0) :
    ∃ N : ℕ, ∀ z : ↥(Omega.upperHalfPlane K₀ K), ∃ γ ∈ Γ'',
      ((ρ γ • z : ↥(Omega.upperHalfPlane K₀ K)) : K) ∈ Omega.affinoid ϖ N := by
  have hfinq := finite_quotVert_map G ρ hact Γ Γ'' hle hidx
  obtain ⟨N, hN⟩ := exists_forall_exists_smul_mem_affinoid ϖ hR₀ ϖ₀ hϖ₀ hϖ hex (Γ''.map ρ) hfinq
  refine ⟨N, fun z => ?_⟩
  obtain ⟨η, hη, hηz⟩ := hN z
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hη
  exact ⟨γ, hγ, hηz⟩

end S_CerednikDrinfeld_Omega_exists_forall_exists_smul_mem_affinoid_of_relIndex_ne_zero
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_forall_exists_smul_mem_affinoid_of_relIndex_ne_zero (solution)
