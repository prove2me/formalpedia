-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_valuations_invariantFieldOf_of_finite_quotVert
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/25d9025e-1cce-5102-8580-c4f4801ef97d

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Theorems.Thm_CerednikDrinfeld_Omega_ordAt_mul
import Theorems.Thm_CerednikDrinfeld_Omega_coordSub_dvd_of_apply_eq_zero
import Theorems.Thm_CerednikDrinfeld_Omega_bddAbove_setOf_coordSub_pow_dvd
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero
import Theorems.Thm_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_of_mem_holOn_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_exists_smul_mem_affinoid_of_relIndex_ne_zero
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_forall_smul_eq_of_forall_exists_smul_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_dvd_of_forall_ordAt_le
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_valuations_invariantFieldOf_of_finite_quotVert
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups WithZero
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace P2mKcValCpt

section Powers

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

theorem algebraMap_varpi_ne_zero : algebraMap K₀ K ϖ.ϖ ≠ 0 := fun h => by
  have := ϖ.pos
  rw [h, map_zero] at this
  exact lt_irrefl _ this

theorem varpi_ne_zero : ϖ.ϖ ≠ 0 := fun h => algebraMap_varpi_ne_zero ϖ (by rw [h, map_zero])

theorem P_pow_mul_p_pow (i : ℕ) :
    (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ i * Valued.v (algebraMap K₀ K ϖ.ϖ) ^ i = 1 := by
  rw [← mul_pow, inv_mul_cancel₀ ϖ.pos.ne', one_pow]

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

section OrdAt

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

local notation "Ω" => upperHalfPlane K₀ K

theorem apply_eq_zero_of_coordSub_dvd {F : ↥(holRing ϖ)} {z : ↥Ω} (h : coordSub ϖ z ∣ F) :
    (F : ↥Ω → K) z = 0 := by
  obtain ⟨G, rfl⟩ := h
  show ((coordSub ϖ z : ↥(holRing ϖ)) : ↥Ω → K) z * (G : ↥Ω → K) z = 0
  rw [coordSub_apply_self, zero_mul]

theorem apply_eq_zero_of_pow_dvd {F : ↥(holRing ϖ)} {z : ↥Ω} {n : ℕ} (hn : n ≠ 0)
    (h : coordSub ϖ z ^ n ∣ F) : (F : ↥Ω → K) z = 0 :=
  apply_eq_zero_of_coordSub_dvd ϖ ((dvd_pow_self _ hn).trans h)

theorem ordAt_eq_zero_of_apply_ne_zero {F : ↥(holRing ϖ)} {z : ↥Ω} (h : (F : ↥Ω → K) z ≠ 0) :
    ordAt ϖ F z = 0 := by
  apply Nat.le_zero.1
  refine ordAt_le_of_forall_le ϖ F z 0 fun n hn => ?_
  by_contra hn0
  exact h (apply_eq_zero_of_pow_dvd ϖ (by omega) hn)

theorem coordSub_ne_zero [Nontrivial K] (z : ↥Ω) (hΩ : ∃ w : ↥Ω, (w : K) ≠ z) : coordSub ϖ z ≠ 0 := by
  obtain ⟨w, hw⟩ := hΩ
  intro h
  have := congrArg (fun F : ↥(holRing ϖ) => (F : ↥Ω → K) w) h
  simp only [coordSub_apply] at this
  exact hw (sub_eq_zero.1 this)

variable [CompleteSpace K] [IsAlgClosed K]
variable (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
variable (hex : IsExhausted ϖ)
variable (hlf : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
  Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
    ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)

include hrk hex hlf in

theorem le_ordAt_of_dvd {F : ↥(holRing ϖ)} (hF : F ≠ 0) (z : ↥Ω) {n : ℕ} (hn : coordSub ϖ z ^ n ∣ F) :
    n ≤ ordAt ϖ F z := by
  classical
  exact le_ordAt_of_pow_dvd ϖ F z hn
    (CerednikDrinfeld.Omega.bddAbove_setOf_coordSub_pow_dvd K₀ K hrk ϖ hex hlf F hF z)

include hrk hex hlf in
theorem pow_ordAt_dvd {F : ↥(holRing ϖ)} (hF : F ≠ 0) (z : ↥Ω) : coordSub ϖ z ^ ordAt ϖ F z ∣ F := by
  classical
  exact Nat.sSup_mem ⟨0, zero_mem_setOf_pow_dvd ϖ F z⟩
    (CerednikDrinfeld.Omega.bddAbove_setOf_coordSub_pow_dvd K₀ K hrk ϖ hex hlf F hF z)

include hrk hex in

theorem one_le_ordAt_of_apply_eq_zero {F : ↥(holRing ϖ)} (hF : F ≠ 0) (z : ↥Ω) (h0 : (F : ↥Ω → K) z = 0)
    (hlf : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n) :
    1 ≤ ordAt ϖ F z := by
  refine le_ordAt_of_dvd ϖ hrk hex hlf hF z ?_
  rw [pow_one]
  exact CerednikDrinfeld.Omega.coordSub_dvd_of_apply_eq_zero K₀ K ϖ hrk hex F z h0

include hrk hex hlf in

theorem min_ordAt_le_ordAt_add {F G : ↥(holRing ϖ)} (hFG : F + G ≠ 0) (hF : F ≠ 0) (hG : G ≠ 0) (z : ↥Ω) :
    min (ordAt ϖ F z) (ordAt ϖ G z) ≤ ordAt ϖ (F + G) z := by
  refine le_ordAt_of_dvd ϖ hrk hex hlf hFG z ?_
  refine dvd_add ?_ ?_
  · exact (pow_dvd_pow _ (min_le_left _ _)).trans (pow_ordAt_dvd ϖ hrk hex hlf hF z)
  · exact (pow_dvd_pow _ (min_le_right _ _)).trans (pow_ordAt_dvd ϖ hrk hex hlf hG z)

end OrdAt

section OrdVal

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)
variable [CompleteSpace K] [IsAlgClosed K]
variable (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
variable (hex : IsExhausted ϖ)
variable (hlf : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
  Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
    ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)

local notation "Ω" => upperHalfPlane K₀ K

def ordFun (z : ↥Ω) (F : ↥(holRing ϖ)) : ℤᵐ⁰ :=
  by classical exact if F = 0 then 0 else WithZero.exp (-(ordAt ϖ F z : ℤ))

theorem ordFun_zero (z : ↥Ω) : ordFun ϖ z 0 = 0 := by simp [ordFun]

theorem ordFun_of_ne_zero (z : ↥Ω) {F : ↥(holRing ϖ)} (hF : F ≠ 0) :
    ordFun ϖ z F = WithZero.exp (-(ordAt ϖ F z : ℤ)) := by simp [ordFun, hF]

theorem ordFun_ne_zero (z : ↥Ω) {F : ↥(holRing ϖ)} (hF : F ≠ 0) : ordFun ϖ z F ≠ 0 := by
  rw [ordFun_of_ne_zero ϖ z hF]; exact WithZero.exp_ne_zero

include hrk hex hlf in

def ordVal [IsDomain ↥(holRing ϖ)] (z : ↥Ω) : Valuation ↥(holRing ϖ) ℤᵐ⁰ where
  toFun := ordFun ϖ z
  map_zero' := ordFun_zero ϖ z
  map_one' := by
    rw [ordFun_of_ne_zero ϖ z one_ne_zero, ordAt_eq_zero_of_apply_ne_zero ϖ (by simp)]
    simp
  map_mul' F G := by
    by_cases hF : F = 0
    · rw [hF, zero_mul, ordFun_zero, zero_mul]
    by_cases hG : G = 0
    · rw [hG, mul_zero, ordFun_zero, mul_zero]
    rw [ordFun_of_ne_zero ϖ z hF, ordFun_of_ne_zero ϖ z hG, ordFun_of_ne_zero ϖ z (mul_ne_zero hF hG),
      CerednikDrinfeld.Omega.ordAt_mul K₀ K ϖ hrk hex hlf F G hF hG z, ← WithZero.exp_add]
    congr 1
    push_cast
    ring
  map_add_le_max' F G := by
    by_cases hFG : F + G = 0
    · rw [hFG, ordFun_zero]; exact zero_le'
    by_cases hF : F = 0
    · rw [hF, zero_add, ordFun_zero]; exact le_max_right _ _
    by_cases hG : G = 0
    · rw [hG, add_zero, ordFun_zero]; exact le_max_left _ _
    rw [ordFun_of_ne_zero ϖ z hF, ordFun_of_ne_zero ϖ z hG, ordFun_of_ne_zero ϖ z hFG]
    have h := min_ordAt_le_ordAt_add ϖ hrk hex hlf hFG hF hG z
    rcases min_le_iff.1 h with h | h
    · exact le_max_of_le_left (WithZero.exp_le_exp.2 (by omega))
    · exact le_max_of_le_right (WithZero.exp_le_exp.2 (by omega))

theorem ordVal_apply [IsDomain ↥(holRing ϖ)] (z : ↥Ω) (F : ↥(holRing ϖ)) :
    ordVal ϖ hrk hex hlf z F = ordFun ϖ z F := rfl

variable [DecidableEq K]

include hrk hex in

theorem coordSub_smul_dvd (γ : PGL(2, K₀)) (z : ↥Ω) : coordSub ϖ (γ • z) ∣ γ • coordSub ϖ z := by
  refine CerednikDrinfeld.Omega.coordSub_dvd_of_apply_eq_zero K₀ K ϖ hrk hex _ _ ?_
  rw [coe_smul_holRing_apply, inv_smul_smul, coordSub_apply_self]

include hrk hex in

theorem smul_coordSub_dvd (γ : PGL(2, K₀)) (z : ↥Ω) : γ • coordSub ϖ z ∣ coordSub ϖ (γ • z) := by
  have h : coordSub ϖ z ∣ γ⁻¹ • coordSub ϖ (γ • z) := by
    refine CerednikDrinfeld.Omega.coordSub_dvd_of_apply_eq_zero K₀ K ϖ hrk hex _ _ ?_
    rw [coe_smul_holRing_apply, inv_inv, coordSub_apply_self]
  obtain ⟨H, hH⟩ := h
  refine ⟨γ • H, ?_⟩
  rw [← smul_mul', ← hH, smul_inv_smul]

include hrk hex in
theorem pow_dvd_smul_iff (γ : PGL(2, K₀)) (z : ↥Ω) (F : ↥(holRing ϖ)) (n : ℕ) :
    coordSub ϖ (γ • z) ^ n ∣ γ • F ↔ coordSub ϖ z ^ n ∣ F := by
  constructor
  · rintro ⟨G, hG⟩
    obtain ⟨H, hH⟩ := coordSub_smul_dvd ϖ hrk hex γ⁻¹ (γ • z)
    rw [inv_smul_smul] at hH
    refine ⟨H ^ n * γ⁻¹ • G, ?_⟩
    calc F = γ⁻¹ • (γ • F) := (inv_smul_smul γ F).symm
      _ = (γ⁻¹ • coordSub ϖ (γ • z)) ^ n * γ⁻¹ • G := by rw [hG, smul_mul', smul_pow']
      _ = coordSub ϖ z ^ n * (H ^ n * γ⁻¹ • G) := by rw [hH, mul_pow, mul_assoc]
  · rintro ⟨G, hG⟩
    obtain ⟨H, hH⟩ := coordSub_smul_dvd ϖ hrk hex γ z
    refine ⟨H ^ n * γ • G, ?_⟩
    calc γ • F = (γ • coordSub ϖ z) ^ n * γ • G := by rw [hG, smul_mul', smul_pow']
      _ = coordSub ϖ (γ • z) ^ n * (H ^ n * γ • G) := by rw [hH, mul_pow, mul_assoc]

include hrk hex in

theorem ordAt_smul (γ : PGL(2, K₀)) (F : ↥(holRing ϖ)) (z : ↥Ω) : ordAt ϖ (γ • F) (γ • z) = ordAt ϖ F z := by
  rw [ordAt_def, ordAt_def]
  congr 1
  ext n
  exact pow_dvd_smul_iff ϖ hrk hex γ z F n

end OrdVal

section Frac

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)
variable {G : Type} [Group G] (ρ : G →* PGL(2, K₀))

local notation "Ω" => upperHalfPlane K₀ K
local notation "𝓞" => HolRingOf ϖ ρ
local notation "𝓚" => FractionRing (HolRingOf ϖ ρ)

def toHol : 𝓞 →+* ↥(holRing ϖ) where
  toFun F := F
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toHol_apply (F : 𝓞) : toHol ϖ ρ F = (show ↥(holRing ϖ) from F) := rfl

theorem toHol_injective : Function.Injective (toHol ϖ ρ) := fun _ _ h => h

theorem toHol_smul (g : G) (F : 𝓞) : toHol ϖ ρ (g • F) = ρ g • toHol ϖ ρ F := rfl

theorem toHol_algebraMap (c : K) : toHol ϖ ρ (algebraMap K 𝓞 c) = algebraMap K ↥(holRing ϖ) c := rfl

theorem toHol_ne_zero {F : 𝓞} : toHol ϖ ρ F ≠ 0 ↔ F ≠ 0 :=
  (map_ne_zero_iff _ (toHol_injective ϖ ρ))

theorem toHol_surjective : Function.Surjective (toHol ϖ ρ) := fun F => ⟨F, rfl⟩

variable [CompleteSpace K] [IsAlgClosed K]
variable (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
variable (hex : IsExhausted ϖ)
variable (hlf : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
  Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
    ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
variable [IsDomain (HolRingOf ϖ ρ)]

omit [DecidableEq K] [CompleteSpace K] [IsAlgClosed K] [IsDomain (HolRingOf ϖ ρ)] in
theorem isDomain_holRing_of (ρ' : G →* PGL(2, K₀)) [IsDomain (HolRingOf ϖ ρ')] : IsDomain ↥(holRing ϖ) :=
  (HolRingOf.isDomain_iff ϖ ρ').1 inferInstance

def ordValOf (z : ↥Ω) : Valuation 𝓞 ℤᵐ⁰ :=
  (@ordVal K₀ _ K _ _ Γ₀ _ _ ϖ _ _ hrk hex hlf (isDomain_holRing_of ϖ ρ) z).comap (toHol ϖ ρ)

theorem ordValOf_apply (z : ↥Ω) (F : 𝓞) : ordValOf ϖ ρ hrk hex hlf z F = ordFun ϖ z (toHol ϖ ρ F) := rfl

theorem ordValOf_ne_zero (z : ↥Ω) {F : 𝓞} (hF : F ≠ 0) : ordValOf ϖ ρ hrk hex hlf z F ≠ 0 :=
  ordFun_ne_zero ϖ z ((toHol_ne_zero ϖ ρ).2 hF)

theorem le_supp (z : ↥Ω) : nonZeroDivisors 𝓞 ≤ (ordValOf ϖ ρ hrk hex hlf z).supp.primeCompl := by
  intro F hF
  show F ∉ (ordValOf ϖ ρ hrk hex hlf z).supp
  rw [Valuation.mem_supp_iff]
  exact ordValOf_ne_zero ϖ ρ hrk hex hlf z (nonZeroDivisors.ne_zero hF)

def merVal (z : ↥Ω) : Valuation 𝓚 ℤᵐ⁰ :=
  (ordValOf ϖ ρ hrk hex hlf z).extendToLocalization (le_supp ϖ ρ hrk hex hlf z) 𝓚

theorem merVal_algebraMap (z : ↥Ω) (F : 𝓞) :
    merVal ϖ ρ hrk hex hlf z (algebraMap 𝓞 𝓚 F) = ordFun ϖ z (toHol ϖ ρ F) :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ F

theorem merVal_div (z : ↥Ω) (a b : 𝓞) :
    merVal ϖ ρ hrk hex hlf z (algebraMap 𝓞 𝓚 a / algebraMap 𝓞 𝓚 b) =
      ordFun ϖ z (toHol ϖ ρ a) / ordFun ϖ z (toHol ϖ ρ b) := by
  rw [map_div₀, merVal_algebraMap, merVal_algebraMap]

theorem merVal_div_eq_exp (z : ↥Ω) {a b : 𝓞} (ha : a ≠ 0) (hb : b ≠ 0) :
    merVal ϖ ρ hrk hex hlf z (algebraMap 𝓞 𝓚 a / algebraMap 𝓞 𝓚 b) =
      WithZero.exp ((ordAt ϖ (toHol ϖ ρ b) z : ℤ) - (ordAt ϖ (toHol ϖ ρ a) z : ℤ)) := by
  rw [merVal_div, ordFun_of_ne_zero ϖ z ((toHol_ne_zero ϖ ρ).2 ha),
    ordFun_of_ne_zero ϖ z ((toHol_ne_zero ϖ ρ).2 hb), ← WithZero.exp_sub]
  congr 1
  ring

omit [CompleteSpace K] [IsAlgClosed K] in

theorem smul_div_algebraMap (g : G) (a b : 𝓞) :
    g • (algebraMap 𝓞 𝓚 a / algebraMap 𝓞 𝓚 b) = algebraMap 𝓞 𝓚 (g • a) / algebraMap 𝓞 𝓚 (g • b) := by
  rw [div_eq_mul_inv, smul_mul', smul_inv'', frac_smul_algebraMap, frac_smul_algebraMap, div_eq_mul_inv]

omit [CompleteSpace K] [IsAlgClosed K] [IsDomain (HolRingOf ϖ ρ)] in
theorem smul_ne_zero_of_ne_zero (g : G) {a : 𝓞} (ha : a ≠ 0) : g • a ≠ 0 := fun h => by
  apply ha
  have := congrArg (fun x : 𝓞 => g⁻¹ • x) h
  simpa using this

theorem merVal_smul_eq (Δ : Subgroup G) {x : 𝓚} (hx : x ∈ invariantFieldOf K G 𝓞 Δ) {γ : G} (hγ : γ ∈ Δ)
    (z : ↥Ω) : merVal ϖ ρ hrk hex hlf (ρ γ • z) x = merVal ϖ ρ hrk hex hlf z x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  by_cases ha0 : a = 0
  · simp [ha0]

  have hinv := (mem_invariantFieldOf_iff K G 𝓞 Δ _).1 hx γ hγ
  rw [smul_div_algebraMap] at hinv
  have hγb0 : γ • b ≠ 0 := smul_ne_zero_of_ne_zero ϖ ρ γ hb0
  have hγa0 : γ • a ≠ 0 := smul_ne_zero_of_ne_zero ϖ ρ γ ha0
  have hne : (algebraMap 𝓞 𝓚 b) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hne' : (algebraMap 𝓞 𝓚 (γ • b)) ≠ 0 := fun h => hγb0 ((IsFractionRing.injective 𝓞 𝓚) (by rw [h, map_zero]))
  rw [div_eq_div_iff hne' hne, ← map_mul, ← map_mul] at hinv
  have hM : (γ • a) * b = a * (γ • b) := IsFractionRing.injective 𝓞 𝓚 hinv

  have hord := congrArg (fun F : 𝓞 => ordAt ϖ (toHol ϖ ρ F) (ρ γ • z)) hM
  simp only [map_mul, toHol_smul] at hord
  have ha1 : toHol ϖ ρ a ≠ 0 := (toHol_ne_zero ϖ ρ).2 ha0
  have hb1 : toHol ϖ ρ b ≠ 0 := (toHol_ne_zero ϖ ρ).2 hb0
  have hγa1 : ρ γ • toHol ϖ ρ a ≠ 0 := (toHol_ne_zero ϖ ρ).2 hγa0
  have hγb1 : ρ γ • toHol ϖ ρ b ≠ 0 := (toHol_ne_zero ϖ ρ).2 hγb0
  rw [CerednikDrinfeld.Omega.ordAt_mul K₀ K ϖ hrk hex hlf _ _ hγa1 hb1,
    CerednikDrinfeld.Omega.ordAt_mul K₀ K ϖ hrk hex hlf _ _ ha1 hγb1,
    ordAt_smul ϖ hrk hex (ρ γ) _ z, ordAt_smul ϖ hrk hex (ρ γ) _ z] at hord
  rw [merVal_div_eq_exp ϖ ρ hrk hex hlf _ ha0 hb0, merVal_div_eq_exp ϖ ρ hrk hex hlf z ha0 hb0]
  congr 1
  omega

def ofHol : ↥(holRing ϖ) →+* 𝓞 where
  toFun F := F
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

omit [CompleteSpace K] [IsAlgClosed K] [IsDomain (HolRingOf ϖ ρ)] in
@[scoped simp] theorem toHol_ofHol (F : ↥(holRing ϖ)) : toHol ϖ ρ (ofHol ϖ ρ F) = F := rfl

omit [CompleteSpace K] [IsAlgClosed K] [IsDomain (HolRingOf ϖ ρ)] in
@[scoped simp] theorem ofHol_toHol (F : 𝓞) : ofHol ϖ ρ (toHol ϖ ρ F) = F := rfl

omit [CompleteSpace K] [IsAlgClosed K] [IsDomain (HolRingOf ϖ ρ)] in
theorem ofHol_smul (g : G) (F : ↥(holRing ϖ)) : ofHol ϖ ρ (ρ g • F) = g • ofHol ϖ ρ F := rfl

omit [CompleteSpace K] [IsAlgClosed K] [IsDomain (HolRingOf ϖ ρ)] in
theorem ofHol_algebraMap (c : K) : ofHol ϖ ρ (algebraMap K ↥(holRing ϖ) c) = algebraMap K 𝓞 c := rfl

omit [DecidableEq K] [CompleteSpace K] [IsAlgClosed K] in
theorem algebraMap_frac_eq (ρ' : G →* PGL(2, K₀)) [IsDomain (HolRingOf ϖ ρ')] (c : K) :
    algebraMap K (FractionRing (HolRingOf ϖ ρ')) c =
      algebraMap (HolRingOf ϖ ρ') (FractionRing (HolRingOf ϖ ρ')) (algebraMap K (HolRingOf ϖ ρ') c) :=
  IsScalarTower.algebraMap_apply K (HolRingOf ϖ ρ') (FractionRing (HolRingOf ϖ ρ')) c

theorem merVal_div_ofHol (z : ↥Ω) (a b : ↥(holRing ϖ)) :
    merVal ϖ ρ hrk hex hlf z (algebraMap 𝓞 𝓚 (ofHol ϖ ρ a) / algebraMap 𝓞 𝓚 (ofHol ϖ ρ b)) =
      ordFun ϖ z a / ordFun ϖ z b := by
  rw [merVal_div]; rfl

theorem merVal_algebraMap_const (z : ↥Ω) {c : K} (hc : c ≠ 0) :
    merVal ϖ ρ hrk hex hlf z (algebraMap K 𝓚 c) = 1 := by
  rw [algebraMap_frac_eq, merVal_algebraMap, toHol_algebraMap,
    ordFun_of_ne_zero ϖ z (by
      intro h
      have := congrArg (fun F : ↥(holRing ϖ) => (F : ↥Ω → K) z) h
      simp only [algebraMap_holRing_apply] at this
      exact hc this),
    ordAt_eq_zero_of_apply_ne_zero ϖ (by rw [algebraMap_holRing_apply]; exact hc)]
  simp

end Frac

section Identity

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)
variable [CompleteSpace K] [IsAlgClosed K]
variable (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
variable (hex : IsExhausted ϖ)
variable (hlf : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
  Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
    ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)

local notation "Ω" => upperHalfPlane K₀ K

omit [CompleteSpace K] [IsAlgClosed K] in

theorem mem_affinoid_of_v_sub_lt {n : ℕ} {w₀ : K} (hw₀ : w₀ ∈ affinoid ϖ n) {ζ : K}
    (hζ : Valued.v (ζ - w₀) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n) : ζ ∈ affinoid ϖ n := by
  obtain ⟨h1, h2⟩ := (mem_affinoid_iff' ϖ n w₀).1 hw₀
  have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n ≤ 1 := pow_le_one₀ zero_le' ϖ.lt_one.le
  have hP1 : (1 : Γ₀) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n :=
    one_le_pow₀ ((one_le_inv₀ ϖ.pos).2 ϖ.lt_one.le)
  rw [mem_affinoid_iff']
  refine ⟨?_, fun a => ?_⟩
  · rw [show ζ = (ζ - w₀) + w₀ by ring]
    exact (Valuation.map_add _ _ _).trans (max_le (hζ.le.trans (hp1.trans hP1)) h1)
  · have hlt : Valued.v (ζ - w₀) < Valued.v (w₀ - algebraMap K₀ K a) := hζ.trans_le (h2 a)
    rw [show ζ - algebraMap K₀ K a = (ζ - w₀) + (w₀ - algebraMap K₀ K a) by ring,
      Valuation.map_add_eq_of_lt_right _ hlt]
    exact h2 a

include hrk hex hlf in

theorem restrictAffinoid_ne_zero {F : ↥(holRing ϖ)} (hF : F ≠ 0) (n : ℕ) (hne : (affinoid ϖ n).Nonempty) :
    restrictAffinoid ϖ n (F : ↥Ω → K) ≠ 0 := by
  intro h0
  obtain ⟨w₀, hw₀⟩ := hne
  apply hF
  apply Subtype.ext
  funext z
  obtain ⟨m, hm⟩ := hex (z : K) z.2
  set k := max m n with hk
  have hzk : (z : K) ∈ affinoid ϖ k := affinoid_mono ϖ (le_max_left m n) hm
  have hw₀k : w₀ ∈ affinoid ϖ k := affinoid_mono ϖ (le_max_right m n) hw₀
  have hg : restrictAffinoid ϖ k (F : ↥Ω → K) ∈ holOn K (affinoid ϖ k) := F.2 k
  have hc : (algebraMap K₀ K ϖ.ϖ) ^ n ≠ 0 := pow_ne_zero n (algebraMap_varpi_ne_zero ϖ)
  have hzero := CerednikDrinfeld.Omega.eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero K₀ K ϖ hrk k
    (hlf k) hg hw₀k hc (fun ζ hζ => by
      rw [Valuation.map_pow] at hζ
      have hζn : (ζ : K) ∈ affinoid ϖ n := mem_affinoid_of_v_sub_lt ϖ hw₀ hζ
      have := congrArg (fun g : ↥(affinoid ϖ n) → K => g ⟨ζ, hζn⟩) h0
      simpa [restrictAffinoid] using this)
  have := congrArg (fun g : ↥(affinoid ϖ k) → K => g ⟨z, hzk⟩) hzero
  simpa [restrictAffinoid] using this

end Identity

end P2mKcValCpt
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_valuations_invariantFieldOf_of_finite_quotVert.P2mKcValCpt"

open P2mKcValCpt in
theorem solution

    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace K] [IsAlgClosed K]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)

    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [MulAction G (LT.LatticeTree.Vertex R₀ K₀)]
    [Mumford.GraphAction G (BruhatTits.tree R₀ K₀)]
    (hact : Mumford.ActsThrough (LT.LatticeTree.Vertex R₀ K₀) ρ)
    [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Δ : Subgroup G)
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Δ.map ρ)) d))
    [Finite (Mumford.QuotVert Δ (LT.LatticeTree.Vertex R₀ K₀))] :
    ∃ V : Set (Valuation ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ) ℤᵐ⁰),
      (∀ v ∈ V, ∀ c : K, c ≠ 0 →
        v (algebraMap K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ) c) = 1) ∧
      (∀ v ∈ V, ∀ f : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ), v f = 1 →
        ∃ c : K, v (f - algebraMap K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ) c) < 1) ∧
      (∀ f : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ), f ≠ 0 → {v ∈ V | 1 < v f}.Finite) ∧
      (∀ f : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ), (∀ v ∈ V, v f ≤ 1) →
        f ∈ Set.range (algebraMap K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ))) := by
  classical

  have hlf := hfin_of_finite_residueField (K := K) hR₀ ϖ ϖ₀ hϖ₀ hϖ
  letI : Fintype (Mumford.QuotVert Δ (LT.LatticeTree.Vertex R₀ K₀)) := Fintype.ofFinite _
  obtain ⟨N, hN⟩ :=
    CerednikDrinfeld.Omega.exists_forall_exists_smul_mem_affinoid_of_relIndex_ne_zero K₀ K R₀ hR₀ ϖ ϖ₀ hϖ₀ hϖ hex
      G ρ hact Δ (Δ ⊓ Mumford.typePreserving G (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀)) le_rfl
      (by rw [Subgroup.relIndex_self]; exact one_ne_zero)
  have hcpt : ∀ z : ↥(upperHalfPlane K₀ K), ∃ γ ∈ Δ,
      ((ρ γ • z : ↥(upperHalfPlane K₀ K)) : K) ∈ affinoid ϖ N := fun z => by
    obtain ⟨γ, hγ, h⟩ := hN z
    exact ⟨γ, (Subgroup.mem_inf.1 hγ).1, h⟩

  let vK : ↥(upperHalfPlane K₀ K) → Valuation ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ) ℤᵐ⁰ := fun z =>
    (merVal ϖ ρ hrk hex hlf z).comap ((Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ).subtype)
  have vK_apply : ∀ (z : ↥(upperHalfPlane K₀ K)) (f : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ)), vK z f = merVal ϖ ρ hrk hex hlf z (f : FractionRing (HolRingOf ϖ ρ)) :=
    fun _ _ => rfl

  have vK_smul : ∀ (z : ↥(upperHalfPlane K₀ K)) (γ : G), γ ∈ Δ → vK (ρ γ • z) = vK z := fun z γ hγ =>
    Valuation.ext fun f => by
      rw [vK_apply, vK_apply]
      exact merVal_smul_eq ϖ ρ hrk hex hlf Δ f.2 hγ z

  have hquot : ∀ f : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ), ∃ a b : HolRingOf ϖ ρ, b ≠ 0 ∧
      (f : FractionRing (HolRingOf ϖ ρ)) = algebraMap _ _ a / algebraMap _ _ b := fun f => by
    obtain ⟨a, b, hb, h⟩ := IsFractionRing.div_surjective (A := HolRingOf ϖ ρ) (f : FractionRing (HolRingOf ϖ ρ))
    exact ⟨a, b, nonZeroDivisors.ne_zero hb, h.symm⟩
  refine ⟨Set.range vK, ?_, ?_, ?_, ?_⟩
  ·
    rintro v ⟨z, rfl⟩ c hc
    rw [vK_apply]
    exact merVal_algebraMap_const ϖ ρ hrk hex hlf z hc
  ·
    rintro v ⟨z, rfl⟩ f hf
    obtain ⟨a, b, hb0, hab⟩ := hquot f
    rw [vK_apply, hab] at hf
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_div, map_zero] at hf
      exact zero_ne_one hf
    rw [merVal_div_eq_exp ϖ ρ hrk hex hlf z ha0 hb0, ← WithZero.exp_zero, WithZero.exp_inj] at hf

    obtain ⟨a', ha', ha'z⟩ :=
      CerednikDrinfeld.Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero K₀ K hrk ϖ hex hlf
        (toHol ϖ ρ a) ((toHol_ne_zero ϖ ρ).2 ha0) z
    obtain ⟨b', hb', hb'z⟩ :=
      CerednikDrinfeld.Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero K₀ K hrk ϖ hex hlf
        (toHol ϖ ρ b) ((toHol_ne_zero ϖ ρ).2 hb0) z
    set m := ordAt ϖ (toHol ϖ ρ a) z with hm
    have hm' : ordAt ϖ (toHol ϖ ρ b) z = m := by omega
    rw [hm'] at hb'

    set c : K := (a' : ↥(upperHalfPlane K₀ K) → K) z / (b' : ↥(upperHalfPlane K₀ K) → K) z with hc
    refine ⟨c, ?_⟩

    set T := algebraMap (HolRingOf ϖ ρ) (FractionRing (HolRingOf ϖ ρ)) (ofHol ϖ ρ (coordSub ϖ z)) with hT
    set A' := algebraMap (HolRingOf ϖ ρ) (FractionRing (HolRingOf ϖ ρ)) (ofHol ϖ ρ a') with hA'
    set B' := algebraMap (HolRingOf ϖ ρ) (FractionRing (HolRingOf ϖ ρ)) (ofHol ϖ ρ b') with hB'
    have haA : algebraMap (HolRingOf ϖ ρ) (FractionRing (HolRingOf ϖ ρ)) a = T ^ m * A' := by
      rw [hT, hA', ← map_pow, ← map_mul, ← map_pow, ← map_mul, ← ha', ofHol_toHol]
    have hbB : algebraMap (HolRingOf ϖ ρ) (FractionRing (HolRingOf ϖ ρ)) b = T ^ m * B' := by
      rw [hT, hB', ← map_pow, ← map_mul, ← map_pow, ← map_mul, ← hb', ofHol_toHol]
    have hTm : T ^ m ≠ 0 := by
      intro h0
      apply ha0
      apply IsFractionRing.injective (HolRingOf ϖ ρ) (FractionRing (HolRingOf ϖ ρ))
      rw [haA, h0, zero_mul, map_zero]
    have hB'0 : B' ≠ 0 := by
      intro h0
      apply hb0
      apply IsFractionRing.injective (HolRingOf ϖ ρ) (FractionRing (HolRingOf ϖ ρ))
      rw [hbB, h0, mul_zero, map_zero]
    have hfrac : (f : FractionRing (HolRingOf ϖ ρ)) = A' / B' := by
      rw [hab, haA, hbB, mul_div_mul_left _ _ hTm]

    have hsub : ((f - algebraMap K ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ) c : ↥(Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Δ)) : FractionRing (HolRingOf ϖ ρ)) =
        algebraMap (HolRingOf ϖ ρ) (FractionRing (HolRingOf ϖ ρ))
            (ofHol ϖ ρ (a' - algebraMap K ↥(holRing ϖ) c * b')) / B' := by
      rw [Subfield.coe_sub, hfrac, Mumford.algebraMap_invariantFieldOf_coe, algebraMap_frac_eq,
        map_sub, map_mul, ofHol_algebraMap, map_sub, map_mul, sub_div, hB', mul_div_cancel_right₀ _ hB'0]
    rw [vK_apply, hsub, hB', merVal_div_ofHol]
    by_cases hnum : a' - algebraMap K ↥(holRing ϖ) c * b' = 0
    · rw [hnum, ordFun_zero, zero_div]; exact zero_lt_one
    have hb'0 : b' ≠ 0 := by
      intro h; apply hb'z; rw [h]; rfl
    rw [ordFun_of_ne_zero ϖ z hnum, ordFun_of_ne_zero ϖ z hb'0, ordAt_eq_zero_of_apply_ne_zero ϖ hb'z,
      ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    have hvan : ((a' - algebraMap K ↥(holRing ϖ) c * b' : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) z = 0 := by
      show (a' : ↥(upperHalfPlane K₀ K) → K) z -
          ((algebraMap K ↥(holRing ϖ) c : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) z *
            (b' : ↥(upperHalfPlane K₀ K) → K) z = 0
      rw [algebraMap_holRing_apply, hc, div_mul_cancel₀ _ hb'z, sub_self]
    have h1 := one_le_ordAt_of_apply_eq_zero ϖ hrk hex hnum z hvan hlf
    push_cast
    omega
  ·
    intro f hf
    obtain ⟨a, b, hb0, hab⟩ := hquot f
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hf
      apply Subtype.ext
      rw [hab, map_zero, zero_div]; rfl

    let incl : ↥(affinoid ϖ N) → ↥(upperHalfPlane K₀ K) := Set.inclusion (affinoid_subset_upperHalfPlane ϖ N)
    let Zb : Set ↥(affinoid ϖ N) := {w | restrictAffinoid ϖ N (toHol ϖ ρ b : ↥(upperHalfPlane K₀ K) → K) w = 0}
    have hZb : Zb.Finite := by
      by_cases hne : (affinoid ϖ N).Nonempty
      · exact CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_of_mem_holOn_affinoid K₀ K ϖ hrk N (hlf N)
          ((toHol ϖ ρ b).2 N) (restrictAffinoid_ne_zero ϖ hrk hex hlf ((toHol_ne_zero ϖ ρ).2 hb0) N hne)
      · haveI : IsEmpty ↥(affinoid ϖ N) := ⟨fun w => hne ⟨w, w.2⟩⟩
        exact Set.toFinite _
    refine (hZb.image fun w => vK (incl w)).subset ?_
    rintro v ⟨⟨z, rfl⟩, hv⟩
    obtain ⟨γ, hγ, hγz⟩ := hcpt z
    have hv' : 1 < vK (ρ γ • z) f := by rwa [vK_smul z γ hγ]
    rw [vK_apply, hab, merVal_div_eq_exp ϖ ρ hrk hex hlf _ ha0 hb0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hv'
    have hbz : (toHol ϖ ρ b : ↥(upperHalfPlane K₀ K) → K) (ρ γ • z) = 0 := by
      by_contra h
      have := ordAt_eq_zero_of_apply_ne_zero ϖ h
      omega
    refine ⟨⟨((ρ γ • z : ↥(upperHalfPlane K₀ K)) : K), hγz⟩, ?_, ?_⟩
    · show restrictAffinoid ϖ N (toHol ϖ ρ b : ↥(upperHalfPlane K₀ K) → K) _ = 0
      simpa [restrictAffinoid] using hbz
    · show vK (incl ⟨((ρ γ • z : ↥(upperHalfPlane K₀ K)) : K), hγz⟩) = vK z
      rw [← vK_smul z γ hγ]
  ·
    intro f hfv
    by_cases hf0 : f = 0
    · exact ⟨0, by rw [hf0, map_zero]⟩
    obtain ⟨a, b, hb0, hab⟩ := hquot f
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hf0
      apply Subtype.ext
      rw [hab, map_zero, zero_div]; rfl
    have hle : ∀ z : ↥(upperHalfPlane K₀ K), ordAt ϖ (toHol ϖ ρ b) z ≤ ordAt ϖ (toHol ϖ ρ a) z := fun z => by
      have h := hfv (vK z) ⟨z, rfl⟩
      rw [vK_apply, hab, merVal_div_eq_exp ϖ ρ hrk hex hlf z ha0 hb0, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at h
      omega
    obtain ⟨q, hq⟩ := CerednikDrinfeld.Omega.dvd_of_forall_ordAt_le K₀ K ϖ hrk hex hlf (toHol ϖ ρ a) (toHol ϖ ρ b)
      ((toHol_ne_zero ϖ ρ).2 hb0) hle

    have hfq : (f : FractionRing (HolRingOf ϖ ρ)) = algebraMap (HolRingOf ϖ ρ) _ (ofHol ϖ ρ q) := by
      have hbne : algebraMap (HolRingOf ϖ ρ) (FractionRing (HolRingOf ϖ ρ)) b ≠ 0 := fun h =>
        hb0 (IsFractionRing.injective (HolRingOf ϖ ρ) (FractionRing (HolRingOf ϖ ρ)) (by rw [h, map_zero]))
      rw [hab, div_eq_iff hbne, ← map_mul]
      congr 1
      apply toHol_injective ϖ ρ
      rw [map_mul, toHol_ofHol, hq, mul_comm]
    have hinv : ∀ γ ∈ Δ, ρ γ • q = q := fun γ hγ => by
      have h := f.2 γ hγ
      rw [hfq, Mumford.frac_smul_algebraMap] at h
      have h' := IsFractionRing.injective (HolRingOf ϖ ρ) (FractionRing (HolRingOf ϖ ρ)) h
      have := congrArg (toHol ϖ ρ) h'
      rwa [toHol_smul, toHol_ofHol] at this
    obtain ⟨c, hc⟩ :=
      CerednikDrinfeld.Omega.exists_eq_algebraMap_of_forall_smul_eq_of_forall_exists_smul_mem_affinoid K₀ K ϖ hrk hex
        hlf G ρ Δ N hcpt q hinv
    refine ⟨c, Subtype.ext ?_⟩
    rw [Mumford.algebraMap_invariantFieldOf_coe, algebraMap_frac_eq, hfq, hc, ofHol_algebraMap]

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_exists_valuations_invariantFieldOf_of_finite_quotVert.P2mKcValCpt"

end S_CerednikDrinfeld_Omega_exists_valuations_invariantFieldOf_of_finite_quotVert
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_valuations_invariantFieldOf_of_finite_quotVert (solution)
