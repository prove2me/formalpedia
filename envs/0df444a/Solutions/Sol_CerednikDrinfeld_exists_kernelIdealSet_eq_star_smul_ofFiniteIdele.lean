-- Prove2me | solution 1 for CerednikDrinfeld.exists_kernelIdealSet_eq_star_smul_ofFiniteIdele
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4a53b91f-ccfc-504c-8091-78a2cb3d0a7a

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_inf_setOf_le_padicValRat_nrd
import Theorems.Thm_CerednikDrinfeld_exists_injective_mem_rationalHomSet_kernelIdealSet_eq_nrd_dvd
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp
import Theorems.Thm_WeierstrassCurve_mem_ideal_rationalEndSubring_of_forall_apply_eq_zero
import Theorems.Thm_Submodule_ofFiniteIdele_diagonal_mul
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_Submodule_exists_ne_zero_natCast_smul_mem_finiteAdeleBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_kernelIdealSet_eq_star_smul_ofFiniteIdele
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.pointAddEquivOfEq_refl"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra~baseChange CerednikDrinfeld P2MW.S_CerednikDrinfeld_exists_kernelIdealSet_eq_star_smul_ofFiniteIdele.CerednikDrinfeld ModularCurve"
open IsDedekindDomain

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "exists_injective_mem_rationalHomSet_kernelIdealSet_eq_nrd_dvd"
p2m_open "CerednikDrinfeld"

namespace KernelIdealClasses

section Quaternion

variable {a b : ℚ}

local notation "ℍ" => ℍ[ℚ, a, b]
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem nrd_mul' (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

theorem nrd_natCast_mul (n : ℕ) (y : ℍ[ℚ, a, b]) : nrd ((n : ℍ[ℚ, a, b]) * y) = (n : ℚ) ^ 2 * nrd y := by
  rw [nrd_mul', ← coe_natCast, nrd_coe]

theorem nrd_pos_of_ne_zero (ha : a < 0) (hb : b < 0) {h : ℍ[ℚ, a, b]} (h0 : h ≠ 0) : 0 < nrd h := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := h
  simp only [nrd_mk]
  have ha' : 0 < -a := by linarith
  have hb' : 0 < -b := by linarith
  have hab : 0 < a * b := by nlinarith
  have t0 : 0 ≤ x₀ ^ 2 := sq_nonneg x₀
  have t1 : 0 ≤ (-a) * x₁ ^ 2 := mul_nonneg ha'.le (sq_nonneg x₁)
  have t2 : 0 ≤ (-b) * x₂ ^ 2 := mul_nonneg hb'.le (sq_nonneg x₂)
  have t3 : 0 ≤ (a * b) * x₃ ^ 2 := mul_nonneg hab.le (sq_nonneg x₃)
  by_contra hle
  push Not at hle
  have h1 : x₀ ^ 2 = 0 := by nlinarith
  have h2 : (-a) * x₁ ^ 2 = 0 := by nlinarith
  have h3 : (-b) * x₂ ^ 2 = 0 := by nlinarith
  have h4 : (a * b) * x₃ ^ 2 = 0 := by nlinarith
  have e0 : x₀ = 0 := by simpa using h1
  have e1 : x₁ = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · simpa using h
  have e2 : x₂ = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · simpa using h
  have e3 : x₃ = 0 := by
    rcases mul_eq_zero.mp h4 with h | h
    · linarith
    · simpa using h
  apply h0
  ext <;> simp [e0, e1, e2, e3]

theorem nrd_ne_zero_of_ne_zero (ha : a < 0) (hb : b < 0) {h : ℍ[ℚ, a, b]} (h0 : h ≠ 0) : nrd h ≠ 0 :=
  (nrd_pos_of_ne_zero ha hb h0).ne'

theorem star_mem_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {h : ℍ[ℚ, a, b]} (hh : h ∈ Λ) :
    star h ∈ Λ := by
  obtain ⟨-, t, ht⟩ := hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hh
  have e : star h = ((trd h : ℚ) : ℍ[ℚ, a, b]) - h := by
    rw [← add_star_eq_coe_trd]; abel
  have e2 : ((trd h : ℚ) : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) := by
    rw [← ht, coe_intCast, zsmul_eq_mul, mul_one]
  rw [e, e2]
  exact Λ.sub_mem (Λ.smul_mem t hΛ.one_mem) hh

theorem exists_natCast_eq_nrd {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ha : a < 0) (hb : b < 0)
    {h : ℍ[ℚ, a, b]} (hh : h ∈ Λ) : ∃ n : ℕ, (n : ℚ) = nrd h := by
  obtain ⟨⟨z, hz⟩, -⟩ := hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hh
  have hz0 : 0 ≤ z := by
    have : (0 : ℚ) ≤ nrd h := by
      by_cases h0 : h = 0
      · rw [h0, nrd_zero]
      · exact (nrd_pos_of_ne_zero ha hb h0).le
    rw [← hz] at this
    exact_mod_cast this
  refine ⟨z.toNat, ?_⟩
  rw [← hz]
  exact_mod_cast Int.toNat_of_nonneg hz0

theorem mul_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f} (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add u w _ _ hu hw => rw [add_mul]; exact add_mem hu hw
    | neg u _ hu =>
      convert neg_mem hu using 1
      exact neg_mul u _
  | zero => rw [mul_zero]; exact zero_mem _
  | add u w _ _ hu hw => rw [mul_add]; exact add_mem hu hw
  | neg u _ hu =>
    convert neg_mem hu using 1
    exact mul_neg x u

theorem tmul_one_mem_finiteAdeleBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, 1, fun v => one_mem _, rfl⟩

theorem mul_mem_ofFiniteIdele {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) {z μ : ℍ[ℚ, a, b]}
    (hz : z ∈ Submodule.ofFiniteIdele Λ g) (hμ : μ ∈ Λ) : z * μ ∈ Submodule.ofFiniteIdele Λ g := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz ⊢
  obtain ⟨w, hw, hwz⟩ := hz
  refine ⟨w * μ ⊗ₜ[ℚ] (1 : 𝔸f), mul_mem_finiteAdeleBox hΛ hw (tmul_one_mem_finiteAdeleBox hμ), ?_⟩
  rw [AddMonoidHom.coe_mulLeft] at hwz ⊢
  rw [← mul_assoc, hwz, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem exists_natCast_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ z ∈ Submodule.ofFiniteIdele Λ x, (N : ℍ[ℚ, a, b]) * z ∈ Λ := by
  obtain ⟨N, hN, hNx⟩ :=
    Submodule.exists_ne_zero_natCast_smul_mem_finiteAdeleBox Λ hΛ.spanTop (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)
  refine ⟨N, hN, fun z hz => ?_⟩
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  rw [AddMonoidHom.coe_mulLeft] at hwz
  have hmem : ((N : ℍ[ℚ, a, b]) * z) ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox Λ := by
    have e : ((N : ℍ[ℚ, a, b]) * z) ⊗ₜ[ℚ] (1 : 𝔸f) = ((N : ℚ) • (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) * w := by
      rw [smul_mul_assoc, hwz, TensorProduct.smul_tmul', ← coe_natCast, ← QuaternionAlgebra.coe_mul_eq_smul]
    rw [e]
    exact mul_mem_finiteAdeleBox hΛ hNx hw
  have : (N : ℍ[ℚ, a, b]) * z ∈ Submodule.ofFiniteIdele Λ 1 := by
    rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
    exact ⟨_, hmem, by rw [AddMonoidHom.coe_mulLeft, Units.val_one, one_mul]⟩
  rwa [Submodule.ofFiniteIdele_one Λ hΛ.fg hΛ.spanTop] at this

def ratUnit (c : ℚ) (hc : c ≠ 0) : (ℍ[ℚ, a, b])ˣ :=
  Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 c hc)

@[scoped simp] theorem val_ratUnit (c : ℚ) (hc : c ≠ 0) : ((ratUnit c hc : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (c : ℍ[ℚ, a, b]) :=
  rfl

theorem mem_units_smul_iff (d : (ℍ[ℚ, a, b])ˣ) (I : Submodule ℤ ℍ[ℚ, a, b]) (z : ℍ[ℚ, a, b]) :
    z ∈ d • I ↔ ∃ y ∈ I, (d : ℍ[ℚ, a, b]) * y = z :=
  Submodule.mem_smul_pointwise_iff_exists z d I

theorem coe_units_smul (d : (ℍ[ℚ, a, b])ˣ) (I : Submodule ℤ ℍ[ℚ, a, b]) :
    ((d • I : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) = (fun y => (d : ℍ[ℚ, a, b]) * y) '' (I : Set ℍ[ℚ, a, b]) := by
  ext z
  rw [SetLike.mem_coe, mem_units_smul_iff, Set.mem_image]
  rfl

theorem coe_ofFiniteIdele_diagonal_ratUnit_mul (Λ : Submodule ℤ ℍ[ℚ, a, b]) (c : ℚ) (hc : c ≠ 0)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) :
    ((Submodule.ofFiniteIdele Λ (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (ratUnit c hc) * x) :
        Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) =
      (fun y => (c : ℍ[ℚ, a, b]) * y) '' (Submodule.ofFiniteIdele Λ x : Set ℍ[ℚ, a, b]) := by
  rw [Submodule.ofFiniteIdele_diagonal_mul, coe_units_smul, val_ratUnit]

def Pset (Λ : Submodule ℤ ℍ[ℚ, a, b]) (q : ℕ) (k : ℕ) : Set ℍ[ℚ, a, b] :=
  {h | h ∈ Λ ∧ (h = 0 ∨ (k : ℤ) ≤ padicValRat q (nrd h))}

theorem mem_Pset_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (q k : ℕ) (h : ℍ[ℚ, a, b]) :
    h ∈ Pset Λ q k ↔ h ∈ Λ ∧ (h = 0 ∨ (k : ℤ) ≤ padicValRat q (nrd h)) :=
  Iff.rfl

theorem Pset_subset (Λ : Submodule ℤ ℍ[ℚ, a, b]) (q k : ℕ) : Pset Λ q k ⊆ (Λ : Set ℍ[ℚ, a, b]) :=
  fun _ hh => hh.1

theorem padicValRat_nrd_nonneg {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ha : a < 0) (hb : b < 0)
    (q : ℕ) {h : ℍ[ℚ, a, b]} (hh : h ∈ Λ) : 0 ≤ padicValRat q (nrd h) := by
  obtain ⟨n, hn⟩ := exists_natCast_eq_nrd hΛ ha hb hh
  rw [← hn, padicValRat.of_nat]
  exact_mod_cast Nat.zero_le _

theorem Pset_zero_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ha : a < 0) (hb : b < 0) (q : ℕ) :
    Pset Λ q 0 = (Λ : Set ℍ[ℚ, a, b]) := by
  refine Set.Subset.antisymm (Pset_subset Λ q 0) fun h hh => ⟨hh, Or.inr ?_⟩
  rw [Nat.cast_zero]
  exact padicValRat_nrd_nonneg hΛ ha hb q hh

theorem natCast_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (n : ℕ) : (n : ℍ[ℚ, a, b]) ∈ Λ := by
  have : (n : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by
    rw [zsmul_eq_mul, Int.cast_natCast, mul_one]
  rw [this]
  exact Λ.smul_mem _ hΛ.one_mem

theorem natCast_mul_mem_of_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (I : Submodule ℤ ℍ[ℚ, a, b]) (n : ℕ)
    {z : ℍ[ℚ, a, b]} (hz : z ∈ I) : (n : ℍ[ℚ, a, b]) * z ∈ I := by
  have : (n : ℍ[ℚ, a, b]) * z = (n : ℤ) • z := by rw [zsmul_eq_mul, Int.cast_natCast]
  rw [this]
  exact I.smul_mem _ hz

theorem mem_of_coprime_natCast_mul_mem {Λ I : Submodule ℤ ℍ[ℚ, a, b]}
    (hIr : ∀ z ∈ I, ∀ μ ∈ Λ, z * μ ∈ I) {n₀ : ℕ} (hn₀ : (n₀ : ℍ[ℚ, a, b]) ∈ I)
    {c : ℕ} (hc : Nat.Coprime c n₀) {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (hcz : (c : ℍ[ℚ, a, b]) * z ∈ I) :
    z ∈ I := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have e : z = u • ((c : ℍ[ℚ, a, b]) * z) + v • ((n₀ : ℍ[ℚ, a, b]) * z) := by
    rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc, ← add_mul, ← Int.cast_natCast c,
      ← Int.cast_natCast n₀, ← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add, huv, Int.cast_one, one_mul]
  rw [e]
  exact I.add_mem (I.smul_mem u hcz) (I.smul_mem v (hIr _ hn₀ _ hz))

theorem exists_natCast_mem_coprime {Λ I : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ha : a < 0) (hb : b < 0)
    (q : ℕ) [Fact q.Prime] (hI : I ≤ Λ) (hIr : ∀ z ∈ I, ∀ μ ∈ Λ, z * μ ∈ I)
    {h : ℍ[ℚ, a, b]} (hhI : h ∈ I) (hh0 : h ≠ 0) (hv : padicValRat q (nrd h) = 0) :
    ∃ n₀ : ℕ, n₀ ≠ 0 ∧ Nat.Coprime q n₀ ∧ (n₀ : ℍ[ℚ, a, b]) ∈ I := by
  obtain ⟨n₀, hn₀⟩ := exists_natCast_eq_nrd hΛ ha hb (hI hhI)
  have hn₀0 : n₀ ≠ 0 := by
    rintro rfl
    exact nrd_ne_zero_of_ne_zero ha hb hh0 (by rw [← hn₀, Nat.cast_zero])
  refine ⟨n₀, hn₀0, ?_, ?_⟩
  · rw [← hn₀, padicValRat.of_nat, Nat.cast_eq_zero, padicValNat.eq_zero_iff] at hv
    rcases hv with hv | hv | hv
    · exact absurd hv (Fact.out : q.Prime).one_lt.ne'
    · exact absurd hv hn₀0
    · exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hv
  · have e : (n₀ : ℍ[ℚ, a, b]) = h * star h := by
      rw [mul_star_eq_coe_nrd, ← hn₀, coe_natCast]
    rw [e]
    exact hIr _ hhI _ (star_mem_of_mem hΛ (hI hhI))

theorem natCast_ne_zero_quat {n : ℕ} (hn : n ≠ 0) : (n : ℍ[ℚ, a, b]) ≠ 0 := by
  rw [← coe_natCast]
  intro h
  have := congrArg QuaternionAlgebra.re h
  simp only [QuaternionAlgebra.re_coe, QuaternionAlgebra.re_zero, Nat.cast_eq_zero] at this
  exact hn this

theorem padicValRat_nrd_natCast_mul (q : ℕ) [Fact q.Prime] (ha : a < 0) (hb : b < 0) {z : ℍ[ℚ, a, b]}
    (hz : z ≠ 0) : padicValRat q (nrd ((q : ℍ[ℚ, a, b]) * z)) = 2 + padicValRat q (nrd z) := by
  have hq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  rw [nrd_natCast_mul, padicValRat.mul (pow_ne_zero 2 hq) (nrd_ne_zero_of_ne_zero ha hb hz),
    padicValRat.pow _, padicValRat.self (Fact.out : q.Prime).one_lt]
  norm_num

theorem exists_eq_natCast_mul_of_two_le (q : ℕ) [Fact q.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {h : ℍ[ℚ, a, b]} (hh : h ∈ Λ) (hh0 : h ≠ 0)
    (h2 : (2 : ℤ) ≤ padicValRat q (nrd h)) : ∃ z ∈ Λ, h = (q : ℍ[ℚ, a, b]) * z := by
  have ha := hdef.neg_left
  have hb := hdef.neg_right
  have hΛo : IsOrder Λ := hΛ.1
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  set xq : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (ratUnit (q : ℚ) hq0) * 1
    with hxq
  have hcoe : ((Submodule.ofFiniteIdele Λ xq : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) =
      (fun y => (q : ℍ[ℚ, a, b]) * y) '' (Λ : Set ℍ[ℚ, a, b]) := by
    rw [hxq, coe_ofFiniteIdele_diagonal_ratUnit_mul, Submodule.ofFiniteIdele_one Λ hΛo.fg hΛo.spanTop,
      coe_natCast]
  have hmem : ∀ z, z ∈ Submodule.ofFiniteIdele Λ xq ↔ ∃ y ∈ Λ, (q : ℍ[ℚ, a, b]) * y = z := by
    intro z
    rw [← SetLike.mem_coe, hcoe, Set.mem_image]
    rfl
  have hle : Submodule.ofFiniteIdele Λ xq ≤ Λ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := (hmem z).mp hz
    exact hΛo.mul_mem (natCast_mem hΛo q) hy
  obtain ⟨k₀, x₀, hx₀, ⟨h', hh'I, hv', hh'0⟩, hsplit⟩ :=
    IsMaximalOrder.exists_ofFiniteIdele_eq_inf_setOf_le_padicValRat_nrd q hdef Λ hΛ xq hle
  have hIr := fun z hz μ hμ => mul_mem_ofFiniteIdele hΛo x₀ (z := z) (μ := μ) hz hμ
  obtain ⟨n₀, hn₀0, hcop, hn₀I⟩ := exists_natCast_mem_coprime hΛo ha hb q hx₀ hIr hh'I hh'0 hv'

  have hΛle : ∀ z ∈ Λ, z ∈ Submodule.ofFiniteIdele Λ x₀ := by
    intro z hz
    have hqz : (q : ℍ[ℚ, a, b]) * z ∈ Submodule.ofFiniteIdele Λ x₀ := by
      have h1 : (q : ℍ[ℚ, a, b]) * z ∈ (Submodule.ofFiniteIdele Λ xq : Set ℍ[ℚ, a, b]) :=
        (hmem _).mpr ⟨z, hz, rfl⟩
      rw [hsplit] at h1
      exact h1.1
    exact mem_of_coprime_natCast_mul_mem hIr hn₀I hcop hz hqz

  have hk₀ : (k₀ : ℤ) ≤ 2 := by
    have h1 : (q : ℍ[ℚ, a, b]) ∈ (Submodule.ofFiniteIdele Λ xq : Set ℍ[ℚ, a, b]) :=
      (hmem _).mpr ⟨1, hΛo.one_mem, mul_one _⟩
    rw [hsplit] at h1
    rcases h1.2.2 with h | h
    · exact absurd h (natCast_ne_zero_quat (Fact.out : q.Prime).ne_zero)
    · rw [← coe_natCast, nrd_coe, padicValRat.pow _, padicValRat.self (Fact.out : q.Prime).one_lt] at h
      simpa using h

  have h1 : h ∈ (Submodule.ofFiniteIdele Λ xq : Set ℍ[ℚ, a, b]) := by
    rw [hsplit]
    exact ⟨hΛle h hh, hh, Or.inr (hk₀.trans h2)⟩
  obtain ⟨z, hz, hzq⟩ := (hmem h).mp h1
  exact ⟨z, hz, hzq.symm⟩

theorem Pset_add_two {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ha : a < 0) (hb : b < 0)
    (q : ℕ) [Fact q.Prime]
    (hP2 : ∀ h ∈ Λ, h ≠ 0 → (2 : ℤ) ≤ padicValRat q (nrd h) → ∃ z ∈ Λ, h = (q : ℍ[ℚ, a, b]) * z)
    (i : ℕ) : Pset Λ q (i + 2) = (fun z => (q : ℍ[ℚ, a, b]) * z) '' Pset Λ q i := by
  ext h
  simp only [mem_Pset_iff, Set.mem_image]
  constructor
  · rintro ⟨hh, h0 | hv⟩
    · exact ⟨0, ⟨Λ.zero_mem, Or.inl rfl⟩, by rw [h0, mul_zero]⟩
    · by_cases hz0 : h = 0
      · exact ⟨0, ⟨Λ.zero_mem, Or.inl rfl⟩, by rw [hz0, mul_zero]⟩
      have h2 : (2 : ℤ) ≤ padicValRat q (nrd h) := le_trans (by push_cast; omega) hv
      obtain ⟨z, hz, rfl⟩ := hP2 h hh hz0 h2
      have hz0' : z ≠ 0 := by rintro rfl; exact hz0 (mul_zero _)
      refine ⟨z, ⟨hz, Or.inr ?_⟩, rfl⟩
      rw [padicValRat_nrd_natCast_mul q ha hb hz0'] at hv
      push_cast at hv
      linarith
  · rintro ⟨z, ⟨hz, hz0 | hv⟩, rfl⟩
    · exact ⟨hΛ.mul_mem (natCast_mem hΛ q) hz, Or.inl (by rw [hz0, mul_zero])⟩
    · refine ⟨hΛ.mul_mem (natCast_mem hΛ q) hz, ?_⟩
      by_cases hz0 : z = 0
      · exact Or.inl (by rw [hz0, mul_zero])
      · right
        rw [padicValRat_nrd_natCast_mul q ha hb hz0]
        push_cast
        linarith

theorem Pset_add_two_mul {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ha : a < 0) (hb : b < 0)
    (q : ℕ) [Fact q.Prime]
    (hP2 : ∀ h ∈ Λ, h ≠ 0 → (2 : ℤ) ≤ padicValRat q (nrd h) → ∃ z ∈ Λ, h = (q : ℍ[ℚ, a, b]) * z)
    (j m : ℕ) : Pset Λ q (j + 2 * m) = (fun z => (q : ℍ[ℚ, a, b]) ^ m * z) '' Pset Λ q j := by
  induction m with
  | zero =>
    simp only [mul_zero, add_zero, pow_zero, one_mul, Set.image_id']
  | succ m ih =>
    rw [show j + 2 * (m + 1) = (j + 2 * m) + 2 by ring, Pset_add_two hΛ ha hb q hP2, ih, Set.image_image]
    refine Set.image_congr fun z _ => ?_
    rw [pow_succ', mul_assoc]

theorem inter_Pset_eq_image {Λ I₀ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ha : a < 0) (hb : b < 0)
    (q : ℕ) [Fact q.Prime]
    (hP2 : ∀ h ∈ Λ, h ≠ 0 → (2 : ℤ) ≤ padicValRat q (nrd h) → ∃ z ∈ Λ, h = (q : ℍ[ℚ, a, b]) * z)
    (hI₀r : ∀ z ∈ I₀, ∀ μ ∈ Λ, z * μ ∈ I₀) {n₀ : ℕ} (hn₀I : (n₀ : ℍ[ℚ, a, b]) ∈ I₀)
    (hcop : Nat.Coprime q n₀) (ε m : ℕ) :
    (I₀ : Set ℍ[ℚ, a, b]) ∩ Pset Λ q (ε + 2 * m) =
      (fun z => (q : ℍ[ℚ, a, b]) ^ m * z) '' ((I₀ : Set ℍ[ℚ, a, b]) ∩ Pset Λ q ε) := by
  rw [Pset_add_two_mul hΛ ha hb q hP2]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨hyI, z, hz, rfl⟩
    refine ⟨z, ⟨?_, hz⟩, rfl⟩
    have hcz : ((q ^ m : ℕ) : ℍ[ℚ, a, b]) * z ∈ I₀ := by rwa [Nat.cast_pow]
    exact mem_of_coprime_natCast_mul_mem hI₀r hn₀I (Nat.Coprime.pow_left m hcop) hz.1 hcz
  · rintro ⟨z, ⟨hzI, hz⟩, rfl⟩
    refine ⟨?_, z, hz, rfl⟩
    have := natCast_mul_mem_of_mem (Λ := Λ) I₀ (q ^ m) hzI
    rwa [Nat.cast_pow] at this

theorem eq_image_div_of_eq_image {c₁ c₂ : ℚ} (hc₂ : c₂ ≠ 0) {T J Ix : Set ℍ[ℚ, a, b]}
    (h1 : T = (fun y => (c₁ : ℍ[ℚ, a, b]) * y) '' Ix)
    (h2 : T = (fun y => (c₂ : ℍ[ℚ, a, b]) * y) '' J) :
    J = (fun y => ((c₁ / c₂ : ℚ) : ℍ[ℚ, a, b]) * y) '' Ix := by
  have key : ∀ y : ℍ[ℚ, a, b], ((c₂⁻¹ : ℚ) : ℍ[ℚ, a, b]) * ((c₂ : ℍ[ℚ, a, b]) * y) = y := by
    intro y
    rw [← mul_assoc, ← QuaternionAlgebra.coe_mul, inv_mul_cancel₀ hc₂, QuaternionAlgebra.coe_one, one_mul]
  have hJ : J = (fun y => ((c₂⁻¹ : ℚ) : ℍ[ℚ, a, b]) * y) '' T := by
    rw [h2, Set.image_image]
    ext y
    simp only [Set.mem_image, key, exists_eq_right]
  rw [hJ, h1, Set.image_image]
  refine Set.image_congr fun y _ => ?_
  rw [← mul_assoc, ← QuaternionAlgebra.coe_mul, div_eq_inv_mul]

theorem star_image_star_image (S : Set ℍ[ℚ, a, b]) : star '' (star '' S) = S := by
  rw [Set.image_image]; simp

theorem star_image_inter (S T : Set ℍ[ℚ, a, b]) : star '' (S ∩ T) = star '' S ∩ star '' T :=
  Set.image_inter star_injective

theorem star_image_Pset {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (q k : ℕ) :
    star '' Pset Λ q k = Pset Λ q k := by
  have hsub : ∀ h ∈ Pset Λ q k, star h ∈ Pset Λ q k := by
    rintro h ⟨hh, h0 | hv⟩
    · exact ⟨star_mem_of_mem hΛ hh, Or.inl (by rw [h0, star_zero])⟩
    · exact ⟨star_mem_of_mem hΛ hh, Or.inr (by rwa [nrd_star])⟩
  refine Set.Subset.antisymm ?_ fun h hh => ⟨star h, hsub h hh, star_star h⟩
  rintro _ ⟨h, hh, rfl⟩
  exact hsub h hh

end Quaternion

section HomSet

open scoped Polynomial.Bivariate
open WeierstrassCurve

variable {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K] [DecidableEq K]

theorem isRationallyRepresented_neg_id (W : WeierstrassCurve F) :
    IsRationallyRepresented K W W (-(AddMonoidHom.id _)) := by
  refine ⟨Polynomial.C Polynomial.X, 1,
    -Polynomial.X - Polynomial.C (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃), 1, ∅,
    Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC K (1 : F[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC K (Polynomial.C Polynomial.X : F[X][Y]) x y = x := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC K (-Polynomial.X - Polynomial.C (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃) :
      F[X][Y]) x y = (W.baseChange K).toAffine.negY x y := by
    simp [evalEvalBC, Polynomial.evalEval, Affine.negY, WeierstrassCurve.baseChange]
    ring
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  rw [e0, e1, e2, div_one, div_one, AddMonoidHom.neg_apply, AddMonoidHom.id_apply,
    Affine.Point.neg_some]
  exact ⟨_, rfl⟩

variable {K}

theorem neg_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange K).toAffine.Point →+ (W₂.baseChange K).toAffine.Point}
    (hα : α ∈ rationalHomSet K W₁ W₂) : -α ∈ rationalHomSet K W₁ W₂ := by
  have h := WeierstrassCurve.comp_mem_rationalHomSet K W₁ W₂ W₂ hα
    (Or.inr (isRationallyRepresented_neg_id K W₂))
  have e : (-(AddMonoidHom.id _)).comp α = -α := AddMonoidHom.ext fun P => rfl
  rwa [e] at h

variable [IsAlgClosed K]

variable (K) in

def homSubring (W : WeierstrassCurve F) [W.IsElliptic] :
    Subring (AddMonoid.End (W.baseChange K).toAffine.Point) where
  carrier := rationalHomSet K W W
  mul_mem' ha hb := WeierstrassCurve.comp_mem_rationalHomSet K W W W hb ha
  one_mem' := id_mem_rationalHomSet K W
  add_mem' ha hb := WeierstrassCurve.add_mem_rationalHomSet K W W ha hb
  zero_mem' := zero_mem_rationalHomSet K W W
  neg_mem' hα := neg_mem_rationalHomSet hα

theorem mem_rationalHomSet_of_mem_rationalEndSubring (W : WeierstrassCurve F) [W.IsElliptic]
    {α : AddMonoid.End (W.baseChange K).toAffine.Point} (hα : α ∈ rationalEndSubring K W) :
    (α : (W.baseChange K).toAffine.Point →+ (W.baseChange K).toAffine.Point) ∈ rationalHomSet K W W := by
  have : rationalEndSubring K W ≤ homSubring K W := Subring.closure_le.mpr (fun x hx => hx)
  exact this hα

end HomSet

section Curve

open WeierstrassCurve

variable {κ : Type} [Field κ] [DecidableEq κ]

abbrev Pt (X : WeierstrassCurve κ) : Type := (X.baseChange κ).toAffine.Point

def jointKer (X₀ : WeierstrassCurve κ) (L : Ideal ↥(rationalEndSubring κ X₀)) : AddSubgroup (Pt X₀) where
  carrier := {P | ∀ l ∈ L, (l : AddMonoid.End (Pt X₀)) P = 0}
  zero_mem' := fun l _ => map_zero _
  add_mem' := fun {P Q} hP hQ l hl => by rw [map_add, hP l hl, hQ l hl, add_zero]
  neg_mem' := fun {P} hP l hl => by rw [map_neg, hP l hl, neg_zero]

theorem mem_jointKer_iff (X₀ : WeierstrassCurve κ) (L : Ideal ↥(rationalEndSubring κ X₀)) (P : Pt X₀) :
    P ∈ jointKer X₀ L ↔ ∀ l ∈ L, (l : AddMonoid.End (Pt X₀)) P = 0 :=
  Iff.rfl

variable {a b : ℚ}

def preIdeal (X₀ : WeierstrassCurve κ) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (I : Submodule ℤ ℍ[ℚ, a, b]) (hIr : ∀ z ∈ I, ∀ μ ∈ Λ, z * μ ∈ I) : Ideal ↥(rationalEndSubring κ X₀) where
  carrier := {r | star (θ r) ∈ I}
  zero_mem' := by simp
  add_mem' := fun {r s} hr hs => by
    simp only [Set.mem_setOf_eq, map_add, star_add]
    exact I.add_mem hr hs
  smul_mem' := fun c r hr => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, star_mul]
    refine hIr _ hr _ (star_mem_of_mem hΛ ?_)
    rw [← SetLike.mem_coe, ← hθΛ]
    exact ⟨c, rfl⟩

theorem mem_preIdeal_iff (X₀ : WeierstrassCurve κ) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (I : Submodule ℤ ℍ[ℚ, a, b]) (hIr : ∀ z ∈ I, ∀ μ ∈ Λ, z * μ ∈ I) (r : ↥(rationalEndSubring κ X₀)) :
    r ∈ preIdeal X₀ hΛ θ hθΛ I hIr ↔ star (θ r) ∈ I :=
  Iff.rfl

theorem image_preIdeal (X₀ : WeierstrassCurve κ) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (I : Submodule ℤ ℍ[ℚ, a, b]) (hI : I ≤ Λ) (hIr : ∀ z ∈ I, ∀ μ ∈ Λ, z * μ ∈ I) :
    θ '' (preIdeal X₀ hΛ θ hθΛ I hIr : Set ↥(rationalEndSubring κ X₀)) = star '' (I : Set ℍ[ℚ, a, b]) := by
  ext y
  simp only [Set.mem_image, SetLike.mem_coe, mem_preIdeal_iff]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨star (θ r), hr, star_star _⟩
  · rintro ⟨z, hz, rfl⟩
    have hz' : star z ∈ Set.range θ := by rw [hθΛ]; exact star_mem_of_mem hΛ (hI hz)
    obtain ⟨r, hr⟩ := hz'
    exact ⟨r, by rw [hr, star_star]; exact hz, hr⟩

theorem natCast_mem_preIdeal (X₀ : WeierstrassCurve κ) {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (θ : ↥(rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (I : Submodule ℤ ℍ[ℚ, a, b]) (hIr : ∀ z ∈ I, ∀ μ ∈ Λ, z * μ ∈ I) {n : ℕ} (hn : (n : ℍ[ℚ, a, b]) ∈ I) :
    (n : ↥(rationalEndSubring κ X₀)) ∈ preIdeal X₀ hΛ θ hθΛ I hIr := by
  rw [mem_preIdeal_iff, map_natCast, ← coe_natCast, QuaternionAlgebra.star_coe, coe_natCast]
  exact hn

theorem jointKer_le_torsionBy (X₀ : WeierstrassCurve κ) (L : Ideal ↥(rationalEndSubring κ X₀)) {n : ℕ}
    (hn : (n : ↥(rationalEndSubring κ X₀)) ∈ L) :
    jointKer X₀ L ≤ (Submodule.torsionBy ℤ (Pt X₀) n).toAddSubgroup := by
  intro P hP
  have h := hP _ hn
  rw [SubringClass.coe_natCast, AddMonoid.End.natCast_apply] at h
  change ((n : ℕ) : ℤ) • P = 0
  rw [natCast_zsmul]
  exact h

variable [IsAlgClosed κ]

theorem natCard_jointKer_dvd (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (L : Ideal ↥(rationalEndSubring κ X₀))
    {n : ℕ} (hnκ : (n : κ) ≠ 0) (hn : (n : ↥(rationalEndSubring κ X₀)) ∈ L) :
    Nat.card (jointKer X₀ L) ∣ n ^ 2 := by
  rw [← WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) X₀ hnκ]
  exact AddSubgroup.card_dvd_of_le (jointKer_le_torsionBy X₀ L hn)

theorem exists_point_ne_zero (W : WeierstrassCurve κ) [W.IsElliptic] : ∃ P : Pt W, P ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨n, hn, hn2⟩ : ∃ n : ℕ, (n : κ) ≠ 0 ∧ 2 ≤ n := by
    by_cases h2 : (2 : κ) = 0
    · refine ⟨3, fun h3 => ?_, by norm_num⟩
      have : (1 : κ) = 0 := by
        have e : (1 : κ) = (3 : ℕ) - 2 := by norm_num
        rw [e, h3, h2, sub_zero]
      exact one_ne_zero this
    · exact ⟨2, by exact_mod_cast h2, le_rfl⟩
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed (K := κ) W hn
  haveI : Subsingleton (Submodule.torsionBy ℤ (Pt W) n) :=
    ⟨fun P Q => Subtype.ext (by rw [hall P.1, hall Q.1])⟩
  rw [Nat.card_of_subsingleton (0 : Submodule.torsionBy ℤ (Pt W) n)] at hcard
  have : n ^ 2 ≤ 1 := hcard ▸ le_rfl
  nlinarith

theorem kernelIdealSet_eq_of_forall (X₀ W : WeierstrassCurve κ) [X₀.IsElliptic] [W.IsElliptic]
    (L : Ideal ↥(rationalEndSubring κ X₀))
    (hA : ∀ r : ↥(rationalEndSubring κ X₀),
      (∀ P : Pt X₀, (∀ l ∈ L, (l : AddMonoid.End (Pt X₀)) P = 0) → (r : AddMonoid.End (Pt X₀)) P = 0) → r ∈ L)
    (χ : Pt X₀ →+ Pt W) (hker : χ.ker = jointKer X₀ L)
    (huniv : ∀ (V : WeierstrassCurve κ) [V.IsElliptic] (α : Pt X₀ →+ Pt V),
      α ∈ rationalHomSet κ X₀ V → jointKer X₀ L ≤ α.ker → ∃ β ∈ rationalHomSet κ W V, α = β.comp χ) :
    kernelIdealSet κ X₀ W χ = (L : Set ↥(rationalEndSubring κ X₀)) := by
  ext r
  simp only [kernelIdealSet, Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨ρ, hρ, hr⟩
    refine hA r fun P hP => ?_
    have hPk : P ∈ χ.ker := by rw [hker]; exact hP
    rw [hr]
    show ρ (χ P) = 0
    rw [(AddMonoidHom.mem_ker).mp hPk, map_zero]
  · intro hr
    have hrat : (r : Pt X₀ →+ Pt X₀) ∈ rationalHomSet κ X₀ X₀ :=
      mem_rationalHomSet_of_mem_rationalEndSubring X₀ r.2
    have hle : jointKer X₀ L ≤ (r : Pt X₀ →+ Pt X₀).ker := fun P hP => hP r hr
    obtain ⟨β, hβ, hrβ⟩ := huniv X₀ r hrat hle
    exact ⟨β, hβ, hrβ⟩

theorem kernelIdealSet_comp_eq (X₀ W₁ W : WeierstrassCurve κ) [X₀.IsElliptic] [W₁.IsElliptic] [W.IsElliptic]
    (L : Ideal ↥(rationalEndSubring κ X₀))
    (hA : ∀ r : ↥(rationalEndSubring κ X₀),
      (∀ P : Pt X₀, (∀ l ∈ L, (l : AddMonoid.End (Pt X₀)) P = 0) → (r : AddMonoid.End (Pt X₀)) P = 0) → r ∈ L)
    (π : Pt X₀ →+ Pt W₁) (hπ : π ∈ rationalHomSet κ X₀ W₁)
    (χ₂ : Pt W₁ →+ Pt W) (hχ₂ : χ₂ ∈ rationalHomSet κ W₁ W) (hker : χ₂.ker = (jointKer X₀ L).map π)
    (huniv : ∀ (V : WeierstrassCurve κ) [V.IsElliptic] (α : Pt W₁ →+ Pt V),
      α ∈ rationalHomSet κ W₁ V → (jointKer X₀ L).map π ≤ α.ker → ∃ β ∈ rationalHomSet κ W V, α = β.comp χ₂) :
    kernelIdealSet κ X₀ W (χ₂.comp π) =
      (L : Set ↥(rationalEndSubring κ X₀)) ∩ kernelIdealSet κ X₀ W₁ π := by
  ext r
  simp only [kernelIdealSet, Set.mem_setOf_eq, Set.mem_inter_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨ρ, hρ, hr⟩
    refine ⟨hA r fun P hP => ?_, ρ.comp χ₂, WeierstrassCurve.comp_mem_rationalHomSet κ W₁ W X₀ hχ₂ hρ, ?_⟩
    · have hPk : π P ∈ χ₂.ker := by rw [hker]; exact AddSubgroup.mem_map_of_mem π hP
      rw [hr]
      show ρ (χ₂ (π P)) = 0
      rw [(AddMonoidHom.mem_ker).mp hPk, map_zero]
    · rw [hr]; rfl
  · rintro ⟨hrL, ρ₁, hρ₁, hr⟩
    have hle : (jointKer X₀ L).map π ≤ ρ₁.ker := by
      rintro _ ⟨P, hP, rfl⟩
      rw [AddMonoidHom.mem_ker]
      have : (r : AddMonoid.End (Pt X₀)) P = 0 := hP r hrL
      rw [hr] at this
      exact this
    obtain ⟨β, hβ, hρβ⟩ := huniv X₀ ρ₁ hρ₁ hle
    refine ⟨β, hβ, ?_⟩
    rw [hr, hρβ]; rfl

end Curve

end KernelIdealClasses
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_kernelIdealSet_eq_star_smul_ofFiniteIdele.CerednikDrinfeld.KernelIdealClasses"

end CerednikDrinfeld
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_kernelIdealSet_eq_star_smul_ofFiniteIdele.CerednikDrinfeld.KernelIdealClasses P2MW.S_CerednikDrinfeld_exists_kernelIdealSet_eq_star_smul_ofFiniteIdele.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_kernelIdealSet_eq_star_smul_ofFiniteIdele.CerednikDrinfeld.KernelIdealClasses P2MW.S_CerednikDrinfeld_exists_kernelIdealSet_eq_star_smul_ofFiniteIdele.CerednikDrinfeld"

open CerednikDrinfeld.KernelIdealClasses WeierstrassCurve in

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₀ : WeierstrassCurve κ) [X₀.IsElliptic] (hss : ∀ P : X₀.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b])
    (hθ : Function.Injective θ) (hθΛ : Set.range θ = (Λ : Set ℍ[ℚ, a, b]))
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∃ (W : WeierstrassCurve κ) (_ : W.IsElliptic) (χ : (X₀.baseChange κ).toAffine.Point →+ (W.baseChange κ).toAffine.Point)
      (_ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (_ : χ ≠ 0) (d : (ℍ[ℚ, a, b])ˣ),
      θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W χ) =
        star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
  have ha := hdef.neg_left
  have hb := hdef.neg_right
  have hΛo : IsOrder Λ := hΛ.1
  have hqprime : q'.Prime := Fact.out

  obtain ⟨N, hN0, hN⟩ := exists_natCast_mul_mem hΛo x
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN0
  set x' : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
    Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (ratUnit (N : ℚ) hNq) * x with hx'
  have hT : ((Submodule.ofFiniteIdele Λ x' : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) =
      (fun y => ((N : ℚ) : ℍ[ℚ, a, b]) * y) '' (Submodule.ofFiniteIdele Λ x : Set ℍ[ℚ, a, b]) :=
    coe_ofFiniteIdele_diagonal_ratUnit_mul Λ _ hNq x
  have hx'le : Submodule.ofFiniteIdele Λ x' ≤ Λ := by
    intro z hz
    have hz' : z ∈ ((Submodule.ofFiniteIdele Λ x' : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := hz
    rw [hT] at hz'
    obtain ⟨y, hy, rfl⟩ := hz'
    rw [coe_natCast]
    exact hN y hy

  obtain ⟨k, x₀, hx₀, ⟨h₀, hh₀I, hv₀, hh₀0⟩, hsplit⟩ :=
    IsMaximalOrder.exists_ofFiniteIdele_eq_inf_setOf_le_padicValRat_nrd q' hdef Λ hΛ x' hx'le
  have hI₀r : ∀ z ∈ Submodule.ofFiniteIdele Λ x₀, ∀ μ ∈ Λ, z * μ ∈ Submodule.ofFiniteIdele Λ x₀ :=
    fun z hz μ hμ => mul_mem_ofFiniteIdele hΛo x₀ hz hμ
  obtain ⟨n₀, hn₀0, hcop, hn₀I⟩ := exists_natCast_mem_coprime hΛo ha hb q' hx₀ hI₀r hh₀I hh₀0 hv₀

  have hP2 : ∀ h ∈ Λ, h ≠ 0 → (2 : ℤ) ≤ padicValRat q' (nrd h) → ∃ z ∈ Λ, h = (q' : ℍ[ℚ, a, b]) * z :=
    fun h hh hh0 h2 => exists_eq_natCast_mul_of_two_le q' hdef hΛ hh hh0 h2
  set ε : ℕ := k % 2 with hεdef
  set m : ℕ := k / 2 with hmdef
  have hk : k = ε + 2 * m := (Nat.mod_add_div k 2).symm
  set J : Set ℍ[ℚ, a, b] := (Submodule.ofFiniteIdele Λ x₀ : Set ℍ[ℚ, a, b]) ∩ Pset Λ q' ε with hJ
  have hsplit' : ((Submodule.ofFiniteIdele Λ x' : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) =
      (fun z => (q' : ℍ[ℚ, a, b]) ^ m * z) '' J := by
    rw [hsplit, show {h : ℍ[ℚ, a, b] | h ∈ Λ ∧ (h = 0 ∨ (k : ℤ) ≤ padicValRat q' (nrd h))} = Pset Λ q' k from rfl,
      hk]
    exact inter_Pset_eq_image hΛo ha hb q' hP2 hI₀r hn₀I hcop ε m
  have hqm : ((q' : ℚ) ^ m) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hqprime.ne_zero)
  have hJd : J = (fun y => (((N : ℚ) / (q' : ℚ) ^ m : ℚ) : ℍ[ℚ, a, b]) * y) ''
      (Submodule.ofFiniteIdele Λ x : Set ℍ[ℚ, a, b]) := by
    refine eq_image_div_of_eq_image hqm hT ?_
    rw [hsplit', QuaternionAlgebra.coe_pow, coe_natCast]
  set d : (ℍ[ℚ, a, b])ˣ := ratUnit ((N : ℚ) / (q' : ℚ) ^ m) (div_ne_zero hNq hqm) with hddef
  have hd : star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) = star '' J := by
    rw [coe_units_smul, val_ratUnit, ← hJd]

  set L₀ : Ideal ↥(rationalEndSubring κ X₀) := preIdeal X₀ hΛo θ hθΛ (Submodule.ofFiniteIdele Λ x₀) hI₀r
    with hL₀
  have hn₀L : (n₀ : ↥(rationalEndSubring κ X₀)) ∈ L₀ :=
    natCast_mem_preIdeal X₀ hΛo θ hθΛ (Submodule.ofFiniteIdele Λ x₀) hI₀r hn₀I
  have hnotdvd : ¬ q' ∣ n₀ := (Nat.Prime.coprime_iff_not_dvd hqprime).mp hcop
  have hn₀κ : (n₀ : κ) ≠ 0 := fun h => hnotdvd ((CharP.cast_eq_zero_iff κ q' n₀).mp h)
  set H : AddSubgroup (Pt X₀) := jointKer X₀ L₀ with hH
  have hHcard : ((Nat.card H : ℕ) : κ) ≠ 0 := by
    intro h
    have hdvd := natCard_jointKer_dvd X₀ L₀ hn₀κ hn₀L
    have hq : q' ∣ Nat.card H := (CharP.cast_eq_zero_iff κ q' _).mp h
    exact hnotdvd (hqprime.dvd_of_dvd_pow (dvd_trans hq hdvd))

  have hA : ∀ r : ↥(rationalEndSubring κ X₀),
      (∀ P : Pt X₀, (∀ l ∈ L₀, (l : AddMonoid.End (Pt X₀)) P = 0) → (r : AddMonoid.End (Pt X₀)) P = 0) →
        r ∈ L₀ :=
    fun r hr => WeierstrassCurve.mem_ideal_rationalEndSubring_of_forall_apply_eq_zero X₀ a b Λ hΛo θ hθ hθΛ
      L₀ n₀ hn₀κ hn₀L r hr
  have himg : θ '' (L₀ : Set ↥(rationalEndSubring κ X₀)) = star '' (Submodule.ofFiniteIdele Λ x₀ : Set ℍ[ℚ, a, b]) :=
    image_preIdeal X₀ hΛo θ hθΛ _ hx₀ hI₀r

  have hε : ε = 0 ∨ ε = 1 := by rw [hεdef]; omega
  rcases hε with hε0 | hε1
  ·
    have hJ0 : J = (Submodule.ofFiniteIdele Λ x₀ : Set ℍ[ℚ, a, b]) := by
      rw [hJ, hε0, Pset_zero_eq hΛo ha hb, Set.inter_eq_left]
      exact hx₀
    obtain ⟨W, hW, χ, hχ, hχs, hker, huniv⟩ :=
      WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp X₀ H hHcard
    refine ⟨W, hW, χ, hχ, ?_, d, ?_⟩
    · intro h0
      obtain ⟨P, hP⟩ := exists_point_ne_zero W
      obtain ⟨Q, rfl⟩ := hχs P
      exact hP (by rw [h0]; rfl)
    · rw [hd, hJ0, ← himg, kernelIdealSet_eq_of_forall X₀ W L₀ hA χ hker huniv]
  ·
    obtain ⟨W₁, hW₁, π, hπ, hπ0, hπinj, hKπ⟩ :=
      exists_injective_mem_rationalHomSet_kernelIdealSet_eq_nrd_dvd q' X₀ hss a b hdef Λ hΛ θ hθ hθΛ
    haveI := hW₁
    have hH₁card : ((Nat.card (H.map π) : ℕ) : κ) ≠ 0 := by
      rwa [AddSubgroup.card_map_of_injective hπinj]
    obtain ⟨W, hW, χ₂, hχ₂, hχ₂s, hker₂, huniv₂⟩ :=
      WeierstrassCurve.exists_mem_rationalHomSet_ker_eq_forall_exists_eq_comp W₁ (H.map π) hH₁card
    refine ⟨W, hW, χ₂.comp π, WeierstrassCurve.comp_mem_rationalHomSet κ X₀ W₁ W hπ hχ₂, ?_, d, ?_⟩
    · intro h0
      obtain ⟨P, hP⟩ := exists_point_ne_zero W
      have hπs := WeierstrassCurve.surjective_of_mem_rationalHomSet κ hπ hπ0
      obtain ⟨Q, rfl⟩ := (hχ₂s.comp hπs) P
      exact hP (by change (χ₂.comp π) Q = 0; rw [h0]; rfl)
    · rw [hd, kernelIdealSet_comp_eq X₀ W₁ W L₀ hA π hπ χ₂ hχ₂ hker₂ huniv₂, Set.image_inter hθ, himg, hKπ,
        hJ, hε1, star_image_inter, star_image_Pset hΛo]
      congr 1

end S_CerednikDrinfeld_exists_kernelIdealSet_eq_star_smul_ofFiniteIdele
end P2MW
export P2MW.S_CerednikDrinfeld_exists_kernelIdealSet_eq_star_smul_ofFiniteIdele (solution)
