-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6fdb3cbe-2239-5c46-bd5c-706314f6ac26

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn
import Theorems.Thm_CerednikDrinfeld_Omega_exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc
import Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_exists_pmoebius_mem_affinoid_of_finite_quotVert
import Theorems.Thm_CerednikDrinfeld_Omega_exists_holRing_ne_zero_forall_le_ordAt_smul
import Theorems.Thm_CerednikDrinfeld_Omega_exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq
import Theorems.Thm_CerednikDrinfeld_Omega_forall_exists_finset_v_sub_lt_pow_of_finite_quotient
import Theorems.Thm_CerednikDrinfeld_Omega_isDiscrete_of_finite_stabilizer_stdVertex
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero
import Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero
import Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero
import Theorems.Thm_CerednikDrinfeld_Omega_inv_mem_holOn_of_forall_le_v_apply
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_disc_of_mem_holOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant
p2m_attr_erase "instance" "AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqV AlgebraicCurve.TotallyDegenerateCovering.instFintypeV AlgebraicCurve.TotallyDegenerateCovering.instDecidableEqE AlgebraicCurve.TotallyDegenerateCovering.instFintypeE instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "simp" "AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_b AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_w AlgebraicCurve.TotallyDegenerateCovering.toDegeneracyData_a AlgebraicCurve.TotallyDegenerateCovering.mk.sizeOf_spec AlgebraicCurve.TotallyDegenerateCovering.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq"

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant.CerednikDrinfeld.Omega CerednikDrinfeld.Mumford"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Mumford.ActsThrough Mumford.GraphAction Mumford.QuotVert tree BruhatTits.tree Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid Omega.eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn Omega.exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc Omega.exists_forall_exists_pmoebius_mem_affinoid_of_finite_quotVert Omega.exists_holRing_ne_zero_forall_le_ordAt_smul Omega.exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq Omega.forall_exists_finset_v_sub_lt_pow_of_finite_quotient Omega.isDiscrete_of_finite_stabilizer_stdVertex Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero Omega.exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero Omega.exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero Omega.inv_mem_holOn_of_forall_le_v_apply Omega.finite_setOf_apply_eq_zero_disc_of_mem_holOn"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid affinoid_subset_upperHalfPlane IsExhausted IsHolOn IsHolOn.const holOn restrictAffinoid holRing coe_smul_upperHalfPlane pmoebius upperHalfPlane coord_mem_holRing coordSub ordAt IsDiscrete exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc exists_forall_exists_pmoebius_mem_affinoid_of_finite_quotVert exists_holRing_ne_zero_forall_le_ordAt_smul exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq forall_exists_finset_v_sub_lt_pow_of_finite_quotient isDiscrete_of_finite_stabilizer_stdVertex exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero inv_mem_holOn_of_forall_le_v_apply finite_setOf_apply_eq_zero_disc_of_mem_holOn"
namespace FracHolAux
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem isHolOn_restrict {S S' : Set K} (hS : S' ⊆ S) {f : ↥S → K} (hf : IsHolOn K S f) :
    IsHolOn K S' (fun w : ↥S' => f ⟨(w : K), hS w.2⟩) := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  refine ⟨r, fun k z hz => hr k z (hS hz), ⟨b, fun k w => hb k ⟨(w : K), hS w.2⟩⟩, ?_⟩
  exact hlim.comp (fun w : ↥S' => (⟨(w : K), hS w.2⟩ : ↥S))

theorem mem_affinoid_of_v_sub_le (ϖ : PseudoUniformizer K₀ K) (n : ℕ) {z : K} (hz : z ∈ affinoid ϖ n)
    {w : K} (hw : Valued.v (w - z) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1)) : w ∈ affinoid ϖ n := by
  obtain ⟨hz1, hz2⟩ := hz
  have hp0 := ϖ.pos
  have hp1 := ϖ.lt_one
  have hlt : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n :=
    pow_lt_pow_right_of_lt_one₀ hp0 hp1 (Nat.lt_succ_self n)
  have hle1 : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) ≤ 1 := pow_le_one₀ zero_le' hp1.le
  have hge1 : (1 : Γ₀) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n := one_le_pow₀ ((one_le_inv₀ hp0).2 hp1.le)
  refine ⟨?_, fun a ha => ?_⟩
  · have : w = (w - z) + z := by ring
    rw [this]
    refine (Valuation.map_add _ _ _).trans (max_le (hw.trans (hle1.trans hge1)) hz1)
  · have hza := hz2 a ha
    have hlt' : Valued.v (w - z) < Valued.v (z - algebraMap K₀ K a) := lt_of_le_of_lt hw (lt_of_lt_of_le hlt hza)
    have : w - algebraMap K₀ K a = (z - algebraMap K₀ K a) + (w - z) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ hlt']
    exact hza

theorem disc_subset_affinoid (ϖ : PseudoUniformizer K₀ K) (n : ℕ) {z : K} (hz : z ∈ affinoid ϖ n)
    {s : K} (hs : Valued.v s ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1)) :
    ∀ w : K, Valued.v (w - z) ≤ Valued.v s → w ∈ affinoid ϖ n :=
  fun w hw => mem_affinoid_of_v_sub_le ϖ n hz (hw.trans hs)

theorem coordFn_mem_holOn (ϖ : PseudoUniformizer K₀ K) (n : ℕ) {S : Set K} (hS : S ⊆ affinoid ϖ n) :
    (fun z : ↥S => (z : K)) ∈ holOn K S :=
  isHolOn_restrict hS ((coord_mem_holRing ϖ) n)

theorem polyFn_mem_holOn (ϖ : PseudoUniformizer K₀ K) (n : ℕ) {S : Set K} (hS : S ⊆ affinoid ϖ n)
    {ι : Type} (Z : Finset ι) (c : ι → K) (k : ι → ℕ) :
    (fun z : ↥S => ∏ p ∈ Z, ((z : K) - c p) ^ k p) ∈ holOn K S := by
  classical
  induction Z using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact (holOn K S).one_mem
  | insert a s ha ih =>
    have : (fun z : ↥S => ∏ p ∈ insert a s, ((z : K) - c p) ^ k p) =
        (fun z : ↥S => ((z : K) - c a) ^ k a) * (fun z : ↥S => ∏ p ∈ s, ((z : K) - c p) ^ k p) := by
      funext z; simp only [Finset.prod_insert ha, Pi.mul_apply]
    rw [this]
    refine mul_mem ?_ ih
    have : (fun z : ↥S => ((z : K) - c a) ^ k a) = ((fun z : ↥S => (z : K)) - fun _ => c a) ^ k a := by
      funext z; simp only [Pi.pow_apply, Pi.sub_apply]
    rw [this]
    exact pow_mem (sub_mem (coordFn_mem_holOn ϖ n hS) ((IsHolOn.const S (c a)))) _

variable [CompleteSpace K] [IsAlgClosed K]

theorem le_of_forall_sub_pow_mul_eq (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ) (p : ↥(affinoid ϖ n)) {A B : ↥(affinoid ϖ n) → K}
    (hA : A ∈ holOn K (affinoid ϖ n)) (hB : B ∈ holOn K (affinoid ϖ n)) (hBp : B p ≠ 0) {a b : ℕ}
    (h : ∀ z : ↥(affinoid ϖ n), z ≠ p → ((z : K) - (p : K)) ^ a * A z = ((z : K) - (p : K)) ^ b * B z) :
    a ≤ b := by
  classical
  by_contra hab
  push Not at hab
  have hp0 := ϖ.pos
  have hp1 := ϖ.lt_one
  set d : ℕ := a - b with hd
  have hd1 : 1 ≤ d := by omega
  have had : a = b + d := by omega

  set P : ↥(affinoid ϖ n) → K := fun z => ((z : K) - (p : K)) ^ d with hP
  have hPhol : P ∈ holOn K (affinoid ϖ n) := by
    have := polyFn_mem_holOn ϖ n (subset_refl (affinoid ϖ n)) ({(0 : Unit)} : Finset Unit) (fun _ => (p : K)) (fun _ => d)
    simpa using this
  set g : ↥(affinoid ϖ n) → K := B - P * A with hg
  have hghol : g ∈ holOn K (affinoid ϖ n) := sub_mem hB (mul_mem hPhol hA)
  have hg0 : ∀ z : ↥(affinoid ϖ n), z ≠ p → g z = 0 := by
    intro z hz
    have hzp : ((z : K) - (p : K)) ^ b ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 fun h0 => hz (Subtype.ext h0))
    apply mul_left_cancel₀ hzp
    rw [mul_zero, hg, Pi.sub_apply, Pi.mul_apply, hP, mul_sub, ← mul_assoc, ← pow_add, ← had, h z hz, sub_self]
  have hπne : (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) ≠ 0 := by
    intro h0; have := congrArg Valued.v h0; rw [map_pow, map_zero] at this; exact pow_ne_zero _ hp0.ne' this
  have hdisc := CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_disc_of_mem_holOn K hrk (affinoid ϖ n) (p : K)
    ((algebraMap K₀ K ϖ.ϖ) ^ (n + 1)) hπne ∅ (by simp)
    (fun w hw _ => mem_affinoid_of_v_sub_le ϖ n p.2 (by rwa [map_pow] at hw)) hghol
  rcases hdisc with hall | hfin
  · have := hall p (by rw [sub_self, map_zero]; exact zero_le') (by simp)
    rw [hg, Pi.sub_apply, Pi.mul_apply, hP] at this
    simp only [sub_self, zero_pow (by omega : d ≠ 0), zero_mul, sub_zero] at this
    exact hBp this
  · set pt : ℕ → ↥(affinoid ϖ n) := fun k => ⟨(p : K) + (algebraMap K₀ K ϖ.ϖ) ^ (n + 1 + k),
      mem_affinoid_of_v_sub_le ϖ n p.2 (by
        rw [add_sub_cancel_left, map_pow, pow_add]
        exact mul_le_of_le_one_right' (pow_le_one₀ zero_le' hp1.le))⟩ with hpt
    have hinj : Function.Injective pt := by
      intro k l hkl
      have h1 : (algebraMap K₀ K ϖ.ϖ) ^ (n + 1 + k) = (algebraMap K₀ K ϖ.ϖ) ^ (n + 1 + l) := by
        have := congrArg (fun x : ↥(affinoid ϖ n) => (x : K)) hkl
        simpa [hpt] using this
      have h2 := congrArg Valued.v h1
      rw [map_pow, map_pow] at h2
      have := (pow_right_strictAnti₀ hp0 hp1).injective h2
      omega
    have hne : ∀ k, pt k ≠ p := by
      intro k hk
      have := congrArg (fun x : ↥(affinoid ϖ n) => (x : K)) hk
      simp only [hpt] at this
      have h2 : (algebraMap K₀ K ϖ.ϖ) ^ (n + 1 + k) = 0 := by linear_combination this
      have h3 := congrArg Valued.v h2
      rw [map_pow, map_zero] at h3
      exact pow_ne_zero _ hp0.ne' h3
    have hsub : Set.range pt ⊆ {w : ↥(affinoid ϖ n) |
        Valued.v ((w : K) - (p : K)) ≤ Valued.v ((algebraMap K₀ K ϖ.ϖ) ^ (n + 1)) ∧
        (∀ ζ ∈ (∅ : Finset K), Valued.v ((algebraMap K₀ K ϖ.ϖ) ^ (n + 1)) ≤ Valued.v ((w : K) - ζ)) ∧ g w = 0} := by
      rintro w ⟨k, rfl⟩
      refine ⟨?_, by simp, hg0 _ (hne k)⟩
      show Valued.v ((p : K) + (algebraMap K₀ K ϖ.ϖ) ^ (n + 1 + k) - (p : K)) ≤ _
      rw [add_sub_cancel_left, map_pow, map_pow, pow_add]
      exact mul_le_of_le_one_right' (pow_le_one₀ zero_le' hp1.le)
    exact (Set.infinite_range_of_injective hinj) (hfin.subset hsub)

end CerednikDrinfeld.Omega.FracHolAux

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Mumford.ActsThrough Mumford.GraphAction Mumford.QuotVert tree BruhatTits.tree Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid Omega.eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn Omega.exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc Omega.exists_forall_exists_pmoebius_mem_affinoid_of_finite_quotVert Omega.exists_holRing_ne_zero_forall_le_ordAt_smul Omega.exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq Omega.forall_exists_finset_v_sub_lt_pow_of_finite_quotient Omega.isDiscrete_of_finite_stabilizer_stdVertex Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero Omega.exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero Omega.exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero Omega.inv_mem_holOn_of_forall_le_v_apply Omega.finite_setOf_apply_eq_zero_disc_of_mem_holOn"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "PseudoUniformizer affinoid affinoid_subset_upperHalfPlane IsExhausted IsHolOn IsHolOn.const holOn restrictAffinoid holRing coe_smul_upperHalfPlane pmoebius upperHalfPlane coord_mem_holRing coordSub ordAt IsDiscrete exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc exists_forall_exists_pmoebius_mem_affinoid_of_finite_quotVert exists_holRing_ne_zero_forall_le_ordAt_smul exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq forall_exists_finset_v_sub_lt_pow_of_finite_quotient isDiscrete_of_finite_stabilizer_stdVertex exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero inv_mem_holOn_of_forall_le_v_apply finite_setOf_apply_eq_zero_disc_of_mem_holOn"
namespace FracHolAux
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]

theorem prod_eq_pow_mul_prod_erase {ι : Type} [DecidableEq ι] (Z : Finset ι) (c : ι → K) (k : ι → ℕ)
    (p : ι) (hk : p ∉ Z → k p = 0) (w : K) :
    (∏ q ∈ Z, (w - c q) ^ k q) = (w - c p) ^ k p * ∏ q ∈ Z.erase p, (w - c q) ^ k q := by
  by_cases hp : p ∈ Z
  · rw [Finset.mul_prod_erase Z (fun q => (w - c q) ^ k q) hp]
  · rw [Finset.erase_eq_of_notMem hp, hk hp, pow_zero, one_mul]

theorem pres (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hholes : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {F : ↥(upperHalfPlane K₀ K) → K} {f g : ↥(affinoid ϖ n) → K}
    (hrep : ∀ w : ↥(affinoid ϖ n), g w ≠ 0 →
      g w * F ⟨(w : K), affinoid_subset_upperHalfPlane ϖ n w.2⟩ = f w)
    (Zf Zg : Finset ↥(affinoid ϖ n)) (jf kg : ↥(affinoid ϖ n) → ℕ) (uf ug : ↥(affinoid ϖ n) → K)
    (huf : uf ∈ holOn K (affinoid ϖ n)) (hug : ug ∈ holOn K (affinoid ϖ n))
    (hug0 : ∀ z : ↥(affinoid ϖ n), ug z ≠ 0)
    (hjf : ∀ q : ↥(affinoid ϖ n), q ∈ Zf ↔ 1 ≤ jf q) (hkg : ∀ q : ↥(affinoid ϖ n), q ∈ Zg ↔ 1 ≤ kg q)
    (hfeq : ∀ z : ↥(affinoid ϖ n), f z = (∏ q ∈ Zf, ((z : K) - (q : K)) ^ jf q) * uf z)
    (hgeq : ∀ z : ↥(affinoid ϖ n), g z = (∏ q ∈ Zg, ((z : K) - (q : K)) ^ kg q) * ug z)
    (p : ↥(affinoid ϖ n)) (hnv : kg p ≤ jf p ∨ uf p ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ ∃ hE : (∀ w : K, Valued.v (w - (p : K)) ≤ Valued.v s → w ∈ affinoid ϖ n),
      ∃ φ : ↥{w : K | Valued.v (w - (p : K)) ≤ Valued.v s} → K,
        φ ∈ holOn K {w : K | Valued.v (w - (p : K)) ≤ Valued.v s} ∧
        (kg p - jf p = 0 ∨ φ ⟨(p : K), by simp⟩ ≠ 0) ∧
        ∀ w : ↥{w : K | Valued.v (w - (p : K)) ≤ Valued.v s}, (w : K) ≠ (p : K) →
          ((w : K) - (p : K)) ^ (kg p - jf p) *
              F ⟨(w : K), affinoid_subset_upperHalfPlane ϖ n (hE (w : K) w.2)⟩ = φ w := by
  classical
  have hp0 := ϖ.pos
  have hp1 := ϖ.lt_one

  set S' : Finset ↥(affinoid ϖ n) := (Zf ∪ Zg).erase p with hS'
  have hS'ne : ∀ q ∈ S', (q : K) - (p : K) ≠ 0 := by
    intro q hq h0
    exact (Finset.mem_erase.1 hq).1 (Subtype.ext (sub_eq_zero.1 h0))

  have hm : ∀ q : ↥(affinoid ϖ n), ∃ m : ℕ, q ∈ S' → Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m ≤ Valued.v ((q : K) - (p : K)) := by
    intro q
    by_cases hq : q ∈ S'
    · obtain ⟨m, hm⟩ := hrk _ _ hp1 (hS'ne q hq)
      exact ⟨m, fun _ => hm⟩
    · exact ⟨0, fun h => absurd h hq⟩
  choose mq hmq using hm
  set L : ℕ := ∑ q ∈ S', (mq q + 1) with hL
  set s : K := (algebraMap K₀ K ϖ.ϖ) ^ (n + 1 + L) with hs
  have hvs : Valued.v s = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1 + L) := by rw [hs, map_pow]
  have hs0 : s ≠ 0 := by
    intro h0; have := congrArg Valued.v h0; rw [hvs, map_zero] at this; exact pow_ne_zero _ hp0.ne' this
  have hsle : Valued.v s ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) := by
    rw [hvs]; exact pow_le_pow_right_of_le_one' hp1.le (by omega)
  have hslt : ∀ q ∈ S', Valued.v s < Valued.v ((q : K) - (p : K)) := by
    intro q hq
    have h1 : mq q + 1 ≤ n + 1 + L := by
      have : mq q + 1 ≤ L := Finset.single_le_sum (f := fun q => mq q + 1) (fun _ _ => Nat.zero_le _) hq
      omega
    calc Valued.v s = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1 + L) := hvs
      _ ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (mq q + 1) := pow_le_pow_right_of_le_one' hp1.le h1
      _ < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ mq q := pow_lt_pow_right_of_lt_one₀ hp0 hp1 (Nat.lt_succ_self _)
      _ ≤ _ := hmq q hq
  have hE : ∀ w : K, Valued.v (w - (p : K)) ≤ Valued.v s → w ∈ affinoid ϖ n :=
    disc_subset_affinoid ϖ n p.2 hsle
  refine ⟨s, hs0, hE, ?_⟩

  have hwq : ∀ (w : K), Valued.v (w - (p : K)) ≤ Valued.v s → ∀ q ∈ S',
      Valued.v (w - (q : K)) = Valued.v ((p : K) - (q : K)) := by
    intro w hw q hq
    have hlt : Valued.v (w - (p : K)) < Valued.v ((p : K) - (q : K)) := by
      rw [Valuation.map_sub_swap _ (p : K)]; exact lt_of_le_of_lt hw (hslt q hq)
    have : w - (q : K) = ((p : K) - (q : K)) + (w - (p : K)) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ hlt]
  have hwq0 : ∀ (w : K), Valued.v (w - (p : K)) ≤ Valued.v s → ∀ q ∈ S', w - (q : K) ≠ 0 := by
    intro w hw q hq h0
    have := hwq w hw q hq
    rw [h0, map_zero, eq_comm, map_eq_zero, sub_eq_zero] at this
    exact hS'ne q hq (by rw [this, sub_self])

  set E : Set K := {w : K | Valued.v (w - (p : K)) ≤ Valued.v s} with hEdef
  have hEsub : E ⊆ affinoid ϖ n := fun w hw => hE w hw
  set Rf : ↥E → K := fun w => (∏ q ∈ Zf.erase p, ((w : K) - (q : K)) ^ jf q) * uf ⟨(w : K), hE (w : K) w.2⟩ with hRf
  set Rg : ↥E → K := fun w => (∏ q ∈ Zg.erase p, ((w : K) - (q : K)) ^ kg q) * ug ⟨(w : K), hE (w : K) w.2⟩ with hRg
  have hRf_hol : Rf ∈ holOn K E :=
    mul_mem (polyFn_mem_holOn ϖ n hEsub (Zf.erase p) (fun q => (q : K)) jf) (isHolOn_restrict hEsub huf)
  have hRg_hol : Rg ∈ holOn K E :=
    mul_mem (polyFn_mem_holOn ϖ n hEsub (Zg.erase p) (fun q => (q : K)) kg) (isHolOn_restrict hEsub hug)

  obtain ⟨δ, hδ0, hδ⟩ := CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero
    K₀ K ϖ hrk n hholes hug hug0
  have hZgS' : Zg.erase p ⊆ S' := by
    intro q hq; rw [hS', Finset.mem_erase] at *; exact ⟨hq.1, Finset.mem_union_right _ hq.2⟩
  have hZfS' : Zf.erase p ⊆ S' := by
    intro q hq; rw [hS', Finset.mem_erase] at *; exact ⟨hq.1, Finset.mem_union_left _ hq.2⟩
  have hRg_v : ∀ w : ↥E, Valued.v ((∏ q ∈ Zg.erase p, ((p : K) - (q : K)) ^ kg q) * δ) ≤ Valued.v (Rg w) := by
    intro w
    rw [hRg, map_mul, map_mul, map_prod, map_prod]
    refine mul_le_mul' (le_of_eq ?_) (hδ _)
    refine Finset.prod_congr rfl fun q hq => ?_
    rw [map_pow, map_pow, hwq (w : K) w.2 q (hZgS' hq)]
  have hcδ0 : (∏ q ∈ Zg.erase p, ((p : K) - (q : K)) ^ kg q) * δ ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun q hq => pow_ne_zero _ ?_) hδ0
    intro h0; exact hS'ne q (hZgS' hq) (by rw [← neg_sub, h0, neg_zero])
  have hRg0 : ∀ w : ↥E, Rg w ≠ 0 := by
    intro w h0
    have := hRg_v w
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hcδ0 this
  have hRginv_hol : (fun w : ↥E => (Rg w)⁻¹) ∈ holOn K E :=
    CerednikDrinfeld.Omega.inv_mem_holOn_of_forall_le_v_apply K E hRg_hol _ hcδ0 hRg_v

  have hjf0 : p ∉ Zf → jf p = 0 := fun h => by
    have h2 : ¬ (1 ≤ jf p) := fun h1 => h ((hjf p).2 h1)
    omega
  have hkg0 : p ∉ Zg → kg p = 0 := fun h => by
    have h2 : ¬ (1 ≤ kg p) := fun h1 => h ((hkg p).2 h1)
    omega

  set φ : ↥E → K := fun w => ((w : K) - (p : K)) ^ (jf p - kg p) * Rf w * (Rg w)⁻¹ with hφ
  refine ⟨φ, ?_, ?_, ?_⟩
  ·
    have : φ = (fun w : ↥E => ((w : K) - (p : K)) ^ (jf p - kg p)) * Rf * fun w => (Rg w)⁻¹ := by
      funext w; simp only [hφ, Pi.mul_apply]
    rw [this]
    refine mul_mem (mul_mem ?_ hRf_hol) hRginv_hol
    have := polyFn_mem_holOn ϖ n hEsub ({(0 : Unit)} : Finset Unit) (fun _ => (p : K)) (fun _ => jf p - kg p)
    simpa using this
  ·
    by_cases hc : kg p - jf p = 0
    · exact Or.inl hc
    · right
      have hj : jf p - kg p = 0 := by omega
      have hufp : uf p ≠ 0 := by
        rcases hnv with h | h
        · exact absurd (by omega : kg p - jf p = 0) hc
        · exact h
      have hRfp : Rf ⟨(p : K), by simp [hEdef]⟩ ≠ 0 := by
        rw [hRf]
        refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun q hq => pow_ne_zero _ ?_) hufp
        exact hwq0 (p : K) (by simp) q (hZfS' hq)
      show ((p : K) - (p : K)) ^ (jf p - kg p) * Rf ⟨(p : K), _⟩ * (Rg ⟨(p : K), _⟩)⁻¹ ≠ 0
      rw [hj, pow_zero, one_mul]
      exact mul_ne_zero hRfp (inv_ne_zero (hRg0 _))
  ·
    intro w hwp
    have hwE : (w : K) ∈ affinoid ϖ n := hE (w : K) w.2
    have hX : (w : K) - (p : K) ≠ 0 := sub_ne_zero.2 hwp
    have hfw : f ⟨(w : K), hwE⟩ = ((w : K) - (p : K)) ^ jf p * Rf w := by
      rw [hfeq, hRf, ← mul_assoc, prod_eq_pow_mul_prod_erase Zf (fun q => (q : K)) jf p hjf0]
    have hgw : g ⟨(w : K), hwE⟩ = ((w : K) - (p : K)) ^ kg p * Rg w := by
      rw [hgeq, hRg, ← mul_assoc, prod_eq_pow_mul_prod_erase Zg (fun q => (q : K)) kg p hkg0]
    have hgne : g ⟨(w : K), hwE⟩ ≠ 0 := by
      rw [hgw]; exact mul_ne_zero (pow_ne_zero _ hX) (hRg0 w)
    have hFw : F ⟨(w : K), affinoid_subset_upperHalfPlane ϖ n hwE⟩ =
        f ⟨(w : K), hwE⟩ / g ⟨(w : K), hwE⟩ := by
      rw [eq_div_iff hgne, mul_comm]; exact hrep ⟨(w : K), hwE⟩ hgne
    have hexp : (kg p - jf p) + jf p = (jf p - kg p) + kg p := by omega
    have key : ((w : K) - (p : K)) ^ (kg p - jf p) * ((w : K) - (p : K)) ^ jf p =
        ((w : K) - (p : K)) ^ (jf p - kg p) * ((w : K) - (p : K)) ^ kg p := by
      rw [← pow_add, ← pow_add, hexp]
    show ((w : K) - (p : K)) ^ (kg p - jf p) * F ⟨(w : K), _⟩ =
      ((w : K) - (p : K)) ^ (jf p - kg p) * Rf w * (Rg w)⁻¹
    rw [hFw, hfw, hgw]
    have hRgw := hRg0 w
    have hXk : ((w : K) - (p : K)) ^ kg p ≠ 0 := pow_ne_zero _ hX
    calc ((w : K) - (p : K)) ^ (kg p - jf p) * (((w : K) - (p : K)) ^ jf p * Rf w /
            (((w : K) - (p : K)) ^ kg p * Rg w))
          = (((w : K) - (p : K)) ^ (kg p - jf p) * ((w : K) - (p : K)) ^ jf p) * Rf w /
            (((w : K) - (p : K)) ^ kg p * Rg w) := by ring
      _ = (((w : K) - (p : K)) ^ (jf p - kg p) * ((w : K) - (p : K)) ^ kg p) * Rf w /
            (((w : K) - (p : K)) ^ kg p * Rg w) := by rw [key]
      _ = ((w : K) - (p : K)) ^ (jf p - kg p) * Rf w * (Rg w)⁻¹ := by
            field_simp

end CerednikDrinfeld.Omega.FracHolAux

open CerednikDrinfeld.Omega.FracHolAux in
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

    (F : ↥(upperHalfPlane K₀ K) → K)
    (hinv : ∀ (γ : G) (z w : ↥(upperHalfPlane K₀ K)), (w : K) = pmoebius K₀ (ρ γ) (z : K) → F w = F z)
    (hmer : ∀ n : ℕ, ∃ f g : ↥(affinoid ϖ₁ n) → K, f ∈ holOn K (affinoid ϖ₁ n) ∧ g ∈ holOn K (affinoid ϖ₁ n) ∧
      (∃ z : ↥(affinoid ϖ₁ n), g z ≠ 0) ∧
      ∀ z : ↥(affinoid ϖ₁ n), g z ≠ 0 →
        g z * F ⟨(z : K), affinoid_subset_upperHalfPlane ϖ₁ n z.2⟩ = f z) :
    ∃ Φ H : ↥(holRing ϖ₁), H ≠ 0 ∧
      ∀ n : ℕ, ∃ Z : Set ↥(affinoid ϖ₁ n), Z.Finite ∧
        ∀ z : ↥(affinoid ϖ₁ n), z ∉ Z →
          (H : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ₁ n z.2⟩ *
              F ⟨(z : K), affinoid_subset_upperHalfPlane ϖ₁ n z.2⟩ =
            (Φ : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ₁ n z.2⟩ := by
  classical
  have hholes := CerednikDrinfeld.Omega.forall_exists_finset_v_sub_lt_pow_of_finite_quotient R K₀ ϖ hϖ K hint hv hq ϖ₁
  have hdisc : IsDiscrete K ρ := by
    refine CerednikDrinfeld.Omega.isDiscrete_of_finite_stabilizer_stdVertex R K₀ ϖ hϖ K hint hv hq ρ ?_
    have hfin0 := hfin (LT.LatticeTree.stdVertex R K₀)
    have : {γ : G | ρ γ • LT.LatticeTree.stdVertex R K₀ = LT.LatticeTree.stdVertex R K₀} =
        ((MulAction.stabilizer G (LT.LatticeTree.stdVertex R K₀)) : Set G) := by
      ext γ; simp only [Set.mem_setOf_eq, SetLike.mem_coe, MulAction.mem_stabilizer_iff, hρ γ]
    rw [this]
    exact Set.toFinite _
  obtain ⟨N, hN⟩ := CerednikDrinfeld.Omega.exists_forall_exists_pmoebius_mem_affinoid_of_finite_quotVert
    R K₀ ϖ hϖ K hint hv hq ϖ₁ hex ρ hρ
  obtain ⟨fN, gN, hfN, hgN, hgNne, hrepN⟩ := hmer N
  obtain ⟨ZN, kN, uN, huN, huN0, hkN, hgNfac⟩ :=
    CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid K₀ K ϖ₁ hrk N (hholes N) hgN hgNne
  have hkM : ∀ p ∈ ZN, kN p ≤ ∑ p ∈ ZN, kN p := fun p hp =>
    Finset.single_le_sum (f := kN) (fun _ _ => Nat.zero_le _) hp
  obtain ⟨H, hH0, hHord⟩ := CerednikDrinfeld.Omega.exists_holRing_ne_zero_forall_le_ordAt_smul
    K₀ K ϖ₁ hrk hex hholes ρ hdisc (ι := ↥ZN)
    (fun p => (⟨((p : ↥(affinoid ϖ₁ N)) : K), affinoid_subset_upperHalfPlane ϖ₁ N (p : ↥(affinoid ϖ₁ N)).2⟩ :
      ↥(upperHalfPlane K₀ K)))
    (fun _ => ∑ p ∈ ZN, kN p)

  obtain ⟨ZfN, jN, ufN, hufN, hjN, hfNfac, hnvN⟩ : ∃ (ZfN : Finset ↥(affinoid ϖ₁ N)) (jN : ↥(affinoid ϖ₁ N) → ℕ)
      (ufN : ↥(affinoid ϖ₁ N) → K), ufN ∈ holOn K (affinoid ϖ₁ N) ∧
      (∀ q : ↥(affinoid ϖ₁ N), q ∈ ZfN ↔ 1 ≤ jN q) ∧
      (∀ z : ↥(affinoid ϖ₁ N), fN z = (∏ q ∈ ZfN, ((z : K) - (q : K)) ^ jN q) * ufN z) ∧
      (∀ q : ↥(affinoid ϖ₁ N), kN q ≤ jN q ∨ ufN q ≠ 0) := by
    by_cases hfNne : ∃ z : ↥(affinoid ϖ₁ N), fN z ≠ 0
    · obtain ⟨ZfN, jN, ufN, hufN, hufN0, hjN, hfNfac⟩ :=
        CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid K₀ K ϖ₁ hrk N (hholes N) hfN hfNne
      exact ⟨ZfN, jN, ufN, hufN, hjN, hfNfac, fun q => Or.inr (hufN0 q)⟩
    · push Not at hfNne
      exact ⟨ZN, kN, 0, (holOn K (affinoid ϖ₁ N)).zero_mem, hkN, fun z => by rw [hfNne z, Pi.zero_apply, mul_zero],
        fun q => Or.inl le_rfl⟩

  have hnum : ∀ n : ℕ, ∃ ψ : ↥(affinoid ϖ₁ n) → K, ψ ∈ holOn K (affinoid ϖ₁ n) ∧
      ∃ Z : Set ↥(affinoid ϖ₁ n), Z.Finite ∧ ∀ z : ↥(affinoid ϖ₁ n), z ∉ Z →
        (fun w : ↥(upperHalfPlane K₀ K) => (H : ↥(upperHalfPlane K₀ K) → K) w * F w)
          ⟨(z : K), affinoid_subset_upperHalfPlane ϖ₁ n z.2⟩ = ψ z := by
    intro n

    obtain ⟨fn, gn, hfn, hgn, hgnne, hrepn⟩ := hmer n
    obtain ⟨Zn, kn, un, hun, hun0, hkn, hgnfac⟩ :=
      CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid K₀ K ϖ₁ hrk n (hholes n) hgn hgnne
    obtain ⟨wn, hwn, hunwn⟩ :=
      CerednikDrinfeld.Omega.exists_mem_holOn_mul_eq_one_of_forall_apply_ne_zero K₀ K ϖ₁ hrk n (hholes n) hun hun0
    set Hn : ↥(affinoid ϖ₁ n) → K := restrictAffinoid ϖ₁ n (H : ↥(upperHalfPlane K₀ K) → K) with hHn
    have hHn_hol : Hn ∈ holOn K (affinoid ϖ₁ n) := H.2 n
    have hHn_apply : ∀ z : ↥(affinoid ϖ₁ n),
        Hn z = (H : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), affinoid_subset_upperHalfPlane ϖ₁ n z.2⟩ := fun z => rfl

    have hPz : ∀ z : ↥(affinoid ϖ₁ n), z ∉ Zn → (∏ p ∈ Zn, ((z : K) - (p : K)) ^ kn p) ≠ 0 := by
      intro z hz
      refine Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (sub_ne_zero.2 fun h => hz ?_)
      rwa [show z = p from Subtype.ext h]
    have hgz : ∀ z : ↥(affinoid ϖ₁ n), z ∉ Zn → gn z ≠ 0 := by
      intro z hz; rw [hgnfac z]; exact mul_ne_zero (hPz z hz) (hun0 z)
    have hunw : ∀ z : ↥(affinoid ϖ₁ n), un z * wn z = 1 := fun z => by
      have := congrArg (fun f : ↥(affinoid ϖ₁ n) → K => f z) hunwn; simpa using this

    suffices hclaim : ∃ ψ₀ : ↥(affinoid ϖ₁ n) → K, ψ₀ ∈ holOn K (affinoid ϖ₁ n) ∧
        ∀ z : ↥(affinoid ϖ₁ n), Hn z * fn z = (∏ p ∈ Zn, ((z : K) - (p : K)) ^ kn p) * ψ₀ z by
      obtain ⟨ψ₀, hψ₀, hψ₀eq⟩ := hclaim
      refine ⟨fun z => ψ₀ z * wn z, mul_mem hψ₀ hwn, (↑Zn : Set ↥(affinoid ϖ₁ n)), Zn.finite_toSet,
        fun z hz => ?_⟩
      have hz' : z ∉ Zn := fun h => hz (Finset.mem_coe.2 h)
      have h1 := hψ₀eq z
      rw [← hrepn z (hgz z hz'), hgnfac z] at h1
      have h2 : Hn z * F ⟨(z : K), affinoid_subset_upperHalfPlane ϖ₁ n z.2⟩ * un z = ψ₀ z := by
        apply mul_left_cancel₀ (hPz z hz')
        linear_combination h1
      show (H : ↥(upperHalfPlane K₀ K) → K) ⟨(z : K), _⟩ * F ⟨(z : K), _⟩ = ψ₀ z * wn z
      rw [← h2, ← hHn_apply, mul_assoc (Hn z * F _), hunw z, mul_one]

    by_cases hΘ : ∃ z : ↥(affinoid ϖ₁ n), (Hn * fn) z ≠ 0
    swap
    · refine ⟨0, (holOn K (affinoid ϖ₁ n)).zero_mem, fun z => ?_⟩
      push Not at hΘ
      rw [Pi.zero_apply, mul_zero]; exact hΘ z
    have hfnne : ∃ z : ↥(affinoid ϖ₁ n), fn z ≠ 0 := by
      obtain ⟨z, hz⟩ := hΘ
      exact ⟨z, fun h0 => hz (by rw [Pi.mul_apply, h0, mul_zero])⟩
    obtain ⟨Zf, jf, uf, huf, huf0, hjf, hfnfac⟩ :=
      CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid K₀ K ϖ₁ hrk n (hholes n) hfn hfnne
    obtain ⟨ZΘ, kΘ, uΘ, huΘ, huΘ0, hkΘ, hΘfac⟩ :=
      CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid K₀ K ϖ₁ hrk n (hholes n)
        (mul_mem hHn_hol hfn) hΘ
    have hjf0 : ∀ p, p ∉ Zf → jf p = 0 := fun p h => by
      have h2 : ¬ (1 ≤ jf p) := fun h1 => h ((hjf p).2 h1); omega
    have hkn0 : ∀ p, p ∉ Zn → kn p = 0 := fun p h => by
      have h2 : ¬ (1 ≤ kn p) := fun h1 => h ((hkn p).2 h1); omega
    have hkΘ0 : ∀ p, p ∉ ZΘ → kΘ p = 0 := fun p h => by
      have h2 : ¬ (1 ≤ kΘ p) := fun h1 => h ((hkΘ p).2 h1); omega

    have hkey : ∀ p : ↥(affinoid ϖ₁ n), kn p ≤ kΘ p := by
      intro p
      by_cases hpZ : p ∈ Zn
      swap
      · rw [hkn0 p hpZ]; exact Nat.zero_le _
      set pΩ : ↥(upperHalfPlane K₀ K) := ⟨(p : K), affinoid_subset_upperHalfPlane ϖ₁ n p.2⟩ with hpΩ

      obtain ⟨H', hHfac, hH'p⟩ :=
        CerednikDrinfeld.Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero K₀ K hrk ϖ₁ hex hholes H hH0 pΩ
      have hstep_e : ordAt ϖ₁ H pΩ + jf p ≤ kΘ p := by
        refine le_of_forall_sub_pow_mul_eq ϖ₁ hrk n p
          (A := (restrictAffinoid ϖ₁ n (H' : ↥(upperHalfPlane K₀ K) → K)) *
            fun z : ↥(affinoid ϖ₁ n) => (∏ q ∈ Zf.erase p, ((z : K) - (q : K)) ^ jf q) * uf z)
          (B := fun z : ↥(affinoid ϖ₁ n) => (∏ q ∈ ZΘ.erase p, ((z : K) - (q : K)) ^ kΘ q) * uΘ z)
          (mul_mem (H'.2 n) (mul_mem (polyFn_mem_holOn ϖ₁ n subset_rfl _ _ _) huf))
          (mul_mem (polyFn_mem_holOn ϖ₁ n subset_rfl _ _ _) huΘ) ?_ fun z _ => ?_
        · refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun q hq => pow_ne_zero _ ?_) (huΘ0 p)
          exact sub_ne_zero.2 fun h => (Finset.mem_erase.1 hq).1 (Subtype.ext h).symm
        ·
          have hΘz : (Hn * fn) z = ((z : K) - (p : K)) ^ kΘ p *
              ((∏ q ∈ ZΘ.erase p, ((z : K) - (q : K)) ^ kΘ q) * uΘ z) := by
            rw [hΘfac z, ← mul_assoc, prod_eq_pow_mul_prod_erase ZΘ (fun q => (q : K)) kΘ p (hkΘ0 p)]
          have hHz : Hn z = ((z : K) - (p : K)) ^ ordAt ϖ₁ H pΩ *
              restrictAffinoid ϖ₁ n (H' : ↥(upperHalfPlane K₀ K) → K) z := by
            rw [hHn_apply, show (H : ↥(upperHalfPlane K₀ K) → K) = ((coordSub ϖ₁ pΩ ^ ordAt ϖ₁ H pΩ * H' :
              ↥(holRing ϖ₁)) : ↥(upperHalfPlane K₀ K) → K) from congrArg Subtype.val hHfac]
            rfl
          have hfz : fn z = ((z : K) - (p : K)) ^ jf p *
              ((∏ q ∈ Zf.erase p, ((z : K) - (q : K)) ^ jf q) * uf z) := by
            rw [hfnfac z, ← mul_assoc, prod_eq_pow_mul_prod_erase Zf (fun q => (q : K)) jf p (hjf0 p)]
          rw [← hΘz]
          simp only [Pi.mul_apply]
          rw [hHz, hfz, pow_add]
          ring

      obtain ⟨sA, hsA0, hEA, φA, hφA, hnvA, hidA⟩ := pres ϖ₁ hrk n (hholes n) hrepn Zf Zn jf kn uf un huf hun hun0
        hjf hkn hfnfac hgnfac p (Or.inr (huf0 p))

      obtain ⟨γ, hq⟩ := hN pΩ
      set q' : ↥(affinoid ϖ₁ N) := ⟨pmoebius K₀ (ρ γ) (pΩ : K), hq⟩ with hq'
      obtain ⟨sB, hsB0, hEB, φB, hφB, hnvB, hidB⟩ := pres ϖ₁ hrk N (hholes N) hrepN ZfN ZN jN kN ufN uN hufN huN huN0
        hjN hkN hfNfac hgNfac q' (hnvN q')
      obtain ⟨rB, hrB0, hDB, φB', hφB', hnvB', hidB'⟩ :=
        CerednikDrinfeld.Omega.exists_disc_forall_sub_pow_mul_eq_of_forall_pmoebius_eq_of_disc K₀ K ϖ₁ hrk ρ F hinv
          γ n N pΩ p.2 sB hsB0 hEB hφB (kN q' - jN q') hnvB hidB

      obtain ⟨r, hr0, hrA, hrB⟩ : ∃ r : K, r ≠ 0 ∧ Valued.v r ≤ Valued.v sA ∧ Valued.v r ≤ Valued.v rB := by
        rcases le_total (Valued.v sA) (Valued.v rB) with h | h
        · exact ⟨sA, hsA0, le_rfl, h⟩
        · exact ⟨rB, hrB0, h, le_rfl⟩
      set S : Set K := {w : K | Valued.v (w - (p : K)) ≤ Valued.v r} with hS
      have hSA : S ⊆ {w : K | Valued.v (w - (p : K)) ≤ Valued.v sA} := fun w hw => le_trans hw hrA
      have hSB : S ⊆ {w : K | Valued.v (w - (pΩ : K)) ≤ Valued.v rB} := fun w hw => le_trans hw hrB
      have hSn : S ⊆ affinoid ϖ₁ n := fun w hw => hEA w (hSA hw)
      have heq : kn p - jf p = kN q' - jN q' := by
        refine CerednikDrinfeld.Omega.eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn K hrk
          (S := S) ⟨(p : K), by simp [hS]⟩ r hr0 (fun z hz => hz)
          (algebraMap K₀ K ϖ₁.ϖ) (fun h0 => ?_) ϖ₁.lt_one
          (fun w : ↥S => F ⟨(w : K), affinoid_subset_upperHalfPlane ϖ₁ n (hSn w.2)⟩)
          (φ := fun w : ↥S => φA ⟨(w : K), hSA w.2⟩) (φ' := fun w : ↥S => φB' ⟨(w : K), hSB w.2⟩)
          (isHolOn_restrict hSA hφA) (isHolOn_restrict hSB hφB') hnvA hnvB'
          {⟨(p : K), by simp [hS]⟩} (Set.finite_singleton _) (fun w hw => ?_) (fun w hw => ?_)
        · have := congrArg Valued.v h0; rw [map_zero] at this; exact ϖ₁.pos.ne' this
        · have hwp : (w : K) ≠ (p : K) := fun h => hw (Set.mem_singleton_iff.2 (Subtype.ext h))
          exact hidA ⟨(w : K), hSA w.2⟩ hwp
        · have hwp : (w : K) ≠ (p : K) := fun h => hw (Set.mem_singleton_iff.2 (Subtype.ext h))
          exact hidB' ⟨(w : K), hSB w.2⟩ hwp

      have hbound : kN q' - jN q' ≤ ordAt ϖ₁ H pΩ := by
        by_cases hqZ : q' ∈ ZN
        · have h1 := hHord ⟨q', hqZ⟩ γ⁻¹
          have h2 : (ρ γ⁻¹ • (⟨((q' : ↥(affinoid ϖ₁ N)) : K), affinoid_subset_upperHalfPlane ϖ₁ N q'.2⟩ :
              ↥(upperHalfPlane K₀ K))) = pΩ := by
            rw [map_inv, inv_smul_eq_iff]
            exact Subtype.ext (by rw [coe_smul_upperHalfPlane])
          rw [h2] at h1
          exact le_trans (Nat.sub_le _ _) (le_trans (hkM q' hqZ) h1)
        · have : kN q' = 0 := by
            have h2 : ¬ (1 ≤ kN q') := fun h1 => hqZ ((hkN q').2 h1); omega
          rw [this, Nat.zero_sub]; exact Nat.zero_le _

      have : kn p ≤ (kn p - jf p) + jf p := by omega
      rw [heq] at this
      omega

    refine ⟨fun z => (∏ p ∈ Zn ∪ ZΘ, ((z : K) - (p : K)) ^ (kΘ p - kn p)) * uΘ z,
      mul_mem (polyFn_mem_holOn ϖ₁ n subset_rfl _ _ _) huΘ, fun z => ?_⟩
    have e1 : (∏ p ∈ ZΘ, ((z : K) - (p : K)) ^ kΘ p) = ∏ p ∈ Zn ∪ ZΘ, ((z : K) - (p : K)) ^ kΘ p :=
      Finset.prod_subset Finset.subset_union_right fun p _ hp => by rw [hkΘ0 p hp, pow_zero]
    have e2 : (∏ p ∈ Zn, ((z : K) - (p : K)) ^ kn p) = ∏ p ∈ Zn ∪ ZΘ, ((z : K) - (p : K)) ^ kn p :=
      Finset.prod_subset Finset.subset_union_left fun p _ hp => by rw [hkn0 p hp, pow_zero]
    have e3 : (∏ p ∈ Zn ∪ ZΘ, ((z : K) - (p : K)) ^ kΘ p) =
        (∏ p ∈ Zn ∪ ZΘ, ((z : K) - (p : K)) ^ kn p) * ∏ p ∈ Zn ∪ ZΘ, ((z : K) - (p : K)) ^ (kΘ p - kn p) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← pow_add, Nat.add_sub_cancel' (hkey p)]
    show Hn z * fn z = (∏ p ∈ Zn, ((z : K) - (p : K)) ^ kn p) *
      ((∏ p ∈ Zn ∪ ZΘ, ((z : K) - (p : K)) ^ (kΘ p - kn p)) * uΘ z)
    rw [show Hn z * fn z = (Hn * fn) z from rfl, hΘfac z, e1, e3, e2, mul_assoc]

  obtain ⟨Φ, hΦ⟩ := CerednikDrinfeld.Omega.exists_holRing_forall_finite_eq_of_forall_exists_mem_holOn_eq
    K₀ K ϖ₁ hrk hex (fun w : ↥(upperHalfPlane K₀ K) => (H : ↥(upperHalfPlane K₀ K) → K) w * F w) hnum
  exact ⟨Φ, H, hH0, hΦ⟩

end S_CerednikDrinfeld_Omega_exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant (solution)
