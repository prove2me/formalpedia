-- Prove2me | solution 1 for Deformation.exists_pDivisibleTower_ker_eq_map_bijective_baseChange_of_isLocalRing_cartierDual_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/11a88b19-df5b-5604-bfa9-ee65f559e4af

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_Deformation_exists_pDivisibleTower_ker_eq_map_bijective_map_comp_mem_fontaineKer_of_isLocalRing_cartierDual_zmodp
import Theorems.Thm_Deformation_exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_forall_ker_eq_torsionIdeal_zmodp
import Theorems.Thm_HopfAlgebra_algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_exists_pDivisibleTower_ker_eq_map_bijective_baseChange_of_isLocalRing_cartierDual_zmodp
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm Deformation.WittKernel.instModuleFinite Deformation.WittKernel.isHopfIdeal Deformation.HondaSystem.SplitCoordinates.instHopfGc Deformation.HondaSystem.SplitCoordinates.instCommRingGe Deformation.HondaSystem.SplitCoordinates.instCommRingGc Deformation.HondaSystem.SplitCoordinates.instCommRingEt Deformation.HondaSystem.SplitCoordinates.instHopfGe Deformation.HondaSystem.SplitCoordinates.instHopfEt MvFormalGroup.instIsCommAddMv MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring"
p2m_attr_erase "instance" "MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid Deformation.UnipotentWittCovector.instInhabited Deformation.UnipotentWittCovector.instAddCommGroup Deformation.TruncWitt.shiftLE_directedSystem instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one"
p2m_attr_erase "simp" "PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ Deformation.WittKernel.π_apply Deformation.WittKernel.coe_tauto Deformation.TruncWitt.coeff_frobeniusFun_iterate Deformation.WittKernel.coeff_tauto Deformation.HondaSystem.SplitCoordinates.mk.sizeOf_spec Deformation.HondaSystem.SplitCoordinates.mk.injEq MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast Deformation.UnipotentWittCovector.lift_of Deformation.UnipotentWittCovector.of_shift Deformation.UnipotentWittCovector.frobenius_of Deformation.DieudonneModule.toCovector_of Deformation.TruncWitt.frobeniusAddHom_apply Deformation.UnipotentWittCovector.dieudonneDatum_F_apply Deformation.UnipotentWittCovector.map_of Deformation.UnipotentWittCovector.verschiebung_of Deformation.UnipotentWittCovector.dieudonneDatum_V_apply Deformation.DieudonneModule.evalMonoidHom_apply Deformation.DieudonneModule.eval_of Deformation.UnipotentWittCovector.of_shiftLE Deformation.PLoc.map_algebraMap Deformation.PLoc.map_invPow Deformation.UnipotentWittCovector.wUp_of Deformation.UnipotentWittCovector.wHom_apply Deformation.UnipotentWittCovector.wLevel_succ_truncate Deformation.PLoc.mapLinear_apply"

set_option autoImplicit false

open scoped TensorProduct
open Function

universe u v w w'

namespace FontaineStep4Zmodp

section CompleteDVR

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ}
variable {k : Type v} [Field k] [Algebra 𝓞 k]

theorem isMaximal_span (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
    (Ideal.span {(p : 𝓞)}).IsMaximal :=
  hker ▸ RingHom.ker_isMaximal_of_surjective _ hk

theorem isLocalRing_of_isAdicComplete [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) : IsLocalRing 𝓞 :=
  haveI := isMaximal_span hk hker
  isLocalRing_of_isAdicComplete_maximal (Ideal.span {(p : 𝓞)})

theorem isUnit_of_not_mem_span [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) {x : 𝓞}
    (hx : x ∉ Ideal.span {(p : 𝓞)}) : IsUnit x := by
  haveI := isLocalRing_of_isAdicComplete hk hker
  have hmax : IsLocalRing.maximalIdeal 𝓞 = Ideal.span {(p : 𝓞)} :=
    (IsLocalRing.eq_maximalIdeal (isMaximal_span hk hker)).symm
  by_contra h
  exact hx (hmax ▸ (IsLocalRing.mem_maximalIdeal x).2 h)

theorem span_singleton_pow_eq (n : ℕ) :
    (Ideal.span {(p : 𝓞)}) ^ n • (⊤ : Submodule 𝓞 𝓞) = Ideal.span {(p : 𝓞) ^ n} := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]

theorem exists_eq_pow_mul_of_ne_zero [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) {x : 𝓞} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : 𝓞), IsUnit u ∧ x = (p : 𝓞) ^ n * u := by
  classical
  have hex : ∃ n : ℕ, x ∉ Ideal.span {(p : 𝓞) ^ n} := by
    by_contra h
    push Not at h
    apply hx
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : 𝓞)}) 𝓞) x fun n => ?_
    rw [SModEq.zero, span_singleton_pow_eq]
    exact h n
  let n₀ := Nat.find hex
  have hn₀ : x ∉ Ideal.span {(p : 𝓞) ^ n₀} := Nat.find_spec hex
  have hpos : n₀ ≠ 0 := by
    intro h0
    apply hn₀
    rw [h0, pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hxm : x ∈ Ideal.span {(p : 𝓞) ^ m} := by
    by_contra h
    have := Nat.find_min hex (m := m) (by rw [show Nat.find hex = n₀ from rfl, hm]; exact Nat.lt_succ_self m)
    exact this h
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hxm
  refine ⟨m, u, ?_, by rw [← hu, mul_comm]⟩
  refine isUnit_of_not_mem_span hk hker fun hu' => hn₀ ?_
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hu'
  rw [hm, ← hu, ← hc, Ideal.mem_span_singleton, pow_succ]
  exact ⟨c, by ring⟩

theorem isDomain_of_isAdicComplete [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) : IsDomain 𝓞 := by
  haveI := isLocalRing_of_isAdicComplete hk hker
  haveI : NoZeroDivisors 𝓞 := ⟨fun {a b} hab => by
    by_contra h
    push Not at h
    obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero hk hker h.1
    obtain ⟨n, v, hv, rfl⟩ := exists_eq_pow_mul_of_ne_zero hk hker h.2
    have h1 : u * v * (p : 𝓞) ^ (m + n) = 0 := by rw [← hab]; ring
    have h2 : u * v = 0 := mem_nonZeroDivisors_iff_right.1 (Submonoid.pow_mem _ hp (m + n)) _ h1
    exact (hu.mul hv).ne_zero h2⟩
  exact NoZeroDivisors.to_isDomain 𝓞

theorem irreducible_natCast [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) : Irreducible (p : 𝓞) := by
  haveI := isLocalRing_of_isAdicComplete hk hker
  have hmax : IsLocalRing.maximalIdeal 𝓞 = Ideal.span {(p : 𝓞)} :=
    (IsLocalRing.eq_maximalIdeal (isMaximal_span hk hker)).symm
  have hpmem : (p : 𝓞) ∈ IsLocalRing.maximalIdeal 𝓞 := hmax ▸ Ideal.mem_span_singleton_self _
  refine ⟨(IsLocalRing.mem_maximalIdeal _).1 hpmem, fun a b hab => ?_⟩
  by_contra h
  push Not at h
  have ha : a ∈ Ideal.span {(p : 𝓞)} := hmax ▸ (IsLocalRing.mem_maximalIdeal a).2 h.1
  have hb : b ∈ Ideal.span {(p : 𝓞)} := hmax ▸ (IsLocalRing.mem_maximalIdeal b).2 h.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hb
  have h1 : (1 - (p : 𝓞) * (c * d)) * (p : 𝓞) = 0 := by
    have : (p : 𝓞) = (p : 𝓞) * (p : 𝓞) * (c * d) := by
      conv_lhs => rw [hab, ← hc, ← hd]
      ring
    calc (1 - (p : 𝓞) * (c * d)) * (p : 𝓞) = (p : 𝓞) - (p : 𝓞) * (p : 𝓞) * (c * d) := by ring
      _ = 0 := by rw [← this, sub_self]
  have h2 : 1 - (p : 𝓞) * (c * d) = 0 := mem_nonZeroDivisors_iff_right.1 hp _ h1
  have hunit : IsUnit (p : 𝓞) := isUnit_iff_exists_inv.2 ⟨c * d, (sub_eq_zero.1 h2).symm⟩
  exact (IsLocalRing.mem_maximalIdeal _).1 hpmem hunit

theorem isDiscreteValuationRing_of_isAdicComplete [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
    @IsDiscreteValuationRing 𝓞 _ (isDomain_of_isAdicComplete hp hk hker) := by
  letI := isDomain_of_isAdicComplete hp hk hker
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨(p : 𝓞), irreducible_natCast hp hk hker, fun {x} hx => ?_⟩
  obtain ⟨n, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero hk hker hx
  exact ⟨n, (associated_mul_unit_right ((p : 𝓞) ^ n) u hu)⟩

end CompleteDVR

section Reduction

variable {𝓞 : Type u} [CommRing 𝓞] (k : Type v) [Field k] [Algebra 𝓞 k]
variable {X : Type w} [CommRing X] [Algebra 𝓞 X] {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y]

noncomputable def red (x : X →ₐ[𝓞] Y) : k ⊗[𝓞] X →ₐ[k] k ⊗[𝓞] Y :=
  Algebra.TensorProduct.map (AlgHom.id k k) x

variable {k}

@[scoped simp] theorem red_tmul (x : X →ₐ[𝓞] Y) (c : k) (r : X) : red k x (c ⊗ₜ[𝓞] r) = c ⊗ₜ[𝓞] x r := by
  rw [red, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem red_comp {Z : Type*} [CommRing Z] [Algebra 𝓞 Z] (x : X →ₐ[𝓞] Y) (y : Y →ₐ[𝓞] Z) :
    red k (y.comp x) = (red k y).comp (red k x) := by
  refine Algebra.TensorProduct.ext' fun c r => ?_
  simp [red_tmul]

theorem red_surjective {x : X →ₐ[𝓞] Y} (hx : Surjective x) : Surjective (red k x) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul c y =>
    obtain ⟨r, rfl⟩ := hx y
    exact ⟨c ⊗ₜ[𝓞] r, red_tmul x c r⟩
  | add a b ha hb =>
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    exact ⟨a' + b', map_add _ _ _⟩

theorem algHom_ext_base {T : Type*} [Semiring T] [Algebra k T] (F G : k ⊗[𝓞] 𝓞 →ₐ[k] T) : F = G := by
  refine AlgHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c o =>
    have : c ⊗ₜ[𝓞] o = algebraMap k (k ⊗[𝓞] 𝓞) (o • c) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        TensorProduct.smul_tmul, smul_eq_mul, mul_one]
    rw [this, AlgHom.commutes, AlgHom.commutes]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem sub_mem_span_of_red_eq (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    {x x' : X →ₐ[𝓞] Y} (h : red k x = red k x') (r : X) :
    x r - x' r ∈ Ideal.span {(p : Y)} := by
  rw [← Deformation.SpecialFibre.ker_reduction_eq_span (ℛ := Y) hk hker, RingHom.mem_ker,
    Deformation.SpecialFibre.reduction_apply, TensorProduct.tmul_sub, ← red_tmul, ← red_tmul, h, sub_self]

end Reduction

section LocalRigidity

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] {k : Type v} [Field k] [Algebra 𝓞 k]
variable {H : Type w} [CommRing H] [Algebra 𝓞 H] {ℛ : Type w'} [CommRing ℛ] [Algebra 𝓞 ℛ]

theorem ker_algebraMap_eq_maximalIdeal (hk : Surjective (algebraMap 𝓞 k)) :
    RingHom.ker (algebraMap 𝓞 k) = IsLocalRing.maximalIdeal 𝓞 :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hk)

noncomputable def residueFieldAlgEquiv (hk : Surjective (algebraMap 𝓞 k)) :
    IsLocalRing.ResidueField 𝓞 ≃ₐ[𝓞] k :=
  (Ideal.quotientEquivAlgOfEq 𝓞 (ker_algebraMap_eq_maximalIdeal hk).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId 𝓞 k) hk)

omit [IsLocalRing 𝓞] in

theorem red_apply_eq_lTensor (x : H →ₐ[𝓞] ℛ) (z : k ⊗[𝓞] H) :
    red k x z = (x.toLinearMap.lTensor k) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c r => rw [red_tmul, LinearMap.lTensor_tmul]; rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem surjective_of_red_surjective (hk : Surjective (algebraMap 𝓞 k)) [Module.Finite 𝓞 ℛ]
    (x : H →ₐ[𝓞] ℛ) (hx : Surjective (red k x)) : Surjective x := by

  set N : Submodule 𝓞 ℛ := LinearMap.range x.toLinearMap with hN
  have hle : (⊤ : Submodule 𝓞 ℛ) ≤ N ⊔ IsLocalRing.maximalIdeal 𝓞 • (⊤ : Submodule 𝓞 ℛ) := by
    intro r _
    obtain ⟨z, hz⟩ := hx ((1 : k) ⊗ₜ[𝓞] r)
    obtain ⟨h, rfl⟩ := Deformation.SpecialFibre.reduction_surjective (ℛ := H) (k := k) hk z
    rw [Deformation.SpecialFibre.reduction_apply, red_tmul] at hz
    have hmem : r - x h ∈ RingHom.ker (Deformation.SpecialFibre.reduction 𝓞 k ℛ) := by
      rw [RingHom.mem_ker, Deformation.SpecialFibre.reduction_apply, TensorProduct.tmul_sub, hz, sub_self]
    rw [Deformation.SpecialFibre.ker_reduction hk, ker_algebraMap_eq_maximalIdeal hk] at hmem
    have hmem' : r - x h ∈ IsLocalRing.maximalIdeal 𝓞 • (⊤ : Submodule 𝓞 ℛ) := by
      rw [Ideal.smul_top_eq_map]
      exact hmem
    have : r = x h + (r - x h) := by ring
    rw [this]
    exact Submodule.add_mem_sup ⟨h, rfl⟩ hmem'
  have hN' : (⊤ : Submodule 𝓞 ℛ) ≤ N :=
    Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle
  intro r
  obtain ⟨h, hh⟩ := hN' (Submodule.mem_top (x := r))
  exact ⟨h, hh⟩

theorem injective_of_red_injective (hk : Surjective (algebraMap 𝓞 k)) [Module.Finite 𝓞 H]
    [Module.Finite 𝓞 ℛ] [Module.Free 𝓞 ℛ]
    (x : H →ₐ[𝓞] ℛ) (hx : Injective (red k x)) : Injective x := by
  set l : H →ₗ[𝓞] ℛ := x.toLinearMap with hl

  let e : IsLocalRing.ResidueField 𝓞 ≃ₗ[𝓞] k := (residueFieldAlgEquiv hk).toLinearEquiv
  have hk' : Injective (l.lTensor k) := by
    intro a b hab
    apply hx
    rw [red_apply_eq_lTensor, red_apply_eq_lTensor]
    exact hab
  have hRF : Injective (l.lTensor (IsLocalRing.ResidueField 𝓞)) := by
    have hcomp : (e.toLinearMap.rTensor ℛ).comp (l.lTensor (IsLocalRing.ResidueField 𝓞)) =
        (l.lTensor k).comp (e.toLinearMap.rTensor H) := by
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    have hinj : Injective ((e.toLinearMap.rTensor ℛ).comp (l.lTensor (IsLocalRing.ResidueField 𝓞))) := by
      rw [hcomp, LinearMap.coe_comp]
      exact hk'.comp (e.rTensor H).injective
    rw [LinearMap.coe_comp] at hinj
    exact Injective.of_comp hinj
  obtain ⟨l', hl'⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective l).2 hRF
  intro a b hab
  have := LinearMap.congr_fun hl' a
  have h' := LinearMap.congr_fun hl' b
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this h'
  rw [← this, ← h']
  exact congrArg l' hab

theorem bijective_of_red_bijective (hk : Surjective (algebraMap 𝓞 k)) [Module.Finite 𝓞 H]
    [Module.Finite 𝓞 ℛ] [Module.Free 𝓞 ℛ]
    (x : H →ₐ[𝓞] ℛ) (hx : Bijective (red k x)) : Bijective x :=
  ⟨injective_of_red_injective hk x hx.1, surjective_of_red_surjective hk x hx.2⟩

end LocalRigidity

end FontaineStep4Zmodp
p2m_reactivate "P2MW.S_Deformation_exists_pDivisibleTower_ker_eq_map_bijective_baseChange_of_isLocalRing_cartierDual_zmodp.FontaineStep4Zmodp"

open FontaineStep4Zmodp in

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (ℛ : Type v) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] (hrank : ∃ a : ℕ, Module.finrank 𝓞 ℛ = p ^ a)
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) ℛ))) :
    ∃ (h : ℕ) (L : ℕ → Type u) (_ : ∀ v, CommRing (L v)) (_ : ∀ v, HopfAlgebra 𝓞 (L v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (L v)) (_ : ∀ v, Module.Free 𝓞 (L v))
      (_ : ∀ v, Module.Finite 𝓞 (L v)) (t : ∀ v, L (v + 1) →ₐc[𝓞] L v),
      (∀ v, Function.Surjective (t v)) ∧ (∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h)) ∧
      (∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v)) ∧
      (∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v)))) ∧
    ∃ (h' : ℕ) (L' : ℕ → Type u) (_ : ∀ v, CommRing (L' v)) (_ : ∀ v, HopfAlgebra 𝓞 (L' v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (L' v)) (_ : ∀ v, Module.Free 𝓞 (L' v))
      (_ : ∀ v, Module.Finite 𝓞 (L' v)) (t' : ∀ v, L' (v + 1) →ₐc[𝓞] L' v),
      (∀ v, Function.Surjective (t' v)) ∧ (∀ v, Module.finrank 𝓞 (L' v) = p ^ (v * h')) ∧
      (∀ v, RingHom.ker (t' v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L' (v + 1)) (p ^ v)) ∧
      (∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L' v)))) ∧
    ∃ (f : ∀ v, L' v →ₐc[𝓞] L v) (v : ℕ)
      (H : Type u) (_ : CommRing H) (_ : HopfAlgebra 𝓞 H) (_ : Coalgebra.IsCocomm 𝓞 H)
      (_ : Module.Free 𝓞 H) (_ : Module.Finite 𝓞 H) (q : L v →ₐc[𝓞] H)
      (ψ : TensorProduct 𝓞 (ZMod p) H →ₐc[ZMod p] TensorProduct 𝓞 (ZMod p) ℛ),
      (∀ u, (f u).comp (t' u) = (t u).comp (f (u + 1))) ∧
      Function.Surjective q ∧
      RingHom.ker (q : L v →ₐ[𝓞] H) =
        Ideal.map (f v : L' v →ₐ[𝓞] L v) (RingHom.ker (Bialgebra.counitAlgHom 𝓞 (L' v))) ∧
      Function.Bijective ψ ∧
      (∀ (n : ℕ) (m : Deformation.wittHom (ZMod p) p n (TensorProduct 𝓞 (ZMod p) H)),
        (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) H)) ∈
            Deformation.TruncWitt.fontaineKer p n
              (Algebra.TensorProduct.includeRight : H →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) H).toRingHom →
          Deformation.TruncWitt.map
              (ψ : TensorProduct 𝓞 (ZMod p) H →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom
              (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) H)) ∈
            Deformation.TruncWitt.fontaineKer p n
              (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom) := by

  have hk : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _

  obtain ⟨h, L, iL₁, iL₂, iL₃, iL₄, iL₅, t, ht, hrankL, hkerL, hunipL, h', L', iL'₁, iL'₂, iL'₃, iL'₄,
    iL'₅, t', ht', hrankL', hkerL', hunipL', f, v, H, iH₁, iH₂, iH₃, q, ψ, hf, hq, hexact, hψ, hχ⟩ :=
    Deformation.exists_pDivisibleTower_ker_eq_map_bijective_map_comp_mem_fontaineKer_of_isLocalRing_cartierDual_zmodp
      p hp hker ℛ hrank hunip

  haveI := isDomain_of_isAdicComplete hp hk hker
  haveI := isDiscreteValuationRing_of_isAdicComplete hp hk hker
  haveI : IsLocalRing 𝓞 := isLocalRing_of_isAdicComplete hk hker
  have hirr : Irreducible (p : 𝓞) := irreducible_natCast hp hk hker
  haveI iH₅ : Module.Finite 𝓞 H := Module.Finite.of_surjective (q : L v →ₐ[𝓞] H).toLinearMap hq

  set χ : TensorProduct 𝓞 (ZMod p) (L v) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) ℛ :=
    (ψ : TensorProduct 𝓞 (ZMod p) H →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) ℛ).comp
      (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (q : L v →ₐ[𝓞] H)) with hχdef
  obtain ⟨x₀, hx₀⟩ :=
    Deformation.exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_forall_ker_eq_torsionIdeal_zmodp
      p hp hker h L t ht hrankL hkerL hunipL v ℛ χ hχ
  have hx₀' : red (ZMod p) x₀ = (ψ : TensorProduct 𝓞 (ZMod p) H →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) ℛ).comp
      (red (ZMod p) (q : L v →ₐ[𝓞] H)) := hx₀

  have hqf : ∀ b : L' v, q (f v b) = algebraMap 𝓞 H (Coalgebra.counit (R := 𝓞) b) := by
    intro b
    have hb : b - algebraMap 𝓞 (L' v) (Coalgebra.counit (R := 𝓞) b) ∈
        RingHom.ker (Bialgebra.counitAlgHom 𝓞 (L' v)) := by
      rw [RingHom.mem_ker, map_sub, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
        Bialgebra.counit_algebraMap, sub_self]
    have hmem : (f v : L' v →ₐ[𝓞] L v) (b - algebraMap 𝓞 (L' v) (Coalgebra.counit (R := 𝓞) b)) ∈
        RingHom.ker (q : L v →ₐ[𝓞] H) := by
      rw [hexact]; exact Ideal.mem_map_of_mem _ hb
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, map_sub, AlgHom.commutes, sub_eq_zero] at hmem
    exact hmem

  have hred_eq : red (ZMod p) (x₀.comp (f v : L' v →ₐ[𝓞] L v)) =
      red (ZMod p) ((Algebra.ofId 𝓞 ℛ).comp (Bialgebra.counitAlgHom 𝓞 (L' v))) := by
    have hqf' : (q : L v →ₐ[𝓞] H).comp (f v : L' v →ₐ[𝓞] L v) =
        (Algebra.ofId 𝓞 H).comp (Bialgebra.counitAlgHom 𝓞 (L' v)) := AlgHom.ext hqf
    rw [red_comp, hx₀', AlgHom.comp_assoc, ← red_comp, hqf', red_comp, red_comp, ← AlgHom.comp_assoc]
    congr 1
    exact algHom_ext_base _ _
  have hyy : x₀.comp (f v : L' v →ₐ[𝓞] L v) =
      (Algebra.ofId 𝓞 ℛ).comp (Bialgebra.counitAlgHom 𝓞 (L' v)) :=
    HopfAlgebra.algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual 𝓞 p hirr (ZMod p) hk hker
      (L' v) ⟨v * h', hrankL' v⟩ (hunipL' v) ℛ _ _ (sub_mem_span_of_red_eq hk hker hred_eq)

  have hle : RingHom.ker (q : L v →ₐ[𝓞] H).toRingHom ≤ RingHom.ker x₀.toRingHom := by
    change RingHom.ker (q : L v →ₐ[𝓞] H) ≤ RingHom.ker x₀
    rw [hexact, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := AlgHom.congr_fun hyy b
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Algebra.ofId_apply, Bialgebra.counitAlgHom_apply] at this
    change x₀ ((f v : L' v →ₐ[𝓞] L v) b) = 0
    rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hb
    rw [this, hb, map_zero]
  let x : H →ₐ[𝓞] ℛ := AlgHom.liftOfSurjective (q : L v →ₐ[𝓞] H) hq x₀ hle
  have hxq : x.comp (q : L v →ₐ[𝓞] H) = x₀ := AlgHom.liftOfSurjective_comp _ _ _ _
  have hx : red (ZMod p) x = (ψ : TensorProduct 𝓞 (ZMod p) H →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) ℛ) := by
    have hcomp : (red (ZMod p) x).comp (red (ZMod p) (q : L v →ₐ[𝓞] H)) =
        (ψ : TensorProduct 𝓞 (ZMod p) H →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) ℛ).comp
          (red (ZMod p) (q : L v →ₐ[𝓞] H)) := by
      rw [← red_comp, hxq, hx₀']
    refine AlgHom.ext fun z => ?_
    obtain ⟨w, rfl⟩ := red_surjective (k := ZMod p) (x := (q : L v →ₐ[𝓞] H)) hq z
    exact AlgHom.congr_fun hcomp w

  have hred : Function.Bijective (red (ZMod p) x) := by
    have : (red (ZMod p) x : TensorProduct 𝓞 (ZMod p) H → TensorProduct 𝓞 (ZMod p) ℛ) = ψ := by
      rw [hx]; rfl
    rw [this]; exact hψ
  have hxb : Function.Bijective x := bijective_of_red_bijective hk x hred
  haveI iH₄ : Module.Free 𝓞 H :=
    Module.Free.of_equiv (LinearEquiv.ofBijective x.toLinearMap hxb).symm

  have hψL : ∀ (n : ℕ) (m : Deformation.wittHom (ZMod p) p n (TensorProduct 𝓞 (ZMod p) H)),
      (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) H)) ∈ Deformation.TruncWitt.fontaineKer p n
          (Algebra.TensorProduct.includeRight : H →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) H).toRingHom →
        Deformation.TruncWitt.map
            (ψ : TensorProduct 𝓞 (ZMod p) H →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom
            (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) H)) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom := by
    intro n m hm
    have hcomm : (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom.comp
        x.toRingHom =
        (ψ : TensorProduct 𝓞 (ZMod p) H →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom.comp
          (Algebra.TensorProduct.includeRight : H →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) H).toRingHom := by
      refine RingHom.ext fun z => ?_
      change (1 : ZMod p) ⊗ₜ[𝓞] x z =
        (ψ : TensorProduct 𝓞 (ZMod p) H →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) ℛ) ((1 : ZMod p) ⊗ₜ[𝓞] z)
      rw [← hx, red_tmul]
    exact Deformation.TruncWitt.map_mem_fontaineKer x.toRingHom
      (ψ : TensorProduct 𝓞 (ZMod p) H →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom _ hcomm hm
  exact ⟨h, L, iL₁, iL₂, iL₃, iL₄, iL₅, t, ht, hrankL, hkerL, hunipL, h', L', iL'₁, iL'₂, iL'₃, iL'₄, iL'₅,
    t', ht', hrankL', hkerL', hunipL', f, v, H, iH₁, iH₂, iH₃, iH₄, iH₅, q, ψ, hf, hq, hexact, hψ, hψL⟩

end S_Deformation_exists_pDivisibleTower_ker_eq_map_bijective_baseChange_of_isLocalRing_cartierDual_zmodp
end P2MW
export P2MW.S_Deformation_exists_pDivisibleTower_ker_eq_map_bijective_baseChange_of_isLocalRing_cartierDual_zmodp (solution)
