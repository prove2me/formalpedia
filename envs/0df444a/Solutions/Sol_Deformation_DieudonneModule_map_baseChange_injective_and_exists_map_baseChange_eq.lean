-- Prove2me | solution 1 for Deformation.DieudonneModule.map_baseChange_injective_and_exists_map_baseChange_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/499eebef-5e1d-590e-9bdf-f9c6f8b9cac0

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_HopfAlgebra_algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_zmodp
import Theorems.Thm_Deformation_DieudonneModule_map_injective_and_exists_map_eq_of_isLocalRing_cartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_map_baseChange_injective_and_exists_map_baseChange_eq
p2m_attr_erase "instance" "PDivisibleGroup.instHopfAlgebra PDivisibleGroup.instModuleFinite PDivisibleGroup.instCommRing PDivisibleGroup.instIsCocomm PDivisibleGroup.instModuleFree PDivisibleGroup.instModuleFlat MvFormalGroup.instIsCommAddMv MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing"
p2m_attr_erase "instance" "Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm Deformation.WittKernel.instModuleFinite Deformation.WittKernel.isHopfIdeal Deformation.HondaSystem.SplitCoordinates.instHopfGc Deformation.HondaSystem.SplitCoordinates.instCommRingGe Deformation.HondaSystem.SplitCoordinates.instCommRingGc Deformation.HondaSystem.SplitCoordinates.instCommRingEt Deformation.HondaSystem.SplitCoordinates.instHopfGe Deformation.HondaSystem.SplitCoordinates.instHopfEt Deformation.UnipotentWittCovector.instInhabited Deformation.UnipotentWittCovector.instAddCommGroup Deformation.TruncWitt.shiftLE_directedSystem instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "PDivisibleGroup.counit_transition PDivisibleGroup.Hopf.nsmulAlgHom_one PDivisibleGroup.Hopf.torsionIdeal_zero PDivisibleGroup.Hopf.nsmulAlgHom_zero_apply PDivisibleGroup.Hopf.torsionIdeal_one PDivisibleGroup.Hopf.counit_nsmulAlgHom PDivisibleGroup.mk.sizeOf_spec PDivisibleGroup.mk.injEq PDivisibleGroup.height_eq MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast ModpDieudonneRealization.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.injEq HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero"
p2m_attr_erase "simp" "PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ Deformation.WittKernel.π_apply Deformation.WittKernel.coe_tauto Deformation.TruncWitt.coeff_frobeniusFun_iterate Deformation.WittKernel.coeff_tauto Deformation.HondaSystem.SplitCoordinates.mk.sizeOf_spec Deformation.HondaSystem.SplitCoordinates.mk.injEq Deformation.UnipotentWittCovector.lift_of Deformation.UnipotentWittCovector.of_shift Deformation.UnipotentWittCovector.frobenius_of Deformation.DieudonneModule.toCovector_of Deformation.TruncWitt.frobeniusAddHom_apply Deformation.UnipotentWittCovector.dieudonneDatum_F_apply Deformation.UnipotentWittCovector.map_of Deformation.UnipotentWittCovector.verschiebung_of Deformation.UnipotentWittCovector.dieudonneDatum_V_apply Deformation.DieudonneModule.evalMonoidHom_apply Deformation.DieudonneModule.eval_of Deformation.UnipotentWittCovector.of_shiftLE Deformation.PLoc.map_algebraMap Deformation.PLoc.map_invPow Deformation.UnipotentWittCovector.wUp_of Deformation.UnipotentWittCovector.wHom_apply Deformation.UnipotentWittCovector.wLevel_succ_truncate"
p2m_attr_erase "simp" "Deformation.PLoc.mapLinear_apply"

set_option autoImplicit false

open scoped TensorProduct
open Function

universe u v w w'

namespace FontaineFF

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

theorem sub_mem_span_of_red_eq (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    {x x' : X →ₐ[𝓞] Y} (h : red k x = red k x') (r : X) :
    x r - x' r ∈ Ideal.span {(p : Y)} := by
  rw [← Deformation.SpecialFibre.ker_reduction_eq_span (ℛ := Y) hk hker, RingHom.mem_ker,
    Deformation.SpecialFibre.reduction_apply, TensorProduct.tmul_sub, ← red_tmul, ← red_tmul, h, sub_self]

theorem red_eq_of_forall_sub_mem_span (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    {x x' : X →ₐ[𝓞] Y} (h : ∀ r : X, x r - x' r ∈ Ideal.span {(p : Y)}) :
    red k x = red k x' := by
  refine Algebra.TensorProduct.ext' fun c r => ?_
  rw [red_tmul, red_tmul]
  have h1 : (1 : k) ⊗ₜ[𝓞] (x r - x' r) = 0 := by
    have := h r
    rw [← Deformation.SpecialFibre.ker_reduction_eq_span (ℛ := Y) hk hker, RingHom.mem_ker] at this
    exact this
  rw [TensorProduct.tmul_sub, sub_eq_zero] at h1
  calc c ⊗ₜ[𝓞] x r = c • ((1 : k) ⊗ₜ[𝓞] x r) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = c • ((1 : k) ⊗ₜ[𝓞] x' r) := by rw [h1]
    _ = c ⊗ₜ[𝓞] x' r := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end Reduction

section TwoVariables

variable {𝓞 : Type u} [CommRing 𝓞] (k : Type v) [Field k] [Algebra 𝓞 k]
variable (ℛ : Type w) [CommRing ℛ] [Algebra 𝓞 ℛ]

noncomputable def redLeft : ℛ →ₐ[𝓞] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ) :=
  (Algebra.TensorProduct.includeLeft (S := 𝓞)).comp Algebra.TensorProduct.includeRight

noncomputable def redRight : ℛ →ₐ[𝓞] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ) :=
  ((Algebra.TensorProduct.includeRight :
        k ⊗[𝓞] ℛ →ₐ[k] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ)).restrictScalars 𝓞).comp
      Algebra.TensorProduct.includeRight

noncomputable def pi2 : ℛ ⊗[𝓞] ℛ →ₐ[𝓞] (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ) :=
  Algebra.TensorProduct.lift (redLeft k ℛ) (redRight k ℛ)
    (fun _ _ => Commute.all (S := (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ)) _ _)

noncomputable def theta : (k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ) →ₐ[k] k ⊗[𝓞] (ℛ ⊗[𝓞] ℛ) :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.map (AlgHom.id k k)
      (Algebra.TensorProduct.includeLeft : ℛ →ₐ[𝓞] ℛ ⊗[𝓞] ℛ))
    ((Algebra.TensorProduct.map (AlgHom.id k k)
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] ℛ ⊗[𝓞] ℛ)).restrictScalars k)
    (fun _ _ => Commute.all (S := k ⊗[𝓞] (ℛ ⊗[𝓞] ℛ)) _ _)

variable {k ℛ}

theorem pi2_tmul (r s : ℛ) :
    pi2 k ℛ (r ⊗ₜ[𝓞] s) = ((1 : k) ⊗ₜ[𝓞] r) ⊗ₜ[k] ((1 : k) ⊗ₜ[𝓞] s) := by
  rw [pi2, Algebra.TensorProduct.lift_tmul]
  change (((1 : k) ⊗ₜ[𝓞] r) ⊗ₜ[k] (1 : k ⊗[𝓞] ℛ)) * ((1 : k ⊗[𝓞] ℛ) ⊗ₜ[k] ((1 : k) ⊗ₜ[𝓞] s)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem theta_pi2 (z : ℛ ⊗[𝓞] ℛ) : theta k ℛ (pi2 k ℛ z) = (1 : k) ⊗ₜ[𝓞] z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, TensorProduct.tmul_zero]
  | tmul r s =>
    rw [pi2_tmul, theta, Algebra.TensorProduct.lift_tmul]
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, TensorProduct.tmul_add]

theorem ker_pi2 (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
    RingHom.ker (pi2 (𝓞 := 𝓞) k ℛ).toRingHom = Ideal.span {(p : ℛ ⊗[𝓞] ℛ)} := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    have h1 : (1 : k) ⊗ₜ[𝓞] z = 0 := by
      rw [← theta_pi2 z]
      change theta k ℛ ((pi2 k ℛ).toRingHom z) = 0
      rw [hz, map_zero]
    have : z ∈ RingHom.ker (Deformation.SpecialFibre.reduction 𝓞 k (ℛ ⊗[𝓞] ℛ)) := by
      rw [RingHom.mem_ker, Deformation.SpecialFibre.reduction_apply, h1]
    rwa [Deformation.SpecialFibre.ker_reduction_eq_span hk hker] at this
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast]
    have h := Deformation.SpecialFibre.natCast_eq_zero (ℛ := ℛ) hk hker
    rw [← map_natCast (algebraMap (k ⊗[𝓞] ℛ) ((k ⊗[𝓞] ℛ) ⊗[k] (k ⊗[𝓞] ℛ))), h, map_zero]

theorem sub_mem_span_of_pi2_eq (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) {a b : ℛ ⊗[𝓞] ℛ}
    (h : pi2 k ℛ a = pi2 k ℛ b) : a - b ∈ Ideal.span {(p : ℛ ⊗[𝓞] ℛ)} := by
  rw [← ker_pi2 hk hker, RingHom.mem_ker, map_sub]
  change pi2 k ℛ a - pi2 k ℛ b = 0
  rw [h, sub_self]

theorem natCast_mem_nonZeroDivisors [Module.Flat 𝓞 ℛ] {p : ℕ}
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) : (p : ℛ) ∈ nonZeroDivisors ℛ := by
  have hreg : IsSMulRegular ℛ (p : 𝓞) := Module.Flat.isSMulRegular_of_nonZeroDivisors hp
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => hreg ?_
  change (p : 𝓞) • x = (p : 𝓞) • (0 : ℛ)
  rw [smul_zero, Algebra.smul_def, map_natCast, mul_comm, hx]

end TwoVariables

section Comul

variable {𝓞 : Type u} [CommRing 𝓞] {k : Type v} [Field k] [Algebra 𝓞 k]
variable {ℛ : Type w} [CommRing ℛ] [Bialgebra 𝓞 ℛ]

theorem comul_one_tmul (r : ℛ) :
    Coalgebra.comul (R := k) ((1 : k) ⊗ₜ[𝓞] r) = pi2 k ℛ (Coalgebra.comul (R := 𝓞) r) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply k 1]
  induction Coalgebra.comul (R := 𝓞) r using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero]
  | tmul x y =>
    rw [pi2_tmul]
    rfl
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]

theorem counit_one_tmul (r : ℛ) :
    Coalgebra.counit (R := k) ((1 : k) ⊗ₜ[𝓞] r) = algebraMap 𝓞 k (Coalgebra.counit (R := 𝓞) r) := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.algebraMap_eq_smul_one]

end Comul

section Lift

variable {𝓞 : Type u} [CommRing 𝓞] {k : Type v} [Field k] [Algebra 𝓞 k]
variable {ℛ : Type w} [CommRing ℛ] [Bialgebra 𝓞 ℛ]
variable {ℛ' : Type w'} [CommRing ℛ'] [Bialgebra 𝓞 ℛ']

theorem baseChange_toAlgHom_eq_red (f : ℛ' →ₐc[𝓞] ℛ) :
    (Bialgebra.TensorProduct.map (BialgHom.id k k) f : k ⊗[𝓞] ℛ' →ₐ[k] k ⊗[𝓞] ℛ) =
      red k (f : ℛ' →ₐ[𝓞] ℛ) := by
  refine Algebra.TensorProduct.ext' fun c r => ?_
  rw [red_tmul]
  rfl

theorem eq_red_of_apply_one_tmul (g : k ⊗[𝓞] ℛ' →ₐ[k] k ⊗[𝓞] ℛ) (f₀ : ℛ' →ₐ[𝓞] ℛ)
    (hg : ∀ r : ℛ', g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r) : g = red k f₀ := by
  refine Algebra.TensorProduct.ext' fun c r => ?_
  rw [red_tmul]
  calc g (c ⊗ₜ[𝓞] r) = g (c • ((1 : k) ⊗ₜ[𝓞] r)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    _ = c • ((1 : k) ⊗ₜ[𝓞] f₀ r) := by rw [map_smul, hg]
    _ = c ⊗ₜ[𝓞] f₀ r := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem apply_one_tmul_of_red_eq {g : k ⊗[𝓞] ℛ' →ₐ[k] k ⊗[𝓞] ℛ} {f₀ : ℛ' →ₐ[𝓞] ℛ}
    (h : red k f₀ = g) (r : ℛ') : g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r := by
  rw [← h, red_tmul]

theorem pi2_map_map (g : k ⊗[𝓞] ℛ' →ₐ[k] k ⊗[𝓞] ℛ) (f₀ : ℛ' →ₐ[𝓞] ℛ)
    (hg : ∀ r : ℛ', g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r) (w : ℛ' ⊗[𝓞] ℛ') :
    pi2 k ℛ (Algebra.TensorProduct.map f₀ f₀ w) =
      TensorProduct.map g.toLinearMap g.toLinearMap (pi2 k ℛ' w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, pi2_tmul, pi2_tmul, TensorProduct.map_tmul,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, hg, hg]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem counitAlgHom_comp_eq {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (hinj : ∀ x x' : ℛ' →ₐ[𝓞] 𝓞, (∀ r, x r - x' r ∈ Ideal.span {(p : 𝓞)}) → x = x')
    (g : k ⊗[𝓞] ℛ' →ₐc[k] k ⊗[𝓞] ℛ) (f₀ : ℛ' →ₐ[𝓞] ℛ)
    (hg : ∀ r : ℛ', g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r) :
    (Bialgebra.counitAlgHom 𝓞 ℛ).comp f₀ = Bialgebra.counitAlgHom 𝓞 ℛ' := by
  refine hinj _ _ fun r => ?_
  rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
  change algebraMap 𝓞 k (Coalgebra.counit (R := 𝓞) (f₀ r)) =
    algebraMap 𝓞 k (Coalgebra.counit (R := 𝓞) r)
  rw [← counit_one_tmul (k := k), ← counit_one_tmul (k := k), ← hg,
    CoalgHomClass.counit_comp_apply]

theorem map_comp_comulAlgHom_eq (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (hinj : ∀ x x' : ℛ' →ₐ[𝓞] ℛ ⊗[𝓞] ℛ,
      (∀ r, x r - x' r ∈ Ideal.span {(p : ℛ ⊗[𝓞] ℛ)}) → x = x')
    (g : k ⊗[𝓞] ℛ' →ₐc[k] k ⊗[𝓞] ℛ) (f₀ : ℛ' →ₐ[𝓞] ℛ)
    (hg : ∀ r : ℛ', g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r) :
    (Algebra.TensorProduct.map f₀ f₀).comp (Bialgebra.comulAlgHom 𝓞 ℛ') =
      (Bialgebra.comulAlgHom 𝓞 ℛ).comp f₀ := by
  refine hinj _ _ fun r => sub_mem_span_of_pi2_eq (k := k) hk hker ?_
  change pi2 k ℛ (Algebra.TensorProduct.map f₀ f₀ (Coalgebra.comul (R := 𝓞) r)) =
    pi2 k ℛ (Coalgebra.comul (R := 𝓞) (f₀ r))
  rw [pi2_map_map (g : k ⊗[𝓞] ℛ' →ₐ[k] k ⊗[𝓞] ℛ) f₀ hg, ← comul_one_tmul, ← comul_one_tmul, ← hg]
  exact (CoalgHomClass.map_comp_comul_apply g _)

noncomputable def bialgHomOfLift (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (hinj₁ : ∀ x x' : ℛ' →ₐ[𝓞] 𝓞, (∀ r, x r - x' r ∈ Ideal.span {(p : 𝓞)}) → x = x')
    (hinj₂ : ∀ x x' : ℛ' →ₐ[𝓞] ℛ ⊗[𝓞] ℛ,
      (∀ r, x r - x' r ∈ Ideal.span {(p : ℛ ⊗[𝓞] ℛ)}) → x = x')
    (g : k ⊗[𝓞] ℛ' →ₐc[k] k ⊗[𝓞] ℛ) (f₀ : ℛ' →ₐ[𝓞] ℛ)
    (hg : ∀ r : ℛ', g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r) : ℛ' →ₐc[𝓞] ℛ :=
  BialgHom.ofAlgHom f₀ (counitAlgHom_comp_eq hker hinj₁ g f₀ hg)
    (map_comp_comulAlgHom_eq hk hker hinj₂ g f₀ hg)

theorem bialgHomOfLift_toAlgHom (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (hinj₁ : ∀ x x' : ℛ' →ₐ[𝓞] 𝓞, (∀ r, x r - x' r ∈ Ideal.span {(p : 𝓞)}) → x = x')
    (hinj₂ : ∀ x x' : ℛ' →ₐ[𝓞] ℛ ⊗[𝓞] ℛ,
      (∀ r, x r - x' r ∈ Ideal.span {(p : ℛ ⊗[𝓞] ℛ)}) → x = x')
    (g : k ⊗[𝓞] ℛ' →ₐc[k] k ⊗[𝓞] ℛ) (f₀ : ℛ' →ₐ[𝓞] ℛ)
    (hg : ∀ r : ℛ', g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r) :
    (bialgHomOfLift hk hker hinj₁ hinj₂ g f₀ hg : ℛ' →ₐ[𝓞] ℛ) = f₀ :=
  AlgHom.ext fun _ => rfl

theorem baseChange_bialgHomOfLift (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (hinj₁ : ∀ x x' : ℛ' →ₐ[𝓞] 𝓞, (∀ r, x r - x' r ∈ Ideal.span {(p : 𝓞)}) → x = x')
    (hinj₂ : ∀ x x' : ℛ' →ₐ[𝓞] ℛ ⊗[𝓞] ℛ,
      (∀ r, x r - x' r ∈ Ideal.span {(p : ℛ ⊗[𝓞] ℛ)}) → x = x')
    (g : k ⊗[𝓞] ℛ' →ₐc[k] k ⊗[𝓞] ℛ) (f₀ : ℛ' →ₐ[𝓞] ℛ)
    (hg : ∀ r : ℛ', g ((1 : k) ⊗ₜ[𝓞] r) = (1 : k) ⊗ₜ[𝓞] f₀ r) :
    Bialgebra.TensorProduct.map (BialgHom.id k k) (bialgHomOfLift hk hker hinj₁ hinj₂ g f₀ hg) = g := by
  apply BialgHom.coe_algHom_injective
  rw [baseChange_toAlgHom_eq_red, bialgHomOfLift_toAlgHom]
  exact (eq_red_of_apply_one_tmul (g : k ⊗[𝓞] ℛ' →ₐ[k] k ⊗[𝓞] ℛ) f₀ hg).symm

end Lift

section Assembly

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [Fact p.Prime] [Algebra 𝓞 (ZMod p)]

theorem surjective_algebraMap_zmod : Surjective (algebraMap 𝓞 (ZMod p)) :=
  ZMod.ringHom_surjective _

theorem eq_of_forall_sub_mem_span [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (ℛ' : Type w') [CommRing ℛ'] [HopfAlgebra 𝓞 ℛ'] [Coalgebra.IsCocomm 𝓞 ℛ']
    [Module.Free 𝓞 ℛ'] [Module.Finite 𝓞 ℛ'] (hrank' : ∃ a : ℕ, Module.finrank 𝓞 ℛ' = p ^ a)
    (hunip' : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) ℛ')))
    (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
    (x x' : ℛ' →ₐ[𝓞] Y) (h : ∀ r : ℛ', x r - x' r ∈ Ideal.span {(p : Y)}) : x = x' := by
  have hk : Surjective (algebraMap 𝓞 (ZMod p)) := surjective_algebraMap_zmod
  haveI := isDomain_of_isAdicComplete hp hk hker
  haveI := isDiscreteValuationRing_of_isAdicComplete hp hk hker
  exact HopfAlgebra.algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual 𝓞 p
    (irreducible_natCast hp hk hker) (ZMod p) hk hker ℛ' hrank' hunip' Y x x' h

end Assembly

end FontaineFF
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_map_baseChange_injective_and_exists_map_baseChange_eq.FontaineFF"

open FontaineFF in
set_option maxHeartbeats 1600000 in

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (ℛ : Type v) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ]
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) ℛ)))
    (ℛ' : Type w) [CommRing ℛ'] [HopfAlgebra 𝓞 ℛ'] [Coalgebra.IsCocomm 𝓞 ℛ']
    [Module.Free 𝓞 ℛ'] [Module.Finite 𝓞 ℛ'] (hrank' : ∃ a : ℕ, Module.finrank 𝓞 ℛ' = p ^ a)
    (hunip' : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) ℛ'))) :
    (∀ f g : ℛ' →ₐc[𝓞] ℛ,
        Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) f) =
          Deformation.DieudonneModule.map (ZMod p) p
            (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) g) →
        f = g) ∧
    (∀ φ : Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ') →+
        Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ),
      (∀ z, φ (Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ') z) =
          Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ) (φ z)) →
      (∀ z, φ (Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ') z) =
          Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ) (φ z)) →
      (∀ z ∈ Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight : ℛ' →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ').toRingHom,
        φ z ∈ Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom) →
      ∃ f : ℛ' →ₐc[𝓞] ℛ,
        Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) f) = φ) := by
  have hk : Surjective (algebraMap 𝓞 (ZMod p)) := surjective_algebraMap_zmod
  have hD := Deformation.DieudonneModule.map_injective_and_exists_map_eq_of_isLocalRing_cartierDual p (TensorProduct 𝓞 (ZMod p) ℛ) (TensorProduct 𝓞 (ZMod p) ℛ') hunip hunip'
  refine ⟨fun f g hfg => ?_, fun φ hF hV hL => ?_⟩
  ·
    have h1 := hD.1 _ _ hfg
    have h2 : red (ZMod p) (f : ℛ' →ₐ[𝓞] ℛ) = red (ZMod p) (g : ℛ' →ₐ[𝓞] ℛ) := by
      rw [← baseChange_toAlgHom_eq_red, ← baseChange_toAlgHom_eq_red, h1]
    apply BialgHom.coe_algHom_injective
    exact eq_of_forall_sub_mem_span hp hker ℛ' hrank' hunip' ℛ _ _
      (sub_mem_span_of_red_eq hk hker h2)
  ·
    have hD2 := hD.2
    clear hD
    obtain ⟨g, hg⟩ := hD2 φ hF hV
    have hpℛ : (p : ℛ) ∈ nonZeroDivisors ℛ := natCast_mem_nonZeroDivisors hp
    have hπle : RingHom.ker (Deformation.SpecialFibre.reduction 𝓞 (ZMod p) ℛ) ≤
        Ideal.span {(p : ℛ)} := (Deformation.SpecialFibre.ker_reduction_eq_span hk hker).le
    have hπs := Deformation.SpecialFibre.reduction_surjective (ℛ := ℛ) (k := ZMod p) hk
    have hχ : ∀ (n : ℕ) (m : Deformation.wittHom (ZMod p) p n (TensorProduct 𝓞 (ZMod p) ℛ')),
        (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) ℛ')) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : ℛ' →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ').toRingHom →
        Deformation.TruncWitt.map (g : TensorProduct 𝓞 (ZMod p) ℛ' →ₐ[ZMod p]
            TensorProduct 𝓞 (ZMod p) ℛ).toRingHom
            (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) ℛ')) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom := by
      intro n m hm
      have h1 := hL _ (Deformation.of_mem_fontaineHodge (R := ZMod p) hm)
      rw [← hg, Deformation.DieudonneModule.map_of] at h1
      exact (Deformation.of_mem_fontaineHodge_iff (R := ZMod p) hpℛ hπle hπs _).1 h1
    obtain ⟨f₀, hf₀⟩ := Deformation.exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_zmodp p hp hker ℛ' hrank' hunip' ℛ
      (g : TensorProduct 𝓞 (ZMod p) ℛ' →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) ℛ) hχ
    have hg1 : ∀ r : ℛ', g ((1 : ZMod p) ⊗ₜ[𝓞] r) = (1 : ZMod p) ⊗ₜ[𝓞] f₀ r :=
      apply_one_tmul_of_red_eq hf₀
    refine ⟨bialgHomOfLift hk hker (eq_of_forall_sub_mem_span hp hker ℛ' hrank' hunip' 𝓞)
      (eq_of_forall_sub_mem_span hp hker ℛ' hrank' hunip' (ℛ ⊗[𝓞] ℛ)) g f₀ hg1, ?_⟩
    rw [baseChange_bialgHomOfLift, hg]

end S_Deformation_DieudonneModule_map_baseChange_injective_and_exists_map_baseChange_eq
end P2MW
export P2MW.S_Deformation_DieudonneModule_map_baseChange_injective_and_exists_map_baseChange_eq (solution)
