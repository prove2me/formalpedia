-- Prove2me | solution 1 for Deformation.HondaSystem.exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8de59581-61a2-5df7-9d1c-16d566f20863

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_Deformation_DieudonneModule_bijective_prod_map_of_bijective_tensorProduct_comul
import Theorems.Thm_Deformation_DieudonneModule_exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_DieudonneModule_frobenius_bijective_of_isReduced
import Theorems.Thm_HopfAlgebra_isLocalRing_cartierDual_of_surjective
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq
p2m_attr_erase "instance" "Deformation.UnipotentWittCovector.instInhabited Deformation.UnipotentWittCovector.instAddCommGroup Deformation.TruncWitt.shiftLE_directedSystem Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "Deformation.UnipotentWittCovector.lift_of Deformation.UnipotentWittCovector.of_shift Deformation.UnipotentWittCovector.frobenius_of Deformation.DieudonneModule.toCovector_of Deformation.TruncWitt.frobeniusAddHom_apply Deformation.UnipotentWittCovector.dieudonneDatum_F_apply Deformation.UnipotentWittCovector.map_of Deformation.UnipotentWittCovector.verschiebung_of Deformation.UnipotentWittCovector.dieudonneDatum_V_apply Deformation.DieudonneModule.evalMonoidHom_apply Deformation.DieudonneModule.eval_of Deformation.UnipotentWittCovector.of_shiftLE Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul"
p2m_attr_erase "simp" "HopfAlgebra.canMap_tmul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct
open MvPowerSeries

universe u v w

namespace Deformation
p2m_export "Deformation" "HondaSystem TruncWitt.coeff_verschiebung_succ wittHom counit_coeff_of_mem_wittHom wittHomVerschiebung coe_wittHomVerschiebung wittHomVerschiebung_iterate_eq_zero DieudonneModule DieudonneModule.of DieudonneModule.exists_of DieudonneModule.verschiebung DieudonneModule.verschiebung_of DieudonneModule.frobenius DieudonneModule.map DieudonneModule.map_verschiebung DieudonneModule.map_frobenius DieudonneModule.exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual DieudonneModule.frobenius_bijective_of_isReduced"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk sh1_le sh2' L mk.inj"
namespace LamAux
p2m_open "Deformation.HondaSystem Deformation"

theorem algHom_apply_eq_constantCoeff {K : Type*} [Field K] {σ : Type*}
    (φ : MvPowerSeries σ K →ₐ[K] K) (G : MvPowerSeries σ K) :
    φ G = MvPowerSeries.constantCoeff G := by
  have hsurj : Function.Surjective φ := fun c => ⟨algebraMap K _ c, φ.commutes c⟩
  have hker : RingHom.ker φ = IsLocalRing.maximalIdeal (MvPowerSeries σ K) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ hsurj)
  have hmem : G - MvPowerSeries.C (MvPowerSeries.constantCoeff G) ∈ RingHom.ker φ := by
    rw [hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff, map_sub, MvPowerSeries.constantCoeff_C, sub_self]
    exact not_isUnit_zero
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
  rw [hmem, MvPowerSeries.c_eq_algebraMap, AlgHom.commutes]
  rfl

theorem exists_eq_single_of_degree_eq_one {σ : Type*} (m : σ →₀ ℕ) (hm : m.degree = 1) :
    ∃ j, m = Finsupp.single j 1 := by
  classical
  have hne : m ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 hne
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hj
  refine ⟨j, ?_⟩
  have hsplit := Finsupp.single_add_erase j m
  have hdeg : m j + (m.erase j).degree = 1 := by
    rw [← hm]
    conv_rhs => rw [← hsplit]
    rw [map_add, Finsupp.degree_single]
  have hj1 : m j = 1 := by omega
  have h0 : (m.erase j).degree = 0 := by omega
  rw [Finsupp.degree_eq_zero_iff] at h0
  rw [← hsplit, h0, add_zero, hj1]

variable {d : ℕ} {k : Type*} [Field k]

noncomputable def linCoeff (f : MvPowerSeries (Fin d) k) : Fin d → k := fun j => MvPowerSeries.coeff (Finsupp.single j 1) f

@[scoped simp] theorem linCoeff_apply (f : MvPowerSeries (Fin d) k) (j : Fin d) :
    linCoeff f j = MvPowerSeries.coeff (Finsupp.single j 1) f := rfl

theorem sub_sum_linCoeff_mem_sq (f : MvPowerSeries (Fin d) k) (hf : MvPowerSeries.constantCoeff f = 0) :
    f - ∑ j, MvPowerSeries.C (linCoeff f j) * X j ∈
      (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) k))) ^ 2 := by
  classical
  refine MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero 2 _ fun m hm => ?_
  rw [map_sub, map_sum]
  have hX : ∀ j, MvPowerSeries.coeff m (MvPowerSeries.C (linCoeff f j) * X j) =
      if m = Finsupp.single j 1 then linCoeff f j else 0 := by
    intro j
    rw [mul_comm, MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_X]
    split_ifs <;> simp
  simp_rw [hX]
  rcases Nat.lt_succ_iff.1 hm |>.eq_or_lt with h1 | h0
  · obtain ⟨j, rfl⟩ := exists_eq_single_of_degree_eq_one m h1
    rw [Finset.sum_eq_single j]
    · simp [linCoeff]
    · intro i _ hij
      rw [if_neg]
      intro h
      exact hij (Finsupp.single_left_injective one_ne_zero h).symm
    · intro h; exact absurd (Finset.mem_univ j) h
  · have : m = 0 := (Finsupp.degree_eq_zero_iff m).1 (by omega)
    subst this
    rw [Finset.sum_eq_zero]
    · simpa using hf
    · intro j _
      rw [if_neg]
      exact (Finsupp.single_ne_zero.2 one_ne_zero).symm

section Cotangent

variable {p : ℕ} [Fact p.Prime] {B : Type v} [CommRing B] [Bialgebra (ZMod p) B]
variable (κ : MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] B)

local notation "𝔪" => RingHom.ker (Bialgebra.counitAlgHom (ZMod p) B)

theorem counit_apply_eq_constantCoeff (f : MvPowerSeries (Fin d) (ZMod p)) :
    Coalgebra.counit (R := ZMod p) (κ f) = MvPowerSeries.constantCoeff f := by
  have := algHom_apply_eq_constantCoeff ((Bialgebra.counitAlgHom (ZMod p) B).comp κ) f
  simpa using this

theorem apply_mem_augIdeal_iff (f : MvPowerSeries (Fin d) (ZMod p)) :
    κ f ∈ 𝔪 ↔ MvPowerSeries.constantCoeff f = 0 := by
  rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply, counit_apply_eq_constantCoeff]

theorem X_mem_augIdeal (j : Fin d) : κ (X j) ∈ 𝔪 := by
  rw [apply_mem_augIdeal_iff, MvPowerSeries.constantCoeff_X]

theorem map_span_X_le : Ideal.map κ (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ≤ 𝔪 := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  exact X_mem_augIdeal κ j

theorem apply_mem_sq_of_mem_sq {g : MvPowerSeries (Fin d) (ZMod p)}
    (hg : g ∈ (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ 2) :
    κ g ∈ 𝔪 ^ 2 := by
  have := Ideal.mem_map_of_mem κ hg
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono (map_span_X_le κ) 2 this

noncomputable def xi : (Fin d → ZMod p) →ₗ[ZMod p] (𝔪).Cotangent :=
  ∑ j, (LinearMap.proj j).smulRight ((𝔪).toCotangent ⟨κ (X j), X_mem_augIdeal κ j⟩)

theorem xi_apply (c : Fin d → ZMod p) :
    xi κ c = ∑ j, c j • (𝔪).toCotangent ⟨κ (X j), X_mem_augIdeal κ j⟩ := by
  simp [xi, LinearMap.sum_apply]

theorem toCotangent_apply_eq_xi_linCoeff (f : MvPowerSeries (Fin d) (ZMod p))
    (hf : MvPowerSeries.constantCoeff f = 0) (hmem : κ f ∈ 𝔪) :
    (𝔪).toCotangent ⟨κ f, hmem⟩ = xi κ (linCoeff f) := by
  classical
  have hsq := apply_mem_sq_of_mem_sq κ (sub_sum_linCoeff_mem_sq f hf)
  have hlin_mem : κ (∑ j, MvPowerSeries.C (linCoeff f j) * X j) ∈ 𝔪 := by
    rw [map_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (X_mem_augIdeal κ j)
  have hsplit : (⟨κ f, hmem⟩ : 𝔪) =
      ⟨κ (∑ j, MvPowerSeries.C (linCoeff f j) * X j), hlin_mem⟩ +
        ⟨κ (f - ∑ j, MvPowerSeries.C (linCoeff f j) * X j), by
          rw [map_sub]; exact Ideal.sub_mem _ hmem hlin_mem⟩ := by
    ext; simp [map_sub]
  have hzero : (𝔪).toCotangent ⟨κ (f - ∑ j, MvPowerSeries.C (linCoeff f j) * X j), by
      rw [map_sub]; exact Ideal.sub_mem _ hmem hlin_mem⟩ = 0 := (Ideal.toCotangent_eq_zero _ _).2 hsq
  rw [hsplit, map_add, hzero, add_zero, xi_apply]

  have : (⟨κ (∑ j, MvPowerSeries.C (linCoeff f j) * X j), hlin_mem⟩ : 𝔪) =
      ∑ j, linCoeff f j • (⟨κ (X j), X_mem_augIdeal κ j⟩ : 𝔪) := by
    ext
    simp only [map_sum, map_mul, AlgHom.commutes, Submodule.coe_sum, Submodule.coe_smul_of_tower,
      Algebra.smul_def, MvPowerSeries.c_eq_algebraMap]
  rw [this, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul_of_tower]

theorem xi_surjective (hκ : Function.Surjective κ) : Function.Surjective (xi κ) := by
  intro t
  obtain ⟨⟨x, hx⟩, rfl⟩ := (𝔪).toCotangent_surjective t
  obtain ⟨f, rfl⟩ := hκ x
  exact ⟨linCoeff f, (toCotangent_apply_eq_xi_linCoeff κ f ((apply_mem_augIdeal_iff κ f).1 hx) hx).symm⟩

end Cotangent

section Linear

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [Fact p.Prime] [Algebra 𝓞 (ZMod p)]

theorem exists_eq_natCast_add_mul (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) (c : 𝓞) :
    ∃ (n : ℕ) (t : 𝓞), c = n + (p : 𝓞) * t ∧ algebraMap 𝓞 (ZMod p) c = n := by
  refine ⟨(algebraMap 𝓞 (ZMod p) c).val, ?_⟩
  have hmem : c - ((algebraMap 𝓞 (ZMod p) c).val : 𝓞) ∈ RingHom.ker (algebraMap 𝓞 (ZMod p)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [hker, Ideal.mem_span_singleton'] at hmem
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, by linear_combination -ht, (ZMod.natCast_zmod_val _).symm⟩

variable {M : Type*} [AddCommGroup M] [Module 𝓞 M]

noncomputable def linearOfKillsP (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (Λ : M →+ (Fin d → ZMod p)) (hΛ : ∀ y : M, Λ ((p : 𝓞) • y) = 0) : M →ₗ[𝓞] (Fin d → ZMod p) where
  toFun := Λ
  map_add' := Λ.map_add
  map_smul' c x := by
    obtain ⟨n, t, rfl, hc⟩ := exists_eq_natCast_add_mul hker c
    have h1 : Λ (((n : 𝓞) + (p : 𝓞) * t) • x) = n • Λ x := by
      rw [add_smul, map_add, mul_smul, hΛ, add_zero, Nat.cast_smul_eq_nsmul, map_nsmul]
    rw [h1, RingHom.id_apply]
    ext j
    rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def ((n : 𝓞) + (p : 𝓞) * t), hc, nsmul_eq_mul]

@[scoped simp] theorem linearOfKillsP_apply (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (Λ : M →+ (Fin d → ZMod p)) (hΛ : ∀ y : M, Λ ((p : 𝓞) • y) = 0) (x : M) :
    linearOfKillsP hker Λ hΛ x = Λ x := rfl

end Linear

section Witt

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]

theorem coeff_last_wittHomVerschiebung {n : ℕ} (u : wittHom R p (n + 2) A) :
    ((wittHomVerschiebung R p (n + 2) A u : wittHom R p (n + 2) A) : TruncatedWittVector p (n + 2) A).coeff
        (Fin.last (n + 1)) =
      (u : TruncatedWittVector p (n + 2) A).coeff ⟨n, by omega⟩ := by
  rw [coe_wittHomVerschiebung]
  have := TruncWitt.coeff_verschiebung_succ (p := p) (u : TruncatedWittVector p (n + 2) A) n (by omega)
  convert this using 2
  rfl

end Witt

end Deformation.HondaSystem.LamAux
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq.Deformation P2MW.S_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq.Deformation.HondaSystem P2MW.S_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq.Deformation.HondaSystem.LamAux"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq.Deformation P2MW.S_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq.Deformation.HondaSystem"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq.Deformation"

open _root_.Deformation _root_.P2MW.S_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq.Deformation _root_.Deformation.DieudonneModule Deformation.HondaSystem.LamAux in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v) (hs : ∀ v, Function.Surjective (s v))
    (hrankG : ∀ v, Module.finrank (ZMod p) (G v) = p ^ (v * r))
    (hkerG : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (G (v + 1)) (p ^ v))
    (hunipG : ∀ v, IsLocalRing (CartierDual (ZMod p) (G v)))
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπ : ∀ v, Function.Surjective (π v))
    (hπker : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x))
    (hπV : ∀ v x, π v (H₁.V x) = Deformation.DieudonneModule.verschiebung (ZMod p) p (G v) (π v x))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
    (Gc₁ Ge₁ : Type v) [CommRing Gc₁] [HopfAlgebra (ZMod p) Gc₁] [Coalgebra.IsCocomm (ZMod p) Gc₁]
    [Module.Finite (ZMod p) Gc₁] [CommRing Ge₁] [HopfAlgebra (ZMod p) Ge₁] [Coalgebra.IsCocomm (ZMod p) Ge₁]
    [Module.Finite (ZMod p) Ge₁]
    (qc₁ : G 1 →ₐc[ZMod p] Gc₁) (πe₁ : G 1 →ₐc[ZMod p] Ge₁) (Θ₁ : G 1 →ₐc[ZMod p] Gc₁ ⊗[ZMod p] Ge₁)
    (hGc₁ : IsLocalRing Gc₁) (hGe₁ : IsReduced Ge₁) (hqc₁ : Function.Surjective qc₁)
    (hΘ₁ : Function.Bijective Θ₁)
    (hΘ₁apply : ∀ b, Θ₁ b = Algebra.TensorProduct.map (qc₁ : G 1 →ₐ[ZMod p] Gc₁) (πe₁ : G 1 →ₐ[ZMod p] Ge₁)
      (Coalgebra.comul (R := ZMod p) b))
    {d : ℕ} (κ₁ : MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] Gc₁) (hκ₁ : Function.Surjective κ₁)
    (hκ₁ε : ∀ i, Coalgebra.counit (R := ZMod p) (κ₁ (X i)) = 0)
    (hκ₁ker : RingHom.ker κ₁ ≤ (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ 2)
    (hd : d = Module.finrank (ZMod p) (PDivisibleGroup.Hopf.augIdeal (ZMod p) Gc₁).Cotangent) :
    ∃ (lam₀ lam₁ : H₁.L →ₗ[𝓞] (Fin d → ZMod p)) (C : Matrix (Fin d) (Fin d) (ZMod p)),
      Module.Free 𝓞 H₁.L ∧ Module.Finite 𝓞 H₁.L ∧ Module.finrank 𝓞 H₁.L = d ∧
      Function.Surjective lam₀ ∧
      (∀ m : H₁.L, lam₀ m = 0 → m ∈ Ideal.span {(p : 𝓞)} • (⊤ : Submodule 𝓞 H₁.L)) ∧
      IsNilpotent C ∧ (∀ m, lam₁ m = C.mulVec (lam₀ m)) ∧
      (∀ (l : H₁.L) (n : ℕ) (u : Deformation.wittHom (ZMod p) p (n + 1) Gc₁),
        Deformation.DieudonneModule.of (ZMod p) p Gc₁ (n + 1) u =
          Deformation.DieudonneModule.map (ZMod p) p qc₁ (π 1 ((l : H₁.L) : Fin r → 𝓞)) →
        ∀ f : MvPowerSeries (Fin d) (ZMod p), MvPowerSeries.constantCoeff f = 0 →
          κ₁ f = (u : TruncatedWittVector p (n + 1) Gc₁).coeff (Fin.last n) →
          ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) f = lam₀ l j) ∧
      (∀ (l : H₁.L) (n : ℕ) (u : Deformation.wittHom (ZMod p) p (n + 2) Gc₁),
        Deformation.DieudonneModule.of (ZMod p) p Gc₁ (n + 2) u =
          Deformation.DieudonneModule.map (ZMod p) p qc₁ (π 1 ((l : H₁.L) : Fin r → 𝓞)) →
        ∀ f : MvPowerSeries (Fin d) (ZMod p), MvPowerSeries.constantCoeff f = 0 →
          κ₁ f = (u : TruncatedWittVector p (n + 2) Gc₁).coeff ⟨n, by omega⟩ →
          ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) f = lam₁ l j) := by
  classical

  set M₁c := DieudonneModule (ZMod p) p Gc₁ with hM₁c
  have hp0 : algebraMap 𝓞 (ZMod p) (p : 𝓞) = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _

  have hunipc : IsLocalRing (CartierDual (ZMod p) Gc₁) :=
    HopfAlgebra.isLocalRing_cartierDual_of_surjective (ZMod p) (G 1) Gc₁ qc₁ hqc₁ (hunipG 1)
  obtain ⟨θ, hθof, hθsurj, hθker⟩ :=
    Deformation.DieudonneModule.exists_addMonoidHom_cotangent_surjective_ker_eq_range_frobenius_of_isLocalRing_cartierDual
      p Gc₁ hunipc hGc₁
  have hsplit := bijective_prod_map_of_bijective_tensorProduct_comul p (G 1) Gc₁ Ge₁ qc₁ πe₁ Θ₁ hΘ₁ hΘ₁apply
  have hFe := Deformation.DieudonneModule.frobenius_bijective_of_isReduced p Ge₁ hGe₁

  have hξsurj := xi_surjective κ₁ hκ₁
  haveI : Module.Finite (ZMod p) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Gc₁)).Cotangent :=
    Module.Finite.of_surjective (xi κ₁) hξsurj
  have hd' : Module.finrank (ZMod p) (Fin d → ZMod p) =
      Module.finrank (ZMod p) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Gc₁)).Cotangent := by
    rw [Module.finrank_fin_fun]; exact hd
  have hξinj : Function.Injective (xi κ₁) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd').2 hξsurj
  let ξe := LinearEquiv.ofBijective (xi κ₁) ⟨hξinj, hξsurj⟩
  have hξe : ∀ c, ξe c = xi κ₁ c := fun c => rfl

  let Λ₀ : (Fin r → 𝓞) →+ (Fin d → ZMod p) :=
    ξe.symm.toLinearMap.toAddMonoidHom.comp (θ.comp ((DieudonneModule.map (ZMod p) p qc₁).comp (π 1)))
  have hΛ₀ : ∀ x, ξe (Λ₀ x) = θ (DieudonneModule.map (ZMod p) p qc₁ (π 1 x)) := fun x =>
    ξe.apply_symm_apply _
  have hπp : ∀ y : Fin r → 𝓞, π 1 ((p : 𝓞) • y) = 0 := fun y => (hπker 1 _).2 ⟨y, by rw [pow_one]⟩
  have hΛ₀p : ∀ y : Fin r → 𝓞, Λ₀ ((p : 𝓞) • y) = 0 := by
    intro y
    show ξe.symm (θ (DieudonneModule.map (ZMod p) p qc₁ (π 1 ((p : 𝓞) • y)))) = 0
    rw [hπp, map_zero, map_zero, map_zero]
  let Λ : (Fin r → 𝓞) →ₗ[𝓞] (Fin d → ZMod p) := linearOfKillsP hker Λ₀ hΛ₀p
  have hΛ : ∀ x, ξe (Λ x) = θ (DieudonneModule.map (ZMod p) p qc₁ (π 1 x)) := hΛ₀
  have hΛinj : ∀ x c, θ (DieudonneModule.map (ZMod p) p qc₁ (π 1 x)) = ξe c → Λ x = c := by
    intro x c h
    exact ξe.injective ((hΛ x).trans h)

  have hΛF : ∀ x, Λ (H₁.F x) = 0 := by
    intro x
    apply hΛinj
    rw [map_zero, hπF, DieudonneModule.map_frobenius]
    exact (hθker _).2 ⟨_, rfl⟩
  have hΛp : ∀ x : Fin r → 𝓞, Λ ((p : 𝓞) • x) = 0 := hΛ₀p
  have hΛV : ∀ x, ξe (Λ (H₁.V x)) =
      θ (DieudonneModule.verschiebung (ZMod p) p Gc₁ (DieudonneModule.map (ZMod p) p qc₁ (π 1 x))) := by
    intro x
    rw [hΛ, hπV, DieudonneModule.map_verschiebung]

  let lam₀ : H₁.L →ₗ[𝓞] (Fin d → ZMod p) := Λ.comp H₁.L.subtype
  let lam₁ : H₁.L →ₗ[𝓞] (Fin d → ZMod p) := Λ.comp (H₁.V.comp H₁.L.subtype)
  have hlam₀ : ∀ l : H₁.L, lam₀ l = Λ (l : Fin r → 𝓞) := fun l => rfl
  have hlam₁ : ∀ l : H₁.L, lam₁ l = Λ (H₁.V (l : Fin r → 𝓞)) := fun l => rfl

  have hdec : ∀ x : Fin r → 𝓞, ∃ (w : Fin r → 𝓞) (l : H₁.L), x = H₁.F w + l := by
    intro x
    have hx : x ∈ LinearMap.range H₁.F ⊔ H₁.L := by rw [H₁.sh2']; trivial
    obtain ⟨a, ⟨w, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨w, ⟨b, hb⟩, rfl⟩

  have hsurj : Function.Surjective lam₀ := by
    intro c
    obtain ⟨z, hz⟩ := hθsurj (ξe c)
    obtain ⟨y, hy⟩ := hsplit.2 (z, 0)
    obtain ⟨x, rfl⟩ := hπ 1 y
    obtain ⟨w, l, rfl⟩ := hdec x
    refine ⟨l, ?_⟩
    have h1 : Λ (H₁.F w + l) = c := by
      apply hΛinj
      rw [(Prod.mk.inj hy).1, hz]
    rwa [map_add, hΛF, zero_add] at h1

  have hker₀ : ∀ l : H₁.L, lam₀ l = 0 → ∃ y : H₁.L, l = (p : 𝓞) • y := by
    intro l hl
    have hθ0 : θ (DieudonneModule.map (ZMod p) p qc₁ (π 1 (l : Fin r → 𝓞))) = 0 := by
      rw [← hΛ, ← hlam₀, hl, map_zero]
    obtain ⟨zc, hzc⟩ := (hθker _).1 hθ0
    obtain ⟨ze, hze⟩ := hFe.2 (DieudonneModule.map (ZMod p) p πe₁ (π 1 (l : Fin r → 𝓞)))
    obtain ⟨w, hw⟩ := hsplit.2 (zc, ze)
    have hw1 := (Prod.mk.inj hw).1
    have hw2 := (Prod.mk.inj hw).2
    have hfw : DieudonneModule.frobenius (ZMod p) p (G 1) w = π 1 (l : Fin r → 𝓞) := by
      apply hsplit.1
      simp only [DieudonneModule.map_frobenius, hw1, hw2]
      exact Prod.ext hzc hze
    obtain ⟨x', rfl⟩ := hπ 1 w
    rw [← hπF] at hfw
    have h0 : π 1 ((l : Fin r → 𝓞) - H₁.F x') = 0 := by rw [map_sub, hfw, sub_self]
    obtain ⟨y', hy'⟩ := (hπker 1 _).1 h0
    rw [pow_one] at hy'
    have hrange : (l : Fin r → 𝓞) ∈ LinearMap.range H₁.F := by
      refine ⟨x' + H₁.V y', ?_⟩
      rw [map_add, H₁.F_V_apply, ← hy', add_sub_cancel]
    obtain ⟨y, hyL, hy⟩ := H₁.sh1_le _ l.2 hrange
    exact ⟨⟨y, hyL⟩, Subtype.ext hy⟩
  have hkerlam : ∀ m : H₁.L, lam₀ m = 0 → m ∈ Ideal.span {(p : 𝓞)} • (⊤ : Submodule 𝓞 H₁.L) := by
    intro m hm
    obtain ⟨y, rfl⟩ := hker₀ m hm
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

  choose lb hlb using fun i : Fin d => hsurj (Pi.single i 1)
  let C : Matrix (Fin d) (Fin d) (ZMod p) := Matrix.of fun j i => lam₁ (lb i) j
  have hCcol : ∀ i, C.mulVec (Pi.single i 1) = lam₁ (lb i) := by
    intro i; rw [Matrix.mulVec_single_one]; rfl

  have hlift : ∀ c : Fin d → ZMod p, ∃ c' : Fin d → 𝓞, ∀ i, algebraMap 𝓞 (ZMod p) (c' i) = c i :=
    fun c => ⟨fun i => ((c i).val : 𝓞), fun i => by rw [map_natCast, ZMod.natCast_zmod_val]⟩
  have hsmul : ∀ (a : 𝓞) (v : Fin d → ZMod p), a • v = algebraMap 𝓞 (ZMod p) a • v :=
    fun a v => (algebraMap_smul (ZMod p) a v).symm
  have hΛVC : ∀ x : Fin r → 𝓞, Λ (H₁.V x) = C.mulVec (Λ x) := by
    intro x
    obtain ⟨w, l, rfl⟩ := hdec x
    obtain ⟨c', hc'⟩ := hlift (lam₀ l)

    have h0 : lam₀ (l - ∑ i, c' i • lb i) = 0 := by
      rw [map_sub, map_sum, sub_eq_zero]
      ext j
      simp only [Finset.sum_apply, map_smul, hlb, hsmul, hc', Pi.smul_apply, Pi.single_apply, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    obtain ⟨y, hy⟩ := hker₀ _ h0
    have hl : (l : Fin r → 𝓞) = ∑ i, c' i • (lb i : Fin r → 𝓞) + (p : 𝓞) • (y : Fin r → 𝓞) := by
      have := congrArg (fun m : H₁.L => (m : Fin r → 𝓞)) hy
      simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul] at this
      rw [← this, add_sub_cancel]
    have hΛVl : Λ (H₁.V l) = ∑ i, c' i • lam₁ (lb i) := by
      rw [hl, map_add, map_smul, map_add, hΛp, add_zero, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, hlam₁]
    have hΛl : Λ l = ∑ i, c' i • Pi.single i 1 := by
      rw [← hlam₀, show lam₀ l = lam₀ (l - ∑ i, c' i • lb i) + lam₀ (∑ i, c' i • lb i) by
        rw [map_sub, sub_add_cancel], h0, zero_add, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hlb]
    have e1 : Λ (H₁.V (H₁.F w + (l : Fin r → 𝓞))) = Λ (H₁.V l) := by
      rw [map_add, map_add, H₁.V_F_apply, hΛp, zero_add]
    have e2 : Λ (H₁.F w + (l : Fin r → 𝓞)) = Λ l := by rw [map_add, hΛF, zero_add]
    rw [e1, e2, hΛVl, hΛl, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsmul, hsmul (c' i) (Pi.single i 1), Matrix.mulVec_smul, hCcol]
  have hlam₁C : ∀ m, lam₁ m = C.mulVec (lam₀ m) := fun m => hΛVC m

  have hΛVk : ∀ (k : ℕ) (x : Fin r → 𝓞), Λ ((H₁.V ^ k) x) = (C ^ k).mulVec (Λ x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih => intro x; rw [pow_succ', Module.End.mul_apply, hΛVC, ih, Matrix.mulVec_mulVec, ← pow_succ']
  have hθVk : ∀ (k : ℕ) (x : Fin r → 𝓞), ξe (Λ ((H₁.V ^ k) x)) =
      θ ((DieudonneModule.verschiebung (ZMod p) p Gc₁)^[k] (DieudonneModule.map (ZMod p) p qc₁ (π 1 x))) := by
    intro k
    induction k with
    | zero => intro x; simpa using hΛ x
    | succ k ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply', hπV, DieudonneModule.map_verschiebung]
      congr 1
      exact (Function.Commute.iterate_self _ k _).symm ▸ rfl
  have hCnil : IsNilpotent C := by

    have hvan : ∀ i : Fin d, ∃ n : ℕ, (C ^ n).mulVec (Pi.single i 1) = 0 := by
      intro i
      obtain ⟨n, u, hu⟩ := DieudonneModule.exists_of (DieudonneModule.map (ZMod p) p qc₁ (π 1 (lb i : Fin r → 𝓞)))
      refine ⟨n, ?_⟩
      have hVof : ∀ (k : ℕ) (x : wittHom (ZMod p) p n Gc₁),
          (DieudonneModule.verschiebung (ZMod p) p Gc₁)^[k] (DieudonneModule.of (ZMod p) p Gc₁ n x) =
            DieudonneModule.of (ZMod p) p Gc₁ n ((wittHomVerschiebung (ZMod p) p n Gc₁)^[k] x) := by
        intro k
        induction k with
        | zero => intro x; rfl
        | succ k ih =>
          intro x
          rw [Function.iterate_succ_apply', ih, DieudonneModule.verschiebung_of, Function.iterate_succ_apply']
      rw [← hlb i, hlam₀, ← hΛVk]
      apply ξe.injective
      rw [hθVk, map_zero, ← hu, hVof, wittHomVerschiebung_iterate_eq_zero, map_zero, map_zero]
    choose nv hnv using hvan
    refine ⟨∑ i, nv i, ?_⟩
    ext j i
    have : (C ^ ∑ i, nv i).mulVec (Pi.single i 1) = 0 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), pow_add, ← Matrix.mulVec_mulVec, hnv, Matrix.mulVec_zero]
    have := congrFun this j
    rwa [Matrix.mulVec_single_one] at this

  obtain ⟨_instDom, _instDVR, -, -⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span p hp hker
  haveI : IsPrincipalIdealRing 𝓞 := IsDiscreteValuationRing.toIsPrincipalIdealRing
  obtain ⟨n, β⟩ := Submodule.basisOfPid (Pi.basisFun 𝓞 (Fin r)) H₁.L
  have hfree : Module.Free 𝓞 H₁.L := Module.Free.of_basis β
  have hfin : Module.Finite 𝓞 H₁.L := Module.Finite.of_basis β
  have hrankn : Module.finrank 𝓞 H₁.L = n := by rw [Module.finrank_eq_card_basis β, Fintype.card_fin]
  have hliftn : ∀ c : Fin n → ZMod p, ∃ c' : Fin n → 𝓞, ∀ i, algebraMap 𝓞 (ZMod p) (c' i) = c i :=
    fun c => ⟨fun i => ((c i).val : 𝓞), fun i => by rw [map_natCast, ZMod.natCast_zmod_val]⟩
  let lamb : (Fin n → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p) := ∑ k, (LinearMap.proj k).smulRight (lam₀ (β k))
  have hlamb : ∀ w, lamb w = ∑ k, w k • lam₀ (β k) := by intro w; simp [lamb, LinearMap.sum_apply]
  have hlamb_surj : Function.Surjective lamb := by
    intro c
    obtain ⟨l, rfl⟩ := hsurj c
    refine ⟨fun k => algebraMap 𝓞 (ZMod p) (β.repr l k), ?_⟩
    rw [hlamb]
    conv_rhs => rw [← β.sum_repr l]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hsmul]
  have hlamb_inj : Function.Injective lamb := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    obtain ⟨c', hc'⟩ := hliftn w
    have hl0 : lam₀ (β.equivFun.symm c') = 0 := by
      rw [← hw, hlamb, Module.Basis.equivFun_symm_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hsmul, hc']
    obtain ⟨y, hy⟩ := hker₀ _ hl0
    have hc'p : c' = (p : 𝓞) • β.equivFun y := by
      have := congrArg β.equivFun hy
      rwa [LinearEquiv.apply_symm_apply, map_smul] at this
    ext k
    rw [← hc', hc'p, Pi.smul_apply, smul_eq_mul, map_mul, hp0, zero_mul, Pi.zero_apply]
  have hnd : n = d := by
    have := LinearEquiv.finrank_eq (LinearEquiv.ofBijective lamb ⟨hlamb_inj, hlamb_surj⟩)
    rwa [Module.finrank_fin_fun, Module.finrank_fin_fun] at this

  have hcoeff_mem : ∀ {m : ℕ} (u : wittHom (ZMod p) p m Gc₁) (i : Fin m),
      (u : TruncatedWittVector p m Gc₁).coeff i ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Gc₁) := by
    intro m u i
    rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply]
    exact counit_coeff_of_mem_wittHom u.2 i
  have bridge₀ : ∀ (l : H₁.L) (n : ℕ) (u : Deformation.wittHom (ZMod p) p (n + 1) Gc₁),
      Deformation.DieudonneModule.of (ZMod p) p Gc₁ (n + 1) u =
        Deformation.DieudonneModule.map (ZMod p) p qc₁ (π 1 ((l : H₁.L) : Fin r → 𝓞)) →
      ∀ f : MvPowerSeries (Fin d) (ZMod p), MvPowerSeries.constantCoeff f = 0 →
        κ₁ f = (u : TruncatedWittVector p (n + 1) Gc₁).coeff (Fin.last n) →
        ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) f = lam₀ l j := by
    intro l n u hu f hf hκf j
    have hfm : κ₁ f ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Gc₁) := (apply_mem_augIdeal_iff κ₁ f).2 hf
    have key := toCotangent_apply_eq_xi_linCoeff κ₁ f hf hfm
    have hΛl : Λ (l : Fin r → 𝓞) = linCoeff f := by
      apply hΛinj
      rw [← hu, hθof n u (hcoeff_mem u _), hξe, ← key]
      congr 1
      exact Subtype.ext hκf.symm
    rw [hlam₀, hΛl, linCoeff_apply]
  have bridge₁ : ∀ (l : H₁.L) (n : ℕ) (u : Deformation.wittHom (ZMod p) p (n + 2) Gc₁),
      Deformation.DieudonneModule.of (ZMod p) p Gc₁ (n + 2) u =
        Deformation.DieudonneModule.map (ZMod p) p qc₁ (π 1 ((l : H₁.L) : Fin r → 𝓞)) →
      ∀ f : MvPowerSeries (Fin d) (ZMod p), MvPowerSeries.constantCoeff f = 0 →
        κ₁ f = (u : TruncatedWittVector p (n + 2) Gc₁).coeff ⟨n, by omega⟩ →
        ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) f = lam₁ l j := by
    intro l n u hu f hf hκf j
    have hfm : κ₁ f ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Gc₁) := (apply_mem_augIdeal_iff κ₁ f).2 hf
    have key := toCotangent_apply_eq_xi_linCoeff κ₁ f hf hfm
    have hΛl : Λ (H₁.V (l : Fin r → 𝓞)) = linCoeff f := by
      apply ξe.injective
      rw [hΛV, ← hu, DieudonneModule.verschiebung_of, hθof (n + 1) _ (hcoeff_mem _ _), hξe, ← key]
      congr 1
      apply Subtype.ext
      show ((wittHomVerschiebung (ZMod p) p (n + 2) Gc₁ u : wittHom (ZMod p) p (n + 2) Gc₁) :
        TruncatedWittVector p (n + 2) Gc₁).coeff (Fin.last (n + 1)) = κ₁ f
      rw [coeff_last_wittHomVerschiebung, hκf]
    rw [hlam₁, hΛl, linCoeff_apply]
  exact ⟨lam₀, lam₁, C, hfree, hfin, hrankn.trans hnd, hsurj, hkerlam, hCnil, hlam₁C, bridge₀, bridge₁⟩

end S_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq
end P2MW
export P2MW.S_Deformation_HondaSystem_exists_linearMap_surjective_mulVec_isNilpotent_coeff_eq (solution)
