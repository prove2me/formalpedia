-- Prove2me | solution 1 for Deformation.HondaSystem.exists_pDivisibleTower_dieudonneModule_of_range_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/3e03b175-97d4-5105-bcef-70154e037f06

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_Deformation_DieudonneDatum_exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le
import Theorems.Thm_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod
import Theorems.Thm_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_dieudonneModule_of_range_pow_le
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient Deformation.WittGroup.instAlgebra Deformation.WittGroup.instHopfAlgebra Deformation.WittGroup.instInhabited Deformation.WittGroup.instCommRing Deformation.WittGroup.instBialgebra Deformation.WittGroup.instIsCocomm Deformation.WittKernel.instModuleFinite Deformation.WittKernel.isHopfIdeal CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl Deformation.HondaSystem.SplitCoordinates.instHopfGc Deformation.HondaSystem.SplitCoordinates.instCommRingGe Deformation.HondaSystem.SplitCoordinates.instCommRingGc Deformation.HondaSystem.SplitCoordinates.instCommRingEt Deformation.HondaSystem.SplitCoordinates.instHopfGe Deformation.HondaSystem.SplitCoordinates.instHopfEt MvFormalGroup.instIsCommAddMv MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring"
p2m_attr_erase "instance" "MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid Deformation.UnipotentWittCovector.instInhabited Deformation.UnipotentWittCovector.instAddCommGroup Deformation.TruncWitt.shiftLE_directedSystem instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk Deformation.WittGroup.coe_univHom Deformation.WittGroup.counit_X Deformation.WittGroup.rehom_apply Deformation.WittGroup.lift_X Deformation.WittGroup.antipode_X Deformation.WittGroup.comul_X Deformation.WittGroup.pointsEquiv_symm_apply_X Deformation.WittGroup.coeff_univ Deformation.WittKernel.π_apply Deformation.WittKernel.coe_tauto Deformation.TruncWitt.coeff_frobeniusFun_iterate Deformation.WittKernel.coeff_tauto ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply"
p2m_attr_erase "simp" "HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul Deformation.HondaSystem.SplitCoordinates.mk.sizeOf_spec Deformation.HondaSystem.SplitCoordinates.mk.injEq MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast Deformation.UnipotentWittCovector.lift_of Deformation.UnipotentWittCovector.of_shift Deformation.UnipotentWittCovector.frobenius_of Deformation.DieudonneModule.toCovector_of Deformation.TruncWitt.frobeniusAddHom_apply Deformation.UnipotentWittCovector.dieudonneDatum_F_apply Deformation.UnipotentWittCovector.map_of Deformation.UnipotentWittCovector.verschiebung_of Deformation.UnipotentWittCovector.dieudonneDatum_V_apply Deformation.DieudonneModule.evalMonoidHom_apply Deformation.DieudonneModule.eval_of Deformation.UnipotentWittCovector.of_shiftLE Deformation.PLoc.map_algebraMap Deformation.PLoc.map_invPow Deformation.UnipotentWittCovector.wUp_of Deformation.UnipotentWittCovector.wHom_apply Deformation.UnipotentWittCovector.wLevel_succ_truncate Deformation.PLoc.mapLinear_apply"

set_option autoImplicit false

universe u v w

namespace FontaineK3Assembly

open Function Deformation

variable {p : ℕ} [Fact p.Prime]

section Transport

variable {A : Type v} {B : Type w} [CommRing A] [CommRing B]
  [Bialgebra (ZMod p) A] [Bialgebra (ZMod p) B]

theorem coe_ofBijective_eq (e : A →ₐc[ZMod p] B) (he : Bijective e) :
    ((BialgEquiv.ofBijective e he : A ≃ₐc[ZMod p] B) : A →ₐc[ZMod p] B) = e :=
  BialgHom.ext fun _ => rfl

theorem symm_comp_eq_id (e : A →ₐc[ZMod p] B) (he : Bijective e) :
    ((BialgEquiv.ofBijective e he).symm : B →ₐc[ZMod p] A).comp e = BialgHom.id (ZMod p) A :=
  BialgHom.ext fun x => (BialgEquiv.ofBijective e he).symm_apply_apply x

theorem comp_symm_eq_id (e : A →ₐc[ZMod p] B) (he : Bijective e) :
    e.comp ((BialgEquiv.ofBijective e he).symm : B →ₐc[ZMod p] A) = BialgHom.id (ZMod p) B :=
  BialgHom.ext fun y => (BialgEquiv.ofBijective e he).apply_symm_apply y

theorem map_symm_map (e : A →ₐc[ZMod p] B) (he : Bijective e) (z : DieudonneModule (ZMod p) p A) :
    DieudonneModule.map (ZMod p) p ((BialgEquiv.ofBijective e he).symm : B →ₐc[ZMod p] A)
      (DieudonneModule.map (ZMod p) p e z) = z := by
  rw [← DieudonneModule.map_comp, symm_comp_eq_id, DieudonneModule.map_id]

theorem map_map_symm (e : A →ₐc[ZMod p] B) (he : Bijective e) (z : DieudonneModule (ZMod p) p B) :
    DieudonneModule.map (ZMod p) p e
      (DieudonneModule.map (ZMod p) p ((BialgEquiv.ofBijective e he).symm : B →ₐc[ZMod p] A) z) = z := by
  rw [← DieudonneModule.map_comp, comp_symm_eq_id, DieudonneModule.map_id]

theorem map_injective_of_bijective (e : A →ₐc[ZMod p] B) (he : Bijective e) :
    Injective (DieudonneModule.map (ZMod p) p e) :=
  (LeftInverse.injective (g := DieudonneModule.map (ZMod p) p
    ((BialgEquiv.ofBijective e he).symm : B →ₐc[ZMod p] A)) fun z => map_symm_map e he z)

theorem map_surjective_of_bijective (e : A →ₐc[ZMod p] B) (he : Bijective e) :
    Surjective (DieudonneModule.map (ZMod p) p e) :=
  fun z => ⟨_, map_map_symm e he z⟩

end Transport

section Nakayama

variable {D : Type v} [AddCommGroup D]

theorem le_of_nested_honda (F : D →+ D) (L' L'' : AddSubgroup D) (q v : ℕ)
    (hle : L' ≤ L'')
    (sh1 : ∀ x ∈ L'', (∃ a, F a = x) → ∃ y ∈ L'', x = (q : ℤ) • y)
    (sh2 : ∀ z : D, ∃ a, ∃ l ∈ L', z = F a + l)
    (hkill : ∀ z : D, (q : ℤ) ^ v • z = 0) : L'' ≤ L' := by

  have step : ∀ z ∈ L'', ∃ l ∈ L', ∃ y ∈ L'', z = l + (q : ℤ) • y := by
    intro z hz
    obtain ⟨a, l, hl, rfl⟩ := sh2 z
    have hFa : F a ∈ L'' := by
      have : F a + l - l ∈ L'' := L''.sub_mem hz (hle hl)
      simpa using this
    obtain ⟨y, hy, hFy⟩ := sh1 (F a) hFa ⟨a, rfl⟩
    exact ⟨l, hl, y, hy, by rw [hFy, add_comm]⟩

  have iter : ∀ n : ℕ, ∀ z ∈ L'', ∃ l ∈ L', ∃ y ∈ L'', z = l + (q : ℤ) ^ n • y := by
    intro n
    induction n with
    | zero => intro z hz; exact ⟨0, L'.zero_mem, z, hz, by simp⟩
    | succ n ih =>
      intro z hz
      obtain ⟨l, hl, y, hy, rfl⟩ := ih z hz
      obtain ⟨l', hl', y', hy', rfl⟩ := step y hy
      refine ⟨l + (q : ℤ) ^ n • l', L'.add_mem hl (L'.zsmul_mem hl' _), y', hy', ?_⟩
      rw [smul_add, smul_smul, ← pow_succ, add_assoc]
  intro z hz
  obtain ⟨l, hl, y, -, rfl⟩ := iter v z hz
  rw [hkill y, add_zero]
  exact hl

end Nakayama

section ThmOne

theorem hondaSystem_level {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (ℛ : Type v) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] (hrank : ∃ a : ℕ, Module.finrank 𝓞 ℛ = p ^ a) :
    ∃ H : HondaSystem (p : ℤ) (DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ)),
      H.toDieudonneDatum = DieudonneModule.dieudonneDatum (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ) ∧
      H.L = fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom :=
  DieudonneModule.exists_hondaSystem_L_eq_fontaineHodge p hp
    (ZMod.ringHom_surjective (algebraMap 𝓞 (ZMod p))) hker ℛ hrank

theorem fontaineHodge_le {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (ℛ : Type v) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] (hrank : ∃ a : ℕ, Module.finrank 𝓞 ℛ = p ^ a)
    (L' : AddSubgroup (DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ))) (v : ℕ)
    (hle : L' ≤ (fontaineHodge (ZMod p) p
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom).toAddSubgroup)
    (sh2 : ∀ z : DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ), ∃ a, ∃ l ∈ L',
      z = DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ) a + l)
    (hkill : ∀ z : DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ), (p : ℤ) ^ v • z = 0) :
    (fontaineHodge (ZMod p) p
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom).toAddSubgroup
      ≤ L' := by
  obtain ⟨Hv, hHvD, hHvL⟩ := hondaSystem_level p hp hker ℛ hrank
  have hHvF : ∀ a, Hv.F a = DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ) a :=
    fun a => by
      have := congrArg (fun D => D.F a) hHvD
      simpa using this
  rw [← hHvL] at hle ⊢
  refine le_of_nested_honda (DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) ℛ))
    L' Hv.L.toAddSubgroup p v hle ?_ sh2 hkill
  intro x hx hxF
  rw [Submodule.mem_toAddSubgroup] at hx
  obtain ⟨a, rfl⟩ := hxF
  obtain ⟨y, hy, hxy⟩ := Hv.sh1_le _ hx (LinearMap.mem_range.2 ⟨a, hHvF a⟩)
  exact ⟨y, (Submodule.mem_toAddSubgroup _).2 hy, hxy⟩

end ThmOne

end FontaineK3Assembly

open FontaineK3Assembly Deformation

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (hV : ∃ N : ℕ, ∀ x, ∃ y, (H₁.V ^ N) x = (p : 𝓞) • y) :
    ∃ (L : ℕ → Type u) (_ : ∀ v, CommRing (L v)) (_ : ∀ v, HopfAlgebra 𝓞 (L v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (L v)) (_ : ∀ v, Module.Free 𝓞 (L v))
      (_ : ∀ v, Module.Finite 𝓞 (L v)) (t : ∀ v, L (v + 1) →ₐc[𝓞] L v),
      (∀ v, Function.Surjective (t v)) ∧ (∀ v, Module.finrank 𝓞 (L v) = p ^ (v * r)) ∧
      (∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v)) ∧
      (∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v)))) ∧
    ∃ π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)),
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y) ∧
      (∀ v x, π v (H₁.F x) =
        Deformation.DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)) (π v x)) ∧
      (∀ v x, π v (H₁.V x) =
        Deformation.DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)) (π v x)) ∧
      (∀ v, (Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight :
            L v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L v)).toRingHom).toAddSubgroup =
        H₁.L.toAddSubgroup.map (π v)) ∧
      (∀ v x, Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v)) (π (v + 1) x) = π v x) := by
  classical

  obtain ⟨G, iG₁, iG₂, iG₃, iG₄, s, hs, hrankG, hkerG, hunipG, π, hπ, hπker, hπF, hπV, hπs⟩ :=
    Deformation.DieudonneDatum.exists_pDivisibleTower_zmod_dieudonneModule_of_range_pow_le
      p hp hker r H₁.toDieudonneDatum hV

  obtain ⟨L, iL₁, iL₂, iL₃, iL₄, iL₅, t, ht, hrankL, hkerL, e, hbij, hcompat, hLinc⟩ :=
    Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_pDivisibleTower_zmod
      p hp hker r H₁ G s hs hrankG hkerG hunipG π hπ hπker hπF hπV hπs

  obtain ⟨π', hπ'_apply⟩ :
      ∃ π' : ∀ v, (Fin r → 𝓞) →+ DieudonneModule (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)),
        ∀ v x, π' v x = DieudonneModule.map (ZMod p) p (e v) (π v x) :=
    ⟨fun v => (DieudonneModule.map (ZMod p) p (e v)).comp (π v), fun v x => rfl⟩
  have hΦinj : ∀ v, Function.Injective (DieudonneModule.map (ZMod p) p (e v)) := fun v =>
    map_injective_of_bijective (e v) (hbij v)
  have hΦsurj : ∀ v, Function.Surjective (DieudonneModule.map (ZMod p) p (e v)) := fun v =>
    map_surjective_of_bijective (e v) (hbij v)
  have hsurj : ∀ v, Function.Surjective (π' v) := fun v z => by
    obtain ⟨y, hy⟩ := hΦsurj v z
    obtain ⟨x, hx⟩ := hπ v y
    exact ⟨x, by rw [hπ'_apply, hx, hy]⟩
  have hker' : ∀ v x, π' v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y := by
    intro v x
    rw [← hπker v x, hπ'_apply]
    exact ⟨fun h => hΦinj v (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  have hF' : ∀ v x, π' v (H₁.F x) =
      DieudonneModule.frobenius (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)) (π' v x) := by
    intro v x
    rw [hπ'_apply, hπ'_apply, hπF v x, DieudonneModule.map_frobenius]
  have hV' : ∀ v x, π' v (H₁.V x) =
      DieudonneModule.verschiebung (ZMod p) p (TensorProduct 𝓞 (ZMod p) (L v)) (π' v x) := by
    intro v x
    rw [hπ'_apply, hπ'_apply, hπV v x, DieudonneModule.map_verschiebung]
  have hunip : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v))) := by

    intro v
    haveI := hunipG v
    exact (CartierDual.congr (BialgEquiv.ofBijective (e v) (hbij v))).symm.toAlgEquiv.toRingEquiv.isLocalRing
  have htrans : ∀ v x, DieudonneModule.map (ZMod p) p
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v)) (π' (v + 1) x) = π' v x := by

    intro v x
    rw [hπ'_apply, hπ'_apply, ← DieudonneModule.map_comp, ← hcompat v, DieudonneModule.map_comp, hπs]
  have hLeq : ∀ v, (fontaineHodge (ZMod p) p
      (Algebra.TensorProduct.includeRight :
        L v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L v)).toRingHom).toAddSubgroup =
      H₁.L.toAddSubgroup.map (π' v) := by

    intro v

    have hge : H₁.L.toAddSubgroup.map (π' v) ≤
        (fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight :
            L v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L v)).toRingHom).toAddSubgroup := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Submodule.mem_toAddSubgroup, hπ'_apply]
      exact hLinc v x ((Submodule.mem_toAddSubgroup _).1 hx)
    refine le_antisymm (fontaineHodge_le p hp hker (L v) ⟨v * r, hrankL v⟩ _ v hge ?_ ?_) hge
    ·
      intro z
      obtain ⟨m, rfl⟩ := hsurj v z
      have hm : m ∈ LinearMap.range H₁.F ⊔ H₁.L := by rw [H₁.sh2']; trivial
      obtain ⟨_, ⟨a, rfl⟩, l, hl, rfl⟩ := Submodule.mem_sup.1 hm
      refine ⟨π' v a, π' v l, ⟨l, hl, rfl⟩, ?_⟩
      rw [map_add, hF']
    ·
      intro z
      obtain ⟨m, rfl⟩ := hsurj v z
      rw [← map_zsmul]
      have h1 : (p : ℤ) ^ v • m = (p : 𝓞) ^ v • m := by
        rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      rw [h1]
      exact (hker' v _).2 ⟨m, rfl⟩
  exact ⟨L, iL₁, iL₂, iL₃, iL₄, iL₅, t, ht, hrankL, hkerL, hunip, π', hsurj, hker', hF', hV', hLeq, htrans⟩

end S_Deformation_HondaSystem_exists_pDivisibleTower_dieudonneModule_of_range_pow_le
end P2MW
export P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_dieudonneModule_of_range_pow_le (solution)
