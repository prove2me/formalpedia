-- Prove2me | solution 1 for Deformation.exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_forall_ker_eq_torsionIdeal_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/d76a45f0-b506-5d7a-9431-42668f65658e

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_Deformation_exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit
import Theorems.Thm_Deformation_DieudonneModule_exists_mem_fontaineHodge_map_eq_of_isLocalRing_cartierDual
import Theorems.Thm_HopfAlgebra_algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual
import Theorems.Thm_PDivisibleGroup_exists_connectedComponent_mvFormalGroup_of_isLocalRing_cartierDual
import Theorems.Thm_HopfAlgebra_exists_formallyEtale_bialgHom_faithfullyFlat_ker_eq_map_ker_counit_zmodp
import Theorems.Thm_Algebra_FormallyEtale_existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp
import Theorems.Thm_Deformation_exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_mvFormalGroup
import Theorems.Thm_MvFormalGroup_exists_rescaledLog_of_isAdicComplete
import Theorems.Thm_MvFormalGroup_exists_rescaledExp_tendsto_zero_of_isLocalRing_cartierDual
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_forall_ker_eq_torsionIdeal_zmodp
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v w

namespace S17T

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]

theorem mem_span_of_includeRight_eq_zero [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {Y : Type w} [CommRing Y] [Algebra 𝓞 Y] {y : Y}
    (hy : (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y) y = 0) :
    y ∈ Ideal.span {(p : Y)} := by
  have hsurj : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  let e : (𝓞 ⧸ RingHom.ker (algebraMap 𝓞 (ZMod p))) ≃ₐ[𝓞] ZMod p :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId 𝓞 (ZMod p)) hsurj
  let q : 𝓞 →ₐ[𝓞] Y ⧸ Ideal.span {(p : Y)} :=
    (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {(p : Y)})).comp (Algebra.ofId 𝓞 Y)
  have hq : ∀ a ∈ RingHom.ker (algebraMap 𝓞 (ZMod p)), q a = 0 := by
    intro a ha
    rw [hker] at ha
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    show Ideal.Quotient.mk _ (algebraMap 𝓞 Y (t * p)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  let f₀ : (𝓞 ⧸ RingHom.ker (algebraMap 𝓞 (ZMod p))) →ₐ[𝓞] Y ⧸ Ideal.span {(p : Y)} :=
    Ideal.Quotient.liftₐ _ q hq
  let f : ZMod p →ₐ[𝓞] Y ⧸ Ideal.span {(p : Y)} := f₀.comp (e.symm : ZMod p →ₐ[𝓞] _)
  let g : TensorProduct 𝓞 (ZMod p) Y →ₐ[𝓞] Y ⧸ Ideal.span {(p : Y)} :=
    Algebra.TensorProduct.lift f (Ideal.Quotient.mkₐ 𝓞 (Ideal.span {(p : Y)})) (fun _ _ => Commute.all _ _)
  have hg : g (Algebra.TensorProduct.includeRight y) = Ideal.Quotient.mk (Ideal.span {(p : Y)}) y := by
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  rw [hy, map_zero] at hg
  exact Ideal.Quotient.eq_zero_iff_mem.1 hg.symm

end S17T

namespace S17T

theorem main
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h : ℕ) (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v))
    (hunipL : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v))))
    (v : ℕ)
    (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
    (χ : TensorProduct 𝓞 (ZMod p) (L v) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) Y)
    (hχ : ∀ (n : ℕ) (m : Deformation.wittHom (ZMod p) p n (TensorProduct 𝓞 (ZMod p) (L v))),
      (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) (L v))) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight :
              L v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L v)).toRingHom →
        Deformation.TruncWitt.map χ.toRingHom
            (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) (L v))) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y).toRingHom)
 :
    ∃ x : L v →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) x = χ := by
  classical
  obtain ⟨R₀, _iCR, _iHA, _iFree, _iFin, ρ, e, he, hεe, hρ, hkerρ, hR₀loc, hR₀kloc, hR₀unip, d, F, _iComm, π,
      hπ, hπX, hπeval, hkerπ, hπΔ⟩ :=
    PDivisibleGroup.exists_connectedComponent_mvFormalGroup_of_isLocalRing_cartierDual p hp hker h L t ht
      hrankL hkerL hunipL v
  obtain ⟨H, _iCH, _iHH, _iCoH, _iFH, _iFiH, _iEt, jH, hexact, hff, hfin, hjinj, hcocomm, hrankR₀'⟩ :=
    HopfAlgebra.exists_formallyEtale_bialgHom_faithfullyFlat_ker_eq_map_ker_counit_zmodp p hp hker (L v) (v * h)
      (hrankL v) R₀ ρ e he hεe hρ hkerρ hR₀loc
  haveI : Coalgebra.IsCocomm 𝓞 R₀ := hcocomm
  have hlift3 : ∀ ψ : TensorProduct 𝓞 (ZMod p) H →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) Y,
      (∀ (n : ℕ) (m : Deformation.wittHom (ZMod p) p n (TensorProduct 𝓞 (ZMod p) H)),
        (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) H)) ∈ Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : H →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) H).toRingHom →
          Deformation.TruncWitt.map ψ.toRingHom (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) H)) ∈
            Deformation.TruncWitt.fontaineKer p n
              (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y).toRingHom) →
      ∃ x : H →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) x = ψ :=
    fun ψ _ => (Algebra.FormallyEtale.existsUnique_algHom_baseChange_eq_of_module_finite_free_zmodp
      p hp hker H Y ψ).exists
  haveI : IsAdicComplete (Ideal.span {(p : R₀)}) R₀ :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p R₀
  haveI : IsAdicComplete (Ideal.span {(p : R₀ ⊗[𝓞] R₀)}) (R₀ ⊗[𝓞] R₀) :=
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (R₀ ⊗[𝓞] R₀)
  have hk : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  obtain ⟨_iDom, _iDVR, hirr, -⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span p hp hker
  have hfree : ∀ (Y' : Type (max v w)) [CommRing Y'] [Algebra 𝓞 Y'] [Module.Finite 𝓞 Y'] [Module.Flat 𝓞 Y'],
      Module.Free 𝓞 Y' := fun Y' _ _ _ _ => Module.free_of_flat_of_isLocalRing

  have hL := fun z hz =>
    Deformation.DieudonneModule.exists_mem_fontaineHodge_map_eq_of_isLocalRing_cartierDual p hp (k := ZMod p)
      hk hker (L v) ⟨v * h, hrankL v⟩ (hunipL v) R₀ hrankR₀' ρ hρ z hz

  have hG : ∀ (Y' : Type (max v w)) [CommRing Y'] [Algebra 𝓞 Y'] [Module.Finite 𝓞 Y']
      [Module.Flat 𝓞 Y'] (y y' : L v →ₐ[𝓞] Y'),
      Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y =
        Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) y' → y = y' := by
    intro Y' _ _ _ _ y y' hyy'
    haveI : Module.Free 𝓞 Y' := hfree Y'
    refine HopfAlgebra.algHom_eq_of_forall_sub_mem_span_of_isLocalRing_cartierDual 𝓞 p hirr (ZMod p) hk hker
      (L v) ⟨v * h, hrankL v⟩ (hunipL v) Y' y y' fun a => ?_
    apply mem_span_of_includeRight_eq_zero p hker
    have := congrArg (fun f => f ((1 : ZMod p) ⊗ₜ[𝓞] a)) hyy'
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at this
    rw [map_sub, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply, this, sub_self]

  have hG₁ : ∀ (Y' : Type (max v w)) [CommRing Y'] [Algebra 𝓞 Y'] [Module.Finite 𝓞 Y']
      [Module.Flat 𝓞 Y'] (ψ : TensorProduct 𝓞 (ZMod p) R₀ →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) Y'),
      (∀ (n : ℕ) (m : Deformation.wittHom (ZMod p) p n (TensorProduct 𝓞 (ZMod p) R₀)),
        (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) R₀)) ∈ Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : R₀ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) R₀).toRingHom →
          Deformation.TruncWitt.map ψ.toRingHom (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) R₀)) ∈
            Deformation.TruncWitt.fontaineKer p n
              (Algebra.TensorProduct.includeRight : Y' →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y').toRingHom) →
      ∃ x : R₀ →ₐ[𝓞] Y', Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) x = ψ := by
    intro Y' _ _ _ _ ψ hψ
    haveI : Module.Free 𝓞 Y' := hfree Y'
    rcases Nat.eq_zero_or_pos v with hv0 | hv
    ·
      subst hv0
      haveI : Nontrivial 𝓞 := (algebraMap 𝓞 (ZMod p)).domain_nontrivial
      have hrk : Module.finrank (ZMod p) (TensorProduct 𝓞 (ZMod p) (L 0)) = 1 := by
        rw [Module.finrank_baseChange, hrankL 0]
        simp
      haveI : Nontrivial (TensorProduct 𝓞 (ZMod p) (L 0)) := Module.nontrivial_of_finrank_eq_succ hrk
      have hgen0 : ∀ z : TensorProduct 𝓞 (ZMod p) (L 0), ∃ c : ZMod p,
          c • (1 : TensorProduct 𝓞 (ZMod p) (L 0)) = z :=
        (finrank_eq_one_iff_of_nonzero' (1 : TensorProduct 𝓞 (ZMod p) (L 0)) one_ne_zero).1 hrk
      have hsurjk : Function.Surjective
          (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (ρ : L 0 →ₐ[𝓞] R₀)) :=
        Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hρ
      have hgen : ∀ z : TensorProduct 𝓞 (ZMod p) R₀, ∃ c : ZMod p, c • (1 : TensorProduct 𝓞 (ZMod p) R₀) = z := by
        intro z
        obtain ⟨z', rfl⟩ := hsurjk z
        obtain ⟨c, rfl⟩ := hgen0 z'
        exact ⟨c, by rw [map_smul, map_one]⟩
      refine ⟨(Algebra.ofId 𝓞 Y').comp (Bialgebra.counitAlgHom 𝓞 R₀), ?_⟩
      apply AlgHom.ext
      intro z
      obtain ⟨c, rfl⟩ := hgen z
      rw [map_smul, map_smul, map_one, map_one]
    · obtain ⟨Fp, φ, hFp, hFp0, hφ0, hφ1, hφT, hφF⟩ :=
        MvFormalGroup.exists_rescaledLog_of_isAdicComplete p hp F
      obtain ⟨ψψ, hψ0, hψT, hψφ, hφψ⟩ :=
        MvFormalGroup.exists_rescaledExp_tendsto_zero_of_isLocalRing_cartierDual p hp hker F Fp hFp hFp0 φ
          hφ0 hφ1 hφF v hv R₀ π hπ hπX hπeval hkerπ hπΔ hR₀unip
      exact Deformation.exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_mvFormalGroup p hp hker F Fp
        hFp hFp0 φ ψψ hφ0 hψ0 hφ1 hφT hψT hφF hψφ hφψ v R₀ π hπ hπX hπeval hkerπ hπΔ hR₀unip Y' ψ hψ

  exact Deformation.exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit p hp hk hker
    ρ hρ jH hexact hff hfin hL hG₁ hG Y hlift3 χ hχ

end S17T

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h : ℕ) (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v))
    (hunipL : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v))))
    (v : ℕ)
    (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
    (χ : TensorProduct 𝓞 (ZMod p) (L v) →ₐ[ZMod p] TensorProduct 𝓞 (ZMod p) Y)
    (hχ : ∀ (n : ℕ) (m : Deformation.wittHom (ZMod p) p n (TensorProduct 𝓞 (ZMod p) (L v))),
      (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) (L v))) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight :
              L v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L v)).toRingHom →
        Deformation.TruncWitt.map χ.toRingHom
            (m : TruncatedWittVector p n (TensorProduct 𝓞 (ZMod p) (L v))) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) Y).toRingHom) :
    ∃ x : L v →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) x = χ :=
  S17T.main p hp hker h L t ht hrankL hkerL hunipL v Y χ hχ

end S_Deformation_exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_forall_ker_eq_torsionIdeal_zmodp
end P2MW
export P2MW.S_Deformation_exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_forall_ker_eq_torsionIdeal_zmodp (solution)
