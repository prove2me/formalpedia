-- Prove2me | solution 1 for Deformation.HondaSystem.finrank_eq_of_isCompl_of_bijective_tensorProduct_comul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/afd7f686-66fa-5e38-9cfe-bd345215657b

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_Deformation_DieudonneModule_bijective_prod_map_of_bijective_tensorProduct_comul
import Theorems.Thm_Deformation_HondaSystem_map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct
import Theorems.Thm_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
import Theorems.Thm_HopfAlgebra_isLocalRing_cartierDual_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_finrank_eq_of_isCompl_of_bijective_tensorProduct_comul
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

open scoped TensorProduct
open MvPowerSeries

universe u v

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

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
    (hc : ℕ)
    (Gc : ℕ → Type v) [∀ v, CommRing (Gc v)] [∀ v, HopfAlgebra (ZMod p) (Gc v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (Gc v)] [∀ v, Module.Finite (ZMod p) (Gc v)]
    (Ge : ℕ → Type v) [∀ v, CommRing (Ge v)] [∀ v, HopfAlgebra (ZMod p) (Ge v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (Ge v)] [∀ v, Module.Finite (ZMod p) (Ge v)]
    (sc : ∀ v, Gc (v + 1) →ₐc[ZMod p] Gc v)
    (qc : ∀ v, G v →ₐc[ZMod p] Gc v) (πe : ∀ v, G v →ₐc[ZMod p] Ge v)
    (Θ : ∀ v, G v →ₐc[ZMod p] Gc v ⊗[ZMod p] Ge v)
    (hGc : ∀ v, IsLocalRing (Gc v)) (hGe : ∀ v, IsReduced (Ge v))
    (hsc : ∀ v, Function.Surjective (sc v))
    (hrankGc : ∀ v, Module.finrank (ZMod p) (Gc v) = p ^ (v * hc))
    (hkerGc : ∀ v, RingHom.ker (sc v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Gc (v + 1)) (p ^ v))
    (hqc : ∀ v, Function.Surjective (qc v))
    (hΘ : ∀ v, Function.Bijective (Θ v))
    (hΘapply : ∀ v b, Θ v b = Algebra.TensorProduct.map (qc v : G v →ₐ[ZMod p] Gc v)
      (πe v : G v →ₐ[ZMod p] Ge v) (Coalgebra.comul (R := ZMod p) b))
    (hqcs : ∀ v, (qc v).comp (s v) = (sc v).comp (qc (v + 1)))
    (Mc Met : Submodule 𝓞 (Fin r → 𝓞)) (hMcMet : IsCompl Mc Met) (hfree : Module.Free 𝓞 Mc)
    (hMet : ∀ m, m ∈ Met ↔ ∀ N : ℕ, ∃ y, (H₁.F ^ N) y = m)
    (hMc : ∀ m, m ∈ Mc ↔ ∀ k : ℕ, ∃ N : ℕ, ∃ y, (H₁.F ^ N) m = (p : 𝓞) ^ k • y) :
    Module.finrank 𝓞 Mc = hc := by
  classical
  haveI : Nontrivial 𝓞 := (algebraMap 𝓞 (ZMod p)).domain_nontrivial
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le

  have hunipGc : IsLocalRing (CartierDual (ZMod p) (Gc 1)) :=
    HopfAlgebra.isLocalRing_cartierDual_of_surjective (ZMod p) (G 1) (Gc 1) (qc 1) (hqc 1) (hunipG 1)
  obtain ⟨Lc, hLc1, hLc2⟩ :=
    Deformation.DieudonneModule.exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
      (ZMod p) p (Gc 1) hunipGc
  have hLc : Lc = hc := by
    have h : p ^ Lc = p ^ hc := by rw [← hLc1, hrankGc 1, one_mul]
    exact Nat.pow_right_injective hp2 h
  rw [Nat.card_zmod, hLc] at hLc2

  have hHA := Deformation.DieudonneModule.bijective_prod_map_of_bijective_tensorProduct_comul p (G 1) (Gc 1) (Ge 1)
    (qc 1) (πe 1) (Θ 1) (hΘ 1) (hΘapply 1)
  obtain ⟨hS4c, hS4e⟩ :=
    Deformation.HondaSystem.map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct p hp hker r H₁ G s π hπ hπker
      hπF hπs 1 (Gc 1) (Ge 1) (qc 1) (πe 1) (Θ 1) (hΘ 1) (hΘapply 1) (hGc 1) (hGe 1) Mc Met hMet hMc

  set φ : Mc →+ Deformation.DieudonneModule (ZMod p) p (Gc 1) :=
    (Deformation.DieudonneModule.map (ZMod p) p (qc 1)).comp ((π 1).comp Mc.subtype.toAddMonoidHom) with hφ
  have hφapply : ∀ m : Mc, φ m = Deformation.DieudonneModule.map (ZMod p) p (qc 1) (π 1 (m : Fin r → 𝓞)) :=
    fun m => rfl
  have hdec : ∀ x : Fin r → 𝓞, ∃ mc ∈ Mc, ∃ met ∈ Met, x = mc + met := fun x => by
    have hx : x ∈ Mc ⊔ Met := by rw [hMcMet.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨mc, hmc, met, hmet, h⟩ := Submodule.mem_sup.1 hx
    exact ⟨mc, hmc, met, hmet, h.symm⟩
  have hφsurj : Function.Surjective φ := by
    intro w
    obtain ⟨z, hz⟩ := hHA.2 (w, 0)
    obtain ⟨x, rfl⟩ := hπ 1 z
    obtain ⟨mc, hmc, met, hmet, hx⟩ := hdec x
    refine ⟨⟨mc, hmc⟩, ?_⟩
    have h1 : Deformation.DieudonneModule.map (ZMod p) p (qc 1) (π 1 x) = w := congrArg Prod.fst hz
    rw [hx, map_add, map_add, hS4e met hmet, add_zero] at h1
    rw [hφapply]
    exact h1
  have hpvec : ∀ y : Fin r → 𝓞, (p : 𝓞) • y = 0 → y = 0 := fun y hy => by
    funext i
    have hi : (p : 𝓞) * y i = 0 := by simpa using congrFun hy i
    exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hp).1 hi
  have hφker : ∀ m : Mc, φ m = 0 ↔ ∃ y : Mc, m = (p : 𝓞) • y := by
    intro m
    constructor
    · intro hm
      have h0 : π 1 (m : Fin r → 𝓞) = 0 := by
        apply hHA.1
        change (_, _) = (_, _)
        rw [← hφapply, hm, hS4c _ m.2, map_zero, map_zero]
      obtain ⟨y, hy⟩ := (hπker 1 _).1 h0
      rw [pow_one] at hy
      obtain ⟨yc, hyc, ye, hye, hyce⟩ := hdec y
      have hpye : (p : 𝓞) • ye ∈ Mc ⊓ Met := by
        refine Submodule.mem_inf.2 ⟨?_, Met.smul_mem _ hye⟩
        have h' : (p : 𝓞) • ye = (m : Fin r → 𝓞) - (p : 𝓞) • yc := by
          rw [hy, hyce, smul_add]; abel
        rw [h']
        exact Mc.sub_mem m.2 (Mc.smul_mem _ hyc)
      rw [hMcMet.inf_eq_bot, Submodule.mem_bot] at hpye
      have hye0 : ye = 0 := hpvec ye hpye
      refine ⟨⟨yc, hyc⟩, Subtype.ext ?_⟩
      rw [Submodule.coe_smul, hy, hyce, hye0, add_zero]
    · rintro ⟨y, rfl⟩
      rw [hφapply, Submodule.coe_smul, (hπker 1 _).2 ⟨(y : Fin r → 𝓞), by rw [pow_one]⟩, map_zero]

  haveI : Module.Finite 𝓞 Mc :=
    Module.Finite.of_surjective (Mc.projectionOnto Met hMcMet) fun m =>
      ⟨(m : Fin r → 𝓞), Submodule.projectionOnto_apply_left hMcMet m⟩
  set n : ℕ := Module.finrank 𝓞 Mc with hn
  let b : Module.Basis (Fin n) 𝓞 Mc := Module.finBasis 𝓞 Mc
  let ψ : Mc →+ (Fin n → ZMod p) :=
    { toFun := fun m i => algebraMap 𝓞 (ZMod p) (b.repr m i)
      map_zero' := by funext i; simp
      map_add' := fun x y => by funext i; simp }
  have hψapply : ∀ (m : Mc) (i : Fin n), ψ m i = algebraMap 𝓞 (ZMod p) (b.repr m i) := fun m i => rfl
  have hk : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  have hψsurj : Function.Surjective ψ := by
    intro c
    choose d hd using fun i => hk (c i)
    refine ⟨b.equivFun.symm d, funext fun i => ?_⟩
    rw [hψapply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hd]
  have hψker : ∀ m : Mc, ψ m = 0 ↔ ∃ y : Mc, m = (p : 𝓞) • y := by
    intro m
    constructor
    · intro hm
      have hmi : ∀ i, ∃ c : 𝓞, c * (p : 𝓞) = b.repr m i := fun i => by
        have h : b.repr m i ∈ RingHom.ker (algebraMap 𝓞 (ZMod p)) := by
          rw [RingHom.mem_ker, ← hψapply, hm]; rfl
        rw [hker] at h
        exact Ideal.mem_span_singleton'.1 h
      choose c hc using hmi
      refine ⟨b.equivFun.symm c, b.equivFun.injective (funext fun i => ?_)⟩
      rw [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_apply,
        ← hc i, mul_comm]
    · rintro ⟨y, rfl⟩
      funext i
      rw [hψapply, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.zero_apply]
      have h0 : algebraMap 𝓞 (ZMod p) (p : 𝓞) = 0 := by
        rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self _
      rw [h0, zero_mul]

  have hkereq : φ.ker = ψ.ker := by
    ext m
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, hφker, hψker]
  have e1 := QuotientAddGroup.quotientKerEquivOfSurjective φ hφsurj
  have e2 := QuotientAddGroup.quotientKerEquivOfSurjective ψ hψsurj
  have e3 : Mc ⧸ φ.ker ≃+ Mc ⧸ ψ.ker := QuotientAddGroup.quotientAddEquivOfEq hkereq
  have hcard : Nat.card (Deformation.DieudonneModule (ZMod p) p (Gc 1)) = Nat.card (Fin n → ZMod p) :=
    Nat.card_congr (e1.symm.toEquiv.trans (e3.toEquiv.trans e2.toEquiv))
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin, hLc2] at hcard
  exact (Nat.pow_right_injective hp2 hcard).symm

end S_Deformation_HondaSystem_finrank_eq_of_isCompl_of_bijective_tensorProduct_comul
end P2MW
export P2MW.S_Deformation_HondaSystem_finrank_eq_of_isCompl_of_bijective_tensorProduct_comul (solution)
