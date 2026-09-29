-- Prove2me | solution 1 for Deformation.HondaSystem.exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/9835176c-1d07-58dc-95bb-a72c4107e26f

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_UnipotentWittCovector
import Definitions.Def_Dieudonne_FontaineFunctor
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_Deformation_SplitCoordinates
import Theorems.Thm_MvFormalGroup_exists_pDivisibleTower_of_cocycle
import Theorems.Thm_Deformation_HondaSystem_exists_bijective_tensorProduct_specialFibre_of_cocycle
import Theorems.Thm_Deformation_HondaSystem_map_apply_basis_mem_fontaineHodge_of_cocycle
import Theorems.Thm_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct
open MvPowerSeries

universe u v w

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map nthSeries nthSeries_zero nthSeries_succ mk toPowerSeries constantCoeff_nthSeries adicEval exists_pDivisibleTower_of_cocycle"
p2m_open "MvFormalGroup"

variable {g : ℕ} {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem toPowerSeries_injective_bmix :
    Function.Injective (MvFormalGroup.toPowerSeries : MvFormalGroup g R → _) := by
  rintro ⟨a, _, _, _, _⟩ ⟨b, _, _, _, _⟩ h
  congr

@[scoped simp] theorem toPowerSeries_map_bmix (f : R →+* S) (F : MvFormalGroup g R) (i : Fin g) :
    (F.map f).toPowerSeries i = MvPowerSeries.map f (F.toPowerSeries i) := rfl

theorem map_map_bmix (f : R →+* S) (h : S →+* T) (F : MvFormalGroup g R) :
    (F.map f).map h = F.map (h.comp f) :=
  toPowerSeries_injective_bmix (funext fun i => by
    simp only [toPowerSeries_map_bmix, MvPowerSeries.map_map])

theorem nthSeries_map_bmix (f : R →+* S) (F : MvFormalGroup g R) (n : ℕ) (i : Fin g) :
    (F.map f).nthSeries n i = MvPowerSeries.map f (F.nthSeries n i) := by
  induction n generalizing i with
  | zero => simp [nthSeries_zero]
  | succ n ih =>
    rw [nthSeries_succ, nthSeries_succ]
    have hsub : HasSubst (Sum.elim (F.nthSeries n) fun j => (X j : MvPowerSeries (Fin g) R)) :=
      hasSubst_of_constantCoeff_zero (by
        rintro (j | j)
        · exact constantCoeff_nthSeries F n j
        · exact constantCoeff_X j)
    change subst (Sum.elim ((F.map f).nthSeries n) fun j => X j) (MvPowerSeries.map f (F.toPowerSeries i)) =
      MvPowerSeries.map f (subst (Sum.elim (F.nthSeries n) fun j => X j) (F.toPowerSeries i))
    rw [map_subst hsub]
    congr 1
    funext s
    rcases s with j | j
    · exact ih j
    · simp [map_X]

end MvFormalGroup
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle.MvFormalGroup"

namespace Deformation
p2m_export "Deformation" "HondaSystem DieudonneModule DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map fontaineHodge PLoc.wSeries HondaSystem.SplitCoordinates HondaSystem.exists_bijective_tensorProduct_specialFibre_of_cocycle HondaSystem.map_apply_basis_mem_fontaineHodge_of_cocycle"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk L SplitCoordinates exists_bijective_tensorProduct_specialFibre_of_cocycle map_apply_basis_mem_fontaineHodge_of_cocycle"
namespace BMix
p2m_open "Deformation.HondaSystem Deformation"

open scoped TensorProduct
open MvPowerSeries Function

section Frame

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]

theorem isMaximal_span (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] : (Ideal.span {(p : 𝓞)}).IsMaximal := by
  obtain ⟨_, _, -, hmax⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_ker_algebraMap_zmod_eq_span p hp hker
  rw [← hmax]
  exact IsLocalRing.maximalIdeal.isMaximal 𝓞

theorem exists_int_sub_mem_span_pow [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) (v : ℕ) (c : 𝓞) :
    ∃ n : ℤ, c - n ∈ Ideal.span {(p : 𝓞) ^ v} := by
  induction v with
  | zero => exact ⟨0, by simp⟩
  | succ V ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hN
    have hy' : y - ((algebraMap 𝓞 (ZMod p) y).val : 𝓞) ∈ Ideal.span {(p : 𝓞)} := by
      rw [← hker, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hy'
    refine ⟨N + (p : ℤ) ^ V * ((algebraMap 𝓞 (ZMod p) y).val : ℤ),
      Ideal.mem_span_singleton'.mpr ⟨t, ?_⟩⟩
    push_cast
    linear_combination (p : 𝓞) ^ V * ht + hy

end Frame
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle.MvFormalGroup"

section Height

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
  (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
  (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
  (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
  (𝒮 : SplitCoordinates p r H₁ G s π)

noncomputable def residueEquiv (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) :
    𝓞 ⧸ Ideal.span {(p : 𝓞)} ≃+* ZMod p :=
  (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (algebraMap 𝓞 (ZMod p))))

theorem residueEquiv_mk (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) (c : 𝓞) :
    residueEquiv p hker (Ideal.Quotient.mk _ c) = algebraMap 𝓞 (ZMod p) c := by
  simp [residueEquiv, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem residueEquiv_comp_mk (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) :
    (residueEquiv p hker).toRingHom.comp (Ideal.Quotient.mk _) = algebraMap 𝓞 (ZMod p) :=
  RingHom.ext fun c => residueEquiv_mk p hker c

private noncomputable def _root_.MvPowerSeries.mapRingEquiv {σ : Type*} {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : MvPowerSeries σ A ≃+* MvPowerSeries σ B :=
  RingEquiv.ofRingHom (MvPowerSeries.map e.toRingHom) (MvPowerSeries.map e.symm.toRingHom)
    (by rw [← MvPowerSeries.map_comp, RingEquiv.toRingHom_comp_symm_toRingHom, MvPowerSeries.map_id])
    (by rw [← MvPowerSeries.map_comp, RingEquiv.symm_toRingHom_comp_toRingHom, MvPowerSeries.map_id])

p2m_alias "P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle.MvPowerSeries.mapRingEquiv" "MvPowerSeries.mapRingEquiv"

theorem finrank_quot_nthSeries_map_eq_pow_hc
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (hℒ : 𝒮.Lawful) (Φ : MvFormalGroup 𝒮.d 𝓞) (hΦ : Φ.map (algebraMap 𝓞 (ZMod p)) = 𝒮.Φ₀) :
    Module.finrank (𝓞 ⧸ Ideal.span {(p : 𝓞)})
      (MvPowerSeries (Fin 𝒮.d) (𝓞 ⧸ Ideal.span {(p : 𝓞)}) ⧸
        Ideal.span (Set.range ((Φ.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))).nthSeries p))) =
      p ^ 𝒮.hc := by
  classical
  set K₀ := 𝓞 ⧸ Ideal.span {(p : 𝓞)}
  set i : K₀ ≃+* ZMod p := residueEquiv p hker with hi
  set J₀ : MvPowerSeries (Fin 𝒮.d) K₀ ≃+* MvPowerSeries (Fin 𝒮.d) (ZMod p) :=
    MvPowerSeries.mapRingEquiv i with hJ₀
  set I₀ : Ideal (MvPowerSeries (Fin 𝒮.d) K₀) :=
    Ideal.span (Set.range ((Φ.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))).nthSeries p)) with hI₀
  set I₁ : Ideal (MvPowerSeries (Fin 𝒮.d) (ZMod p)) := Ideal.span (Set.range (𝒮.Φ₀.nthSeries p)) with hI₁
  have hJ₀apply : ∀ f, J₀ f = MvPowerSeries.map i.toRingHom f := fun f => rfl
  have hΦ₀ : (Φ.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))).map i.toRingHom = 𝒮.Φ₀ := by
    rw [MvFormalGroup.map_map_bmix, residueEquiv_comp_mk, hΦ]
  have hIJ : I₁ = I₀.map (J₀ : MvPowerSeries (Fin 𝒮.d) K₀ →+* MvPowerSeries (Fin 𝒮.d) (ZMod p)) := by
    rw [hI₀, hI₁, Ideal.map_span, ← Set.range_comp]
    congr 2
    funext k
    change 𝒮.Φ₀.nthSeries p k = J₀ ((Φ.map (Ideal.Quotient.mk _)).nthSeries p k)
    rw [hJ₀apply, ← MvFormalGroup.nthSeries_map_bmix, hΦ₀]
  have key := Algebra.finrank_eq_of_equiv_equiv (R₀ := K₀) (S₀ := MvPowerSeries (Fin 𝒮.d) K₀ ⧸ I₀)
    (R₁ := ZMod p) (S₁ := MvPowerSeries (Fin 𝒮.d) (ZMod p) ⧸ I₁) i (Ideal.quotientEquiv I₀ I₁ J₀ hIJ)
    (by
      refine RingHom.ext fun x => ?_
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        Ideal.quotientEquiv_apply, RingHom.toFun_eq_coe]
      change Ideal.Quotient.mk I₁ (algebraMap (ZMod p) (MvPowerSeries (Fin 𝒮.d) (ZMod p)) (i _)) =
        Ideal.quotientMap I₁ (J₀ : MvPowerSeries (Fin 𝒮.d) K₀ →+* MvPowerSeries (Fin 𝒮.d) (ZMod p)) _
          (Ideal.Quotient.mk I₀ (algebraMap K₀ (MvPowerSeries (Fin 𝒮.d) K₀) _))
      rw [Ideal.quotientMap_mk, MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply,
        Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply, RingEquiv.coe_toRingHom, hJ₀apply,
        MvPowerSeries.map_C]
      rfl)
  rw [key, hI₁, hℒ.finrank_quot_nthSeries]

end Height
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle.MvFormalGroup"

section Basis

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
  (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
  (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
  (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
  (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
  (𝒮 : SplitCoordinates p r H₁ G s π)

theorem forall_mem_of_basis
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (hπker : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    {B : ℕ → Type*} [∀ v, CommRing (B v)] [∀ v, Bialgebra (ZMod p) (B v)]
    (e : ∀ v, G v →ₐc[ZMod p] B v) (N : ∀ v, Submodule ℤ (Deformation.DieudonneModule (ZMod p) p (B v)))
    (hbasis : ∀ v i, Deformation.DieudonneModule.map (ZMod p) p (e v) (π v ((𝒮.α i : H₁.L) : Fin r → 𝓞)) ∈ N v)
    (v : ℕ) (x : Fin r → 𝓞) (hx : x ∈ H₁.L) :
    Deformation.DieudonneModule.map (ZMod p) p (e v) (π v x) ∈ N v := by
  classical

  have hxsum : x = ∑ i, (𝒮.α.repr ⟨x, hx⟩ i) • ((𝒮.α i : H₁.L) : Fin r → 𝓞) := by
    have h := congrArg (Subtype.val : H₁.L → Fin r → 𝓞) (𝒮.α.sum_repr ⟨x, hx⟩).symm
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
  rw [hxsum, map_sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_

  obtain ⟨k, hk⟩ := exists_int_sub_mem_span_pow p hker v (𝒮.α.repr ⟨x, hx⟩ i)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hk
  have hsplit : (𝒮.α.repr ⟨x, hx⟩ i) • ((𝒮.α i : H₁.L) : Fin r → 𝓞) =
      k • ((𝒮.α i : H₁.L) : Fin r → 𝓞) + (p : 𝓞) ^ v • (c • ((𝒮.α i : H₁.L) : Fin r → 𝓞)) := by
    rw [smul_smul, ← Int.cast_smul_eq_zsmul 𝓞 k, ← add_smul, mul_comm, hc, add_sub_cancel]
  have hkill : π v ((p : 𝓞) ^ v • (c • ((𝒮.α i : H₁.L) : Fin r → 𝓞))) = 0 := (hπker v _).2 ⟨_, rfl⟩
  rw [hsplit, map_add, hkill, add_zero, map_zsmul, map_zsmul]
  exact Submodule.smul_mem _ k (hbasis v i)

end Basis
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle.MvFormalGroup"

end Deformation.HondaSystem.BMix
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle.MvFormalGroup"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle.MvFormalGroup"
p2m_reactivate "P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle.MvFormalGroup"

open scoped TensorProduct
open MvPowerSeries _root_.Deformation _root_.P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle.Deformation Deformation.HondaSystem.BMix in
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

    (𝒮 : Deformation.HondaSystem.SplitCoordinates p r H₁ G s π) (h𝒮 : 𝒮.Lawful)

    (Φ : MvFormalGroup 𝒮.d 𝓞) [Φ.IsComm] (hΦ : Φ.map (algebraMap 𝓞 (ZMod p)) = 𝒮.Φ₀)

    (c₂ : ∀ v, Fin 𝒮.d → 𝒮.Et v ⊗[𝓞] 𝒮.Et v)
    (hCOC :
      (∀ v i, Algebra.TensorProduct.map (𝒮.st v : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et v)
          (𝒮.st v : 𝒮.Et (v + 1) →ₐ[𝓞] 𝒮.Et v) (c₂ (v + 1) i) = c₂ v i) ∧
      (∀ v i, c₂ v i ∈ Ideal.span {(p : 𝒮.Et v ⊗[𝓞] 𝒮.Et v)}) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f : 𝒮.Et v →ₐ[𝓞] g) (j : Fin 𝒮.d),
          Algebra.TensorProduct.lift f ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 (𝒮.Et v))) (fun _ _ => Commute.all _ _) (c₂ v j) = 0 ∧
          Algebra.TensorProduct.lift ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 (𝒮.Et v))) f (fun _ _ => Commute.all _ _) (c₂ v j) = 0) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' : 𝒮.Et v →ₐ[𝓞] g) (j : Fin 𝒮.d),
          Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j) = Algebra.TensorProduct.lift f' f (fun _ _ => Commute.all _ _) (c₂ v j)) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' f'' : 𝒮.Et v →ₐ[𝓞] g),
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j))) ((fun j => Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v))) f'' (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)) =
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _) (c₂ v j))) ((fun j => Algebra.TensorProduct.lift f ((Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v))) (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i))))

    (hLOGA :
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' : 𝒮.Et v →ₐ[𝓞] g) (x x' : Fin 𝒮.d → g),
          (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, x' j ∈ (Ideal.span {(p : g)}).radical) → ∀ i : Fin 𝒮.d,
          Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)})
              (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim (x) ((fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim (x') ((fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)))) (Φ.toPowerSeries i)) (𝒮.a i n)) +
            Deformation.PLoc.wSeries p (fun k => ((Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (𝒮.Et v))) (𝒮.ĉ i k v)) =
          (Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x (𝒮.a i n)) +
              Deformation.PLoc.wSeries p (fun k => f (𝒮.ĉ i k v))) +
            (Deformation.PLoc.wSeries p (fun n => MvFormalGroup.adicEval (Ideal.span {(p : g)}) x' (𝒮.a i n)) +
              Deformation.PLoc.wSeries p (fun k => f' (𝒮.ĉ i k v))))) :
    ∃ (L : ℕ → Type u) (_ : ∀ v, CommRing (L v)) (_ : ∀ v, HopfAlgebra 𝓞 (L v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (L v)) (_ : ∀ v, Module.Free 𝓞 (L v))
      (_ : ∀ v, Module.Finite 𝓞 (L v)) (t : ∀ v, L (v + 1) →ₐc[𝓞] L v),
      (∀ v, Function.Surjective (t v)) ∧ (∀ v, Module.finrank 𝓞 (L v) = p ^ (v * r)) ∧
      (∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v)) ∧
    ∃ e : ∀ v, G v →ₐc[ZMod p] TensorProduct 𝓞 (ZMod p) (L v),
      (∀ v, Function.Bijective (e v)) ∧
      (∀ v, (e v).comp (s v) =
        (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t v)).comp (e (v + 1))) ∧
      (∀ v, ∀ x ∈ H₁.L, Deformation.DieudonneModule.map (ZMod p) p (e v) (π v x) ∈
        Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight :
            L v →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) (L v)).toRingHom) := by
  classical
  haveI : (Ideal.span {(p : 𝓞)}).IsMaximal := isMaximal_span p hp hker
  haveI : Nontrivial 𝓞 := (algebraMap 𝓞 (ZMod p)).domain_nontrivial
  haveI hEtco : ∀ v, Coalgebra.IsCocomm 𝓞 (𝒮.Et v) := h𝒮.isCocomm_Et
  haveI hEtfr : ∀ v, Module.Free 𝓞 (𝒮.Et v) := h𝒮.free_Et
  haveI hEtfi : ∀ v, Module.Finite 𝓞 (𝒮.Et v) := h𝒮.finite_Et
  obtain ⟨hc₂st, hc₂p, hc₂unit, hc₂symm, hc₂coc⟩ := hCOC

  have hrankEt : ∀ v, Module.finrank 𝓞 (𝒮.Et v) = p ^ (v * 𝒮.he) := fun v => by
    have e : (ZMod p ⊗[𝓞] 𝒮.Et v) ≃ₗ[ZMod p] 𝒮.Ge v :=
      LinearEquiv.ofBijective (𝒮.θe v : ZMod p ⊗[𝓞] 𝒮.Et v →ₐ[ZMod p] 𝒮.Ge v).toLinearMap
        (h𝒮.θe_bijective v)
    have h := e.finrank_eq
    rw [Module.finrank_baseChange, h𝒮.finrank_Ge] at h
    exact h

  obtain ⟨L, _, _, _, _, _, t, ι, Ψ, hT1, hT2, hT3, hI1, hP1, hP2, hP3, hP4, hP5, hG1, hC1⟩ :=
    MvFormalGroup.exists_pDivisibleTower_of_cocycle p hp Φ 𝒮.hc
      (finrank_quot_nthSeries_map_eq_pow_hc p r H₁ G s π 𝒮 hker h𝒮 Φ hΦ) 𝒮.he 𝒮.Et 𝒮.st
      h𝒮.st_surjective hrankEt h𝒮.ker_st c₂ ⟨hc₂st, hc₂p, hc₂unit, hc₂symm, hc₂coc⟩

  obtain ⟨ee, heebij, heeκ, heeθ, heecomp⟩ :=
    Deformation.HondaSystem.exists_bijective_tensorProduct_specialFibre_of_cocycle p hp hker r H₁ G s π
      𝒮 h𝒮 Φ hΦ c₂ hc₂p L t ι Ψ hT2 hI1 hP1 hP4 hP5 hG1 hC1

  obtain ⟨-, -, -, -, -, hkill, -⟩ :=
    PDivisibleGroup.Hopf.exists_forall_comp_transition_surjective_ker_eq_torsionIdeal p (𝒮.hc + 𝒮.he) L t
      hT1 hT2 hT3
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, t, hT1,
    fun v => by rw [hT2, h𝒮.hc_add_he], hT3, fun v => (ee v).comp (𝒮.Θ v),
    fun v => (heebij v).comp (h𝒮.Θ_bijective v), fun v => ?_, fun v x hx => ?_⟩
  ·
    rw [BialgHom.comp_assoc, h𝒮.Θ_comp_s, ← BialgHom.comp_assoc, heecomp, BialgHom.comp_assoc]
  ·
    exact forall_mem_of_basis p r H₁ G s π 𝒮 hker hπker (fun v => (ee v).comp (𝒮.Θ v))
      (fun v => Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : L v →ₐ[𝓞] ZMod p ⊗[𝓞] L v).toRingHom)
      (fun v i => Deformation.HondaSystem.map_apply_basis_mem_fontaineHodge_of_cocycle p hp hker r H₁ G s π
        𝒮 h𝒮 Φ c₂ hc₂p hLOGA v (L v) (ι v) (Ψ v) (hP2 v) (hP3 v) (hP4 v) (hC1 v) (hkill v) (ee v)
        (heeκ v) (heeθ v) i) v x hx

end S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle
end P2MW
export P2MW.S_Deformation_HondaSystem_exists_pDivisibleTower_bijective_map_mem_fontaineHodge_of_splitCoordinates_of_cocycle (solution)
