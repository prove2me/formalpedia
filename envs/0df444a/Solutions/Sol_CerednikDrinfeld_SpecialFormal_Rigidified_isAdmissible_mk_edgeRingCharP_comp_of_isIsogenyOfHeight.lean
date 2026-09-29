-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.isAdmissible_mk_edgeRingCharP_comp_of_isIsogenyOfHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e501378d-214e-5286-a57d-c2c1526223d4

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants

import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp
import Theorems.Thm_WittVector_nonempty_ringEquiv_quotient_pIdeal_of_perfectRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isAdmissible_mk_edgeRingCharP_comp_of_isIsogenyOfHeight
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

namespace B37ADM

variable (p : ℕ) [Fact p.Prime]

theorem isField_quot (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    IsField (WittVector p k ⧸ pIdeal p (WittVector p k)) := by
  obtain ⟨e⟩ := WittVector.nonempty_ringEquiv_quotient_pIdeal_of_perfectRing p k
  exact MulEquiv.isField (Field.toIsField k) e.symm.toMulEquiv

@[reducible] noncomputable def fieldQuot (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    Field (WittVector p k ⧸ pIdeal p (WittVector p k)) :=
  (isField_quot p k).toField

scoped instance isNoetherianRing_edgeRingCharP (k : Type) [CommRing k] [IsNoetherianRing k] :
    IsNoetherianRing (EdgeFamily.edgeRingCharP p k) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (FormalOmega.edgeQuot.discr k (0 : k) p)) _
    (show IsNoetherianRing (MvPolynomial (Fin 2) k ⧸ Ideal.span {FormalOmega.edgeRel k (0 : k)}) from inferInstance)

section adm

variable (k : Type) [Field k] [CharP k p] [PerfectRing k p]

noncomputable abbrev ψE : WittVector p k →+* EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)) :=
  (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp
    (Ideal.Quotient.mk (pIdeal p (WittVector p k)))

noncomputable abbrev gE : (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)) ⧸
    pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))) :=
  (Ideal.Quotient.mk _).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) _)

omit [CharP k p] [PerfectRing k p] in
theorem residueMap_ψE : residueMap (p := p) (ψE p k) = gE p k := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  rfl

theorem admissible (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (f₀ : EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (hXs : X.IsSpecial (structureMap ι (ψE p k))) (hX4 : X.HasHeight 4)
    (m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m))
    (ρ₁ : Series (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (hρ₁ : FormalODModule.IsIsogenyOfHeight ((X.map f₀).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) _)) X ρ₁ 4) :
    (Rigidified.mk (Φ := Φ) X (m + 1)
      ((ρ₁.map (Ideal.Quotient.mk (pIdeal p _))).comp (ρ₀.map (gE p k)))).IsAdmissible ι (ψE p k) := by
  letI : Field (WittVector p k ⧸ pIdeal p (WittVector p k)) := fieldQuot p k
  refine ⟨hXs, hX4, ?_⟩
  show FormalODModule.IsIsogenyOfHeight (Φ.map (residueMap (ψE p k))) (X.map (Ideal.Quotient.mk (pIdeal p _)))
    ((ρ₁.map (Ideal.Quotient.mk (pIdeal p _))).comp (ρ₀.map (gE p k))) (4 * (m + 1))
  rw [residueMap_ψE]
  have h1 : FormalODModule.IsODHom ((X.map f₀).map (gE p k)) (X.map (Ideal.Quotient.mk (pIdeal p _)))
      (ρ₁.map (Ideal.Quotient.mk (pIdeal p _))) := by
    have h := hρ₁.1.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))
    rw [FormalODModule.map_map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) _)
      (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) (X.map f₀)] at h
    exact h
  refine ⟨h1.comp (hρ₀.1.map (gE p k)), ?_⟩
  have d0 : FormalODModule.HasKernelOfDegree (ρ₀.map (gE p k)) (p ^ (4 * m)) :=
    CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map (gE p k) ρ₀ hρ₀.1.1.1 hρ₀.2
  have d1 : FormalODModule.HasKernelOfDegree (ρ₁.map (Ideal.Quotient.mk (pIdeal p _))) (p ^ 4) :=
    CerednikDrinfeld.FormalODModule.hasKernelOfDegree_map _ ρ₁ hρ₁.1.1.1 hρ₁.2
  rw [show p ^ (4 * (m + 1)) = p ^ (4 * m) * p ^ 4 by ring]
  exact CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp (hρ₀.1.map (gE p k)).1.1 h1.1.1 d0 d1

end adm

end B37ADM
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isAdmissible_mk_edgeRingCharP_comp_of_isIsogenyOfHeight.B37ADM"

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (X : FormalODModule p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (hXs : X.IsSpecial (structureMap ι ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))))) (hX4 : X.HasHeight 4)
    (f₀ : (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))) →+* (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (m : ℕ) (ρ₀ : Series (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hρ₀ : FormalODModule.IsIsogenyOfHeight Φ (X.map f₀) ρ₀ (4 * m))
    (ρ₁ : Series (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))
    (hρ₁ : FormalODModule.IsIsogenyOfHeight ((X.map f₀).map (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))) X ρ₁ 4) :
    (Rigidified.mk (Φ := Φ) X (m + 1)
      ((ρ₁.map (Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))).comp
        (ρ₀.map ((Ideal.Quotient.mk (pIdeal p (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k))))).comp (algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))))))).IsAdmissible ι
      ((algebraMap (WittVector p k ⧸ pIdeal p (WittVector p k)) (EdgeFamily.edgeRingCharP p (WittVector p k ⧸ pIdeal p (WittVector p k)))).comp (Ideal.Quotient.mk (pIdeal p (WittVector p k)))) := by
  haveI : PerfectRing k p := IsAlgClosed.perfectRing k p
  exact B37ADM.admissible p k ι Φ f₀ X hXs hX4 m ρ₀ hρ₀ ρ₁ hρ₁

end S_CerednikDrinfeld_SpecialFormal_Rigidified_isAdmissible_mk_edgeRingCharP_comp_of_isIsogenyOfHeight
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isAdmissible_mk_edgeRingCharP_comp_of_isIsogenyOfHeight (solution)
