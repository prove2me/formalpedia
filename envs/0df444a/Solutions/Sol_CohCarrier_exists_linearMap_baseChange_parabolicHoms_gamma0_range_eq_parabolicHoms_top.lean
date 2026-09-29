-- Prove2me | solution 1 for CohCarrier.exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/2d2b3652-94b9-5113-a1f2-3fda26d957e3

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PDPairing
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_ModularCurve_PDPairing_heckeT0_apply_eq_heckeT_top_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CongruenceSubgroup ModularCurve.Period

namespace CohCarrier
p2m_export "CohCarrier" "coresAdd coresAdd_smul GammaH mem_GammaH_iff GammaH_le_Gamma0 GammaH_top H1 conjL heckeT heckeT_comp_coeff"
namespace ParabolicBridge
p2m_open "CohCarrier"

variable (N : ℕ)

def jTop : ↥(CohCarrier.GammaH N ⊤) →* ↥(Gamma0 N) :=
  Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 ⊤)

@[scoped simp] theorem coe_jTop (γ : ↥(CohCarrier.GammaH N ⊤)) : ((jTop N γ : ↥(Gamma0 N)) : SL(2, ℤ)) = γ := rfl

theorem jTop_apply (γ : ↥(CohCarrier.GammaH N ⊤)) :
    jTop N γ = ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩ := rfl

theorem jTop_bijective : Function.Bijective (jTop N) := by
  refine ⟨Subgroup.inclusion_injective _, fun δ => ?_⟩
  refine ⟨⟨(δ : SL(2, ℤ)), CohCarrier.mem_GammaH_iff.mpr ⟨δ.2, Subgroup.mem_top _⟩⟩, Subtype.ext rfl⟩

noncomputable def eTop : ↥(CohCarrier.GammaH N ⊤) ≃* ↥(Gamma0 N) :=
  MulEquiv.ofBijective (jTop N) (jTop_bijective N)

@[scoped simp] theorem coe_eTop_symm (δ : ↥(Gamma0 N)) : (((eTop N).symm δ : ↥(CohCarrier.GammaH N ⊤)) : SL(2, ℤ)) = δ := by
  have h' : jTop N ((eTop N).symm δ) = δ := MulEquiv.apply_symm_apply (eTop N) δ
  exact congrArg Subtype.val h'

section Transport

variable (R : Type*) [Semiring R] (A : Type*) [AddCommGroup A] [Module R A]

def τ : (Additive ↥(Gamma0 N) →+ A) →ₗ[R] (Additive ↥(CohCarrier.GammaH N ⊤) →+ A) where
  toFun ψ := ψ.comp (MonoidHom.toAdditive (jTop N))
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

variable {R A}

@[scoped simp] theorem τ_apply (ψ : Additive ↥(Gamma0 N) →+ A) (γ : ↥(CohCarrier.GammaH N ⊤)) :
    τ N R A ψ (Additive.ofMul γ) = ψ (Additive.ofMul (jTop N γ)) := rfl

noncomputable def τinv (φ : Additive ↥(CohCarrier.GammaH N ⊤) →+ A) : Additive ↥(Gamma0 N) →+ A :=
  φ.comp (MonoidHom.toAdditive (eTop N).symm.toMonoidHom)

theorem τ_τinv (φ : Additive ↥(CohCarrier.GammaH N ⊤) →+ A) : τ N R A (τinv N φ) = φ := by
  ext a
  change φ (Additive.ofMul ((eTop N).symm (jTop N (Additive.toMul a)))) = φ a
  have : (eTop N).symm (jTop N (Additive.toMul a)) = Additive.toMul a :=
    (eTop N).symm_apply_apply (Additive.toMul a)
  rw [this]
  rfl

theorem τ_injective : Function.Injective (τ N R A) := by
  intro ψ ψ' h
  ext d
  obtain ⟨γ, hγ⟩ := (jTop_bijective N).2 (Additive.toMul d)
  have := congrArg (fun f => f (Additive.ofMul γ)) h
  simp only [τ_apply, hγ] at this
  exact this

theorem isParabolicHom_τ_iff (ψ : Additive ↥(Gamma0 N) →+ A) :
    IsParabolicHom (CohCarrier.GammaH N ⊤) (τ N R A ψ) ↔ IsParabolicHom (Gamma0 N) ψ := by
  constructor
  · intro h δ hδ
    obtain ⟨γ, rfl⟩ := (jTop_bijective N).2 δ
    exact h γ hδ
  · intro h γ hγ
    exact h (jTop N γ) hγ

theorem τ_mem_parabolicHoms_iff (ψ : Additive ↥(Gamma0 N) →+ A) :
    τ N R A ψ ∈ parabolicHoms R (CohCarrier.GammaH N ⊤) A ↔ ψ ∈ parabolicHoms R (Gamma0 N) A :=
  isParabolicHom_τ_iff N ψ

end Transport

section Main

variable (𝒪 : Type) [CommRing 𝒪]

def L : ↥(parabolicHoms ℤ (Gamma0 N) ℤ) →ₗ[ℤ] CohCarrier.H1 N ⊤ 𝒪 where
  toFun x := (Int.castAddHom 𝒪).comp ((x : Additive ↥(Gamma0 N) →+ ℤ).comp (MonoidHom.toAdditive (jTop N)))
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem L_apply (x : ↥(parabolicHoms ℤ (Gamma0 N) ℤ)) (γ : ↥(CohCarrier.GammaH N ⊤)) :
    L N 𝒪 x (Additive.ofMul γ) = ((x : Additive ↥(Gamma0 N) →+ ℤ) (Additive.ofMul (jTop N γ)) : 𝒪) := rfl

theorem L_eq (x : ↥(parabolicHoms ℤ (Gamma0 N) ℤ)) :
    L N 𝒪 x = (Int.castAddHom 𝒪).comp (τ N ℤ ℤ (x : Additive ↥(Gamma0 N) →+ ℤ)) := rfl

theorem L_eq' (x : ↥(parabolicHoms ℤ (Gamma0 N) ℤ)) :
    L N 𝒪 x = τ N 𝒪 𝒪 ((Int.castAddHom 𝒪).comp (x : Additive ↥(Gamma0 N) →+ ℤ)) := rfl

theorem L_mem (x : ↥(parabolicHoms ℤ (Gamma0 N) ℤ)) :
    L N 𝒪 x ∈ parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 := by
  rw [L_eq', τ_mem_parabolicHoms_iff]
  intro δ hδ
  have := x.2 δ hδ
  simp [this]

noncomputable def ι : 𝒪 ⊗[ℤ] ↥(parabolicHoms ℤ (Gamma0 N) ℤ) →ₗ[𝒪] CohCarrier.H1 N ⊤ 𝒪 :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton 𝒪 (↥(parabolicHoms ℤ (Gamma0 N) ℤ) →ₗ[ℤ] CohCarrier.H1 N ⊤ 𝒪) (L N 𝒪))

theorem ι_tmul (r : 𝒪) (x : ↥(parabolicHoms ℤ (Gamma0 N) ℤ)) : ι N 𝒪 (r ⊗ₜ[ℤ] x) = r • L N 𝒪 x := by
  simp [ι]

theorem range_ι : LinearMap.range (ι N 𝒪) = Submodule.span 𝒪 (Set.range (L N 𝒪)) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [ι_tmul]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨x, rfl⟩)
    | add v w hv hw =>
      rw [map_add]
      exact Submodule.add_mem _ hv hw
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by rw [ι_tmul, one_smul]⟩

variable [IsAddTorsionFree 𝒪]

def Φ : ↥(parabolicHoms 𝒪 (Gamma0 N) 𝒪) →ₗ[𝒪] CohCarrier.H1 N ⊤ 𝒪 :=
  (τ N 𝒪 𝒪).comp (parabolicHoms 𝒪 (Gamma0 N) 𝒪).subtype

omit [IsAddTorsionFree 𝒪] in
theorem Φ_injective : Function.Injective (Φ N 𝒪) :=
  (τ_injective N (R := 𝒪) (A := 𝒪)).comp Subtype.val_injective

omit [IsAddTorsionFree 𝒪] in
theorem parabolicHoms_top_le_range_Φ :
    parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 ≤ LinearMap.range (Φ N 𝒪) := by
  intro φ hφ
  have hmem : τinv N φ ∈ parabolicHoms 𝒪 (Gamma0 N) 𝒪 := by
    rw [← τ_mem_parabolicHoms_iff N (R := 𝒪), τ_τinv]
    exact hφ
  exact ⟨⟨τinv N φ, hmem⟩, τ_τinv N (R := 𝒪) φ⟩

theorem main [NeZero N] :
    (∀ (r : 𝒪) (x : ↥(parabolicHoms ℤ (Gamma0 N) ℤ)) (γ : ↥(CohCarrier.GammaH N ⊤)),
        ι N 𝒪 (r ⊗ₜ[ℤ] x) (Additive.ofMul γ) =
          r * ((x : Additive ↥(Gamma0 N) →+ ℤ)
            (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) : 𝒪)) ∧
    Function.Injective (ι N 𝒪) ∧
    LinearMap.range (ι N 𝒪) = parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 ∧
    ∀ (ℓ : ℕ) [NeZero ℓ] (r : 𝒪) (x y : ↥(parabolicHoms ℤ (Gamma0 N) ℤ)),
      (y : Additive ↥(Gamma0 N) →+ ℤ) =
          ModularCurve.PDPairing.heckeT0 N ℓ ℤ (x : Additive ↥(Gamma0 N) →+ ℤ) →
        ι N 𝒪 (r ⊗ₜ[ℤ] y) = CohCarrier.heckeT N ⊤ ℓ 𝒪 (ι N 𝒪 (r ⊗ₜ[ℤ] x)) := by
  classical

  obtain ⟨n, b, hb⟩ := ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree (Gamma0 N)
  obtain ⟨b𝒪, hb𝒪⟩ := hb 𝒪
  have hΦb : ∀ i, Φ N 𝒪 (b𝒪 i) = L N 𝒪 (b i) := by
    intro i
    change τ N 𝒪 𝒪 (b𝒪 i : Additive ↥(Gamma0 N) →+ 𝒪) = _
    rw [hb𝒪 i, L_eq']
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro r x γ
    rw [ι_tmul]
    rfl
  ·
    have hli : LinearIndependent 𝒪 (fun i => Φ N 𝒪 (b𝒪 i)) :=
      (b𝒪.linearIndependent.map' (Φ N 𝒪) (LinearMap.ker_eq_bot.mpr (Φ_injective N 𝒪)))
    let B := Algebra.TensorProduct.basis 𝒪 b
    have hιB : ∀ i, ι N 𝒪 (B i) = Φ N 𝒪 (b𝒪 i) := by
      intro i
      rw [Algebra.TensorProduct.basis_apply, ι_tmul, one_smul, hΦb]
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have hrepr := B.linearCombination_repr v
    rw [← hrepr, Finsupp.linearCombination_apply, map_finsuppSum] at hv
    simp_rw [map_smul, hιB] at hv
    have h0 : ∀ i, B.repr v i = 0 := by
      have := linearIndependent_iff.mp hli (B.repr v) (by
        rw [Finsupp.linearCombination_apply]
        exact hv)
      intro i
      rw [this]
      rfl
    rw [← hrepr]
    have : B.repr v = 0 := Finsupp.ext h0
    rw [this]
    simp
  ·
    rw [range_ι]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact L_mem N 𝒪 x
    · intro φ hφ
      obtain ⟨ψ, rfl⟩ := parabolicHoms_top_le_range_Φ N 𝒪 hφ
      have hψ : ψ ∈ Submodule.span 𝒪 (Set.range b𝒪) := by rw [b𝒪.span_eq]; trivial
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hψ
      · rintro _ ⟨i, rfl⟩
        rw [hΦb]
        exact Submodule.subset_span ⟨b i, rfl⟩
      · simp
      · intro u w _ _ hu hw
        rw [map_add]
        exact Submodule.add_mem _ hu hw
      · intro r u _ hu
        rw [map_smul]
        exact Submodule.smul_mem _ r hu
  ·
    intro ℓ _ r x y hy
    rw [ι_tmul, ι_tmul]
    have hlin : ∀ φ : CohCarrier.H1 N ⊤ 𝒪,
        CohCarrier.heckeT N ⊤ ℓ 𝒪 (r • φ) = r • CohCarrier.heckeT N ⊤ ℓ 𝒪 φ := by
      intro φ
      change CohCarrier.coresAdd _ ((r • φ).comp (MonoidHom.toAdditive (CohCarrier.conjL N ⊤ ℓ))) =
        r • CohCarrier.coresAdd _ (φ.comp (MonoidHom.toAdditive (CohCarrier.conjL N ⊤ ℓ)))
      rw [← CohCarrier.coresAdd_smul]
      rfl
    rw [hlin]
    congr 1
    rw [L_eq, L_eq, CohCarrier.heckeT_comp_coeff]
    congr 1
    ext a
    rw [hy]
    change ModularCurve.PDPairing.heckeT0 N ℓ ℤ (x : Additive ↥(Gamma0 N) →+ ℤ) (Additive.ofMul (jTop N (Additive.toMul a))) =
      CohCarrier.heckeT N ⊤ ℓ ℤ (τ N ℤ ℤ (x : Additive ↥(Gamma0 N) →+ ℤ)) (Additive.ofMul (Additive.toMul a))
    rw [jTop_apply, ← ModularCurve.PDPairing.heckeT0_apply_eq_heckeT_top_apply N ℓ ℤ _ (x : Additive ↥(Gamma0 N) →+ ℤ)]
    intro γ
    rfl

end Main

end CohCarrier.ParabolicBridge
p2m_reactivate "P2MW.S_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top.CohCarrier P2MW.S_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top.CohCarrier.ParabolicBridge"
p2m_reactivate "P2MW.S_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top.CohCarrier"

theorem solution
    (N : ℕ) [NeZero N] (𝒪 : Type) [CommRing 𝒪] [IsAddTorsionFree 𝒪] :
    ∃ ι : 𝒪 ⊗[ℤ] ↥(parabolicHoms ℤ (Gamma0 N) ℤ) →ₗ[𝒪] CohCarrier.H1 N ⊤ 𝒪,
      (∀ (r : 𝒪) (x : ↥(parabolicHoms ℤ (Gamma0 N) ℤ)) (γ : ↥(CohCarrier.GammaH N ⊤)),
          ι (r ⊗ₜ[ℤ] x) (Additive.ofMul γ) =
            r * ((x : Additive ↥(Gamma0 N) →+ ℤ)
              (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) : 𝒪)) ∧
      Function.Injective ι ∧
      LinearMap.range ι = parabolicHoms 𝒪 (CohCarrier.GammaH N ⊤) 𝒪 ∧
      ∀ (ℓ : ℕ) [NeZero ℓ] (r : 𝒪) (x y : ↥(parabolicHoms ℤ (Gamma0 N) ℤ)),
        (y : Additive ↥(Gamma0 N) →+ ℤ) =
            ModularCurve.PDPairing.heckeT0 N ℓ ℤ (x : Additive ↥(Gamma0 N) →+ ℤ) →
          ι (r ⊗ₜ[ℤ] y) = CohCarrier.heckeT N ⊤ ℓ 𝒪 (ι (r ⊗ₜ[ℤ] x)) :=
  ⟨CohCarrier.ParabolicBridge.ι N 𝒪, CohCarrier.ParabolicBridge.main N 𝒪⟩

end S_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top
end P2MW
export P2MW.S_CohCarrier_exists_linearMap_baseChange_parabolicHoms_gamma0_range_eq_parabolicHoms_top (solution)
