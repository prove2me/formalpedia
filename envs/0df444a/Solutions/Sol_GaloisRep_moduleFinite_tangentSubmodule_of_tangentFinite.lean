-- Prove2me | solution 1 for GaloisRep.moduleFinite_tangentSubmodule_of_tangentFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4fccb75c-444c-5867-a00e-ded6c287423b

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor
import Definitions.Def_Deformations_TangentSubmodule
import Definitions.Def_Representation_AbsolutelyIrreducible
import Definitions.Def_Deformations_MatrixRepresentation
import Definitions.Def_Deformations_DualNumbers
import Theorems.Thm_GaloisRepAdic_galoisActionIsAdicContinuous_toLin_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_moduleFinite_tangentSubmodule_of_tangentFinite

set_option autoImplicit false
open CategoryTheory IsLocalRing

set_option autoImplicit false
set_option maxHeartbeats 0

open CategoryTheory IsLocalRing Deformation Deformation.ProartinianCat TrivSqZeroExt
open scoped TensorProduct DualNumber

namespace GaloisRep
p2m_export "GaloisRep" "IsDeformationCondition TangentFinite conditionSubfunctor"
namespace SolTF
p2m_open "GaloisRep"

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Framed

variable (X : Type) [CommRing X] [IsLocalRing X]

abbrev StdCont (τ : Γℚ →* GL (Fin 2) X) : Prop :=
  GaloisActionIsAdicContinuous X
    ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp τ))

noncomputable def mkStd (τ : Γℚ →* GL (Fin 2) X) (hc : StdCont X τ) : GaloisRepAdic X where
  V := Fin 2 → X
  finrank_eq := by simp
  ρ := (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp τ)
  isAdicContinuous := hc

omit [IsLocalRing X] in
lemma mkStd_ρ_eq_toLin' [IsLocalRing X] (τ : Γℚ →* GL (Fin 2) X) (hc : StdCont X τ) (σ : Γℚ) :
    (mkStd X τ hc).ρ σ = Matrix.toLin' ((τ σ : GL (Fin 2) X) : Matrix (Fin 2) (Fin 2) X) := by
  rw [Matrix.toLin'_apply']
  exact Matrix.GeneralLinearGroup.coe_toLin _

lemma mkStd_ρ_apply (τ : Γℚ →* GL (Fin 2) X) (hc : StdCont X τ) (σ : Γℚ) (v : Fin 2 → X) :
    (mkStd X τ hc).ρ σ v = ((τ σ : GL (Fin 2) X) : Matrix (Fin 2) (Fin 2) X).mulVec v := by
  show ((Matrix.GeneralLinearGroup.toLin (τ σ) : LinearMap.GeneralLinearGroup X (Fin 2 → X)) :
    (Fin 2 → X) →ₗ[X] (Fin 2 → X)) v = _
  rw [Matrix.GeneralLinearGroup.coe_toLin]
  rfl

theorem exists_conj_of_isEquiv_mkStd (τ₁ τ₂ : Γℚ →* GL (Fin 2) X)
    (hc₁ : StdCont X τ₁) (hc₂ : StdCont X τ₂) (h : (mkStd X τ₁ hc₁).IsEquiv (mkStd X τ₂ hc₂)) :
    ∃ g : GL (Fin 2) X, ∀ σ, g * τ₁ σ * g⁻¹ = τ₂ σ := by
  obtain ⟨e⟩ := h
  let L : (Fin 2 → X) ≃ₗ[X] (Fin 2 → X) := e.toLinearEquiv
  have h1 : LinearMap.toMatrix' L.toLinearMap * LinearMap.toMatrix' L.symm.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    exact congrArg _ (LinearMap.ext fun v => L.apply_symm_apply v)
  have h2 : LinearMap.toMatrix' L.symm.toLinearMap * LinearMap.toMatrix' L.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    exact congrArg _ (LinearMap.ext fun v => L.symm_apply_apply v)
  let g : GL (Fin 2) X :=
    ⟨LinearMap.toMatrix' L.toLinearMap, LinearMap.toMatrix' L.symm.toLinearMap, h1, h2⟩
  have hg : ∀ w, (g : Matrix (Fin 2) (Fin 2) X).mulVec w = L w := fun w =>
    LinearMap.toMatrix'_mulVec _ _
  refine ⟨g, fun σ => ?_⟩
  have key : (g : Matrix (Fin 2) (Fin 2) X) * ((τ₁ σ : GL (Fin 2) X) : Matrix (Fin 2) (Fin 2) X) =
      ((τ₂ σ : GL (Fin 2) X) : Matrix (Fin 2) (Fin 2) X) * (g : Matrix (Fin 2) (Fin 2) X) := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [hg, hg]
    have := e.map_apply σ v
    rw [mkStd_ρ_apply, mkStd_ρ_apply] at this
    exact this
  rw [mul_inv_eq_iff_eq_mul]
  exact Units.ext key

end Framed

lemma equiv_toLin_apply {ι R M N : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (β₁ : Module.Basis ι R M) (β₂ : Module.Basis ι R N) (P : Matrix ι ι R) (x : M) :
    β₁.equiv β₂ (Equiv.refl ι) (Matrix.toLin β₁ β₁ P x) =
      Matrix.toLin β₂ β₂ P (β₁.equiv β₂ (Equiv.refl ι) x) := by
  have key : (β₁.equiv β₂ (Equiv.refl ι)).toLinearMap ∘ₗ Matrix.toLin β₁ β₁ P =
      Matrix.toLin β₂ β₂ P ∘ₗ (β₁.equiv β₂ (Equiv.refl ι)).toLinearMap := by
    refine β₁.ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Matrix.toLin_self, map_sum,
      map_smul, Module.Basis.equiv_apply, Equiv.refl_apply]
  exact LinearMap.congr_fun key x

section Dual

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]

scoped instance instIsArtinianRing_dualNumbers : IsArtinianRing (dualNumbers 𝒪) :=
  inferInstanceAs (IsArtinianRing ((ResidueField 𝒪)[ε]))

scoped instance instFinite_dualNumber [Finite (ResidueField 𝒪)] : Finite ((ResidueField 𝒪)[ε]) :=
  inferInstanceAs (Finite ((ResidueField 𝒪) × (ResidueField 𝒪)))

omit [IsLocalRing 𝒪] in
lemma fst_eq_zero_of_mem_maximalIdeal [IsLocalRing 𝒪] {x : (ResidueField 𝒪)[ε]}
    (hx : x ∈ maximalIdeal ((ResidueField 𝒪)[ε])) : x.fst = 0 := by
  rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero,
    not_not] at hx
  exact hx

lemma maximalIdeal_dualNumber_sq_eq_bot : (maximalIdeal ((ResidueField 𝒪)[ε])) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [Ideal.mem_bot]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [fst_mul, fst_eq_zero_of_mem_maximalIdeal hx, zero_mul, fst_zero]
  · rw [snd_mul, fst_eq_zero_of_mem_maximalIdeal hx, fst_eq_zero_of_mem_maximalIdeal hy, zero_smul,
      MulOpposite.op_zero, zero_smul, add_zero, snd_zero]

scoped instance instIsAdicTopology_dualNumbers : IsAdicTopology (dualNumbers 𝒪) := by
  refine ⟨isAdic_iff.mpr ⟨fun n => isOpen_discrete _, fun s hs => ⟨2, ?_⟩⟩⟩
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y : (ResidueField 𝒪)[ε], y = x := ⟨x, rfl⟩
  have hy : y ∈ ((maximalIdeal ((ResidueField 𝒪)[ε])) ^ 2 : Ideal ((ResidueField 𝒪)[ε])) := hx
  rw [maximalIdeal_dualNumber_sq_eq_bot, Ideal.mem_bot] at hy
  rw [hy]
  exact mem_of_mem_nhds hs

variable (𝒪) in

noncomputable abbrev algTF : Algebra 𝒪 ((ResidueField 𝒪)[ε]) :=
  ((algebraMap (ResidueField 𝒪) ((ResidueField 𝒪)[ε])).comp (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra

variable (𝒪) in

noncomputable abbrev algResTF :
    Algebra (ResidueField 𝒪) (ResidueField ((ResidueField 𝒪)[ε])) :=
  ((IsLocalRing.residue ((ResidueField 𝒪)[ε])).comp
    (algebraMap (ResidueField 𝒪) ((ResidueField 𝒪)[ε]))).toAlgebra

lemma algebra_dualNumbers_eq_algTF :
    (ProartinianCat.algebra (dualNumbers 𝒪) : Algebra 𝒪 ((ResidueField 𝒪)[ε])) = algTF 𝒪 := by
  refine Algebra.algebra_ext _ _ fun o => ?_
  rfl

variable (ρ₀ : Γℚ →ₜ* GL (Fin 2) (ProartinianCat.residueField (𝓞 := 𝒪)))

def toDual (τ : Γℚ →ₜ* GL (Fin 2) (dualNumbers 𝒪)) : Γℚ →* GL (Fin 2) ((ResidueField 𝒪)[ε]) :=
  τ.toMonoidHom

omit [IsLocalRing 𝒪] in
lemma toDual_apply [IsLocalRing 𝒪] (τ : Γℚ →ₜ* GL (Fin 2) (dualNumbers 𝒪)) (σ : Γℚ) :
    toDual τ σ = τ σ := rfl

lemma stdCont_toDual (τ : Γℚ →ₜ* GL (Fin 2) (dualNumbers 𝒪)) :
    StdCont ((ResidueField 𝒪)[ε]) (toDual τ) :=
  GaloisRepAdic.galoisActionIsAdicContinuous_toLin_of_continuous (dualNumbers 𝒪) τ

noncomputable def mkDual (τ : Γℚ →ₜ* GL (Fin 2) (dualNumbers 𝒪)) : GaloisRepAdic ((ResidueField 𝒪)[ε]) :=
  mkStd ((ResidueField 𝒪)[ε]) (toDual τ) (stdCont_toDual τ)

lemma fst_apply_of_mem_liftFunctor {τ : Γℚ →ₜ* GL (Fin 2) (dualNumbers 𝒪)}
    (hτ : τ ∈ (liftFunctor (Fin 2) Γℚ 𝒪 ρ₀).obj (dualNumbers 𝒪)) (σ : Γℚ) (i j : Fin 2) :
    (((toDual τ σ : GL (Fin 2) ((ResidueField 𝒪)[ε])) : Matrix (Fin 2) (Fin 2) ((ResidueField 𝒪)[ε])) i j).fst =
      (ρ₀ σ).val i j := by
  have h2 : (repnFunctor (Fin 2) Γℚ 𝒪).map (dualNumbersFst 𝒪) τ = ρ₀ := by
    have := hτ
    simp only [liftFunctor, Subfunctor.ofIsTerminal] at this
    rw [Subsingleton.elim (isTerminalResidueField.from (dualNumbers 𝒪)) (dualNumbersFst 𝒪)] at this
    exact this
  have h3 := congrArg (fun (f : Γℚ →ₜ* GL (Fin 2) (ProartinianCat.residueField (𝓞 := 𝒪))) => f σ) h2
  simp only at h3
  rw [repnFunctor_map] at h3
  have h4 := congrArg (fun u : GL (Fin 2) (ProartinianCat.residueField (𝓞 := 𝒪)) => u.val i j) h3
  beta_reduce at h4
  rw [← h4]
  rfl

lemma cond_mkDual
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    {τ : Γℚ →ₜ* GL (Fin 2) (dualNumbers 𝒪)}
    (hτ : τ ∈ (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).obj (dualNumbers 𝒪)) :
    letI := algTF 𝒪
    𝒟 (mkDual τ) := by

  have hD : (letI := ProartinianCat.algebra (dualNumbers 𝒪); 𝒟 (mkDual τ)) := by
    refine hτ.2 (dualNumbers 𝒪) (𝟙 _) (mkDual τ) (Pi.basisFun ((ResidueField 𝒪)[ε]) (Fin 2)) (fun σ => ?_)
    have e1 : LinearMap.toMatrix' ((mkDual τ).ρ σ) =
        ((mapRepn (Fin 2) Γℚ 𝒪 (𝟙 (dualNumbers 𝒪)) τ σ : GL (Fin 2) (dualNumbers 𝒪)) :
          Matrix (Fin 2) (Fin 2) (dualNumbers 𝒪)) := by
      rw [show (mkDual τ).ρ σ = _ from mkStd_ρ_eq_toLin' _ _ _ σ, LinearMap.toMatrix'_toLin']
      rfl
    have e2 : LinearMap.toMatrix (Pi.basisFun ((ResidueField 𝒪)[ε]) (Fin 2))
        (Pi.basisFun ((ResidueField 𝒪)[ε]) (Fin 2)) ((mkDual τ).ρ σ) = LinearMap.toMatrix' ((mkDual τ).ρ σ) := by
      rw [LinearMap.toMatrix_eq_toMatrix']
    exact e2.trans e1
  have key : ∀ (inst : Algebra 𝒪 ((ResidueField 𝒪)[ε])), inst = algTF 𝒪 →
      (letI := inst; 𝒟 (mkDual τ)) → (letI := algTF 𝒪; 𝒟 (mkDual τ)) := by
    rintro _ rfl h
    exact h
  exact key _ algebra_dualNumbers_eq_algTF hD

variable (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (b : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V)
  (hρ₀ : ∀ σ, (ρ₀ σ).val = LinearMap.toMatrix b b (ρbar.ρ σ))

include hρ₀ in

theorem residual_mkDual_isEquiv {τ : Γℚ →ₜ* GL (Fin 2) (dualNumbers 𝒪)}
    (hτ : τ ∈ (liftFunctor (Fin 2) Γℚ 𝒪 ρ₀).obj (dualNumbers 𝒪)) :
    (mkDual τ).residual.IsEquiv
      (@ResidualGaloisRep.baseChange (ResidueField 𝒪) _ (ResidueField ((ResidueField 𝒪)[ε])) _
        (algResTF 𝒪) ρbar) := by
  letI : Algebra (ResidueField 𝒪) (ResidueField ((ResidueField 𝒪)[ε])) := algResTF 𝒪
  letI : Module (ResidueField 𝒪) (ResidueField ((ResidueField 𝒪)[ε])) := Algebra.toModule
  classical

  let K' := ResidueField ((ResidueField 𝒪)[ε])

  let P : Γℚ → Matrix (Fin 2) (Fin 2) K' := fun σ => ((ρ₀ σ).val).map (algebraMap (ResidueField 𝒪) K')

  let β₁ : Module.Basis (Fin 2) K' (K' ⊗[(ResidueField 𝒪)[ε]] (Fin 2 → (ResidueField 𝒪)[ε])) :=
    Algebra.TensorProduct.basis K' (Pi.basisFun ((ResidueField 𝒪)[ε]) (Fin 2))
  let β₂ : Module.Basis (Fin 2) K' (K' ⊗[ResidueField 𝒪] ρbar.V) :=
    Algebra.TensorProduct.basis K' b

  have h1 : ∀ σ, (mkDual τ).residual.ρ σ = Matrix.toLin β₁ β₁ (P σ) := by
    intro σ
    show ((mkDual τ).ρ σ).baseChange K' = Matrix.toLin β₁ β₁ (P σ)
    apply (LinearMap.toMatrix β₁ β₁).injective
    rw [LinearMap.toMatrix_toLin]
    have hρ : (mkDual τ).ρ σ = Matrix.toLin (Pi.basisFun ((ResidueField 𝒪)[ε]) (Fin 2))
        (Pi.basisFun ((ResidueField 𝒪)[ε]) (Fin 2))
        ((toDual τ σ : GL (Fin 2) ((ResidueField 𝒪)[ε])) : Matrix (Fin 2) (Fin 2) ((ResidueField 𝒪)[ε])) := by
      rw [Matrix.toLin_eq_toLin']
      exact mkStd_ρ_eq_toLin' _ _ _ σ
    rw [hρ]
    show LinearMap.toMatrix (Algebra.TensorProduct.basis K' (Pi.basisFun ((ResidueField 𝒪)[ε]) (Fin 2)))
        (Algebra.TensorProduct.basis K' (Pi.basisFun ((ResidueField 𝒪)[ε]) (Fin 2)))
        (LinearMap.baseChange K' (Matrix.toLin (Pi.basisFun ((ResidueField 𝒪)[ε]) (Fin 2))
          (Pi.basisFun ((ResidueField 𝒪)[ε]) (Fin 2))
          ((toDual τ σ : GL (Fin 2) ((ResidueField 𝒪)[ε])) : Matrix (Fin 2) (Fin 2) ((ResidueField 𝒪)[ε])))) = P σ
    rw [LinearMap.toMatrix_baseChange, LinearMap.toMatrix_toLin]
    ext i j
    rw [Matrix.map_apply, IsLocalRing.ResidueField.algebraMap_eq, ← residue_inl_fst_eq,
      fst_apply_of_mem_liftFunctor ρ₀ hτ σ i j]
    rfl
  have h2 : ∀ σ, (ResidualGaloisRep.baseChange K' ρbar).ρ σ = Matrix.toLin β₂ β₂ (P σ) := by
    intro σ
    show (ρbar.ρ σ).baseChange K' = _
    apply (LinearMap.toMatrix β₂ β₂).injective
    rw [LinearMap.toMatrix_toLin, LinearMap.toMatrix_baseChange, ← hρ₀ σ]
    rfl
  refine ⟨{ toLinearEquiv := β₁.equiv β₂ (Equiv.refl _), map_apply := fun σ x => ?_ }⟩
  rw [h1, h2]
  exact equiv_toLin_apply β₁ β₂ (P σ) x

end Dual

section FiniteLifts

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
variable (ρbar : ResidualGaloisRep (ResidueField 𝒪))
  (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
  (ρ₀ : Γℚ →ₜ* GL (Fin 2) (ProartinianCat.residueField (𝓞 := 𝒪)))
  (b : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V)
  (hρ₀ : ∀ σ, (ρ₀ σ).val = LinearMap.toMatrix b b (ρbar.ρ σ))

lemma exists_smul_eq_of_isEquiv {τ₁ τ₂ : Γℚ →ₜ* GL (Fin 2) (dualNumbers 𝒪)}
    (h : (mkDual τ₁).IsEquiv (mkDual τ₂)) :
    ∃ g : ConjAct (GL (Fin 2) (dualNumbers 𝒪)), τ₂ = g • τ₁ := by
  obtain ⟨g, hg⟩ := exists_conj_of_isEquiv_mkStd _ _ _ _ _ h
  refine ⟨ConjAct.toConjAct (show GL (Fin 2) (dualNumbers 𝒪) from g), ?_⟩
  apply ContinuousMonoidHom.ext
  intro σ
  rw [conjAct_smul_apply, ConjAct.ofConjAct_toConjAct]
  exact (hg σ).symm

scoped instance instFinite_conjAct [Finite (ResidueField 𝒪)] : Finite (ConjAct (GL (Fin 2) (dualNumbers 𝒪))) := by
  haveI : Finite (dualNumbers 𝒪) := inferInstanceAs (Finite ((ResidueField 𝒪)[ε]))
  haveI : Finite (Matrix (Fin 2) (Fin 2) (dualNumbers 𝒪)) :=
    inferInstanceAs (Finite (Fin 2 → Fin 2 → dualNumbers 𝒪))
  haveI : Finite (GL (Fin 2) (dualNumbers 𝒪)) :=
    Finite.of_injective (fun u : GL (Fin 2) (dualNumbers 𝒪) => (u : Matrix (Fin 2) (Fin 2) (dualNumbers 𝒪)))
      Units.val_injective
  exact Finite.of_equiv _ ConjAct.toConjAct.toEquiv

include hρ₀ in

theorem finite_conditionLifts_dualNumbers [Finite (ResidueField 𝒪)]
    (hfin : GaloisRep.TangentFinite 𝒪 ρbar 𝒟) :
    Finite ((GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).obj (dualNumbers 𝒪)) := by
  classical
  letI : Algebra 𝒪 ((ResidueField 𝒪)[ε]) := algTF 𝒪
  letI : Algebra (ResidueField 𝒪) (ResidueField ((ResidueField 𝒪)[ε])) := algResTF 𝒪

  let T := {ρ : GaloisRepAdic ((ResidueField 𝒪)[ε]) //
      𝒟 ρ ∧ ρ.residual.IsEquiv (ρbar.baseChange (ResidueField ((ResidueField 𝒪)[ε])))}
  let s : Setoid T := ⟨fun ρ ρ' => ρ.1.IsEquiv ρ'.1, ⟨fun ρ => ⟨GaloisRepAdic.Equiv.refl ρ.1⟩,
        fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩⟩
  haveI hQ : Finite (Quotient s) := hfin
  let S := (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).obj (dualNumbers 𝒪)
  let ι : S → (Γℚ →ₜ* GL (Fin 2) (dualNumbers 𝒪)) := fun τ => τ.1
  have hι : Function.Injective ι := Subtype.val_injective
  let f : S → Quotient s := fun τ => Quotient.mk s
    ⟨mkDual (ι τ), cond_mkDual ρ₀ 𝒟 τ.2, residual_mkDual_isEquiv ρ₀ ρbar b hρ₀ τ.2.1⟩

  have hfib : ∀ τ τ' : S, f τ = f τ' →
      ∃ g : ConjAct (GL (Fin 2) (dualNumbers 𝒪)), ι τ' = g • ι τ := by
    intro τ τ' h
    exact exists_smul_eq_of_isEquiv (Quotient.exact h)
  haveI : ∀ q : Quotient s, Finite {τ : S // f τ = q} := by
    intro q
    by_cases hq : ∃ τ₀ : S, f τ₀ = q
    · obtain ⟨τ₀, hτ₀⟩ := hq
      have hsel : ∀ τ : {τ : S // f τ = q},
          ∃ g : ConjAct (GL (Fin 2) (dualNumbers 𝒪)), ι τ.1 = g • ι τ₀ :=
        fun τ => hfib τ₀ τ.1 (hτ₀.trans τ.2.symm)
      choose φ hφ using hsel
      refine Finite.of_injective φ fun τ τ' hφφ => ?_
      have hh : ι τ.1 = ι τ'.1 := by rw [hφ τ, hφ τ', hφφ]
      exact Subtype.ext (hι hh)
    · haveI : IsEmpty {τ : S // f τ = q} := ⟨fun τ => hq ⟨τ.1, τ.2⟩⟩
      infer_instance
  exact Finite.of_equiv _ (Equiv.sigmaFiberEquiv f)

end FiniteLifts

section Tangent

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (R : ProartinianCat 𝒪)

noncomputable def tangentHom {D : R → ResidueField 𝒪} (hD : IsTangentVector R D) : R ⟶ dualNumbers 𝒪 where
  hom :=
    { toFun := fun r => (⟨residueMap R r, D r⟩ : (ResidueField 𝒪)[ε])
      map_one' := TrivSqZeroExt.ext residueMap_one hD.map_one
      map_mul' := fun r s => TrivSqZeroExt.ext (residueMap_mul r s) <| by
        show D (r * s) = residueMap R r • D s + MulOpposite.op (residueMap R s) • D r
        rw [smul_eq_mul, op_smul_eq_mul, hD.leibniz r s, mul_comm (D r) (residueMap R s)]
      map_zero' := TrivSqZeroExt.ext residueMap_zero hD.map_zero
      map_add' := fun r s => TrivSqZeroExt.ext (residueMap_add r s) (hD.map_add r s)
      commutes' := fun o => by
        refine TrivSqZeroExt.ext (R := ResidueField 𝒪) (M := ResidueField 𝒪) ?_ ?_
        · exact (residueMap_algebraMap o).trans
            (congrArg TrivSqZeroExt.fst
              (TrivSqZeroExt.algebraMap_eq_inl' 𝒪 (ResidueField 𝒪) (ResidueField 𝒪) o)).symm
        · exact (hD.map_algebraMap o).trans
            (congrArg TrivSqZeroExt.snd
              (TrivSqZeroExt.algebraMap_eq_inl' 𝒪 (ResidueField 𝒪) (ResidueField 𝒪) o)).symm
      cont := (IsLocallyConstant.iff_continuous _).mp
        (isLocallyConstant_residueMap.prodMk hD.isLocallyConstant) }

lemma snd_tangentHom_apply {D : R → ResidueField 𝒪} (hD : IsTangentVector R D) (r : R) :
    ((tangentHom R hD).hom r : (ResidueField 𝒪)[ε]).snd = D r := rfl

theorem tangentHom_injective :
    Function.Injective (fun D : tangentSubmodule R => tangentHom R D.2) := by
  intro D D' h
  apply Subtype.ext
  funext r
  have := congrArg (fun f : R ⟶ dualNumbers 𝒪 => ((f.hom r : (ResidueField 𝒪)[ε])).snd) h
  exact this

end Tangent

end GaloisRep.SolTF
p2m_reactivate "P2MW.S_GaloisRep_moduleFinite_tangentSubmodule_of_tangentFinite.GaloisRep P2MW.S_GaloisRep_moduleFinite_tangentSubmodule_of_tangentFinite.GaloisRep.SolTF"
p2m_reactivate "P2MW.S_GaloisRep_moduleFinite_tangentSubmodule_of_tangentFinite.GaloisRep"

open CategoryTheory IsLocalRing GaloisRep.SolTF Deformation in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
    (b : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V)
    (hρ₀ : ∀ σ, (ρ₀ σ).val = LinearMap.toMatrix b b (ρbar.ρ σ))
    [Representation.IsAbsolutelyIrreducible.{0} (Deformation.matrixRepresentation ρ₀.toMonoidHom)]
    (hfin : GaloisRep.TangentFinite 𝒪 ρbar 𝒟)
    {R : Deformation.ProartinianCat 𝒪}
    (e : (Deformation.conjQuotSubfunctor (Fin 2) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀)).toFunctor.CorepresentableBy R) :
    Module.Finite (IsLocalRing.ResidueField 𝒪) (Deformation.ProartinianCat.tangentSubmodule R) := by
  classical
  have h1 : Finite ((GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).toFunctor.obj (ProartinianCat.dualNumbers 𝒪)) :=
    finite_conditionLifts_dualNumbers ρbar 𝒟 ρ₀ b hρ₀ hfin
  have h2 : Finite ((Deformation.conjQuotSubfunctor (Fin 2)
      (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀)).toFunctor.obj (ProartinianCat.dualNumbers 𝒪)) :=
    @Finite.of_surjective _ _ h1 _
      (condLiftToDeformation_surjective (Fin 2) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀)
        (ProartinianCat.dualNumbers 𝒪))
  haveI : Finite (R ⟶ ProartinianCat.dualNumbers 𝒪) := @Finite.of_equiv _ _ h2 e.homEquiv.symm
  haveI : Finite (ProartinianCat.tangentSubmodule R) := Finite.of_injective _ (tangentHom_injective R)
  exact Module.Finite.of_finite

end S_GaloisRep_moduleFinite_tangentSubmodule_of_tangentFinite
end P2MW
export P2MW.S_GaloisRep_moduleFinite_tangentSubmodule_of_tangentFinite (solution)
