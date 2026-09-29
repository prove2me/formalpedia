-- Prove2me | solution 1 for CerednikDrinfeld.HeckeTower.atkinLehner_involutive_comm_galois_of_descentIntertwining_one_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/1972e2f4-80fa-58e8-8323-1b9345eef431

import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_DescentIntertwining_v2
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_CerednikDrinfeld_CosetGraph_atkinLehner_relations_levelGroups_place
import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_HeckeTower_atkinLehner_involutive_comm_galois_of_descentIntertwining_one_zero
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve
open CerednikDrinfeld.Mumford CerednikDrinfeld.Omega
open scoped Classical

set_option maxHeartbeats 6400000 in
theorem solution

    {a₂ b₂ : ℚ} {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (hdef₂ : IsDefiniteRamifiedExactlyAt a₂ b₂ q)
    (Λ₂ R₂ : Submodule ℤ ℍ[ℚ, a₂, b₂]) (hΛ₂ : IsMaximalOrder Λ₂) (hR₂ : IsEichlerOrder R₂ N) (hRΛ₂ : R₂ ≤ Λ₂)
    (n₂ : (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₂ : n₂ ∈ primeHeckeSet R₂ q')
    (hS₂ : IsEichlerOrder (meetOrder R₂ n₂) (N * q'))
    (hnorm₂ : Submodule.conjByFiniteIdele (meetOrder R₂ n₂) n₂ = meetOrder R₂ n₂)
    (hsq₂ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)),
      classSetShift _ n₂ (classSetShift _ n₂ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    (hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂)

    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')

    (FN : Type) [Field FN] [Algebra (AlgebraicClosure ℚ) FN] [IsCurveOver (AlgebraicClosure ℚ) FN]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) FN]
    (𝕋 : HeckeTower.TowerData q q' FN)
    (hfg : ∀ j : HeckeTower.Obj q q', ∃ x : 𝕋.objField j, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (𝕋.objField j))) (𝕋.objField j))
    (galN : ↥(A₁.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) FN)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ↥(A₁.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (hgalN : ∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galN τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (hgalT : ∀ ℓ (τ : ↥(A₁.decompositionSubgroup ℚ)) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (galT ℓ τ) a = (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a)
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) FN) (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))

    [hiso₁ : Fact (A₁.DecompositionIsometric ℚ)]
    (v₁ : HeightOneSpectrum (𝓞 ℚ)) (hv₁ : ((q' : ℕ) : 𝓞 ℚ) ∈ v₁.asIdeal)

    (ι₁ : ℍ[ℚ, a₂, b₂] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) (hι₁ : Function.Injective ι₁)
    (ρ₁ : (ℍ[ℚ, a₂, b₂])ˣ →* PGL(2, ↥(ValuationSubring.ratClosure A₁)))
    (hρ₁ : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, ρ₁ x = Matrix.ProjGenLinGroup.mk (Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) x))

    (ϖ₁ : Omega.PseudoUniformizer ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hϖ₁ : algebraMap ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion ϖ₁.ϖ = ((q' : AlgebraicClosure ℚ) : A₁.valuation.Completion))
    [hdom₁ : IsDomain (Omega.HolRingOf ϖ₁ ρ₁)]

    (s₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (sf₁ : HeckeTower.AwayPrime q q' → (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs₁ : ∀ ℓ : HeckeTower.AwayPrime q q',
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s₁ ℓ : ℍ[ℚ, a₂, b₂]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₂, b₂] u (sf₁ ℓ : ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₂, b₂]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf₁ ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₂ (meetOrder R₂ n₂) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₂ n₂) (ℓ.1 : ℕ)) ∧
      nrd (s₁ ℓ : ℍ[ℚ, a₂, b₂]) = ((ℓ.1 : ℕ) : ℚ))

    (Γ₁ : HeckeTower.Obj q q' → Subgroup (ℍ[ℚ, a₂, b₂])ˣ)
    (hΓ₁0 : ∀ x : (ℍ[ℚ, a₂, b₂])ˣ, x ∈ Γ₁ none ↔
      x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ Even (padicValRat q' (nrd (x : ℍ[ℚ, a₂, b₂]))))
    (hΓ₁ℓ : ∀ ℓ : HeckeTower.AwayPrime q q', Γ₁ (some ℓ) = Γ₁ none ⊓ (Γ₁ none).map (MulAut.conj (s₁ ℓ)).toMonoidHom)

    (w₁ wbar₁ : HeckeTower.Obj q q' → (ℍ[ℚ, a₂, b₂])ˣ)
    (hw₁ : (w₁ none ∈ CerednikDrinfeld.CosetGraph.awayUnits R₂ v₁ ∧ nrd (w₁ none : ℍ[ℚ, a₂, b₂]) = (q' : ℚ)) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        w₁ (some ℓ) ∈ CerednikDrinfeld.CosetGraph.awayUnits (meetOrder R₂ (sf₁ ℓ)) v₁ ∧ nrd (w₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q' : ℚ))
    (hwbar₁ :
      (nrd (wbar₁ none : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
          CosetGraph.toLoc u (wbar₁ none) ∈ Submodule.localBoxUnits R₂ u) ∧
        (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox R₂ u ↔
            x ∈ Submodule.localBox R₂ u) ∧
          ((((CosetGraph.toLoc u (wbar₁ none))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
              ((CosetGraph.toLoc u (wbar₁ none) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
            x ∈ Submodule.localBox Λ₂ u))) ∧
      ∀ ℓ : HeckeTower.AwayPrime q q',
        (nrd (wbar₁ (some ℓ) : ℍ[ℚ, a₂, b₂]) = (q : ℚ) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ((q : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
            CosetGraph.toLoc u (wbar₁ (some ℓ)) ∈ Submodule.localBoxUnits (meetOrder R₂ (sf₁ ℓ)) u) ∧
          (∀ u : HeightOneSpectrum (𝓞 ℚ), u ≠ v₁ → ∀ x : CosetGraph.Loc a₂ b₂ u,
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u ↔
              x ∈ Submodule.localBox (meetOrder R₂ (sf₁ ℓ)) u) ∧
            ((((CosetGraph.toLoc u (wbar₁ (some ℓ)))⁻¹ : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) * x *
                ((CosetGraph.toLoc u (wbar₁ (some ℓ)) : (CosetGraph.Loc a₂ b₂ u)ˣ) : CosetGraph.Loc a₂ b₂ u) ∈ Submodule.localBox Λ₂ u ↔
              x ∈ Submodule.localBox Λ₂ u))))

    (dIso₁ : ↥(A₁.decompositionSubgroup ℚ) →* Omega.IsometricAut ↥(ValuationSubring.ratClosure A₁) A₁.valuation.Completion)
    (hdIso₁ : ∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (x : A₁.valuation.Completion), (dIso₁ τ).toRingEquiv x = τ • x)

    (χ₁ : ↥(A₁.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
    (ιM₁ : ∀ j : HeckeTower.Obj q q', 𝕋.objField j →+* FractionRing (Omega.HolRingOf ϖ₁ ρ₁))
    (hI : CerednikDrinfeld.DescentIntertwining q' (1 : Fin 2) (0 : Fin 2) A₁ ρ₁ ϖ₁ Γ₁ w₁ wbar₁ s₁ dIso₁
      FN 𝕋 galN galT W WT χ₁ ιM₁)
    :
    (∀ i : Fin 2, W i * W i = 1) ∧ W 1 * W 0 = W 0 * W 1 ∧
    (∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (i : Fin 2), galN τ * W i = W i * galN τ) ∧
    (∀ (i : Fin 2) (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (W i) a = a) ∧
    (∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2), WT ℓ i * WT ℓ i = 1) ∧
    (∀ ℓ : HeckeTower.AwayPrime q q', WT ℓ 1 * WT ℓ 0 = WT ℓ 0 * WT ℓ 1) ∧
    (∀ (ℓ : HeckeTower.AwayPrime q q') (τ : ↥(A₁.decompositionSubgroup ℚ)) (i : Fin 2), galT ℓ τ * WT ℓ i = WT ℓ i * galT ℓ τ) ∧
    (∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2) (a : AlgebraicClosure ℚ), SemilinearAut.baseAut (WT ℓ i) a = a) := by
  classical

  let galJ : ∀ j : HeckeTower.Obj q q',
      ↥(A₁.decompositionSubgroup ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.objField j) :=
    fun j => match j with
      | none => galN
      | some ℓ => galT ℓ
  let WJ : ∀ j : HeckeTower.Obj q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.objField j) :=
    fun j => match j with
      | none => W
      | some ℓ => WT ℓ

  obtain ⟨hP1, hP2, hP3, hI0a, hI0b, hI0c, hI1a, hI1b, hI2a, hI2b, hI2c, hI2d, hI3a, hI3b⟩ := id hI
  have hAL := CerednikDrinfeld.CosetGraph.atkinLehner_relations_levelGroups_place hN hqN hq'N hqq' hq5 hq'5
    q' q (by assumption) (by assumption) (by first | exact hqq' | exact (Ne.symm hqq')) hdef₂ Λ₂ R₂ hΛ₂ hR₂ hRΛ₂
    n₂ hn₂ v₁ hv₁ s₁ sf₁ hs₁ Γ₁ hΓ₁0 hΓ₁ℓ w₁ wbar₁ hw₁ hwbar₁

  let wJ : HeckeTower.Obj q q' → Fin 2 → (ℍ[ℚ, a₂, b₂])ˣ := fun j i => if i = (1 : Fin 2) then w₁ j else wbar₁ j
  have hfin2 : ∀ i : Fin 2, i = (1 : Fin 2) ∨ i = (0 : Fin 2) := by decide

  have hI2 : ∀ (j : HeckeTower.Obj q q') (i : Fin 2) (x : 𝕋.objField j), ιM₁ j (WJ j i • x) = wJ j i • ιM₁ j x := by
    intro j i x
    rcases hfin2 i with rfl | rfl <;> cases j with
    | none => first | exact hI2a x | exact hI2b x
    | some ℓ => first | exact hI2c ℓ x | exact hI2d ℓ x

  have hιmem : ∀ (j : HeckeTower.Obj q q') (x : 𝕋.objField j),
      ιM₁ j x ∈ Mumford.invariantFieldOf A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j) := by
    intro j x
    rw [← hI0b j]
    exact Subfield.subset_closure (Or.inr ⟨x, rfl⟩)
  have hfix : ∀ (j : HeckeTower.Obj q q') (x : 𝕋.objField j) (γ : (ℍ[ℚ, a₂, b₂])ˣ), γ ∈ Γ₁ j → γ • ιM₁ j x = ιM₁ j x :=
    fun j x γ hγ => (Mumford.mem_invariantFieldOf_iff A₁.valuation.Completion (ℍ[ℚ, a₂, b₂])ˣ (Omega.HolRingOf ϖ₁ ρ₁) (Γ₁ j) (ιM₁ j x)).1 (hιmem j x) γ hγ
  have hιinj : ∀ j : HeckeTower.Obj q q', Function.Injective (ιM₁ j) := fun j => (ιM₁ j).injective

  have slext : ∀ (j : HeckeTower.Obj q q') (g h : SemilinearAut (AlgebraicClosure ℚ) (𝕋.objField j)),
      (∀ x : 𝕋.objField j, g • x = h • x) → g = h := by
    intro j g h hgh
    apply Subtype.ext
    apply Prod.ext
    · exact RingEquiv.ext hgh
    · apply RingEquiv.ext
      intro a
      apply (algebraMap (AlgebraicClosure ℚ) (𝕋.objField j)).injective
      show algebraMap _ _ (SemilinearAut.baseAut g a) = algebraMap _ _ (SemilinearAut.baseAut h a)
      rw [← SemilinearAut.commutes, ← SemilinearAut.commutes]
      exact hgh _
  have hWbase : ∀ (j : HeckeTower.Obj q q') (i : Fin 2) (a : AlgebraicClosure ℚ),
      SemilinearAut.baseAut (WJ j i) a = a := by
    intro j i a
    have key : WJ j i • algebraMap (AlgebraicClosure ℚ) (𝕋.objField j) a = algebraMap (AlgebraicClosure ℚ) (𝕋.objField j) a := by
      apply hιinj j
      rw [hI2 j i, hI0a j a, Mumford.smul_algebraMap_const]
    rw [SemilinearAut.smul_algebraMap] at key
    exact (algebraMap (AlgebraicClosure ℚ) (𝕋.objField j)).injective key
  have hw0 : ∀ j : HeckeTower.Obj q q', wJ j (1 : Fin 2) = w₁ j := fun _ => rfl
  have hw1 : ∀ j : HeckeTower.Obj q q', wJ j (0 : Fin 2) = wbar₁ j := fun _ => rfl

  have hscal : ∀ (j : HeckeTower.Obj q q') (x : 𝕋.objField j), (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) • ιM₁ j x = ιM₁ j x := by
    have hρc : ρ₁ (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) = 1 := by
      rw [hρ₁]
      have : Units.map (ι₁ : ℍ[ℚ, a₂, b₂] →* Matrix (Fin 2) (Fin 2) ↥(ValuationSubring.ratClosure A₁)) (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) =
          Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℚ ↥(ValuationSubring.ratClosure A₁)).toMonoidHom
            (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) := by
        ext i k
        simp [Matrix.GeneralLinearGroup.scalar]
      rw [this, Matrix.ProjGenLinGroup.mk_scalar]
    have hM : ∀ f : Omega.HolRingOf ϖ₁ ρ₁, (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) • f = f := fun f => by
      rw [Omega.HolRingOf.smul_def, hρc, one_smul]
    intro j x
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Omega.HolRingOf ϖ₁ ρ₁) (ιM₁ j x)
    rw [← hab, Mumford.frac_smul_def, map_div₀, ← Mumford.frac_smul_def, ← Mumford.frac_smul_def,
      Mumford.frac_smul_algebraMap, Mumford.frac_smul_algebraMap, hM, hM]
  have hWinv : ∀ (j : HeckeTower.Obj q q') (i : Fin 2), WJ j i * WJ j i = 1 := by
    intro j i
    apply slext j
    intro x
    apply hιinj j
    rw [mul_smul, one_smul]
    rcases hfin2 i with rfl | rfl
    · rw [hI2 j (1 : Fin 2), hI2 j (1 : Fin 2), smul_smul]
      exact hfix j x _ (hAL j).2.2.1
    · rw [hI2 j (0 : Fin 2), hI2 j (0 : Fin 2), smul_smul]
      have h5 := (hAL j).2.2.2.2.1
      show (wbar₁ j * wbar₁ j) • ιM₁ j x = ιM₁ j x
      calc (wbar₁ j * wbar₁ j) • ιM₁ j x
          = ((Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) * ((Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)))⁻¹ * (wbar₁ j * wbar₁ j))) • ιM₁ j x := by congr 1; group
        _ = (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) • (((Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)))⁻¹ * (wbar₁ j * wbar₁ j)) • ιM₁ j x) := mul_smul _ _ _
        _ = (Units.map (algebraMap ℚ ℍ[ℚ, a₂, b₂]).toMonoidHom (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) • ιM₁ j x := by rw [hfix j x _ h5]
        _ = ιM₁ j x := hscal j x
  have hWcomm : ∀ (j : HeckeTower.Obj q q') (i i' : Fin 2), WJ j i * WJ j i' = WJ j i' * WJ j i := by
    intro j i i'
    apply slext j
    intro x
    apply hιinj j
    have h4 := (hAL j).2.2.2.1
    have e10 : wbar₁ j • w₁ j • ιM₁ j x = ιM₁ j (WJ j (0 : Fin 2) • (WJ j (1 : Fin 2) • x)) := by
      rw [hI2 j (0 : Fin 2), hI2 j (1 : Fin 2), hw1, hw0]
    have key : w₁ j • wbar₁ j • ιM₁ j x = wbar₁ j • w₁ j • ιM₁ j x := by
      calc w₁ j • wbar₁ j • ιM₁ j x
          = (w₁ j * wbar₁ j * (w₁ j)⁻¹ * (wbar₁ j)⁻¹ * (wbar₁ j * w₁ j)) • ιM₁ j x := by
            rw [smul_smul]; congr 1; group
        _ = (w₁ j * wbar₁ j * (w₁ j)⁻¹ * (wbar₁ j)⁻¹) • (wbar₁ j • w₁ j • ιM₁ j x) := by simp only [mul_smul]
        _ = wbar₁ j • w₁ j • ιM₁ j x := by rw [e10]; exact hfix j _ _ h4
    rcases hfin2 i with rfl | rfl <;> rcases hfin2 i' with rfl | rfl
    · rfl
    · rw [mul_smul, mul_smul, hI2 j (1 : Fin 2), hI2 j (0 : Fin 2), hI2 j (0 : Fin 2), hI2 j (1 : Fin 2)]; exact key
    · rw [mul_smul, mul_smul, hI2 j (0 : Fin 2), hI2 j (1 : Fin 2), hI2 j (1 : Fin 2), hI2 j (0 : Fin 2)]; exact key.symm
    · rfl
  have hgalW : ∀ (j : HeckeTower.Obj q q') (i : Fin 2) (τ : ↥(A₁.decompositionSubgroup ℚ)),
      WJ j i * galJ j τ = galJ j τ * WJ j i := by

    have hI1 : ∀ (j : HeckeTower.Obj q q') (τ : ↥(A₁.decompositionSubgroup ℚ)) (x : 𝕋.objField j),
        ιM₁ j (galJ j τ • x) = (if χ₁ τ = 1 then (1 : (ℍ[ℚ, a₂, b₂])ˣ) else w₁ j) •
          Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ τ)) (ιM₁ j x) := by
      intro j τ x
      match j with
      | none => exact hI1a τ x
      | some ℓ => exact hI1b ℓ τ x
    intro j i τ
    apply slext j
    intro x
    apply hιinj j
    have h4 := (hAL j).2.2.2.1
    have hI2w1 : ∀ y : 𝕋.objField j, ιM₁ j (WJ j (0 : Fin 2) • y) = wbar₁ j • ιM₁ j y := fun y => hI2 j (0 : Fin 2) y

    have H : ∀ y : 𝕋.objField j, w₁ j • wbar₁ j • (w₁ j)⁻¹ • ιM₁ j y = wbar₁ j • ιM₁ j y := by
      intro y
      calc w₁ j • wbar₁ j • (w₁ j)⁻¹ • ιM₁ j y
          = (w₁ j * wbar₁ j * (w₁ j)⁻¹ * (wbar₁ j)⁻¹ * wbar₁ j) • ιM₁ j y := by simp only [smul_smul]; congr 1; group
        _ = (w₁ j * wbar₁ j * (w₁ j)⁻¹ * (wbar₁ j)⁻¹) • (wbar₁ j • ιM₁ j y) := by rw [mul_smul]
        _ = (w₁ j * wbar₁ j * (w₁ j)⁻¹ * (wbar₁ j)⁻¹) • ιM₁ j (WJ j (0 : Fin 2) • y) := by rw [hI2w1]
        _ = ιM₁ j (WJ j (0 : Fin 2) • y) := hfix j _ _ h4
        _ = wbar₁ j • ιM₁ j y := hI2w1 y
    rw [mul_smul, mul_smul, hI2 j i, hI1 j τ, hI1 j τ, hI2 j i, Mumford.AmbientSemilinearAut.fracMap_smul]
    by_cases hχ : χ₁ τ = 1
    · simp only [hχ, if_true, one_smul]
    · rw [if_neg hχ]
      have hz : Mumford.AmbientSemilinearAut.fracMap (Omega.toAmbientOf ϖ₁ ρ₁ (dIso₁ τ)) (ιM₁ j x) =
          (w₁ j)⁻¹ • ιM₁ j (galJ j τ • x) := by
        rw [hI1 j τ, if_neg hχ, smul_smul, inv_mul_cancel, one_smul]
      rw [hz]
      rcases hfin2 i with rfl | rfl
      · rfl
      · show wbar₁ j • w₁ j • (w₁ j)⁻¹ • ιM₁ j (galJ j τ • x) = w₁ j • wbar₁ j • (w₁ j)⁻¹ • ιM₁ j (galJ j τ • x)
        rw [H, smul_smul (w₁ j) (w₁ j)⁻¹, mul_inv_cancel, one_smul]
  exact ⟨fun i => hWinv none i, hWcomm none 1 0, fun τ i => (hgalW none i τ).symm, fun i a => hWbase none i a,
    fun ℓ i => hWinv (some ℓ) i, fun ℓ => hWcomm (some ℓ) 1 0, fun ℓ τ i => (hgalW (some ℓ) i τ).symm,
    fun ℓ i a => hWbase (some ℓ) i a⟩

#print axioms solution

end S_CerednikDrinfeld_HeckeTower_atkinLehner_involutive_comm_galois_of_descentIntertwining_one_zero
end P2MW
export P2MW.S_CerednikDrinfeld_HeckeTower_atkinLehner_involutive_comm_galois_of_descentIntertwining_one_zero (solution)
