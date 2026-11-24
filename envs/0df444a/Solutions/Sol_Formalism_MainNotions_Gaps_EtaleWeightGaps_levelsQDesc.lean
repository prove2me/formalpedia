-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.levelsQDesc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:56:23.030506+00:00
-- url     : https://prove2.me/submissions/84f8e9a5-8861-4623-9943-750a67c1cb39

import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LevelsQDesc
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_isLattice_span_image_alt
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_localStepDescent
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_localStepLevelsQ
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_ql_span_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps
open Module Formalism.LatticeBaseChangeAlt Formalism.LatticeBaseChangeAlt.BQuot Formalism.MainNotions.Gaps.T0
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (ι : Type) [Fintype ι] (ep f : ι → ℕ) (ν v : ι → ℝ) (νs c' : ℝ) (T R I : ℕ)
    (hep : ∀ z, 1 ≤ ep z) (hT : 1 ≤ T) (hc' : 0 ≤ c') (hv : ∀ z, 0 ≤ v z) (hν : ∀ z, ν z ≤ νs + c' * v z)
    (O O' K K' V V₁ W : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] [AddCommGroup W] [Module O' W]
    (j : V →ₗ[K] V₁) (hj : IsBaseChange K' j)
    (ϖ : O) (hϖ : Irreducible ϖ) (hϖ' : Irreducible (algebraMap O O' ϖ))
    (M Θ Mgg : Submodule O V) (N₁ Z Zm N' : Submodule O' V₁) (e n q : ℕ) (th : Fin n → V)
    (AA AA' N₁' : Submodule O' W) (ρ : ↥N' →ₗ[O'] W)
    (hM : Formalism.LatticeIndexTer.IsLat O K V M) (hΘ : Formalism.LatticeIndexTer.IsLat O K V Θ)
    (h1 : N₁ ⊔ Z ≤ Submodule.span O' (j '' (Θ : Set V))) (h2 : ∀ i, th i ∈ M) (h3 : ∀ i, th i ∈ Θ)
    (h4 : Mgg ≤ M)
    (h5 : ∀ x ∈ Mgg, j x ∈ Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁))
    (h6 : Module.length O (↥M ⧸ (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype) ≤ (q : ℕ∞))
    (h8 : (Submodule.span O' (j '' (M : Set V))).map
        ((algebraMap O O' ϖ ^ e) • (LinearMap.id : V₁ →ₗ[O'] V₁)) ⊓
      (Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁)).restrictScalars O' ≤ N')
    (h9 : N₁ ≤ N') (h10 : Z ≤ Zm) (h11 : Zm ≤ N') (h12 : ∀ x, ρ x ∈ AA')
    (h13 : LinearMap.ker ρ = Zm.comap N'.subtype) (h14 : (N₁.comap N'.subtype).map ρ = N₁') (h15 : N₁' ≤ AA)
    (h16 : AA ≤ AA')
    (h17 : Module.length O' (↥Zm ⧸ Z.comap Zm.subtype) ≠ ⊤)
    (hcase : ((T : ℝ) * νs ≤ (e : ℝ) ∧ ∀ z, ∃ m : ℤ, (ep z : ℝ) * ν z = m) ∨ (T : ℝ) * νs + 1 ≤ (e : ℝ))
    (hA : Module.length O' (↥AA' ⧸ AA.comap AA'.subtype) ≤
      ((R * ∑ z, (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat * f z : ℕ) : ℕ∞))
    (hN : Module.length O' (↥AA ⧸ N₁'.comap AA.subtype) ≤ ((R * I : ℕ) : ℕ∞))
    (V' : Submodule K V) :
    (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
      (e : ℝ) * (finrank K V' : ℝ) +
          (R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
          ((Module.length O' (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ) := by
  let jj : V →ₛₗ[algebraMap O O'] V₁ :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a x => by
        show j (a • x) = algebraMap O O' a • j x
        rw [← algebraMap_smul K a x, j.map_smul, ← algebraMap_smul K' (algebraMap O K a) (j x),
          ← IsScalarTower.algebraMap_apply O K K', IsScalarTower.algebraMap_apply O O' K',
          algebraMap_smul] }
  have hlen : ql (Submodule.span O' (j '' (M : Set V)))
      (Submodule.span O' (j '' (Mgg : Set V)) ⊔ Submodule.span O' (Set.range fun i => j (th i))) ≤
      ql M (Mgg ⊔ Submodule.span O (Set.range th)) := by
    refine ql_span_le ϖ hϖ hϖ' jj M _ _ ?_
    have hle : Mgg ⊔ Submodule.span O (Set.range th) ≤
        (Submodule.span O' (j '' (Mgg : Set V)) ⊔
          Submodule.span O' (Set.range fun i => j (th i))).comap jj := by
      refine sup_le (fun x hx => ?_) (Submodule.span_le.2 ?_)
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨x, hx, rfl⟩)
      · rintro _ ⟨i, rfl⟩
        exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
    exact fun x hx => hle hx
  have h5' : Submodule.span K' ((Submodule.span O' (j '' (Mgg : Set V)) : Submodule O' V₁) : Set V₁) ≤
      Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁) := by
    rw [Submodule.span_le]
    have hle : Submodule.span O' (j '' (Mgg : Set V)) ≤
        (Submodule.span K' ((N₁ ⊔ Z : Submodule O' V₁) : Set V₁)).restrictScalars O' := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact h5 x hx
    exact fun x hx => hle hx
  have : FiniteDimensional K' V₁ := Module.Finite.equiv hj.equiv
  have h := localStepLevelsQ ι ep f ν v νs c' T R I hep hT hc' hv hν O' K' V₁ W (algebraMap O O' ϖ) hϖ'
    (Submodule.span O' (j '' (M : Set V))) (Submodule.span O' (j '' (Θ : Set V))) N₁ Z Zm N'
    (Submodule.span O' (j '' (Mgg : Set V))) e n q (fun i => j (th i)) AA AA' N₁' ρ
    (isLattice_span_image_alt O O' K K' V V₁ j hj M hM) (isLattice_span_image_alt O O' K K' V V₁ j hj Θ hΘ) h1
    (fun i => Submodule.subset_span ⟨th i, h2 i, rfl⟩) (fun i => Submodule.subset_span ⟨th i, h3 i, rfl⟩)
    (Submodule.span_mono (Set.image_mono h4)) h5' (hlen.trans h6) h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 hcase hA hN
    (Submodule.span K' (j '' (V' : Set V)))
  have hd := localStepDescent O O' K K' V V₁ j hj ϖ hϖ hϖ' M Θ V' hM hΘ 1
    ((R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
      ((Module.length O' (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ)) 0 e (by linarith)
  linarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps
