-- Prove2me | solution 1 for Formalism.NG.globalConcrete_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:54:15.547643+00:00
-- url     : https://prove2.me/submissions/f8f7ffd6-14db-4f5c-94e5-f9586fa32e04

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_DetTri
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_VccSpan
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
import Theorems.Thm_Formalism_NG_GlobalDeterminantRelations_det_relMap_eq
import Theorems.Thm_Formalism_NG_genericFin
import Theorems.Thm_Formalism_NG_lenKer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
universe u v w
open GlobalDeterminantRelations
namespace Formalism.NG
theorem _root_.solution (hD : StatDescent.{u, v, w}) (hV : StatVccSpan.{u, v}) :
    CharacterColumnGlobal.{u, v, w} := by
  intro O _ _ _ X X' T T' Z p q b hT hZ d _ _ R' m g _ _ _ P hdet hφ π' ρπ hρπ α _ _ bl hbl ρk
    hsurj hblk hcard
  classical
  obtain ⟨C, hC⟩ := genericFin R' O m g α (fun k => {a // bl a = k}) hcard ρk hsurj P
  obtain ⟨f, hfT, hf⟩ := hdet (C * P)
  have hcomp : ∀ (x' : X') (v : g → EvalSp O d R' x'),
      relMap (FractionRing O) (EvalSp O d R' x') (C * P) v =
        relMap (FractionRing O) (EvalSp O d R' x') C (relMap (FractionRing O) (EvalSp O d R' x') P v) := by
    intro x' v
    funext i
    show ∑ j, (C * P) i j • v j = ∑ l, C i l • ∑ j, P l j • v j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  have hvanish : ∀ x', p x' ∉ Z → f x' = 0 := by
    intro x' hx
    obtain ⟨φ, hφ0⟩ := hφ x' hx
    let e := (homEquiv P : (Coker P →ₗ[R'] EvalSp O d R' x') ≃ₗ[FractionRing O]
      LinearMap.ker (relMap (FractionRing O) (EvalSp O d R' x') P))
    have hne : e φ ≠ 0 := fun h => hφ0 (e.injective (h.trans (map_zero e).symm))
    have hv0 : ((e φ : LinearMap.ker _) : g → EvalSp O d R' x') ≠ 0 := fun h => hne (Subtype.ext h)
    have hvk := LinearMap.mem_ker.mp (e φ).2
    have hnot : ¬ Function.Injective (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) := by
      intro hinj
      apply hv0
      apply hinj
      rw [hcomp, hvk, map_zero, map_zero]
    have hdet0 : LinearMap.det (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) = 0 := by
      by_contra hne'
      apply hnot
      have hu : IsUnit (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) :=
        (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne')
      exact ((Module.End.isUnit_iff _).mp hu).injective
    rw [GlobalDeterminantRelations.det_relMap_eq] at hdet0
    apply IsFractionRing.injective O (FractionRing O)
    rw [hf x', hdet0, map_zero]
  have hspan := hD O X X' T T' Z p q b hT hZ f hfT hvanish π'
  refine (hV O X T Z (p π') (f π') hspan).trans (le_of_eq ?_)
  have hfπ : f π' = (bigMat (fun r : R' => ρπ r) (C * P)).det := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [hf π', RingHom.map_det]
    congr 1
    refine Matrix.ext fun x y => ?_
    simp [bigMat, RingHom.mapMatrix_apply, ← hρπ]
  rcases isEmpty_or_nonempty g with hg | hg
  · have h1 : f π' = 1 := by
      rw [hfπ]
      exact Matrix.det_isEmpty
    rw [h1, IsDiscreteValuationRing.addVal_one]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Module.length_eq_zero_iff]
    exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hBT : (bigMat (fun r : R' => ρπ r) (C * P)).BlockTriangular (fun x : g × d => bl x.2) := by
    intro x y hxy
    exact hbl _ hxy
  have himage : (Finset.univ.image fun x : g × d => bl x.2) = Finset.univ.image bl := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨a, ha⟩
      exact ⟨(Classical.arbitrary g, a), ha⟩
  have hprod : ∀ (s : Finset α) (F : α → O), IsDiscreteValuationRing.addVal O (∏ k ∈ s, F k) =
      ∑ k ∈ s, IsDiscreteValuationRing.addVal O (F k) := by
    intro s F
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.prod_empty, Finset.sum_empty, IsDiscreteValuationRing.addVal_one]
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.sum_insert ha, IsDiscreteValuationRing.addVal_mul, ih]
  have hblock : ∀ k, ((bigMat (fun r : R' => ρπ r) (C * P)).toSquareBlock
      (fun x : g × d => bl x.2) k).det = (bigMat (fun r : R' => ρk k r) (C * P)).det := by
    intro k
    let eK : g × {a // bl a = k} ≃ {x : g × d // bl x.2 = k} :=
      { toFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
        invFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Matrix.det_reindex_self eK.symm]
    congr 1
    refine Matrix.ext fun x y => ?_
    obtain ⟨pp, i⟩ := x
    obtain ⟨qq, j⟩ := y
    show _ = (ρk k) ((C * P) pp qq) i j
    rw [← hblk]
    rfl
  rw [hfπ, hBT.det, hprod, himage]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hblock k, ← (lenKer : StatLenKer) O _ (bigMat (fun r : R' => ρk k r) (C * P))]
  exact hC k
end Formalism.NG
