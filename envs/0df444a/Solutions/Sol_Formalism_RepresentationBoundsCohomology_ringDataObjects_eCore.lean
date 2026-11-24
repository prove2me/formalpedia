-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.eCore
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:40.205394+00:00
-- url     : https://prove2.me/submissions/acb7ea56-caeb-4b40-a10c-8ec85fdd6fc8

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_tailProd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution {K : Type} [Field K] {S : Type} [Fintype S] [DecidableEq S] (A : Matrix S S K) (t : ℕ)
    (α : ℕ → K) (ht : 1 ≤ t)
    (hA : A.charpoly = ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α i)))
    (hα : ∀ i j, i < t → j < t → α i = α j → i = j) :
    let EA := ((List.range t).tail.map fun i => A - α i • (1 : Matrix S S K)).prod
    let δ := ∏ i ∈ Finset.Ioo 0 t, (α 0 - α i)
    EA * EA = δ • EA ∧ EA.rank = 1 ∧ A * EA = α 0 • EA ∧ δ ≠ 0 := by
  intro EA δ
  let q : Polynomial K := ∏ i ∈ Finset.Ioo 0 t, (Polynomial.X - Polynomial.C (α i))
  have hEA : EA = Polynomial.aeval A q := by
    show EA = Polynomial.aeval A (∏ i ∈ Finset.Ioo 0 t, (Polynomial.X - Polynomial.C (α i)))
    rw [← tailProd (fun i => Polynomial.X - Polynomial.C (α i)) t, map_list_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
    simp [Algebra.algebraMap_eq_smul_one]
  have hp : A.charpoly = (Polynomial.X - Polynomial.C (α 0)) * q := by
    rw [hA, Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot (by omega)]
    congr 1
  have hδq : q.eval (α 0) = δ := by
    simp [q, δ, Polynomial.eval_prod]
  have hδ : δ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    rw [Finset.mem_Ioo] at hi
    intro h
    have := hα 0 i (by omega) hi.2 (sub_eq_zero.mp h)
    omega
  have hCH : Polynomial.aeval A ((Polynomial.X - Polynomial.C (α 0)) * q) = 0 := by
    rw [← hp]; exact Matrix.aeval_self_charpoly A
  have hAE : A * EA = α 0 • EA := by
    have h1 := hCH
    rw [map_mul, ← hEA] at h1
    have h2 : Polynomial.aeval A (Polynomial.X - Polynomial.C (α 0)) = A - α 0 • 1 := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [h2, sub_mul, sub_eq_zero] at h1
    rw [h1]; simp
  have hsq : EA * EA = δ • EA := by
    obtain ⟨h, hh⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := α 0) (p := q)
    rw [hδq] at hh
    have h3 : q * q = Polynomial.C δ * q + h * ((Polynomial.X - Polynomial.C (α 0)) * q) := by
      have : q = Polynomial.C δ + (Polynomial.X - Polynomial.C (α 0)) * h := by rw [← hh]; ring
      calc q * q = (Polynomial.C δ + (Polynomial.X - Polynomial.C (α 0)) * h) * q := by rw [← this]
        _ = _ := by ring
    rw [hEA, ← map_mul, h3, map_add, map_mul, map_mul _ h, hCH, mul_zero, add_zero,
      Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  refine ⟨hsq, ?_, hAE, hδ⟩
  let φ : Module.End K (S → K) := Matrix.toLin' A
  have hφc : φ.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  apply le_antisymm
  · have h1 : LinearMap.range EA.mulVecLin ≤ φ.eigenspace (α 0) := by
      rintro _ ⟨v, rfl⟩
      rw [Module.End.mem_eigenspace_iff]
      show A.mulVec (EA.mulVec v) = α 0 • EA.mulVec v
      rw [Matrix.mulVec_mulVec, hAE, Matrix.smul_mulVec]
    have h2 : Polynomial.rootMultiplicity (α 0) φ.charpoly = 1 := by
      have hq0 : q ≠ 0 := fun h => hδ (by rw [← hδq, h]; simp)
      rw [hφc, hp, Polynomial.rootMultiplicity_mul (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) hq0),
        Polynomial.rootMultiplicity_X_sub_C_self,
        Polynomial.rootMultiplicity_eq_zero (by rw [Polynomial.IsRoot, hδq]; exact hδ)]
    calc EA.rank = Module.finrank K (LinearMap.range EA.mulVecLin) := rfl
      _ ≤ Module.finrank K (φ.eigenspace (α 0)) := Submodule.finrank_mono h1
      _ ≤ 1 := h2 ▸ LinearMap.finrank_eigenspace_le φ (α 0)
  · have hroot : φ.charpoly.IsRoot (α 0) := by
      rw [hφc, hp, Polynomial.IsRoot, Polynomial.eval_mul]; simp
    obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly φ (α 0)).mpr hroot).exists_hasEigenvector
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q) hv
    have h2 : Polynomial.aeval φ q = Matrix.toLin' EA := by
      rw [hEA]
      exact (Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix S S K ≃ₐ[K] _) A q)
    rw [h2, hδq] at h1
    by_contra hlt
    have h0 : EA.rank = 0 := by omega
    have h3 : LinearMap.range EA.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
    have h4 : EA.mulVecLin v ∈ LinearMap.range EA.mulVecLin := LinearMap.mem_range_self _ v
    rw [h3, Submodule.mem_bot] at h4
    have h5 : δ • v = 0 := by rw [← h1]; exact h4
    exact hv.2 ((smul_eq_zero.mp h5).resolve_left hδ)
end Formalism.RepresentationBoundsCohomology.ringDataObjects
