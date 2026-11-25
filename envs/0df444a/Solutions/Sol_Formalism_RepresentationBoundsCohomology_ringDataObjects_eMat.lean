-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.eMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:21:16.114532+00:00
-- url     : https://prove2.me/submissions/b4e99e19-8e2c-431f-bef6-57c73f2ae604

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_eCore
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_idem_factor

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
theorem _root_.solution : StatEMat := by
  intro K _ d _ _ e x t α ht he hex hxe hpoly hα E
  obtain ⟨S, _, _, U, W, hUW, hWU⟩ := idem_factor e he
  let A : Matrix S S K := W * x * U
  have hx : x = U * A * W := by
    show x = U * (W * x * U) * W
    have : U * (W * x * U) * W = (U * W) * x * (U * W) := by simp only [Matrix.mul_assoc]
    rw [this, hUW, hex, hxe]
  have hsand : ∀ B B' : Matrix S S K, (U * B * W) * (U * B' * W) = U * (B * B') * W := by
    intro B B'
    have : (U * B * W) * (U * B' * W) = U * B * (W * U) * B' * W := by simp only [Matrix.mul_assoc]
    rw [this, hWU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have he1 : e = U * (1 : Matrix S S K) * W := by rw [Matrix.mul_one, hUW]
  have hf : ∀ i, x - α i • e = U * (A - α i • 1) * W := by
    intro i
    rw [Matrix.mul_sub, Matrix.sub_mul, ← hx, Matrix.mul_smul, Matrix.smul_mul, ← he1]
  have hlist : ∀ l : List ℕ, e * (l.map fun i => x - α i • e).prod =
      U * (l.map fun i => A - α i • (1 : Matrix S S K)).prod * W := by
    intro l
    induction l with
    | nil => simp [hUW]
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons]
      have h1 : e * ((x - α i • e) * (l.map fun i => x - α i • e).prod) =
          (x - α i • e) * (e * (l.map fun i => x - α i • e).prod) := by
        have h2 : e * (x - α i • e) = (x - α i • e) * e := by
          rw [mul_sub, sub_mul, hex, hxe, Matrix.mul_smul, Matrix.smul_mul]
        rw [← mul_assoc, h2, mul_assoc]
      rw [h1, ih, hf, hsand]
  have hchar : A.charpoly = ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α i)) := by
    rw [← hpoly]
    unfold blockPoly Matrix.charpoly Matrix.charmatrix
    let C' : K →+* Polynomial K := Polynomial.C
    have hUW' : U.map C' * W.map C' = e.map C' := by rw [← Matrix.map_mul, hUW]
    have hWU' : W.map C' * U.map C' = 1 := by
      rw [← Matrix.map_mul, hWU, Matrix.map_one _ C'.map_zero C'.map_one]
    have hx' : x.map C' = U.map C' * A.map C' * W.map C' := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← hx]
    have h1 : (Polynomial.X : Polynomial K) • e.map C' - x.map C' + (1 - e).map C' =
        1 + U.map C' * (((Polynomial.X : Polynomial K) • 1 - A.map C' - 1) * W.map C') := by
      have h2 : (1 - e).map C' = 1 - e.map C' := by
        ext i j
        by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
      rw [h2, hx', ← hUW']
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_assoc]
      abel
    rw [h1, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hWU', Matrix.mul_one]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, C']
  obtain ⟨h1, h2, h3, h4⟩ := eCore A t α ht hchar hα
  set EA := ((List.range t).tail.map fun i => A - α i • (1 : Matrix S S K)).prod with hEAdef
  have hE : E = U * EA * W := hlist _
  have hEA : EA = W * E * U := by
    rw [hE]
    have : W * (U * EA * W) * U = (W * U) * EA * (W * U) := by simp only [Matrix.mul_assoc]
    rw [this, hWU, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, h4⟩
  · rw [hE, hsand, h1, Matrix.mul_smul, Matrix.smul_mul]
  · apply le_antisymm
    · rw [← h2, hE]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    · rw [← h2]
      calc EA.rank = (W * E * U).rank := congrArg Matrix.rank hEA
        _ ≤ E.rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · rw [hE, hx, hsand, h3, Matrix.mul_smul, Matrix.smul_mul]
  · rw [hE, he1, hsand, Matrix.one_mul]
  · rw [hE, he1, hsand, Matrix.mul_one]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
