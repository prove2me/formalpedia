-- Prove2me | solution 1 for BornVolume.psiMat_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:49.945349+00:00
-- url     : https://prove2.me/submissions/ba3ee9e1-4ea6-4e24-9da9-ad5b08388746

module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.Block
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN
public import Theorems.Thm_BornVolume_psiMat_col_sum

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (S : ℝ) (t : Fin M → ℝ) : (psiMat S t).det = S ^ M := by
  -- Row operation: replace the last row by the sum of all rows (det unchanged,
  -- coefficient 1). The new last row is `e_last` by `psiMat_col_sum`.
  set A := psiMat S t with hA
  set B := A.updateRow (Fin.last M) (∑ k, A k) with hB
  have hdet_eq : A.det = B.det := by
    have h := Matrix.det_updateRow_sum A (Fin.last M) (fun _ => (1 : ℝ))
    simp only [one_smul] at h
    rw [hB, h]
  -- Last row of B is the indicator `[j = last]`.
  have hBlast : ∀ j, B (Fin.last M) j = if j = Fin.last M then (1 : ℝ) else 0 := by
    intro j
    have hBj : B (Fin.last M) j = ∑ k, A k j := by
      rw [hB, Matrix.updateRow_self]
      exact Finset.sum_apply j Finset.univ (fun k => A k)
    rw [hBj, hA, psiMat_col_sum]
  -- Off the last row, B agrees with A (= psiMat).
  have hBoff : ∀ i, i ≠ Fin.last M → ∀ j, B i j = A i j := by
    intro i hi j; rw [hB, Matrix.updateRow_ne hi]
  -- B is two-block-triangular for `p := (· ≠ last)`: rows that ARE last (¬p)
  -- vanish on columns that are NOT last (p).
  have htri : ∀ i, ¬ (i ≠ Fin.last M) → ∀ j, (j ≠ Fin.last M) → B i j = 0 := by
    intro i hi j hj
    rw [not_not] at hi; subst hi
    rw [hBlast, if_neg hj]
  rw [hdet_eq, B.twoBlockTriangular_det (· ≠ Fin.last M) htri]
  -- Corner block (i = last): 1×1 with entry B last last = 1.
  have hcorner : (B.toSquareBlockProp (fun i => ¬ (i ≠ Fin.last M))).det = 1 := by
    have hne : Nonempty {i : Fin (M + 1) // ¬ (i ≠ Fin.last M)} := ⟨⟨Fin.last M, by simp⟩⟩
    have hsub : Subsingleton {i : Fin (M + 1) // ¬ (i ≠ Fin.last M)} := by
      constructor; rintro ⟨a, ha⟩ ⟨b, hb⟩; rw [not_not] at ha hb; simp [ha, hb]
    rw [Matrix.det_eq_elem_of_subsingleton _ (Classical.arbitrary _)]
    obtain ⟨k, hk⟩ := (Classical.arbitrary {i : Fin (M + 1) // ¬ (i ≠ Fin.last M)})
    rw [not_not] at hk
    show B k k = 1
    rw [hk, hBlast, if_pos rfl]
  -- Big block (i ≠ last): `S·I` on the `M` `castSucc` indices, det `S^M`.
  have hbig : (B.toSquareBlockProp (· ≠ Fin.last M)).det = S ^ M := by
    have hblock : B.toSquareBlockProp (· ≠ Fin.last M)
        = Matrix.diagonal (fun _ : {i : Fin (M + 1) // i ≠ Fin.last M} => S) := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      show B a b = _
      rw [hBoff a ha b]
      obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.mpr ha
      obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.mpr hb
      simp only [hA, psiMat, Matrix.of_apply, Fin.lastCases_castSucc, Matrix.diagonal_apply]
      by_cases h : a' = b'
      · subst h; simp
      · rw [if_neg h, if_neg]; exact fun hc => h (by simpa using Subtype.ext_iff.mp hc)
    rw [hblock, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq, Nat.add_sub_cancel]
  rw [hbig, hcorner, mul_one]
end BornVolume
