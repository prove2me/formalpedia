-- Prove2me | solution 1 for CompressedOracleDuality.LabelSymmetric.equation_24
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T03:28:15.445637+00:00
-- url     : https://prove2.me/submissions/86a6c105-227c-4106-b5ee-33467e02eb22

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Database

open QAlgorithms
open scoped BigOperators MatrixOrder ComplexOrder Matrix

noncomputable section
namespace CompressedOracleDuality.LabelSymmetric.E24

variable {n : ℕ}

lemma hnn (G : DBMatrix n) (hG : G.PosSemidef) : 0 ≤ G := Matrix.nonneg_iff_posSemidef.mpr hG

lemma sa (G : DBMatrix n) : (sqrtGram G)ᴴ = sqrtGram G := by
  have h : IsSelfAdjoint (sqrtGram G) := (CFC.sqrt_nonneg G).isSelfAdjoint
  exact h

lemma entry (G : DBMatrix n) (i j : Database n) : sqrtGram G j i = star (sqrtGram G i j) := by
  have := congrFun (congrFun (sa G) j) i
  rw [Matrix.conjTranspose_apply] at this
  rw [← this]

lemma sq (G : DBMatrix n) (hG : G.PosSemidef) : sqrtGram G * sqrtGram G = G :=
  CFC.sqrt_mul_sqrt_self G (hnn G hG)

lemma marg (G : DBMatrix n) (hG : G.PosSemidef) (D : Database n) :
    ∑ E, jointLaw G (D, E) = (G D D).re := by
  have h := congrFun (congrFun (sq G hG) D) D
  rw [Matrix.mul_apply] at h
  rw [← h, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro E _
  rw [entry G D E, jointLaw]
  simp [Complex.normSq_apply, Complex.mul_re]


lemma valid (G : DBMatrix n) (hG : G.PosSemidef) (hV : ValidMatrix G) : ValidMatrix (sqrtGram G) := by
  intro w D x
  set S := sqrtGram G with hS
  set Dy : Label n → Database n := fun y => Function.update D x (some y) with hDy
  have hcol : ∀ E, ∑ y, G (Dy y) E = 0 := by
    intro E
    have := hV (Pi.single E 1) D x
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hDy] using this
  set r : Database n → ℂ := fun E => ∑ y, S (Dy y) E with hr
  have key : (∑ E, ((Complex.normSq (r E) : ℝ) : ℂ)) = 0 := by
    have e1 : ∀ E, ((Complex.normSq (r E) : ℝ) : ℂ) =
        ∑ y, ∑ y', S (Dy y') E * S E (Dy y) := by
      intro E
      rw [← Complex.mul_conj, hr]
      simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro y _
      apply Finset.sum_congr rfl; intro y' _
      rw [hS, entry G (Dy y) E]; rfl
    simp_rw [e1]
    rw [Finset.sum_comm]
    have e2 : ∀ y, ∑ E, ∑ y', S (Dy y') E * S E (Dy y) = ∑ y', G (Dy y') (Dy y) := by
      intro y
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro y' _
      rw [← sq G hG, Matrix.mul_apply]
    simp_rw [e2]
    simp [hcol]
  have key' : ∑ E, Complex.normSq (r E) = 0 := by exact_mod_cast key
  have hz : ∀ E, r E = 0 := by
    intro E
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun E _ => Complex.normSq_nonneg (r E))).mp key'
      E (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.mp this
  show ∑ y, (S.mulVec w) (Dy y) = 0
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp [show ∀ E, ∑ y, S (Dy y) E = 0 from hz]

theorem main {n : ℕ} (G : DBMatrix n) (hG : G.PosSemidef) (htr : G.trace = 1) :
    (∀ D₁ D₂, jointLaw G (D₁, D₂) = jointLaw G (D₂, D₁)) ∧
    (∀ D₁, ∑ D₂, jointLaw G (D₁, D₂) = (G D₁ D₁).re) ∧
    (∀ D₂, ∑ D₁, jointLaw G (D₁, D₂) = (G D₂ D₂).re) ∧
    (ValidMatrix G → ValidMatrix (sqrtGram G)) := by
  have hsym : ∀ D₁ D₂, jointLaw G (D₁, D₂) = jointLaw G (D₂, D₁) := by
    intro D₁ D₂
    simp only [jointLaw]
    rw [entry G D₁ D₂]
    exact (Complex.normSq_conj _).symm
  refine ⟨hsym, marg G hG, fun D₂ => ?_, valid G hG⟩
  rw [← marg G hG D₂]
  exact Finset.sum_congr rfl (fun D₁ _ => hsym D₁ D₂)

end CompressedOracleDuality.LabelSymmetric.E24

namespace CompressedOracleDuality.LabelSymmetric

theorem equation_24 {n : ℕ} (G : DBMatrix n) (hG : G.PosSemidef)
    (htr : G.trace = 1) :
    (∀ D₁ D₂, jointLaw G (D₁, D₂) = jointLaw G (D₂, D₁)) ∧
    (∀ D₁, ∑ D₂, jointLaw G (D₁, D₂) = (G D₁ D₁).re) ∧
    (∀ D₂, ∑ D₁, jointLaw G (D₁, D₂) = (G D₂ D₂).re) ∧
    (ValidMatrix G → ValidMatrix (sqrtGram G)) :=
  E24.main G hG htr

end CompressedOracleDuality.LabelSymmetric

open CompressedOracleDuality.LabelSymmetric in
theorem solution {n : ℕ} (G : DBMatrix n) (hG : G.PosSemidef)
    (htr : G.trace = 1) :
    (∀ D₁ D₂, jointLaw G (D₁, D₂) = jointLaw G (D₂, D₁)) ∧
    (∀ D₁, ∑ D₂, jointLaw G (D₁, D₂) = (G D₁ D₁).re) ∧
    (∀ D₂, ∑ D₁, jointLaw G (D₁, D₂) = (G D₂ D₂).re) ∧
    (ValidMatrix G → ValidMatrix (sqrtGram G)) :=
  CompressedOracleDuality.LabelSymmetric.equation_24 G hG htr
