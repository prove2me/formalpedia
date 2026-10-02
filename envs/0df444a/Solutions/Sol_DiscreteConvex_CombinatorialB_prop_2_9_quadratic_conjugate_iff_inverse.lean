-- Prove2me | solution 1 for DiscreteConvex.CombinatorialB.prop_2_9_quadratic_conjugate_iff_inverse
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T03:10:29.191101+00:00
-- url     : https://prove2.me/submissions/6e2f7405-f709-4eca-a7f0-1db0dfb24e43

import Definitions.Def_DiscreteConvex_CombinatorialB_QF
import Definitions.Def_DiscreteConvex_CombinatorialB_CharVec
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_DiscreteConvex_CombinatorialB_Conjugate
import Mathlib.Data.EReal.Operations
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace QuadraticConjugateAlgebra
open DiscreteConvex.CombinatorialB
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def bilin (L : Matrix V V ℝ) (p q : V → ℝ) : ℝ :=
  dotProduct p (L.mulVec q)


lemma bilin_symm (L : Matrix V V ℝ) (hL : L.IsSymm) (p q : V → ℝ) :
    bilin L p q = bilin L q p := by
  simpa only [hL.eq, bilin] using Matrix.dotProduct_transpose_mulVec L p q

lemma bilin_add_left (L : Matrix V V ℝ) (p q r : V → ℝ) :
    bilin L (p+q) r = bilin L p r + bilin L q r := by
  simp only [bilin, add_dotProduct]

lemma bilin_add_right (L : Matrix V V ℝ) (p q r : V → ℝ) :
    bilin L p (q+r) = bilin L p q + bilin L p r := by
  simp only [bilin, Matrix.mulVec_add, dotProduct_add]

lemma bilin_sub_left (L : Matrix V V ℝ) (p q r : V → ℝ) :
    bilin L (p-q) r = bilin L p r - bilin L q r := by
  simp only [bilin, sub_dotProduct]

lemma bilin_sub_right (L : Matrix V V ℝ) (p q r : V → ℝ) :
    bilin L p (q-r) = bilin L p q - bilin L p r := by
  simp only [bilin, Matrix.mulVec_sub, dotProduct_sub]


@[simp] lemma qf_zero (L : Matrix V V ℝ) : QF L (0 : V → ℝ) = 0 := by
  simp [QF]

lemma qf_add (L : Matrix V V ℝ) (hL : L.IsSymm) (p q : V → ℝ) :
    QF L (p+q) = QF L p + QF L q + bilin L p q := by
  change (1/2 : ℝ) * bilin L (p+q) (p+q) =
    (1/2 : ℝ) * bilin L p p + (1/2 : ℝ) * bilin L q q + bilin L p q
  simp only [bilin_add_left, bilin_add_right]
  rw [bilin_symm L hL q p]
  ring

lemma qf_sub (L : Matrix V V ℝ) (hL : L.IsSymm) (p q : V → ℝ) :
    QF L (p-q) = QF L p + QF L q - bilin L p q := by
  change (1/2 : ℝ) * bilin L (p-q) (p-q) =
    (1/2 : ℝ) * bilin L p p + (1/2 : ℝ) * bilin L q q - bilin L p q
  simp only [bilin_sub_left, bilin_sub_right]
  rw [bilin_symm L hL q p]
  ring


lemma charVec_eq_single (i : V) : CharVec i = Pi.single i (1 : ℝ) := by
  ext j
  by_cases h : j=i <;> simp [CharVec,Pi.single_apply,h]

lemma dot_charVec_left (i : V) (p : V → ℝ) : dotProduct (CharVec i) p = p i := by
  simp [charVec_eq_single]

lemma dot_charVec_right (p : V → ℝ) (i : V) : dotProduct p (CharVec i) = p i := by
  simp [charVec_eq_single]

lemma mulVec_charVec (L : Matrix V V ℝ) (i j : V) :
    L.mulVec (CharVec j) i = L i j := by
  simp [charVec_eq_single, Matrix.mulVec_single_one]

lemma bilin_charVec_left (L : Matrix V V ℝ) (i : V) (p : V → ℝ) :
    bilin L (CharVec i) p = L.mulVec p i := by
  exact dot_charVec_left i _

lemma bilin_charVec_charVec (L : Matrix V V ℝ) (i j : V) :
    bilin L (CharVec i) (CharVec j) = L i j := by
  rw [bilin_charVec_left, mulVec_charVec]


lemma matrix_eq_of_qf_eq (L M : Matrix V V ℝ) (hL : L.IsSymm) (hM : M.IsSymm)
    (h : ∀ p : V → ℝ, QF L p = QF M p) : L = M := by
  ext i j
  have hi := h (CharVec i)
  have hj := h (CharVec j)
  have hij := h (CharVec i + CharVec j)
  rw [qf_add L hL, qf_add M hM, bilin_charVec_charVec, bilin_charVec_charVec] at hij
  linarith

end QuadraticConjugateAlgebra

#print axioms QuadraticConjugateAlgebra.qf_sub
#print axioms QuadraticConjugateAlgebra.matrix_eq_of_qf_eq



set_option autoImplicit false

namespace QuadraticConjugate
open DiscreteConvex.CombinatorialB

/-- A real upper bound attained at a witness computes the extended-real conjugate. -/
lemma conjugate_eq_of_maximizer {V : Type*} [Fintype V]
    (f : (V → ℝ) → ℝ) (p x₀ : V → ℝ) (c : ℝ)
    (hbound : ∀ x, dotProduct p x - f x ≤ c)
    (hwitness : dotProduct p x₀ - f x₀ = c) :
    Conjugate f p = (c : EReal) := by
  unfold Conjugate
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨x, rfl⟩
    rw [← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.mpr (hbound x)
  · apply le_sSup
    refine ⟨x₀, ?_⟩
    rw [← EReal.coe_sub, hwitness]

#print axioms conjugate_eq_of_maximizer
end QuadraticConjugate


set_option autoImplicit false

namespace QuadraticConjugate
open DiscreteConvex.CombinatorialB QuadraticConjugateAlgebra

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma qf_nonneg (M : Matrix V V ℝ) (hM : M.PosSemidef) (x : V → ℝ) :
    0 ≤ QF M x := by
  unfold QF
  apply mul_nonneg (by norm_num)
  simpa only [star_trivial] using hM.dotProduct_mulVec_nonneg x

lemma completing_square (M L : Matrix V V ℝ) (hM : M.IsSymm)
    (hML : M * L = 1) (p x : V → ℝ) :
    QF M (x - L.mulVec p) = QF M x + QF L p - dotProduct p x := by
  have hMp : M.mulVec (L.mulVec p) = p := by
    rw [Matrix.mulVec_mulVec, hML, Matrix.one_mulVec]
  have hQ : QF M (L.mulVec p) = QF L p := by
    unfold QF
    rw [hMp]
    rw [dotProduct_comm (L.mulVec p) p]
  have hb : bilin M x (L.mulVec p) = dotProduct p x := by
    unfold bilin
    rw [hMp, dotProduct_comm x p]
  rw [qf_sub M hM, hQ, hb]

lemma conjugate_of_mul_eq_one (M L : Matrix V V ℝ) (hM : M.IsSymm)
    (hMpsd : M.PosSemidef) (hML : M * L = 1) (p : V → ℝ) :
    Conjugate (QF M) p = ((QF L p : ℝ) : EReal) := by
  apply conjugate_eq_of_maximizer (QF M) p (L.mulVec p) (QF L p)
  · intro x
    have hn := qf_nonneg M hMpsd (x - L.mulVec p)
    rw [completing_square M L hM hML p x] at hn
    linarith
  · have h := completing_square M L hM hML p (L.mulVec p)
    rw [sub_self, qf_zero] at h
    linarith

lemma mul_eq_one_reverse_of_symm (M L : Matrix V V ℝ)
    (hM : M.IsSymm) (hL : L.IsSymm) (hML : M * L = 1) : L * M = 1 := by
  have h := congrArg Matrix.transpose hML
  simpa only [Matrix.transpose_mul, hM.eq, hL.eq, Matrix.transpose_one] using h

theorem conjugate_iff_inverse (M L : Matrix V V ℝ)
    (hMsymm : M.IsSymm) (hLsymm : L.IsSymm) (hMpd : M.PosDef) (hLpd : L.PosDef) :
    ((∀ p : V → ℝ, Conjugate (QF M) p = ((QF L p : ℝ) : EReal)) ∧
      (∀ x : V → ℝ, Conjugate (QF L) x = ((QF M x : ℝ) : EReal))) ↔ M * L = 1 := by
  constructor
  · intro hconj
    letI : Invertible M := hMpd.isUnit.invertible
    have hMI : M * M⁻¹ = 1 := Matrix.mul_inv_of_invertible M
    have hforms : ∀ p : V → ℝ, QF L p = QF M⁻¹ p := by
      intro p
      apply EReal.coe_eq_coe_iff.mp
      exact (hconj.1 p).symm.trans
        (conjugate_of_mul_eq_one M M⁻¹ hMsymm hMpd.posSemidef hMI p)
    have hLI : L = M⁻¹ := matrix_eq_of_qf_eq L M⁻¹ hLsymm hMsymm.inv hforms
    rw [hLI]
    exact hMI
  · intro hML
    refine ⟨conjugate_of_mul_eq_one M L hMsymm hMpd.posSemidef hML, ?_⟩
    exact conjugate_of_mul_eq_one L M hLsymm hLpd.posSemidef
      (mul_eq_one_reverse_of_symm M L hMsymm hLsymm hML)

#print axioms completing_square
#print axioms conjugate_of_mul_eq_one
#print axioms conjugate_iff_inverse
end QuadraticConjugate

open DiscreteConvex.CombinatorialB

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (M L : Matrix V V ℝ) (hMsymm : M.IsSymm) (hLsymm : L.IsSymm) (hMpd : M.PosDef)
    (hLpd : L.PosDef) :
    ((∀ p : V → ℝ, Conjugate (QF M) p = ((QF L p : ℝ) : EReal)) ∧
      (∀ x : V → ℝ, Conjugate (QF L) x = ((QF M x : ℝ) : EReal))) ↔ M * L = 1 := by
  exact QuadraticConjugate.conjugate_iff_inverse M L hMsymm hLsymm hMpd hLpd

#print axioms solution
