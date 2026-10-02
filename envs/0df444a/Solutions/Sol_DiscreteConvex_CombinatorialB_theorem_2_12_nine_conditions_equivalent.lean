-- Prove2me | solution 1 for DiscreteConvex.CombinatorialB.theorem_2_12_nine_conditions_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T04:15:36.983069+00:00
-- url     : https://prove2.me/submissions/1ec02fe0-57a0-4f53-936e-2c65e7c8066b

import Definitions.Def_DiscreteConvex_CombinatorialB_QF
import Definitions.Def_DiscreteConvex_CombinatorialB_CharVec
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_DiscreteConvex_CombinatorialB_OffDiagNonpos
import Definitions.Def_DiscreteConvex_CombinatorialB_DiagDominance
import Definitions.Def_DiscreteConvex_CombinatorialB_CondBPlus
import Definitions.Def_DiscreteConvex_CombinatorialB_CondCPlus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Definitions.Def_DiscreteConvex_CombinatorialB_MNatExchangeR
import Definitions.Def_DiscreteConvex_CombinatorialB_CondB
import Definitions.Def_DiscreteConvex_CombinatorialB_MemLInv
import Definitions.Def_DiscreteConvex_CombinatorialB_CondC
import Theorems.Thm_DiscreteConvex_CombinatorialB_prop_2_4_offdiag_diagdom_psd
import Mathlib.Analysis.Matrix.Order
import Definitions.Def_DiscreteConvex_CombinatorialB_CondD
import Definitions.Def_DiscreteConvex_CombinatorialB_CondDPlus
import Definitions.Def_DiscreteConvex_CombinatorialB_MNatExchangePlusR
import Mathlib.Tactic.TFAE


set_option autoImplicit false
open scoped BigOperators

namespace QuadraticNineCore
open DiscreteConvex.CombinatorialB

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def bilin (L : Matrix V V ℝ) (p q : V → ℝ) : ℝ :=
  dotProduct p (L.mulVec q)

noncomputable def rowSum (L : Matrix V V ℝ) (i : V) : ℝ := ∑ j, L i j

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

lemma bilin_smul_left (L : Matrix V V ℝ) (a : ℝ) (p q : V → ℝ) :
    bilin L (a • p) q = a * bilin L p q := by
  simp only [bilin, smul_dotProduct, smul_eq_mul]

lemma bilin_smul_right (L : Matrix V V ℝ) (a : ℝ) (p q : V → ℝ) :
    bilin L p (a • q) = a * bilin L p q := by
  simp only [bilin, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma bilin_eq_sum (L : Matrix V V ℝ) (p q : V → ℝ) :
    bilin L p q = ∑ i, ∑ j, L i j * (p i * q j) := by
  simp only [bilin, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

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

lemma qf_smul (L : Matrix V V ℝ) (a : ℝ) (p : V → ℝ) :
    QF L (a • p) = a^2 * QF L p := by
  change (1/2 : ℝ) * bilin L (a • p) (a • p) = a^2 * ((1/2 : ℝ) * bilin L p p)
  rw [bilin_smul_left, bilin_smul_right]
  ring

lemma qf_exchange (L : Matrix V V ℝ) (hL : L.IsSymm)
    (x y d : V → ℝ) (a : ℝ) :
    QF L (x-a • d) + QF L (y+a • d) =
      QF L x + QF L y - a * bilin L (x-y) d + a^2 * bilin L d d := by
  simp only [qf_sub L hL, qf_add L hL, qf_smul, bilin_smul_right, bilin_sub_left]
  change (QF L x + a^2 * ((1/2 : ℝ) * bilin L d d) - a * bilin L x d) +
      (QF L y + a^2 * ((1/2 : ℝ) * bilin L d d) + a * bilin L y d) = _
  ring

lemma qf_parallelogram (L : Matrix V V ℝ) (hL : L.IsSymm) (p q : V → ℝ) :
    QF L p + QF L q = (1/2 : ℝ) * (QF L (p+q) + QF L (p-q)) := by
  rw [qf_add L hL, qf_sub L hL]
  ring

lemma row_minimum_formula (L : Matrix V V ℝ) (p : V → ℝ) (m : ℝ) (i : V) :
    L.mulVec p i = m * rowSum L i + ∑ j, L i j * (p j-m) := by
  change (∑ j, L i j * p j) = m * (∑ j, L i j) + ∑ j, L i j * (p j-m)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma row_square_sum (L : Matrix V V ℝ) (p : V → ℝ) :
    (∑ i, ∑ j, L i j * (p i)^2) = ∑ i, rowSum L i * (p i)^2 := by
  simp only [rowSum, Finset.sum_mul]

lemma column_square_sum (L : Matrix V V ℝ) (hL : L.IsSymm) (p : V → ℝ) :
    (∑ i, ∑ j, L i j * (p j)^2) = ∑ i, rowSum L i * (p i)^2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [hL.apply i]
  simp only [rowSum, Finset.sum_mul]

lemma edge_energy_identity (L : Matrix V V ℝ) (hL : L.IsSymm) (p : V → ℝ) :
    (∑ i, ∑ j, L i j * (p i-p j)^2) =
      2 * (∑ i, rowSum L i * (p i)^2) - 2 * bilin L p p := by
  calc
    (∑ i, ∑ j, L i j * (p i-p j)^2) =
        (∑ i, ∑ j, L i j * (p i)^2) + (∑ i, ∑ j, L i j * (p j)^2) -
          2 * (∑ i, ∑ j, L i j * (p i*p j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = 2 * (∑ i, rowSum L i * (p i)^2) - 2 * bilin L p p := by
      rw [row_square_sum, column_square_sum L hL, ← bilin_eq_sum]
      ring

lemma energy_decomposition (L : Matrix V V ℝ) (hL : L.IsSymm) (p : V → ℝ) :
    QF L p = (1/2 : ℝ) * (∑ i, rowSum L i * (p i)^2) -
      (1/4 : ℝ) * (∑ i, ∑ j, L i j * (p i-p j)^2) := by
  have h := edge_energy_identity L hL p
  change (1/2 : ℝ) * bilin L p p = _
  linarith

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

lemma qf_charVec (L : Matrix V V ℝ) (i : V) : QF L (CharVec i) = (1/2 : ℝ) * L i i := by
  change (1/2 : ℝ) * bilin L (CharVec i) (CharVec i) = _
  rw [bilin_charVec_charVec]

lemma bilin_one_charVec (L : Matrix V V ℝ) (hL : L.IsSymm) (i : V) :
    bilin L (fun _ => (1 : ℝ)) (CharVec i) = rowSum L i := by
  rw [bilin_symm L hL, bilin_charVec_left]
  simp [Matrix.mulVec,dotProduct,rowSum]

lemma matrix_eq_of_qf_eq (L M : Matrix V V ℝ) (hL : L.IsSymm) (hM : M.IsSymm)
    (h : ∀ p : V → ℝ, QF L p = QF M p) : L = M := by
  ext i j
  have hi := h (CharVec i)
  have hj := h (CharVec j)
  have hij := h (CharVec i + CharVec j)
  rw [qf_add L hL, qf_add M hM, bilin_charVec_charVec, bilin_charVec_charVec] at hij
  linarith

#print axioms qf_exchange
#print axioms energy_decomposition
#print axioms matrix_eq_of_qf_eq

end QuadraticNineCore


set_option autoImplicit false
open scoped BigOperators

namespace QuadraticNineMaximum
open DiscreteConvex.CombinatorialB QuadraticNineCore

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma row_at_floor_nonpos (L : Matrix V V ℝ)
    (hOff : OffDiagNonpos L) (hRow : DiagDominance L)
    (w : V → ℝ) (c : ℝ) (hc : c ≤ 0) (hw : ∀ j, c ≤ w j)
    (i : V) (hi : w i = c) : L.mulVec w i ≤ 0 := by
  rw [row_minimum_formula L w c i]
  apply add_nonpos
  · exact mul_nonpos_of_nonpos_of_nonneg hc (hRow i)
  · apply Finset.sum_nonpos
    intro j hj
    by_cases hij : i = j
    · subst j
      simp [hi]
    · exact mul_nonpos_of_nonpos_of_nonneg (hOff i j hij) (sub_nonneg.mpr (hw j))

lemma maximum_principle (L : Matrix V V ℝ) (hLpd : L.PosDef)
    (hOff : OffDiagNonpos L) (hRow : DiagDominance L)
    (p : V → ℝ) (i : V) (hpos : 0 < L.mulVec p i) :
    0 < p i ∨ ∃ j, L.mulVec p j < 0 ∧ p j < p i := by
  by_contra h
  push_neg at h
  obtain ⟨hc, hbelow⟩ := h
  have hb : ∀ j, p j < p i → 0 ≤ L.mulVec p j := by
    intro j hj
    by_contra hn
    have hx : L.mulVec p j < 0 := lt_of_not_ge hn
    exact (not_lt_of_ge (hbelow j hx)) hj
  let v : V → ℝ := fun j => if p j < p i then p j - p i else 0
  let w : V → ℝ := p - v
  have hv_nonpos : ∀ j, v j ≤ 0 := by
    intro j
    dsimp [v]
    split_ifs with hj
    · exact sub_nonpos.mpr hj.le
    · exact le_rfl
  have hw_floor : ∀ j, p i ≤ w j := by
    intro j
    dsimp [w, v]
    split_ifs with hj <;> linarith
  have hw_eq : ∀ j, p j < p i → w j = p i := by
    intro j hj
    simp only [w, Pi.sub_apply, v, if_pos hj]
    ring
  have hdot_p : dotProduct v (L.mulVec p) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    by_cases hji : p j < p i
    · exact mul_nonpos_of_nonpos_of_nonneg (hv_nonpos j) (hb j hji)
    · simp [v, hji]
  have hdot_w : 0 ≤ dotProduct v (L.mulVec w) := by
    apply Finset.sum_nonneg
    intro j hj
    by_cases hji : p j < p i
    · exact mul_nonneg_of_nonpos_of_nonpos (hv_nonpos j)
        (row_at_floor_nonpos L hOff hRow w (p i) hc hw_floor j (hw_eq j hji))
    · simp [v, hji]
  have hv_zero : v = 0 := by
    by_contra hne
    have hpd : 0 < dotProduct v (L.mulVec v) := by
      simpa only [star_trivial] using hLpd.dotProduct_mulVec_pos hne
    have hp : p = v + w := by
      ext j
      simp only [w, Pi.add_apply, Pi.sub_apply]
      ring
    have hsum : dotProduct v (L.mulVec p) =
        dotProduct v (L.mulVec v) + dotProduct v (L.mulVec w) := by
      conv_lhs => rw [hp]
      rw [Matrix.mulVec_add, dotProduct_add]
    linarith
  have hw_p : w = p := by simp [w, hv_zero]
  have hi : w i = p i := by rw [hw_p]
  have hn := row_at_floor_nonpos L hOff hRow w (p i) hc hw_floor i hi
  rw [hw_p] at hn
  exact (not_lt_of_ge hn) hpos

lemma reverse_inverse (M L : Matrix V V ℝ)
    (hM : M.IsSymm) (hL : L.IsSymm) (hML : M * L = 1) : L * M = 1 := by
  have h := congrArg Matrix.transpose hML
  simpa only [Matrix.transpose_mul, hM.eq, hL.eq, Matrix.transpose_one] using h

lemma condCPlus_of_signs (M L : Matrix V V ℝ)
    (hMsymm : M.IsSymm) (hLsymm : L.IsSymm) (hLpd : L.PosDef)
    (hML : M * L = 1) (hOff : OffDiagNonpos L) (hRow : DiagDominance L) :
    CondCPlus M := by
  intro x i hi
  have hx : 0 < x i := by simpa [SuppPosR] using hi
  have hLM : L.mulVec (M.mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, reverse_inverse M L hMsymm hLsymm hML, Matrix.one_mulVec]
  have hp : 0 < L.mulVec (M.mulVec x) i := by rwa [hLM]
  rcases maximum_principle L hLpd hOff hRow (M.mulVec x) i hp with h | ⟨j, hj, hij⟩
  · exact Or.inl h
  · right
    refine ⟨j, ?_, hij⟩
    simpa [SuppNegR, hLM] using hj

lemma condBPlus_of_condCPlus (M : Matrix V V ℝ) (h : CondCPlus M) : CondBPlus M := by
  intro x i hi
  rcases h x i hi with hp | ⟨j, hj, hij⟩
  · exact Or.inl hp
  · right
    refine ⟨j, ?_, hij⟩
    intro hji
    subst j
    have hx : 0 < x i := by simpa [SuppPosR] using hi
    have hn : x i < 0 := by simpa [SuppNegR] using hj
    linarith

lemma signs_of_condBPlus (M L : Matrix V V ℝ) (hML : M * L = 1)
    (hB : CondBPlus M) : OffDiagNonpos L ∧ DiagDominance L := by
  have hInv : ∀ p : V → ℝ, M.mulVec (L.mulVec p) = p := by
    intro p
    rw [Matrix.mulVec_mulVec, hML, Matrix.one_mulVec]
  constructor
  · intro i j hij
    by_contra hn
    have hpos : 0 < L.mulVec (CharVec j) i := by
      rw [mulVec_charVec]
      exact lt_of_not_ge hn
    have hi : i ∈ SuppPosR (L.mulVec (CharVec j)) := by
      simpa [SuppPosR] using hpos
    have h := hB (L.mulVec (CharVec j)) i hi
    simp only [ColDot, hInv] at h
    have hzero : CharVec j i = 0 := by simp [CharVec, hij]
    rcases h with hp | ⟨k, hk, hlt⟩
    · rw [hzero] at hp
      exact (lt_irrefl 0) hp
    · rw [hzero] at hlt
      have hk0 : 0 ≤ CharVec j k := by
        unfold CharVec
        split_ifs <;> norm_num
      exact (not_lt_of_ge hk0) hlt
  · intro i
    by_contra hn
    have hrow : (∑ j, L i j) < 0 := lt_of_not_ge hn
    have hpos : 0 < L.mulVec (fun _ : V => (-1 : ℝ)) i := by
      simpa [Matrix.mulVec, dotProduct] using neg_pos.mpr hrow
    have hi : i ∈ SuppPosR (L.mulVec (fun _ : V => (-1 : ℝ))) := by
      simpa [SuppPosR] using hpos
    have h := hB (L.mulVec (fun _ : V => (-1 : ℝ))) i hi
    simp only [ColDot, hInv] at h
    rcases h with hp | ⟨j, hj, hlt⟩ <;> norm_num at *

theorem signs_iff_condCPlus (M L : Matrix V V ℝ)
    (hMsymm : M.IsSymm) (hLsymm : L.IsSymm) (hLpd : L.PosDef) (hML : M * L = 1) :
    (OffDiagNonpos L ∧ DiagDominance L) ↔ CondCPlus M := by
  constructor
  · rintro ⟨hOff, hRow⟩
    exact condCPlus_of_signs M L hMsymm hLsymm hLpd hML hOff hRow
  · intro h
    exact signs_of_condBPlus M L hML (condBPlus_of_condCPlus M h)

#print axioms maximum_principle
#print axioms signs_iff_condCPlus
end QuadraticNineMaximum


set_option autoImplicit false

namespace QuadraticNineExchange
open DiscreteConvex.CombinatorialB QuadraticNineCore

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma charVec_ne_zero (i : V) : (CharVec i : V → ℝ) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [CharVec] at hi

lemma charVec_sub_ne_zero (i j : V) (hij : i ≠ j) :
    (CharVec i - CharVec j : V → ℝ) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [CharVec, hij] at hi

lemma bilin_charVec_right (M : Matrix V V ℝ) (hM : M.IsSymm)
    (z : V → ℝ) (i : V) : bilin M z (CharVec i) = ColDot M z i := by
  rw [bilin_symm M hM, bilin_charVec_left]
  rfl

lemma bilin_exchange_direction (M : Matrix V V ℝ) (hM : M.IsSymm)
    (z : V → ℝ) (i j : V) :
    bilin M z (CharVec i - CharVec j) = ColDot M z i - ColDot M z j := by
  rw [bilin_sub_right, bilin_charVec_right M hM, bilin_charVec_right M hM]

lemma interval_iff (M : Matrix V V ℝ) (hM : M.IsSymm) (hMpd : M.PosDef)
    (x y d : V → ℝ) (hd : d ≠ 0) :
    (∃ a0 : ℝ, 0 < a0 ∧ ∀ a : ℝ, 0 ≤ a → a ≤ a0 →
      QF M x + QF M y ≥ QF M (x - a • d) + QF M (y + a • d)) ↔
      0 < bilin M (x-y) d := by
  have hb : 0 < bilin M d d := by
    simpa only [bilin, star_trivial] using hMpd.dotProduct_mulVec_pos hd
  constructor
  · rintro ⟨a0, ha0, h⟩
    have he := h a0 ha0.le le_rfl
    rw [qf_exchange M hM] at he
    by_contra hn
    have hn' : bilin M (x-y) d ≤ 0 := le_of_not_gt hn
    have hlin : a0 * bilin M (x-y) d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ha0.le hn'
    have hquad : 0 < a0^2 * bilin M d d := mul_pos (sq_pos_of_pos ha0) hb
    linarith
  · intro ha
    refine ⟨bilin M (x-y) d / bilin M d d, div_pos ha hb, ?_⟩
    intro a ha0 ha1
    have hab : a * bilin M d d ≤ bilin M (x-y) d := (le_div_iff₀ hb).mp ha1
    have he := mul_le_mul_of_nonneg_left hab ha0
    rw [qf_exchange M hM]
    nlinarith

theorem exchange_iff_condCPlus (M : Matrix V V ℝ)
    (hMsymm : M.IsSymm) (hMpd : M.PosDef) :
    MNatExchangeR (QF M) ↔ CondCPlus M := by
  constructor
  · intro h x i hi
    rcases h x 0 i (by simpa only [sub_zero] using hi) with hpair | hsingle
    · rcases hpair with ⟨j, hj, he⟩
      have hj' : j ∈ SuppNegR x := by simpa only [sub_zero] using hj
      have hij : i ≠ j := by
        intro heq
        subst j
        have hp : 0 < x i := by simpa [SuppPosR] using hi
        have hn : x i < 0 := by simpa [SuppNegR] using hj'
        linarith
      have ha := (interval_iff M hMsymm hMpd x 0 (CharVec i-CharVec j)
        (charVec_sub_ne_zero i j hij)).mp he
      rw [sub_zero, bilin_exchange_direction M hMsymm] at ha
      exact Or.inr ⟨j, hj', sub_pos.mp ha⟩
    · have ha := (interval_iff M hMsymm hMpd x 0 (CharVec i)
        (charVec_ne_zero i)).mp hsingle
      rw [sub_zero, bilin_charVec_right M hMsymm] at ha
      exact Or.inl ha
  · intro h x y i hi
    rcases h (x-y) i hi with hp | ⟨j, hj, hij'⟩
    · right
      apply (interval_iff M hMsymm hMpd x y (CharVec i) (charVec_ne_zero i)).mpr
      rwa [bilin_charVec_right M hMsymm]
    · left
      refine ⟨j, hj, ?_⟩
      have hij : i ≠ j := by
        intro heq
        subst j
        exact (lt_irrefl _) hij'
      apply (interval_iff M hMsymm hMpd x y (CharVec i-CharVec j)
        (charVec_sub_ne_zero i j hij)).mpr
      rw [bilin_exchange_direction M hMsymm]
      exact sub_pos.mpr hij'

#print axioms interval_iff
#print axioms exchange_iff_condCPlus
end QuadraticNineExchange


set_option autoImplicit false
open scoped BigOperators

namespace QuadraticNineWeakMaximum
open DiscreteConvex.CombinatorialB QuadraticNineCore

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma positive_small_perturbation (a b : ℝ) (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ 0 < a - δ*b := by
  by_cases hb : b ≤ 0
  · exact ⟨1, by norm_num, by simpa using sub_pos.mpr (lt_of_le_of_lt hb ha)⟩
  · have hb' : 0 < b := lt_of_not_ge hb
    have hden : 0 < b+1 := by linarith
    let δ := a/(b+1)
    have hδ : 0 < δ := div_pos ha hden
    have he : δ*(b+1) = a := by
      dsimp [δ]
      exact div_mul_cancel₀ a (ne_of_gt hden)
    exact ⟨δ, hδ, by nlinarith⟩

lemma unique_negative_minimum_nonpos (M L : Matrix V V ℝ)
    (hML : M * L = 1) (hB : CondB M) (p : V → ℝ) (i : V)
    (hpi : p i < 0) (hmin : ∀ j, j ≠ i → p i < p j) :
    L.mulVec p i ≤ 0 := by
  by_contra hn
  have hp : 0 < L.mulVec p i := lt_of_not_ge hn
  have hi : i ∈ SuppPosR (L.mulVec p) := by simpa [SuppPosR] using hp
  have hInv : M.mulVec (L.mulVec p) = p := by
    rw [Matrix.mulVec_mulVec, hML, Matrix.one_mulVec]
  have h := hB (L.mulVec p) i hi
  simp only [ColDot, hInv] at h
  rcases h with hz | ⟨j, hji, hj⟩
  · exact (not_le_of_gt hpi) hz
  · exact (not_le_of_gt (hmin j hji)) hj

theorem signs_of_condB (M L : Matrix V V ℝ) (hML : M * L = 1)
    (hB : CondB M) : OffDiagNonpos L ∧ DiagDominance L := by
  constructor
  · intro i j hij
    by_contra hn
    have hpos : 0 < L i j := lt_of_not_ge hn
    obtain ⟨δ, hδ, hpert⟩ := positive_small_perturbation (L i j) (L i i) hpos
    let p : V → ℝ := CharVec j - δ • CharVec i
    have hpi : p i = -δ := by simp [p, CharVec, hij]
    have hpk : ∀ k, k ≠ i → 0 ≤ p k := by
      intro k hki
      have he : p k = CharVec j k := by simp [p, CharVec, hki]
      rw [he]
      unfold CharVec
      split_ifs <;> norm_num
    have hmin : ∀ k, k ≠ i → p i < p k := by
      intro k hki
      rw [hpi]
      exact lt_of_lt_of_le (neg_neg_of_pos hδ) (hpk k hki)
    have hnonpos := unique_negative_minimum_nonpos M L hML hB p i
      (by rw [hpi]; exact neg_neg_of_pos hδ) hmin
    have he : L.mulVec p i = L i j - δ * L i i := by
      simp only [p, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, mulVec_charVec]
    rw [he] at hnonpos
    exact (not_lt_of_ge hnonpos) hpert
  · intro i
    by_contra hn
    have hrow : (∑ j, L i j) < 0 := lt_of_not_ge hn
    obtain ⟨δ, hδ, hpert⟩ := positive_small_perturbation (-(∑ j, L i j)) (L i i)
      (neg_pos.mpr hrow)
    let p : V → ℝ := (fun _ => (-1 : ℝ)) - δ • CharVec i
    have hpi : p i = -1-δ := by simp [p, CharVec]
    have hpk : ∀ k, k ≠ i → p k = -1 := by
      intro k hki
      simp [p, CharVec, hki]
    have hmin : ∀ k, k ≠ i → p i < p k := by
      intro k hki
      rw [hpi, hpk k hki]
      linarith
    have hnonpos := unique_negative_minimum_nonpos M L hML hB p i
      (by rw [hpi]; linarith) hmin
    have he : L.mulVec p i = -(∑ j, L i j) - δ * L i i := by
      simp only [p, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, mulVec_charVec]
      simp [Matrix.mulVec, dotProduct]
    rw [he] at hnonpos
    exact (not_lt_of_ge hnonpos) hpert

#print axioms signs_of_condB
end QuadraticNineWeakMaximum


set_option autoImplicit false

namespace QuadraticNineMembership
open DiscreteConvex.CombinatorialB

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma posDef_of_memLInv (M : Matrix V V ℝ) (h : MemLInv M) : M.PosDef := by
  rcases h with ⟨L, hLs, hLpd, hOff, hRow, rfl⟩
  exact hLpd.inv

lemma condCPlus_of_memLInv (M : Matrix V V ℝ) (h : MemLInv M) : CondCPlus M := by
  rcases h with ⟨L, hLs, hLpd, hOff, hRow, rfl⟩
  have hunit : IsUnit L.det := L.isUnit_iff_isUnit_det.mp hLpd.isUnit
  exact QuadraticNineMaximum.condCPlus_of_signs L⁻¹ L hLs.inv hLs hLpd
    (Matrix.nonsing_inv_mul L hunit) hOff hRow

lemma memLInv_of_condB (M : Matrix V V ℝ) (hsymm : M.IsSymm)
    (hnonsing : M.det ≠ 0) (hB : CondB M) : MemLInv M := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hnonsing
  have hML : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  obtain ⟨hOff, hRow⟩ := QuadraticNineWeakMaximum.signs_of_condB M M⁻¹ hML hB
  have hPSD := prop_2_4_offdiag_diagdom_psd M⁻¹ hsymm.inv hOff hRow
  have hPD : M⁻¹.PosDef :=
    hPSD.posDef_iff_det_ne_zero.mpr (M.isUnit_nonsing_inv_det hunit).ne_zero
  exact ⟨M⁻¹, hsymm.inv, hPD, hOff, hRow, (M.nonsing_inv_nonsing_inv hunit).symm⟩

lemma condB_of_condBPlus (M : Matrix V V ℝ) (h : CondBPlus M) : CondB M := by
  intro x i hi
  rcases h x i hi with hp | ⟨j, hj, hij⟩
  · exact Or.inl hp.le
  · exact Or.inr ⟨j, hj, hij.le⟩

lemma condC_of_condCPlus (M : Matrix V V ℝ) (h : CondCPlus M) : CondC M := by
  intro x i hi
  rcases h x i hi with hp | ⟨j, hj, hij⟩
  · exact Or.inl hp.le
  · exact Or.inr ⟨j, hj, hij.le⟩

lemma condB_of_condC (M : Matrix V V ℝ) (h : CondC M) : CondB M := by
  intro x i hi
  rcases h x i hi with hp | ⟨j, hj, hij⟩
  · exact Or.inl hp
  · right
    refine ⟨j, ?_, hij⟩
    intro hji
    subst j
    have hpos : 0 < x i := by simpa [SuppPosR] using hi
    have hneg : x i < 0 := by simpa [SuppNegR] using hj
    linarith

lemma memLInv_of_condCPlus (M : Matrix V V ℝ) (hsymm : M.IsSymm)
    (hnonsing : M.det ≠ 0) (h : CondCPlus M) : MemLInv M :=
  memLInv_of_condB M hsymm hnonsing
    (condB_of_condC M (condC_of_condCPlus M h))

#print axioms memLInv_of_condB
#print axioms condCPlus_of_memLInv
end QuadraticNineMembership


set_option autoImplicit false

namespace QuadraticNineDerivative
open DiscreteConvex.CombinatorialB QuadraticNineCore

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma bilin_neg_right (M : Matrix V V ℝ) (x d : V → ℝ) :
    bilin M x (-d) = -bilin M x d := by
  simp only [bilin, Matrix.mulVec_neg, dotProduct_neg]

lemma derivative_pair (M : Matrix V V ℝ) (hM : M.IsSymm)
    (x y : V → ℝ) (i j : V) :
    DirDeriv M x (-CharVec i + CharVec j) + DirDeriv M y (CharVec i-CharVec j) =
      ColDot M (x-y) j - ColDot M (x-y) i := by
  change bilin M x (-CharVec i + CharVec j) + bilin M y (CharVec i-CharVec j) = _
  rw [bilin_add_right, bilin_neg_right, bilin_sub_right]
  simp only [QuadraticNineExchange.bilin_charVec_right M hM]
  simp only [ColDot, Matrix.mulVec_sub, Pi.sub_apply]
  ring

lemma derivative_single (M : Matrix V V ℝ) (hM : M.IsSymm)
    (x y : V → ℝ) (i : V) :
    DirDeriv M x (-CharVec i) + DirDeriv M y (CharVec i) = -ColDot M (x-y) i := by
  change bilin M x (-CharVec i) + bilin M y (CharVec i) = _
  rw [bilin_neg_right]
  simp only [QuadraticNineExchange.bilin_charVec_right M hM]
  simp only [ColDot, Matrix.mulVec_sub, Pi.sub_apply]
  ring

theorem condD_iff_condC (M : Matrix V V ℝ) (hM : M.IsSymm) : CondD M ↔ CondC M := by
  constructor
  · intro h x i hi
    rcases h x 0 i (by simpa only [sub_zero] using hi) with hpair | hsingle
    · rcases hpair with ⟨j, hj, he⟩
      rw [derivative_pair M hM, sub_zero] at he
      exact Or.inr ⟨j, by simpa only [sub_zero] using hj, sub_nonpos.mp he⟩
    · rw [derivative_single M hM, sub_zero] at hsingle
      exact Or.inl (neg_nonpos.mp hsingle)
  · intro h x y i hi
    rcases h (x-y) i hi with hp | ⟨j, hj, hij⟩
    · right
      rw [derivative_single M hM]
      exact neg_nonpos.mpr hp
    · left
      refine ⟨j, hj, ?_⟩
      rw [derivative_pair M hM]
      exact sub_nonpos.mpr hij

theorem condDPlus_iff_condCPlus (M : Matrix V V ℝ) (hM : M.IsSymm) :
    CondDPlus M ↔ CondCPlus M := by
  constructor
  · intro h x i hi
    rcases h x 0 i (by simpa only [sub_zero] using hi) with hpair | hsingle
    · rcases hpair with ⟨j, hj, he⟩
      rw [derivative_pair M hM, sub_zero] at he
      exact Or.inr ⟨j, by simpa only [sub_zero] using hj, sub_neg.mp he⟩
    · rw [derivative_single M hM, sub_zero] at hsingle
      exact Or.inl (by linarith)
  · intro h x y i hi
    rcases h (x-y) i hi with hp | ⟨j, hj, hij⟩
    · right
      rw [derivative_single M hM]
      linarith
    · left
      refine ⟨j, hj, ?_⟩
      rw [derivative_pair M hM]
      exact sub_neg.mpr hij

#print axioms condD_iff_condC
#print axioms condDPlus_iff_condCPlus
end QuadraticNineDerivative


set_option autoImplicit false

namespace QuadraticNineWeakStrictExchange
open DiscreteConvex.CombinatorialB QuadraticNineCore

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma small_positive_linear (a b t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    ∃ α : ℝ, 0 < α ∧ α ≤ t ∧ 0 < a + α*b := by
  have hden : 0 < |b|+1 := by have := abs_nonneg b; linarith
  let α := min t (a/(|b|+1))
  have hα : 0 < α := lt_min ht (div_pos ha hden)
  have hle : α * (|b|+1) ≤ a := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hprod := mul_le_mul_of_nonneg_left (neg_abs_le b) hα.le
  exact ⟨α, hα, min_le_left _ _, by nlinarith⟩

lemma linear_coefficient_nonneg (a b : ℝ)
    (h : ∃ t : ℝ, 0 < t ∧ ∀ α : ℝ, 0 ≤ α → α ≤ t → -α*a + α^2*b ≤ 0) :
    0 ≤ a := by
  by_contra hn
  have ha : a < 0 := lt_of_not_ge hn
  rcases h with ⟨t, ht, hpoly⟩
  obtain ⟨α, hα, hαt, hlin⟩ := small_positive_linear (-a) b t (neg_pos.mpr ha) ht
  have he := hpoly α hα.le hαt
  have hp := mul_pos hα hlin
  nlinarith

lemma interval_linear_nonneg (M : Matrix V V ℝ) (hM : M.IsSymm)
    (x y d : V → ℝ)
    (h : ∃ t : ℝ, 0 < t ∧ ∀ α : ℝ, 0 ≤ α → α ≤ t →
      QF M x + QF M y ≥ QF M (x-α • d) + QF M (y+α • d)) :
    0 ≤ bilin M (x-y) d := by
  apply linear_coefficient_nonneg _ (bilin M d d)
  rcases h with ⟨t, ht, h⟩
  refine ⟨t, ht, ?_⟩
  intro α hα hαt
  have he := h α hα hαt
  rw [qf_exchange M hM] at he
  linarith

theorem condC_of_exchange (M : Matrix V V ℝ) (hM : M.IsSymm)
    (h : MNatExchangeR (QF M)) : CondC M := by
  intro x i hi
  rcases h x 0 i (by simpa only [sub_zero] using hi) with hpair | hsingle
  · rcases hpair with ⟨j, hj, he⟩
    have ha := interval_linear_nonneg M hM x 0 (CharVec i-CharVec j) he
    rw [sub_zero, QuadraticNineExchange.bilin_exchange_direction M hM] at ha
    exact Or.inr ⟨j, by simpa only [sub_zero] using hj, sub_nonneg.mp ha⟩
  · have ha := interval_linear_nonneg M hM x 0 (CharVec i) hsingle
    rw [sub_zero, QuadraticNineExchange.bilin_charVec_right M hM] at ha
    exact Or.inl ha

lemma strict_interval (M : Matrix V V ℝ) (hM : M.IsSymm) (hMpd : M.PosDef)
    (x y d : V → ℝ) (hd : d ≠ 0) (ha : 0 < bilin M (x-y) d) :
    ∃ t : ℝ, 0 < t ∧ ∀ α : ℝ, 0 < α → α < t →
      QF M x + QF M y > QF M (x-α • d) + QF M (y+α • d) := by
  have hb : 0 < bilin M d d := by
    simpa only [bilin, star_trivial] using hMpd.dotProduct_mulVec_pos hd
  refine ⟨bilin M (x-y) d / bilin M d d, div_pos ha hb, ?_⟩
  intro α hα hαt
  have he : α * bilin M d d < bilin M (x-y) d := (lt_div_iff₀ hb).mp hαt
  have hmul := mul_lt_mul_of_pos_left he hα
  rw [qf_exchange M hM]
  nlinarith

theorem exchangePlus_of_condCPlus (M : Matrix V V ℝ) (hM : M.IsSymm)
    (hMpd : M.PosDef) (h : CondCPlus M) : MNatExchangePlusR (QF M) := by
  intro x y i hi
  rcases h (x-y) i hi with hp | ⟨j, hj, hij⟩
  · right
    apply strict_interval M hM hMpd x y (CharVec i) (QuadraticNineExchange.charVec_ne_zero i)
    rwa [QuadraticNineExchange.bilin_charVec_right M hM]
  · left
    refine ⟨j, hj, ?_⟩
    have hne : i ≠ j := by intro he; subst j; exact (lt_irrefl _) hij
    apply strict_interval M hM hMpd x y (CharVec i-CharVec j)
      (QuadraticNineExchange.charVec_sub_ne_zero i j hne)
    rw [QuadraticNineExchange.bilin_exchange_direction M hM]
    exact sub_pos.mpr hij

lemma weak_interval_of_strict (f : (V → ℝ) → ℝ) (x y d : V → ℝ)
    (h : ∃ t : ℝ, 0 < t ∧ ∀ α : ℝ, 0 < α → α < t →
      f x + f y > f (x-α • d) + f (y+α • d)) :
    ∃ t : ℝ, 0 < t ∧ ∀ α : ℝ, 0 ≤ α → α ≤ t →
      f x + f y ≥ f (x-α • d) + f (y+α • d) := by
  rcases h with ⟨t, ht, h⟩
  refine ⟨t/2, by linarith, ?_⟩
  intro α hα hαt
  by_cases hz : α = 0
  · subst α
    simp
  · exact (h α (lt_of_le_of_ne hα (Ne.symm hz)) (by linarith)).le

theorem exchange_of_exchangePlus (f : (V → ℝ) → ℝ)
    (h : MNatExchangePlusR f) : MNatExchangeR f := by
  intro x y i hi
  rcases h x y i hi with hpair | hsingle
  · rcases hpair with ⟨j, hj, he⟩
    exact Or.inl ⟨j, hj, weak_interval_of_strict f x y (CharVec i-CharVec j) he⟩
  · exact Or.inr (weak_interval_of_strict f x y (CharVec i) hsingle)

#print axioms condC_of_exchange
#print axioms exchangePlus_of_condCPlus
#print axioms exchange_of_exchangePlus
end QuadraticNineWeakStrictExchange


set_option autoImplicit false
open DiscreteConvex.CombinatorialB

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hsymm : M.IsSymm) (hnonsing : M.det ≠ 0) :
    List.TFAE [MemLInv M, CondB M, CondBPlus M, CondC M, CondCPlus M, CondD M, CondDPlus M,
      MNatExchangeR (QF M), MNatExchangePlusR (QF M)] := by
  tfae_have 1 → 5 := QuadraticNineMembership.condCPlus_of_memLInv M
  tfae_have 5 → 3 := QuadraticNineMaximum.condBPlus_of_condCPlus M
  tfae_have 3 → 2 := QuadraticNineMembership.condB_of_condBPlus M
  tfae_have 2 → 1 := QuadraticNineMembership.memLInv_of_condB M hsymm hnonsing
  tfae_have 5 → 4 := QuadraticNineMembership.condC_of_condCPlus M
  tfae_have 4 → 2 := QuadraticNineMembership.condB_of_condC M
  tfae_have 4 ↔ 6 := (QuadraticNineDerivative.condD_iff_condC M hsymm).symm
  tfae_have 5 ↔ 7 := (QuadraticNineDerivative.condDPlus_iff_condCPlus M hsymm).symm
  tfae_have 5 → 9 := by
    intro h
    have hmem := QuadraticNineMembership.memLInv_of_condCPlus M hsymm hnonsing h
    exact QuadraticNineWeakStrictExchange.exchangePlus_of_condCPlus M hsymm
      (QuadraticNineMembership.posDef_of_memLInv M hmem) h
  tfae_have 9 → 8 := QuadraticNineWeakStrictExchange.exchange_of_exchangePlus (QF M)
  tfae_have 8 → 4 := QuadraticNineWeakStrictExchange.condC_of_exchange M hsymm
  tfae_finish

#print axioms solution
