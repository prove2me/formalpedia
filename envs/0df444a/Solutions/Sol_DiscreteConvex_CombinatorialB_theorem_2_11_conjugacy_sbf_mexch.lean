-- Prove2me | solution 1 for DiscreteConvex.CombinatorialB.theorem_2_11_conjugacy_sbf_mexch
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T04:07:42.035742+00:00
-- url     : https://prove2.me/submissions/16be6375-da50-456c-9b08-54359fb33634

import Mathlib.Tactic.SplitIfs
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
import Definitions.Def_DiscreteConvex_CombinatorialB_MNatExchangeR
import Theorems.Thm_DiscreteConvex_CombinatorialB_theorem_2_7_offdiag_diagdom_iff_translation_submodular
import Theorems.Thm_DiscreteConvex_CombinatorialB_prop_2_9_quadratic_conjugate_iff_inverse


set_option autoImplicit false
open scoped BigOperators

namespace QuadraticMissionCore
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

end QuadraticMissionCore


set_option autoImplicit false
open scoped BigOperators

namespace QuadraticMissionMaximum
open DiscreteConvex.CombinatorialB QuadraticMissionCore

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
end QuadraticMissionMaximum


set_option autoImplicit false

namespace QuadraticMissionExchange
open DiscreteConvex.CombinatorialB QuadraticMissionCore

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
end QuadraticMissionExchange

open DiscreteConvex.CombinatorialB

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (M L : Matrix V V ℝ) (hMsymm : M.IsSymm) (hLsymm : L.IsSymm) (hMpd : M.PosDef)
    (hLpd : L.PosDef)
    (hconj : (∀ p : V → ℝ, Conjugate (QF M) p = ((QF L p : ℝ) : EReal)) ∧
      (∀ x : V → ℝ, Conjugate (QF L) x = ((QF M x : ℝ) : EReal))) :
    TranslationSubmodular (QF L) ↔ MNatExchangeR (QF M) := by
  have hML : M * L = 1 :=
    (prop_2_9_quadratic_conjugate_iff_inverse M L hMsymm hLsymm hMpd hLpd).mp hconj
  exact (theorem_2_7_offdiag_diagdom_iff_translation_submodular L hLsymm).symm.trans
    ((QuadraticMissionMaximum.signs_iff_condCPlus M L hMsymm hLsymm hLpd hML).trans
      (QuadraticMissionExchange.exchange_iff_condCPlus M hMsymm hMpd).symm)

#print axioms solution
