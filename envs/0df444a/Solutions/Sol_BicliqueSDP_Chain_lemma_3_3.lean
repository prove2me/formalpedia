-- Prove2me | solution 1 for BicliqueSDP.Chain.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:55:38.665653+00:00
-- url     : https://prove2.me/submissions/64ee9f5d-1cba-4e2a-95a6-d92697e3a2a7

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false



open Matrix
open scoped BigOperators

namespace BicliqueSDP.Chain.R12

noncomputable section

lemma psd_entry_le_diag_avg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (i j : ι) :
    X i j ≤ (X i i + X j j) / 2 := by
  have hs : X j i = X i j := by simpa using hX.isHermitian.apply i j
  have h := hX.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    Matrix.mulVec_single, single_dotProduct] at h
  linarith

lemma psd_entry_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (htr : X.trace = 1) (i j : ι) :
    X i j ≤ 1 := by
  have hdiag (k : ι) : X k k ≤ 1 := by
    calc X k k ≤ ∑ l, X l l := Finset.single_le_sum (f := fun l => X l l) (fun l _ => hX.diag_nonneg) (Finset.mem_univ k)
         _ = 1 := htr
  have hpair := psd_entry_le_diag_avg hX i j
  linarith [hdiag i, hdiag j]

variable {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]

lemma h1_objective_bddAbove (E : V1 → V2 → Prop) :
    BddAbove ((fun X => frob Cmat X) '' {X | H1Feasible E X}) := by
  refine ⟨∑ _ : V1 ⊕ V2, ∑ _ : V1 ⊕ V2, (1 : ℝ), ?_⟩
  rintro z ⟨X, hX, rfl⟩
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  have hx := psd_entry_le_one hX.1 hX.2.1 u v
  cases u <;> cases v <;> simp [Cmat, Matrix.fromBlocks] <;> linarith

lemma frob_smul_right {ι : Type} [Fintype ι] (a : ℝ) (M X : Matrix ι ι ℝ) :
    frob M (a • X) = a * frob M X := by
  simp only [frob, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

lemma psd_objective_le_trace_mul_h1 (E : V1 → V2 → Prop)
    {X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ} (hp : X.PosSemidef)
    (hE : VanishesOnEdges E X) :
    frob Cmat X ≤ X.trace * h1 E := by
  obtain ht | ht := eq_or_lt_of_le hp.trace_nonneg
  · have hz : X = 0 := hp.trace_eq_zero_iff.mp ht.symm
    simp [hz, frob]
  · have hnorm : H1Feasible E (X.trace⁻¹ • X) := by
      refine ⟨hp.smul (inv_nonneg.mpr ht.le), ?_, ?_⟩
      · simp [Matrix.trace_smul, ht.ne']
      · intro u v huv
        simp [hE u v huv]
    have hle := le_csSup (h1_objective_bddAbove E) ⟨X.trace⁻¹ • X, hnorm, rfl⟩
    change frob Cmat (X.trace⁻¹ • X) ≤ h1 E at hle
    rw [frob_smul_right] at hle
    have := (div_le_iff₀ ht).mp (show frob Cmat X / X.trace ≤ h1 E by
      simpa [div_eq_mul_inv, mul_comm] using hle)
    simpa [mul_comm] using this

/-- The Frobenius pairing of two positive semidefinite real matrices is nonnegative. -/
lemma frob_nonneg_of_posSemidef {ι : Type} [Fintype ι]
    {S X : Matrix ι ι ℝ} (hS : S.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ frob S X := by
  simpa [frob, dotProduct, Matrix.mulVec, Matrix.hadamard] using
    (hS.hadamard hX).dotProduct_mulVec_nonneg (fun _ => 1)

lemma frob_add_left {ι : Type} [Fintype ι] (A B X : Matrix ι ι ℝ) :
    frob (A + B) X = frob A X + frob B X := by
  simp [frob, add_mul, Finset.sum_add_distrib]

lemma frob_sub_left {ι : Type} [Fintype ι] (A B X : Matrix ι ι ℝ) :
    frob (A - B) X = frob A X - frob B X := by
  simp [frob, sub_mul, Finset.sum_sub_distrib]

lemma frob_smul_left {ι : Type} [Fintype ι] (a : ℝ) (A X : Matrix ι ι ℝ) :
    frob (a • A) X = a * frob A X := by
  simp only [frob, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma frob_one_left {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℝ) :
    frob 1 X = X.trace := by
  simp [frob, Matrix.one_apply, Matrix.trace, Matrix.diag]

omit [DecidableEq V1] [DecidableEq V2] in
/-- The support conditions of the primal and dual make their edge pairing vanish. -/
lemma frob_eq_zero_of_inSG (E : V1 → V2 → Prop)
    {Z X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ}
    (hZ : InSG E Z) (hX : VanishesOnEdges E X) : frob Z X = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  by_cases huv : (bipGraph E).Adj u v
  · simp [hX u v huv]
  · simp [hZ.2 u v huv]

/-- Every primal feasible value is at most every dual feasible value. -/
theorem weak_duality {E : V1 → V2 → Prop}
    {X Z : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ} {lam : ℝ}
    (hX : H1Feasible E X) (hZ : H1DualFeasible E lam Z) :
    frob Cmat X ≤ lam := by
  have hnonneg := frob_nonneg_of_posSemidef hZ.2 hX.1
  rw [frob_sub_left, frob_add_left, frob_smul_left, frob_one_left,
    hX.2.1, frob_eq_zero_of_inSG E hZ.1 hX.2.2] at hnonneg
  linarith

/-- A single vertex supplies a primal feasible diagonal matrix. -/
lemma exists_h1Feasible [Nonempty (V1 ⊕ V2)] (E : V1 → V2 → Prop) :
    ∃ X, H1Feasible E X := by
  classical
  obtain ⟨k⟩ := ‹Nonempty (V1 ⊕ V2)›
  refine ⟨Matrix.diagonal (Pi.single k 1), ?_, ?_, ?_⟩
  · apply Matrix.PosSemidef.diagonal
    intro i
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · simp
  · intro u v huv
    have hne : u ≠ v := (bipGraph E).ne_of_adj huv
    simp [hne]

/-- For a nonempty vertex type, the primal supremum is bounded by each dual value. -/
theorem h1_le_dual [Nonempty (V1 ⊕ V2)] {E : V1 → V2 → Prop}
    {lam : ℝ} {Z : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ}
    (hZ : H1DualFeasible E lam Z) : h1 E ≤ lam := by
  unfold h1
  refine csSup_le ?_ ?_
  · obtain ⟨X, hX⟩ := exists_h1Feasible E
    exact ⟨frob Cmat X, X, hX, rfl⟩
  · rintro y ⟨X, hX, rfl⟩
    exact weak_duality hX hZ

end
end BicliqueSDP.Chain.R12


namespace BicliqueSDP.Chain.R12

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every real symmetric matrix becomes positive semidefinite after adding a scalar
multiple of the identity. This also applies to an empty index type. -/
lemma exists_scalar_shift_posSemidef (Y : Matrix ι ι ℝ) (hY : Y.IsSymm) :
    ∃ a : ℝ, (a • (1 : Matrix ι ι ℝ) + Y).PosSemidef := by
  have hY' : IsSelfAdjoint Y := Matrix.isHermitian_iff_isSymm.mpr hY
  have h : algebraMap ℝ (Matrix ι ι ℝ) (-(‖Y‖ * ‖(1 : Matrix ι ι ℝ)‖)) ≤ Y :=
    algebraMap_le_of_le_spectrum
      (fun x hx => (neg_le_neg (spectrum.norm_le_norm_mul_of_mem hx)).trans
        (by simpa using neg_le_neg (Real.le_norm_self (-x)))) hY'
  refine ⟨‖Y‖ * ‖(1 : Matrix ι ι ℝ)‖, ?_⟩
  simpa only [Matrix.le_iff, map_neg, Algebra.algebraMap_eq_smul_one,
    sub_neg_eq_add, add_comm] using h

/-- The symmetric part of any real matrix admits a positive semidefinite scalar shift. -/
lemma exists_symmetrized_scalar_shift_posSemidef (Y : Matrix ι ι ℝ) :
    ∃ a : ℝ, (a • (1 : Matrix ι ι ℝ) + (1 / 2 : ℝ) • (Y + Yᵀ)).PosSemidef :=
  exists_scalar_shift_posSemidef _ ((Matrix.isSymm_add_transpose_self Y).smul _)

end BicliqueSDP.Chain.R12


namespace BicliqueSDP.Chain.R12

open Matrix

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A real linear functional on matrices is the Frobenius pairing with its
values on the matrix units. -/
theorem linearMap_eq_frob_matrixUnits
    (g : Matrix ι ι ℝ →ₗ[ℝ] ℝ) (X : Matrix ι ι ℝ) :
    g X = frob (fun i j => g (Matrix.single i j 1)) X := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, frob]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hsingle : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℝ) := by
    simp
  rw [hsingle, map_smul]
  simp [mul_comm]

/-- Every real linear functional nonnegative on the positive semidefinite
cone has a positive semidefinite representing matrix on symmetric matrices. -/
theorem exists_posSemidef_frob_representation
    (g : Matrix ι ι ℝ →ₗ[ℝ] ℝ)
    (hg : ∀ X : Matrix ι ι ℝ, X.PosSemidef → 0 ≤ g X) :
    ∃ S : Matrix ι ι ℝ, S.PosSemidef ∧
      ∀ X : Matrix ι ι ℝ, X.IsSymm → g X = frob S X := by
  let T : Matrix ι ι ℝ := fun i j => g (Matrix.single i j 1)
  let S : Matrix ι ι ℝ := fun i j => (T i j + T j i) / 2
  have hSsym : S.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    dsimp [S]
    ring
  have hrepr : ∀ X : Matrix ι ι ℝ, X.IsSymm → g X = frob S X := by
    intro X hX
    have htranspose : (∑ i, ∑ j, T j i * X i j) = frob T X := by
      rw [Finset.sum_comm]
      unfold frob
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hX.apply i j]
    rw [linearMap_eq_frob_matrixUnits]
    change frob T X = frob S X
    unfold frob S
    simp_rw [add_div, add_mul, div_mul_eq_mul_div]
    simp only [Finset.sum_add_distrib, ← Finset.sum_div]
    rw [htranspose]
    unfold frob
    ring
  refine ⟨S, ?_, hrepr⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr hSsym
  intro x
  have hxx : (Matrix.vecMulVec x x).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star x
  have hnonneg := hg (Matrix.vecMulVec x x) hxx
  rw [hrepr _ (Matrix.isHermitian_iff_isSymm.mp hxx.isHermitian)] at hnonneg
  suffices hquadratic : star x ⬝ᵥ (S *ᵥ x) = frob S (Matrix.vecMulVec x x) by
    rwa [hquadratic]
  simp only [dotProduct, mulVec, star_trivial, frob,
    Matrix.vecMulVec_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end

end BicliqueSDP.Chain.R12

namespace BicliqueSDP.Chain.R12

open Matrix

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The pointed cone of positive semidefinite real matrices. -/
def psdCone : PointedCone ℝ (Matrix ι ι ℝ) where
  carrier := {X | X.PosSemidef}
  zero_mem' := Matrix.PosSemidef.zero
  add_mem' hX hY := hX.add hY
  smul_mem' a _X hX := hX.smul a.property

/-- The linear functional whose positivity on edge-zero matrices expresses primal optimality. -/
def slackFunctional (h : ℝ) (C : Matrix ι ι ℝ) : Matrix ι ι ℝ →ₗ[ℝ] ℝ where
  toFun X := h * X.trace - frob C X
  map_add' X Y := by
    simp [Matrix.trace_add, frob, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c X := by
    simp [Matrix.trace_smul, frob_smul_right, smul_eq_mul]
    ring

variable {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]

/-- The symmetric part vanishes on the graph's edges. Allowing arbitrary skew parts
makes this subspace order-generating for the full matrix space. -/
def edgeKernel (E : V1 → V2 → Prop) : Submodule ℝ (Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) where
  carrier := {X | ∀ u v, (bipGraph E).Adj u v → X u v + X v u = 0}
  zero_mem' := by intro u v h; simp
  add_mem' := by
    intro X Y hX hY u v huv
    simp only [Matrix.add_apply]
    linarith [hX u v huv, hY u v huv]
  smul_mem' := by
    intro c X hX u v huv
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_add, hX u v huv, mul_zero]

omit [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2] in
lemma vanishes_of_mem_edgeKernel (E : V1 → V2 → Prop)
    {X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ} (hp : X.PosSemidef) (hX : X ∈ edgeKernel E) :
    VanishesOnEdges E X := by
  intro u v huv
  have hs : X v u = X u v := by simpa using hp.isHermitian.apply u v
  have h := hX u v huv
  linarith

lemma edgeKernel_order_generating (E : V1 → V2 → Prop)
    (Y : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) :
    ∃ X : edgeKernel E, ((X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) + Y).PosSemidef := by
  obtain ⟨a, ha⟩ := exists_symmetrized_scalar_shift_posSemidef Y
  let X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ :=
    a • 1 + (1 / 2 : ℝ) • (Yᵀ - Y)
  have hX : X ∈ edgeKernel E := by
    intro u v huv
    have hne : u ≠ v := huv.ne
    simp [X, hne, hne.symm, Matrix.transpose_apply]
    ring
  refine ⟨⟨X, hX⟩, ?_⟩
  convert ha using 1
  ext u v
  simp [X, Matrix.transpose_apply]
  ring

omit [Fintype V1] [Fintype V2] in
lemma single_mem_edgeKernel (E : V1 → V2 → Prop) (u v : V1 ⊕ V2)
    (huv : ¬ (bipGraph E).Adj u v) : Matrix.single u v (1 : ℝ) ∈ edgeKernel E := by
  intro a b hab
  have h₁ : ¬(u = a ∧ v = b) := by
    rintro ⟨rfl, rfl⟩
    exact huv hab
  have h₂ : ¬(u = b ∧ v = a) := by
    rintro ⟨rfl, rfl⟩
    exact huv hab.symm
  simp [h₁, h₂]

lemma frob_single_one (A : Matrix ι ι ℝ) (i j : ι) :
    frob A (Matrix.single i j 1) = A i j := by
  simp [frob, Matrix.single_apply, ite_and]

omit [DecidableEq ι] in
lemma frob_add_right (A X Y : Matrix ι ι ℝ) :
    frob A (X + Y) = frob A X + frob A Y := by
  simp [frob, mul_add, Finset.sum_add_distrib]

omit [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2] in
lemma cmat_isSymm : (Cmat : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ).IsSymm := by
  ext i j
  cases i <;> cases j <;> simp [Cmat, Matrix.fromBlocks, Matrix.transpose_apply]

/-- Positive extension supplies an attaining dual slack matrix. -/
theorem dual_attainment (E : V1 → V2 → Prop) :
    ∃ Z, H1DualFeasible E (h1 E) Z := by
  let f := (slackFunctional (h1 E) (Cmat : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ)).toPMap
    (edgeKernel E)
  have hfpos : ∀ X : f.domain, (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) ∈ psdCone → 0 ≤ f X := by
    intro X hX
    have hp : (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ).PosSemidef := hX
    have he : (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) ∈ edgeKernel E := X.property
    have hle := psd_objective_le_trace_mul_h1 E hp (vanishes_of_mem_edgeKernel E hp he)
    change 0 ≤ h1 E * (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ).trace - frob Cmat (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ)
    nlinarith
  have hfdense : ∀ Y, ∃ X : f.domain, (X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) + Y ∈ psdCone := by
    intro Y
    exact edgeKernel_order_generating E Y
  obtain ⟨g, hgagree, hgpos⟩ := riesz_extension psdCone f hfpos hfdense
  obtain ⟨S, hS, hrepr⟩ := exists_posSemidef_frob_representation g hgpos
  let Z : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ := S - h1 E • 1 + Cmat
  have hSsym : S.IsSymm := Matrix.isHermitian_iff_isSymm.mp hS.isHermitian
  have hZsym : Z.IsSymm := (hSsym.sub (Matrix.isSymm_one.smul _)).add cmat_isSymm
  have hZsupport : ∀ u v, ¬ (bipGraph E).Adj u v → Z u v = 0 := by
    intro u v huv
    let M : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ := Matrix.single u v 1 + Matrix.single v u 1
    have hM : M ∈ edgeKernel E := (edgeKernel E).add_mem
      (single_mem_edgeKernel E u v huv)
      (single_mem_edgeKernel E v u (fun h => huv h.symm))
    have hMsym : M.IsSymm := by
      simpa only [M, Matrix.transpose_single] using
        Matrix.isSymm_add_transpose_self (Matrix.single u v (1 : ℝ))
    have h := (hrepr M hMsym).symm.trans (hgagree ⟨M, hM⟩)
    change frob S M = h1 E * M.trace - frob Cmat M at h
    have hpair : frob Z M = 0 := by
      simp only [Z, frob_add_left, frob_sub_left, frob_smul_left, frob_one_left]
      linarith
    have hsum : Z u v + Z v u = 0 := by
      simpa only [M, frob_add_right, frob_single_one] using hpair
    have hs := hZsym.apply u v
    linarith
  refine ⟨Z, ⟨hZsym, hZsupport⟩, ?_⟩
  have heq : h1 E • (1 : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) + Z - Cmat = S := by
    dsimp [Z]
    abel
  rwa [heq]

end
end BicliqueSDP.Chain.R12

open BicliqueSDP.Chain

/-- Strong SDP duality and attainment for the canonical biclique model. -/
theorem solution {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) :
    h1Dual E = h1 E ∧ ∃ Z, H1DualFeasible E (h1 E) Z := by
  classical
  have hatt := R12.dual_attainment E
  refine ⟨?_, hatt⟩
  by_cases hn : Nonempty (V1 ⊕ V2)
  · letI := hn
    have hb : BddBelow {lam : ℝ | ∃ Z, H1DualFeasible E lam Z} := by
      refine ⟨h1 E, ?_⟩
      rintro lam ⟨Z, hZ⟩
      exact R12.h1_le_dual hZ
    apply le_antisymm
    · exact csInf_le hb hatt
    · apply le_csInf ⟨h1 E, hatt⟩
      rintro lam ⟨Z, hZ⟩
      exact R12.h1_le_dual hZ
  · letI : IsEmpty (V1 ⊕ V2) := not_nonempty_iff.mp hn
    have hempty : {X | H1Feasible E X} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro X hX
      have ht : X.trace = 0 := by simp [Matrix.trace]
      exact zero_ne_one (ht.symm.trans hX.2.1)
    have hall : {lam : ℝ | ∃ Z, H1DualFeasible E lam Z} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro lam
      refine ⟨0, ⟨Matrix.isSymm_zero, fun _ _ _ => rfl⟩, ?_⟩
      have heq : lam • (1 : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) + 0 - Cmat = 0 :=
        Subsingleton.elim _ _
      rw [heq]
      exact Matrix.PosSemidef.zero
    simp [h1Dual, h1, hall, hempty]
