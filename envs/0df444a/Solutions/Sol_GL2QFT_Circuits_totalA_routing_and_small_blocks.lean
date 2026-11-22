-- Prove2me | solution 1 for GL2QFT.Circuits.totalA_routing_and_small_blocks
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T06:52:57.511498+00:00
-- url     : https://prove2.me/submissions/b3b0c003-6a9c-4ad5-b570-4f73768ccc97
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GL2QFT_Circuits_Leaves
import Theorems.Thm_GL2QFT_Circuits_totalA_q2_uniform
import Theorems.Thm_GL2QFT_Circuits_totalA_split_merge_uniform
import Theorems.Thm_GL2QFT_Circuits_totalA_nonhard_uniform
import Theorems.Thm_GL2QFT_Circuits_totalA_hard_route_uniform
import Theorems.Thm_GL2QFT_Circuits_qftGL2_eq_mackey_factorization
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_sum
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_seq
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_eq

open Classical
noncomputable section

namespace GL2QFT_TotalARouting_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.Supplement GL2QFT.Supplement.TotalA QAlgorithms

lemma norm_mulVec_le_of_iso {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    (M : Matrix Y X ℂ) (hM : M.conjTranspose * M = 1) (ψ : EuclideanSpace ℂ X) :
    ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))‖ ≤ ‖ψ‖ := by
  have hnorm_sq : ∀ {ι : Type} [Fintype ι] (v : ι → ℂ),
      ((∑ i : ι, ‖v i‖ ^ 2 : ℝ) : ℂ) = ∑ i : ι, star (v i) * v i := by
    intro ι _ v
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
      RCLike.star_def, mul_comm]
  have hlhs_c : ((‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))‖ ^ 2 : ℝ) : ℂ) =
      ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, hnorm_sq, hnorm_sq]
    simp_rw [Matrix.mulVec, dotProduct, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x₁ _ => ?_
    rw [Finset.sum_comm]
    have hx : ∀ x₂ : X, (∑ y : Y, star (ψ x₁) * star (M y x₁) * (M y x₂ * ψ x₂)) =
        star (ψ x₁) * ((∑ y : Y, star (M y x₁) * M y x₂) * ψ x₂) := by
      intro x₂
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => by ring
    simp_rw [hx]
    have hinner : ∀ x₂ : X, (∑ y : Y, star (M y x₁) * M y x₂) = (1 : Matrix X X ℂ) x₁ x₂ := by
      intro x₂
      have := congrFun (congrFun hM x₁) x₂
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using this
    simp_rw [hinner, Matrix.one_apply]
    simp
  have hsq : ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))‖ ^ 2 = ‖ψ‖ ^ 2 :=
    Complex.ofReal_injective hlhs_c
  nlinarith [norm_nonneg (WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))), norm_nonneg ψ]

lemma isometry_mul {X M Y : Type} [Fintype X] [DecidableEq X] [Fintype M] [DecidableEq M] [Fintype Y]
    {A : Matrix M X ℂ} {B : Matrix Y M ℂ}
    (hA : A.conjTranspose * A = 1) (hB : B.conjTranspose * B = 1) :
    (B * A).conjTranspose * (B * A) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B.conjTranspose B A, hB,
    Matrix.one_mul, hA]

lemma permMat_iso {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (hf : Function.Injective f) :
    (permMat f).conjTranspose * permMat f = 1 := by
  ext x₁ x₂
  simp only [permMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (f x₁)]
  · simp [hf.eq_iff]
  · intro y _ hy
    rw [if_neg hy, star_zero, zero_mul]
  · intro hm
    exact absurd (Finset.mem_univ _) hm

lemma splitInA_injective (D : FieldData) : Function.Injective (splitInA D) := by
  have hinv : ∀ x : InReg D, Sum.elim (Subtype.val : InRegNonHard D → InReg D) Subtype.val (splitInA D x) = x := by
    intro x
    unfold splitInA
    split_ifs <;> rfl
  intro x₁ x₂ h
  simpa [hinv] using congrArg (Sum.elim (Subtype.val : InRegNonHard D → InReg D) Subtype.val) h

lemma sumMat_iso {X₀ X₁ Y₀ Y₁ : Type}
    [Fintype X₀] [DecidableEq X₀] [Fintype X₁] [DecidableEq X₁]
    [Fintype Y₀] [DecidableEq Y₀] [Fintype Y₁] [DecidableEq Y₁]
    (M₀ : Matrix Y₀ X₀ ℂ) (M₁ : Matrix Y₁ X₁ ℂ)
    (h₀ : M₀.conjTranspose * M₀ = 1) (h₁ : M₁.conjTranspose * M₁ = 1) :
    (sumMat M₀ M₁).conjTranspose * sumMat M₀ M₁ = 1 := by
  ext x₁ x₂
  simp only [sumMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.sum_sum_type]
  cases x₁ with
  | inl a₁ =>
      cases x₂ with
      | inl a₂ =>
          have hm := congrFun (congrFun h₀ a₁) a₂
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
          simpa using hm
      | inr b₂ => simp
  | inr b₁ =>
      cases x₂ with
      | inl a₂ => simp
      | inr b₂ =>
          have hm := congrFun (congrFun h₁ b₁) b₂
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
          simpa using hm

lemma totalA_zero_of_hard_ne (D : FieldData) (y : OutReg D) (x : InReg D)
    (h : isHardOut D y ≠ isHardIn D x) : totalA D y x = 0 := by
  simp only [totalA, Matrix.of_apply]
  split_ifs with heq
  · exfalso
    apply h
    unfold isHardOut isHardIn
    rw [heq.1, heq.2]
  · rfl

def outSplitEquiv (D : FieldData) : OutRegNonHard D ⊕ OutRegHard D ≃ OutReg D where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun y := if h : isHardOut D y then .inr ⟨y, h⟩ else .inl ⟨y, Bool.eq_false_iff.mpr h⟩
  left_inv s := by
    cases s with
    | inl a => simp [a.2]
    | inr b => simp [b.2]
  right_inv y := by
    dsimp only
    split_ifs <;> rfl

lemma sum_outReg_split (D : FieldData) (g : OutReg D → ℂ) :
    (∑ y : OutReg D, g y) = (∑ y : OutRegNonHard D, g y.1) + (∑ y : OutRegHard D, g y.1) := by
  rw [← (outSplitEquiv D).sum_comp, Fintype.sum_sum_type]
  rfl

lemma submatrix_totalA_nonhard_iso (D : FieldData) :
    ((totalA D).submatrix (Subtype.val : OutRegNonHard D → OutReg D)
        (Subtype.val : InRegNonHard D → InReg D)).conjTranspose *
      (totalA D).submatrix (Subtype.val : OutRegNonHard D → OutReg D)
        (Subtype.val : InRegNonHard D → InReg D) = 1 := by
  have htot := (qftGL2_eq_mackey_factorization D).2.2.2.2.1
  ext x₁ x₂
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.one_apply]
  have himg : (∑ y : OutRegNonHard D, star (totalA D y.1 x₁.1) * totalA D y.1 x₂.1) =
      ∑ y : OutReg D, star (totalA D y x₁.1) * totalA D y x₂.1 := by
    rw [sum_outReg_split]
    have hzero : (∑ y : OutRegHard D, star (totalA D y.1 x₁.1) * totalA D y.1 x₂.1) = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [totalA_zero_of_hard_ne D y.1 x₁.1 (by rw [y.2, x₁.2]; decide), star_zero, zero_mul]
    rw [hzero, add_zero]
  rw [himg]
  have hm := congrFun (congrFun htot x₁.1) x₂.1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
  rw [hm]
  simp [Subtype.ext_iff]

lemma submatrix_totalA_hard_iso (D : FieldData) :
    ((totalA D).submatrix (Subtype.val : OutRegHard D → OutReg D)
        (Subtype.val : InRegHard D → InReg D)).conjTranspose *
      (totalA D).submatrix (Subtype.val : OutRegHard D → OutReg D)
        (Subtype.val : InRegHard D → InReg D) = 1 := by
  have htot := (qftGL2_eq_mackey_factorization D).2.2.2.2.1
  ext x₁ x₂
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.one_apply]
  have himg : (∑ y : OutRegHard D, star (totalA D y.1 x₁.1) * totalA D y.1 x₂.1) =
      ∑ y : OutReg D, star (totalA D y x₁.1) * totalA D y x₂.1 := by
    rw [sum_outReg_split]
    have hzero : (∑ y : OutRegNonHard D, star (totalA D y.1 x₁.1) * totalA D y.1 x₂.1) = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [totalA_zero_of_hard_ne D y.1 x₁.1 (by rw [y.2, x₁.2]; decide), star_zero, zero_mul]
    rw [hzero, zero_add]
  rw [himg]
  have hm := congrFun (congrFun htot x₁.1) x₂.1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
  rw [hm]
  simp [Subtype.ext_iff]

def routedB (D : FieldData) :
    Matrix (OutRegNonHard D ⊕ OutRegHard D) (InRegNonHard D ⊕ InRegHard D) ℂ :=
  sumMat
    ((totalA D).submatrix (Subtype.val : OutRegNonHard D → OutReg D)
      (Subtype.val : InRegNonHard D → InReg D))
    ((totalA D).submatrix (Subtype.val : OutRegHard D → OutReg D)
      (Subtype.val : InRegHard D → InReg D))

lemma totalA_eq_routed (D : FieldData) :
    permMat (mergeOutA D) * (routedB D * permMat (splitInA D)) = totalA D := by
  ext y x
  have hR : ∀ out, (routedB D * permMat (splitInA D)) out x = routedB D out (splitInA D x) := by
    intro out
    simp only [Matrix.mul_apply, permMat, Matrix.of_apply]
    rw [Finset.sum_eq_single (splitInA D x)]
    · rw [if_pos rfl, mul_one]
    · intro inp _ hinp; rw [if_neg hinp, mul_zero]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  simp only [Matrix.mul_apply, hR]
  by_cases hy : isHardOut D y
  · rw [Finset.sum_eq_single (Sum.inr ⟨y, hy⟩)]
    · rw [permMat, Matrix.of_apply, mergeOutA, Sum.elim_inr, if_pos rfl, one_mul]
      by_cases hx : isHardIn D x
      · simp only [routedB, splitInA, dif_pos hx, sumMat, Matrix.of_apply, Matrix.submatrix_apply]
      · have hxF : isHardIn D x = false := Bool.eq_false_iff.mpr hx
        rw [splitInA, dif_neg hx]
        simp only [routedB, sumMat, Matrix.of_apply]
        exact (totalA_zero_of_hard_ne D y x (by rw [hy, hxF]; decide)).symm
    · intro out _ hout
      cases out with
      | inl out₀ =>
          have hneq : mergeOutA D (.inl out₀) ≠ y := by
            intro heq
            have h1 : isHardOut D y = false := by
              change out₀.1 = y at heq
              rw [← heq]
              exact out₀.2
            have hcontra : false = true := h1.symm.trans hy
            exact Bool.noConfusion hcontra
          rw [permMat, Matrix.of_apply, if_neg hneq.symm, zero_mul]
      | inr out₁ =>
          have hneq : mergeOutA D (.inr out₁) ≠ y := fun heq =>
            hout (congrArg Sum.inr (Subtype.ext heq))
          rw [permMat, Matrix.of_apply, if_neg hneq.symm, zero_mul]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · have hyF : isHardOut D y = false := Bool.eq_false_iff.mpr hy
    rw [Finset.sum_eq_single (Sum.inl ⟨y, hyF⟩)]
    · rw [permMat, Matrix.of_apply, mergeOutA, Sum.elim_inl, if_pos rfl, one_mul]
      by_cases hx : isHardIn D x
      · rw [splitInA, dif_pos hx]
        simp only [routedB, sumMat, Matrix.of_apply]
        exact (totalA_zero_of_hard_ne D y x (by rw [hyF, hx]; decide)).symm
      · simp only [routedB, splitInA, dif_neg hx, sumMat, Matrix.of_apply, Matrix.submatrix_apply]
    · intro out _ hout
      cases out with
      | inl out₀ =>
          have hneq : mergeOutA D (.inl out₀) ≠ y := fun heq =>
            hout (congrArg Sum.inl (Subtype.ext heq))
          rw [permMat, Matrix.of_apply, if_neg hneq.symm, zero_mul]
      | inr out₁ =>
          have hneq : mergeOutA D (.inr out₁) ≠ y := by
            intro heq
            have h1 : isHardOut D y = true := by
              change out₁.1 = y at heq
              rw [← heq]
              exact out₁.2
            have hcontra : false = true := hyF.symm.trans h1
            exact Bool.noConfusion hcontra
          rw [permMat, Matrix.of_apply, if_neg hneq.symm, zero_mul]
    · intro hm; exact absurd (Finset.mem_univ _) hm

end GL2QFT_TotalARouting_Aux

open Classical GL2QFT GL2QFT.Circuits GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT_TotalARouting_Aux

theorem solution :
    UniformlyImplementsOn (fun D => D.q = 2) (fun D => inCodeA D) (fun D => outCodeA D)
      (fun D => totalA D) ∧
    (UniformlyImplementsOn (fun D => 2 < D.q) (fun D => D.gammaInCode) (fun D => D.gammaIrrCode)
        (fun D => Matrix.of fun out inp => if out.1 = inp.1 then D.AGamma inp.1 out.2 inp.2 else 0) →
      UniformlyImplementsOn (fun D => 2 < D.q) (fun D => inCodeA D) (fun D => outCodeA D)
        (fun D => totalA D)) := by
  refine ⟨totalA_q2_uniform, fun hAG => ?_⟩
  have hmid := uniformlyImplementsOn_sum totalA_nonhard_uniform (totalA_hard_route_uniform hAG)
  have h12 := uniformlyImplementsOn_seq totalA_split_merge_uniform.1 hmid fun D _ ψ =>
    norm_mulVec_le_of_iso _ (permMat_iso _ (splitInA_injective D)) ψ
  have h123 := uniformlyImplementsOn_seq h12 totalA_split_merge_uniform.2 fun D _ ψ =>
    norm_mulVec_le_of_iso _
      (isometry_mul (permMat_iso _ (splitInA_injective D))
        (sumMat_iso _ _ (submatrix_totalA_nonhard_iso D) (submatrix_totalA_hard_iso D))) ψ
  exact uniformlyImplementsOn_eq h123 fun D _ => totalA_eq_routed D
