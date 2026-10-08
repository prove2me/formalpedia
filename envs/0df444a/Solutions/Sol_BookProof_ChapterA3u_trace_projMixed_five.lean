-- Prove2me | solution 1 for BookProof.ChapterA3u.trace_projMixed_five
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:46:49.572551+00:00
-- url     : https://prove2.me/submissions/57842a3a-2294-4cf2-8339-b207b79a82af

-- Generated from ChapterA3u.lean — theorem BookProof.ChapterA3u.trace_projMixed_five
import Definitions.Def_ChapterA3q
import Definitions.Def_ChapterA3r
import Mathlib
import Definitions.Def_ChapterA3u
import Definitions.Def_ChapterA3l
import Definitions.Def_ChapterA3n
import Definitions.Def_ChapterA3o
open BookProof.ChapterA3l
open BookProof.ChapterA3n
open BookProof.ChapterA3o
open BookProof.ChapterA3u


open Matrix
open scoped BigOperators


open BookProof.ChapterA3n BookProof.ChapterA3o BookProof.ChapterA3q
open BookProof.ChapterA3r

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem invariant_pow {N : ℕ} {σ : Equiv.Perm (Fin N)} {a : Idx N}
    (ha : a ∘ σ = a) (n : ℕ) (x : Fin N) : a ((σ ^ n) x) = a x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    exact congrFun ha x

private theorem constant_cycle {N : ℕ} {σ : Equiv.Perm (Fin N)} {a : Idx N}
    (ha : a ∘ σ = a) {x y : Fin N} (h : σ.SameCycle x y) : a x = a y := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn]
  exact (invariant_pow ha n x).symm

private abbrev Labels {N : ℕ} (σ : Equiv.Perm (Fin N)) :=
  Function.fixedPoints σ ⊕ σ.cycleFactorsFinset

private noncomputable def label {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Fin N) :
    Labels σ := by
  classical
  exact if hx : σ x = x then Sum.inl ⟨x, hx⟩
    else Sum.inr ⟨σ.cycleOf x, σ.cycleOf_mem_cycleFactorsFinset_iff.mpr
      (Equiv.Perm.mem_support.mpr hx)⟩

private theorem label_surjective {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Function.Surjective (label σ) := by
  classical
  intro c
  cases c with
  | inl x =>
    refine ⟨x.val, ?_⟩
    have hx : σ x.val = x.val := x.prop
    simp [label, hx]
  | inr c =>
    obtain ⟨x, hx⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.prop).1.nonempty_support
    have hn : σ x ≠ x :=
      Equiv.Perm.mem_support.mp (Equiv.Perm.mem_cycleFactorsFinset_support_le c.prop hx)
    refine ⟨x, ?_⟩
    simp only [label, dif_neg hn]
    congr 1
    apply Subtype.ext
    exact (Equiv.Perm.cycle_is_cycleOf hx c.prop).symm

private theorem label_cycle {N : ℕ} (σ : Equiv.Perm (Fin N)) {x y : Fin N}
    (h : label σ x = label σ y) : σ.SameCycle x y := by
  classical
  by_cases hx : σ x = x <;> by_cases hy : σ y = y
  · have he : x = y := by simpa [label, hx, hy, Subtype.ext_iff] using h
    exact he.sameCycle σ
  · simp [label, hx, hy] at h
  · simp [label, hx, hy] at h
  · have he : σ.cycleOf x = σ.cycleOf y := by
      simpa [label, hx, hy, Subtype.ext_iff] using h
    exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
      (Equiv.Perm.mem_support.mpr hx) (Equiv.Perm.mem_support.mpr hy)).mpr he

private theorem label_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Fin N) :
    label σ (σ x) = label σ x := by
  classical
  by_cases hx : σ x = x
  · rw [hx]
  · have hy : σ (σ x) ≠ σ x := fun h => hx (σ.injective h)
    simp only [label, dif_neg hx, dif_neg hy]
    congr 1
    apply Subtype.ext
    exact (Equiv.Perm.SameCycle.rfl.apply_left).cycleOf_eq

private noncomputable def fixedEquiv {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    {a : Idx N // a ∘ σ = a} ≃ (Labels σ → Fin 4) := by
  classical
  let r := Function.surjInv (label_surjective σ)
  have hr : ∀ c, label σ (r c) = c := Function.surjInv_eq (label_surjective σ)
  exact {
    toFun := fun a c => a.val (r c)
    invFun := fun f => ⟨fun x => f (label σ x), by
      funext x
      exact congrArg f (label_apply σ x)⟩
    left_inv := by
      intro a
      apply Subtype.ext
      funext x
      exact constant_cycle a.prop (label_cycle σ (hr (label σ x)))
    right_inv := by
      intro f
      funext c
      exact congrArg f (hr c) }

private theorem fixed_card {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (Finset.univ.filter (fun a : Idx N => a ∘ σ = a)).card =
      4 ^ ((N - σ.cycleType.sum) + σ.cycleType.card) := by
  classical
  have he := Fintype.card_congr (fixedEquiv σ)
  have hlabels : Fintype.card (Labels σ) =
      (N - σ.cycleType.sum) + σ.cycleType.card := by
    simp only [Labels, Fintype.card_sum, σ.card_fixedPoints, Fintype.card_fin,
      Fintype.card_coe, Equiv.Perm.cycleType_def, Multiset.card_map, Finset.card]
  simpa only [Fintype.card_subtype, Fintype.card_fun, Fintype.card_fin, hlabels] using he

private theorem trace_cycle {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Matrix.trace (permMat σ) =
      ((4 ^ ((N - σ.cycleType.sum) + σ.cycleType.card) : ℕ) : ℂ) := by
  classical
  have ht : Matrix.trace (permMat σ) =
      ((Finset.univ.filter (fun a : Idx N => a ∘ σ = a)).card : ℂ) := by
    rw [Finset.card_filter]
    simp only [Matrix.trace, Matrix.diag, permMat, Matrix.of_apply,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro a _
    simp only [eq_comm]
  rw [ht, fixed_card σ]


private theorem symmetric_trace : Matrix.trace (projSym 5) = 56 := by
  have hc : (∑ σ : Equiv.Perm (Fin 5),
      4 ^ ((5 - σ.cycleType.sum) + σ.cycleType.card) : ℕ) = 6720 := by
    decide
  rw [BookProof.ChapterA3n.projSym, Matrix.trace_smul, Matrix.trace_sum]
  simp only [trace_cycle, ← Nat.cast_sum, hc]
  norm_num


private theorem antisymmetric_trace : Matrix.trace (projAnti 5) = 0 := by
  have hc : (∑ σ : Equiv.Perm (Fin 5), (Equiv.Perm.sign σ : ℤ) *
      (4 ^ ((5 - σ.cycleType.sum) + σ.cycleType.card) : ℕ)) = 0 := by
    decide
  rw [BookProof.ChapterA3o.projAnti, Matrix.trace_smul, Matrix.trace_sum]
  simp only [Matrix.trace_smul, trace_cycle, signC, smul_eq_mul]
  have he : (∑ σ : Equiv.Perm (Fin 5), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ((4 ^ ((5 - σ.cycleType.sum) + σ.cycleType.card) : ℕ) : ℂ)) = 0 := by
    exact_mod_cast hc
  rw [he]
  simp


theorem solution : Matrix.trace (projMixed 5) = 968 := by
  rw [projMixed, Matrix.trace_sub, Matrix.trace_sub, symmetric_trace, antisymmetric_trace]
  have hid : Matrix.trace (1 : MN 5) = 1024 := by
    simp [Matrix.trace_one, Idx]
  rw [hid]
  norm_num

#print axioms solution

