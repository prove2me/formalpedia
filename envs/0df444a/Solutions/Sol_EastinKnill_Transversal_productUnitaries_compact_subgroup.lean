-- Prove2me | solution 1 for EastinKnill.Transversal.productUnitaries_compact_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T20:58:21.569808+00:00
-- url     : https://prove2.me/submissions/9d382e1e-32c1-4818-937c-628dc322bc56

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix
open EastinKnill.Transversal

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ j, Fintype (α j)]
    [∀ j, DecidableEq (α j)]

lemma prodOp_mulX (U V : ∀ j, Matrix (α j) (α j) ℂ) :
    prodOp α U * prodOp α V = prodOp α (fun j => U j * V j) := by
  ext a c
  simp only [prodOp, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, ← Finset.prod_mul_distrib]

lemma prodOp_oneX : prodOp α (fun j => (1 : Matrix (α j) (α j) ℂ)) = 1 := by
  ext a b
  simp only [prodOp, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one]
  congr 1
  exact propext ⟨fun h => funext h, fun h j => by rw [h]⟩

lemma prodOp_starX (U : ∀ j, Matrix (α j) (α j) ℂ) :
    star (prodOp α U) = prodOp α (fun j => star (U j)) := by
  rw [Matrix.star_eq_conjTranspose]
  ext a b
  simp only [Matrix.conjTranspose_apply, prodOp, Matrix.of_apply, Matrix.star_eq_conjTranspose]
  rw [star_prod]

end

lemma unitary_compactX (n : Type*) [Fintype n] [DecidableEq n] :
    IsCompact (unitary (Matrix n n ℂ) : Set (Matrix n n ℂ)) := by
  have hK0 : IsCompact (Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hK : IsCompact ((Set.pi Set.univ fun _ : n => Set.pi Set.univ fun _ : n =>
      Metric.closedBall (0 : ℂ) 1 : Set (n → n → ℂ)) : Set (Matrix n n ℂ)) := hK0
  refine hK.of_isClosed_subset (isClosed_unitary (R := Matrix n n ℂ)) ?_
  intro (A : Matrix n n ℂ) hA
  have hcol : ∀ i j, ‖A i j‖ ≤ 1 := by
    intro i j
    have hm : (star A * A : Matrix n n ℂ) = 1 := Unitary.star_mul_self_of_mem (R := Matrix n n ℂ) hA
    have h1 : ∑ k, star A j k * A k j = 1 := by
      have := congrArg (fun M : Matrix n n ℂ => M j j) hm
      simpa [Matrix.mul_apply] using this
    have h2 : ∑ k, ‖A k j‖ ^ 2 = 1 := by
      have : ∑ k, ((‖A k j‖ ^ 2 : ℝ) : ℂ) = 1 := by
        rw [← h1]; refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.star_apply, RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact_mod_cast this
    have h3 : ‖A i j‖ ^ 2 ≤ 1 := by
      rw [← h2]
      exact Finset.single_le_sum (f := fun k => ‖A k j‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
    nlinarith [norm_nonneg (A i j)]
  exact fun i _ j _ => by simpa using hcol i j

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ j, Fintype (α j)]
    [∀ j, DecidableEq (α j)] :
    ∃ T : Subgroup (Matrix.unitaryGroup (∀ j, α j) ℂ),
      (T : Set (Matrix.unitaryGroup (∀ j, α j) ℂ)) = productUnitaries α ∧
      IsCompact (T : Set (Matrix.unitaryGroup (∀ j, α j) ℂ)) := by
  have hmem : ∀ V : ∀ j, Matrix.unitaryGroup (α j) ℂ,
      prodOp α (fun j => (V j : Matrix (α j) (α j) ℂ)) ∈ Matrix.unitaryGroup (∀ j, α j) ℂ := by
    intro V
    rw [Matrix.mem_unitaryGroup_iff, prodOp_starX, prodOp_mulX]
    have : (fun j => (V j : Matrix (α j) (α j) ℂ) * star (V j : Matrix (α j) (α j) ℂ)) =
          fun j => (1 : Matrix (α j) (α j) ℂ) := funext fun j => Matrix.mem_unitaryGroup_iff.mp (V j).2
    rw [this, prodOp_oneX]
  let f : (∀ j, Matrix.unitaryGroup (α j) ℂ) → Matrix.unitaryGroup (∀ j, α j) ℂ :=
    fun V => ⟨_, hmem V⟩
  have hrange : Set.range f = productUnitaries α := by
    ext U; constructor
    · rintro ⟨V, rfl⟩; exact ⟨V, rfl⟩
    · rintro ⟨V, hV⟩; exact ⟨V, Subtype.ext hV.symm⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    apply continuous_pi; intro a; apply continuous_pi; intro b
    simp only [prodOp, Matrix.of_apply]
    apply continuous_finsetProd; intro j _
    have h1 : Continuous fun V : (∀ j, Matrix.unitaryGroup (α j) ℂ) => V j := continuous_apply j
    have h2 : Continuous fun W : Matrix.unitaryGroup (α j) ℂ => (W : Matrix (α j) (α j) ℂ) :=
      continuous_subtype_val
    have h3 : Continuous fun M : Matrix (α j) (α j) ℂ => M (a j) (b j) := continuous_apply_apply _ _
    exact h3.comp (h2.comp h1)
  haveI : ∀ j, CompactSpace (Matrix.unitaryGroup (α j) ℂ) := fun j =>
    isCompact_iff_compactSpace.mp (unitary_compactX (α j))
  refine ⟨{ carrier := productUnitaries α, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl, ?_⟩
  · rintro U U' ⟨V, hV⟩ ⟨V', hV'⟩
    refine ⟨fun j => V j * V' j, ?_⟩
    show U.1 * U'.1 = _
    rw [hV, hV', prodOp_mulX]; rfl
  · refine ⟨fun j => 1, ?_⟩
    show (1 : Matrix _ _ ℂ) = _
    rw [← prodOp_oneX]; rfl
  · rintro U ⟨V, hV⟩
    refine ⟨fun j => (V j)⁻¹, ?_⟩
    show star U.1 = _
    rw [hV, prodOp_starX]; rfl
  · show IsCompact (productUnitaries α)
    rw [← hrange]; exact isCompact_range hf
