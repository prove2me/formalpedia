-- Prove2me | solution 1 for GEPPGrowth.Main.proposition_4_11
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T21:46:39.835448+00:00
-- url     : https://prove2.me/submissions/7c4e5a24-4321-415d-82e8-9905242d6c6f

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main.Prop411

/-- The set of states whose leading `d`-block dominates the identity. -/
def Good (d : ℕ) : Set CovState := {S | (block S d - 1).PosSemidef}

lemma good_closed (d : ℕ) : IsClosed (Good d) := by
  have : Good d = {S | ∀ i j : Fin d, (block S d - 1) j i = (block S d - 1) i j} ∩
      ⋂ x : Fin d → ℝ, {S | 0 ≤ x ⬝ᵥ ((block S d - 1) *ᵥ x)} := by
    ext S
    simp only [Good, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian.ext_iff, star_trivial]
  rw [this]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  · simp only [Set.ofPred_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_ <;>
      simp only [block, Matrix.sub_apply] <;> fun_prop
  · simp only [block, dotProduct, Matrix.mulVec, Matrix.sub_apply]; fun_prop

lemma good_measurable (d : ℕ) : MeasurableSet (Good d) := (good_closed d).measurableSet

/-- The deterministic core: one elimination step keeps `S ⪰ I`, for any column and pivot. -/
lemma updateAt_sub_one {d : ℕ} (S : Mat (d+1)) (hS : (S - 1).PosSemidef) (y : Vec (d+1))
    (i : Fin (d+1)) : (updateAt S y i - 1).PosSemidef := by
  set C := compressionAt y i
  set w : Vec d := fun a => ratiosAt y i (Equiv.swap 0 i a.succ)
  have hrow : ∀ a c, C a c = (if Equiv.swap 0 i a.succ = c then 1 else 0) -
      (if c = i then w a else 0) := by
    intro a c
    simp only [C, w, compressionAt, deletion, eliminationAt, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.one_apply, Matrix.vecMulVec_apply, basisVector, mul_sub]
    simp [Finset.sum_sub_distrib, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  have hC : C * C.transpose = 1 + Matrix.vecMulVec w w := by
    ext a a'
    have hne : ∀ a : Fin d, Equiv.swap 0 i a.succ ≠ i := by
      intro a h
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
      exact Fin.succ_ne_zero a h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hrow]
    simp [sub_mul, mul_sub, Finset.sum_sub_distrib, ite_mul, mul_ite, Finset.sum_ite_eq,
      Finset.sum_ite_eq', hne, Matrix.one_apply, Matrix.vecMulVec_apply, Fin.succ_inj]
  have hsplit : updateAt S y i - 1 = C * (S - 1) * C.transpose + Matrix.vecMulVec w w := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hC]
    simp only [updateAt, C]
    abel
  rw [hsplit]
  have h1 := hS.mul_mul_conjTranspose_same C
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  have h2 := Matrix.posSemidef_vecMulVec_self_star w
  rw [star_trivial] at h2
  exact h1.add h2

lemma block_embed {d : ℕ} (M : Mat d) : block (embed M) d = M := by
  ext i j; simp [block, embed]

/-- A pushforward of a measure by a map into a measurable set gives its complement mass zero. -/
lemma map_compl_eq_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (f : α → β) {G : Set β} (hG : MeasurableSet G) (hf : ∀ x, f x ∈ G) : μ.map f Gᶜ = 0 := by
  by_cases h : AEMeasurable f μ
  · rw [Measure.map_apply_of_aemeasurable h hG.compl]
    have : f ⁻¹' Gᶜ = ∅ := by ext x; simp [hf x]
    simp [this]
  · simp [Measure.map_of_not_aemeasurable h]

lemma bind_compl_eq_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (κ : α → Measure β) {G : Set β} (hG : MeasurableSet G) (hκ : ∀ᵐ x ∂μ, κ x Gᶜ = 0) :
    μ.bind κ Gᶜ = 0 := by
  by_cases h : AEMeasurable κ μ
  · rw [Measure.bind_apply hG.compl h]
    simpa using lintegral_congr_ae hκ
  · simp [Measure.bind, Measure.map_of_not_aemeasurable h]

lemma main (n t : ℕ) (ht : t < n) : covLaw n t (Good (n - t))ᶜ = 0 := by
  induction t with
  | zero =>
    simp only [covLaw, Nat.sub_zero]
    rw [Measure.dirac_apply' _ (good_measurable n).compl]
    simp [Good, block_embed, Matrix.PosSemidef.zero]
  | succ t ih =>
    obtain ⟨d, hd⟩ : ∃ d, n - t = d + 1 := ⟨n - t - 1, by omega⟩
    have hd' : n - (t + 1) = d := by omega
    simp only [covLaw]
    rw [hd, hd']
    apply bind_compl_eq_zero _ _ (good_measurable d)
    have := ih (by omega)
    rw [hd] at this
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with S hS
    simp only [Set.mem_compl_iff, not_not] at hS
    simp only [covStep]
    exact map_compl_eq_zero _ _ (good_measurable d) fun y => by
      simp only [Good, Set.mem_ofPred_eq, block_embed]
      exact updateAt_sub_one _ hS _ _

end GEPPGrowth.Main.Prop411

open GEPPGrowth.Main in
theorem solution (n t : ℕ) (ht : t < n) :
    ∀ᵐ S ∂(covLaw n t), (block S (n-t) - 1).PosSemidef :=
  measure_eq_zero_iff_ae_notMem.1 (GEPPGrowth.Main.Prop411.main n t ht) |>.mono
    fun _ h => not_not.1 h
