-- Prove2me | solution 1 for DensInertW.an_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:29.504023+00:00
-- url     : https://prove2.me/submissions/f0e27636-508f-485e-87bf-a5ed64b628f8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeel
import Theorems.Thm_DensInertW_Sub_hf_symm
import Theorems.Thm_DensInertW_Sub_q_ne_zero_of_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open DensInertW
open DensInertW.Sub
variable {L : Type} [Field L]
open Classical
namespace DensInertW
theorem _root_.solution [Fintype L] {n m q : ℕ} {M : Matrix (Fin n) (Fin n) L}
    (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hM : IsHerm q M) (W : Submodule L (Fin n → L)) (b : L) (w : Fin m → L) (x : Fin n → L)
    (hxW : x ∈ W) (hxx : hf q M x x = b) (hb : b ≠ 0) :
    (Finset.univ.filter (fun X : Fin (m + 1) → Fin n → L =>
        anP q M W (Matrix.diagonal (Fin.cons b w : Fin (m + 1) → L)) X ∧ X 0 = x)).card =
      (Finset.univ.filter (anP q M (W ⊓ LinearMap.ker (hfL q M x)) (Matrix.diagonal w))).card := by
  have hq := q_ne_zero_of_inv hinv
  symm
  refine Finset.card_nbij' (fun U : Fin m → Fin n → L => (Fin.cons x U : Fin (m + 1) → Fin n → L))
    (fun X : Fin (m + 1) → Fin n → L => (fun i : Fin m => X i.succ)) ?_ ?_ ?_ ?_
  · intro U hU
    have hU' := (Finset.mem_filter.1 (Finset.mem_coe.1 hU)).2
    obtain ⟨hUW, hUi, hUg⟩ := hU'
    have hUx : ∀ i, hf q M (U i) x = 0 := fun i => (hUW i).2
    have hxU : ∀ i, hf q M x (U i) = 0 := fun i => by
      rw [hf_symm hadd hinv hM, hUx i, zero_pow hq]
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨?_, ?_, ?_⟩, rfl⟩
    · intro i
      induction i using Fin.cases with
      | zero => exact hxW
      | succ i => exact (hUW i).1
    · rw [linearIndependent_finCons]
      refine ⟨hUi, fun hmem => ?_⟩
      have hle : Submodule.span L (Set.range U) ≤ W ⊓ LinearMap.ker (hfL q M x) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact hUW j
      have := (hle hmem).2
      change hf q M x x = 0 at this
      exact hb (hxx ▸ this)
    · intro i j
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simpa [Matrix.diagonal_apply] using hxx
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ, Matrix.diagonal_apply,
            (Fin.succ_ne_zero j).symm, if_false]
          exact hxU j
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ, Matrix.diagonal_apply, Fin.succ_ne_zero,
            if_false]
          exact hUx i
        | succ j =>
          simp only [Fin.cons_succ, Matrix.diagonal_apply, Fin.succ_inj]
          rw [hUg i j, Matrix.diagonal_apply]
  · intro X hX
    have hX' := (Finset.mem_filter.1 (Finset.mem_coe.1 hX)).2
    obtain ⟨⟨hXW, hXi, hXg⟩, hX0⟩ := hX'
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun i => ⟨hXW _, ?_⟩, hXi.comp _ (Fin.succ_injective _), ?_⟩
    · change hf q M (X i.succ) x = 0
      rw [← hX0, hXg, Matrix.diagonal_apply, if_neg (Fin.succ_ne_zero i)]
    · intro i j
      rw [hXg, Matrix.diagonal_apply, Matrix.diagonal_apply]
      simp only [Fin.succ_inj, Fin.cons_succ]
  · intro U _
    rfl
  · intro X hX
    have hX' := (Finset.mem_filter.1 (Finset.mem_coe.1 hX)).2
    rw [← hX'.2]
    exact Fin.cons_self_tail X
end DensInertW
