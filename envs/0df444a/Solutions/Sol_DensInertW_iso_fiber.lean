-- Prove2me | solution 1 for DensInertW.iso_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:08.669296+00:00
-- url     : https://prove2.me/submissions/8d8eb4bd-de6e-4c2b-a052-d6fccb92e17a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_IsoPeel
import Theorems.Thm_DensInertW_iso_li_tail
import Theorems.Thm_DensInertW_iso_li_cons
import Theorems.Thm_DensInertW_Sub_hf_add_right
import Theorems.Thm_DensInertW_Sub_hf_smul_right
import Theorems.Thm_DensInertW_Sub_hf_sub_left
import Theorems.Thm_DensInertW_Sub_hf_sub_right
import Theorems.Thm_DensInertW_Sub_hf_symm


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
theorem _root_.solution [Fintype L] {n c q : ℕ} {M : Matrix (Fin n) (Fin n) L}
    (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hM : IsHerm q M) (W : Submodule L (Fin n → L)) (x y : Fin n → L)
    (hxW : x ∈ W) (hyW : y ∈ W) (hxx : hf q M x x = 0) (hxy : hf q M x y = 1) :
    (Finset.univ.filter (fun X : Fin (c + 1) → Fin n → L => isoP q M W X ∧ X 0 = x)).card =
      Fintype.card (Fin c → L) * (Finset.univ.filter (isoP (m := c) q M
        (W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y)))).card := by
  have hq : q ≠ 0 := by
    rintro rfl
    have := hinv 0
    simp at this
  have hzero : ∀ v w, hf q M v w = 0 → hf q M w v = 0 := fun v w h => by
    rw [hf_symm hadd hinv hM v w, h, zero_pow hq]
  rw [← Finset.card_univ, ← Finset.card_product]
  refine Finset.card_nbij'
    (fun X => ((fun i => hf q M (X i.succ) y), fun i => X i.succ - hf q M (X i.succ) y • x))
    (fun p => Fin.cons x (fun i => p.2 i + p.1 i • x)) ?_ ?_ ?_ ?_
  · rintro X hX
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hX
    obtain ⟨⟨hW, hli, hiso⟩, hX0⟩ := hX
    simp only [Finset.coe_product, Finset.coe_univ, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq]
    refine ⟨fun i => ?_, ?_, fun i j => ?_⟩
    · refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
      · exact W.sub_mem (hW _) (W.smul_mem _ hxW)
      · show hf q M _ x = 0
        rw [hf_sub_left, hf_smul_left, hxx, mul_zero, sub_zero, ← hX0]
        exact hiso _ _
      · show hf q M _ y = 0
        rw [hf_sub_left, hf_smul_left, hxy, mul_one, sub_self]
    · have h := hli
      rw [← Fin.cons_self_tail X, hX0] at h
      exact iso_li_tail x _ _ h
    · simp only [hf_sub_left, hf_sub_right hq hadd, hf_smul_left, hf_smul_right]
      rw [← hX0]
      simp [hiso]
  · rintro ⟨a, U⟩ hp
    simp only [Finset.coe_product, Finset.coe_univ, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq] at hp
    obtain ⟨hUW, hUli, hUiso⟩ := hp
    have hU : ∀ i, U i ∈ W ∧ hf q M (U i) x = 0 ∧ hf q M (U i) y = 0 := fun i => by
      have := hUW i
      simp only [Submodule.mem_inf, LinearMap.mem_ker] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    refine ⟨⟨fun i => ?_, ?_, fun i j => ?_⟩, rfl⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hxW
      · simp only [Fin.cons_succ]
        exact W.add_mem (hU j).1 (W.smul_mem _ hxW)
    · exact iso_li_cons x U a (hfL q M y) hxy (fun i => (hU i).2.2) hUli
    · refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
        simp only [Fin.cons_zero, Fin.cons_succ]
      · exact hxx
      · simp only [hf_add_right hadd, hf_smul_right, hxx, mul_zero, add_zero]
        exact hzero _ _ (hU j').2.1
      · simp only [hf_add_left, hf_smul_left, hxx, mul_zero, add_zero]
        exact (hU i').2.1
      · simp only [hf_add_left, hf_add_right hadd, hf_smul_left, hf_smul_right, hxx, (hU i').2.1,
          hzero _ _ (hU j').2.1, hUiso]
        ring
  · intro X hX
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hX
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hX.2]
    · simp
  · rintro ⟨a, U⟩ hp
    simp only [Finset.coe_product, Finset.coe_univ, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq] at hp
    have hUy : ∀ i, hf q M (U i) y = 0 := fun i => by
      have := hp.1 i
      simp only [Submodule.mem_inf, LinearMap.mem_ker] at this
      exact this.2
    have ha : ∀ i, hf q M (U i + a i • x) y = a i := fun i => by
      rw [hf_add_left, hf_smul_left, hxy, hUy, mul_one, zero_add]
    simp only [Fin.cons_succ]
    refine Prod.ext (funext fun i => ha i) (funext fun i => ?_)
    simp only [ha]
    simp
end DensInertW
