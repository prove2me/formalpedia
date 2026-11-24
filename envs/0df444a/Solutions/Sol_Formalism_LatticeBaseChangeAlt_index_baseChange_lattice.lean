-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.index_baseChange_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:07:00.174808+00:00
-- url     : https://prove2.me/submissions/a1f9dba1-0773-4614-82dd-d2ff532f6855

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LatticeIndexBis
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeIndexBis_span_image_span
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeIndexBis_core
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeIndexBis_exists_indep
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeIndexBis_addVal_map
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_LatticeIndexBis_indep_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : RelIndexSpanImage := by
  intro O O' K K' V V₁
  intros
  rename_i j hj ϖ hϖ hϖ' A B hA hB hAB
  classical
  obtain ⟨a, ha, hAa, haU⟩ := LatticeIndexBis.exists_indep A hA (Submodule.span K (A : Set V)) rfl
  obtain ⟨b, hb, hBb, hbU⟩ := LatticeIndexBis.exists_indep B hB (Submodule.span K (A : Set V)) hAB.symm
  have hmem : ∀ i, b i ∈ Submodule.span K (Set.range a) := by
    intro i
    rw [haU, ← hbU]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hc0 : ∀ i, ∃ c : Fin (Module.finrank K (Submodule.span K (A : Set V))) → K,
      ∑ k, c k • a k = b i := by
    intro i
    first
    | exact (Submodule.mem_span_range_iff_exists_fun K).1 (hmem i)
    | exact Submodule.mem_span_range_iff_exists_fun.1 (hmem i)
  choose c hc using hc0
  let P : Matrix (Fin (Module.finrank K (Submodule.span K (A : Set V))))
      (Fin (Module.finrank K (Submodule.span K (A : Set V)))) K := fun k i => c i k
  obtain ⟨hdet, hcore⟩ := LatticeIndexBis.core (O := O) b a hb ha (hbU.trans haU.symm) P (fun i => (hc i).symm)
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors O) P.det
  dsimp only at hxy
  have hy0 : (y : O) ≠ 0 := nonZeroDivisors.ne_zero y.2
  have hyK : algebraMap O K (y : O) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hxy
    exact (mul_ne_zero hdet hyK) hxy
  have hjK : ∀ (r : K) (z : V), j (r • z) = algebraMap K K' r • j z := by
    intro r z
    rw [map_smul, algebraMap_smul]
  have hjO : ∀ (o : O) (z : V), j (o • z) = algebraMap O O' o • j z := by
    intro o z
    rw [← algebraMap_smul K o z, map_smul, ← algebraMap_smul K' (algebraMap O K o) (j z),
      ← IsScalarTower.algebraMap_apply O K K', IsScalarTower.algebraMap_apply O O' K', algebraMap_smul]
  have hspanK : ∀ f : Fin (Module.finrank K (Submodule.span K (A : Set V))) → V,
      Submodule.span K (Set.range f) = Submodule.span K (A : Set V) →
      Submodule.span K' (Set.range fun i => j (f i)) =
        Submodule.span K' (j '' (Submodule.span K (A : Set V) : Set V)) := by
    intro f hf
    have h1 := LatticeIndexBis.span_image_span (R := K) (S := K') j.toAddMonoidHom (algebraMap K K')
      (fun r z => hjK r z) (Set.range f)
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    calc Submodule.span K' (Set.range fun i => j (f i)) = Submodule.span K' (j '' Set.range f) := by
          rw [← Set.range_comp] <;> rfl
      _ = Submodule.span K' (j '' (Submodule.span K (Set.range f) : Set V)) := h1.symm
      _ = _ := congrArg (fun s : Submodule K V => Submodule.span K' (j '' (s : Set V))) hf
  have hspanO : ∀ f : Fin (Module.finrank K (Submodule.span K (A : Set V))) → V,
      Submodule.span O' (j '' (Submodule.span O (Set.range f) : Set V)) =
        Submodule.span O' (Set.range fun i => j (f i)) := by
    intro f
    have h1 := LatticeIndexBis.span_image_span (R := O) (S := O') j.toAddMonoidHom (algebraMap O O')
      (fun o z => hjO o z) (Set.range f)
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    rw [h1, ← Set.range_comp]
    all_goals rfl
  have hP' : ∀ i, j (b i) = ∑ k, (P.map (algebraMap K K')) k i • j (a k) := by
    intro i
    rw [← hc i, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Matrix.map_apply, algebraMap_smul]
    all_goals rfl
  have hdetmap : (P.map (algebraMap K K')).det = algebraMap K K' P.det := by
    rw [RingHom.map_det]
    rfl
  have hne : ∀ z : O, z ≠ 0 → algebraMap O O' z ≠ 0 := by
    intro z hz h0
    have hzK : algebraMap O K z ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hz)
    apply (map_ne_zero (algebraMap K K')).2 hzK
    rw [← IsScalarTower.algebraMap_apply O K K', IsScalarTower.algebraMap_apply O O' K', h0, map_zero]
  have hx'y' : algebraMap O' K' (algebraMap O O' x) =
      (P.map (algebraMap K K')).det * algebraMap O' K' (algebraMap O O' (y : O)) := by
    rw [← IsScalarTower.algebraMap_apply O O' K', ← IsScalarTower.algebraMap_apply O O' K',
      IsScalarTower.algebraMap_apply O K K' x, IsScalarTower.algebraMap_apply O K K' (y : O), hdetmap,
      ← map_mul, hxy]
  have hab' : Submodule.span K' (Set.range fun i => j (b i)) =
      Submodule.span K' (Set.range fun i => j (a i)) :=
    (hspanK b hbU).trans (hspanK a haU).symm
  obtain ⟨-, hcore'⟩ := LatticeIndexBis.core (O := O') (K := K') (V := V₁) (fun i => j (b i)) (fun i => j (a i))
    (LatticeIndexBis.indep_baseChange j hj b hb) (LatticeIndexBis.indep_baseChange j hj a ha) hab'
    (P.map (algebraMap K K')) hP'
  rw [hAa, hBb, hspanO a, hspanO b,
    hcore' (algebraMap O O' x) (algebraMap O O' (y : O)) (hne x hx0) (hne _ hy0) hx'y',
    hcore x (y : O) hx0 hy0 hxy.symm, LatticeIndexBis.addVal_map ϖ hϖ hϖ' x hx0,
    LatticeIndexBis.addVal_map ϖ hϖ hϖ' (y : O) hy0]
end Formalism.LatticeBaseChangeAlt
