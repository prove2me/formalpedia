-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_finite_between
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:43:20.693677+00:00
-- url     : https://prove2.me/submissions/b7556f18-f680-4a9b-a6a6-a7ab5bd34d56

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetAssembly_torsion
import Theorems.Thm_Formalism_HermitianLatticesTheory_closure_range_le_closure_range_inv_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix
noncomputable section
namespace Formalism.HermitianLatticesTheory
section Trace
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
end Trace
section Real
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
end Real
section Finite
variable {V : Type*} [AddCommGroup V]
private theorem exists_coeffs_of_mem_closure_lemma_4 {W : Type*} [AddCommGroup W] {n : ℕ} (g : Fin n → W)
    (q : W) (hq : q ∈ AddSubgroup.closure (Set.range g)) :
    ∃ c : Fin n → ℤ, ∑ i, c i • g i = q := by
  classical
  let S : AddSubgroup W :=
    { carrier := {q | ∃ c : Fin n → ℤ, ∑ i, c i • g i = q}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨-a, by simp [neg_smul, Finset.sum_neg_distrib]⟩ }
  have hle : AddSubgroup.closure (Set.range g) ≤ S := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨Pi.single j 1, by simp [Pi.single_apply]⟩
  exact hle hq
end Finite
section Isom
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
end Isom
section Main
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
end Main
end Formalism.HermitianLatticesTheory
end
end

set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {V : Type*} [AddCommGroup V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (hE : FinIntermediate) {K W : Type} [Field K] [CharZero K]
    [AddCommGroup W] [Module K W] {n : ℕ} (u : Fin n → W) (e : ℤ) (he : e ≠ 0) :
    {M : AddSubgroup W | AddSubgroup.closure (Set.range u) ≤ M ∧
      M ≤ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i)}.Finite := by
  classical
  unfold FinIntermediate at hE
  have hPQ := closure_range_le_closure_range_inv_smul (K := K) u e he
  have hkill : ∀ q ∈ AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i),
      e • q ∈ AddSubgroup.closure (Set.range u) :=
    fun q hq => classSetAssembly_torsion (K := K) u e he hq
  refine hE W _ _ hPQ ?_
  set P := AddSubgroup.closure (Set.range u) with hP
  set Q := AddSubgroup.closure (Set.range fun i => ((e : K)⁻¹) • u i) with hQ
  have hgQ : ∀ i, ((e : K)⁻¹) • u i ∈ Q := fun i => AddSubgroup.subset_closure ⟨i, rfl⟩
  let F : (Fin n → ℤ) → Q ⧸ P.addSubgroupOf Q := fun k =>
    QuotientAddGroup.mk ⟨∑ i, k i • (((e : K)⁻¹) • u i),
      Q.sum_mem fun i _ => Q.zsmul_mem (hgQ i) (k i)⟩
  have hsurj : (Set.univ : Set (Q ⧸ P.addSubgroupOf Q)) ⊆
      F '' (Set.univ.pi fun _ => Set.Ico (0 : ℤ) (e.natAbs : ℤ)) := by
    intro z _
    obtain ⟨⟨q, hq⟩, rfl⟩ := QuotientAddGroup.mk_surjective z
    obtain ⟨c, hc⟩ := exists_coeffs_of_mem_closure_lemma_4 (fun i => ((e : K)⁻¹) • u i) q hq
    refine ⟨fun i => c i % e, ?_, ?_⟩
    · intro i _
      exact Set.mem_Ico.mpr ⟨Int.emod_nonneg _ he, Int.emod_lt _ he⟩
    · apply QuotientAddGroup.eq.mpr
      rw [AddSubgroup.mem_addSubgroupOf]
      show -(∑ i, (c i % e) • (((e : K)⁻¹) • u i)) + q ∈ P
      have hsum : -(∑ i, (c i % e) • (((e : K)⁻¹) • u i)) + q =
          ∑ i, (c i / e) • (e • (((e : K)⁻¹) • u i)) := by
        rw [← hc, neg_add_eq_sub, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, ← sub_smul]
        congr 1
        have key : c i % e + e * (c i / e) = c i := by
          first
          | exact Int.emod_add_ediv (c i) e
          | (have := Int.ediv_add_emod (c i) e; linarith)
          | (rw [Int.emod_def]; ring)
        linarith
      rw [hsum]
      exact P.sum_mem fun i _ => P.zsmul_mem (hkill _ (hgQ i)) _
  have hfin : (Set.univ : Set (Q ⧸ P.addSubgroupOf Q)).Finite :=
    ((Set.Finite.pi fun _ => Set.finite_Ico _ _).image F).subset hsurj
  exact Set.finite_univ_iff.mp hfin
end Formalism.HermitianLatticesTheory
