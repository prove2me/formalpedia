-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.exists_common_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:54.650899+00:00
-- url     : https://prove2.me/submissions/b1cb6902-ee75-453a-a187-a503485838a4

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GoodPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution (h : ι → ℕ) (hinj : Function.Injective h) (W : Submodule ℂ (ι → ℂ))
    (hW : W ≠ ⊥) : ∃ w₀ ∈ W, w₀ ≠ 0 ∧ ∀ A : Matrix ι ι ℂ, A.BlockTriangular h → (∀ w ∈ W, A *ᵥ w ∈ W) →
      ∃ c : ℂ, A *ᵥ w₀ = c • w₀ := by
  classical
  have hex : ∃ n : ℕ, ∃ w ∈ W, w ≠ 0 ∧ ∀ i, n ≤ h i → w i = 0 := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    refine ⟨Finset.univ.sup h + 1, w, hw, hw0, fun i hi => ?_⟩
    have : h i ≤ Finset.univ.sup h := Finset.le_sup (Finset.mem_univ i)
    omega
  obtain ⟨w₀, hw₀, hne, hz⟩ := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    apply hne
    funext i
    exact hz i (by omega)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmin : ∀ w ∈ W, (∀ i, m ≤ h i → w i = 0) → w = 0 := by
    intro w hw hw'
    by_contra hw0
    exact Nat.find_min hex (show m < Nat.find hex by omega) ⟨w, hw, hw0, hw'⟩
  have hj : ∃ j, h j = m := by
    by_contra hno
    apply hne
    refine hmin w₀ hw₀ fun i hi => hz i ?_
    have : h i ≠ m := fun e => hno ⟨i, e⟩
    omega
  obtain ⟨j, hj⟩ := hj
  refine ⟨w₀, hw₀, hne, fun A hA hAW => ⟨A j j, ?_⟩⟩
  rw [← sub_eq_zero]
  refine hmin _ (W.sub_mem (hAW _ hw₀) (W.smul_mem _ hw₀)) fun i hi => ?_
  have key : (A *ᵥ w₀) i = A i j * w₀ j := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_single j (fun k _ hk => ?_) (by simp)
    have hkj : h k ≠ m := fun e => hk (hinj (e.trans hj.symm))
    rcases lt_or_ge (h k) (h i) with h1 | h1
    · rw [hA h1, zero_mul]
    · rw [hz k (by omega), mul_zero]
  rw [Pi.sub_apply, key, Pi.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · rw [hij, sub_self]
  · have him : h i ≠ m := fun e => hij (hinj (e.trans hj.symm))
    rw [hA (show h j < h i by omega), hz i (by omega)]
    simp
end CompanionTheory.D.gk.admitted
