-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.successive_minima_gap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:34.9637+00:00
-- url     : https://prove2.me/submissions/0f7a0752-1481-464c-b879-6d6f527d0a48

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpAlg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_NilpotentSubgroupRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.RF
variable {K : Type} [Field K] [StarRing K] {n : ℕ} {J : Matrix (Fin n) (Fin n) K} {W : Submodule K (Fin n → K)}
namespace CompanionTheory.D.gk.RF
theorem _root_.solution : Gap := by
  classical
  intro K _ n A ν s₀ η hs hη hη1 ⟨u₀, hu₀, hne, hν⟩
  let S : ℕ → Set (Fin n → K) := fun j => {u | u ∈ A ∧ ν u ≤ s₀ * η ^ j}
  let Wj : ℕ → Submodule K (Fin n → K) := fun j => Submodule.span K (S j)
  have hmono : ∀ j, Wj (j + 1) ≤ Wj j := fun j => Submodule.span_mono fun u hu =>
    ⟨hu.1, hu.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη.le hη1.le (Nat.le_succ j)) hs.le)⟩
  have hnz : ∀ j ≤ n + 1, Wj j ≠ ⊥ := fun j hj h => hne (by
    have : u₀ ∈ Wj j := Submodule.subset_span ⟨hu₀, hν.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hη.le hη1.le hj) hs.le)⟩
    rwa [h, Submodule.mem_bot] at this)
  have hex : ∃ j ≤ n, Wj (j + 1) = Wj j := by
    by_contra hc
    push Not at hc
    have : ∀ j ≤ n + 1, Module.finrank K (Wj j) + j ≤ n := by
      intro j hj
      induction j with
      | zero => simpa using (Wj 0).finrank_le
      | succ j ih =>
        have h1 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hmono j) (hc j (by omega)))
        have h2 := ih (by omega)
        omega
    have := this (n + 1) le_rfl
    omega
  obtain ⟨j, hj, he⟩ := hex
  obtain ⟨B, hBS, hBsp, hli⟩ := exists_linearIndependent K (S (j + 1))
  have hfin : B.Finite := hli.setFinite
  have := hfin.fintype
  let e := Fintype.equivFin B
  have hr : Set.range (fun i => ((e.symm i : B) : Fin n → K)) = B := by
    rw [show (fun i => ((e.symm i : B) : Fin n → K)) = Subtype.val ∘ e.symm from rfl, e.symm.surjective.range_comp,
      Subtype.range_coe]
  refine ⟨s₀ * η ^ j, by positivity, mul_le_of_le_one_right hs.le (pow_le_one₀ hη.le hη1.le), _,
    fun i => e.symm i, by simpa using hli.fintype_card_le_finrank, fun i => ⟨(hBS (e.symm i).2).1,
      (hBS (e.symm i).2).2.trans (le_of_eq (by ring))⟩, ?_, fun u hu hut => ?_⟩
  · rw [hr, hBsp]; exact hnz (j + 1) (by omega)
  · rw [hr, hBsp]
    show u ∈ Wj (j + 1)
    rw [he]
    exact Submodule.subset_span ⟨hu, hut⟩
end CompanionTheory.D.gk.RF
