-- Prove2me | solution 1 for Formalism.REAL.compactDecomposition_of_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:15.548582+00:00
-- url     : https://prove2.me/submissions/721960dd-68fb-4f08-b03e-4fb4b3a656d5

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf
import Theorems.Thm_Formalism_REAL_mem_compactSpan_self
import Theorems.Thm_Formalism_REAL_compactSpan_le_of_mem
import Theorems.Thm_Formalism_REAL_compactSpan_isCompactInvariant
import Theorems.Thm_Formalism_REAL_isCompactInvariant_orthogonal_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (he : KHiExist) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (n : ℕ) (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hr : KRel ε F)
    (hu : KUnit ε F) :
    ∀ (d : ℕ) (S : Submodule ℂ V), Module.finrank ℂ S = d → FiniteDimensional ℂ S →
    KStable ε F S →
    ∃ (m : ℕ) (x : Fin m → V) (μ : Fin m → Fin n → ℝ),
      (∀ i, x i ∈ S ∧ x i ≠ 0 ∧ KHighest ε F (μ i) (x i)) ∧
      (∀ i i', i ≠ i' → ∀ y ∈ kSpan ε F (x i), ∀ z ∈ kSpan ε F (x i'), ⟪y, z⟫_ℂ = 0) ∧
      (⨆ i, kSpan ε F (x i)) = S := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro S hd hfin hS
  by_cases h0 : S = ⊥
  · refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    rw [h0]
    exact iSup_of_empty _
  obtain ⟨x, hxS, hx0, μ, hxμ⟩ := he V n ε F S hfin hr hu hS h0
  have hKS : kSpan ε F x ≤ S := compactSpan_le_of_mem ε F hxS hS
  have : FiniteDimensional ℂ (kSpan ε F x) := Submodule.finiteDimensional_of_le hKS
  have hS'S : (kSpan ε F x)ᗮ ⊓ S < S := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro heq
    have hx' : x ∈ (kSpan ε F x)ᗮ ⊓ S := by rw [heq]; exact hxS
    rw [Submodule.mem_inf] at hx'
    have h1 := (Submodule.mem_orthogonal (kSpan ε F x) x).1 hx'.1 x (mem_compactSpan_self ε F x)
    exact hx0 (inner_self_eq_zero.1 h1)
  have : FiniteDimensional ℂ ↥((kSpan ε F x)ᗮ ⊓ S) := Submodule.finiteDimensional_of_le hS'S.le
  have hlt : Module.finrank ℂ ↥((kSpan ε F x)ᗮ ⊓ S) < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hS'S
  obtain ⟨m, xs, μs, h1, h2, h3⟩ := ih _ hlt ((kSpan ε F x)ᗮ ⊓ S) rfl inferInstance
    (isCompactInvariant_orthogonal_inf ε F hu (compactSpan_isCompactInvariant ε F x) hS)
  have hle : ∀ j, kSpan ε F (xs j) ≤ (kSpan ε F x)ᗮ ⊓ S := fun j =>
    h3 ▸ le_iSup (fun i => kSpan ε F (xs i)) j
  refine ⟨m + 1, Fin.cons x xs, Fin.cons μ μs, ?_, ?_, ?_⟩
  · intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · simp only [Fin.cons_zero]
      exact ⟨hxS, hx0, hxμ⟩
    · simp only [Fin.cons_succ]
      exact ⟨(h1 j).1.2, (h1 j).2⟩
  · intro i i' hii'
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ i' with rfl | ⟨j', rfl⟩
    · exact absurd rfl hii'
    · simp only [Fin.cons_zero, Fin.cons_succ]
      intro y hy z hz
      exact Submodule.inner_right_of_mem_orthogonal hy (hle j' hz).1
    · simp only [Fin.cons_zero, Fin.cons_succ]
      intro y hy z hz
      exact Submodule.inner_left_of_mem_orthogonal hz (hle j hy).1
    · simp only [Fin.cons_succ]
      exact h2 j j' (fun h => hii' (congrArg Fin.succ h))
  · apply le_antisymm
    · refine iSup_le fun i => ?_
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simpa using hKS
      · simp only [Fin.cons_succ]
        exact (hle j).trans inf_le_right
    · calc S = kSpan ε F x ⊔ (kSpan ε F x)ᗮ ⊓ S :=
            (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hKS).symm
        _ ≤ _ := by
          refine sup_le ?_ ?_
          · exact le_iSup_of_le (0 : Fin (m + 1)) (by simp)
          · conv_lhs => rw [← h3]
            exact iSup_le fun j => le_iSup_of_le j.succ (by simp)
end Formalism.REAL
