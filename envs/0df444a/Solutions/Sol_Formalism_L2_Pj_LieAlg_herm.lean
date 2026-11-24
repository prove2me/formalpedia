-- Prove2me | solution 1 for Formalism.L2.Pj.LieAlg.herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:36:48.498182+00:00
-- url     : https://prove2.me/submissions/4a17c602-2b6c-496a-9cd4-01f6a40f8f25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieAlg
import Theorems.Thm_Formalism_L2_Pj_LieAlg_fg_eq_span_singleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LieAlg
open Submodule
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]
namespace Formalism.L2.Pj.LieAlg
theorem _root_.solution (m : ℕ) (Λ : Submodule V (Fin m → K)) (hfg : Λ.FG)
    (hne : ∀ i : Fin m, ∃ α ∈ Λ, (∀ j, i < j → α j = 0) ∧ α i ≠ 0) :
    ∃ β : Fin m → (Fin m → K), (∀ i, β i ∈ Λ) ∧ (∀ i j, i < j → β i j = 0) ∧ (∀ i, β i i ≠ 0) ∧
      ∀ α ∈ Λ, ∃! r : Fin m → V, α = ∑ i, r i • β i := by
  classical
  haveI : IsNoetherian V Λ := isNoetherian_of_fg_of_noetherian Λ hfg
  have key : ∀ i : Fin m, ∃ b : Fin m → K, b ∈ Λ ∧ (∀ j, i < j → b j = 0) ∧ b i ≠ 0 ∧
      ∀ α ∈ Λ, (∀ j, i < j → α j = 0) → ∃ c : V, α i = c • b i := by
    intro i
    let I : Submodule V K := (Λ ⊓ tailZero (V := V) (K := K) m i).map (LinearMap.proj i)
    have hIfg : I.FG := by
      have h1 : ((tailZero (V := V) (K := K) m i).comap Λ.subtype).FG := IsNoetherian.noetherian _
      have h2 := h1.map Λ.subtype
      rw [Submodule.map_comap_subtype] at h2
      exact h2.map _
    obtain ⟨t, ht⟩ := fg_eq_span_singleton I hIfg
    have tI : t ∈ I := ht ▸ mem_span_singleton_self t
    obtain ⟨b, ⟨hbΛ, hbz⟩, hbt⟩ := Submodule.mem_map.1 tI
    have hbt' : b i = t := hbt
    have hmem : ∀ α ∈ Λ, (∀ j, i < j → α j = 0) → ∃ c : V, α i = c • b i := by
      intro α hα hz
      have h3 : α i ∈ I := Submodule.mem_map.2 ⟨α, ⟨hα, hz⟩, rfl⟩
      rw [ht, mem_span_singleton] at h3
      obtain ⟨c, hc⟩ := h3
      exact ⟨c, by rw [hbt', hc]⟩
    refine ⟨b, hbΛ, hbz, ?_, hmem⟩
    obtain ⟨α, hα, hz, hne'⟩ := hne i
    obtain ⟨c, hc⟩ := hmem α hα hz
    intro h0
    exact hne' (by rw [hc, h0, smul_zero])
  choose β hβΛ hβz hβd hβc using key
  have indep : ∀ r : Fin m → V, ∑ i, r i • β i = 0 → r = 0 := by
    intro r hr
    by_contra hne0
    have hS : (Finset.univ.filter fun i => r i ≠ 0).Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hne0
      exact ⟨i, by simpa using hi⟩
    have hi : r ((Finset.univ.filter fun i => r i ≠ 0).max' hS) ≠ 0 := by
      have h4 := Finset.max'_mem _ hS
      simpa using h4
    set i := (Finset.univ.filter fun i => r i ≠ 0).max' hS with hidef
    have hgt : ∀ j, i < j → r j = 0 := by
      intro j hj
      by_contra h
      have h5 : j ≤ i := Finset.le_max' _ j (by simpa using h)
      exact absurd hj (not_lt.2 h5)
    have hcoord := congrFun hr i
    rw [Finset.sum_apply, Finset.sum_eq_single i] at hcoord
    · rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, mul_eq_zero] at hcoord
      rcases hcoord with h | h
      · exact hi ((IsFractionRing.injective V K) (by rw [h, map_zero]))
      · exact hβd i h
    · intro j _ hji
      rw [Pi.smul_apply]
      rcases lt_or_gt_of_ne hji with h | h
      · rw [hβz j i h, smul_zero]
      · rw [hgt j h, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have exist : ∀ k : ℕ, ∀ α ∈ Λ, (∀ j : Fin m, k ≤ j.val → α j = 0) →
      ∃ r : Fin m → V, α = ∑ i, r i • β i := by
    intro k
    induction k with
    | zero =>
      intro α _ hz
      refine ⟨0, ?_⟩
      funext j
      simp [hz j (Nat.zero_le _)]
    | succ k ih =>
      intro α hα hz
      by_cases hk : k < m
      · let i : Fin m := ⟨k, hk⟩
        obtain ⟨c, hc⟩ := hβc i α hα (fun j hj => hz j (by have h6 : k < j.val := hj; omega))
        obtain ⟨r, hr⟩ := ih (α - c • β i) (Λ.sub_mem hα (Λ.smul_mem c (hβΛ i))) (by
          intro j hj
          simp only [Pi.sub_apply, Pi.smul_apply]
          rcases Nat.eq_or_lt_of_le hj with h | h
          · have h7 : j = i := Fin.ext h.symm
            rw [h7, hc, sub_self]
          · rw [hz j h, hβz i j (show i < j from h), smul_zero, sub_zero])
        have hs : ∑ j, (Pi.single i c : Fin m → V) j • β j = c • β i := by
          rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp),
            Pi.single_eq_same]
        refine ⟨r + Pi.single i c, ?_⟩
        rw [sub_eq_iff_eq_add] at hr
        rw [hr]
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hs]
      · exact ih α hα (fun j hj => hz j (by have := j.isLt; omega))
  refine ⟨β, hβΛ, hβz, hβd, ?_⟩
  intro α hα
  obtain ⟨r, hr⟩ := exist m α hα (fun j hj => absurd j.isLt (not_lt.2 hj))
  refine ⟨r, hr, fun r' hr' => ?_⟩
  have h8 := indep (r' - r) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    rw [← hr, ← hr', sub_self])
  exact sub_eq_zero.1 h8
end Formalism.L2.Pj.LieAlg
