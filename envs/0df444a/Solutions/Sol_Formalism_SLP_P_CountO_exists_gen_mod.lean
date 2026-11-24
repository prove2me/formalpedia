-- Prove2me | solution 1 for Formalism.SLP.P.CountO.exists_gen_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:01:27.839392+00:00
-- url     : https://prove2.me/submissions/398cf5ea-000f-466f-9511-bae4e5f2cf34

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
import Theorems.Thm_Formalism_SLP_P_CountO_exists_rel_not_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace Formalism.SLP.P.CountO
theorem _root_.solution (P : Ideal R) [hPm : P.IsMaximal] (hP : P ≠ ⊥) {X : Type}
    [AddCommGroup X] [Module R X] [Module.Finite R X]
    (htf : ∀ a : R, a ≠ 0 → ∀ x : X, a • x = 0 → x = 0) (k : ℕ)
    (hli : ∀ (ι : Type) [Fintype ι] (v : ι → X), LinearIndependent R v → Fintype.card ι ≤ k) :
    ∃ s : Finset X, s.card ≤ k ∧ Submodule.span R (s : Set X) ⊔ P • ⊤ = ⊤ := by
  classical
  have hex : ∃ n, ∃ s : Finset X, s.card = n ∧ Submodule.span R (s : Set X) ⊔ P • ⊤ = ⊤ := by
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := X)
    exact ⟨s.card, s, rfl, by rw [hs, top_sup_eq]⟩
  obtain ⟨s, hsc, hs⟩ := Nat.find_spec hex
  refine ⟨s, ?_, hs⟩
  rw [hsc]
  by_contra hlt
  push Not at hlt
  have hnli : ¬ LinearIndependent R (fun x : s => (x : X)) := fun h => by
    have := hli s _ h
    rw [Fintype.card_coe] at this
    omega
  rw [linearIndependent_iff'] at hnli
  push Not at hnli
  obtain ⟨t, g, hg, i, hit, hgi⟩ := hnli
  obtain ⟨i0, hi0, d, hd0, hd⟩ :=
    exists_rel_not_mem htf P hP t (fun x : s => (x : X)) g hg ⟨i, hit, hgi⟩
  set s' := s.erase (i0 : X) with hs'def
  have hmem : (i0 : X) ∈ Submodule.span R (s' : Set X) ⊔ P • ⊤ := by
    obtain ⟨a, b, hb, hab⟩ := Ideal.IsMaximal.exists_inv hPm hd0
    have h1 : d i0 • (i0 : X) ∈ Submodule.span R (s' : Set X) := by
      have h2 : d i0 • (i0 : X) = - ∑ i ∈ t.erase i0, d i • (i : X) := by
        rw [← Finset.add_sum_erase t _ hi0] at hd
        exact eq_neg_of_add_eq_zero_left hd
      rw [h2]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      have hne : i ≠ i0 := Finset.ne_of_mem_erase hi
      simp only [s', Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
      exact ⟨i.2, fun h => hne (Subtype.ext h)⟩
    have h3 : (i0 : X) = a • (d i0 • (i0 : X)) + b • (i0 : X) := by
      rw [smul_smul, ← add_smul, hab, one_smul]
    rw [h3]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ h1))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul hb Submodule.mem_top))
  have hs' : Submodule.span R (s' : Set X) ⊔ P • ⊤ = ⊤ := by
    rw [eq_top_iff]
    refine le_trans hs.ge (sup_le ?_ le_sup_right)
    rw [Submodule.span_le]
    intro x hx
    by_cases hx0 : x = (i0 : X)
    · rw [hx0]; exact hmem
    · exact Submodule.mem_sup_left (Submodule.subset_span (by simp [s', hx0, hx]))
  have hcard : s'.card < Nat.find hex := by
    rw [← hsc, hs'def, Finset.card_erase_of_mem i0.2]
    have : 0 < s.card := Finset.card_pos.mpr ⟨i0, i0.2⟩
    omega
  exact Nat.find_min hex hcard ⟨s', rfl, hs'⟩
end Formalism.SLP.P.CountO
