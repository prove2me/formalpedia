-- Prove2me | solution 1 for Formalism.L2.Pj.AvAlg.mem_adjoin_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:14:15.421428+00:00
-- url     : https://prove2.me/submissions/f8a3c253-fe9a-4934-a624-f0d512fb64e5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.AvAlg
variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
namespace Formalism.L2.Pj.AvAlg
theorem _root_.solution (α : B) (hres : Algebra.adjoin (ResidueField A) {residue B α} = ⊤) (f : A[X])
    (hβ : Irreducible (aeval α f)) :
    ∀ (n : ℕ) (b : B), ∃ s ∈ Algebra.adjoin A {α}, ∃ c : B, b = s + aeval α f ^ n * c := by
  have hra : ∀ G : A[X], residue B (aeval α G) = aeval (residue B α) (G.map (residue A)) := by
    intro G
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
    congr 1
    all_goals (ext x; simp only [RingHom.comp_apply]; exact (IsLocalRing.ResidueField.algebraMap_residue x).symm)
  intro n
  induction n with
  | zero => intro b; exact ⟨0, Subalgebra.zero_mem _, b, by simp⟩
  | succ n ih =>
    intro b
    obtain ⟨s, hs, c, rfl⟩ := ih b
    have hc : residue B c ∈ Algebra.adjoin (ResidueField A) {residue B α} := by
      rw [hres]; exact Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hc
    obtain ⟨p, hp⟩ := hc
    obtain ⟨P, rfl⟩ := Polynomial.map_surjective (residue A) IsLocalRing.residue_surjective p
    have hm : c - aeval α P ∈ maximalIdeal B := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hra]
      rw [← hp]
      exact sub_self _
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hβ, Ideal.mem_span_singleton'] at hm
    obtain ⟨c', hc'⟩ := hm
    have hα : aeval α f ∈ Algebra.adjoin A {α} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ f
    have hP : aeval α P ∈ Algebra.adjoin A {α} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ P
    refine ⟨s + aeval α f ^ n * aeval α P, ?_, c', ?_⟩
    · exact Subalgebra.add_mem _ hs (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hα n) hP)
    · have e : c = aeval α P + c' * aeval α f := by rw [hc']; ring
      rw [e]
      ring
end Formalism.L2.Pj.AvAlg
