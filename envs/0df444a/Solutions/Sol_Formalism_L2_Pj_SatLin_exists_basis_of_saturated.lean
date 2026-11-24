-- Prove2me | solution 1 for Formalism.L2.Pj.SatLin.exists_basis_of_saturated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:16:50.281668+00:00
-- url     : https://prove2.me/submissions/46d9c2e7-90ca-4429-bffa-3a5fa1047527

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExistsBasisOfSaturated

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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.SatLin
namespace Formalism.L2.Pj.SatLin
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {d r : ℕ}
    (u : Fin r → (Fin d → R)) (hu : LinearIndependent R u)
    (hs : ∀ (v : Fin d → R) (a : R), a ≠ 0 → a • v ∈ Submodule.span R (Set.range u) →
      v ∈ Submodule.span R (Set.range u)) :
    ∃ (w : Fin d → Fin d → R) (emb : Fin r ↪ Fin d), (∀ i, w (emb i) = u i) ∧
      ∀ v : Fin d → R, ∃! a : Fin d → R, ∀ j, ∑ k, a k * w k j = v j := by
  classical
  set S := Submodule.span R (Set.range u) with hS
  haveI : NoZeroSMulDivisors R ((Fin d → R) ⧸ S) := by
    refine ⟨fun {a q} h => ?_⟩
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective S q
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      rw [Submodule.Quotient.mk_eq_zero]
      exact hs v a ha h
  haveI : Module.Free R ((Fin d → R) ⧸ S) := Module.free_of_finite_type_torsion_free'
  let bQ := Module.Free.chooseBasis R ((Fin d → R) ⧸ S)
  choose s' hs' using fun j => Submodule.Quotient.mk_surjective S (bQ j)
  let w' := Sum.elim u s'
  have hmk : ∀ i, Submodule.Quotient.mk (p := S) (u i) = 0 := fun i =>
    (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent R w' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    have hr : ∀ j, g (Sum.inr j) = 0 := by
      have h1 := congrArg S.mkQ hg
      simp only [w', Sum.elim_inl, Sum.elim_inr, map_add, map_sum, map_smul, map_zero, Submodule.mkQ_apply,
        hmk, hs', smul_zero, Finset.sum_const_zero, zero_add] at h1
      exact Fintype.linearIndependent_iff.1 bQ.linearIndependent _ h1
    have hl : ∀ i, g (Sum.inl i) = 0 := by
      simp only [hr, zero_smul, Finset.sum_const_zero, add_zero, w', Sum.elim_inl] at hg
      exact Fintype.linearIndependent_iff.1 hu _ hg
    rintro (i | j)
    · exact hl i
    · exact hr j
  have hsp : ⊤ ≤ Submodule.span R (Set.range w') := by
    intro v _
    have hv := bQ.sum_repr (Submodule.Quotient.mk (p := S) v)
    have ht : (∑ j, bQ.repr (Submodule.Quotient.mk (p := S) v) j • s' j) ∈ Submodule.span R (Set.range w') :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
    have hvt : v - ∑ j, bQ.repr (Submodule.Quotient.mk (p := S) v) j • s' j ∈ S := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
      simp only [map_smul, Submodule.mkQ_apply, hs']
      rw [hv, sub_self]
    have hSle : S ≤ Submodule.span R (Set.range w') :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨Sum.inl i, rfl⟩)
    have h := Submodule.add_mem _ (hSle hvt) ht
    rwa [sub_add_cancel] at h
  let B := Module.Basis.mk hli hsp
  have hcard : Fintype.card (Fin r ⊕ Module.Free.ChooseBasisIndex R ((Fin d → R) ⧸ S)) = d := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  let b := B.reindex e
  refine ⟨fun k => b k, ⟨fun i => e (Sum.inl i), e.injective.comp Sum.inl_injective⟩, fun i => ?_, fun v => ?_⟩
  · simp [b, B, Module.Basis.reindex_apply, Module.Basis.mk_apply, w']
  · refine ⟨fun k => b.repr v k, fun j => ?_, fun a ha => ?_⟩
    · have h := congrFun (b.sum_repr v) j
      simpa [Finset.sum_apply, smul_eq_mul] using h
    · have hv : ∑ k, a k • b k = v := funext fun j => by simpa [Finset.sum_apply, smul_eq_mul] using ha j
      funext k
      rw [← hv]
      simp [map_sum, Module.Basis.repr_self, Finsupp.single_apply]
end Formalism.L2.Pj.SatLin
