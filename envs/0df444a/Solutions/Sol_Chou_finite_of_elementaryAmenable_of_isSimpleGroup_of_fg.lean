-- Prove2me | solution 1 for Chou.finite_of_elementaryAmenable_of_isSimpleGroup_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T18:51:20.04888+00:00
-- url     : https://prove2.me/submissions/64db7716-6866-4d29-956a-45ed43987bf9

import Theorems.Thm_Chou_elementaryAmenable_iff_constructible
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

/-! # Chou §2: Propositions 2.1 and 2.2

`Constructible` is closed under subgroups and quotients (one structural induction proving both at
once — Chou's transfinite induction), hence coincides with `ElementaryAmenable`. -/

universe u

namespace Chou
namespace Lib

open Subgroup QuotientGroup

end Lib
end Chou

/-! # Chou §2: Theorem 2.3 and Corollary 2.4 -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Small tools -/

lemma subsingleton_of_iSup_empty {G : Type*} [Group G] {ι : Type*} [IsEmpty ι]
    (H : ι → Subgroup G) (hsup : ⨆ i, H i = ⊤) : Subsingleton G := by
  rw [iSup_of_empty] at hsup
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊥ : Subgroup G) := hsup ▸ mem_top a
  have hb : b ∈ (⊥ : Subgroup G) := hsup ▸ mem_top b
  rw [mem_bot] at ha hb
  rw [ha, hb]

lemma exists_subset_of_directed {G : Type*} [Group G] {ι : Type*} [Nonempty ι]
    {H : ι → Subgroup G} (hdir : Directed (· ≤ ·) H) (hsup : ⨆ i, H i = ⊤) {S : Set G}
    (hS : S.Finite) : ∃ k, S ⊆ H k := by
  classical
  obtain ⟨T, rfl⟩ := hS.exists_finset_coe
  clear hS
  induction T using Finset.induction_on with
  | empty => obtain ⟨k⟩ := ‹Nonempty ι›; exact ⟨k, by simp⟩
  | insert a T _ ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨j, hj⟩ := (mem_iSup_of_directed hdir).mp (hsup ▸ mem_top a)
    obtain ⟨m, hkm, hjm⟩ := hdir k j
    refine ⟨m, ?_⟩
    rw [Finset.coe_insert]
    exact Set.insert_subset (hjm hj) (hk.trans hkm)

/-! ### Locally finite groups -/

/-! ### Periodic groups lie in NF; NF ∖ EG is nonempty -/

/-! ### Corollary 2.4 -/

theorem finite_of_constructible_of_isSimpleGroup {G : Type u} [Group G] (hG : Constructible G) :
    ∀ [Group.FG G] [IsSimpleGroup G], Finite G := by
  induction hG with
  | @of_finite G _ _ => intro _ _; infer_instance
  | @of_commGroup G _ => intro _ _; exact Nat.finite_of_card_ne_zero IsSimpleGroup.prime_card.ne_zero
  | @of_mulEquiv G H _ _ e _ ih =>
    intro _ _
    haveI : Group.FG G := Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    haveI : IsSimpleGroup G := e.isSimpleGroup
    haveI := ih
    exact Finite.of_equiv G e.toEquiv
  | @extension G _ N _ _ _ ihN ihQ =>
    intro _ _
    rcases ‹N.Normal›.eq_bot_or_eq_top with hN | hN
    · have e : G ⧸ N ≃* G := (quotientMulEquivOfEq hN).trans quotientBot
      haveI : Group.FG (G ⧸ N) := Group.fg_of_surjective (mk'_surjective N)
      haveI : IsSimpleGroup (G ⧸ N) := e.isSimpleGroup
      haveI := ihQ
      exact Finite.of_equiv _ e.toEquiv
    · have e : N ≃* G := (MulEquiv.subgroupCongr hN).trans Subgroup.topEquiv
      haveI : Group.FG N := Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      haveI : IsSimpleGroup N := e.isSimpleGroup
      haveI := ihN
      exact Finite.of_equiv _ e.toEquiv
  | @directedUnion G _ ι H hdir hsup _ ih =>
    intro hfg _
    rcases isEmpty_or_nonempty ι with hι | hι
    · haveI := subsingleton_of_iSup_empty H hsup
      exact inferInstance
    · obtain ⟨S, hS⟩ := hfg.out
      obtain ⟨k, hk⟩ := exists_subset_of_directed hdir hsup (Finset.finite_toSet S)
      have htop : H k = ⊤ := by
        rw [eq_top_iff, ← hS]
        exact (closure_le _).mpr hk
      have e : H k ≃* G := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      haveI : Group.FG (H k) := Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      haveI : IsSimpleGroup (H k) := e.isSimpleGroup
      haveI := ih k
      exact Finite.of_equiv _ e.toEquiv

/-- Corollary 2.4. -/
theorem finite_of_elementaryAmenable_of_isSimpleGroup_of_fg' {G : Type u} [Group G]
    (hG : ElementaryAmenable G) [Group.FG G] [IsSimpleGroup G] : Finite G :=
  finite_of_constructible_of_isSimpleGroup (Chou.elementaryAmenable_iff_constructible.mp hG)

end Lib
end Chou

open Chou

theorem solution {G : Type*} [Group G] (hG : ElementaryAmenable G) [Group.FG G] [IsSimpleGroup G] :
    Finite G :=
  Chou.Lib.finite_of_elementaryAmenable_of_isSimpleGroup_of_fg' hG
