-- Prove2me | solution 1 for Chou.hasPackingProperty_of_directedUnion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T18:14:18.003926+00:00
-- url     : https://prove2.me/submissions/5642472b-3f0b-4a06-bc4d-c8cf05b89dfe

import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib
import Theorems.Thm_Chou_hasPackingProperty_of_finite

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

end Lib
end Chou

/-! # Chou §4: packings and property (P) — the basic cases and Lemmas 4.1, 4.6 (a) -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Packings -/

lemma isPacking_iff {G : Type*} [Group G] (S X : Set G) :
    IsPacking S X ↔ (∀ s ∈ S, ∀ x ∈ X, ∀ s' ∈ S, ∀ x' ∈ X, s * x = s' * x' → s = s' ∧ x = x') ∧
      (∀ g : G, ∃ s ∈ S, ∃ x ∈ X, s * x = g) := by
  constructor
  · rintro ⟨-, hinj, hsurj⟩
    refine ⟨fun s hs x hx s' hs' x' hx' h => ?_, fun g => ?_⟩
    · have := @hinj (s, x) ⟨hs, hx⟩ (s', x') ⟨hs', hx'⟩ h
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    · obtain ⟨⟨s, x⟩, ⟨hs, hx⟩, h⟩ := hsurj (Set.mem_univ g)
      exact ⟨s, hs, x, hx, h⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
    · rintro ⟨s, x⟩ ⟨hs, hx⟩ ⟨s', x'⟩ ⟨hs', hx'⟩ h
      obtain ⟨rfl, rfl⟩ := hinj s hs x hx s' hs' x' hx' h
      rfl
    · intro g _
      obtain ⟨s, hs, x, hx, h⟩ := hsurj g
      exact ⟨(s, x), ⟨hs, hx⟩, h⟩

/-! ### Finite groups and the integers -/

/-! ### Lemma 4.1 (a): directed unions -/

theorem hasPackingProperty_of_directedUnion' {G : Type*} [Group G] {ι : Type*}
    (H : ι → Subgroup G) (hdir : Directed (· ≤ ·) H) (hsup : ⨆ i, H i = ⊤)
    (h : ∀ i, HasPackingProperty (H i)) : HasPackingProperty G := by
  intro F hF
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := subsingleton_of_iSup_empty H hsup
    exact Chou.hasPackingProperty_of_finite F hF
  · obtain ⟨k, hk⟩ := exists_subset_of_directed hdir hsup hF
    obtain ⟨S', Y', hFS', hS'fin, hpack⟩ :=
      h k (Subtype.val ⁻¹' F) (hF.preimage Subtype.val_injective.injOn)
    rw [isPacking_iff] at hpack
    obtain ⟨hinj, hsurj⟩ := hpack
    -- representatives of the right cosets `(H k) z`
    let Q := Quotient (QuotientGroup.rightRel (H k))
    let Z : Set G := Set.range (fun q : Q => q.out)
    refine ⟨Subtype.val '' S', (fun p : (H k) × G => (p.1 : G) * p.2) '' (Y' ×ˢ Z), ?_,
      hS'fin.image _, (isPacking_iff _ _).mpr ⟨?_, ?_⟩⟩
    · intro f hf
      exact ⟨⟨f, hk hf⟩, hFS' hf, rfl⟩
    · rintro _ ⟨s, hs, rfl⟩ _ ⟨⟨y, z⟩, ⟨hy, hz⟩, rfl⟩ _ ⟨s', hs', rfl⟩ _ ⟨⟨y', z'⟩, ⟨hy', hz'⟩, rfl⟩ hh
      obtain ⟨q, rfl⟩ := hz
      obtain ⟨q', rfl⟩ := hz'
      simp only at hh
      -- the two representatives lie in the same right coset, hence coincide
      have hcos : q'.out * (q.out)⁻¹ = ((s' : G) * y')⁻¹ * (s * y) := by
        have := hh
        calc q'.out * (q.out)⁻¹ = ((s' : G) * y')⁻¹ * ((s' : G) * (y' * q'.out)) * (q.out)⁻¹ := by group
          _ = ((s' : G) * y')⁻¹ * ((s : G) * (y * q.out)) * (q.out)⁻¹ := by rw [this]
          _ = ((s' : G) * y')⁻¹ * (s * y) := by group
      have hqq : q = q' := by
        rw [← Quotient.out_eq q, ← Quotient.out_eq q']
        apply Quotient.sound
        exact QuotientGroup.rightRel_apply.mpr (by
          rw [hcos]
          exact (H k).mul_mem ((H k).inv_mem ((H k).mul_mem s'.2 y'.2)) ((H k).mul_mem s.2 y.2))
      subst hqq
      have h2 : (s : G) * y = s' * y' := by
        have := hh
        rw [← mul_assoc, ← mul_assoc] at this
        exact mul_right_cancel this
      obtain ⟨rfl, rfl⟩ := hinj s hs y hy s' hs' y' hy' (Subtype.ext h2)
      exact ⟨rfl, rfl⟩
    · intro g
      let q : Q := Quotient.mk'' g
      have hq : g * (q.out)⁻¹ ∈ H k := by
        have := Quotient.mk_out (s := QuotientGroup.rightRel (H k)) g
        exact (QuotientGroup.rightRel_apply).mp this
      obtain ⟨s, hs, y, hy, hsy⟩ := hsurj ⟨g * (q.out)⁻¹, hq⟩
      refine ⟨s, ⟨s, hs, rfl⟩, y * q.out, ⟨(y, q.out), ⟨hy, ⟨q, rfl⟩⟩, rfl⟩, ?_⟩
      have : ((s : G) * y) = g * (q.out)⁻¹ := congrArg Subtype.val hsy
      rw [← mul_assoc, this]
      group

end Lib
end Chou

open Chou

theorem solution {G : Type*} [Group G] {ι : Type*} (H : ι → Subgroup G)
    (hdir : Directed (· ≤ ·) H) (hsup : ⨆ i, H i = ⊤) (h : ∀ i, HasPackingProperty (H i)) :
    HasPackingProperty G :=
  Chou.Lib.hasPackingProperty_of_directedUnion' H hdir hsup h
