-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.topologicalKrullDim_lt_of_isClosed_of_not_subset_irreducibleComponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:46.185931+00:00
-- url     : https://prove2.me/submissions/e72bae76-ec5f-4b32-8ce9-77ef885ef22b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u v
open TopologicalSpace AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
open Order in
private theorem topologicalKrullDim_eq_iSup_length {Z : Type*} [TopologicalSpace Z] :
    topologicalKrullDim Z =
      ⨆ p : LTSeries (IrreducibleCloseds Z), (p.length : WithBot ℕ∞) := rfl
private theorem coe_irreducibleClosedsImageVal {X : Type u} [TopologicalSpace X] {Y : Set X} (hY : IsClosed Y)
    (a : IrreducibleCloseds ↥Y) :
    ((irreducibleClosedsImageSubtypeVal hY a : IrreducibleCloseds X) : Set X) = Subtype.val '' (a : Set ↥Y) := rfl
private theorem irreducibleClosedsImageVal_subset {X : Type u} [TopologicalSpace X] {Y : Set X} (hY : IsClosed Y)
    (a : IrreducibleCloseds ↥Y) :
    ((irreducibleClosedsImageSubtypeVal hY a : IrreducibleCloseds X) : Set X) ⊆ Y := by
  rw [coe_irreducibleClosedsImageVal]
  rintro x ⟨y, -, rfl⟩
  exact y.2
private theorem strictMono_irreducibleClosedsImageVal {X : Type u} [TopologicalSpace X] {Y : Set X}
    (hY : IsClosed Y) : StrictMono (irreducibleClosedsImageSubtypeVal hY) := by
  intro a b hab
  refine lt_of_le_of_ne ?_ ?_
  · rw [← SetLike.coe_subset_coe, coe_irreducibleClosedsImageVal, coe_irreducibleClosedsImageVal]
    exact Set.image_mono (SetLike.coe_subset_coe.mpr hab.le)
  · intro h
    have h1 : Subtype.val '' (a : Set ↥Y) = Subtype.val '' (b : Set ↥Y) := by
      rw [← coe_irreducibleClosedsImageVal hY a, ← coe_irreducibleClosedsImageVal hY b, h]
    exact hab.ne (SetLike.coe_injective (Set.image_injective.mpr Subtype.val_injective h1))
private theorem exists_mem_irreducibleComponents_superset_of_isIrreducible {X : Type u} [TopologicalSpace X] {s : Set X}
    (hs : IsIrreducible s) :
    ∃ C : Set X, C ∈ irreducibleComponents X ∧ IsIrreducible C ∧ IsClosed C ∧ s ⊆ C := by
  obtain ⟨t, ht, hst, hmax⟩ := exists_preirreducible s hs.2
  have htirr : IsIrreducible t := ⟨hs.1.mono hst, ht⟩
  have htc : closure t = t := hmax (closure t) ht.closure subset_closure
  exact ⟨t, ⟨htirr, fun u hu htu => le_of_eq (hmax u hu.2 htu)⟩, htirr,
    closure_eq_iff_isClosed.mp htc, hst⟩
private theorem nonempty_irreducibleCloseds {Z : Type u} [TopologicalSpace Z] (z : Z) :
    Nonempty (IrreducibleCloseds Z) :=
  ⟨⟨closure {z}, ⟨⟨z, subset_closure rfl⟩, isPreirreducible_singleton.closure⟩,
    isClosed_closure⟩⟩
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u v
open TopologicalSpace AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open Order
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution
    {X : Type u} [TopologicalSpace X] (Y : Set X) (hY : IsClosed Y) (hne : Y.Nonempty)
    (hcomp : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ Y)
    (hfin : topologicalKrullDim X < ⊤) :
    topologicalKrullDim ↥Y < topologicalKrullDim X := by
  have key : ∀ p : LTSeries (IrreducibleCloseds ↥Y),
      (((p.length + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim X := by
    intro p
    obtain ⟨q, hqlen, hqlast⟩ :
        ∃ q : LTSeries (IrreducibleCloseds X),
          q.length = p.length ∧ q.last = irreducibleClosedsImageSubtypeVal hY p.last :=
      ⟨p.map (irreducibleClosedsImageSubtypeVal hY) (strictMono_irreducibleClosedsImageVal hY), rfl, rfl⟩
    obtain ⟨C, hCmem, hCirr, hCcl, hsub⟩ := exists_mem_irreducibleComponents_superset_of_isIrreducible q.last.2
    have hsub' : ((q.last : IrreducibleCloseds X) : Set X)
        ⊆ ((⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) : Set X) := hsub
    have hlt : q.last < (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) := by
      refine lt_of_le_of_ne (SetLike.coe_subset_coe.mp hsub') ?_
      intro h
      refine hcomp C hCmem ?_
      have hc : ((⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) : Set X) ⊆ Y := by
        rw [← h, hqlast]
        exact irreducibleClosedsImageVal_subset hY p.last
      exact hc
    have hs1 : (q.snoc (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) hlt).length = q.length + 1 := rfl
    have hs2 : (q.snoc (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) hlt).length = p.length + 1 := by
      omega
    have h1 : ((q.snoc (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds X) hlt).length : WithBot ℕ∞)
        ≤ ⨆ r : LTSeries (IrreducibleCloseds X), (r.length : WithBot ℕ∞) :=
      le_iSup (fun r : LTSeries (IrreducibleCloseds X) => (r.length : WithBot ℕ∞)) _
    rw [hs2] at h1
    rw [topologicalKrullDim_eq_iSup_length, WithBot.coe_natCast]
    exact h1
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨a0⟩ := nonempty_irreducibleCloseds (⟨y0, hy0⟩ : ↥Y)
  have hp0 : (((1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim X :=
    key ⟨0, fun _ => a0, fun i => i.elim0⟩
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    intro hb
    rw [hb] at hp0
    exact WithBot.coe_ne_bot (le_bot_iff.mp hp0)
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hetop : e ≠ ⊤ := by
    rintro rfl
    rw [← he] at hfin
    exact lt_irrefl _ hfin
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hetop
  have hD : topologicalKrullDim X = (((N : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [← he, ← hN]
  rw [hD] at hp0
  have hN1 : 1 ≤ N := by
    have h2 := WithBot.coe_le_coe.mp hp0
    exact_mod_cast h2
  have hbound : (⨆ p : LTSeries (IrreducibleCloseds ↥Y), (p.length : WithBot ℕ∞))
      ≤ ((((N - 1 : ℕ)) : ℕ∞) : WithBot ℕ∞) := by
    refine iSup_le fun p => ?_
    show ((p.length : ℕ) : WithBot ℕ∞) ≤ ((((N - 1 : ℕ)) : ℕ∞) : WithBot ℕ∞)
    have hk := key p
    rw [hD] at hk
    have h3 : p.length + 1 ≤ N := by
      have h2 := WithBot.coe_le_coe.mp hk
      exact_mod_cast h2
    have h4 : p.length ≤ N - 1 := by omega
    rw [← WithBot.coe_natCast]
    exact WithBot.coe_le_coe.mpr (by exact_mod_cast h4)
  have h5 : N - 1 < N := by omega
  have h6 : (((N - 1 : ℕ)) : ℕ∞) < ((N : ℕ) : ℕ∞) := by exact_mod_cast h5
  rw [topologicalKrullDim_eq_iSup_length (Z := ↥Y), hD]
  exact lt_of_le_of_lt hbound (WithBot.coe_lt_coe.mpr h6)
end FunctorialResolution.EmbeddedResolution
