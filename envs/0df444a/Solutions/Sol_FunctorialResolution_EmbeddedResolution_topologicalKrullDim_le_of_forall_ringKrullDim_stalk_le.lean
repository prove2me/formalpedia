-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.topologicalKrullDim_le_of_forall_ringKrullDim_stalk_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:31:38.092802+00:00
-- url     : https://prove2.me/submissions/7d1f2321-0fcc-485a-a3fa-d4301a81c49a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_AffineSpaceJacobson
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StalkKrullDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem specializes_of_fromSpecStalk_base_specializes {X : Scheme.{u}} (x : X)
    {a b : PrimeSpectrum (X.presheaf.stalk x)}
    (hab : (X.fromSpecStalk x).base a ⤳ (X.fromSpecStalk x).base b) : a ⤳ b := by
  have hemb : Topology.IsEmbedding (X.fromSpecStalk x).base :=
    AlgebraicGeometry.Scheme.Hom.isEmbedding (X.fromSpecStalk x)
  exact hemb.toIsInducing.specializes_iff.mp hab
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (X : Scheme.{u}) (d : WithBot ℕ∞)
    (h : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ d) :
    topologicalKrullDim X ≤ d := by
  unfold topologicalKrullDim
  refine iSup_le fun p => ?_
  have hSM := p.strictMono
  have key : ∀ i : Fin (p.length + 1), ∃ z : X, closure ({z} : Set X) = (p i : Set X) := by
    intro i
    obtain ⟨z, hz⟩ := QuasiSober.sober (p i).isIrreducible' (p i).isClosed'
    exact ⟨z, hz⟩
  choose y hy using key
  have hspec : ∀ i j : Fin (p.length + 1), i ≤ j → y j ⤳ y i := by
    intro i j hij
    have hsub : (p i : Set X) ⊆ (p j : Set X) :=
      SetLike.coe_subset_coe.mpr (hSM.monotone hij)
    have hmem : y i ∈ closure ({y j} : Set X) := by
      rw [hy j]
      apply hsub
      rw [← hy i]
      exact subset_closure rfl
    exact specializes_iff_mem_closure.mpr hmem
  have hinj : Function.Injective y := by
    intro i j hij
    apply hSM.injective
    apply SetLike.coe_injective
    rw [← hy i, ← hy j, hij]
  have hrange : ∀ i : Fin (p.length + 1),
      ∃ z : PrimeSpectrum (X.presheaf.stalk (y 0)), (X.fromSpecStalk (y 0)).base z = y i := by
    intro i
    have hmem : y i ∈ Set.range (X.fromSpecStalk (y 0)).base := by
      rw [Scheme.range_fromSpecStalk]
      exact hspec 0 i (Fin.zero_le i)
    exact hmem
  choose q hq using hrange
  have hg : StrictMono (fun i : Fin (p.length + 1) => q i.rev) := by
    intro i j hij
    have hlt : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
    have hsp : (X.fromSpecStalk (y 0)).base (q i.rev) ⤳ (X.fromSpecStalk (y 0)).base (q j.rev) := by
      rw [hq i.rev, hq j.rev]
      exact hspec j.rev i.rev hlt.le
    have hle : q i.rev ≤ q j.rev :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr
        (specializes_of_fromSpecStalk_base_specializes (y 0) hsp)
    refine lt_of_le_of_ne hle ?_
    intro hcon
    have hcon' : q i.rev = q j.rev := hcon
    have hyy : y i.rev = y j.rev :=
      (hq i.rev).symm.trans
        ((congrArg (fun z : PrimeSpectrum (X.presheaf.stalk (y 0)) =>
          (X.fromSpecStalk (y 0)).base z) hcon').trans (hq j.rev))
    have h4 := congrArg Fin.rev (hinj hyy)
    rw [Fin.rev_rev, Fin.rev_rev] at h4
    exact absurd h4 (ne_of_lt hij)
  have hlen : (p.length : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk (y 0)) :=
    le_iSup (fun t : LTSeries (PrimeSpectrum (X.presheaf.stalk (y 0))) => (t.length : WithBot ℕ∞))
      ⟨p.length, fun i => q i.rev, fun i => hg Fin.castSucc_lt_succ⟩
  exact le_trans hlen (h (y 0))
end FunctorialResolution.EmbeddedResolution
