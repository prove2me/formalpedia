-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.principalizationCertificate_mono_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:15.951383+00:00
-- url     : https://prove2.me/submissions/5df29144-0600-42ef-ac47-6332a364759a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificateMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem forall_principalizationCertificate_of_subset {k : Type u} [Field k]
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    ∀ Mem' : Set ↥W, Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z := by
  refine PrincipalizationCertificate.rec
    (motive_1 := fun W p I m Mem Z _ =>
      ∀ Mem' : Set ↥W, Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z)
    (motive_2 := fun W p N μ Mem Z _ =>
      ∀ Mem' : Set ↥W, Mem ⊆ Mem' → OrderCertificate W p N μ Mem' Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intro W p I m Mem Z hmem Mem' hsub
    exact PrincipalizationCertificate.memory (Set.Subset.trans hmem hsub)
  · intro W p I m Mem Z hm Mem' _
    exact PrincipalizationCertificate.large hm
  · intro W p I m Mem Z M N μ hI hM hmu hZ _ ih Mem' hsub
    exact PrincipalizationCertificate.toOrder M N μ hI (Set.Subset.trans hM hsub) hmu hZ (ih Mem' hsub)
  · intro W p I m Mem Z U hU _ ih Mem' hsub
    refine PrincipalizationCertificate.localize U hU ?_
    intro z hz
    exact ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hsub)
  · intro W p N μ Mem Z hmem Mem' hsub
    exact OrderCertificate.memory (Set.Subset.trans hmem hsub)
  · intro W p N μ Mem Z hmu Mem' _
    exact OrderCertificate.large hmu
  · intro W p N μ Mem Z U hU _ ih Mem' hsub
    refine OrderCertificate.localize U hU ?_
    intro z hz
    exact ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hsub)
  · intro W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih Mem' hsub
    refine OrderCertificate.descend U hU H hH hNsubH hZH J hJnone hJcomp ?_ ?_
    · intro z hz Jz hJz x hx
      exact hJloc z hz Jz hJz x fun hmem => hx (hsub hmem)
    · intro z hz Jz hJz
      exact ih z hz Jz hJz (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem')
        (Set.preimage_mono hsub)
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem Mem' : Set ↥W} {Z : W.IdealSheafData} (hsub : Mem ⊆ Mem')
    (h : PrincipalizationCertificate W p I m Mem Z) :
    PrincipalizationCertificate W p I m Mem' Z :=
  forall_principalizationCertificate_of_subset h Mem' hsub
end FunctorialResolution.EmbeddedResolution
