-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.orderCertificate_mono_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:24:08.243665+00:00
-- url     : https://prove2.me/submissions/5990b8cb-f538-4436-a2b4-20c6e964b501

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
private theorem forall_orderCertificate_of_subset {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : OrderCertificate W p N μ Mem Z) :
    ∀ Mem' : Set ↥W, Mem ⊆ Mem' → OrderCertificate W p N μ Mem' Z := by
  refine @OrderCertificate.rec k ‹Field k›
    (fun W p I m Mem Z _ => ∀ Mem' : Set ↥W, Mem ⊆ Mem' → PrincipalizationCertificate W p I m Mem' Z)
    (fun W p N μ Mem Z _ => ∀ Mem' : Set ↥W, Mem ⊆ Mem' → OrderCertificate W p N μ Mem' Z)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ W p N μ Mem Z h
  · intro W p I m Mem Z hmem Mem' hs
    exact PrincipalizationCertificate.memory (Set.Subset.trans hmem hs)
  · intro W p I m Mem Z hm Mem' _
    exact PrincipalizationCertificate.large hm
  · intro W p I m Mem Z M N μ hI hM hmu hZ _ ih Mem' hs
    exact PrincipalizationCertificate.toOrder M N μ hI (Set.Subset.trans hM hs) hmu hZ (ih Mem' hs)
  · intro W p I m Mem Z U hU _ ih Mem' hs
    exact PrincipalizationCertificate.localize U hU fun z hz =>
      ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hs)
  · intro W p N μ Mem Z hmem Mem' hs
    exact OrderCertificate.memory (Set.Subset.trans hmem hs)
  · intro W p N μ Mem Z hmu Mem' _
    exact OrderCertificate.large hmu
  · intro W p N μ Mem Z U hU _ ih Mem' hs
    exact OrderCertificate.localize U hU fun z hz =>
      ih z hz ((U z hz).ι.base ⁻¹' Mem') (Set.preimage_mono hs)
  · intro W p N μ Mem Z U hU H hH hNsubH hZH J hJnone hJcomp hJloc _ ih Mem' hs
    refine OrderCertificate.descend U hU H hH hNsubH hZH J hJnone hJcomp ?_ ?_
    · intro z hz Jz hJ x hx
      exact hJloc z hz Jz hJ x fun hm => hx (hs hm)
    · intro z hz Jz hJ
      exact ih z hz Jz hJ (((H z hz).subschemeι ≫ (U z hz).ι).base ⁻¹' Mem')
        (Set.preimage_mono hs)
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem Mem' : Set ↥W} {Z : W.IdealSheafData} (hsub : Mem ⊆ Mem')
    (h : OrderCertificate W p N μ Mem Z) :
    OrderCertificate W p N μ Mem' Z :=
  forall_orderCertificate_of_subset h Mem' hsub
end FunctorialResolution.EmbeddedResolution
