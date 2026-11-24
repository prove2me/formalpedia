-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.length_at_span_localized
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:30:52.900155+00:00
-- url     : https://prove2.me/submissions/120d2b3e-cda5-4abf-967f-e7a44cc25807

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem

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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (w : Ideal R)
    [w.IsPrime] [Module (Localization.AtPrime w) V] [IsScalarTower R (Localization.AtPrime w) V]
    (A B : Submodule R V) (hBA : B ≤ A) (A'' : Submodule (Localization.AtPrime w) V)
    (hA : haveI := isLocalizedModule_id w.primeCompl V (Localization.AtPrime w)
      A.localized' (Localization.AtPrime w) w.primeCompl LinearMap.id = A'') :
    locLen w (A ⧸ B.comap A.subtype) = Module.length (Localization.AtPrime w)
      (A'' ⧸ (Submodule.span (Localization.AtPrime w) (B : Set V)).comap A''.subtype) := by
  have i0 := isLocalizedModule_id w.primeCompl V (Localization.AtPrime w)
  subst hA
  set f1 := A.toLocalized' (Localization.AtPrime w) w.primeCompl LinearMap.id with hf1
  have hf1c : ∀ a : A, ((f1 a : V)) = (a : V) := fun a => rfl
  have hB : (B.comap A.subtype).localized' (Localization.AtPrime w) w.primeCompl f1 =
      (Submodule.span (Localization.AtPrime w) (B : Set V)).comap
        (A.localized' (Localization.AtPrime w) w.primeCompl LinearMap.id).subtype := by
    have hspan : Submodule.span (Localization.AtPrime w) (B : Set V) =
        B.localized' (Localization.AtPrime w) w.primeCompl LinearMap.id := by
      rw [Submodule.localized'_eq_span]; simp
    rw [hspan]
    ext x
    rw [Submodule.mem_localized', Submodule.mem_comap, Submodule.mem_localized']
    constructor
    · rintro ⟨m, hm, s, hx⟩
      refine ⟨(m : V), hm, s, ?_⟩
      rw [IsLocalizedModule.mk'_eq_iff] at hx ⊢
      have := congrArg Subtype.val hx
      simpa [hf1c] using this
    · rintro ⟨m, hm, s, hx⟩
      refine ⟨⟨m, hBA hm⟩, hm, s, ?_⟩
      rw [IsLocalizedModule.mk'_eq_iff] at hx ⊢
      apply Subtype.ext
      simpa [hf1c] using hx
  rw [← hB]
  exact ((IsLocalizedModule.iso w.primeCompl ((B.comap A.subtype).toLocalizedQuotient'
    (Localization.AtPrime w) w.primeCompl f1)).extendScalarsOfIsLocalization w.primeCompl
      (Localization.AtPrime w)).length_eq
end Formalism.LFunctionChainParameters.slopeLatticeData
