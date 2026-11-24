-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.le_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:30:51.719979+00:00
-- url     : https://prove2.me/submissions/2b4ad9b4-e877-491d-b761-939a99b737b1

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
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
omit [Module K V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution [∀ w : FinPl K, Module (Rloc w) V]
    [∀ w : FinPl K, IsScalarTower (𝓞 K) (Rloc w) V] {A B : Submodule (𝓞 K) V}
    (h : ∀ w : FinPl K, Submodule.span (Rloc w) (A : Set V) ≤ Submodule.span (Rloc w) (B : Set V)) :
    A ≤ B := by
  intro x hx
  let I : Ideal (𝓞 K) := B.colon {x}
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    let w : FinPl K := ⟨m, hm⟩
    have := w.2.isPrime
    have i0 := isLocalizedModule_id w.1.primeCompl V (Rloc w)
    have hxB : x ∈ Submodule.span (Rloc w) (B : Set V) := h w (Submodule.subset_span hx)
    have hspan : Submodule.span (Rloc w) (B : Set V) =
        B.localized' (Rloc w) w.1.primeCompl LinearMap.id := by
      rw [Submodule.localized'_eq_span]; simp
    rw [hspan, Submodule.mem_localized'] at hxB
    obtain ⟨y, hy, s, hs⟩ := hxB
    rw [IsLocalizedModule.mk'_eq_iff] at hs
    have hsI : (s : 𝓞 K) ∈ I := by
      rw [Submodule.mem_colon_singleton]
      have : (s : 𝓞 K) • x = y := hs.symm
      rw [this]; exact hy
    exact s.2 (hIm hsI)
  have h1 : (1 : 𝓞 K) ∈ I := by rw [hI]; exact Submodule.mem_top
  rw [Submodule.mem_colon_singleton, one_smul] at h1
  exact h1
end Formalism.LFunctionChainParameters.slopeLatticeData
