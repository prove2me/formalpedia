-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.pLen_simple_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:29:32.169631+00:00
-- url     : https://prove2.me/submissions/60d8ecd9-88e0-42e7-b9f7-08e738420a2a

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_idem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono


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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution (p m : Ideal R) [hp : p.IsMaximal] [hm : m.IsMaximal] (h : p ≠ m)
    {A C : Submodule R W} (hkill : ∀ s ∈ m, ∀ x ∈ A, s • x ∈ C) : pLen p A C = 0 := by
  have hnle : ¬ m ≤ p := fun hle => h (hm.eq_of_le hp.ne_top hle).symm
  obtain ⟨s, hsm, hsp⟩ := SetLike.not_le_iff_exists.1 hnle
  have hA : A ≤ localization₂ p C := fun x hx => ⟨s, hsp, hkill s hsm x hx⟩
  have hle : localization₂ p A ≤ localization₂ p C := by
    have := locBasic_locS_mono p.primeCompl hA
    unfold localization₂ at this ⊢
    rwa [locBasic_locS_idem] at this
  unfold pLen
  rw [Submodule.comap_subtype_eq_top.2 hle]
  simp
end Formalism.LFunctionChainParameters.LLcv
