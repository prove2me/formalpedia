-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Eta.galE_cQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:53.997257+00:00
-- url     : https://prove2.me/submissions/cae2ffc6-164c-4a6a-85e5-c75f42e2b050

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_NcardEqTwoIff
import Theorems.Thm_Formalism_FrobeniusOrbits_Eta_cases
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGalois
import Theorems.Thm_Formalism_FrobeniusOrbits_hostReal_at
import Theorems.Thm_Formalism_FrobeniusOrbits_isCMField_hostE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Eta
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Eta
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) :
    galE e ζ a b (cQ hqd h) = cc e := by
  haveI := isCMField_hostE hqd h
  obtain ⟨-, -, hmul, hbij⟩ := hostGalois e q d hqd L ζ a b h
  obtain ⟨σ0, hσ0⟩ := hbij.2 (cc e)
  have hfix := fun x => ((hostReal_at hqd h).2 x).1
  let τ : hostE ζ a b ≃ₐ[hostF ζ a b] hostE ζ a b :=
    AlgEquiv.ofRingEquiv (f := σ0.toRingEquiv) (fun r => (hfix _).mp r.2 σ0 hσ0)
  rcases cases (hostE ζ a b) τ with h1 | h1
  · exfalso
    have hσ1 : σ0 = 1 := AlgEquiv.ext fun x => DFunLike.congr_fun h1 x
    have g1 : galE e ζ a b 1 = 1 := map_one (MonoidHom.mk' (galE e ζ a b) hmul)
    rw [hσ1, g1] at hσ0
    have := congrArg (fun x : GG e => ((x.1.1 : ℤˣ) : ℤ)) hσ0
    simp [cc, c0] at this
  · have hc : cQ hqd h = σ0 :=
      AlgEquiv.ext fun x => (DFunLike.congr_fun h1 x).symm
    rw [hc, hσ0]
end Formalism.FrobeniusOrbits.Eta
