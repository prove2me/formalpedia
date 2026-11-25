-- Prove2me | solution 1 for BayesianPersuasion.Proof.noInformation_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:09:15.804594+00:00
-- url     : https://prove2.me/submissions/b1318ee9-75ce-43e9-8bea-6b5d74091630

module
public import Definitions.Def_BayesianPersuasion_Signals
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Mathlib.Analysis.Convex.Jensen
public import Definitions.Def_BayesianPersuasion_Attainment

set_option autoImplicit true
@[expose] public section
public section
universe uΩ uA
open Set Finset
open BayesianPersuasion
variable {Ω : Type uΩ} {A : Type uA} [Fintype Ω]
open BayesianPersuasion.Proof
namespace BayesianPersuasion.Proof
theorem _root_.solution (u v : A → Ω → ℝ) (p : Belief Ω) :
    signalValue u v p noInformationSignal = senderPayoff u v p := by
  have hm : ∀ s : Fin 1, signalMass p noInformationSignal s = 1 := by
    intro s
    simpa [signalMass, noInformationSignal] using p.property.2
  have hb : ∀ s : Fin 1, signalPosterior p noInformationSignal s = p := by
    intro s
    apply Subtype.ext
    funext ω
    simp [signalPosterior, posteriorVector, hm, noInformationSignal]
  simp [signalValue, hm, hb]
end BayesianPersuasion.Proof
