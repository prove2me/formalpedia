-- Prove2me | solution 1 for Formalism.L2.Host.finiteSingle_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:53:04.952798+00:00
-- url     : https://prove2.me/submissions/062b3c0a-4acf-4042-842d-01400aec1bca

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAEPf
import Theorems.Thm_Formalism_L2_Host_isOpen_integers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.L2.Host
theorem _root_.solution (Vf : Set (FiniteAdeleRing (𝓞 L) L)) (hV : Vf ∈ nhds (1 : FiniteAdeleRing (𝓞 L) L)) :
    ∃ S : Set (HeightOneSpectrum (𝓞 L)), S.Finite ∧ ∀ v, v ∉ S → ∀ y : v.adicCompletion L,
      y ∈ v.adicCompletionIntegers L → finiteSingle L v y ∈ Vf := by
  classical
  have hσ := RestrictedProduct.isOpenEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
    (A := fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) isOpen_integers
  have h1 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) Filter.cofinite 1 = 1 :=
    RestrictedProduct.ext _ _ fun i => rfl
  have h2 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) Filter.cofinite ⁻¹' Vf ∈ nhds 1 := by
    apply hσ.continuous.continuousAt.preimage_mem_nhds
    rw [h1]
    exact hV
  rw [nhds_pi, Filter.mem_pi] at h2
  obtain ⟨I, hI, t, ht, hsub⟩ := h2
  refine ⟨I, hI, fun v hv y hy => ?_⟩
  have hmem : (Pi.mulSingle v (⟨y, hy⟩ : ((v.adicCompletionIntegers L : Set (v.adicCompletion L)))) :
      (i : HeightOneSpectrum (𝓞 L)) → ((i.adicCompletionIntegers L : Set (i.adicCompletion L)))) ∈ I.pi t := by
    intro i hi
    have hne : i ≠ v := fun e => hv (e ▸ hi)
    rw [Pi.mulSingle_eq_of_ne hne]
    exact mem_of_mem_nhds (ht i)
  have hg := hsub hmem
  have e : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) Filter.cofinite (Pi.mulSingle v ⟨y, hy⟩) =
      finiteSingle L v y := by
    apply RestrictedProduct.ext
    intro i
    rw [RestrictedProduct.structureMap_apply]
    show _ = Pi.mulSingle v y i
    by_cases hi : i = v
    · subst hi
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi]
      rfl
  rw [← e]
  exact hg
end Formalism.L2.Host
