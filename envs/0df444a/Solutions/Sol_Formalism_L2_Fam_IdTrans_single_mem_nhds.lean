-- Prove2me | solution 1 for Formalism.L2.Fam.IdTrans.single_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:56:17.935961+00:00
-- url     : https://prove2.me/submissions/aa9e0379-ceba-465e-ae6c-8e178b1e4fb8

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_NumberFieldFamilies_IdTransSM
import Theorems.Thm_Formalism_L2_Fam_IdTrans_isOpen_integers
import Theorems.Thm_Formalism_L2_Fam_IdTrans_finiteSingle_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Filter Topology
open Formalism Formalism.L2 Formalism.L2.Fam Formalism.L2.Fam.IdTrans
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.L2.Fam.IdTrans
theorem _root_.solution {S : Set (AdeleRing (𝓞 L) L)} (hS : S ∈ 𝓝 (1 : AdeleRing (𝓞 L) L)) :
    ∃ I : Set (HeightOneSpectrum (𝓞 L)), I.Finite ∧ ∀ v ∉ I, ∀ (x : v.adicCompletion L) (_hx : x ∈ v.adicCompletionIntegers L),
      (((1 : InfiniteAdeleRing L), finiteSingle L v x) : AdeleRing (𝓞 L) L) ∈ S := by
  have hS' : S ∈ 𝓝 (((1 : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L)) : InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L) := hS
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.mp hS'
  have hw' : w ∈ Filter.map (RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) cofinite)
      (𝓝 (1 : Π v : HeightOneSpectrum (𝓞 L), v.adicCompletionIntegers L)) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap (fun v => isOpen_integers v)]
    exact hw
  have hw'' : RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) cofinite ⁻¹' w ∈
      𝓝 (1 : Π v : HeightOneSpectrum (𝓞 L), v.adicCompletionIntegers L) := hw'
  rw [nhds_pi, Filter.mem_pi] at hw''
  obtain ⟨I, hI, t, ht, hIt⟩ := hw''
  refine ⟨I, hI, fun v hv x hx => huw ⟨mem_of_mem_nhds hu, ?_⟩⟩
  classical
  have hf : (Pi.mulSingle v (⟨x, hx⟩ : v.adicCompletionIntegers L) : Π v : HeightOneSpectrum (𝓞 L),
      v.adicCompletionIntegers L) ∈ I.pi t := by
    intro w' hw'
    have hne : w' ≠ v := fun h => hv (h ▸ hw')
    rw [Pi.mulSingle_eq_of_ne hne]
    exact mem_of_mem_nhds (ht w')
  have := hIt hf
  show finiteSingle L v x ∈ w
  rw [finiteSingle_eq v x hx]
  exact this
end Formalism.L2.Fam.IdTrans
