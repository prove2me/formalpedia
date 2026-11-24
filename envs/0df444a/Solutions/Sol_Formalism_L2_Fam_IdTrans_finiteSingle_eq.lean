-- Prove2me | solution 1 for Formalism.L2.Fam.IdTrans.finiteSingle_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:56.097942+00:00
-- url     : https://prove2.me/submissions/6822bcd9-fe76-4f7a-9dbc-7f48fe235582

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_NumberFieldFamilies_IdTransSM

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
open Classical
namespace Formalism.L2.Fam.IdTrans
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (x : v.adicCompletion L) (hx : x ∈ v.adicCompletionIntegers L) :
    finiteSingle L v x = RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) cofinite
      (Pi.mulSingle v (⟨x, hx⟩ : v.adicCompletionIntegers L)) := by
  apply RestrictedProduct.ext
  intro w
  show (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v x w) =
    ((Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => ↥(w.adicCompletionIntegers L)) v ⟨x, hx⟩ w :
      w.adicCompletionIntegers L) : w.adicCompletion L)
  by_cases h : w = v
  · subst h
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h]
    rfl
end Formalism.L2.Fam.IdTrans
