-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:15:33.623113+00:00
-- url     : https://prove2.me/submissions/4b1a0d64-bac7-4427-bade-a2203f0bd278

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaH_Imports
import Definitions.Def_Lemmata_GeneralBFactThirdVariant_Imports
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatTheta
import Theorems.Thm_Bl_FirstBlockLemmaH_goal1
import Theorems.Thm_Bl_general_b_fact_third_variant_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open NumberField TensorProduct
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis ι E V) (Ψ : Finset (E →+* ℂ)) (M : Submodule (𝓞 E) V)
variable {Ψ}
variable {b M}
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (hfg : Module.Finite (𝓞 E) M) :
    ∃ s ∈ (𝓞 E)⁰, ∀ v ∈ M, ∀ i,
      algebraMap (𝓞 E) E s * b.repr v i ∈ (algebraMap (𝓞 E) E).range := by
  first | exact Bl.FirstBlockLemmaH.goal1 .. | (apply Bl.FirstBlockLemmaH.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaH.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaH.goal1 <;> assumption) | (intros; apply @Bl.FirstBlockLemmaH.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaH.goal1 <;> first | assumption | infer_instance) | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› ι ‹_› ‹_› b M hfg | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› ι ‹_› ‹_› b M | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› ι ‹_› ‹_› b | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› ι ‹_› ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› ι ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› ι | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E
end Formalism.L2.Pj.DatLin
