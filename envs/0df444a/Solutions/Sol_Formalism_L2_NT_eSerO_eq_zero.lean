-- Prove2me | solution 1 for Formalism.L2.NT.eSerO_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:27:04.939109+00:00
-- url     : https://prove2.me/submissions/6db8088e-c90c-4fc4-87b6-26b7ed995cf3

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Theorems.Thm_Formalism_L2_NT_hasLabelO_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.PT
variable {g : ℕ} [Fact g.Prime]
namespace Formalism.L2.NT
theorem _root_.solution {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) (r : ℕ) (f : (ZMod g)[X])
    (hf : ¬ (f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0)) : eSerO O r f = 0 := by
  unfold eSerO
  apply finsum_eq_zero_of_forall_eq_zero
  intro z
  have hne : ¬ ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f :=
    fun ⟨_, _, _, hτ⟩ => hf (hasLabelO_spec O hτ)
  haveI : IsEmpty (∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f) := ⟨hne⟩
  exact finsum_of_isEmpty _
end Formalism.L2.NT
