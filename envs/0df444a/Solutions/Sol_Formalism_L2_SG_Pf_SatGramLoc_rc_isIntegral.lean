-- Prove2me | solution 1 for Formalism.L2.SG.Pf.SatGramLoc.rc_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:40.79088+00:00
-- url     : https://prove2.me/submissions/46cb5f44-8fd9-458c-964c-821a8c272a5a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.SatGramLoc
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.SG.Pf.SatGramLoc
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F)
    (hx : x ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E)
      (v.adicCompletionIntegers F).toSubring) :
    letI := rcIntAlg (E := E) v
    IsIntegral (v.adicCompletionIntegers F) x := by
  letI := rcIntAlg (E := E) v
  unfold Formalism.UG.tensInt Formalism.UG.intOE at hx
  refine (Subring.closure_le (t := (integralClosure (v.adicCompletionIntegers F)
    (E ⊗[F] v.adicCompletion F)).toSubring).2 ?_) hx
  rintro _ (⟨a, rfl⟩ | ⟨y, rfl⟩)
  · have ha : IsIntegral ℤ (a : E) := by
      obtain ⟨b, hb⟩ := a.2
      rw [← hb]
      first
      | exact b.isIntegral_coe
      | exact b.2
      | exact NumberField.RingOfIntegers.isIntegral_coe b
    exact IsIntegral.map_of_comp_eq (Int.castRingHom (v.adicCompletionIntegers F))
      (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E) (B := v.adicCompletion F))
      (RingHom.ext_int _ _) ha
  · show IsIntegral _ (algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) y)
    exact isIntegral_algebraMap
end Formalism.L2.SG.Pf.SatGramLoc
