-- Prove2me | solution 1 for Formalism.UG.P.mk_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:02.237793+00:00
-- url     : https://prove2.me/submissions/e5a1657f-9599-45d5-bafb-a8162832df07

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AutomorphicFormsDecompositionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G] (Γ K : Subgroup G)
namespace Formalism.UG.P
theorem _root_.solution (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c)
    (c : ClassSet Γ K) (g : G) (γ : Γ) (κ : K) (e : g = (γ : G) * s c * κ) :
    DoubleCoset.mk Γ K g = c := by
  conv_rhs => rw [← hs c]
  rw [DoubleCoset.eq]
  refine ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, (κ : G)⁻¹, K.inv_mem κ.2, ?_⟩
  rw [e]
  group
end Formalism.UG.P
