-- Prove2me | solution 1 for Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.volHE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:18.423583+00:00
-- url     : https://prove2.me/submissions/784ec642-d672-4507-9806-9526db0b51d9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FrameTransport
import Theorems.Thm_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_volHE_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
theorem _root_.solution (G : GaugeFam F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (c : ENNReal)
    (h : AllSome (IsFDH F E σ M J (G.μ M J)) fun 𝓕 => G.μ M J 𝓕 = c) : volHE G M J = c := by
  obtain ⟨𝓕, h1, h2⟩ := volHE_spec G M J h.1
  rw [h2, h.2 𝓕 h1]
end Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
