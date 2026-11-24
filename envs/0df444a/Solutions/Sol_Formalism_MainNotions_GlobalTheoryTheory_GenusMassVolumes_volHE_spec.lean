-- Prove2me | solution 1 for Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.volHE_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:40:18.600285+00:00
-- url     : https://prove2.me/submissions/4b6e000f-d516-4b24-9f6e-5c0c9387457b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FrameTransport

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
theorem _root_.solution (G : GaugeFam F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (h : ∃ 𝓕, IsFDH F E σ M J (G.μ M J) 𝓕) :
    ∃ 𝓕, IsFDH F E σ M J (G.μ M J) 𝓕 ∧ volHE G M J = G.μ M J 𝓕 := by
  have hf : HasFundamentalDomain (HFinIn (AF F) σ J) (HA (AF F) σ J) (G.μ M J) := ⟨h⟩
  refine ⟨hf.ExistsIsFundamentalDomain.choose, hf.ExistsIsFundamentalDomain.choose_spec, ?_⟩
  simp [volHE, covolume, hf]
end Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
