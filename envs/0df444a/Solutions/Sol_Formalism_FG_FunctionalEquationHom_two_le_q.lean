-- Prove2me | solution 1 for Formalism.FG.FunctionalEquationHom.two_le_q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:37.280429+00:00
-- url     : https://prove2.me/submissions/bf15da36-e080-4e38-a865-c23729b5ca64

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffExpandEqZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.FunctionalEquationHom
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.FG.FunctionalEquationHom
theorem _root_.solution {p q : ℕ} {σ : K →+* K} (h : FunctionalEquationSetting K p q σ) : 2 ≤ q := by
  unfold FunctionalEquationSetting at h
  obtain ⟨hp, ⟨k, hk, rfl⟩, -, -⟩ := h
  calc 2 ≤ p := hp.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
end Formalism.FG.FunctionalEquationHom
