-- Prove2me | solution 1 for Formalism.L2.Host.mus_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:52:05.238748+00:00
-- url     : https://prove2.me/submissions/35a2631c-a50e-4c25-b6df-473eac7364d1

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.L2.Host
theorem _root_.solution {M N : ℕ} (h : M ∣ N) : mus M ⊆ mus N := by
  intro z hz
  obtain ⟨c, rfl⟩ := h
  show z ^ (M * c) = 1
  rw [pow_mul, show z ^ M = 1 from hz, one_pow]
end Formalism.L2.Host
