-- Prove2me | solution 1 for Formalism.ELL.WeierstrassChordSeries.eq_single_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:38.670865+00:00
-- url     : https://prove2.me/submissions/eb2b83c8-1cae-4c4d-bbe5-31a888ca965f

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
namespace Formalism.ELL.WeierstrassChordSeries
theorem _root_.solution (e : Fin 2 →₀ ℕ) :
    (e = Finsupp.single 1 (e 1) ↔ e 0 = 0) ∧ (e = Finsupp.single 0 (e 0) ↔ e 1 = 0) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [h]
    simp [Finsupp.single_apply]
  · ext j
    fin_cases j <;> simp [h, Finsupp.single_apply]
  · rw [h]
    simp [Finsupp.single_apply]
  · ext j
    fin_cases j <;> simp [h, Finsupp.single_apply]
end Formalism.ELL.WeierstrassChordSeries
