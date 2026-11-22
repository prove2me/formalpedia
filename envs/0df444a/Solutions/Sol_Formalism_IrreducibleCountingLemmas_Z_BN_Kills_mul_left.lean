-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.Kills.mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:46:04.651799+00:00
-- url     : https://prove2.me/submissions/e2a1d34a-29e3-4e78-9d97-3fedc8e8baf9

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
namespace Formalism.IrreducibleCountingLemmas.Z.BN
namespace Kills
theorem _root_.solution {K A : Type} [Field K] [Ring A] [Algebra K A] {t : Finset (A → K[X])}
    {a : A} (h : Kills t a) (b : A) : Kills t (b * a) := by
  intro F hF
  obtain ⟨S, i1, i2, i3, i4, i5, hFS, hS⟩ := h F hF
  exact ⟨S, i1, i2, i3, i4, i5, hFS, fun s => by rw [mul_smul, hS, smul_zero]⟩
end Kills
end Formalism.IrreducibleCountingLemmas.Z.BN
