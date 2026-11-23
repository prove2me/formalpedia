-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz7.prod_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:36.260794+00:00
-- url     : https://prove2.me/submissions/4d6c9806-4708-4e64-b95e-53d32773d5fb

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz7
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz7
theorem _root_.solution (f : ℕ → ℝ) (k l : ℕ) (hl : 1 ≤ l) (hlk : l + 2 ≤ k) :
    ∏ i ∈ Icc 1 (k - 1), f i =
      (∏ i ∈ Ico 1 l, f i) * (f l * ((∏ i ∈ Ico (l + 1) (k - 1), f i) * f (k - 1))) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have e1 : n + 1 - 1 = n := by omega
  rw [e1]
  have e2 : Icc 1 n = Ico 1 (n + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [e2, ← Finset.prod_Ico_consecutive f hl (by omega : l ≤ n + 1),
    Finset.prod_eq_prod_Ico_succ_bot (by omega : l < n + 1),
    Finset.prod_Ico_succ_top (by omega : l + 1 ≤ n)]
end Formalism.FourierDecayAlt.P.Sz7
