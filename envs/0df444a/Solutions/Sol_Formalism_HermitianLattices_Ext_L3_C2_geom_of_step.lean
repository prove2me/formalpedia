-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.C2.geom_of_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:32.950866+00:00
-- url     : https://prove2.me/submissions/26374765-686c-4ce3-b814-dc815bbbbd98

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.C2
namespace Formalism.HermitianLattices.Ext.L3.C2
theorem _root_.solution (c : ℕ → ℕ) (a : ℕ) (h : ∀ k, 1 ≤ k → c (k + 1) = a * c k) (k : ℕ)
    (hk : 1 ≤ k) : c k = a ^ (k - 1) * c 1 := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [h n hn, ih, show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
    ring
end Formalism.HermitianLattices.Ext.L3.C2
