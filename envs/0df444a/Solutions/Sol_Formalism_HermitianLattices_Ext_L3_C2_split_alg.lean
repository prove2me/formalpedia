-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.C2.split_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:41.551494+00:00
-- url     : https://prove2.me/submissions/c177bd35-1c27-4723-a48a-30f1a5fb802b

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
theorem _root_.solution (q : ℝ) (hq : q ≠ 0) (M : ℕ) (hM : 1 ≤ M) :
    q ^ (2 * M - 1) - q ^ (M - 1) = q ^ (2 * M - 1) * (1 - q ^ (-(M : ℤ))) := by
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.add_sub_cancel, zpow_neg]
  rw [show ((j + 1 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp
  ring
end Formalism.HermitianLattices.Ext.L3.C2
