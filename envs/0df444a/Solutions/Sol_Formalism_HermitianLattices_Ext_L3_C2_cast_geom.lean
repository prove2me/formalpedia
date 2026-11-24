-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.C2.cast_geom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:39.548294+00:00
-- url     : https://prove2.me/submissions/8fa9ba58-4bf0-479e-a58e-0837b535d258

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_C2_geom_of_step

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
theorem _root_.solution (c : ℕ → ℕ) (q N : ℕ) (X : ℝ) (h : ∀ k, 1 ≤ k → c (k + 1) = q ^ N * c k)
    (h1 : (c 1 : ℝ) = (q : ℝ) ^ N * X) (k : ℕ) (hk : 1 ≤ k) :
    (c k : ℝ) = (q : ℝ) ^ (N * k) * X := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [geom_of_step c (q ^ N) h (j + 1) hk]
  push_cast
  rw [h1]
  ring
end Formalism.HermitianLattices.Ext.L3.C2
