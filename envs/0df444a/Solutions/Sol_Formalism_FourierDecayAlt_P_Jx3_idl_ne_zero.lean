-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.idl_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:38.365837+00:00
-- url     : https://prove2.me/submissions/d8599cc5-aa69-44da-bf40-fc82daba96f1

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_rd_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
namespace Formalism.FourierDecayAlt.P.Jx3
theorem _root_.solution (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (k ν : ℤ)
    (hg : 0 < g) : S6.idl E g k ν ≠ 0 := by
  intro h
  have h1 := hN E g k ν hg
  rw [h] at h1
  have hpos : 0 < ((g : ℝ) ^ k * S6.rd E ^ ν) ^ S6.deg E := by
    have := rd_pos E
    have hg' : (0 : ℝ) < g := by exact_mod_cast hg
    positivity
  simp at h1
  rw [← h1] at hpos
  exact lt_irrefl _ hpos
end Formalism.FourierDecayAlt.P.Jx3
