-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.tendsto_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:40.255531+00:00
-- url     : https://prove2.me/submissions/34871f23-b2e4-4bd6-9fde-818248cffa2b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumCoset
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution (e : ℕ) :
    Tendsto (fun j : ℕ => (((j : ℝ) ^ 2) ^ e) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ e)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun j : ℕ => (j : ℝ) / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    refine (tendsto_natCast_div_add_atTop (1 : ℝ)).congr fun j => ?_
    push_cast
    rfl
  have h2 := (h1.pow 2).pow e
  simp only [one_pow] at h2
  exact h2.congr fun j => by rw [div_pow, div_pow]
end Formalism.HermitianLattices.Ext.L3.BoxSum
