-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.main_le_two_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:22.093878+00:00
-- url     : https://prove2.me/submissions/65a0d980-f5ea-4acd-ad3c-96403c5dce26

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution {P m k : ℝ} (hP : 0 ≤ P) (hk : |k| ≤ 1 / 2) (h : |P - m| ≤ k * m) :
    |m| ≤ 2 * P ∧ |P - m| ≤ 2 * |k| * P := by
  have h0 : k * m ≤ |k| * |m| := by rw [← abs_mul]; exact le_abs_self _
  have h1 : |k| * |m| ≤ 1 / 2 * |m| := mul_le_mul_of_nonneg_right hk (abs_nonneg m)
  have h2 : |m| - |P| ≤ |m - P| := abs_sub_abs_le_abs_sub m P
  rw [abs_sub_comm, abs_of_nonneg hP] at h2
  have hm : |m| ≤ 2 * P := by linarith
  refine ⟨hm, ?_⟩
  have h3 : |k| * |m| ≤ |k| * (2 * P) := mul_le_mul_of_nonneg_left hm (abs_nonneg k)
  linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
