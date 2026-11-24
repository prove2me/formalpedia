-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_diff_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:49.029075+00:00
-- url     : https://prove2.me/submissions/2ce6e46e-afdb-4d8c-a8ab-c3870fe6cb4f

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution (g : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc 1 b, g n = ∑ n ∈ Icc 1 a, g n + ∑ n ∈ Ioc a b, g n := by
  have h1 : Icc 1 b = Icc 1 a ∪ Ioc a b := by
    ext n
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  rw [h1, sum_union]
  rw [disjoint_left]
  intro n h2 h3
  simp only [mem_Icc, mem_Ioc] at h2 h3
  omega
end Formalism.HermitianLattices.Ext.BoxTail
