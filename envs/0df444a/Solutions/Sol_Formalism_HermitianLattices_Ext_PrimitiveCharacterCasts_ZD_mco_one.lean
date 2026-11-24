-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mco_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:31.597646+00:00
-- url     : https://prove2.me/submissions/3f404be7-b4c4-4b95-bdbc-58fb3b75b7b9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZMoll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution {Y N : ℕ} (hY : 1 ≤ Y) (hN : 1 ≤ N) : mco Y N 1 = 1 := by
  unfold mco
  have h : (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = 1) = {(1, 1)} := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_Icc, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨ha1, -⟩, hb1, -⟩, h⟩
      constructor <;> nlinarith
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨⟨le_rfl, hY⟩, le_rfl, hN⟩, rfl⟩
  rw [h, sum_singleton]
  simp
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
