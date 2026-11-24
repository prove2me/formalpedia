-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mco_filter_eq_antidiag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:31.3685+00:00
-- url     : https://prove2.me/submissions/3677dc13-1f65-4927-bac2-2e5b531f45e0

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
theorem _root_.solution {Y N n : ℕ} (hn : 1 ≤ n) (hnY : n ≤ Y) (hYN : Y ≤ N) :
    (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n) = n.divisorsAntidiagonal := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨h, by omega⟩
  · rintro ⟨h, -⟩
    have ha : a ≠ 0 := by
      rintro rfl
      omega
    have hb : b ≠ 0 := by
      rintro rfl
      omega
    have ha' : a ≤ n := Nat.le_of_dvd (by omega) (Dvd.intro b h)
    have hb' : b ≤ n := Nat.le_of_dvd (by omega) (Dvd.intro_left a h)
    exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, h⟩
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
