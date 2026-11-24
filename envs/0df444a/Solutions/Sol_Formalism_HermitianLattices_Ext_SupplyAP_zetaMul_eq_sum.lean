-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.zetaMul_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:34.808935+00:00
-- url     : https://prove2.me/submissions/2cd763c1-c044-4f6d-9d92-4b9882408d5b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
open Finset
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency.types false
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    DirichletCharacter.zetaMul χ n = ∑ d ∈ n.divisors, χ (d : ZMod q) := by
  simp only [DirichletCharacter.zetaMul, toArithmeticFunction, ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.coe_mk]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  simp [this]
end Formalism.HermitianLattices.Ext.SupplyAP
