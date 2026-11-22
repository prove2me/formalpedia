-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.isUnitIn_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:18.367215+00:00
-- url     : https://prove2.me/submissions/481a5973-beb6-483c-86f6-1d261f1624d7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K} {π : K}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution {a b : K} (ha : a ∈ S) (hb : b ∈ S) (hab : IsUnitIn S (a * b)) :
    IsUnitIn S b := by
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hab.1
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hab.1
  refine ⟨hb0, hb, ?_⟩
  have : b⁻¹ = a * (a * b)⁻¹ := by field_simp
  rw [this]
  exact S.mul_mem ha hab.2.2
end Formalism.HermitianLattices.Ext.L3.U0
