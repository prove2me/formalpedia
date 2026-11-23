-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.exists_inv_mod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:29.845581+00:00
-- url     : https://prove2.me/submissions/8385f2af-c78b-424d-b176-52c885db7a92

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
theorem _root_.solution {J : Ideal (𝓞 K)} {a : 𝓞 K} (h : IsCoprime (Ideal.span {a}) J) :
    ∃ b : 𝓞 K, Ideal.Quotient.mk J a * Ideal.Quotient.mk J b = 1 := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hi
  refine ⟨b, ?_⟩
  rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq, ← hij]
  have e : a * b - (b * a + j) = -j := by ring
  rw [e]
  exact J.neg_mem hj
end Formalism.HermitianLattices.Ext.L3.NormLifting
