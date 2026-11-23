-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.isCoprime_span_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:35.228445+00:00
-- url     : https://prove2.me/submissions/c2c576cf-9fdc-4fa9-8eac-52882f141ed1

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
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {a : 𝓞 K} (ha : a ∉ P) :
    IsCoprime (Ideal.span {a}) P := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h
  have h2 := hP.eq_of_le h le_sup_right
  exact ha (by rw [h2]; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))
end Formalism.HermitianLattices.Ext.L3.NormLifting
