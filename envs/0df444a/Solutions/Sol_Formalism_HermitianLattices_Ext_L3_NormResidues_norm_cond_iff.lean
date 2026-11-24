-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormResidues.norm_cond_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:34.805322+00:00
-- url     : https://prove2.me/submissions/99c61d30-dad3-4345-bf27-2939b2df485f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_conjO_sum_norm

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open NormResidues
open Formalism.HermitianLattices.Ext.L3.NormResidues
namespace Formalism.HermitianLattices.Ext.L3.NormResidues
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P)
    (M : ℕ) (n : 𝓞 K) (hn : conjO K n = n) (y : Fin M → 𝓞 K) :
    Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (∑ i, conjO K (y i) * y i) =
        Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) n ↔
      ∑ i, Ideal.Quotient.mk P (conjO K (y i)) * Ideal.Quotient.mk P (y i) =
        Ideal.Quotient.mk P n := by
  rw [Ideal.Quotient.eq, mem_mul_conjIdeal hP hc, map_sub, conjO_sum_norm, hn, and_self,
    ← Ideal.Quotient.eq, map_sum]
  simp only [map_mul]
end Formalism.HermitianLattices.Ext.L3.NormResidues
