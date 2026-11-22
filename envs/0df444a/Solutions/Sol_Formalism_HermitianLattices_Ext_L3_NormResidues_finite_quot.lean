-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormResidues.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:18.742918+00:00
-- url     : https://prove2.me/submissions/45ed7233-c377-451a-8e8c-6b814bedd6f5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne

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
open Formalism.HermitianLattices.Ext.L3.NormResidues
namespace Formalism.HermitianLattices.Ext.L3.NormResidues
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : Finite (𝓞 K ⧸ P) := by
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hcard : Nat.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h0 : Nat.card (𝓞 K ⧸ P) ≠ 0 := by
    rw [hcard]
    exact fun h => hne (Ideal.absNorm_eq_zero_iff.mp h)
  exact Nat.finite_of_card_ne_zero h0
end Formalism.HermitianLattices.Ext.L3.NormResidues
