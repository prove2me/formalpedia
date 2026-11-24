-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.normRepCount_eq_eulerFac_inert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:16.08905+00:00
-- url     : https://prove2.me/submissions/c9919c23-0083-462a-9b13-5cecff3ac593

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localDensity

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
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) :
    (normRepCount K (P ^ k) M n : ℝ) =
      Real.sqrt (Ideal.absNorm P : ℝ) ^ ((2 * M - 1) * k) * (Formalism.HermitianLatticesTheory.eulerFac K M P)⁻¹ := by
  rw [(localDensity K hK P hP M k hM hk n hn hnP).1 hc, Formalism.HermitianLatticesTheory.eulerFac, if_pos hc, inv_inv]
end Formalism.HermitianLattices.Ext.L3
