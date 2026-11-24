-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.J.nO_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:16.54126+00:00
-- url     : https://prove2.me/submissions/65dd411d-259d-4ec3-bad7-fd99d1444f3f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_nO_prod
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.J
namespace Formalism.HermitianLattices.Ext.L3.D2.J
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {z : K} (hz : z ∈ pK K 𝔭 0) (hz0 : z ≠ 0)
    (n : ℕ) : z ^ n ∈ pK K 𝔭 0 ∧ nO 𝔭 (z ^ n) = nO 𝔭 z ^ n := by
  simpa using nO_prod h𝔭 (Finset.range n) (fun _ => z) (fun _ => ⟨hz, hz0⟩)
end Formalism.HermitianLattices.Ext.L3.D2.J
