-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.absNorm_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:42.023091+00:00
-- url     : https://prove2.me/submissions/622cca9d-62cc-4b96-888e-27b8ee07dd95

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_mem_boxSet_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_absNorm_eq_prod_of_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_card_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K := by
  rw [absNorm_eq_prod_of_mem hK hF hn, ← card_real hK hF, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun w _ => (((mem_boxSet_iff hK hF).1 hn) w).1.le)
    fun w _ => (((mem_boxSet_iff hK hF).1 hn) w).2
end Formalism.HermitianLattices.Ext.L3.BoxSum
