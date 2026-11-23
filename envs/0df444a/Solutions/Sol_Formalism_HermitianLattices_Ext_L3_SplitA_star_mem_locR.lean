-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.SplitA.star_mem_locR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:35:49.670083+00:00
-- url     : https://prove2.me/submissions/f01d2c3a-4dd6-4773-8821-195a5940018b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_conjO_mem_hcompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.SplitA
theorem _root_.solution (p : Ideal (𝓞 K)) {c : K} (hc : c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) :
    starRingEnd K c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
  obtain ⟨s, hs, hc⟩ := hc
  refine ⟨conjO K s, conjO_mem_hcompl p hs, ?_⟩
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp hc
  refine Submodule.mem_one.mpr ⟨conjO K r, ?_⟩
  rw [Algebra.smul_def] at hr ⊢
  show starRingEnd K (algebraMap (𝓞 K) K r) = _
  rw [hr, map_mul]
  rfl
end Formalism.HermitianLattices.Ext.L3.SplitA
