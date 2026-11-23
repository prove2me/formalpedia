-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.dcMap_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:27.550894+00:00
-- url     : https://prove2.me/submissions/3c22dc47-bb20-457f-af12-2094496deb6b

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
variable {G : Type} [Group G]
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (K₀ : Subgroup G) (g : G) (k k' : K₀) :
    dcMap K₀ g k = dcMap K₀ g k' ↔
      k⁻¹ * k' ∈ (K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀ := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  simp only [dcMap, QuotientGroup.eq]
  simp [mul_assoc]
end Formalism.DoubleCosetMeasures.P
