-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.relIndex_conj_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:30.744136+00:00
-- url     : https://prove2.me/submissions/d9b7a634-b54e-4213-a077-db63f4244aa3

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
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G))
    (hc : IsCompact (K₀ : Set G)) (g : G) :
    (K₀.map (MulAut.conj g).toMonoidHom).relIndex K₀ ≠ 0 := by
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 hc
  have hopen : IsOpen (((K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀ : Subgroup K₀) :
      Set K₀) := by
    have : (((K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀ : Subgroup K₀) : Set K₀) =
        Subtype.val ⁻¹' ((fun x => g⁻¹ * x * g) ⁻¹' (K₀ : Set G)) := by
      ext k
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [this]
    exact (hK.preimage (by fun_prop)).preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ hopen
  exact Subgroup.index_ne_zero_of_finite
end Formalism.DoubleCosetMeasures.P
