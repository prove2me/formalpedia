-- Prove2me | solution 1 for Formalism.HN.DualPolygon.misc_mem_dual_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:15.187835+00:00
-- url     : https://prove2.me/submissions/7dde7ba5-abe9-4f5d-beb7-965c92d031d1

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open nonZeroDivisors
namespace Formalism.HN.DualPolygon
theorem _root_.solution (t : K) :
    t ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ s : 𝓞 K, ∃ z : ℤ, Algebra.trace ℚ K (t * (s : K)) = z := by
  have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := one_ne_zero
  rw [FractionalIdeal.mem_dual h1]
  constructor
  · intro h s
    obtain ⟨z, hz⟩ := h (s : K) ((FractionalIdeal.mem_one_iff _).2 ⟨s, rfl⟩)
    exact ⟨z, by simpa [Algebra.traceForm_apply] using hz.symm⟩
  · intro h a ha
    obtain ⟨s, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨z, hz⟩ := h s
    exact ⟨z, by simpa [Algebra.traceForm_apply] using hz.symm⟩
end Formalism.HN.DualPolygon
