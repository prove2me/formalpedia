-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.adjoin_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:07.862195+00:00
-- url     : https://prove2.me/submissions/3b993adf-20f3-4387-9abd-e6baa840c56b

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.Discr
variable {K : Type*} [Field K] [NumberField K] {e : ℕ} {z : K}
variable [IsCyclotomicExtension {2 ^ (e + 2)} ℚ K]
namespace Formalism.FrobeniusOrbits.Discr
theorem _root_.solution (hz : IsPrimitiveRoot z (2 ^ (e + 2))) :
    Algebra.adjoin ℚ⟮z + z⁻¹⟯ {z} = ⊤ := by
  have hne : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩
  have h := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := ℚ) hz
  rw [eq_top_iff] at h ⊢
  intro x _
  have hx : x ∈ Algebra.adjoin ℚ {z} := h Algebra.mem_top
  have hle : Algebra.adjoin ℚ {z} ≤ (Algebra.adjoin ℚ⟮z + z⁻¹⟯ {z}).restrictScalars ℚ :=
    Algebra.adjoin_le Algebra.subset_adjoin
  exact hle hx
end Formalism.FrobeniusOrbits.Discr
