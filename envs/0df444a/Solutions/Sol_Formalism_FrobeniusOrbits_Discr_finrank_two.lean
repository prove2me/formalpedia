-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.finrank_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:39.638162+00:00
-- url     : https://prove2.me/submissions/0f6bc140-e6af-4328-a75e-5e90fdbb3208

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_isIntegral_over_adjoin_add_inv_of_isPrimitiveRoot
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_minpoly_eq
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_adjoin_top

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
    Module.finrank ℚ⟮z + z⁻¹⟯ K = 2 := by
  have hint := isIntegral_over_adjoin_add_inv_of_isPrimitiveRoot hz
  have htop : IntermediateField.adjoin ℚ⟮z + z⁻¹⟯ {z} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ (by rw [adjoin_top hz]; exact Algebra.mem_top)
  calc Module.finrank ℚ⟮z + z⁻¹⟯ K
      = Module.finrank ℚ⟮z + z⁻¹⟯ (⊤ : IntermediateField ℚ⟮z + z⁻¹⟯ K) :=
        IntermediateField.finrank_top'.symm
    _ = Module.finrank ℚ⟮z + z⁻¹⟯ (IntermediateField.adjoin ℚ⟮z + z⁻¹⟯ {z}) :=
        (IntermediateField.equivOfEq htop).toLinearEquiv.finrank_eq.symm
    _ = (minpoly ℚ⟮z + z⁻¹⟯ z).natDegree := IntermediateField.adjoin.finrank hint
    _ = 2 := by rw [minpoly_eq hz]; compute_degree!
end Formalism.FrobeniusOrbits.Discr
