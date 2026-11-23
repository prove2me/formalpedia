-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.gg_isLatIn_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:04.276883+00:00
-- url     : https://prove2.me/submissions/3a88e006-11cd-4381-8188-554261b98d1f

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locS_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution [FiniteDimensional K Z] (W : Submodule K Z) (B : Submodule (𝓞 K) Z)
    (hB : IsLatIn ⊤ B) : IsLatIn W (cut W B) := by
  constructor
  · have hno : IsNoetherian (𝓞 K) B := isNoetherian_of_fg_of_noetherian B hB.1
    have h1 : ((cut W B).comap B.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map B.subtype
    rw [Submodule.map_comap_subtype] at h2
    have : B ⊓ cut W B = cut W B := inf_eq_right.mpr inf_le_left
    rwa [this] at h2
  · apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      exact hx.2
    · intro z hz
      have htop := Formalism.HermitianLatticesTheory.indexBasic_locS_top (K := K) B hB.2
      have hz' : z ∈ Formalism.HermitianLatticesTheory.locS (nonZeroDivisors (𝓞 K)) B := by rw [htop]; trivial
      obtain ⟨d, hd, hdz⟩ := hz'
      have hd0 : (d : K) ≠ 0 := by
        have := nonZeroDivisors.ne_zero hd
        exact_mod_cast this
      have e : z = (d : K)⁻¹ • (d • z) := by
        rw [← algebraMap_smul K d z, smul_smul, inv_mul_cancel₀ hd0, one_smul]
      rw [e]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨hdz, ?_⟩)
      rw [← algebraMap_smul K d z]
      exact W.smul_mem _ hz
end Formalism.EigenvalueLevelCeiling
