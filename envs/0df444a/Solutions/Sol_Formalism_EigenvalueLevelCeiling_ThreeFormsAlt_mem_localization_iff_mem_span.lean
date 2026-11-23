-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.mem_localization_iff_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:58.934797+00:00
-- url     : https://prove2.me/submissions/c5ea70f4-fa1d-49cd-b74e-e23a088dd7e8

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_algebraMap_ne_zero_of_notMem
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_mem_OO
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
namespace Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) Z) (x : Z) :
    x ∈ localization₂ w.asIdeal M ↔ x ∈ Submodule.span (OO w) (M : Set Z) := by
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hs0 := algebraMap_ne_zero_of_notMem w.asIdeal hs
    have hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ OO w := (mem_OO w _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : OO w) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact locBasic_le_locS _ M hy
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := hy
      obtain ⟨r, t, ht, hat⟩ := (mem_OO w a).mp a.2
      refine ⟨t * s, mul_mem ht hs, ?_⟩
      have ht0 := algebraMap_ne_zero_of_notMem w.asIdeal ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
