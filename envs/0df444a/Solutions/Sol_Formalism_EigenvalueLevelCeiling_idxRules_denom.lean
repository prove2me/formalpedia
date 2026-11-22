-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.idxRules_denom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:52:12.249351+00:00
-- url     : https://prove2.me/submissions/f83a3833-d494-4fc3-9953-c3662d36f9ee

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_alg_ne
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {V' : Type*} [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (B : Submodule R V) {x : V} (hx : x ∈ Submodule.span K (B : Set V)) :
    x ∈ locS R⁰ B := by
  induction hx using Submodule.span_induction with
  | mem x h => exact locBasic_le_locS _ _ h
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul k x _ hx =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    refine ⟨b * d, mul_mem hb hd, ?_⟩
    have hb0 : algebraMap R K b ≠ 0 := idxRules_alg_ne (nonZeroDivisors.ne_zero hb)
    have e : (b * d) • ((algebraMap R K a / algebraMap R K b) • x) = a • (d • x) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K a, ← algebraMap_smul K d, smul_smul,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [e]
    exact B.smul_mem a hdx
end Formalism.EigenvalueLevelCeiling
