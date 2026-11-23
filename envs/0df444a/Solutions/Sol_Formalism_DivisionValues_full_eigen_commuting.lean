-- Prove2me | solution 1 for Formalism.DivisionValues.full_eigen_commuting
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:29.745109+00:00
-- url     : https://prove2.me/submissions/5190fa2a-c1f8-43e6-b077-e24a04401a84

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_exists_retract
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_fnl_extSpan
import Theorems.Thm_P2M_Formalism_DivisionValues_FinitelyNonzeroLinear_map_mulVec__22fb7428e0b1
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_mem_extSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open FinitelyNonzeroLinear
namespace Formalism.DivisionValues
theorem _root_.solution : FullEigComm := by
  intro K Ω _ _ j n 𝒯 Z hZ B hB z hz
  obtain ⟨S, hS⟩ := hZ
  obtain ⟨ρ, hρ⟩ := exists_retract j
  have hstab : ∀ χ, ∀ x ∈ simEig j 𝒯 χ, B.map j *ᵥ x ∈ simEig j 𝒯 χ := by
    intro χ x hx
    have hx' : ∀ T ∈ 𝒯, (T.map j).mulVec x = χ T • x := hx
    show ∀ T ∈ 𝒯, (T.map j).mulVec (B.map j *ᵥ x) = χ T • (B.map j *ᵥ x)
    intro T hT
    have hc : T.map j * B.map j = B.map j * T.map j := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, hB T hT]
    rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hx' T hT, Matrix.mulVec_smul]
  have hle : (⨆ χ ∈ S, simEig j 𝒯 χ) ≤ (⨆ χ ∈ S, simEig j 𝒯 χ).comap (B.map j).mulVecLin := by
    refine iSup₂_le fun χ hχ => ?_
    intro x hx
    rw [Submodule.mem_comap, Matrix.mulVecLin_apply]
    exact (le_iSup₂ (f := fun χ (_ : χ ∈ S) => simEig j 𝒯 χ) χ hχ) (hstab χ x hx)
  have hmem : (fun i => j ((B *ᵥ z) i)) ∈ extSpan j Z := by
    have e := map_mulVec' (j := j) B z
    rw [← e, hS]
    have hz' : (fun i => j (z i)) ∈ ⨆ χ ∈ S, simEig j 𝒯 χ := by
      rw [← hS]
      exact mem_extSpan hz
    exact hle hz'
  have h := fnl_extSpan Z _ hmem ρ
  simp only [hρ] at h
  exact h
end Formalism.DivisionValues
