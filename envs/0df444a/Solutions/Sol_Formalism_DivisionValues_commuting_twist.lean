-- Prove2me | solution 1 for Formalism.DivisionValues.commuting_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:12.092625+00:00
-- url     : https://prove2.me/submissions/e8355de7-6d3c-477a-b649-4fcd912b60f1

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_normal_idem
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_extSpan_eq_range
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_comm_ext
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_posDef_all
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_herm_of_pos
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_isUnit_of_pos
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_exists_proj
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_adj_matrix
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_comm_of_stable
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_map_conjTranspose_twist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_map_twist_of_mem
import Theorems.Thm_Formalism_HN_twist


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
theorem _root_.solution : CommTwist := by
  intro K _ _ _ K0 hK0 v0 hv0 n H hH hpos 𝒯 h𝒯 hcomm hadj Z hZ σ
  obtain ⟨e, hee, heH, h1, h2⟩ := exists_proj hv0 (hpos v0) Z
  have hHh : Hᴴ = H := herm_of_pos hv0 (hpos v0)
  have hHu : IsUnit H := isUnit_of_pos (hpos v0)
  have hadjK : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, Tᴴ * H = H * T' := by
    intro T hT
    obtain ⟨T', hT', h⟩ := hadj T hT
    exact ⟨T', hT', adj_matrix h⟩
  have hec := comm_of_stable hHh hHu hadjK hZ heH h1 h2
  have hPD := posDef_all hpos σ
  have hMM : e.map (twist σ) * e.map (twist σ) = e.map (twist σ) := by
    rw [← Matrix.map_mul, hee]
  have hMadj : (e.map (twist σ))ᴴ * H.map σ = H.map σ * e.map σ := by
    have := congrArg (fun X => X.map σ) heH
    simp only [Matrix.map_mul] at this
    rwa [map_conjTranspose_twist] at this
  have hMc : ∀ T ∈ 𝒯, e.map (twist σ) * T.map σ = T.map σ * e.map (twist σ) := by
    intro T hT
    have h3 := congrArg (fun X => X.map (twist σ)) (hec T fun T' hT' => hcomm T hT T' hT')
    simp only [Matrix.map_mul] at h3
    rwa [map_twist_of_mem hK0 σ T (h𝒯 T hT)] at h3
  have hEM : e.map σ * e.map (twist σ) = e.map (twist σ) * e.map σ := comm_ext σ hec _ hMc
  have heq := normal_idem hPD (e.map (twist σ)) (e.map σ) hMM hMadj hEM
  show extSpan σ Z = extSpan (twist σ) Z
  rw [extSpan_eq_range Z e h1 h2, extSpan_eq_range Z e h1 h2, heq]
end Formalism.DivisionValues
