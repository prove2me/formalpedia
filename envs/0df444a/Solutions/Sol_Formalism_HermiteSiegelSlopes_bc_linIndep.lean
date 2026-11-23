-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.bc_linIndep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:27.149861+00:00
-- url     : https://prove2.me/submissions/4fe28436-6451-4395-8b74-fb4e5b689db6

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution {j : ℕ} (e : Fin j → ι → F) (he : LinearIndependent F e) :
    LinearIndependent E (fun a => bcMap (E := E) (e a)) := by
  classical
  let T : (Fin j → F) →ₗ[F] (ι → F) := Fintype.linearCombination F e
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact he.fintypeLinearCombination_injective
  obtain ⟨π, hπ⟩ := T.exists_leftInverse_of_injective hT
  have key : ∀ a c, ∑ i, π (Pi.single i 1) a * e c i = if c = a then 1 else 0 := by
    intro a c
    have h1 : π (e c) = Pi.single c 1 := by
      have h2 : T (Pi.single c 1) = e c := by
        simp [T, Fintype.linearCombination_apply, Pi.single_apply]
      rw [← h2]
      exact LinearMap.congr_fun hπ _
    have h3 : e c = ∑ i, e c i • (Pi.single i 1 : ι → F) := by
      funext i'
      simp [Finset.sum_apply, Pi.single_apply]
    have h4 : π (e c) a = ∑ i, π (Pi.single i 1) a * e c i := by
      conv_lhs => rw [h3]
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← h4, h1]
    simp [Pi.single_apply, eq_comm]
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have h0 : ∑ i, algebraMap F E (π (Pi.single i 1) a) * (∑ c, g c • bcMap (E := E) (e c)) i = 0 := by
    rw [hg]; simp
  have h1 : ∑ i, algebraMap F E (π (Pi.single i 1) a) * (∑ c, g c • bcMap (E := E) (e c)) i
      = ∑ c, g c * algebraMap F E (∑ i, π (Pi.single i 1) a * e c i) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bcMap, Finset.mul_sum, map_sum, map_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
  rw [h1] at h0
  simpa [key] using h0
end Formalism.HermiteSiegelSlopes
