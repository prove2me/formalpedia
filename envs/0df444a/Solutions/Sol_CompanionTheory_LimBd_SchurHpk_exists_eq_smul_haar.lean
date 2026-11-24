-- Prove2me | solution 1 for CompanionTheory.LimBd.SchurHpk.exists_eq_smul_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:01:26.970617+00:00
-- url     : https://prove2.me/submissions/f06114be-9af9-4ebe-b5b0-ef02358cd093

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.SchurHpk
open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal
namespace CompanionTheory.LimBd.SchurHpk
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν μ : Measure G)
    [SigmaFinite ν] [ν.IsMulLeftInvariant] (hν : ν ≠ 0) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ν = c • μ := by
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have e := measure_eq_div_smul ν μ (s := K₀) (Measure.measure_pos_of_nonempty_interior μ K₀.interior_nonempty).ne'
    K₀.isCompact.measure_ne_top
  refine ⟨_, fun h0 => hν (by rw [e, h0, zero_smul]), fun hT => ?_, e⟩
  rw [hT] at e
  have h1 : ∀ n, μ (spanningSets ν n) = 0 := by
    intro n
    by_contra hn
    have h3 := measure_spanningSets_lt_top ν n
    have h4 := congrArg (fun m : Measure G => m (spanningSets ν n)) e
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.top_mul hn] at h4
    exact h3.ne h4
  have h2 : μ Set.univ = 0 := by
    rw [← iUnion_spanningSets ν]
    exact measure_iUnion_null h1
  exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne' h2
end CompanionTheory.LimBd.SchurHpk
