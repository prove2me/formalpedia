-- Prove2me | solution 1 for EisTube.tubeExtends_farCone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:29:01.450801+00:00
-- url     : https://prove2.me/submissions/a98c228a-880f-42cb-9ca4-11b6e74ec902

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
import Theorems.Thm_EisTube_tubeExtends

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory
open EisTube
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
variable {ι : Type} [Fintype ι]
namespace EisTube
theorem _root_.solution {J : Type*} [Fintype J]
    (P : Type*) [TopologicalSpace P] [FirstCountableTopology P]
    (a : J → ι → ℝ) (R : ℝ) (hR : 0 ≤ R) (hne : (farCone a R).Nonempty)
    (Ω : Set (ι → ℝ)) (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hpos : farCone a R ⊆ Ω) (hneg : ∀ x ∈ farCone a R, -x ∈ Ω)
    (h : P → ℝ) (h0 : ∀ p, 0 ≤ h p) (hloc : ∀ p, ∃ U ∈ 𝓝 p, BddAbove (h '' U))
    (F : (ι → ℂ) → P → ℂ)
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω))
    (hcont : ∀ z ∈ tube Ω, Continuous (F z))
    (hbd : ∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N) :
    ∃ G : (ι → ℂ) → P → ℂ,
      (∀ p, Differentiable ℂ (fun z => G z p)) ∧
      (∀ z ∈ tube Ω, ∀ p, G z p = F z p) ∧
      Continuous (Function.uncurry G) ∧
      (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p, ‖G z p‖ ≤ C * h p) := by
  refine tubeExtends P Ω hΩo hΩc ?_ h h0 hloc F hhol hcont hbd
  intro v
  obtain ⟨x₀, hx₀⟩ := hne
  have hd : ∀ j, 0 < ∑ i, x₀ i * a j i := fun j => lt_of_le_of_lt hR (hx₀ j)
  set s : ℝ := 1 + ∑ j, (R + |∑ i, v i * a j i|) / ∑ i, x₀ i * a j i with hs
  have key : ∀ j, R + |∑ i, v i * a j i| < s * ∑ i, x₀ i * a j i := by
    intro j
    have hle : (R + |∑ i, v i * a j i|) / ∑ i, x₀ i * a j i ≤
        ∑ j, (R + |∑ i, v i * a j i|) / ∑ i, x₀ i * a j i :=
      Finset.single_le_sum (f := fun j => (R + |∑ i, v i * a j i|) / ∑ i, x₀ i * a j i)
        (fun j _ => div_nonneg (add_nonneg hR (abs_nonneg _)) (hd j).le) (Finset.mem_univ j)
    have h1 : (1 + (R + |∑ i, v i * a j i|) / ∑ i, x₀ i * a j i) * ∑ i, x₀ i * a j i ≤
        s * ∑ i, x₀ i * a j i :=
      mul_le_mul_of_nonneg_right (by rw [hs]; linarith) (hd j).le
    rw [add_mul, one_mul, div_mul_cancel₀ _ (hd j).ne'] at h1
    linarith [hd j]
  have hsum : ∀ (u w : ι → ℝ) (c : ℝ) j,
      ∑ i, (u + c • w) i * a j i = ∑ i, u i * a j i + c * ∑ i, w i * a j i := by
    intro u w c j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
  have m1 : v + s • x₀ ∈ farCone a R := fun j => by
    rw [hsum]; linarith [key j, neg_abs_le (∑ i, v i * a j i)]
  have m2 : -v + s • x₀ ∈ farCone a R := fun j => by
    rw [hsum]
    have : ∑ i, (-v) i * a j i = -∑ i, v i * a j i := by
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [this]; linarith [key j, le_abs_self (∑ i, v i * a j i)]
  refine ⟨v + s • x₀, hpos m1, -(-v + s • x₀), hneg _ m2, ?_⟩
  funext i
  simp [midpoint_eq_smul_add]
  ring
end EisTube
