-- Prove2me | solution 1 for ConnesGreen.actual_zero_original_actor_picard_limit
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T13:19:21.158998+00:00
-- url     : https://prove2.me/submissions/ceaee4e8-92b9-41a5-8264-1b4d000b5ddc

import Theorems.Thm_ConnesGreen_actual_zero_negative_form_obstruction
import Definitions.Def_WeilMarker_regularized_cost
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped InnerProductSpace ComplexOrder Topology
open ContinuousLinearMap Filter Set
noncomputable section
namespace WeilDefect.MarkerStability
open WeilDefect.WDT13
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem inverse_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A) :
    0 ≤ operatorInverse A := by
  rw [operatorInverse, Ring.inverse_of_isUnit hA.isUnit]
  exact CFC.inv_nonneg_of_nonneg hA.isUnit.unit (by simpa using hA.nonneg)

theorem inverse_smul (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (c : ℝ) (hc : 0 < c) :
    operatorInverse (c • A) = c⁻¹ • operatorInverse A := by
  have hunit := (hA.smul hc).isUnit
  have hright : (c • A) * (c⁻¹ • operatorInverse A) = 1 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_inv_cancel₀ hc.ne', one_smul]
    exact Ring.mul_inverse_cancel A hA.isUnit
  calc
    operatorInverse (c • A) = operatorInverse (c • A) * 1 := (mul_one _).symm
    _ = operatorInverse (c • A) * ((c • A) * (c⁻¹ • operatorInverse A)) := by rw [hright]
    _ = (operatorInverse (c • A) * (c • A)) * (c⁻¹ • operatorInverse A) := (mul_assoc _ _ _).symm
    _ = c⁻¹ • operatorInverse A := by
      rw [show operatorInverse (c • A) * (c • A) = 1 from Ring.inverse_mul_cancel _ hunit,
        one_mul]

theorem cost_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : 0 ≤ selectedCost A N := by
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (inverse_nonnegative A hA)).conj_adjoint N.adjoint
  simpa [selectedCost] using (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp

theorem cost_mono {A B : H →L[ℂ] H}
    (hAB : A ≤ B) (hA : IsStrictlyPositive A) (N : K →L[ℂ] H) :
    selectedCost B N ≤ selectedCost A N := by
  have hi := CStarAlgebra.ringInverse_le_ringInverse hAB hA
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr hi)).conj_adjoint N.adjoint
  apply sub_nonneg.mp
  simpa [selectedCost, operatorInverse, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.sub_comp] using (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hp

theorem cost_smul (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) (c : ℝ) (hc : 0 < c) :
    selectedCost (c • A) N = c⁻¹ • selectedCost A N := by
  rw [selectedCost, inverse_smul A hA c hc]
  ext x
  simp [selectedCost]

theorem marker_nonnegative (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : 0 ≤ marker A N :=
  inverse_nonnegative _ (isStrictlyPositive_one.add_nonneg (cost_nonnegative A hA N))

theorem marker_le_one (A : H →L[ℂ] H) (hA : IsStrictlyPositive A)
    (N : K →L[ℂ] H) : marker A N ≤ 1 := by
  have h := CStarAlgebra.ringInverse_le_ringInverse
    (le_add_of_nonneg_right (cost_nonnegative A hA N)) isStrictlyPositive_one
  simpa [marker, operatorInverse] using h


end WeilDefect.MarkerStability
namespace WeilDefect.MarkerStability
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
theorem scalar_identity_mono {a b : ℝ} (hab : a ≤ b) : a • (1 : K →L[ℂ] K) ≤ b • 1 := smul_le_smul_of_nonneg_right hab zero_le_one
end WeilDefect.MarkerStability
namespace WeilDefect.MarkerStability
open WeilDefect.WDT13

/-- A monotone family in a compact subset of a closed partial order has a
right limit; it is the greatest lower bound of the positive-parameter values. -/
theorem exists_compact_monotone_right_limit {E : Type*} [TopologicalSpace E]
    [PartialOrder E] [OrderClosedTopology E] (f : ℝ → E) (C : Set E)
    (hC : IsCompact C) (hmem : ∀ ε : ℝ, 0 < ε → f ε ∈ C)
    (hmono : MonotoneOn f (Ioi (0 : ℝ))) :
    ∃ G₀ : E, G₀ ∈ C ∧ IsGLB (f '' Ioi (0 : ℝ)) G₀ ∧
      Tendsto f (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds G₀) := by
  have hev : ∀ᶠ ε in nhdsWithin 0 (Ioi (0 : ℝ)), f ε ∈ C :=
    by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hmem ε hε
  obtain ⟨G₀, hG₀, hc⟩ := hC.exists_mapClusterPt (Filter.tendsto_principal.mpr hev)
  have hglb : ∀ y : E, MapClusterPt y (nhdsWithin 0 (Ioi (0 : ℝ))) f →
      IsGLB (f '' Ioi (0 : ℝ)) y := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rintro _ ⟨ε, hε, rfl⟩
      apply isClosed_Iic.mem_of_mapClusterPt hy
      filter_upwards [Ioo_mem_nhdsGT hε] with η hη
      exact hmono hη.1 hε hη.2.le
    · intro z hz
      apply isClosed_Ici.mem_of_mapClusterPt hy
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hz (mem_image_of_mem f hε)
  refine ⟨G₀, hG₀, hglb G₀ hc, ?_⟩
  apply hC.tendsto_nhds_of_unique_mapClusterPt hev
  intro y _ hy
  exact (hglb y hy).unique (hglb G₀ hc)

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem marker_mono {A B : H →L[ℂ] H} (hAB : A ≤ B)
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) (N : K →L[ℂ] H) :
    marker A N ≤ marker B N := by
  exact CStarAlgebra.ringInverse_le_ringInverse
    (by simpa only [add_comm] using add_le_add_left (cost_mono hAB hA N) 1)
    (isStrictlyPositive_one.add_nonneg (cost_nonnegative B hB N))

theorem regularized_marker_monotone (L : H →L[ℂ] H) (hL : 0 ≤ L)
    (N : K →L[ℂ] H) : MonotoneOn (fun ε : ℝ => marker (L + ε • 1) N) (Ioi 0) := by
  intro ε hε η hη heη
  exact marker_mono (A := L + ε • 1) (B := L + η • 1)
    (by simpa only [add_comm] using add_le_add_left (scalar_identity_mono (K := H) heη) L)
    (IsStrictlyPositive.nonneg_add hL (isStrictlyPositive_one.smul hε))
    (IsStrictlyPositive.nonneg_add hL (isStrictlyPositive_one.smul hη)) N

theorem regularized_marker_norm_le_one (L : H →L[ℂ] H) (hL : 0 ≤ L)
    (N : K →L[ℂ] H) (ε : ℝ) (hε : 0 < ε) :
    ‖marker (L + ε • 1) N‖ ≤ 1 := by
  have ha : IsStrictlyPositive (L + ε • (1 : H →L[ℂ] H)) :=
    IsStrictlyPositive.nonneg_add hL (isStrictlyPositive_one.smul hε)
  apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (by norm_num : (0 : ℝ) ≤ 1)
    (marker_nonnegative _ ha N)).mpr
  simpa using marker_le_one _ ha N

/-- Original finite selected marker: the inner regularization norm limit exists
without a range, tail-rate, inverse-cost or arithmetic positivity premise. -/
theorem finite_selected_marker_norm_limit_aux [FiniteDimensional ℂ K]
    (L : H →L[ℂ] H) (hL : 0 ≤ L) (N : K →L[ℂ] H) :
    ∃ G₀ : K →L[ℂ] K, 0 ≤ G₀ ∧ G₀ ≤ 1 ∧
      IsGLB ((fun ε : ℝ => marker (L + ε • 1) N) '' Ioi 0) G₀ ∧
      Tendsto (fun ε : ℝ => marker (L + ε • 1) N)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds G₀) := by
  obtain ⟨G₀, _, hglb, hlim⟩ := exists_compact_monotone_right_limit
    (fun ε : ℝ => marker (L + ε • 1) N) (Metric.closedBall 0 1)
    (isCompact_closedBall _ _) (fun ε hε => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        regularized_marker_norm_le_one L hL N ε hε)
    (regularized_marker_monotone L hL N)
  have hbounds : ∀ᶠ ε in nhdsWithin 0 (Ioi (0 : ℝ)),
      0 ≤ marker (L + ε • 1) N ∧ marker (L + ε • 1) N ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have ha : IsStrictlyPositive (L + ε • (1 : H →L[ℂ] H)) :=
      IsStrictlyPositive.nonneg_add hL (isStrictlyPositive_one.smul hε)
    exact ⟨marker_nonnegative _ ha N, marker_le_one _ ha N⟩
  exact ⟨G₀, isClosed_Ici.mem_of_tendsto hlim (hbounds.mono fun _ h => h.1),
    isClosed_Iic.mem_of_tendsto hlim (hbounds.mono fun _ h => h.2), hglb, hlim⟩

end WeilDefect.MarkerStability

open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability Filter Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
namespace ConnesGreen
theorem canonical_selected_coefficient_finiteDimensional (S : Finset CriticalZeros) :
    FiniteDimensional ℂ ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) := by
  letI := Fintype.ofFinite {ρ : CriticalZeros // ρ ∈ S}
  let e : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →ₗ[ℂ]
      ({ρ : CriticalZeros // ρ ∈ S} → ℂ) :=
    { toFun := fun a => fun j => a j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact FiniteDimensional.of_injective e (by
    intro a b hab
    ext j
    exact congrFun hab j)

end ConnesGreen
theorem solution (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) :
    ∃ P : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
    ∃ M : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t,
      (∀ ρ, P (lp.single 2 ρ (1 : ℂ)) =
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
      (∀ ρ, M (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
      ∃ G₀ : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ),
        0 ≤ G₀ ∧ G₀ ≤ 1 ∧
        IsGLB ((fun ε : ℝ => marker (P ∘L P.adjoint + ε • 1) M) '' Ioi 0) G₀ ∧
        Tendsto (fun ε : ℝ => marker (P ∘L P.adjoint + ε • 1) M)
          (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds G₀) := by
  obtain ⟨P, M, hP, hM, _⟩ := actual_zero_negative_form_obstruction t ht S
  letI := canonical_selected_coefficient_finiteDimensional S
  refine ⟨P, M, hP, hM, ?_⟩
  apply finite_selected_marker_norm_limit_aux (P ∘L P.adjoint) _ M
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.isPositive_self_comp_adjoint P)
