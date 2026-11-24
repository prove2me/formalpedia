-- Prove2me | solution 1 for DimdPolyLEAN.stablePhaseRetrievalExplicitLpClosure_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:03:23.797744+00:00
-- url     : https://prove2.me/submissions/436209d5-7952-4667-b7a8-96932a102670

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
public import Theorems.Thm_DimdPolyLEAN_stablePhaseRetrievalExplicitLpClosure
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
private theorem explicitGaussianL2DistanceSq_nonneg
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ) :
    0 ≤ explicitGaussianL2DistanceSq P Q :=
  MeasureTheory.integral_nonneg fun _ => sq_nonneg _
private theorem sqrt_integral_norm_sq_eq_lpNorm
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (F : (Fin d -> ℂ) -> E)
    (hF : MeasureTheory.AEStronglyMeasurable F (explicitGamma d)) :
    Real.sqrt (∫ z, ‖F z‖ ^ 2 ∂ explicitGamma d) =
      MeasureTheory.lpNorm F 2 (explicitGamma d) := by
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  have hlp := MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow
    (μ := explicitGamma d) (p := (2 : NNReal)) (f := F) htwo hF
  change
    Real.sqrt (∫ z, ‖F z‖ ^ 2 ∂ explicitGamma d) =
      MeasureTheory.lpNorm F (↑(2 : NNReal)) (explicitGamma d)
  rw [hlp]
  change
    Real.sqrt (∫ z, ‖F z‖ ^ 2 ∂ explicitGamma d) =
      (∫ z, ‖F z‖ ^ (2 : ℝ) ∂ explicitGamma d) ^ ((2 : ℝ)⁻¹)
  rw [show (∫ z, ‖F z‖ ^ (2 : ℝ) ∂ explicitGamma d) =
      ∫ z, ‖F z‖ ^ 2 ∂ explicitGamma d by
    simp_all]
  rw [Real.sqrt_eq_rpow]
  norm_num
private theorem sqrt_explicitGaussianL2DistanceSq_eq_lpNorm
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ)
    (hPQ : MeasureTheory.AEStronglyMeasurable (fun z => P z - Q z)
      (explicitGamma d)) :
    Real.sqrt (explicitGaussianL2DistanceSq P Q) =
      MeasureTheory.lpNorm (fun z => P z - Q z) 2 (explicitGamma d) := by
  simpa [explicitGaussianL2DistanceSq] using
    sqrt_integral_norm_sq_eq_lpNorm (d := d) (fun z => P z - Q z) hPQ
private theorem memLp_of_explicitHermitePoly
    {d : ℕ} (hd : 0 < d) {κ : Fin d -> ℕ} {Q : (Fin d -> ℂ) -> ℂ}
    (hQ : Q ∈ Set.range (explicitEvalPkappa κ)) :
    MeasureTheory.MemLp Q 2 (explicitGamma d) := by
  rcases hQ with ⟨F, rfl⟩
  exact memLp_two_evalPkappa hd κ F
private theorem explicitGaussianL2DistanceSq_phase_eq_l2_norm_sq
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ)
    (hP : MeasureTheory.MemLp P 2 (explicitGamma d))
    (hQ : MeasureTheory.MemLp Q 2 (explicitGamma d))
    (θ : UnitPhase) :
    explicitGaussianL2DistanceSq P (fun z => θ.1 * Q z) =
      ‖hP.toLp P - θ.1 • hQ.toLp Q‖ ^ 2 := by
  have hθQ : MeasureTheory.MemLp (fun z => θ.1 * Q z) 2 (explicitGamma d) := by
    refine MeasureTheory.MemLp.ae_eq ?_ (hQ.const_smul θ.1)
    filter_upwards with z
    simp only [Pi.smul_apply, smul_eq_mul]
  have hdiff : MeasureTheory.MemLp (fun z => P z - θ.1 * Q z) 2 (explicitGamma d) :=
    hP.sub hθQ
  have hsqrt :=
    sqrt_explicitGaussianL2DistanceSq_eq_lpNorm P (fun z => θ.1 * Q z) hdiff.aestronglyMeasurable
  have hnorm :
      ‖(hP.sub hθQ).toLp (fun z => P z - θ.1 * Q z)‖ =
        MeasureTheory.lpNorm (fun z => P z - θ.1 * Q z) 2 (explicitGamma d) := by
    rw [MeasureTheory.Lp.norm_toLp]
    exact MeasureTheory.toReal_eLpNorm hdiff.aestronglyMeasurable
  have htoLp :
      (hP.sub hθQ).toLp (fun z => P z - θ.1 * Q z) =
        hP.toLp P - θ.1 • hQ.toLp Q := by
    change (hP.sub hθQ).toLp (P - fun z => θ.1 * Q z) =
      hP.toLp P - θ.1 • hQ.toLp Q
    rw [MeasureTheory.MemLp.toLp_sub]
    change hP.toLp P - hθQ.toLp (θ.1 • Q) =
      hP.toLp P - θ.1 • hQ.toLp Q
    rw [MeasureTheory.MemLp.toLp_const_smul]
  rw [← Real.sq_sqrt (explicitGaussianL2DistanceSq_nonneg P (fun z => θ.1 * Q z)),
    hsqrt, ← hnorm, htoLp]
private theorem explicitPhaseOptimizedDistanceSq_attained
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ)
    (hP : MeasureTheory.MemLp P 2 (explicitGamma d))
    (hQ : MeasureTheory.MemLp Q 2 (explicitGamma d)) :
    ∃ θ : ℂ, ‖θ‖ = 1 ∧
      explicitGaussianL2DistanceSq P (fun z => θ * Q z) =
        explicitPhaseOptimizedDistanceSq P Q := by
  let objective : UnitPhase -> ℝ :=
    fun θ => ‖hP.toLp P - θ.1 • hQ.toLp Q‖ ^ 2
  have hcontinuous : Continuous objective := by
    dsimp [objective]
    fun_prop
  rcases isCompact_univ.exists_isMinOn
      (Set.univ_nonempty : (Set.univ : Set UnitPhase).Nonempty)
      hcontinuous.continuousOn with
    ⟨θ₀, _hθ₀_mem, hθ₀_min⟩
  have hobjective :
      ∀ θ : UnitPhase,
        explicitGaussianL2DistanceSq P (fun z => θ.1 * Q z) = objective θ := by
    intro θ
    exact explicitGaussianL2DistanceSq_phase_eq_l2_norm_sq P Q hP hQ θ
  refine ⟨θ₀.1, θ₀.2, ?_⟩
  have hbdd :
      BddBelow (Set.range fun θ : UnitPhase =>
        explicitGaussianL2DistanceSq P (fun z => θ.1 * Q z)) := by
    refine ⟨0, ?_⟩
    rintro r ⟨θ, rfl⟩
    exact explicitGaussianL2DistanceSq_nonneg P (fun z => θ.1 * Q z)
  have hle :
      explicitPhaseOptimizedDistanceSq P Q ≤
        explicitGaussianL2DistanceSq P (fun z => θ₀.1 * Q z) :=
    csInf_le hbdd ⟨θ₀, rfl⟩
  have hge :
      explicitGaussianL2DistanceSq P (fun z => θ₀.1 * Q z) ≤
        explicitPhaseOptimizedDistanceSq P Q := by
    unfold explicitPhaseOptimizedDistanceSq
    refine le_csInf (Set.range_nonempty _) ?_
    rintro r ⟨θ, rfl⟩
    change explicitGaussianL2DistanceSq P (fun z => θ₀.1 * Q z) ≤
      explicitGaussianL2DistanceSq P (fun z => θ.1 * Q z)
    rw [hobjective θ, hobjective θ₀]
    exact hθ₀_min trivial
  exact le_antisymm hge hle
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ Set.range (explicitEvalPkappa κ)) :
    ∃ C_P : ℝ, 0 < C_P ∧
      ∀ Q : MeasureTheory.Lp ℂ 2 (explicitGamma d),
        Q ∈ closure (explicitHermiteLpPolys κ) →
          ∃ θ : ℂ, ‖θ‖ = 1 ∧
            explicitGaussianL2DistanceSq P (fun z => θ * Q z) ≤
              C_P ^ 2 * explicitModulusDistanceSq P (Q : (Fin d -> ℂ) -> ℂ) := by
  rcases stablePhaseRetrievalExplicitLpClosure hd κ P hP with ⟨C_P, hC_P_pos, hbound⟩
  have hP_mem : MeasureTheory.MemLp P 2 (explicitGamma d) :=
    memLp_of_explicitHermitePoly hd hP
  refine ⟨C_P, hC_P_pos, ?_⟩
  intro Q hQ
  have hQ_mem : MeasureTheory.MemLp (Q : (Fin d -> ℂ) -> ℂ) 2 (explicitGamma d) :=
    MeasureTheory.Lp.memLp Q
  rcases explicitPhaseOptimizedDistanceSq_attained P (Q : (Fin d -> ℂ) -> ℂ)
      hP_mem hQ_mem with
    ⟨θ, hθ, hθ_eq⟩
  refine ⟨θ, hθ, ?_⟩
  simp_all only []
end DimdPolyLEAN
