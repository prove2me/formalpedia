-- Prove2me | solution 1 for DimdPolyLEAN.stablePhaseRetrievalCoefficients
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:57:25.522407+00:00
-- url     : https://prove2.me/submissions/4d4d0c28-b8a8-4661-97fd-4d9a61f87d9f

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
public import Theorems.Thm_DimdPolyLEAN_evalPkappa_smul
public import Theorems.Thm_DimdPolyLEAN_evalPkappa_sub
public import Theorems.Thm_DimdPolyLEAN_phaseStability
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
private theorem explicitPkappaNorm_sq_eq_integral
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (F : Finsupp (Fin d -> ℕ) ℂ) :
    explicitPkappaNorm F ^ 2 =
      ∫ z, ‖explicitEvalPkappa κ F z‖ ^ 2 ∂ explicitGamma d :=
  (evalPkappa_total_mass hd κ F).symm
private theorem explicitPkappaNorm_smul
    {d : ℕ} (c : ℂ) (F : Finsupp (Fin d -> ℕ) ℂ) :
    explicitPkappaNorm (c • F) = ‖c‖ * explicitPkappaNorm F := by
  classical
  by_cases hc : c = 0
  · subst c
    simp [explicitPkappaNorm]
  · change
      Real.sqrt (Finset.sum (c • F).support (fun α => ‖(c • F) α‖ ^ 2)) =
        ‖c‖ * Real.sqrt (Finset.sum F.support (fun α => ‖F α‖ ^ 2))
    rw [Finsupp.support_smul_eq hc]
    have hsum :
        Finset.sum F.support (fun α => ‖(c • F) α‖ ^ 2) =
          ‖c‖ ^ 2 * Finset.sum F.support (fun α => ‖F α‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro α halpha
      simp [Finsupp.smul_apply, mul_pow]
    simp_all
private theorem explicitPkappaNorm_pos_of_ne_zero
    {d : ℕ} {F : Finsupp (Fin d -> ℕ) ℂ} (hF : F ≠ 0) :
    0 < explicitPkappaNorm F := by
  classical
  rw [explicitPkappaNorm]
  apply Real.sqrt_pos.mpr
  have hexists : ∃ α, F α ≠ 0 := by
    by_contra hnone
    exact hF (by ext α; exact not_not.mp (not_exists.mp hnone α))
  rcases hexists with ⟨α, halpha⟩
  have halpha_mem : α ∈ F.support := F.mem_support_iff.mpr halpha
  have hterm_pos : 0 < ‖F α‖ ^ 2 := sq_pos_of_ne_zero (by simpa using halpha)
  exact hterm_pos.trans_le
    (Finset.single_le_sum (fun β _ => sq_nonneg ‖F β‖) halpha_mem)
private theorem explicitPkappaNorm_normalized
    {d : ℕ} {F : Finsupp (Fin d -> ℕ) ℂ} (hF : F ≠ 0) :
    explicitPkappaNorm (((explicitPkappaNorm F : ℂ)⁻¹) • F) = 1 := by
  have hpos : 0 < explicitPkappaNorm F := explicitPkappaNorm_pos_of_ne_zero hF
  rw [explicitPkappaNorm_smul]
  have hnorm_inv : ‖((explicitPkappaNorm F : ℂ)⁻¹)‖ = (explicitPkappaNorm F)⁻¹ := by
    rw [norm_inv]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
  rw [hnorm_inv]
  field_simp [ne_of_gt hpos]
private theorem explicitModulusDefect_smul_of_nonneg
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ) (a : ℝ) (ha : 0 ≤ a)
    (F Q : Finsupp (Fin d -> ℕ) ℂ) :
    modulusDefect κ ((a : ℂ) • F) ((a : ℂ) • Q) =
      a * modulusDefect κ F Q := by
  unfold modulusDefect
  have hintegral :
      (∫ z,
          (‖evalPkappa κ ((a : ℂ) • Q) z‖ -
                ‖evalPkappa κ ((a : ℂ) • F) z‖) ^ 2
            ∂ gammaD d) =
        a ^ 2 *
          ∫ z,
            (‖evalPkappa κ Q z‖ - ‖evalPkappa κ F z‖) ^ 2
              ∂ gammaD d := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    rw [congrFun (evalPkappa_smul hd κ (a : ℂ) Q) z,
      congrFun (evalPkappa_smul hd κ (a : ℂ) F) z, norm_mul, norm_mul,
      Complex.norm_of_nonneg ha]
    ring
  rw [hintegral, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
private theorem modulusDefect_sq_eq_integral_rev
    {d : ℕ} (κ : Fin d -> ℕ)
    (F Q : Finsupp (Fin d -> ℕ) ℂ) :
    modulusDefect κ F Q ^ 2 =
      ∫ z,
        (‖explicitEvalPkappa κ F z‖ - ‖explicitEvalPkappa κ Q z‖) ^ 2
          ∂ explicitGamma d := by
  unfold modulusDefect
  rw [Real.sq_sqrt]
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    have hF :
        explicitEvalPkappa κ F z = evalPkappa κ F z := by
      simp [explicitEvalPkappa, explicitPhi, explicitPhi1D, explicitComplexHermite,
        evalPkappa, Phi, phi1D, complexHermite]
    have hQ :
        explicitEvalPkappa κ Q z = evalPkappa κ Q z := by
      simp [explicitEvalPkappa, explicitPhi, explicitPhi1D, explicitComplexHermite,
        evalPkappa, Phi, phi1D, complexHermite]
    rw [hF, hQ]
    ring
  · exact MeasureTheory.integral_nonneg fun z => sq_nonneg _
private theorem phase_stability_coefficients_of_ne_zero
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (F : Finsupp (Fin d -> ℕ) ℂ) (hF : F ≠ 0) :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ Q : Finsupp (Fin d -> ℕ) ℂ,
        ∃ phase : ℂ, ‖phase‖ = 1 ∧
          explicitPkappaNorm (phase • Q - F) ≤ C_F * modulusDefect κ F Q := by
  let a : ℝ := (explicitPkappaNorm F)⁻¹
  have hnorm_pos : 0 < explicitPkappaNorm F := explicitPkappaNorm_pos_of_ne_zero hF
  have ha_pos : 0 < a := inv_pos.mpr hnorm_pos
  let Fn : Finsupp (Fin d -> ℕ) ℂ := (a : ℂ) • F
  have hFn_norm : explicitPkappaNorm Fn = 1 := by
    change explicitPkappaNorm ((a : ℂ) • F) = 1
    rw [show (a : ℂ) = ((explicitPkappaNorm F : ℂ)⁻¹) by simp [a]]
    exact explicitPkappaNorm_normalized hF
  let Fpk : Pkappa d κ := Fn
  have hFn_norm' : ‖Fpk‖ = 1 := by
    change explicitPkappaNorm Fn = 1
    exact hFn_norm
  rcases phaseStability hd κ Fpk hFn_norm' with ⟨C_F, hC_F_pos, hstable⟩
  refine ⟨C_F, hC_F_pos, ?_⟩
  intro Q
  let Qn : Finsupp (Fin d -> ℕ) ℂ := (a : ℂ) • Q
  let Qnpk : Pkappa d κ := Qn
  rcases hstable Qnpk with ⟨phase, hphase, hbound⟩
  refine ⟨phase, hphase, ?_⟩
  have hbound' :
      explicitPkappaNorm (phase • Qn - Fn) ≤ C_F * modulusDefect κ Fn Qn :=
    hbound
  have hcoeff :
      phase • Qn - Fn = (a : ℂ) • (phase • Q - F) := by
    ext α
    simp only [Qn, Fn, Finsupp.sub_apply, Finsupp.smul_apply]
    change phase * ((a : ℂ) * Q α) - (a : ℂ) * F α =
      (a : ℂ) * (phase * Q α - F α)
    ring
  have hleft_scale :
      explicitPkappaNorm (phase • Qn - Fn) =
        a * explicitPkappaNorm (phase • Q - F) := by
    rw [hcoeff, explicitPkappaNorm_smul, Complex.norm_of_nonneg (le_of_lt ha_pos)]
  have hdef_scale :
      modulusDefect κ Fn Qn = a * modulusDefect κ F Q := by
    exact explicitModulusDefect_smul_of_nonneg hd κ a (le_of_lt ha_pos) F Q
  have hscaled :
      a * explicitPkappaNorm (phase • Q - F) ≤
        C_F * (a * modulusDefect κ F Q) := by simpa [hleft_scale, hdef_scale] using hbound'
  have hscaled' :
      a * explicitPkappaNorm (phase • Q - F) ≤
        a * (C_F * modulusDefect κ F Q) := by
    rw [show a * (C_F * modulusDefect κ F Q) = C_F * (a * modulusDefect κ F Q) by ring]
    exact hscaled
  exact (mul_le_mul_iff_of_pos_left ha_pos).mp hscaled'
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
    (F : Finsupp (Fin d -> ℕ) ℂ) (hF : F ≠ 0) :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ Q : Finsupp (Fin d -> ℕ) ℂ,
        ∃ θ : ℂ, ‖θ‖ = 1 ∧
          ∫ z, ‖explicitEvalPkappa κ F z - θ * explicitEvalPkappa κ Q z‖ ^ 2
              ∂ explicitGamma d
            ≤ C_F ^ 2 *
              ∫ z, (‖explicitEvalPkappa κ F z‖ - ‖explicitEvalPkappa κ Q z‖) ^ 2
                ∂ explicitGamma d := by
  rcases phase_stability_coefficients_of_ne_zero hd κ F hF with ⟨C_F, hC_F_pos, hstable⟩
  refine ⟨C_F, hC_F_pos, ?_⟩
  intro Q
  rcases hstable Q with ⟨θ, htheta, hbound⟩
  refine ⟨θ, htheta, ?_⟩
  have hbound_sq :
      explicitPkappaNorm (θ • Q - F) ^ 2 ≤ C_F ^ 2 * modulusDefect κ F Q ^ 2 := by
    have hdist_nonneg : 0 ≤ explicitPkappaNorm (θ • Q - F) := Real.sqrt_nonneg _
    have hdef_nonneg : 0 ≤ modulusDefect κ F Q := Real.sqrt_nonneg _
    nlinarith only [hbound, hC_F_pos, hdist_nonneg, hdef_nonneg]
  have hleft :
      ∫ z, ‖explicitEvalPkappa κ F z - θ * explicitEvalPkappa κ Q z‖ ^ 2
          ∂ explicitGamma d =
        explicitPkappaNorm (θ • Q - F) ^ 2 := by
    calc
      ∫ z, ‖explicitEvalPkappa κ F z - θ * explicitEvalPkappa κ Q z‖ ^ 2
          ∂ explicitGamma d
          = ∫ z, ‖explicitEvalPkappa κ (θ • Q - F) z‖ ^ 2 ∂ explicitGamma d := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with z
            have hsub := congrFun (evalPkappa_sub hd κ (θ • Q) F) z
            have hsmul := congrFun (evalPkappa_smul hd κ θ Q) z
            rw [hsmul] at hsub
            have heval :
                explicitEvalPkappa κ (θ • Q - F) z =
                  θ * explicitEvalPkappa κ Q z - explicitEvalPkappa κ F z := by
              exact
                                                              hsub
            rw [heval, norm_sub_rev]
      _ = explicitPkappaNorm (θ • Q - F) ^ 2 := by
            rw [← explicitPkappaNorm_sq_eq_integral hd κ (θ • Q - F)]
  rw [hleft, ← modulusDefect_sq_eq_integral_rev κ F Q]
  exact hbound_sq
end DimdPolyLEAN
