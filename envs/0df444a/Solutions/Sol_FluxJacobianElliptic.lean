-- Prove2me | solution 1 for FluxJacobianElliptic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:15:42.968182+00:00
-- url     : https://prove2.me/submissions/baff4889-ed77-4a8d-aa69-991e1b28c05f

import Definitions.Def_PHigherOrder_FluxJacobian
import Definitions.Def_PHigherOrder_FluxJacobianIsDeriv
import Definitions.Def_PHigherOrder_FluxJacobianAnnulusEllipticity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_PHigherOrder_FluxJacobianElliptic
import Theorems.Thm_FluxJacobianAnnulusEllipticity
import Theorems.Thm_FluxJacobianIsDeriv


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) :
    (∀ ξ : Plane, ξ ≠ 0 → HasFDerivAt (PFlux p) (FluxJacobian p ξ) ξ)
      ∧ ContDiffOn ℝ (⊤ : ℕ∞) (FluxJacobian p) {ζ : Plane | ζ ≠ 0}
      ∧ 0 < (p - 1) * b ^ (p - 2) ∧ (p - 1) * b ^ (p - 2) ≤ a ^ (p - 2)
      ∧ (∀ ξ : Plane, a ≤ ‖ξ‖ → ‖ξ‖ ≤ b → ∀ w : Plane,
          (p - 1) * b ^ (p - 2) * ‖w‖ ^ 2 ≤ inner ℝ (FluxJacobian p ξ w) w
            ∧ ‖FluxJacobian p ξ w‖ ≤ a ^ (p - 2) * ‖w‖)
      ∧ (∀ j : ℕ, ∃ M : ℝ, 0 < M ∧ ∀ ξ : Plane, a ≤ ‖ξ‖ → ‖ξ‖ ≤ b →
          ‖iteratedFDeriv ℝ j (FluxJacobian p) ξ‖ ≤ M)
      ∧ ContDiffOn ℝ (⊤ : ℕ∞) (PFlux p) {ζ : Plane | ζ ≠ 0} := by
  -- Preliminaries.  `0 < p - 1 < 1` and `p - 2 < 0`:  the exponent is NEGATIVE, so
  -- `t ↦ t ^ (p - 2)` is DECREASING and the scalar factor is smallest at the OUTER radius.
  have hp1 : 0 < p - 1 := by linarith
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hmono : ∀ s t : ℝ, 0 < s → s ≤ t → t ^ (p - 2) ≤ s ^ (p - 2) := fun s t hs hst =>
    Real.rpow_le_rpow_of_nonpos hs hst (by linarith)
  have hopen : IsOpen {ζ : Plane | ζ ≠ 0} := isOpen_ne
  -- Clause 1:  the flux Jacobian is the derivative of the flux away from the origin.
  have hclaim1 := FluxJacobianIsDeriv p
  -- Clause 3:  the constants.
  have hbpow : 0 < b ^ (p - 2) := Real.rpow_pos_of_pos hb _
  have hapow : 0 < a ^ (p - 2) := Real.rpow_pos_of_pos ha _
  have hlam : 0 < (p - 1) * b ^ (p - 2) := mul_pos hp1 hbpow
  have hlamLam : (p - 1) * b ^ (p - 2) ≤ a ^ (p - 2) := by
    have h1 : b ^ (p - 2) ≤ a ^ (p - 2) := hmono a b ha hab
    nlinarith
  -- Clauses 2 and 6:  smoothness off the origin.
  have hphi : ContDiffOn ℝ (⊤ : ℕ∞) (fun ζ : Plane => ‖ζ‖ ^ (p - 2)) {ζ : Plane | ζ ≠ 0} := by
    intro ζ hζ
    exact ((Real.contDiffAt_rpow_const_of_ne
      (ne_of_gt (norm_pos_iff.mpr hζ))).comp ζ (contDiffAt_norm ℝ hζ)).contDiffWithinAt
  have hden : ContDiffOn ℝ (⊤ : ℕ∞) (fun ζ : Plane => (p - 2) / ‖ζ‖ ^ 2) {ζ : Plane | ζ ≠ 0} :=
    contDiffOn_const.div (contDiff_norm_sq ℝ).contDiffOn
      (fun ζ hζ => pow_ne_zero 2 (norm_ne_zero_iff.mpr hζ))
  have hbil : ContDiff ℝ (⊤ : ℕ∞) (fun ζ : Plane => (innerSL ℝ ζ).smulRight ζ) :=
    (((ContinuousLinearMap.smulRightL ℝ Plane Plane).comp (innerSL ℝ)).contDiff).clm_apply
      contDiff_id
  have hclaim2 : ContDiffOn ℝ (⊤ : ℕ∞) (FluxJacobian p) {ζ : Plane | ζ ≠ 0} := by
    have h : ContDiffOn ℝ (⊤ : ℕ∞) (fun ζ : Plane => ‖ζ‖ ^ (p - 2) •
        (ContinuousLinearMap.id ℝ Plane + ((p - 2) / ‖ζ‖ ^ 2) •
          (innerSL ℝ ζ).smulRight ζ)) {ζ : Plane | ζ ≠ 0} :=
      hphi.smul (contDiffOn_const.add (hden.smul hbil.contDiffOn))
    exact h.congr fun ζ _ => rfl
  have hclaim6 : ContDiffOn ℝ (⊤ : ℕ∞) (PFlux p) {ζ : Plane | ζ ≠ 0} := by
    have h : ContDiffOn ℝ (⊤ : ℕ∞) (fun ζ : Plane => ‖ζ‖ ^ (p - 2) • ζ) {ζ : Plane | ζ ≠ 0} :=
      hphi.smul contDiff_id.contDiffOn
    exact h.congr fun ζ _ => rfl
  -- Clause 4:  uniform ellipticity on the annulus.
  have hclaim4 := FluxJacobianAnnulusEllipticity p hp hp2 a b ha hab
  -- Clause 5:  bounded derivatives of every order, by compactness of the annulus.
  have hKcomp : IsCompact {ξ : Plane | a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b} := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hset : {ξ : Plane | a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b}
          = (fun ξ : Plane => ‖ξ‖) ⁻¹' (Set.Ici a) ∩ (fun ξ : Plane => ‖ξ‖) ⁻¹' (Set.Iic b) := by
        ext ξ
        simp [Set.mem_inter_iff]
      rw [hset]
      exact (isClosed_Ici.preimage continuous_norm).inter (isClosed_Iic.preimage continuous_norm)
    · refine (Metric.isBounded_closedBall (x := (0 : Plane)) (r := b)).subset ?_
      intro ξ hξ
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hξ.2
  have hKsub : {ξ : Plane | a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b} ⊆ {ζ : Plane | ζ ≠ 0} := fun ξ hξ =>
    norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le ha hξ.1))
  have hclaim5 : ∀ j : ℕ, ∃ M : ℝ, 0 < M ∧ ∀ ξ : Plane, a ≤ ‖ξ‖ → ‖ξ‖ ≤ b →
      ‖iteratedFDeriv ℝ j (FluxJacobian p) ξ‖ ≤ M := by
    intro j
    have h1 : ContinuousOn (iteratedFDerivWithin ℝ j (FluxJacobian p) {ζ : Plane | ζ ≠ 0})
        {ζ : Plane | ζ ≠ 0} :=
      hclaim2.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hopen.uniqueDiffOn
    have h2 : ContinuousOn (iteratedFDeriv ℝ j (FluxJacobian p)) {ζ : Plane | ζ ≠ 0} :=
      h1.congr fun ζ hζ => (iteratedFDerivWithin_of_isOpen j hopen hζ).symm
    have hcont : ContinuousOn (fun ξ : Plane => ‖iteratedFDeriv ℝ j (FluxJacobian p) ξ‖)
        {ξ : Plane | a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b} := (h2.mono hKsub).norm
    rcases Set.eq_empty_or_nonempty {ξ : Plane | a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b} with hemp | hne
    · refine ⟨1, one_pos, fun ξ h1' h2' => ?_⟩
      exact absurd (show ξ ∈ {ξ : Plane | a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b} from ⟨h1', h2'⟩)
        (by rw [hemp]; exact Set.notMem_empty ξ)
    · obtain ⟨ξ₀, hξ₀, hmax⟩ := hKcomp.exists_isMaxOn hne hcont
      refine ⟨‖iteratedFDeriv ℝ j (FluxJacobian p) ξ₀‖ + 1, by positivity, ?_⟩
      intro ξ h1' h2'
      have hle : ‖iteratedFDeriv ℝ j (FluxJacobian p) ξ‖
          ≤ ‖iteratedFDeriv ℝ j (FluxJacobian p) ξ₀‖ :=
        hmax (show ξ ∈ {ξ : Plane | a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b} from ⟨h1', h2'⟩)
      linarith
  exact ⟨hclaim1, hclaim2, hlam, hlamLam, hclaim4, hclaim5, hclaim6⟩
