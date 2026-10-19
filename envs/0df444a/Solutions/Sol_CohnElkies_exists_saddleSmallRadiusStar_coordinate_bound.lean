-- Prove2me | solution 1 for CohnElkies.exists_saddleSmallRadiusStar_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/a74d54f0-7035-4632-81d7-962ed83a44fd

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_abs_exp_sub_one_le_abs_mul_exp_abs
import Theorems.Thm_CohnElkies_saddleSmallRadiusVariable_star_eq
import Theorems.Thm_CohnElkies_exists_saddleSourceShellDerivative_endpoint_bound
import Theorems.Thm_CohnElkies_saddle_log_sq_le_four_mul

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ d : ℕ,
        8 < Real.log ((d : ℝ) / 2) →
          saddleSmallRadiusVariable ε
            (saddleSmallRadiusStar ε d) ≤
              Real.log ((d : ℝ) / 2) / 8 + C := by
  obtain ⟨K, hK, hKbound⟩ :=
    exists_saddleSourceShellDerivative_endpoint_bound
      hε horder
  let C : ℝ := K / 4 * Real.exp (K / 2)
  have hC : 0 ≤ C := by
    try dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro d hloglarge
  let ℓ : ℝ := (d : ℝ) / 2
  let m : ℝ := Real.log ℓ / 8
  let q : ℝ := Real.log ℓ / (4 * ℓ)
  let z : ℝ := 2 * K * q
  have hℓnonnegative : 0 ≤ ℓ := by
    try dsimp [ℓ]
    positivity
  have hlogpositive : 0 < Real.log ℓ := by
    try dsimp [ℓ]
    linarith
  have hℓone : 1 < ℓ :=
    (Real.log_pos_iff hℓnonnegative).mp hlogpositive
  have hℓ : 0 < ℓ := by linarith
  have hdreal : 0 < (d : ℝ) := by
    try dsimp [ℓ] at hℓ
    linarith
  have hd : 0 < d := by
    exact_mod_cast hdreal
  have hm : 1 < m := by
    try dsimp [m, ℓ]
    linarith
  have hmpositive : 0 < m := by linarith
  have hqnonnegative : 0 ≤ q := by
    try dsimp [q]
    positivity
  have hlogupper : Real.log ℓ ≤ ℓ := by
    linarith [Real.log_le_sub_one_of_pos hℓ]
  have hqbound : q ≤ 1 / 4 := by
    try dsimp [q]
    apply (div_le_iff₀ (show 0 < 4 * ℓ by positivity)).mpr
    nlinarith
  have hstar :
      saddleSmallRadiusStarOrdinate ε d = -1 + q := by
    rfl
  have huinterval :
      saddleSmallRadiusStarOrdinate ε d ∈
        Icc (-1 : ℝ) 0 := by
    rw [hstar]
    constructor <;> linarith
  have hshell :
      saddleShellDerivativeOne ε +
          saddleSourceShellDerivative ε
            (saddleSmallRadiusStarOrdinate ε d) ≤
        K * q := by
    calc
      saddleShellDerivativeOne ε +
          saddleSourceShellDerivative ε
            (saddleSmallRadiusStarOrdinate ε d) ≤
        |saddleShellDerivativeOne ε +
          saddleSourceShellDerivative ε
            (saddleSmallRadiusStarOrdinate ε d)| :=
          le_abs_self _
      _ ≤ K *
          (saddleSmallRadiusStarOrdinate ε d + 1) :=
        hKbound _ huinterval
      _ = K * q := by
        rw [hstar]
        ring
  have hznonnegative : 0 ≤ z := by
    try dsimp [z]
    positivity
  have hzupper : z ≤ K / 2 := by
    try dsimp [z]
    calc
      2 * K * q ≤ 2 * K * (1 / 4 : ℝ) := by
        gcongr
      _ = K / 2 := by ring
  have hlogquad := saddle_log_sq_le_four_mul hℓone.le
  have hmz : m * z ≤ K / 4 := by
    have hid :
        m * z =
          K * (Real.log ℓ) ^ 2 / (16 * ℓ) := by
      try dsimp [m, z, q]
      field_simp
      ring
    rw [hid]
    apply (div_le_iff₀
      (show 0 < 16 * ℓ by positivity)).mpr
    nlinarith [mul_nonneg hK
      (sub_nonneg.mpr hlogquad)]
  have hexpdifference :
      Real.exp z - 1 ≤ z * Real.exp z := by
    have hsource :=
      abs_exp_sub_one_le_abs_mul_exp_abs z
    rw [abs_of_nonneg
      (sub_nonneg.mpr (by
        simpa using! Real.exp_le_exp.mpr hznonnegative)),
      abs_of_nonneg hznonnegative] at hsource
    exact hsource
  have hproduct :
      m * Real.exp z ≤
        m + K / 4 * Real.exp (K / 2) := by
    have hdifference :=
      mul_le_mul_of_nonneg_left hexpdifference
        hmpositive.le
    have hexpbound :=
      Real.exp_le_exp.mpr hzupper
    have hscaled :
        m * z * Real.exp z ≤
          (K / 4) * Real.exp (K / 2) := by
      exact mul_le_mul hmz hexpbound
        (Real.exp_pos z).le (by positivity)
    nlinarith
  calc
    saddleSmallRadiusVariable ε
        (saddleSmallRadiusStar ε d) =
      Real.exp
        (saddleDigamma m +
          2 * (saddleShellDerivativeOne ε +
            saddleSourceShellDerivative ε
              (saddleSmallRadiusStarOrdinate ε d))) := by
        simpa [m, ℓ] using!
          saddleSmallRadiusVariable_star_eq
            (ε := ε) hd
    _ ≤ Real.exp (Real.log m + z) := by
      apply Real.exp_le_exp.mpr
      have hdigamma := (saddleDigamma_bounds hm).2
      try dsimp [z]
      linarith
    _ = m * Real.exp z := by
      rw [Real.exp_add, Real.exp_log hmpositive]
    _ ≤ m + K / 4 * Real.exp (K / 2) := hproduct
    _ = Real.log ((d : ℝ) / 2) / 8 + C := by
      rfl
end CohnElkies
