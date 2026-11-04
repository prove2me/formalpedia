-- Prove2me | solution 1 for CryptoMembership.PerfectInfo.lhs15_log_concave_bell
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:14:11.102208+00:00
-- url     : https://prove2.me/submissions/81684166-873f-4e0b-a0e5-94a45048ddd4

import Mathlib
import Definitions.Def_CryptoMembership_PerfectInfo_Model

open CryptoMembership.PerfectInfo MeasureTheory ProbabilityTheory Filter Topology

namespace BellAux

/-- Standard normal density. -/
noncomputable def phi (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

theorem phi_eq (x : ℝ) : phi x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp [phi, gaussianPDFReal_def]

theorem phi_pos (x : ℝ) : 0 < phi x := gaussianPDFReal_pos _ _ _ one_ne_zero

theorem phi_cont : Continuous phi := by
  have : phi = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := funext phi_eq
  rw [this]; fun_prop

theorem phi_int : Integrable phi := integrable_gaussianPDFReal 0 1

theorem Phi_eq_integral (x : ℝ) : Phi x = ∫ t in Set.Iic x, phi t := by
  rw [Phi, cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic
      (fun t _ => gaussianPDFReal_nonneg _ _ t))]
  rfl

theorem Phi_pos (x : ℝ) : 0 < Phi x := by
  rw [Phi_eq_integral, integral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun t => (phi_pos t).le)) phi_int.integrableOn]
  have hs : Function.support phi = Set.univ :=
    Set.eq_univ_of_forall (fun t => (phi_pos t).ne')
  rw [hs, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Iic]
  simp

theorem Phi_hasDerivAt (x : ℝ) : HasDerivAt Phi (phi x) x := by
  have hPhi : Phi = fun y => Phi 0 + ∫ t in (0:ℝ)..y, phi t := by
    funext y
    rw [← intervalIntegral.integral_Iic_sub_Iic phi_int.integrableOn phi_int.integrableOn,
      Phi_eq_integral, Phi_eq_integral]
    ring
  rw [hPhi]
  apply HasDerivAt.const_add
  exact intervalIntegral.integral_hasDerivAt_right (phi_int.intervalIntegrable)
    (phi_cont.stronglyMeasurableAtFilter _ _) phi_cont.continuousAt

/-- `I x = Φ(x)/φ(x) = ∫_{u ≥ 0} e^{xu - u²/2} du`. -/
noncomputable def Ifun (x : ℝ) : ℝ :=
  ∫ u, (Set.Ici (0:ℝ)).indicator (fun u => Real.exp (x * u - u ^ 2 / 2)) u

theorem indicator_shift (x u : ℝ) :
    (Set.Iic x).indicator phi (x - u) =
      phi x * (Set.Ici (0:ℝ)).indicator (fun u => Real.exp (x * u - u ^ 2 / 2)) u := by
  by_cases hu : 0 ≤ u
  · rw [Set.indicator_of_mem (by simp only [Set.mem_Iic]; linarith),
      Set.indicator_of_mem (by simpa using hu), phi_eq, phi_eq, mul_assoc, ← Real.exp_add]
    congr 2; ring
  · rw [Set.indicator_of_notMem (by simp only [Set.mem_Iic]; linarith),
      Set.indicator_of_notMem (by simpa using hu), mul_zero]

theorem ind_int (x : ℝ) :
    Integrable (fun u => (Set.Ici (0:ℝ)).indicator
      (fun u => Real.exp (x * u - u ^ 2 / 2)) u) := by
  have h1 : Integrable (fun u => (Set.Iic x).indicator phi (x - u)) :=
    (phi_int.indicator measurableSet_Iic).comp_sub_left x
  have h2 := h1.const_mul (phi x)⁻¹
  refine h2.congr (ae_of_all _ (fun u => ?_))
  simp only
  rw [indicator_shift, ← mul_assoc, inv_mul_cancel₀ (phi_pos x).ne', one_mul]

theorem Phi_eq_mul (x : ℝ) : Phi x = phi x * Ifun x := by
  rw [Phi_eq_integral, ← integral_indicator measurableSet_Iic,
    ← integral_sub_left_eq_self _ volume x, Ifun, ← integral_const_mul]
  congr 1
  funext u
  exact indicator_shift x u

theorem Ifun_pos (x : ℝ) : 0 < Ifun x := by
  have h := Phi_pos x
  rw [Phi_eq_mul] at h
  exact pos_of_mul_pos_right h (phi_pos x).le

theorem Ifun_strictMono : StrictMono Ifun := by
  intro x y hxy
  rw [Ifun, Ifun, ← sub_pos, ← integral_sub (ind_int y) (ind_int x),
    integral_pos_iff_support_of_nonneg_ae]
  · apply pos_iff_ne_zero.2
    intro h0
    have : volume (Set.Ioi (0:ℝ)) = 0 := by
      refine measure_mono_null (fun u (hu : 0 < u) => ?_) h0
      rw [Function.mem_support,
        Set.indicator_of_mem (by simpa using hu.le), Set.indicator_of_mem (by simpa using hu.le)]
      have : x * u - u ^ 2 / 2 < y * u - u ^ 2 / 2 := by nlinarith
      linarith [Real.exp_lt_exp.2 this]
    simp at this
  · refine ae_of_all _ (fun u => ?_)
    simp only [Pi.zero_apply, Pi.sub_apply, sub_nonneg]
    by_cases hu : 0 ≤ u
    · rw [Set.indicator_of_mem (by simpa using hu), Set.indicator_of_mem (by simpa using hu)]
      apply Real.exp_le_exp.2
      nlinarith
    · rw [Set.indicator_of_notMem (by simpa using hu), Set.indicator_of_notMem (by simpa using hu)]
  · exact (ind_int y).sub (ind_int x)

theorem logPhi_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => Real.log (Phi y)) (1 / Ifun x) x := by
  have := (Phi_hasDerivAt x).log (Phi_pos x).ne'
  convert this using 1
  rw [Phi_eq_mul]
  field_simp [(phi_pos x).ne']

theorem logPhi_strictConcave : StrictConcaveOn ℝ Set.univ (fun y => Real.log (Phi y)) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv convex_univ
  · exact (continuous_iff_continuousAt.2 fun x => (logPhi_hasDerivAt x).continuousAt).continuousOn
  · intro x _ y _ hxy
    rw [(logPhi_hasDerivAt x).deriv, (logPhi_hasDerivAt y).deriv]
    exact one_div_lt_one_div_of_lt (Ifun_pos x) (Ifun_strictMono hxy)

/-- Chernoff bound for the lower tail. -/
theorem Phi_le (l x : ℝ) (hl : 0 ≤ l) : Phi x ≤ Real.exp (l * x + l ^ 2 / 2) := by
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) x (t := -l)
    (by linarith) (integrable_exp_mul_gaussianReal (-l))
  rw [mgf_id_gaussianReal] at h
  rw [Phi, cdf_eq_real]
  have hs : Set.Iic x = {ω : ℝ | id ω ≤ x} := rfl
  rw [hs]
  refine h.trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  simp

end BellAux

open BellAux in
theorem solution (P : Params) (hP : P.Standing) :
    (∀ s : ℝ, 0 < lhs15 P s) ∧
    StrictConcaveOn ℝ Set.univ (fun s => Real.log (lhs15 P s)) ∧
    Tendsto (lhs15 P) atBot (𝓝 0) ∧
    Tendsto (lhs15 P) atTop (𝓝 0) := by
  obtain ⟨-, heta1, hte, hTe, -, -⟩ := hP
  set k := 1 - P.eta + Real.sqrt (P.tauEps / P.tauE) with hk
  set α := P.eta / Real.sqrt P.tauEps
  set β := Real.sqrt P.tauEps
  have hβ : 0 < β := Real.sqrt_pos.2 hte
  have hkpos : 0 < k := by
    have := Real.sqrt_nonneg (P.tauEps / P.tauE); linarith
  have hlhs : ∀ s, lhs15 P s = Real.exp (k * s) * Phi (α - β * s) := fun s => rfl
  have hpos : ∀ s, 0 < lhs15 P s := fun s => by
    rw [hlhs]; exact mul_pos (Real.exp_pos _) (Phi_pos _)
  refine ⟨hpos, ?_, ?_, ?_⟩
  · -- strict concavity
    have hlog : ∀ s, Real.log (lhs15 P s) = k * s + Real.log (Phi (α - β * s)) := by
      intro s
      rw [hlhs, Real.log_mul (Real.exp_pos _).ne' (Phi_pos _).ne', Real.log_exp]
    refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
    simp only [smul_eq_mul, hlog]
    have hne : α - β * x ≠ α - β * y := by
      intro h; apply hxy
      have : β * x = β * y := by linarith
      exact mul_left_cancel₀ hβ.ne' this
    have hc := logPhi_strictConcave.2 (Set.mem_univ (α - β * x)) (Set.mem_univ (α - β * y))
      hne ha hb hab
    simp only [smul_eq_mul] at hc
    have harg : a * (α - β * x) + b * (α - β * y) = α - β * (a * x + b * y) := by
      have : a * α + b * α = α := by rw [← add_mul, hab, one_mul]
      linear_combination this
    rw [harg] at hc
    nlinarith
  · -- s → -∞
    have hexp : Tendsto (fun s => Real.exp (k * s)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hkpos)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp
      (fun s => (hpos s).le) (fun s => ?_)
    rw [hlhs]
    have h1 : Phi (α - β * s) ≤ 1 := cdf_le_one _ _
    have h2 := Real.exp_pos (k * s)
    nlinarith
  · -- s → +∞ : Chernoff bound with l = 2k/β
    set l := 2 * k / β
    have hl : 0 ≤ l := by positivity
    have hexp : Tendsto (fun s => Real.exp (-k * s + (l * α + l ^ 2 / 2))) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      apply tendsto_atBot_add_const_right
      exact tendsto_id.const_mul_atTop_of_neg (by linarith)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hexp
      (fun s => (hpos s).le) (fun s => ?_)
    rw [hlhs]
    calc Real.exp (k * s) * Phi (α - β * s)
        ≤ Real.exp (k * s) * Real.exp (l * (α - β * s) + l ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (Phi_le l _ hl) (Real.exp_pos _).le
      _ = Real.exp (-k * s + (l * α + l ^ 2 / 2)) := by
          rw [← Real.exp_add]
          congr 1
          simp only [l]
          field_simp
          ring
