-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_filling_locally_convex_at_each_point
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T23:51:56.019073+00:00
-- url     : https://prove2.me/submissions/0e9512c6-f3a9-4bf7-9a12-f44fda8605af

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue


open BirkhoffGlobalSection

theorem radial_ray_representation (s : Phase) (hs : s ≠ 0) :
    ∃ x ∈ unitThreeSphere, ∃ R : ℝ, 0 < R ∧ (fun i : Fin 4 => R * x i) = s := by
  let Q := zNormSq s + wNormSq s
  have hQ : 0 < Q := by
    by_contra h
    have hle : Q ≤ 0 := le_of_not_gt h
    dsimp [Q, zNormSq, wNormSq] at hle
    have hz0 : s 0 = 0 := by
      nlinarith [sq_nonneg (s 0), sq_nonneg (s 1), sq_nonneg (s 2), sq_nonneg (s 3)]
    have hz1 : s 1 = 0 := by
      nlinarith [sq_nonneg (s 0), sq_nonneg (s 1), sq_nonneg (s 2), sq_nonneg (s 3)]
    have hz2 : s 2 = 0 := by
      nlinarith [sq_nonneg (s 0), sq_nonneg (s 1), sq_nonneg (s 2), sq_nonneg (s 3)]
    have hz3 : s 3 = 0 := by
      nlinarith [sq_nonneg (s 0), sq_nonneg (s 1), sq_nonneg (s 2), sq_nonneg (s 3)]
    have hz : s = 0 := by
      ext i
      change s i = 0
      fin_cases i
      · exact hz0
      · exact hz1
      · exact hz2
      · exact hz3
    exact hs hz
  let R := Real.sqrt Q
  have hR : 0 < R := Real.sqrt_pos.mpr hQ
  have hRsq : R ^ 2 = Q := Real.sq_sqrt hQ.le
  let x : Phase := R⁻¹ • s
  have hscale (a : ℝ) : zNormSq (a • s) + wNormSq (a • s) = a ^ 2 * Q := by
    simp only [zNormSq, wNormSq, Pi.smul_apply, smul_eq_mul, Q]
    ring
  refine ⟨x, ?_, R, hR, ?_⟩
  · change zNormSq (R⁻¹ • s) + wNormSq (R⁻¹ • s) = 1
    rw [hscale, ← hRsq, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hR.ne')]
  · change R • (R⁻¹ • s) = s
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]

theorem radial_origin_negative (F : Phase → ℝ) (S : Set Phase)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0) :
    F 0 < 0 := by
  let e : Phase := fun i => if i = 0 then 1 else 0
  have he : e ∈ unitThreeSphere := by
    have h10 : (1 : Fin 4) ≠ 0 := by decide
    have h20 : (2 : Fin 4) ≠ 0 := by decide
    have h30 : (3 : Fin 4) ≠ 0 := by decide
    norm_num [e, unitThreeSphere, zNormSq, wNormSq, h10, h20, h30]
  obtain ⟨R, hR, hRS⟩ := hray e he
  have hezero : (fun _ : Fin 4 => (0 : ℝ)) = (0 : Phase) := rfl
  simpa only [zero_mul, hezero] using hneg e he R hR hRS 0 le_rfl hR

theorem radial_scaling_negative (F : Phase → ℝ) (S : Set Phase)
    (hF0 : ∀ s ∈ S, F s = 0)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0) :
    ∀ s ∈ S, ∀ t : ℝ, 0 ≤ t → t < 1 → F (t • s) < 0 := by
  intro s hs t ht0 ht1
  have hzero : F 0 < 0 := radial_origin_negative F S hray hneg
  have hsne : s ≠ 0 := by
    intro he
    have hf := hF0 s hs
    rw [he] at hf
    linarith
  obtain ⟨x, hx, R, hR, hRs⟩ := radial_ray_representation s hsne
  have hRS : (fun i : Fin 4 => R * x i) ∈ S := hRs.symm ▸ hs
  have hlt : t * R < R := by nlinarith
  have hf := hneg x hx R hR hRS (t * R) (mul_nonneg ht0 hR.le) hlt
  have heq : (fun i : Fin 4 => (t * R) * x i) = t • s := by
    rw [← hRs]
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq] at hf
  exact hf

theorem radial_filling_sign_and_zero_set (F : Phase → ℝ) (S : Set Phase)
    (hF0 : ∀ s ∈ S, F s = 0)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0) :
    let K : Set Phase := {y | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s}
    (∀ y ∈ K, F y ≤ 0) ∧ K ∩ {y | F y = 0} = S := by
  dsimp only
  constructor
  · rintro y ⟨s, hs, t, ht0, ht1, rfl⟩
    rcases ht1.eq_or_lt with ht | ht
    · simp [ht, hF0 s hs]
    · exact (radial_scaling_negative F S hF0 hray hneg s hs t ht0 ht).le
  · ext y
    constructor
    · rintro ⟨⟨s, hs, t, ht0, ht1, heq⟩, hf⟩
      have ht : t = 1 := by
        by_contra hne
        have hlt := radial_scaling_negative F S hF0 hray hneg s hs t ht0
          (lt_of_le_of_ne ht1 hne)
        rw [← heq, hf] at hlt
        exact (lt_irrefl 0) hlt
      rw [ht, one_smul] at heq
      rw [heq]
      exact hs
    · intro hy
      exact ⟨⟨y, hy, 1, zero_le_one, le_rfl, (one_smul ℝ y).symm⟩, hF0 y hy⟩

private theorem radial_filling_contains_origin_ball (S : Set Phase)
    (hS : IsCompact S) (hne : S.Nonempty) (hsne : ∀ s ∈ S, s ≠ 0)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S) :
    ∃ ε > 0, Metric.ball (0 : Phase) ε ⊆
      {y | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s} := by
  obtain ⟨s₀, hs₀, hmin⟩ := hS.exists_isMinOn hne continuous_norm.continuousOn
  have hε : 0 < ‖s₀‖ := norm_pos_iff.mpr (hsne s₀ hs₀)
  refine ⟨‖s₀‖, hε, ?_⟩
  intro y hy
  have hynorm : ‖y‖ < ‖s₀‖ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hy
  by_cases hy0 : y = 0
  · exact ⟨s₀, hs₀, 0, le_rfl, zero_le_one, by simp [hy0]⟩
  obtain ⟨x, hx, R, hR, hRy⟩ := radial_ray_representation y hy0
  obtain ⟨r, hr, hrs⟩ := hray x hx
  let s : Phase := fun i => r * x i
  let t : ℝ := R / r
  have ht : 0 < t := div_pos hR hr
  have heq : y = t • s := by
    rw [← hRy]
    ext i
    change R * x i = (R / r) * (r * x i)
    field_simp
  have hnorm : ‖y‖ = t * ‖s‖ := by
    rw [heq, norm_smul, Real.norm_of_nonneg ht.le]
  have hbound : ‖s₀‖ ≤ ‖s‖ := hmin hrs
  have ht1 : t ≤ 1 := by nlinarith
  exact ⟨s, hrs, t, ht.le, ht1, heq⟩

private theorem radial_filling_locally_convex_at_origin (S : Set Phase)
    (hS : IsCompact S) (hne : S.Nonempty) (hsne : ∀ s ∈ S, s ≠ 0)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S) :
    let K : Set Phase := {y | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s}
    ∃ U : Set Phase, U ∈ nhds (0 : Phase) ∧ Convex ℝ (K ∩ U) := by
  obtain ⟨ε, hε, hsub⟩ := radial_filling_contains_origin_ball S hS hne hsne hray
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, ?_⟩
  rw [Set.inter_eq_right.mpr hsub]
  exact convex_ball _ _

theorem radial_filling_origin_case (F : Phase → ℝ) (S : Set Phase)
    (hS : IsCompact S) (hF0 : ∀ s ∈ S, F s = 0)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0) :
    let K : Set Phase := {y | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s}
    ∃ U : Set Phase, U ∈ nhds (0 : Phase) ∧ Convex ℝ (K ∩ U) := by
  have hfzero := radial_origin_negative F S hray hneg
  have hsne : ∀ s ∈ S, s ≠ 0 := by
    intro s hs he
    have hf := hF0 s hs
    rw [he] at hf
    linarith
  let e : Phase := fun i => if i = 0 then 1 else 0
  have he : e ∈ unitThreeSphere := by
    have h10 : (1 : Fin 4) ≠ 0 := by decide
    have h20 : (2 : Fin 4) ≠ 0 := by decide
    have h30 : (3 : Fin 4) ≠ 0 := by decide
    norm_num [e, unitThreeSphere, zNormSq, wNormSq, h10, h20, h30]
  obtain ⟨r, _, hrs⟩ := hray e he
  exact radial_filling_locally_convex_at_origin S hS ⟨_, hrs⟩ hsne hray




open BirkhoffGlobalSection
open scoped Topology

/-- An inward-negative radial slice cannot have both a stationary boundary point
and a positive second derivative there. -/
theorem inward_negative_second_derivative_boundary_not_stationary (f : ℝ → ℝ)
    (hc : ContinuousAt f 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 0 ≤ t → t < 1 → f t < 0)
    (hsecond : 0 < deriv (deriv f) 1) : deriv f 1 ≠ 0 := by
  intro hstationary
  have hmin := isLocalMin_of_deriv_deriv_pos hsecond hstationary hc
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hmin
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hd : dist (1 - δ) (1 : ℝ) < ε := by
    rw [Real.dist_eq]
    have heq : (1 - δ) - 1 = -δ := by ring
    rw [heq, abs_neg, abs_of_pos hδ]
    exact hδε
  have hl := hnear hd
  have hn := hneg (1 - δ) (by linarith) (by linarith)
  rw [hzero] at hl
  linarith

theorem radial_slice_first_and_second_derivative (F : Phase → ℝ) (s : Phase)
    (hc : ContDiffAt ℝ 2 F s) :
    let f : ℝ → ℝ := fun t => F (t • s)
    deriv f 1 = fderiv ℝ F s s ∧
      deriv (deriv f) 1 = fderiv ℝ (fun x => fderiv ℝ F x s) s s := by
  let P : ℝ → Phase := fun t => t • s
  let f : ℝ → ℝ := F ∘ P
  let G : Phase → ℝ := fun x => fderiv ℝ F x s
  have hP (t : ℝ) : HasDerivAt P s t := by
    simpa only [P, id_eq, one_smul] using (hasDerivAt_id t).smul_const s
  have hPc : Continuous P := continuous_id.smul continuous_const
  have hP1 : P 1 = s := one_smul ℝ s
  have hFdiff : DifferentiableAt ℝ F s := hc.differentiableAt (by norm_num)
  have hf : HasDerivAt f (fderiv ℝ F s s) 1 :=
    hFdiff.hasFDerivAt.comp_hasDerivAt_of_eq 1 (hP 1) hP1.symm
  have hGc : ContDiffAt ℝ 1 G s :=
    (hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hg : HasDerivAt (G ∘ P) (fderiv ℝ G s s) 1 :=
    hGc.differentiableAt_one.hasFDerivAt.comp_hasDerivAt_of_eq 1 (hP 1) hP1.symm
  have hPt : Filter.Tendsto P (nhds 1) (nhds s) := by
    have hPt' : Filter.Tendsto P (nhds 1) (nhds (P 1)) := hPc.continuousAt.tendsto
    simpa only [hP1] using hPt'
  have heq : deriv f =ᶠ[nhds 1] G ∘ P := by
    filter_upwards [hPt.eventually (hc.eventually (by norm_num))] with t ht
    exact (ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hP t) |>.deriv
  exact ⟨hf.deriv, (hg.congr_of_eventuallyEq heq).deriv⟩

theorem radial_transversality_from_tangential_curvature (F : Phase → ℝ) (s : Phase)
    (hsne : s ≠ 0) (hc : ContDiffAt ℝ 2 F s) (hzero : F s = 0)
    (hneg : ∀ t : ℝ, 0 ≤ t → t < 1 → F (t • s) < 0)
    (hcurv : ∀ v : Phase, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v) :
    fderiv ℝ F s s ≠ 0 := by
  intro hstationary
  let f : ℝ → ℝ := fun t => F (t • s)
  obtain ⟨hfirst, hsecond⟩ := radial_slice_first_and_second_derivative F s hc
  have hpositive : 0 < deriv (deriv f) 1 := by
    rw [hsecond]
    exact hcurv s hsne hstationary
  have hfcont : ContinuousAt f 1 := by
    have hPcont : ContinuousAt (fun t : ℝ => t • s) 1 :=
      (continuous_id.smul continuous_const).continuousAt
    have hFcont : ContinuousAt F ((1 : ℝ) • s) := by
      simpa only [one_smul] using hc.continuousAt
    exact hFcont.comp (f := fun t : ℝ => t • s) hPcont
  have hfzero : f 1 = 0 := by simpa [f] using hzero
  have hnot := inward_negative_second_derivative_boundary_not_stationary f hfcont hfzero hneg hpositive
  rw [hfirst, hstationary] at hnot
  exact hnot rfl

theorem inward_negative_derivative_nonnegative (f : ℝ → ℝ) (d : ℝ)
    (hd : HasDerivAt f d 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 0 ≤ t → t < 1 → f t < 0) : 0 ≤ d := by
  have hmax : IsMaxOn f (Set.Icc (0 : ℝ) 1) 1 := by
    intro t ht
    change f t ≤ f 1
    rcases ht.2.eq_or_lt with he | hlt
    · rw [he]
    · rw [hzero]
      exact (hneg t ht.1 hlt).le
  have hseg : segment ℝ (1 : ℝ) 0 ⊆ Set.Icc 0 1 :=
    (convex_Icc (0 : ℝ) 1).segment_subset ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩
  have htangent := sub_mem_posTangentConeAt_of_segment_subset hseg
  have h := hmax.localize.hasFDerivWithinAt_nonpos
    hd.hasFDerivAt.hasFDerivWithinAt htangent
  simpa using h

theorem radial_derivative_positive (F : Phase → ℝ) (s : Phase)
    (hsne : s ≠ 0) (hc : ContDiffAt ℝ 2 F s) (hzero : F s = 0)
    (hneg : ∀ t : ℝ, 0 ≤ t → t < 1 → F (t • s) < 0)
    (hcurv : ∀ v : Phase, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v) :
    0 < fderiv ℝ F s s := by
  have hne := radial_transversality_from_tangential_curvature F s hsne hc hzero hneg hcurv
  have hP : HasDerivAt (fun t : ℝ => t • s) s 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const s
  have hf : HasDerivAt (fun t : ℝ => F (t • s)) (fderiv ℝ F s s) 1 :=
    (hc.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 1 hP
      (one_smul ℝ s).symm
  have hnonneg := inward_negative_derivative_nonnegative _ _ hf
    (by simpa only [one_smul] using hzero) hneg
  exact lt_of_le_of_ne hnonneg hne.symm




open BirkhoffGlobalSection NormedSpace
open scoped Topology

abbrev PhaseNormSphere := {x : Phase // ‖x‖ = 1}
abbrev NonzeroPhase := {x : Phase // x ≠ 0}

noncomputable def radialDirectionMap (S : Set Phase) (hsne : ∀ s ∈ S, s ≠ 0) : S → PhaseNormSphere :=
  fun s => ⟨normalize (s : Phase), norm_normalize (hsne s s.property)⟩

theorem radialDirectionMap_continuous (S : Set Phase) (hsne : ∀ s ∈ S, s ≠ 0) :
    Continuous (radialDirectionMap S hsne) := by
  apply Continuous.subtype_mk
  change Continuous (fun s : S => ‖(s : Phase)‖⁻¹ • (s : Phase))
  exact (continuous_subtype_val.norm.inv₀
    (fun s => norm_ne_zero_iff.mpr (hsne s s.property))).smul continuous_subtype_val

theorem radialDirectionMap_bijective (S : Set Phase) (hsne : ∀ s ∈ S, s ≠ 0)
    (hray : ∀ x : Phase, ‖x‖ = 1 → ∃ r : ℝ, 0 < r ∧ r • x ∈ S)
    (huniq : ∀ x : Phase, ‖x‖ = 1 → ∀ r t : ℝ, 0 < r → 0 < t →
      r • x ∈ S → t • x ∈ S → r = t) :
    Function.Bijective (radialDirectionMap S hsne) := by
  constructor
  · intro s t hst
    have heq : normalize (s : Phase) = normalize (t : Phase) := congrArg Subtype.val hst
    have hspos : 0 < ‖(s : Phase)‖ := norm_pos_iff.mpr (hsne s s.property)
    have htpos : 0 < ‖(t : Phase)‖ := norm_pos_iff.mpr (hsne t t.property)
    have hnr : ‖(s : Phase)‖ = ‖(t : Phase)‖ :=
      huniq (normalize (s : Phase)) (norm_normalize (hsne s s.property))
        ‖(s : Phase)‖ ‖(t : Phase)‖ hspos htpos
        (by simpa only [norm_smul_normalize] using s.property)
        (by rw [heq]; simpa only [norm_smul_normalize] using t.property)
    apply Subtype.ext
    calc
      (s : Phase) = ‖(s : Phase)‖ • normalize (s : Phase) := (norm_smul_normalize _).symm
      _ = ‖(t : Phase)‖ • normalize (t : Phase) := by rw [hnr, heq]
      _ = (t : Phase) := norm_smul_normalize _
  · intro x
    obtain ⟨r, hr, hrs⟩ := hray x x.property
    refine ⟨⟨r • (x : Phase), hrs⟩, ?_⟩
    apply Subtype.ext
    exact (normalize_smul_of_pos hr _).trans (normalize_eq_self_of_norm_eq_one x.property)

noncomputable def radialDirectionHomeomorph (S : Set Phase) (hS : IsCompact S)
    (hsne : ∀ s ∈ S, s ≠ 0)
    (hray : ∀ x : Phase, ‖x‖ = 1 → ∃ r : ℝ, 0 < r ∧ r • x ∈ S)
    (huniq : ∀ x : Phase, ‖x‖ = 1 → ∀ r t : ℝ, 0 < r → 0 < t →
      r • x ∈ S → t • x ∈ S → r = t) : S ≃ₜ PhaseNormSphere := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let e := Equiv.ofBijective (radialDirectionMap S hsne)
    (radialDirectionMap_bijective S hsne hray huniq)
  have he : Continuous e := radialDirectionMap_continuous S hsne
  exact e.toHomeomorphOfContinuousClosed he he.isClosedMap

noncomputable def nonzeroDirection : NonzeroPhase → PhaseNormSphere :=
  fun y => ⟨normalize (y : Phase), norm_normalize y.property⟩

theorem nonzeroDirection_continuous : Continuous nonzeroDirection := by
  apply Continuous.subtype_mk
  change Continuous (fun y : NonzeroPhase => ‖(y : Phase)‖⁻¹ • (y : Phase))
  exact (continuous_subtype_val.norm.inv₀
    (fun y => norm_ne_zero_iff.mpr y.property)).smul continuous_subtype_val

theorem unitThreeSphere_radial_hypotheses_to_norm_sphere (S : Set Phase)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (huniq : ∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ S → (fun i : Fin 4 => t * x i) ∈ S → r = t) :
    (∀ x : Phase, ‖x‖ = 1 → ∃ r : ℝ, 0 < r ∧ r • x ∈ S) ∧
    (∀ x : Phase, ‖x‖ = 1 → ∀ r t : ℝ, 0 < r → 0 < t →
      r • x ∈ S → t • x ∈ S → r = t) := by
  have hrepr : ∀ x : Phase, ‖x‖ = 1 →
      ∃ u ∈ unitThreeSphere, ∃ R : ℝ, 0 < R ∧ R • u = x := by
    intro x hx
    have hxne : x ≠ 0 := by intro he; simp [he] at hx
    exact radial_ray_representation x hxne
  constructor
  · intro x hx
    obtain ⟨u, hu, R, hR, hRx⟩ := hrepr x hx
    obtain ⟨r, hr, hrs⟩ := hray u hu
    refine ⟨r / R, div_pos hr hR, ?_⟩
    rw [← hRx, smul_smul, div_mul_cancel₀ _ hR.ne']
    exact hrs
  · intro x hx r t hr ht hrs hts
    obtain ⟨u, hu, R, hR, hRx⟩ := hrepr x hx
    have hrS : (r * R) • u ∈ S := by
      rw [← hRx, smul_smul] at hrs
      exact hrs
    have htS : (t * R) • u ∈ S := by
      rw [← hRx, smul_smul] at hts
      exact hts
    have he := huniq u hu (r * R) (t * R) (mul_pos hr hR) (mul_pos ht hR) hrS htS
    exact (mul_right_cancel₀ hR.ne') he

theorem radial_coordinates_of_homeomorph (S : Set Phase) (hsne : ∀ s ∈ S, s ≠ 0)
    (e : S ≃ₜ PhaseNormSphere)
    (he : ∀ s : S, (e s : Phase) = normalize (s : Phase)) :
    ∃ b : NonzeroPhase → S, ∃ τ : NonzeroPhase → ℝ,
      Continuous b ∧ Continuous τ ∧
      (∀ y : NonzeroPhase, 0 < τ y ∧ (y : Phase) = τ y • (b y : Phase)) ∧
      (∀ y : NonzeroPhase, (y : Phase) ∈
        {z | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • s} ↔ τ y ≤ 1) := by
  let b : NonzeroPhase → S := e.symm ∘ nonzeroDirection
  let τ : NonzeroPhase → ℝ := fun y => ‖(y : Phase)‖ / ‖(b y : Phase)‖
  have hb : Continuous b := e.symm.continuous.comp nonzeroDirection_continuous
  have hτ : Continuous τ := continuous_subtype_val.norm.div
    (continuous_subtype_val.comp hb).norm (fun y => norm_ne_zero_iff.mpr (hsne _ (b y).property))
  have hpos (y : NonzeroPhase) : 0 < τ y :=
    div_pos (norm_pos_iff.mpr y.property) (norm_pos_iff.mpr (hsne _ (b y).property))
  have hdir (y : NonzeroPhase) : normalize (b y : Phase) = normalize (y : Phase) := by
    rw [← he]
    exact congrArg Subtype.val (e.apply_symm_apply (nonzeroDirection y))
  have hrepr (y : NonzeroPhase) : (y : Phase) = τ y • (b y : Phase) := by
    dsimp only [τ]
    calc
      (y : Phase) = ‖(y : Phase)‖ • normalize (y : Phase) := (norm_smul_normalize _).symm
      _ = ‖(y : Phase)‖ • normalize (b y : Phase) := by rw [hdir]
      _ = (‖(y : Phase)‖ / ‖(b y : Phase)‖) •
          (‖(b y : Phase)‖ • normalize (b y : Phase)) := by
        rw [smul_smul,
          div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hsne _ (b y).property))]
      _ = (‖(y : Phase)‖ / ‖(b y : Phase)‖) • (b y : Phase) := by
        rw [norm_smul_normalize]
  refine ⟨b, τ, hb, hτ, fun y => ⟨hpos y, hrepr y⟩, ?_⟩
  intro y
  constructor
  · rintro ⟨s, hs, t, ht0, ht1, hys⟩
    have ht : 0 < t := by
      apply lt_of_le_of_ne ht0
      intro hz
      have hy0 : (y : Phase) = 0 := by simpa only [← hz, zero_smul] using hys
      exact y.property hy0
    have hes : e ⟨s, hs⟩ = nonzeroDirection y := by
      apply Subtype.ext
      rw [he]
      change normalize s = normalize (y : Phase)
      rw [hys, normalize_smul_of_pos ht]
    have hbs : b y = ⟨s, hs⟩ :=
      e.injective ((e.apply_symm_apply (nonzeroDirection y)).trans hes.symm)
    change ‖(y : Phase)‖ / ‖(b y : Phase)‖ ≤ 1
    rw [hbs, hys, norm_smul, Real.norm_of_nonneg ht0,
      mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr (hsne s hs))]
    exact ht1
  · intro hτ1
    exact ⟨b y, (b y).property, τ y, (hpos y).le, hτ1, hrepr y⟩

theorem compact_radial_coordinates (S : Set Phase) (hS : IsCompact S)
    (hsne : ∀ s ∈ S, s ≠ 0)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (huniq : ∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ S → (fun i : Fin 4 => t * x i) ∈ S → r = t) :
    ∃ b : NonzeroPhase → S, ∃ τ : NonzeroPhase → ℝ,
      Continuous b ∧ Continuous τ ∧
      (∀ y : NonzeroPhase, 0 < τ y ∧ (y : Phase) = τ y • (b y : Phase)) ∧
      (∀ y : NonzeroPhase, (y : Phase) ∈
        {z | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • s} ↔ τ y ≤ 1) := by
  obtain ⟨hray', huniq'⟩ := unitThreeSphere_radial_hypotheses_to_norm_sphere S hray huniq
  let e := radialDirectionHomeomorph S hS hsne hray' huniq'
  have he : ∀ s : S, (e s : Phase) = normalize (s : Phase) := fun _ => rfl
  exact radial_coordinates_of_homeomorph S hsne e he

theorem radial_coordinates_strict_inside_is_interior (S : Set Phase)
    (τ : NonzeroPhase → ℝ) (hτ : Continuous τ)
    (hK : ∀ y : NonzeroPhase, (y : Phase) ∈
      {z | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • s} ↔ τ y ≤ 1)
    (x : NonzeroPhase) (hx : τ x < 1) :
    (x : Phase) ∈ interior {z | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • s} := by
  let V : Set NonzeroPhase := {y | τ y < 1}
  have hV : IsOpen V := isOpen_Iio.preimage hτ
  have hnonzero : IsOpen {y : Phase | y ≠ 0} := isOpen_ne
  have hU : IsOpen (Subtype.val '' V : Set Phase) :=
    hnonzero.isOpenEmbedding_subtypeVal.isOpenMap V hV
  have hxU : (x : Phase) ∈ (Subtype.val '' V : Set Phase) := ⟨x, hx, rfl⟩
  have hsub : (Subtype.val '' V : Set Phase) ⊆
      {z | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • s} := by
    rintro y ⟨z, hz, rfl⟩
    exact (hK z).mpr hz.le
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (hU.mem_nhds hxU) hsub

theorem compact_radial_filling_nonzero_nonboundary_interior (S : Set Phase)
    (hS : IsCompact S) (hsne : ∀ s ∈ S, s ≠ 0)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (huniq : ∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ S → (fun i : Fin 4 => t * x i) ∈ S → r = t)
    (x : Phase) (hxne : x ≠ 0)
    (hxK : x ∈ {z | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • s})
    (hxS : x ∉ S) :
    x ∈ interior {z | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • s} := by
  obtain ⟨b, τ, hb, hτ, hrepr, hK⟩ := compact_radial_coordinates S hS hsne hray huniq
  let x' : NonzeroPhase := ⟨x, hxne⟩
  have hxle : τ x' ≤ 1 := (hK x').mp hxK
  have hxlt : τ x' < 1 := by
    apply lt_of_le_of_ne hxle
    intro he
    have hxeq := (hrepr x').2
    rw [he, one_smul] at hxeq
    apply hxS
    change (x' : Phase) ∈ S
    rw [hxeq]
    exact (b x').property
  exact radial_coordinates_strict_inside_is_interior S τ hτ hK x' hxlt

theorem interior_point_locally_convex (K : Set Phase) (x : Phase) (hx : x ∈ interior K) :
    ∃ U : Set Phase, U ∈ nhds x ∧ Convex ℝ (K ∩ U) := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  refine ⟨Metric.ball x r, Metric.ball_mem_nhds x hr, ?_⟩
  rw [Set.inter_eq_right.mpr hsub]
  exact convex_ball _ _




open scoped Topology

open BirkhoffGlobalSection NormedSpace

/-- A continuous homogeneous quadratic function positive on the kernel of a
linear functional can be made positive definite by a positive rank-one term. -/
theorem finite_dimensional_quadratic_correction (L : Phase →L[ℝ] ℝ) (q : Phase → ℝ)
    (hq : Continuous q) (hhom : ∀ r : ℝ, ∀ v : Phase, q (r • v) = r ^ 2 * q v)
    (htan : ∀ v : Phase, v ≠ 0 → L v = 0 → 0 < q v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Phase, v ≠ 0 → 0 < q v + c * (L v) ^ 2 := by
  let T : Set Phase := {v | ‖v‖ = 1}
  have hT : IsCompact T := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : Phase) 1
  let B := T ∩ {v | q v ≤ 0}
  have hB : IsCompact B := hT.inter_right (isClosed_le hq continuous_const)
  have hL : Continuous (fun v : Phase => (L v) ^ 2) := L.continuous.pow 2
  have hLpos : ∀ v ∈ B, 0 < (L v) ^ 2 := by
    intro v hv
    have hvne : v ≠ 0 := by
      intro he
      have hvnorm : ‖v‖ = 1 := hv.1
      norm_num [he] at hvnorm
    have hLv : L v ≠ 0 := by
      intro he
      have hpos := htan v hvne he
      exact (not_lt_of_ge hv.2) hpos
    exact sq_pos_of_ne_zero hLv
  have hunit : ∃ c : ℝ, 0 < c ∧ ∀ v ∈ T, 0 < q v + c * (L v) ^ 2 := by
    rcases B.eq_empty_or_nonempty with hempty | hne
    · refine ⟨1, zero_lt_one, ?_⟩
      intro v hv
      have hqpos : 0 < q v := by
        by_contra hh
        have hvB : v ∈ B := ⟨hv, le_of_not_gt hh⟩
        rw [hempty] at hvB
        exact hvB
      nlinarith [sq_nonneg (L v)]
    · obtain ⟨u, hu, hminL⟩ := hB.exists_isMinOn hne hL.continuousOn
      obtain ⟨w, hw, hminq⟩ := hB.exists_isMinOn hne hq.continuousOn
      let α := (L u) ^ 2
      let M := max 0 (-q w)
      let c := (M + 1) / α
      have hα : 0 < α := hLpos u hu
      have hM : 0 ≤ M := le_max_left _ _
      have hc : 0 < c := div_pos (by linarith) hα
      have hca : c * α = M + 1 := div_mul_cancel₀ _ hα.ne'
      have hqM : -M ≤ q w := by
        have hh : -q w ≤ M := le_max_right _ _
        linarith
      refine ⟨c, hc, ?_⟩
      intro v hv
      by_cases hqpos : 0 < q v
      · exact add_pos_of_pos_of_nonneg hqpos (mul_nonneg hc.le (sq_nonneg _))
      · have hvB : v ∈ B := ⟨hv, le_of_not_gt hqpos⟩
        have hαv : α ≤ (L v) ^ 2 := hminL hvB
        have hqv : q w ≤ q v := hminq hvB
        have hmul := mul_le_mul_of_nonneg_left hαv hc.le
        nlinarith
  obtain ⟨c, hc, hcu⟩ := hunit
  refine ⟨c, hc, ?_⟩
  intro v hv
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : normalize v ∈ T := norm_normalize hv
  have hpos := hcu _ hu
  have hqv : q v = ‖v‖ ^ 2 * q (normalize v) := by
    simpa only [norm_smul_normalize] using hhom ‖v‖ (normalize v)
  have hLv : L v = ‖v‖ * L (normalize v) := by
    simpa only [norm_smul_normalize, smul_eq_mul] using L.map_smul ‖v‖ (normalize v)
  calc
    0 < ‖v‖ ^ 2 * (q (normalize v) + c * (L (normalize v)) ^ 2) :=
      mul_pos (sq_pos_of_pos hnorm) hpos
    _ = q v + c * (L v) ^ 2 := by rw [hqv, hLv]; ring

theorem tangential_hessian_rank_one_correction (F : Phase → ℝ) (s : Phase)
    (hc : ContDiffAt ℝ 2 F s)
    (htan : ∀ v : Phase, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Phase, v ≠ 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v + c * (fderiv ℝ F s v) ^ 2 := by
  let H := fderiv ℝ (fderiv ℝ F) s
  let q : Phase → ℝ := fun v => H v v
  have hD : DifferentiableAt ℝ (fderiv ℝ F) s :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hq : Continuous q := H.continuous.clm_apply continuous_id
  have hhom : ∀ r : ℝ, ∀ v : Phase, q (r • v) = r ^ 2 * q v := by
    intro r v
    simp only [q, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hessian_eq (v : Phase) :
      fderiv ℝ (fun x => fderiv ℝ F x v) s v = q v := by
    rw [fderiv_clm_apply hD (differentiableAt_const v)]
    simp [q, H]
  have htanq : ∀ v : Phase, v ≠ 0 → fderiv ℝ F s v = 0 → 0 < q v := by
    intro v hv hLv
    rw [← hessian_eq]
    exact htan v hv hLv
  obtain ⟨c, hcpos, hpos⟩ := finite_dimensional_quadratic_correction (fderiv ℝ F s) q hq hhom htanq
  refine ⟨c, hcpos, ?_⟩
  intro v hv
  rw [hessian_eq]
  exact hpos v hv

theorem corrected_defining_function_hessian_identity (F : Phase → ℝ) (s v : Phase) (c : ℝ)
    (hc : ContDiffAt ℝ 2 F s) (hzero : F s = 0) :
    let G : Phase → ℝ := fun x => F x + c * (F x * F x)
    fderiv ℝ (fun x => fderiv ℝ G x v) s v =
      fderiv ℝ (fun x => fderiv ℝ F x v) s v + 2 * c * (fderiv ℝ F s v) ^ 2 := by
  let G : Phase → ℝ := fun x => F x + c * (F x * F x)
  change fderiv ℝ (fun x => fderiv ℝ G x v) s v =
    fderiv ℝ (fun x => fderiv ℝ F x v) s v + 2 * c * (fderiv ℝ F s v) ^ 2
  let D : Phase → ℝ := fun x => fderiv ℝ F x v
  have hfirst (x : Phase) (hx : DifferentiableAt ℝ F x) :
      fderiv ℝ G x v = D x + c * (F x * D x + F x * D x) := by
    have hh := hx.hasFDerivAt.add ((hx.hasFDerivAt.mul hx.hasFDerivAt).const_mul c)
    have hh' : fderiv ℝ G x = fderiv ℝ F x +
        c • (F x • fderiv ℝ F x + F x • fderiv ℝ F x) := hh.fderiv
    rw [hh']
    simp [D, smul_eq_mul]
    ring
  have hDc : ContDiffAt ℝ 1 D s :=
    (hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hD := hDc.differentiableAt_one.hasFDerivAt
  have hF := (hc.differentiableAt (by norm_num)).hasFDerivAt
  let g : Phase → ℝ := fun x => D x + c * (F x * D x + F x * D x)
  have hg := hD.add (((hF.mul hD).add (hF.mul hD)).const_mul c)
  have heq : (fun x => fderiv ℝ G x v) =ᶠ[nhds s] g := by
    filter_upwards [hc.eventually (by norm_num)] with x hx
    exact hfirst x (hx.differentiableAt (by norm_num))
  have hG := hg.congr_of_eventuallyEq heq
  rw [hG.fderiv]
  simp only [smul_eq_mul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    hzero, zero_mul, zero_add, D]
  ring




open BirkhoffGlobalSection NormedSpace
open scoped Topology

theorem canonical_hessian_apply_eq (F : Phase → ℝ) (x v : Phase) (hc : ContDiffAt ℝ 2 F x) :
    fderiv ℝ (fun z => fderiv ℝ F z v) x v = fderiv ℝ (fderiv ℝ F) x v v := by
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  rw [fderiv_clm_apply hD (differentiableAt_const v)]
  simp

theorem positive_hessian_neighborhood (F : Phase → ℝ) (s : Phase)
    (hc : ContDiffAt ℝ 2 F s)
    (hpos : ∀ v : Phase, v ≠ 0 → 0 < fderiv ℝ (fun z => fderiv ℝ F z v) s v) :
    ∃ r > 0, ∀ x ∈ Metric.ball s r, ContDiffAt ℝ 2 F x ∧
      ∀ v : Phase, v ≠ 0 → 0 < fderiv ℝ (fun z => fderiv ℝ F z v) x v := by
  let H := fun x => fderiv ℝ (fderiv ℝ F) x
  have hHc : ContinuousAt H s :=
    (hc.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv (by norm_num)
  let T : Set Phase := {v | ‖v‖ = 1}
  have hT : IsCompact T := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : Phase) 1
  have hunit : ∀ v ∈ T, 0 < H s v v := by
    intro v hv
    have hvne : v ≠ 0 := by intro he; have hh : ‖v‖ = 1 := hv; norm_num [he] at hh
    rw [← canonical_hessian_apply_eq F s v hc]
    exact hpos v hvne
  have hev : ∀ᶠ x in nhds s, ∀ v ∈ T, 0 < H x v v := by
    apply hT.eventually_forall_of_forall_eventually
    intro v hv
    have hHp : ContinuousAt (fun p : Phase × Phase => H p.1) (s, v) := hHc.comp continuousAt_fst
    have hQp : ContinuousAt (fun p : Phase × Phase => H p.1 p.2 p.2) (s, v) :=
      (hHp.clm_apply continuousAt_snd).clm_apply continuousAt_snd
    exact hQp.preimage_mem_nhds (Ioi_mem_nhds (hunit v hv))
  have hall : ∀ᶠ x in nhds s, ContDiffAt ℝ 2 F x ∧
      ∀ v : Phase, v ≠ 0 → 0 < fderiv ℝ (fun z => fderiv ℝ F z v) x v := by
    filter_upwards [hc.eventually (by norm_num), hev] with x hx hxu
    refine ⟨hx, ?_⟩
    intro v hv
    have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : normalize v ∈ T := norm_normalize hv
    have hscale (a : ℝ) (u : Phase) : H x (a • u) (a • u) = a ^ 2 * H x u u := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    have hrepr : H x v v = ‖v‖ ^ 2 * H x (normalize v) (normalize v) := by
      simpa only [norm_smul_normalize] using hscale ‖v‖ (normalize v)
    rw [canonical_hessian_apply_eq F x v hx, hrepr]
    exact mul_pos (sq_pos_of_pos hnorm) (hxu _ hu)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  exact ⟨r, hr, hball⟩

theorem affine_line_first_second_hasDeriv (F : Phase → ℝ) (x v : Phase) (t : ℝ)
    (hc : ContDiffAt ℝ 2 F (x + t • v)) :
    let f : ℝ → ℝ := fun u => F (x + u • v)
    HasDerivAt f (fderiv ℝ F (x + t • v) v) t ∧
      HasDerivAt (deriv f) (fderiv ℝ (fun z => fderiv ℝ F z v) (x + t • v) v) t := by
  let P : ℝ → Phase := fun u => x + u • v
  let f : ℝ → ℝ := F ∘ P
  let D : Phase → ℝ := fun z => fderiv ℝ F z v
  have hP (u : ℝ) : HasDerivAt P v u := by
    have h := (hasDerivAt_const u x).add ((hasDerivAt_id u).smul_const v)
    change HasDerivAt P (0 + (1 : ℝ) • v) u at h
    simpa only [one_smul, zero_add] using h
  have hPc : Continuous P := continuous_const.add (continuous_id.smul continuous_const)
  have hf := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hP t)
  have hDc : ContDiffAt ℝ 1 D (P t) :=
    (hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hd := hDc.differentiableAt_one.hasFDerivAt.comp_hasDerivAt t (hP t)
  have heq : deriv f =ᶠ[nhds t] D ∘ P := by
    have hPt : Filter.Tendsto P (nhds t) (nhds (P t)) := hPc.continuousAt.tendsto
    filter_upwards [hPt.eventually (hc.eventually (by norm_num))] with u hu
    exact ((hu.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt u (hP u)).deriv
  exact ⟨hf, hd.congr_of_eventuallyEq heq⟩

theorem convexOn_of_nonnegative_directional_hessian (F : Phase → ℝ) (U : Set Phase)
    (hU : Convex ℝ U) (hc : ∀ x ∈ U, ContDiffAt ℝ 2 F x)
    (hpos : ∀ x ∈ U, ∀ v : Phase, 0 ≤ fderiv ℝ (fun z => fderiv ℝ F z v) x v) :
    ConvexOn ℝ U F := by
  refine ⟨hU, ?_⟩
  intro x hx y hy a b ha hb hab
  let v := y - x
  let P : ℝ → Phase := fun t => x + t • v
  let f : ℝ → ℝ := F ∘ P
  have hPformula (t : ℝ) : P t = (1 - t) • x + t • y := by
    ext i
    simp only [P, v, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hPU : ∀ t ∈ Set.Icc (0 : ℝ) 1, P t ∈ U := by
    intro t ht
    rw [hPformula]
    exact hU hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :=
    affine_line_first_second_hasDeriv F x v t (hc _ (hPU t ht))
  have hfc : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f :=
    convexOn_of_deriv2_nonneg' (convex_Icc _ _)
      (fun t ht => (hderiv t ht).1.differentiableAt.differentiableWithinAt)
      (fun t ht => (hderiv t ht).2.differentiableAt.differentiableWithinAt)
      (fun t ht => by
        change 0 ≤ deriv (deriv f) t
        have he : deriv (deriv f) t =
            fderiv ℝ (fun z => fderiv ℝ F z v) (P t) v := (hderiv t ht).2.deriv
        rw [he]
        exact hpos _ (hPU t ht) v)
  have hh := hfc.2 (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) ha hb hab
  have hPb : P b = a • x + b • y := by
    rw [hPformula]
    have he : 1 - b = a := by linarith
    rw [he]
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, f, Function.comp_apply,
    hPb, P, zero_smul, add_zero, one_smul, v, add_sub_cancel] using hh

theorem local_convex_sublevel_of_positive_tangential_hessian (F : Phase → ℝ) (s : Phase)
    (hc : ContDiffAt ℝ 2 F s) (hz : F s = 0)
    (htan : ∀ v : Phase, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v) :
    ∃ U : Set Phase, U ∈ nhds s ∧ Convex ℝ ({y | F y ≤ 0} ∩ U) := by
  obtain ⟨c, hcp, hpos⟩ := tangential_hessian_rank_one_correction F s hc htan
  let k := c / 2
  let G : Phase → ℝ := fun x => F x + k * (F x * F x)
  have hcG : ContDiffAt ℝ 2 G s := hc.add (contDiffAt_const.mul (hc.mul hc))
  have hGpos : ∀ v : Phase, v ≠ 0 → 0 < fderiv ℝ (fun x => fderiv ℝ G x v) s v := by
    intro v hv
    rw [corrected_defining_function_hessian_identity F s v k hc hz]
    have hk : 2 * k = c := by dsimp [k]; ring
    rw [hk]
    exact hpos v hv
  obtain ⟨r, hr, hball⟩ := positive_hessian_neighborhood G s hcG hGpos
  have hcoeff : ∀ᶠ y in nhds s, 0 < 1 + k * F y := by
    have hcon : ContinuousAt (fun y => 1 + k * F y) s :=
      continuousAt_const.add (hc.continuousAt.const_mul k)
    exact hcon.preimage_mem_nhds (Ioi_mem_nhds (by simp [hz]))
  obtain ⟨r', hr', hball'⟩ := Metric.mem_nhds_iff.mp hcoeff
  let R := min r r'
  have hR : 0 < R := lt_min hr hr'
  have hsub : Metric.ball s R ⊆ Metric.ball s r := Metric.ball_subset_ball (min_le_left _ _)
  have hsub' : Metric.ball s R ⊆ Metric.ball s r' := Metric.ball_subset_ball (min_le_right _ _)
  have hconv : ConvexOn ℝ (Metric.ball s R) G :=
    convexOn_of_nonnegative_directional_hessian G _ (convex_ball s R)
      (fun y hy => (hball y (hsub hy)).1)
      (fun y hy v => by
        by_cases hv : v = 0
        · simp [hv]
        · exact le_of_lt ((hball y (hsub hy)).2 v hv))
  refine ⟨Metric.ball s R, Metric.ball_mem_nhds s hR, ?_⟩
  have heq : {y | F y ≤ 0} ∩ Metric.ball s R = {y ∈ Metric.ball s R | G y ≤ 0} := by
    ext y
    constructor
    · rintro ⟨hyF, hy⟩
      refine ⟨hy, ?_⟩
      have hp := hball' (hsub' hy)
      have he : G y = F y * (1 + k * F y) := by dsimp [G]; ring
      rw [he]
      exact mul_nonpos_of_nonpos_of_nonneg hyF hp.le
    · rintro ⟨hy, hyG⟩
      refine ⟨?_, hy⟩
      have hp := hball' (hsub' hy)
      have he : G y = F y * (1 + k * F y) := by dsimp [G]; ring
      rw [he] at hyG
      by_contra hn
      exact (not_lt_of_ge hyG) (mul_pos (lt_of_not_ge hn) hp)
  rw [heq]
  exact hconv.convex_le 0




open BirkhoffGlobalSection
open scoped Topology

theorem radial_outward_positive_of_ball (F : Phase → ℝ) (s b : Phase) (r t : ℝ)
    (ht : 1 < t) (hb : b ∈ Metric.ball s r) (hy : t • b ∈ Metric.ball s r)
    (hFb : F b = 0)
    (hball : ∀ z ∈ Metric.ball s r, DifferentiableAt ℝ F z ∧ 0 < fderiv ℝ F z z) :
    0 < F (t • b) := by
  have htden : 0 < t - 1 := by linarith
  have hpoints : ∀ u ∈ Set.Icc (1 : ℝ) t, u • b ∈ Metric.ball s r := by
    intro u hu
    let β := (u - 1) / (t - 1)
    have hβ0 : 0 ≤ β := div_nonneg (sub_nonneg.mpr hu.1) htden.le
    have hβ1 : β ≤ 1 := (div_le_one htden).mpr (sub_le_sub_right hu.2 1)
    have hmem := (convex_ball s r) hb hy (sub_nonneg.mpr hβ1) hβ0
      (show (1 - β) + β = 1 by ring)
    have hden : β * (t - 1) = u - 1 := div_mul_cancel₀ _ htden.ne'
    have heq : (1 - β) • b + β • (t • b) = u • b := by
      rw [smul_smul, ← add_smul]
      congr 1
      nlinarith
    rw [heq] at hmem
    exact hmem
  let f : ℝ → ℝ := fun u => F (u • b)
  have hderiv : ∀ u ∈ Set.Icc (1 : ℝ) t,
      HasDerivAt f (fderiv ℝ F (u • b) b) u := by
    intro u hu
    have hP : HasDerivAt (fun a : ℝ => a • b) b u := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id u).smul_const b
    exact (hball _ (hpoints u hu)).1.hasFDerivAt.comp_hasDerivAt u hP
  have hpositive : ∀ u ∈ Set.Icc (1 : ℝ) t, 0 < fderiv ℝ F (u • b) b := by
    intro u hu
    have hpos := (hball _ (hpoints u hu)).2
    have heq : fderiv ℝ F (u • b) (u • b) = u * fderiv ℝ F (u • b) b := by
      rw [map_smul, smul_eq_mul]
    rw [heq] at hpos
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu.1
    nlinarith
  have hf : ContinuousOn f (Set.Icc (1 : ℝ) t) :=
    fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Set.Icc (1 : ℝ) t) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hf (fun u hu => by
      have hu' := interior_subset hu
      rw [(hderiv u hu').deriv]
      exact hpositive u hu')
  have hlt := hmono ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht
  simpa only [f, one_smul, hFb] using hlt

theorem radial_filling_boundary_locally_eq_sublevel (F : Phase → ℝ) (S : Set Phase)
    (s : NonzeroPhase) (hc : ContDiffAt ℝ 2 F (s : Phase))
    (hrad : 0 < fderiv ℝ F (s : Phase) (s : Phase))
    (b : NonzeroPhase → S) (τ : NonzeroPhase → ℝ) (hb : Continuous b)
    (hrepr : ∀ y : NonzeroPhase, 0 < τ y ∧ (y : Phase) = τ y • (b y : Phase))
    (hK : ∀ y : NonzeroPhase, (y : Phase) ∈
      {z | ∃ u ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • u} ↔ τ y ≤ 1)
    (hfix : (b s : Phase) = (s : Phase)) (hF0 : ∀ u ∈ S, F u = 0)
    (hsign : ∀ y ∈ {z | ∃ u ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • u}, F y ≤ 0) :
    let K : Set Phase := {z | ∃ u ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • u}
    ∃ U : Set Phase, U ∈ nhds (s : Phase) ∧ K ∩ U = {y | F y ≤ 0} ∩ U := by
  let J : Phase → ℝ := fun z => fderiv ℝ F z z
  have hJc : ContinuousAt J (s : Phase) :=
    (hc.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_id
  have hJpos : {z | 0 < J z} ∈ nhds (s : Phase) :=
    hJc.preimage_mem_nhds (Ioi_mem_nhds hrad)
  have hnear : {z | DifferentiableAt ℝ F z ∧ 0 < J z} ∈ nhds (s : Phase) := by
    filter_upwards [hc.eventually (by norm_num), hJpos] with z hz hpos
    exact ⟨hz.differentiableAt (by norm_num), hpos⟩
  obtain ⟨r, hr, hrball⟩ := Metric.mem_nhds_iff.mp hnear
  have hbc : Continuous (fun y : NonzeroPhase => (b y : Phase)) := continuous_subtype_val.comp hb
  have hbcAt : ContinuousAt (fun y : NonzeroPhase => (b y : Phase)) s := hbc.continuousAt
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.mp hbcAt (r / 2) (by linarith)
  let η := min δ (min (r / 2) (‖(s : Phase)‖ / 2))
  have hspos : 0 < ‖(s : Phase)‖ := norm_pos_iff.mpr s.property
  have hη : 0 < η := lt_min hδ (lt_min (by linarith) (by linarith))
  have hηδ : η ≤ δ := min_le_left _ _
  have hηr : η ≤ r / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηs : η ≤ ‖(s : Phase)‖ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨Metric.ball (s : Phase) η, Metric.ball_mem_nhds _ hη, ?_⟩
  ext y
  constructor
  · rintro ⟨hyK, hyU⟩
    exact ⟨hsign y hyK, hyU⟩
  · rintro ⟨hyF, hyU⟩
    refine ⟨?_, hyU⟩
    have hyne : y ≠ 0 := by
      intro he
      have hd : dist y (s : Phase) < η := hyU
      rw [he, dist_zero_left] at hd
      linarith
    let y' : NonzeroPhase := ⟨y, hyne⟩
    have hyδ : dist y' s < δ := (show dist y (s : Phase) < η from hyU).trans_le hηδ
    have hbnear : dist (b y' : Phase) (s : Phase) < r / 2 := by
      have hh := hδb hyδ
      simpa only [hfix] using hh
    have hbball : (b y' : Phase) ∈ Metric.ball (s : Phase) r := hbnear.trans (by linarith)
    have hyball : y ∈ Metric.ball (s : Phase) r :=
      (show dist y (s : Phase) < η from hyU).trans_le hηr |>.trans (by linarith)
    by_contra hyK
    have ht : 1 < τ y' := lt_of_not_ge (fun h => hyK ((hK y').mpr h))
    have hpositive := radial_outward_positive_of_ball F (s : Phase) (b y' : Phase) r (τ y')
      ht hbball (by rw [← (hrepr y').2]; exact hyball) (hF0 _ (b y').property) hrball
    rw [← (hrepr y').2] at hpositive
    exact (not_lt_of_ge hyF) hpositive

theorem radial_coordinates_fix_boundary (S : Set Phase) (hsne : ∀ u ∈ S, u ≠ 0)
    (huniq : ∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ S → (fun i : Fin 4 => t * x i) ∈ S → r = t)
    (b : NonzeroPhase → S) (τ : NonzeroPhase → ℝ)
    (hrepr : ∀ y : NonzeroPhase, 0 < τ y ∧ (y : Phase) = τ y • (b y : Phase))
    (s : NonzeroPhase) (hs : (s : Phase) ∈ S) : (b s : Phase) = (s : Phase) := by
  obtain ⟨u, hu, R, hR, hRb⟩ := radial_ray_representation (b s : Phase) (hsne _ (b s).property)
  change R • u = (b s : Phase) at hRb
  have hRS : R • u ∈ S := by rw [hRb]; exact (b s).property
  have hys := (hrepr s).2
  rw [← hRb, smul_smul] at hys
  have hYS : (τ s * R) • u ∈ S := by rw [← hys]; exact hs
  have he := huniq u hu (τ s * R) R (mul_pos (hrepr s).1 hR) hR hYS hRS
  have hτ1 : τ s = 1 := by nlinarith
  have hsrepr := (hrepr s).2
  rw [hτ1, one_smul] at hsrepr
  exact hsrepr.symm

theorem compact_radial_boundary_locally_eq_sublevel (F : Phase → ℝ) (S : Set Phase)
    (hS : IsCompact S) (hF0 : ∀ s ∈ S, F s = 0)
    (hTH : HasPositiveTangentialHessianOn F S)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (huniq : ∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ S → (fun i : Fin 4 => t * x i) ∈ S → r = t)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0)
    (s : Phase) (hs : s ∈ S) :
    let K : Set Phase := {z | ∃ u ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = t • u}
    ∃ U : Set Phase, U ∈ nhds s ∧ K ∩ U = {y | F y ≤ 0} ∩ U := by
  have hfzero := radial_origin_negative F S hray hneg
  have hsne : ∀ u ∈ S, u ≠ 0 := by
    intro u hu he
    have hf := hF0 u hu
    rw [he] at hf
    linarith
  obtain ⟨b, τ, hb, hτ, hrepr, hK⟩ := compact_radial_coordinates S hS hsne hray huniq
  let s' : NonzeroPhase := ⟨s, hsne s hs⟩
  have hrad := radial_derivative_positive F s (hsne s hs) (hTH.1 s hs) (hF0 s hs)
    (radial_scaling_negative F S hF0 hray hneg s hs) (hTH.2 s hs)
  have hfix := radial_coordinates_fix_boundary S hsne huniq b τ hrepr s' hs
  exact radial_filling_boundary_locally_eq_sublevel F S s' (hTH.1 s hs) hrad b τ hb hrepr hK
    hfix hF0 (radial_filling_sign_and_zero_set F S hF0 hray hneg).1




open BirkhoffGlobalSection
open scoped Topology

theorem solution
    (F : Phase → ℝ) (S : Set Phase)
    (hS : IsCompact S)
    (hF0 : ∀ s ∈ S, F s = 0)
    (hreg : ∀ s ∈ S, fderiv ℝ F s ≠ 0)
    (hTH : HasPositiveTangentialHessianOn F S)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (huniq : ∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ S → (fun i : Fin 4 => t * x i) ∈ S → r = t)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0) :
    let K : Set Phase :=
      {y : Phase | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s}
    ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U) := by
  let K : Set Phase := {y | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s}
  change ∀ x ∈ K, ∃ U : Set Phase, U ∈ nhds x ∧ Convex ℝ (K ∩ U)
  intro x hx
  by_cases hxS : x ∈ S
  · obtain ⟨U, hU, heq⟩ := compact_radial_boundary_locally_eq_sublevel F S hS hF0 hTH hray huniq hneg x hxS
    obtain ⟨V, hV, hconv⟩ := local_convex_sublevel_of_positive_tangential_hessian F x
      (hTH.1 x hxS) (hF0 x hxS) (hTH.2 x hxS)
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hU hV)
    refine ⟨Metric.ball x r, Metric.ball_mem_nhds x hr, ?_⟩
    have hsets : K ∩ Metric.ball x r = ({y | F y ≤ 0} ∩ V) ∩ Metric.ball x r := by
      ext y
      constructor
      · rintro ⟨hyK, hyB⟩
        have hyU := (hsub hyB).1
        have h := Set.mem_of_mem_inter_left (heq ▸ (show y ∈ K ∩ U from ⟨hyK, hyU⟩))
        exact ⟨⟨h, (hsub hyB).2⟩, hyB⟩
      · rintro ⟨⟨hyF, _⟩, hyB⟩
        have h : y ∈ K ∩ U := heq.symm ▸ ⟨hyF, (hsub hyB).1⟩
        exact ⟨h.1, hyB⟩
    rw [hsets]
    exact hconv.inter (convex_ball x r)
  · by_cases hx0 : x = 0
    · subst x
      exact radial_filling_origin_case F S hS hF0 hray hneg
    · have hfzero := radial_origin_negative F S hray hneg
      have hsne : ∀ s ∈ S, s ≠ 0 := by
        intro s hs he
        have hf := hF0 s hs
        rw [he] at hf
        linarith
      exact interior_point_locally_convex K x
        (compact_radial_filling_nonzero_nonboundary_interior S hS hsne hray huniq x hx0 hx hxS)
