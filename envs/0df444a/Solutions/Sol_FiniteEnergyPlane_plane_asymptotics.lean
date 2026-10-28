-- Prove2me | solution 1 for FiniteEnergyPlane.plane_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T21:16:18.151857+00:00
-- url     : https://prove2.me/submissions/2c548fc4-e75d-41d2-ac09-d355311377f5

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_pos_of_plane
import Theorems.Thm_FiniteEnergyPlane_energyDensity_nonneg
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_norm_sub_le_of_norm_mul_fderiv_le
import Theorems.Thm_FiniteEnergyPlane_loopAction_ccwLoop_eq_dlambdaEnergy
import Theorems.Thm_FiniteEnergyPlane_exists_norm_mul_gradNorm_le_of_plane
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_cylinder_limit



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A continuous `m : ℝ → ℝ` that gains at least `1` over every step of length `L > 0` beyond
`s₀` tends to `+∞`. -/
theorem tendsto_atTop_of_add_le_step_aux (m : ℝ → ℝ) (hm : Continuous m) (L s₀ : ℝ)
    (hL : 0 < L) (hstep : ∀ s, s₀ ≤ s → m s + 1 ≤ m (s + L)) : Tendsto m atTop atTop := by
  have hind : ∀ j : ℕ, ∀ t, s₀ ≤ t → m t + j ≤ m (t + j * L) := by
    intro j
    induction j with
    | zero => intro t _; simp
    | succ j ih =>
      intro t ht
      have h1 := ih t ht
      have h2 := hstep (t + j * L) (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
      push_cast
      have : t + (j + 1) * L = t + j * L + L := by ring
      rw [this]
      linarith
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := s₀) (b := s₀ + L)).bddBelow_image hm.continuousOn
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨j₀, hj₀⟩ := exists_nat_ge (b - B)
  refine ⟨s₀ + (j₀ + 1) * L, fun s hs => ?_⟩
  set j : ℕ := ⌊(s - s₀) / L⌋₊ with hj
  have hq : 0 ≤ (s - s₀) / L := div_nonneg (by nlinarith) hL.le
  have hjle : (j : ℝ) ≤ (s - s₀) / L := Nat.floor_le hq
  have hjlt : (s - s₀) / L < j + 1 := Nat.lt_floor_add_one _
  have hjL : (j : ℝ) * L ≤ s - s₀ := by rwa [le_div_iff₀ hL] at hjle
  have hjL' : s - s₀ < (j + 1) * L := by rwa [div_lt_iff₀ hL] at hjlt
  have hj0 : (j₀ : ℝ) ≤ j := by
    have : (j₀ + 1 : ℝ) * L ≤ s - s₀ := by linarith
    have h3 : (j₀ : ℝ) + 1 < j + 1 + 1 := by
      by_contra hc
      push_neg at hc
      nlinarith
    have h4 : (j₀ : ℕ) < j + 1 := by exact_mod_cast (by linarith : (j₀ : ℝ) < j + 1)
    exact_mod_cast Nat.lt_succ_iff.1 h4
  set t := s - j * L with ht
  have htI : t ∈ Set.Icc s₀ (s₀ + L) := ⟨by linarith, by linarith⟩
  have hmt : B ≤ m t := hB ⟨t, htI, rfl⟩
  have := hind j t htI.1
  have hs' : t + j * L = s := by rw [ht]; ring
  rw [hs'] at this
  linarith

/-- Hofer 1993, Theorem 31. -/
theorem plane_asymptotics_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    0 < (dlambdaEnergy H Set.univ u).toReal ∧
      Tendsto (fun z => aCoord H (u z)) (cocompact ℂ) atTop ∧
      Tendsto (fun R => loopAction H u (ccwLoop R)) atTop
        (𝓝 (dlambdaEnergy H Set.univ u).toReal) ∧
      ∀ R : ℕ → ℝ, Tendsto R atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : ReebOrbit H,
        P.T = (dlambdaEnergy H Set.univ u).toReal ∧ ∃ c : ℝ,
          TendstoCInfty (fun k => loopInS H u (ccwLoop (R (φ k)))) (fun t => P.x (P.T * t + c)) := by
  set D := dlambdaEnergy H Set.univ u with hDdef
  have hD0 : 0 < D := dlambdaEnergy_pos_of_plane H hH J hJ u hu hnc
  have hDE : D ≤ energy H Set.univ u :=
    (energyDensity_nonneg H hH J hJ Set.univ isOpen_univ u hu).2.2.1
  have hDtop : D ≠ ⊤ := ne_top_of_le_ne_top hu.2.2.2.ne hDE
  have hT : 0 < D.toReal := ENNReal.toReal_pos hD0.ne' hDtop
  obtain ⟨C, hC⟩ := exists_norm_mul_gradNorm_le_of_plane H hH J hJ u hu
  have hY := exists_subseq_cylinder_limit H hH J hJ u hu hnc ⟨C, hC⟩
  refine ⟨hT, ?_, ?_, ?_⟩
  · -- `a ∘ u → +∞`
    obtain ⟨-, -, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
    have hsm : ContDiff ℝ ∞ u := contDiffOn_univ.1 hu.1
    set f : ℂ → ℝ := fun z => aCoord H (u z) with hf
    have hfd : ∀ z, DifferentiableAt ℝ f z := by
      intro z
      have h1 : DifferentiableAt ℝ (aCoord H) (u z) :=
        (haCs.differentiableOn (by simp)).differentiableAt
          ((isOpen_ne).mem_nhds (hu.2.1 z (Set.mem_univ _)))
      exact h1.comp z (hsm.differentiable (by simp) z)
    have hfc : Continuous f := continuous_iff_continuousAt.2 fun z => (hfd z).continuousAt
    have hfC : ∀ z : ℂ, ‖z‖ * ‖fderiv ℝ f z‖ ≤ C := by
      intro z
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg z)) (hC z)
      exact le_add_of_nonneg_right (norm_nonneg _)
    have hosc : ∀ z w : ℂ, z ≠ 0 → ‖w‖ = ‖z‖ → ‖f z - f w‖ ≤ π * C := fun z w hz hw =>
      norm_sub_le_of_norm_mul_fderiv_le f (‖z‖ + 1) C (fun z' _ _ => ⟨hfd z', hfC z'⟩) z w hz
        (by linarith) hw
    set m : ℝ → ℝ := fun s => f ((Real.exp (2 * π * s) : ℝ) : ℂ) with hmdef
    have hmc : Continuous m := hfc.comp (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
    set L : ℝ := 2 / D.toReal with hL
    have hLpos : 0 < L := div_pos two_pos hT
    have hstep : ∃ s₀, ∀ s, s₀ ≤ s → m s + 1 ≤ m (s + L) := by
      by_contra hcon
      push_neg at hcon
      choose s hs hlt using fun k : ℕ => hcon k
      have hsR : Tendsto (fun k => Real.exp (2 * π * s k)) atTop atTop := by
        refine Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop (by positivity) ?_)
        exact tendsto_atTop_mono hs tendsto_natCast_atTop_atTop
      obtain ⟨φ, -, P, hPT, c, -, hinc⟩ := hY _ hsR
      have hlim := hinc L
      rw [hPT] at hlim
      have hval : D.toReal * L = 2 := by rw [hL]; field_simp
      rw [hval] at hlim
      have hle : ∀ j, aCoord H (u ((Real.exp (2 * π * L) * Real.exp (2 * π * s (φ j)) : ℝ) : ℂ)) -
          aCoord H (u ((Real.exp (2 * π * s (φ j)) : ℝ) : ℂ)) ≤ 1 := by
        intro j
        have h := hlt (φ j)
        have he : Real.exp (2 * π * L) * Real.exp (2 * π * s (φ j)) =
            Real.exp (2 * π * (s (φ j) + L)) := by rw [← Real.exp_add]; ring_nf
        rw [he]
        simp only [hmdef, hf] at h
        linarith
      have := le_of_tendsto' hlim hle
      norm_num at this
    obtain ⟨s₀, hs₀⟩ := hstep
    have hmtop := tendsto_atTop_of_add_le_step_aux m hmc L s₀ hLpos hs₀
    rw [Filter.tendsto_atTop]
    intro b
    obtain ⟨s₁, hs₁⟩ := (Filter.tendsto_atTop.1 hmtop) (b + π * C) |>.exists_forall_of_atTop
    have hev : ∀ᶠ z in cocompact ℂ, Real.exp (2 * π * s₁) ≤ ‖z‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hev] with z hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      exact absurd hz (not_le.2 (Real.exp_pos _))
    have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz0
    set s := Real.log ‖z‖ / (2 * π) with hsdef
    have hes : Real.exp (2 * π * s) = ‖z‖ := by
      rw [hsdef, mul_div_cancel₀ _ (by positivity), Real.exp_log hnz]
    have hss : s₁ ≤ s := by
      rw [hsdef, le_div_iff₀ (by positivity)]
      have := Real.log_le_log (Real.exp_pos _) hz
      rw [Real.log_exp] at this
      linarith
    have hms := hs₁ s hss
    have hnorm : ‖(((Real.exp (2 * π * s)) : ℝ) : ℂ)‖ = ‖z‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hes]
    have h := hosc z _ hz0 hnorm
    rw [Real.norm_eq_abs] at h
    have := (abs_le.1 h).1
    simp only [hmdef] at hms
    linarith
  · -- actions of the circles
    have hball : Tendsto (fun R : ℝ => dlambdaEnergy H (ball 0 R) u) atTop (𝓝 D) := by
      set μ := (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (dlambdaDensity H u z))
      have hμ : ∀ s : Set ℂ, MeasurableSet s → dlambdaEnergy H s u = μ s := fun s hs =>
        (withDensity_apply _ hs).symm
      have hU : (⋃ R : ℝ, ball (0 : ℂ) R) = Set.univ := by
        ext z
        simp only [Set.mem_iUnion, mem_ball_zero_iff, Set.mem_univ, iff_true]
        exact ⟨‖z‖ + 1, by linarith⟩
      have h := tendsto_measure_iUnion_atTop (μ := μ) (s := fun R : ℝ => ball (0 : ℂ) R)
        (fun a b hab => ball_subset_ball hab)
      rw [hU, ← hμ _ MeasurableSet.univ] at h
      refine h.congr fun R => ?_
      exact (hμ _ measurableSet_ball).symm
    have h2 := (ENNReal.tendsto_toReal hDtop).comp hball
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact (loopAction_ccwLoop_eq_dlambdaEnergy H hH J hJ u hu R hR).symm
  · intro R hR
    obtain ⟨φ, hφ, P, hPT, c, hconv, -⟩ := hY R hR
    exact ⟨φ, hφ, P, hPT, c, hconv⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (hnc : ∃ z₁ z₂, u z₁ ≠ u z₂) :
    0 < (dlambdaEnergy H Set.univ u).toReal ∧
      Tendsto (fun z => aCoord H (u z)) (cocompact ℂ) atTop ∧
      Tendsto (fun R => loopAction H u (ccwLoop R)) atTop
        (𝓝 (dlambdaEnergy H Set.univ u).toReal) ∧
      ∀ R : ℕ → ℝ, Tendsto R atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : ReebOrbit H,
        P.T = (dlambdaEnergy H Set.univ u).toReal ∧ ∃ c : ℝ,
          TendstoCInfty (fun k => loopInS H u (ccwLoop (R (φ k)))) (fun t => P.x (P.T * t + c)) :=
  plane_asymptotics_aux H hH J hJ u hu hnc
