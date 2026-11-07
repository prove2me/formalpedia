-- Prove2me | solution 1 for FiniteEnergyPlane.isFastPlane_of_infDist_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T17:34:41.723677+00:00
-- url     : https://prove2.me/submissions/74a7f8cb-6e88-4999-ad5d-b7878497cc9f

import Definitions.Def_FiniteEnergyPlane_CylClose
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_energy_univ_lt_top_of_norm_fderiv_mul_I_le
import Theorems.Thm_FiniteEnergyPlane_exists_norm_fderiv_mul_I_le_of_hasExpAsymptoticsEnd
import Theorems.Thm_FiniteEnergyPlane_exists_mul_norm_le_infDist_proj_add_of_isPrime
import Theorems.Thm_FiniteEnergyPlane_exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_asymptotic_eigenvector
import Theorems.Thm_FiniteEnergyPlane_exists_hasWindInfAt_of_hasAsymptoticEigenvector
import Theorems.Thm_FiniteEnergyPlane_hasEigenWind_of_isAsymptoticEigen
import Theorems.Thm_FiniteEnergyPlane_one_le_windInf_of_plane
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_iff_hasWindInfAt_one
import Theorems.Thm_FiniteEnergyPlane_isPrime_of_isFastPlane_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_isFiniteEnergyCurve_comp_inv
import Theorems.Thm_FiniteEnergyPlane_exists_dlambdaDensity_ne_zero_of_isOpen
import Theorems.Thm_FiniteEnergyPlane_exists_ne_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem ifl_cylEnd_inv (s t : ℝ) : (cylEnd s t)⁻¹ = cylInf s t := by
  unfold cylEnd cylInf cwLoop ccwLoop
  rw [zero_add, mul_inv, ← Complex.ofReal_inv, ← Real.exp_neg, neg_neg, ← Complex.exp_neg]
  congr 2
  ring

theorem ifl_endA_inv {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) :
    endA H (fun z => u z⁻¹) cylEnd = endA H u cylInf := by
  funext p
  simp only [endA, ifl_cylEnd_inv]

theorem ifl_endW_inv {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) :
    endW H (fun z => u z⁻¹) cylEnd = endW H u cylInf := by
  funext p
  simp only [endW, ifl_cylEnd_inv]

theorem ifl_cylEndAt_zero : cylEndAt 0 = cylEnd := rfl

theorem ifl_norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem ifl_tendsto_of_tendstoZeroCInfty {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : TendstoZeroCInfty f) (t : ℝ) :
    Tendsto (fun s : ℝ => f (s, t)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨s₁, hs₁⟩ := hf.2 0 (ε / 2) (by positivity)
  refine ⟨s₁, fun s hs => ?_⟩
  have := hs₁ s hs t
  rw [norm_iteratedFDeriv_zero] at this
  rw [dist_zero_right]
  linarith

/-- The rate bounds the asymptotic eigenvalue: an orbit distance `≤ C e^{δ s}` along the end forces
`μ ≤ δ`. -/
theorem ifl_le_of_rate (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (f : ℂ → V 1) (e : ℝ → ℝ → ℂ)
    (μ : ℝ) (v : ℝ → V 1) (hv : HasAsymptoticEigenvector H J f e P 1 μ v)
    (δ C : ℝ) (hrate : ∀ s t : ℝ, infDist (endW H f e (s, t)) (Set.range P.x) ≤
      C * Real.exp (δ * s)) : μ ≤ δ := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c₀, hc₀, ρ, hρ, htube⟩ := exists_mul_norm_le_infDist_proj_add_of_isPrime H hH J hJ P hP
  obtain ⟨hE, hμ, c, τ, r, s₀, hτ, hr, hrep⟩ := hv
  have hμ0 : μ < 0 := by linarith
  obtain ⟨t₀, ht₀⟩ := hE.2.1
  have hTne : P.T ≠ 0 := P.T_pos.ne'
  set t₁ : ℝ := t₀ - c / P.T with ht₁
  have hτt : Tendsto (fun s : ℝ => τ (s, t₁) / P.T) atTop (𝓝 t₀) := by
    have h := (ifl_tendsto_of_tendstoZeroCInfty hτ t₁).div_const P.T
    have h2 := h.add_const t₀
    rw [zero_div, zero_add] at h2
    refine h2.congr fun s => ?_
    simp only [ht₁]
    field_simp
    ring
  have hvc : Continuous v := hE.1.1.continuous
  have hsum : Tendsto (fun s : ℝ => v (τ (s, t₁) / P.T) + r (s, t₁)) atTop (𝓝 (v t₀ + 0)) :=
    (hvc.tendsto t₀ |>.comp hτt).add (ifl_tendsto_of_tendstoZeroCInfty hr t₁)
  rw [add_zero] at hsum
  have hm : 0 < ‖v t₀‖ := norm_pos_iff.2 ht₀
  set m := ‖v t₀‖ with hmdef
  have hn := hsum.norm
  have hlo : ∀ᶠ s : ℝ in atTop, m / 2 ≤ ‖v (τ (s, t₁) / P.T) + r (s, t₁)‖ :=
    hn.eventually (le_mem_nhds (by linarith))
  have hhi : ∀ᶠ s : ℝ in atTop, ‖v (τ (s, t₁) / P.T) + r (s, t₁)‖ ≤ 2 * m :=
    hn.eventually (ge_mem_nhds (by linarith))
  have hexp0 : Tendsto (fun s : ℝ => Real.exp (μ * s) * (2 * m)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => μ * s) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg hμ0
    simpa using (Real.tendsto_exp_atBot.comp h1).mul_const (2 * m)
  have hsmall : ∀ᶠ s : ℝ in atTop, Real.exp (μ * s) * (2 * m) ≤ ρ :=
    hexp0.eventually (ge_mem_nhds hρ)
  -- the growth contradiction
  have hgrow : Tendsto (fun s : ℝ => Real.exp ((μ - δ) * s)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))
  have hbig : ∀ᶠ s : ℝ in atTop, 2 * |C| / (c₀ * m) + 1 ≤ Real.exp ((μ - δ) * s) :=
    hgrow.eventually_ge_atTop _
  obtain ⟨s, hs₀, hs₁, hs₂, hs₃, hs₄⟩ :=
    ((eventually_ge_atTop s₀).and (hlo.and (hhi.and (hsmall.and hbig)))).exists
  obtain ⟨hin, heq⟩ := hrep s hs₀ t₁
  simp only [one_mul] at hin heq
  set h := Real.exp (μ * s) • (v (τ (s, t₁) / P.T) + r (s, t₁)) with hh
  have hnorm : ‖h‖ = Real.exp (μ * s) * ‖v (τ (s, t₁) / P.T) + r (s, t₁)‖ := by
    rw [hh, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have he := Real.exp_pos (μ * s)
  have hhρ : ‖h‖ ≤ ρ := by
    rw [hnorm]
    exact le_trans (mul_le_mul_of_nonneg_left hs₂ he.le) hs₃
  have h1 := htube _ h hin hhρ
  rw [← heq] at h1
  have h2 := hrate s t₁
  have hlow : c₀ * (Real.exp (μ * s) * (m / 2)) ≤ c₀ * ‖h‖ := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs₁ he.le) hc₀.le
  have h3 : c₀ * (Real.exp (μ * s) * (m / 2)) ≤ |C| * Real.exp (δ * s) := by
    refine hlow.trans (h1.trans (h2.trans ?_))
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
  have hsplit : Real.exp (μ * s) = Real.exp ((μ - δ) * s) * Real.exp (δ * s) := by
    rw [← Real.exp_add]; congr 1; ring
  have hd := Real.exp_pos (δ * s)
  rw [hsplit] at h3
  have h4 : c₀ * (Real.exp ((μ - δ) * s) * (m / 2)) ≤ |C| := by
    have : c₀ * (Real.exp ((μ - δ) * s) * (m / 2)) * Real.exp (δ * s) ≤ |C| * Real.exp (δ * s) := by
      calc _ = c₀ * (Real.exp ((μ - δ) * s) * Real.exp (δ * s) * (m / 2)) := by ring
        _ ≤ _ := h3
    exact le_of_mul_le_mul_right this hd
  have hcm : 0 < c₀ * m := by positivity
  have h5 : Real.exp ((μ - δ) * s) ≤ 2 * |C| / (c₀ * m) := by
    rw [le_div_iff₀ hcm]
    nlinarith
  linarith

/-- Glue for `isFastPlane_of_infDist_le`. -/
theorem isFastPlane_of_infDist_le_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (δ : ℝ) (hδ : δ < 0)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k))
    (ε : ℝ) (f : ℂ → V 1) (hf : ContDiff ℝ ∞ f) (hf0 : ∀ z, f z ≠ 0)
    (hfJ : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ f)
    (hfP : IsNondegenerateEnd H f cylInf P 1) (hclose : IsCylCloseTo H ε f u)
    (C : ℝ) (hrate : ∀ z, infDist (proj H (f z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (δ / (2 * π))) :
    IsFastPlane H J f := by
  have hP : P.IsPrime := isPrime_of_isFastPlane_of_isNondegenerateEnd H hH J hJ u hu P huP
  obtain ⟨-, hprojs, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hfun : ∀ g : ℂ → V 1, ContDiff ℝ ∞ g → (∀ z, g z ≠ 0) →
      ContDiff ℝ ∞ (fun z => proj H (g z)) := fun g hg hg0 =>
    contDiffOn_univ.1 (hprojs.comp (hg.contDiffOn (s := Set.univ)) (fun z _ => hg0 z))
  have huC : ContDiff ℝ ∞ u := contDiffOn_univ.1 hu.1.1
  have hu0 : ∀ z, u z ≠ 0 := fun z => hu.1.2.1 z (Set.mem_univ z)
  have hwu := hfun u huC hu0
  have hwf := hfun f hf hf0
  -- finite energy of `f`
  obtain ⟨b, hb, hexp⟩ :=
    exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd H hH J hJ u hu.1 P huP
  obtain ⟨K, hK⟩ := exists_norm_fderiv_mul_I_le_of_hasExpAsymptoticsEnd H hH u
    (hwu.of_le (by norm_cast)) P b hb hexp
  have hKf : ∀ z, ‖fderiv ℝ (fun z => proj H (f z)) z (z * Complex.I)‖ ≤ K + ε := by
    intro z
    have hcl := (hclose z).2.2
    have hzn : ‖z * Complex.I‖ = ‖z‖ := by simp
    have hle : ‖(fderiv ℝ (fun w => proj H (f w)) z - fderiv ℝ (fun w => proj H (u w)) z)
        (z * Complex.I)‖ ≤ ε := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [hzn]
      set A := ‖fderiv ℝ (fun w => proj H (f w)) z - fderiv ℝ (fun w => proj H (u w)) z‖
      set B := ‖fderiv ℝ (fun w => aCoord H (f w)) z - fderiv ℝ (fun w => aCoord H (u w)) z‖
      have hA : 0 ≤ A := norm_nonneg _
      have hB : 0 ≤ B := norm_nonneg _
      have hz : 0 ≤ ‖z‖ := norm_nonneg _
      nlinarith
    have h := hK z
    rw [ContinuousLinearMap.sub_apply] at hle
    calc ‖fderiv ℝ (fun z => proj H (f z)) z (z * Complex.I)‖
        = ‖(fderiv ℝ (fun w => proj H (f w)) z (z * Complex.I) -
            fderiv ℝ (fun w => proj H (u w)) z (z * Complex.I)) +
            fderiv ℝ (fun w => proj H (u w)) z (z * Complex.I)‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (by linarith)
  have hfin : IsFiniteEnergyCurve H J Set.univ f :=
    ⟨hf.contDiffOn, fun z _ => hf0 z, hfJ,
      energy_univ_lt_top_of_norm_fderiv_mul_I_le H hH J hJ f hf hf0 hfJ (K + ε) hKf⟩
  -- the inverted curve near `0`
  have hnc : ∃ z₁ z₂, f z₁ ≠ f z₂ := exists_ne_of_isNondegenerateEnd H f cylInf P one_ne_zero hfP
  obtain ⟨hũ, hdens⟩ := isFiniteEnergyCurve_comp_inv H hH J hJ f hfin
  have hndũ : IsNondegenerateEnd H (fun z => f z⁻¹) cylEnd P 1 := by
    unfold IsNondegenerateEnd
    rw [ifl_endA_inv, ifl_endW_inv]
    exact hfP
  have hneũ : ∀ ρ > 0, ∃ z ∈ ball (0 : ℂ) ρ \ {0}, dlambdaDensity H (fun z => f z⁻¹) z ≠ 0 := by
    intro ρ hρ
    obtain ⟨w, hw, hdw⟩ := exists_dlambdaDensity_ne_zero_of_isOpen H hH J hJ f hfin hnc
      {w : ℂ | ρ⁻¹ < ‖w‖} (isOpen_lt continuous_const continuous_norm)
      ⟨((ρ⁻¹ + 1 : ℝ) : ℂ), by
        show ρ⁻¹ < ‖((ρ⁻¹ + 1 : ℝ) : ℂ)‖
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith⟩
    have hw' : ρ⁻¹ < ‖w‖ := hw
    have hwpos : 0 < ‖w‖ := lt_trans (inv_pos.2 hρ) hw'
    have hw0 : w ≠ 0 := norm_pos_iff.1 hwpos
    refine ⟨w⁻¹, ⟨?_, inv_ne_zero hw0⟩, ?_⟩
    · rw [mem_ball_zero_iff, norm_inv]
      exact (inv_lt_comm₀ hρ hwpos).1 hw'
    · rw [hdens _ (inv_ne_zero hw0), inv_inv]
      refine mul_ne_zero (inv_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 (inv_ne_zero hw0)))) hdw
  obtain ⟨-, hev⟩ := asymptotic_eigenvector H hH J hJ (fun z => f z⁻¹) hũ P 1 (Or.inl rfl) hndũ
  obtain ⟨μ, v, hv⟩ := hev hneũ
  have hv' : HasAsymptoticEigenvector H J (fun z => f z⁻¹) (cylEndAt 0) P 1 μ v := hv
  obtain ⟨k, hkv, hkW⟩ := exists_hasWindInfAt_of_hasAsymptoticEigenvector H hH J hJ 0 1 one_pos
    (fun z => f z⁻¹) hũ P 1 (Or.inl rfl) μ v hv'
  have hWI : HasWindInfAt H f cylInf 1 k := by
    have h := hkW
    unfold HasWindInfAt at h ⊢
    rwa [ifl_cylEndAt_zero, ifl_endW_inv] at h
  have hEW : HasEigenWind J P μ k :=
    hasEigenWind_of_isAsymptoticEigen H hH J hJ P μ v k hv.1 hkv
  -- the rate
  have hμδ : μ ≤ δ := by
    refine ifl_le_of_rate H hH J hJ P hP (fun z => f z⁻¹) cylEnd μ v hv δ |C| ?_
    intro s t
    rw [ifl_endW_inv]
    simp only [endW]
    refine (hrate _).trans ?_
    have hpos : 0 < Real.exp (2 * π * s) := Real.exp_pos _
    have hexp : (0 : ℝ) ≤ 2 * π := by positivity
    have h1 : (1 + ‖cylInf s t‖) ^ (δ / (2 * π)) ≤ Real.exp (δ * s) := by
      rw [ifl_norm_cylInf]
      have hle : Real.exp (2 * π * s) ≤ 1 + Real.exp (2 * π * s) := by linarith
      refine (Real.rpow_le_rpow_of_nonpos hpos hle
        (div_nonpos_of_nonpos_of_nonneg hδ.le hexp)).trans (le_of_eq ?_)
      rw [← Real.exp_mul]
      congr 1
      field_simp
    have h2 : 0 ≤ (1 + ‖cylInf s t‖) ^ (δ / (2 * π)) := by positivity
    calc C * (1 + ‖cylInf s t‖) ^ (δ / (2 * π))
        ≤ |C| * (1 + ‖cylInf s t‖) ^ (δ / (2 * π)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
  have hk1 : k ≤ 1 := by
    rcases hwin μ k hEW with h | h
    · exact h.2
    · exact absurd h.1 (not_lt.2 hμδ)
  -- `wind_∞ ≥ 1`
  obtain ⟨k', hk', hWI'⟩ := one_le_windInf_of_plane H hH J hJ f hfin P hfP
  have hkk' : k = k' := by
    obtain ⟨s₀, hs₀⟩ := hWI
    obtain ⟨s₁, hs₁⟩ := hWI'
    exact hasLoopWind_unique (hs₀ _ (le_max_left s₀ s₁)) (hs₁ _ (le_max_right s₀ s₁))
  have hk : k = 1 := by omega
  rw [hk] at hWI
  exact (isFastPlane_iff_hasWindInfAt_one H hH J hJ f hfin P hP hfP).2 hWI

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (δ : ℝ) (hδ : δ < 0)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasEigenWind J P μ k → (μ < δ ∧ k ≤ 1) ∨ (δ < μ ∧ 2 ≤ k))
    (ε : ℝ) (f : ℂ → V 1) (hf : ContDiff ℝ ∞ f) (hf0 : ∀ z, f z ≠ 0)
    (hfJ : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ f)
    (hfP : IsNondegenerateEnd H f cylInf P 1) (hclose : IsCylCloseTo H ε f u)
    (C : ℝ) (hrate : ∀ z, infDist (proj H (f z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (δ / (2 * π))) :
    IsFastPlane H J f :=
  isFastPlane_of_infDist_le_aux H hH J hJ P u hu huP δ hδ hwin ε f hf hf0 hfJ hfP hclose C hrate
