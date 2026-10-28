-- Prove2me | solution 1 for FiniteEnergyPlane.exists_bubbling_plane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T16:27:22.270007+00:00
-- url     : https://prove2.me/submissions/699bc95d-982c-468b-be8e-76fab3f978f7

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_exists_blowup_points
import Theorems.Thm_FiniteEnergyPlane_exists_closedBall_subset_of_away
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Theorems.Thm_FiniteEnergyPlane_exists_plane_of_gradNorm_le
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Bubbling-off analysis: the rescaled limit plane. -/
theorem exists_bubbling_plane_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ) (U : ℕ → Set ℂ)
    (hUo : ∀ k, IsOpen (U k)) (hUmono : Monotone U) (hUsub : ∀ k, U k ⊆ (↑Γ)ᶜ)
    (hUunion : ⋃ k, U k = (↑Γ)ᶜ) (u : ℕ → ℂ → V n)
    (hu : ∀ k, IsFiniteEnergyCurve H J (U k) (u k)) (C : ℝ)
    (hC : ∀ k, energy H (U k) (u k) ≤ ENNReal.ofReal C) (z : ℕ → ℂ) (hz : ∀ k, z k ∈ U k)
    (hblow : Tendsto (fun k => gradNorm H (u k) (z k)) atTop atTop)
    (haway : ∃ δ : ℝ, 0 < δ ∧ ∀ k, ∀ γ ∈ Γ, δ ≤ ‖z k - γ‖)
    (hbdd : (∃ R : ℝ, ∀ k, ‖z k‖ ≤ R) ∨ ∃ m : ℕ, ∃ R : ℝ, {w : ℂ | R < ‖w‖} ⊆ U m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z' : ℕ → ℂ, ∃ R : ℕ → ℝ, ∃ v : ℂ → V n,
      Tendsto (fun j => ‖z (φ j) - z' j‖) atTop (𝓝 0) ∧ (∀ j, 0 < R j) ∧
      Tendsto R atTop atTop ∧ IsFiniteEnergyCurve H J Set.univ v ∧ (∃ z₁ z₂, v z₁ ≠ v z₂) ∧
      energy H Set.univ v ≤ ENNReal.ofReal C ∧
      ∀ ρ : ℝ, 0 < ρ → (∀ᶠ j in atTop, ball (z' j) (ρ / R j) ⊆ U (φ j)) ∧
        dlambdaEnergy H (ball 0 ρ) v ≤
          liminf (fun j => dlambdaEnergy H (ball (z' j) (ρ / R j)) (u (φ j))) atTop := by
  classical
  obtain ⟨-, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨ρ₀, hρ₀, m, hm⟩ :=
    exists_closedBall_subset_of_away Γ U hUo hUmono hUunion z haway hbdd
  obtain ⟨m', hm'⟩ := eventually_atTop.1 (hblow.eventually (eventually_gt_atTop (0 : ℝ)))
  set N := max m m' with hN
  -- shifted data
  set uu : ℕ → ℂ → V n := fun k => u (k + N) with huu
  set UU : ℕ → Set ℂ := fun k => U (k + N) with hUU
  set zz : ℕ → ℂ := fun k => z (k + N) with hzz
  set g : ℕ → ℂ → ℝ := fun k => gradNorm H (uu k) with hg
  have hgc : ∀ k, ContinuousOn (g k) (UU k) := by
    intro k
    obtain ⟨hsm, hne, -, -⟩ := hu (k + N)
    have ho := hUo (k + N)
    have ha : ContDiffOn ℝ ∞ (fun z => aCoord H (u (k + N) z)) (U (k + N)) :=
      haCs.comp hsm (fun z hz => hne z hz)
    have hp : ContDiffOn ℝ ∞ (fun z => proj H (u (k + N) z)) (U (k + N)) :=
      hprojs.comp hsm (fun z hz => hne z hz)
    exact (ha.continuousOn_fderiv_of_isOpen ho (by simp)).norm.add
      (hp.continuousOn_fderiv_of_isOpen ho (by simp)).norm
  have hg0 : ∀ k w, 0 ≤ g k w := fun k w => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hgpos : ∀ k, 0 < g k (zz k) := fun k => hm' (k + N) (by omega)
  have hgblow : Tendsto (fun k => g k (zz k)) atTop atTop :=
    hblow.comp (tendsto_add_atTop_nat N)
  have hball : ∀ k, closedBall (zz k) ρ₀ ⊆ UU k := fun k => hm (k + N) (by omega)
  obtain ⟨ζ, ε, hε, hε0, hεR, hzζ, hRpos, hsub, hdbl⟩ :=
    exists_blowup_points g UU zz ρ₀ hρ₀ hball hgc hg0 hgpos hgblow
  set R : ℕ → ℝ := fun k => g k (ζ k) with hR
  set a : ℕ → ℝ := fun k => aCoord H (uu k (ζ k)) with ha
  set c : ℕ → ℝ := fun k => Real.exp (-2 * a k) with hc
  have hcpos : ∀ k, 0 < c k := fun k => Real.exp_pos _
  set v : ℕ → ℂ → V n := fun k w => c k • uu k (ζ k + (R k)⁻¹ • w) with hv
  set ρ : ℕ → ℝ := fun k => ε k * R k with hρ
  have hD := fun k => rescale_isFiniteEnergyCurve H hH J hJ (UU k) (hUo (k + N)) (uu k)
    (hu (k + N)) (ζ k) (R k)⁻¹ (inv_pos.2 (hRpos k)) (c k) (hcpos k)
  -- points of `ball 0 (ρ k)` land in `closedBall (ζ k) (ε k)`
  have hmem : ∀ k, ∀ w ∈ ball (0 : ℂ) (ρ k), ζ k + (R k)⁻¹ • w ∈ ball (ζ k) (ε k) := by
    intro k w hw
    rw [mem_ball_zero_iff] at hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (hRpos k)), inv_mul_lt_iff₀ (hRpos k)]
    simpa [hρ, mul_comm] using hw
  have hballU : ∀ k, ball (ζ k) (ε k) ⊆ UU k := fun k => ball_subset_closedBall.trans (hsub k)
  have hpre : ∀ k, ball (0 : ℂ) (ρ k) ⊆ {w | ζ k + (R k)⁻¹ • w ∈ UU k} :=
    fun k w hw => hballU k (hmem k w hw)
  -- the rescaled curves
  have hvfe : ∀ k, IsFiniteEnergyCurve H J (ball 0 (ρ k)) (v k) := by
    intro k
    obtain ⟨⟨h1, h2, h3, h4⟩, -, -, -⟩ := hD k
    refine ⟨h1.mono (hpre k), fun w hw => h2 w (hpre k hw), fun w hw => h3 w (hpre k hw),
      lt_of_le_of_lt ?_ h4⟩
    exact iSup₂_mono fun φ _ => lintegral_mono_set (hpre k)
  have hvC : ∀ k, energy H (ball 0 (ρ k)) (v k) ≤ ENNReal.ofReal C := by
    intro k
    obtain ⟨-, -, -, hE⟩ := hD k
    calc energy H (ball 0 (ρ k)) (v k)
        ≤ energy H {w | ζ k + (R k)⁻¹ • w ∈ UU k} (v k) :=
          iSup₂_mono fun φ _ => lintegral_mono_set (hpre k)
      _ = energy H (UU k) (uu k) := (hE (UU k) subset_rfl (hUo (k + N)).measurableSet).1
      _ ≤ ENNReal.ofReal C := hC (k + N)
  have hvgrad : ∀ k, ∀ w ∈ ball (0 : ℂ) (ρ k), gradNorm H (v k) w ≤ 2 := by
    intro k w hw
    obtain ⟨-, -, hG, -⟩ := hD k
    rw [hG w (hpre k hw)]
    have h := hdbl k _ (ball_subset_closedBall (hmem k w hw))
    have hi := inv_pos.2 (hRpos k)
    calc (R k)⁻¹ * gradNorm H (uu k) (ζ k + (R k)⁻¹ • w) ≤ (R k)⁻¹ * (2 * R k) :=
          mul_le_mul_of_nonneg_left h hi.le
      _ = 2 := by rw [mul_left_comm, inv_mul_cancel₀ (hRpos k).ne', mul_one]
  have hεR' : Tendsto ρ atTop atTop := hεR
  have h0pre : ∀ k, ζ k + (R k)⁻¹ • (0 : ℂ) ∈ UU k := by
    intro k
    rw [smul_zero, add_zero]
    exact hsub k (mem_closedBall_self (hε k).le)
  have hva0 : ∀ k, aCoord H (v k 0) = 0 := by
    intro k
    obtain ⟨-, hA, -, -⟩ := hD k
    show aCoord H (c k • uu k (ζ k + (R k)⁻¹ • (0 : ℂ))) = 0
    rw [hA 0 (h0pre k)]
    simp only [smul_zero, add_zero, hc, Real.log_exp, ha]
    ring
  have hvg0 : ∀ k, gradNorm H (v k) 0 = 1 := by
    intro k
    obtain ⟨-, -, hG, -⟩ := hD k
    rw [hG 0 (h0pre k)]
    simp only [smul_zero, add_zero]
    exact inv_mul_cancel₀ (hRpos k).ne'
  obtain ⟨φ, hφ, w, hw, hnc, hEw, hlim⟩ := exists_plane_of_gradNorm_le H hH J hJ v ρ hεR' hvfe C
    hvC hvgrad hva0 hvg0
  have hRtop : Tendsto R atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hεR
    filter_upwards [hε0.eventually (ge_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with k hk
    have := hRpos k
    simp only [hρ]
    nlinarith [hε k]
  have hφt := hφ.tendsto_atTop
  -- small balls around `ζ k` of radius `r / R k` lie in `ball (ζ k) (ε k)` once `r < ρ k`
  have hsmall : ∀ k, ∀ r : ℝ, r < ρ k → ball (ζ k) (r / R k) ⊆ UU k := by
    intro k r hr
    refine (ball_subset_ball ?_).trans (hballU k)
    rw [div_le_iff₀ (hRpos _)]
    simp only [hρ] at hr
    linarith
  refine ⟨fun j => φ j + N, fun i j hij => by
      have := hφ hij
      simp only
      omega,
    fun j => ζ (φ j), fun j => R (φ j), w, hzζ.comp hφt, fun j => hRpos _, hRtop.comp hφt,
    hw, hnc, hEw, fun r hr => ?_⟩
  have hev : ∀ᶠ j in atTop, r < ρ (φ j) := (hεR.comp hφt).eventually (eventually_gt_atTop r)
  refine ⟨hev.mono fun j hj => hsmall (φ j) r hj, ?_⟩
  refine (hlim r).trans (le_of_eq (liminf_congr ?_))
  filter_upwards [hev] with j hj
  set k := φ j with hk
  obtain ⟨-, -, -, hE⟩ := hD k
  have h := (hE _ (hsmall k r hj) measurableSet_ball).2
  have hset : {x : ℂ | ζ k + (R k)⁻¹ • x ∈ ball (ζ k) (r / R k)} = ball 0 r := by
    ext x
    simp only [Set.mem_setOf_eq, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, sub_zero]
    rw [abs_inv, abs_of_pos (hRpos k), inv_mul_lt_iff₀ (hRpos k), mul_div_cancel₀ _ (hRpos k).ne']
  rw [hset] at h
  exact h

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ) (U : ℕ → Set ℂ)
    (hUo : ∀ k, IsOpen (U k)) (hUmono : Monotone U) (hUsub : ∀ k, U k ⊆ (↑Γ)ᶜ)
    (hUunion : ⋃ k, U k = (↑Γ)ᶜ) (u : ℕ → ℂ → V n)
    (hu : ∀ k, IsFiniteEnergyCurve H J (U k) (u k)) (C : ℝ)
    (hC : ∀ k, energy H (U k) (u k) ≤ ENNReal.ofReal C) (z : ℕ → ℂ) (hz : ∀ k, z k ∈ U k)
    (hblow : Tendsto (fun k => gradNorm H (u k) (z k)) atTop atTop)
    (haway : ∃ δ : ℝ, 0 < δ ∧ ∀ k, ∀ γ ∈ Γ, δ ≤ ‖z k - γ‖)
    (hbdd : (∃ R : ℝ, ∀ k, ‖z k‖ ≤ R) ∨ ∃ m : ℕ, ∃ R : ℝ, {w : ℂ | R < ‖w‖} ⊆ U m)  :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z' : ℕ → ℂ, ∃ R : ℕ → ℝ, ∃ v : ℂ → V n,
      Tendsto (fun j => ‖z (φ j) - z' j‖) atTop (𝓝 0) ∧ (∀ j, 0 < R j) ∧
      Tendsto R atTop atTop ∧ IsFiniteEnergyCurve H J Set.univ v ∧ (∃ z₁ z₂, v z₁ ≠ v z₂) ∧
      energy H Set.univ v ≤ ENNReal.ofReal C ∧
      ∀ ρ : ℝ, 0 < ρ → (∀ᶠ j in atTop, ball (z' j) (ρ / R j) ⊆ U (φ j)) ∧
        dlambdaEnergy H (ball 0 ρ) v ≤
          liminf (fun j => dlambdaEnergy H (ball (z' j) (ρ / R j)) (u (φ j))) atTop :=
  exists_bubbling_plane_aux H hH J hJ Γ U hUo hUmono hUsub hUunion u hu C hC z hz hblow haway hbdd
