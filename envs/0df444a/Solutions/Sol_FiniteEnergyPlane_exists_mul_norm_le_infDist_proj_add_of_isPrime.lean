-- Prove2me | solution 1 for FiniteEnergyPlane.exists_mul_norm_le_infDist_proj_add_of_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T17:31:30.241606+00:00
-- url     : https://prove2.me/submissions/6fb42812-28fc-4fba-b5cf-a448a378ce1b

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_isCompact_energySurface
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Theorems.Thm_FiniteEnergyPlane_exists_mul_abs_sub_le_norm_sub_of_isPrime



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `|ω₀(x, y)| ≤ C ‖x‖ ‖y‖`. -/
theorem iflt_abs_omega0_le {n : ℕ} (x y : V n) :
    |omega0 x y| ≤ (2 * (n + 1) : ℝ) * (‖x‖ * ‖y‖) := by
  unfold omega0 dot
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hj : ∀ k, |j0 x k| ≤ ‖x‖ := by
    intro k
    unfold j0
    split_ifs
    · rw [abs_neg]; exact norm_le_pi_norm x _
    · exact norm_le_pi_norm x _
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin (2 * (n + 1)))),
      |j0 x k * y k| ≤ ‖x‖ * ‖y‖ := by
    intro k _
    rw [abs_mul]
    exact mul_le_mul (hj k) (norm_le_pi_norm y k) (abs_nonneg _) (norm_nonneg _)
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans (le_of_eq ?_)
  simp

theorem iflt_liouville_add {n : ℕ} (x a b : V n) :
    liouville x (a + b) = liouville x a + liouville x b := by
  simp only [liouville, omega0, dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem iflt_liouville_sub {n : ℕ} (x a b : V n) :
    liouville x (a - b) = liouville x a - liouville x b := by
  simp only [liouville, omega0, dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

theorem iflt_liouville_smul {n : ℕ} (x a : V n) (c : ℝ) :
    liouville x (c • a) = c * liouville x a := by
  simp only [liouville, omega0, dot, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Uniform first-order expansion on a compact set. -/
theorem iflt_unif {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : E → G} {U K : Set E} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (hK : IsCompact K) (hKU : K ⊆ U) (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ∀ x ∈ K, ∀ h : E, ‖h‖ ≤ ρ → ‖F (x + h) - F x - fderiv ℝ F x h‖ ≤ η * ‖h‖ := by
  obtain ⟨r₀, hr₀, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  have hKc : IsCompact (cthickening r₀ K) := hK.cthickening
  have hc : ContinuousOn (fderiv ℝ F) U := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  have huc := hKc.uniformContinuousOn_of_continuous (hc.mono hsub)
  obtain ⟨ρ₁, hρ₁, hδ⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  refine ⟨min (r₀) (ρ₁ / 2), lt_min hr₀ (by positivity), fun x hx h hh => ?_⟩
  set s := closedBall x (min r₀ (ρ₁ / 2)) with hs
  have hsK : s ⊆ cthickening r₀ K := fun y hy =>
    mem_cthickening_of_dist_le y x r₀ K hx ((mem_closedBall.1 hy).trans (min_le_left _ _))
  have hxs : x ∈ s := mem_closedBall_self (le_of_lt (lt_min hr₀ (by positivity)))
  have hys : x + h ∈ s := by
    rw [hs, mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hh
  have hdiff : ∀ y ∈ s, HasFDerivWithinAt F (fderiv ℝ F y) s y := fun y hy => by
    have hyU := hsub (hsK hy)
    exact ((hF.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hbd : ∀ y ∈ s, ‖fderiv ℝ F y - fderiv ℝ F x‖ ≤ η := fun y hy => by
    have h1 : dist y x < ρ₁ := by
      have := (mem_closedBall.1 hy).trans (min_le_right _ _)
      linarith
    have h2 := hδ y (hsK hy) x (hsK hxs) h1
    rw [dist_eq_norm] at h2
    exact h2.le
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' hdiff hbd (convex_closedBall x _)
    hxs hys
  simpa only [add_sub_cancel_left] using this

/-- On `S`: `scaleToS = 1`, so `proj x = x`. -/
theorem iflt_proj_of_mem {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : H x = 1) : proj H x = x := by
  have hx0 : x ≠ 0 := by
    intro h0
    have := hH.2.2 x hx
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨r, -, huniq⟩ := hH.2.1 x hx0
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • x) = 1 := ⟨1, one_pos, by rwa [one_smul]⟩
  have h1 : scaleToS H x = 1 := by
    unfold scaleToS
    rw [dif_pos hex]
    have h2 := Classical.choose_spec hex
    rw [huniq _ h2, huniq 1 ⟨one_pos, by rwa [one_smul]⟩]
  rw [proj, h1, one_smul]

/-- The derivative of `proj` at a point of `S` is the identity on `ker dH`. -/
theorem iflt_fderiv_proj {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (x h : V n) (hx : H x = 1)
    (hdH : fderiv ℝ H x h = 0) : fderiv ℝ (proj H) x h = h := by
  obtain ⟨-, hps, has, hrep, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hx0 : x ≠ 0 := by
    intro h0
    have := hH.2.2 x hx
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  have hU : IsOpen {y : V n | y ≠ 0} := isOpen_ne
  have hUx : {y : V n | y ≠ 0} ∈ 𝓝 x := hU.mem_nhds hx0
  have hp : HasFDerivAt (proj H) (fderiv ℝ (proj H) x) x :=
    ((hps.contDiffAt hUx).differentiableAt (by simp)).hasFDerivAt
  have ha : HasFDerivAt (aCoord H) (fderiv ℝ (aCoord H) x) x :=
    ((has.contDiffAt hUx).differentiableAt (by simp)).hasFDerivAt
  have hpx : proj H x = x := iflt_proj_of_mem H hH x hx
  have hax : Real.exp (2 * aCoord H x) = 1 := by
    have h1 := (hrep x hx0).2
    rw [hpx] at h1
    have h2 : (Real.exp (2 * aCoord H x) - 1) • x = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · linarith
    · exact absurd h3 hx0
  -- derivative of `H ∘ proj`
  have hHd : HasFDerivAt H (fderiv ℝ H x) x :=
    (hH.1.differentiable (by simp) x).hasFDerivAt
  have hc1 : HasFDerivAt (fun y => H (proj H y)) ((fderiv ℝ H x).comp (fderiv ℝ (proj H) x)) x := by
    have hHd' : HasFDerivAt H (fderiv ℝ H x) (proj H x) := by rw [hpx]; exact hHd
    exact hHd'.comp x hp
  have hev1 : (fun y => H (proj H y)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [hUx] with y hy using (hrep y hy).1
  have hc1' : HasFDerivAt (fun y => H (proj H y)) (0 : V n →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq hev1
  have hz := hc1.unique hc1'
  have hdp : fderiv ℝ H x (fderiv ℝ (proj H) x h) = 0 := by
    have := congrArg (fun L : V n →L[ℝ] ℝ => L h) hz
    simpa using this
  -- derivative of `y = exp(2a) proj`
  have he : HasFDerivAt (fun y => Real.exp (2 * aCoord H y))
      (Real.exp (2 * aCoord H x) • ((2 : ℝ) • fderiv ℝ (aCoord H) x)) x :=
    (ha.const_mul 2).exp
  have hc2 := he.smul hp
  have hev2 : (fun y => Real.exp (2 * aCoord H y) • proj H y) =ᶠ[𝓝 x] id := by
    filter_upwards [hUx] with y hy using (hrep y hy).2.symm
  have hc2' : HasFDerivAt (fun y => Real.exp (2 * aCoord H y) • proj H y)
      (ContinuousLinearMap.id ℝ (V n)) x := (hasFDerivAt_id x).congr_of_eventuallyEq hev2
  have hz2 := hc2.unique hc2'
  have hval := congrArg (fun L : V n →L[ℝ] V n => L h) hz2
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, hax, hpx, one_smul,
    smul_eq_mul, one_mul] at hval
  -- `h = Dproj h + (2 Da h) x`
  have happly := congrArg (fderiv ℝ H x) hval
  rw [map_add, map_smul, hdp, hdH, zero_add, smul_eq_mul] at happly
  have hD := hH.2.2 x hx
  have h2a : 2 * fderiv ℝ (aCoord H) x h = 0 := by
    rcases mul_eq_zero.1 happly with h3 | h3
    · exact h3
    · exact absurd h3 hD.ne'
  rw [h2a, zero_smul, add_zero] at hval
  exact hval

/-- The real-number absorption step. -/
theorem iflt_real (Λ η M D s h : ℝ) (hΛ : 0 ≤ Λ) (hη : 0 ≤ η) (hM : 0 ≤ M) (hD : 0 ≤ D) (hs : 0 ≤ s)
    (hh : 0 ≤ h) (hη1 : η ≤ 1) (h1 : Λ * η ≤ 1 / 2)
    (h2 : η * (2 * Λ * (M + 1) + 1) ≤ 1 / 2)
    (h3 : s ≤ Λ * D + Λ * (η * s) + Λ * (η * h)) (h4 : h ≤ D + (M + η) * s + η * h) :
    h ≤ (2 * Λ * (M + 1) + 1) * D * 2 := by
  have a1 : Λ * (η * s) ≤ 1 / 2 * s := by
    have := mul_le_mul_of_nonneg_right h1 hs
    calc Λ * (η * s) = Λ * η * s := by ring
      _ ≤ _ := this
  have a2 : s ≤ 2 * Λ * (D + η * h) := by
    have e : 2 * Λ * (D + η * h) = 2 * (Λ * D + Λ * (η * h)) := by ring
    rw [e]
    linarith
  have a3 : (M + η) * s ≤ (M + 1) * (2 * Λ * (D + η * h)) :=
    mul_le_mul (by linarith) a2 hs (by positivity)
  have a4 : η * (2 * Λ * (M + 1) + 1) * h ≤ 1 / 2 * h := mul_le_mul_of_nonneg_right h2 hh
  have e : (2 * Λ * (M + 1) + 1) * D * 2 =
      2 * (D + (M + 1) * (2 * Λ * D)) := by ring
  have e2 : (M + 1) * (2 * Λ * (D + η * h)) + η * h =
      (M + 1) * (2 * Λ * D) + η * (2 * Λ * (M + 1) + 1) * h := by ring
  rw [e]
  linarith

theorem exists_mul_norm_le_infDist_proj_add_of_isPrime_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) (hP : P.IsPrime) :
    ∃ c > 0, ∃ ρ > 0, ∀ (τ : ℝ) (h : V n), IsInXi H (P.x τ) h → ‖h‖ ≤ ρ →
      c * ‖h‖ ≤ infDist (proj H (P.x τ + h)) (Set.range P.x) := by
  obtain ⟨-, hps, -, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hSc := isCompact_energySurface H hH
  have hS0 : energySurface H ⊆ {y : V n | y ≠ 0} := by
    intro x hx h0
    have := hH.2.2 x hx
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  have hxper : Function.Periodic P.x P.T := P.periodic
  have hxc : ContDiff ℝ ∞ P.x := P.contDiff_x H hH
  obtain ⟨c₀, hc₀, hsep⟩ := exists_mul_abs_sub_le_norm_sub_of_isPrime H hH P hP
  -- bounds
  obtain ⟨M₀', hM₀'⟩ := hSc.exists_bound_of_continuousOn
    (continuous_norm.continuousOn (s := energySurface H))
  have hM₀ : ∀ τ, ‖P.x τ‖ ≤ M₀' := fun τ => by simpa using hM₀' _ (P.mem τ)
  have hM₀0 : 0 ≤ M₀' := (norm_nonneg _).trans (hM₀ 0)
  have hdper : Function.Periodic (deriv P.x) P.T := by
    intro τ
    rw [(P.hasDerivAt (τ + P.T)).deriv, (P.hasDerivAt τ).deriv, P.periodic]
  obtain ⟨M₁', hM₁'⟩ := isBounded_iff_forall_norm_le.1
    (hdper.compact_of_continuous P.T_pos.ne' (hxc.continuous_deriv (by simp))).isBounded
  have hM₁ : ∀ τ, ‖reeb H (P.x τ)‖ ≤ M₁' := fun τ => by
    rw [← (P.hasDerivAt τ).deriv]
    exact hM₁' _ ⟨τ, rfl⟩
  have hM₁0 : 0 ≤ M₁' := (norm_nonneg _).trans (hM₁ 0)
  set Λ : ℝ := (n + 1 : ℝ) * 2 / 2 * M₀' with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hL : ∀ τ (v : V n), |liouville (P.x τ) v| ≤ Λ * ‖v‖ := by
    intro τ v
    unfold liouville
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num)]
    have h1 := iflt_abs_omega0_le (P.x τ) v
    have h2 : ‖P.x τ‖ * ‖v‖ ≤ M₀' * ‖v‖ := mul_le_mul_of_nonneg_right (hM₀ τ) (norm_nonneg v)
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * (n + 1))
    calc _ ≤ _ := h1
      _ ≤ _ := h3
      _ = _ := by rw [hΛ]; ring
  set Q : ℝ := 2 * Λ * (M₁' + 1) + 1 with hQ
  have hQ1 : 1 ≤ Q := by
    have : 0 ≤ 2 * Λ * (M₁' + 1) := by positivity
    linarith
  set η : ℝ := 1 / (2 * (Q + 1) + 2 * Λ) with hηdef
  have hden : 0 < 2 * (Q + 1) + 2 * Λ := by linarith
  have hη : 0 < η := by positivity
  have hηe : η * (2 * (Q + 1) + 2 * Λ) = 1 := by
    rw [hηdef]; field_simp
  have hη1 : η ≤ 1 := by nlinarith [mul_nonneg hη.le hΛ0]
  have hηΛ : Λ * η ≤ 1 / 2 := by nlinarith [mul_nonneg hη.le hΛ0, mul_pos hη (by linarith : 0 < Q)]
  have hηQ : η * Q ≤ 1 / 2 := by nlinarith [mul_nonneg hη.le hΛ0]
  -- first-order expansions
  obtain ⟨ρ₁, hρ₁, hexp⟩ := iflt_unif isOpen_ne (hps.of_le (by norm_cast)) hSc hS0 η hη
  obtain ⟨σ₀, hσ₀, hexpx⟩ := iflt_unif (U := Set.univ) isOpen_univ
    ((hxc.of_le (by norm_cast)).contDiffOn) (isCompact_Icc (a := (0 : ℝ)) (b := P.T))
    (Set.subset_univ _) η hη
  -- the expansion of `x` at every `τ`
  have hxexp : ∀ τ σ : ℝ, |σ| ≤ σ₀ →
      ‖P.x (τ + σ) - P.x τ - σ • reeb H (P.x τ)‖ ≤ η * |σ| := by
    intro τ σ hσ
    set k : ℤ := ⌊τ / P.T⌋ with hk
    set τ₀ := τ - k * P.T with hτ₀
    have hT := P.T_pos
    have hk1 : (k : ℝ) ≤ τ / P.T := Int.floor_le _
    have hk2 : τ / P.T < k + 1 := Int.lt_floor_add_one _
    have hτ₀m : τ₀ ∈ Set.Icc 0 P.T := by
      rw [le_div_iff₀ hT] at hk1
      rw [div_lt_iff₀ hT] at hk2
      constructor <;> simp only [hτ₀] <;> nlinarith
    have h1 := hexpx τ₀ hτ₀m σ (by simpa using hσ)
    have hxe : ∀ a : ℝ, P.x (a - k * P.T) = P.x a := fun a => hxper.sub_int_mul_eq k
    have e1 : P.x τ₀ = P.x τ := hxe τ
    have e2 : P.x (τ₀ + σ) = P.x (τ + σ) := by
      rw [show τ₀ + σ = (τ + σ) - k * P.T by simp only [hτ₀]; ring, hxe]
    have e3 : fderiv ℝ P.x τ₀ σ = σ • reeb H (P.x τ) := by
      rw [(P.hasDerivAt τ₀).hasFDerivAt.fderiv, e1]
      simp
    rw [e1, e2, e3, Real.norm_eq_abs] at h1
    exact h1
  refine ⟨1 / (2 * Q), by positivity, min ρ₁ (c₀ * σ₀ / 4), lt_min hρ₁ (by positivity), ?_⟩
  intro τ h hh hρ
  have hne : (Set.range P.x).Nonempty := Set.range_nonempty _
  rw [le_infDist hne]
  rintro _ ⟨τ', rfl⟩
  have hhn := norm_nonneg h
  set y := proj H (P.x τ + h) with hy
  -- reduce `τ'` to `|σ| ≤ T / 2`
  set k : ℤ := round ((τ' - τ) / P.T) with hk
  set τ'' := τ' - k * P.T with hτ''
  have hxτ'' : P.x τ'' = P.x τ' := hxper.sub_int_mul_eq k
  rw [← hxτ'']
  set σ := τ'' - τ with hσdef
  have hτσ : τ'' = τ + σ := by rw [hσdef]; ring
  have hσT : |σ| ≤ P.T / 2 := by
    have h1 := abs_sub_round ((τ' - τ) / P.T)
    have hT := P.T_pos
    have h2 : σ = ((τ' - τ) / P.T - k) * P.T := by
      rw [hσdef, hτ'']; field_simp; ring
    rw [h2, abs_mul, abs_of_pos hT]
    have := mul_le_mul_of_nonneg_right h1 hT.le
    linarith
  set D := dist y (P.x τ'') with hD
  have hD' : D = ‖y - P.x τ''‖ := dist_eq_norm _ _
  have hD0 : 0 ≤ D := dist_nonneg
  -- the expansion of `proj`
  have hmem : H (P.x τ) = 1 := P.mem τ
  have hpx := iflt_proj_of_mem H hH _ hmem
  have hdp := iflt_fderiv_proj H hH J hJ _ h hmem hh.2
  have he1 := hexp (P.x τ) (P.mem τ) h (hρ.trans (min_le_left _ _))
  rw [hpx, hdp] at he1
  set e1 := y - P.x τ - h with he1def
  have hyx : ‖y - P.x τ‖ ≤ 2 * ‖h‖ := by
    have : y - P.x τ = e1 + h := by rw [he1def]; abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  have hsmall : ‖h‖ ≤ c₀ * σ₀ / 4 := hρ.trans (min_le_right _ _)
  have hQp : 0 < 2 * Q := by linarith
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hQp]
  by_cases hnear : |σ| ≤ σ₀
  · have he2 := hxexp τ σ hnear
    rw [← hτσ] at he2
    set R := reeb H (P.x τ) with hR
    set e2 := P.x τ'' - P.x τ - σ • R with he2def
    have hdecomp : h = (y - P.x τ'') + σ • R + e2 - e1 := by
      rw [he2def, he1def]; abel
    have hspec := reeb_spec H hH (P.x τ) (P.mem τ)
    have hLR : liouville (P.x τ) R = 1 := hspec.2.1
    have hLh : liouville (P.x τ) h = 0 := hh.1
    have hLeq : σ = -liouville (P.x τ) (y - P.x τ'') - liouville (P.x τ) e2 +
        liouville (P.x τ) e1 := by
      have h1 := congrArg (liouville (P.x τ)) hdecomp
      rw [iflt_liouville_sub, iflt_liouville_add, iflt_liouville_add, iflt_liouville_smul, hLR,
        hLh] at h1
      linarith
    have ha := hL τ (y - P.x τ'')
    have hb := hL τ e2
    have hc := hL τ e1
    rw [← hD'] at ha
    have hσ0 := abs_nonneg σ
    have hb' : |liouville (P.x τ) e2| ≤ Λ * (η * |σ|) :=
      hb.trans (mul_le_mul_of_nonneg_left he2 hΛ0)
    have hc' : |liouville (P.x τ) e1| ≤ Λ * (η * ‖h‖) :=
      hc.trans (mul_le_mul_of_nonneg_left he1 hΛ0)
    have hσbd : |σ| ≤ Λ * D + Λ * (η * |σ|) + Λ * (η * ‖h‖) := by
      have A := abs_le.1 ha
      have B := abs_le.1 hb'
      have C := abs_le.1 hc'
      rw [abs_le]
      constructor <;> linarith [A.1, A.2, B.1, B.2, C.1, C.2]
    have hhbd : ‖h‖ ≤ D + (M₁' + η) * |σ| + η * ‖h‖ := by
      have h1 : ‖h‖ ≤ ‖y - P.x τ''‖ + ‖σ • R‖ + ‖e2‖ + ‖e1‖ := by
        conv_lhs => rw [hdecomp]
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      have h2 : ‖σ • R‖ ≤ |σ| * M₁' := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hM₁ τ) hσ0
      rw [← hD'] at h1
      have h3 : (M₁' + η) * |σ| = |σ| * M₁' + η * |σ| := by ring
      linarith
    have := iflt_real Λ η M₁' D |σ| ‖h‖ hΛ0 hη.le hM₁0 hD0 hσ0 hhn hη1 hηΛ hηQ hσbd hhbd
    linarith
  · push_neg at hnear
    have h1 : c₀ * |τ - τ''| ≤ ‖P.x τ - P.x τ''‖ := hsep τ τ'' (by
      rw [abs_sub_comm]; exact hσT)
    rw [abs_sub_comm] at h1
    have h2 : ‖P.x τ - P.x τ''‖ ≤ D + 2 * ‖h‖ := by
      have : P.x τ - P.x τ'' = (y - P.x τ'') - (y - P.x τ) := by abel
      rw [this, hD']
      exact (norm_sub_le _ _).trans (by linarith)
    have h3 : c₀ * σ₀ ≤ c₀ * |σ| := mul_le_mul_of_nonneg_left hnear.le hc₀.le
    have h4 : ‖h‖ ≤ D := by
      have : c₀ * σ₀ / 2 ≤ D := by
        have : |τ'' - τ| = |σ| := rfl
        linarith
      linarith
    have h5 : 0 ≤ D * (2 * Q - 1) := mul_nonneg hD0 (by linarith)
    linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) (hP : P.IsPrime) :
    ∃ c > 0, ∃ ρ > 0, ∀ (τ : ℝ) (h : V n), IsInXi H (P.x τ) h → ‖h‖ ≤ ρ →
      c * ‖h‖ ≤ infDist (proj H (P.x τ + h)) (Set.range P.x) :=
  exists_mul_norm_le_infDist_proj_add_of_isPrime_aux H hH J hJ P hP
