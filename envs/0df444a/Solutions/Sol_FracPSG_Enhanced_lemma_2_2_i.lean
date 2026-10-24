-- Prove2me | solution 1 for FracPSG.Enhanced.lemma_2_2_i
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T03:45:30.955981+00:00
-- url     : https://prove2.me/submissions/e04111ae-1fd9-46cc-9792-91f6a4d0ffa1

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_FracPSG_Enhanced_Basic

open Filter Topology
open scoped InnerProductSpace

namespace P1ad1

open NonconvexSplitting.Shared FracPSG.Enhanced

/-- Values of `addInd h S`: either `⊤` or a real number (never `⊥`). -/
theorem addInd_real {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {h : EuclideanSpace ℝ (Fin N) → EReal} (hprop : IsProperFn h)
    {z : EuclideanSpace ℝ (Fin N)} (hz : FracPSG.Subseq.addInd h S z ≠ ⊤) :
    z ∈ S ∧ h z = FracPSG.Subseq.addInd h S z ∧
      FracPSG.Subseq.addInd h S z = (((FracPSG.Subseq.addInd h S z).toReal : ℝ) : EReal) := by
  by_cases hzS : z ∈ S
  · have e : FracPSG.Subseq.addInd h S z = h z := by unfold FracPSG.Subseq.addInd; simp [hzS]
    rw [e] at hz ⊢
    exact ⟨hzS, rfl, (EReal.coe_toReal hz (hprop.1 z)).symm⟩
  · exfalso; apply hz; unfold FracPSG.Subseq.addInd; simp [hzS]

/-- A regular subgradient of `h + ι_S` (weakly convex with modulus `ρ`) at `z` satisfies the global
weak-convexity subgradient inequality. -/
theorem reg_ineq {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {h : EuclideanSpace ℝ (Fin N) → EReal} {ρ : ℝ} (hprop : IsProperFn h)
    (hwc : IsWeaklyConvexOnE S h ρ)
    {z v y : EuclideanSpace ℝ (Fin N)}
    (hv : IsRegularSubgrad (FracPSG.Subseq.addInd h S) z v)
    (hy : FracPSG.Subseq.addInd h S y ≠ ⊤) :
    (FracPSG.Subseq.addInd h S z).toReal + ⟪v, y - z⟫_ℝ - ρ / 2 * ‖y - z‖ ^ 2
      ≤ (FracPSG.Subseq.addInd h S y).toReal := by
  obtain ⟨hρ, hconv⟩ := hwc
  obtain ⟨hzS, hhz, hzr⟩ := addInd_real hprop hv.1
  obtain ⟨hyS, hhy, hyr⟩ := addInd_real hprop hy
  set a := (FracPSG.Subseq.addInd h S z).toReal with ha
  set b := (FracPSG.Subseq.addInd h S y).toReal with hb
  have hza : h z = (a : EReal) := hhz.trans hzr
  have hyb : h y = (b : EReal) := hhy.trans hyr
  obtain ⟨d, hd⟩ : ∃ d, y - z = d := ⟨_, rfl⟩
  have hyd : y = z + d := by rw [← hd]; abel
  rw [hd]
  rw [hyd] at hyS hyb
  apply le_of_forall_pos_le_add
  intro η hη
  set ε : ℝ := η / (‖d‖ + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hεd : ε * ‖d‖ ≤ η := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg d]
  have hline : Tendsto (fun s : ℝ => z + s • d) (𝓝[>] (0:ℝ)) (𝓝 z) := by
    have : Continuous (fun s : ℝ => z + s • d) := by fun_prop
    have h0 := this.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have h1 := hline.eventually (hv.2 ε hε0)
  have h2 : ∀ᶠ s in 𝓝[>] (0:ℝ), s ∈ Set.Ioc (0:ℝ) 1 := Ioc_mem_nhdsGT zero_lt_one
  obtain ⟨s, hs1, hs2⟩ := (h1.and h2).exists
  obtain ⟨hs0, hs1'⟩ := hs2
  -- epigraph points
  have hpz : ((z, a + ρ / 2 * ‖z‖ ^ 2) : EuclideanSpace ℝ (Fin N) × ℝ) ∈
      {q : EuclideanSpace ℝ (Fin N) × ℝ | q.1 ∈ S ∧ h q.1 + ((ρ / 2 * ‖q.1‖ ^ 2 : ℝ) : EReal) ≤ (q.2 : EReal)} := by
    refine ⟨hzS, ?_⟩
    show h z + ((ρ / 2 * ‖z‖ ^ 2 : ℝ) : EReal) ≤ ((a + ρ / 2 * ‖z‖ ^ 2 : ℝ) : EReal)
    rw [hza, ← EReal.coe_add]
  have hpy : ((z + d, b + ρ / 2 * ‖z + d‖ ^ 2) : EuclideanSpace ℝ (Fin N) × ℝ) ∈
      {q : EuclideanSpace ℝ (Fin N) × ℝ | q.1 ∈ S ∧ h q.1 + ((ρ / 2 * ‖q.1‖ ^ 2 : ℝ) : EReal) ≤ (q.2 : EReal)} := by
    refine ⟨hyS, ?_⟩
    show h (z + d) + ((ρ / 2 * ‖z + d‖ ^ 2 : ℝ) : EReal) ≤ ((b + ρ / 2 * ‖z + d‖ ^ 2 : ℝ) : EReal)
    rw [hyb, ← EReal.coe_add]
  have hc := hconv hpz hpy (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring : (1 - s) + s = 1)
  have hwS : (1 - s) • z + s • (z + d) ∈ S := hc.1
  have hwle : h ((1 - s) • z + s • (z + d)) + ((ρ / 2 * ‖(1 - s) • z + s • (z + d)‖ ^ 2 : ℝ) : EReal)
      ≤ (((1 - s) * (a + ρ / 2 * ‖z‖ ^ 2) + s * (b + ρ / 2 * ‖z + d‖ ^ 2) : ℝ) : EReal) := hc.2
  have hmem : (1 - s) • z + s • (z + d) = z + s • d := by module
  rw [hmem] at hwS hwle
  set w := z + s • d with hw
  set c : ℝ := (1 - s) * (a + ρ / 2 * ‖z‖ ^ 2) + s * (b + ρ / 2 * ‖z + d‖ ^ 2) with hc'
  -- h w is real
  have hwtop : h w ≠ ⊤ := by
    intro htop
    rw [htop, EReal.top_add_coe] at hwle
    exact (EReal.coe_ne_top c) (top_le_iff.mp hwle)
  set r := (h w).toReal with hr
  have hwr : h w = (r : EReal) := (EReal.coe_toReal hwtop (hprop.1 w)).symm
  have hwle' : r + ρ / 2 * ‖w‖ ^ 2 ≤ c := by
    rw [hwr, ← EReal.coe_add] at hwle
    exact_mod_cast hwle
  have hreg : a + (s * ⟪v, d⟫_ℝ - ε * (s * ‖d‖)) ≤ r := by
    have hh := hs1
    have hwz : w - z = s • d := by rw [hw]; abel
    rw [hwz, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at hh
    have hFw : FracPSG.Subseq.addInd h S w = h w := by
      unfold FracPSG.Subseq.addInd; simp [hwS]
    rw [hFw, hwr, hzr] at hh
    rw [← EReal.coe_add] at hh
    exact EReal.coe_le_coe_iff.mp hh
  have hn1 : ‖w‖ ^ 2 = ‖z‖ ^ 2 + 2 * (s * ⟪z, d⟫_ℝ) + s ^ 2 * ‖d‖ ^ 2 := by
    rw [hw, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]; ring
  have hn2 : ‖z + d‖ ^ 2 = ‖z‖ ^ 2 + 2 * ⟪z, d⟫_ℝ + ‖d‖ ^ 2 := by
    rw [norm_add_sq_real]
  rw [hn1] at hwle'
  rw [hc', hn2] at hwle'
  have key : s * (⟪v, d⟫_ℝ - ε * ‖d‖ - (b - a) - ρ / 2 * (1 - s) * ‖d‖ ^ 2) ≤ 0 := by
    nlinarith
  have key2 : ⟪v, d⟫_ℝ - ε * ‖d‖ - (b - a) - ρ / 2 * (1 - s) * ‖d‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have := mul_pos hs0 hcon
    linarith
  have hb' : ρ / 2 * (1 - s) * ‖d‖ ^ 2 ≤ ρ / 2 * ‖d‖ ^ 2 := by
    have : 0 ≤ ρ / 2 * s * ‖d‖ ^ 2 := by positivity
    nlinarith
  linarith

end P1ad1

open NonconvexSplitting.Shared FracPSG.Enhanced in
theorem solution {N : ℕ} {S : Set (EuclideanSpace ℝ (Fin N))}
    {h : EuclideanSpace ℝ (Fin N) → EReal}
    (hSne : S.Nonempty) (hS : IsClosed S) (hSconv : Convex ℝ S)
    (hprop : IsProperFn h) (hlsc : LowerSemicontinuous h)
    (hwc : ∃ ρ : ℝ, IsWeaklyConvexOnE S h ρ) (x : EuclideanSpace ℝ (Fin N)) :
    IsClosed (LimitingSubdiff (FracPSG.Subseq.addInd h S) x) ∧ Convex ℝ (LimitingSubdiff (FracPSG.Subseq.addInd h S) x) := by
  obtain ⟨ρ, hρwc⟩ := hwc
  set F := FracPSG.Subseq.addInd h S with hF
  by_cases hxt : F x = ⊤
  · have hempty : LimitingSubdiff F x = ∅ := by
      ext v; simp only [Set.mem_empty_iff_false, iff_false]
      intro hv; exact hv.1 hxt
    rw [hempty]; exact ⟨isClosed_empty, convex_empty⟩
  set a := (F x).toReal with ha
  have hxr : F x = (a : EReal) := (P1ad1.addInd_real hprop hxt).2.2
  set A : Set (EuclideanSpace ℝ (Fin N)) :=
    ⋂ y ∈ {y | F y ≠ ⊤}, {v | a + ⟪v, y - x⟫_ℝ - ρ / 2 * ‖y - x‖ ^ 2 ≤ (F y).toReal} with hA
  have hEq : LimitingSubdiff F x = A := by
    ext v
    constructor
    · rintro ⟨-, xs, vs, hxs, hfx, hvs, hreg⟩
      simp only [hA, Set.mem_iInter, Set.mem_setOf_eq]
      intro y hy
      have hlimF : Tendsto (fun t => (F (xs t)).toReal) atTop (𝓝 a) := by
        have hb : F x ≠ ⊥ := by rw [hxr]; exact EReal.coe_ne_bot a
        exact (EReal.tendsto_toReal hxt hb).comp hfx
      have hlim : Tendsto (fun t => (F (xs t)).toReal + ⟪vs t, y - xs t⟫_ℝ - ρ / 2 * ‖y - xs t‖ ^ 2)
          atTop (𝓝 (a + ⟪v, y - x⟫_ℝ - ρ / 2 * ‖y - x‖ ^ 2)) := by
        have h2 : Tendsto (fun t => ⟪vs t, y - xs t⟫_ℝ) atTop (𝓝 ⟪v, y - x⟫_ℝ) :=
          Filter.Tendsto.inner (𝕜 := ℝ) hvs (tendsto_const_nhds.sub hxs)
        have h3 : Tendsto (fun t => ‖y - xs t‖) atTop (𝓝 ‖y - x‖) :=
          (tendsto_const_nhds.sub hxs).norm
        exact (hlimF.add h2).sub ((h3.pow 2).const_mul (ρ / 2))
      refine le_of_tendsto hlim ?_
      exact Eventually.of_forall fun t => P1ad1.reg_ineq hprop hρwc (hreg t) hy
    · intro hv
      simp only [hA, Set.mem_iInter, Set.mem_setOf_eq] at hv
      refine ⟨hxt, fun _ => x, fun _ => v, tendsto_const_nhds, tendsto_const_nhds,
        tendsto_const_nhds, fun _ => ⟨hxt, ?_⟩⟩
      intro ε hε
      have hδ : (0:ℝ) < 2 * ε / (ρ + 1) := by
        have := hρwc.1; positivity
      filter_upwards [Metric.ball_mem_nhds x hδ] with z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      by_cases hzt : F z = ⊤
      · rw [hzt]; exact le_top
      have hzr : F z = ((F z).toReal : EReal) := (P1ad1.addInd_real hprop hzt).2.2
      have hineq := hv z hzt
      have hρ0 := hρwc.1
      have hq : ρ / 2 * ‖z - x‖ ^ 2 ≤ ε * ‖z - x‖ := by
        have hn := norm_nonneg (z - x)
        have h1 : ρ * ‖z - x‖ ≤ 2 * ε := by
          have : ‖z - x‖ * (ρ + 1) < 2 * ε := by
            rwa [lt_div_iff₀ (by linarith)] at hz
          nlinarith
        nlinarith
      rw [hzr, hxr, ← EReal.coe_add]
      exact_mod_cast (by linarith : a + (⟪v, z - x⟫_ℝ - ε * ‖z - x‖) ≤ (F z).toReal)
  rw [hEq]
  constructor
  · refine isClosed_biInter fun y _ => ?_
    exact isClosed_le (by fun_prop) continuous_const
  · refine convex_iInter₂ fun y _ => ?_
    intro v1 hv1 v2 hv2 θ1 θ2 hθ1 hθ2 hθ
    simp only [Set.mem_setOf_eq] at hv1 hv2 ⊢
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    have e1 := mul_le_mul_of_nonneg_left hv1 hθ1
    have e2 := mul_le_mul_of_nonneg_left hv2 hθ2
    set T := (F y).toReal
    set c := ρ / 2 * ‖y - x‖ ^ 2
    calc a + (θ1 * ⟪v1, y - x⟫_ℝ + θ2 * ⟪v2, y - x⟫_ℝ) - c
        = θ1 * (a + ⟪v1, y - x⟫_ℝ - c) + θ2 * (a + ⟪v2, y - x⟫_ℝ - c) := by
          linear_combination (c - a) * hθ
      _ ≤ θ1 * T + θ2 * T := add_le_add e1 e2
      _ = T := by rw [← add_mul, hθ, one_mul]
