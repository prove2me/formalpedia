-- Prove2me | solution 1 for GKP1998.massive_string_state_dimension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:41:28.147867+00:00
-- url     : https://prove2.me/submissions/afa3038f-d84a-4e38-bab0-4cc6fe2b0217

import Theorems.Thm_GKP1998_flux_factor_nonanalytic
import Theorems.Thm_GKP1998_mass_radius_relation
import Theorems.Thm_GKP1998_scaling_dimension_asymptotic

open Filter Topology Asymptotics GKP1998

private lemma twoPointExpansion (N ν R : ℝ) (hν : 0 < ν) (hR : 0 < R)
    (A : ℝ → ℝ) (hA : AnalyticAt ℝ A 0)
    (he : (fun k : ℝ => fluxFactor ν k R - A (k ^ 2)
        - (-2 * ν * Real.Gamma (1 - ν) / Real.Gamma (1 + ν)
          * (k * R / 2) ^ (2 * ν) / R ^ 4))
      =o[𝓝[>] (0 : ℝ)] (fun k : ℝ => k ^ (2 * ν))) :
    ∃ B : ℝ → ℝ, AnalyticAt ℝ B 0 ∧
      (fun k : ℝ => twoPointFunction N ν k R - B (k ^ 2)
        - (-(N ^ 2 / (8 * Real.pi ^ 2)) * Real.Gamma (1 - ν)
          / Real.Gamma ν * (k * R / 2) ^ (2 * ν) / R ^ 4))
      =o[𝓝[>] (0 : ℝ)] (fun k : ℝ => k ^ (2 * ν)) := by
  refine ⟨fun x => N ^ 2 / (16 * Real.pi ^ 2) * A x,
    analyticAt_const.mul hA, ?_⟩
  have hGamma : Real.Gamma (1 + ν) = ν * Real.Gamma ν := by
    rw [add_comm, Real.Gamma_add_one hν.ne']
  have hGn : Real.Gamma ν ≠ 0 := (Real.Gamma_pos_of_pos hν).ne'
  convert he.const_mul_left (N ^ 2 / (16 * Real.pi ^ 2)) using 1
  all_goals try rfl
  funext k
  dsimp [twoPointFunction]
  rw [hGamma]
  field_simp [hν.ne', hGn, Real.pi_ne_zero, hR.ne']
  ring

/-- Goal (Eqs. (41)–(46)): for a scalar string state at level `n ≥ 1` with `m² = 4n/α'`,
`R⁴ = 2 N g_YM² α'²` and non-integer Bessel order `ν = √(4 + (mR)²)`:
(i) the two-point function of the dual operator is an analytic function of `k²` plus the
leading non-analytic term `−N²/(8π²) · Γ(1−ν)/Γ(ν) · (kR/2)^{2ν} · R⁻⁴` (Eq. (44)), up to
`o(k^{2ν})` as `k → 0⁺`;
(ii) the dimension of the dual operator is `Δ = 2 + ν = 2 + √(4 + 4 n g_YM √(2N))`
(Eqs. (41), (45));
(iii) for fixed `n ≥ 1` and `N > 0`, `Δ ∼ 2 (n g_YM √(2N))^{1/2}` as `g_YM → ∞` (Eq. (46)). -/
theorem solution (n : ℕ) (hn : 1 ≤ n) (N gYM α' m R : ℝ)
    (hN : 0 < N) (hg : 0 < gYM) (hα : 0 < α') (hm : 0 < m) (hR : 0 < R)
    (hmass : m ^ 2 = 4 * n / α') (hradius : R ^ 4 = 2 * N * gYM ^ 2 * α' ^ 2)
    (hνZ : ∀ j : ℤ, massiveOrder m R ≠ j) :
    (∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧
      (fun k : ℝ => twoPointFunction N (massiveOrder m R) k R - A (k ^ 2)
          - (-(N ^ 2 / (8 * Real.pi ^ 2)) * Real.Gamma (1 - massiveOrder m R)
              / Real.Gamma (massiveOrder m R) * (k * R / 2) ^ (2 * massiveOrder m R) / R ^ 4))
        =o[𝓝[>] (0 : ℝ)] (fun k : ℝ => k ^ (2 * massiveOrder m R))) ∧
    scalingDimension (massiveOrder m R) = 2 + Real.sqrt (4 + 4 * n * gYM * Real.sqrt (2 * N)) ∧
    Tendsto (fun g : ℝ =>
        scalingDimension (Real.sqrt (4 + 4 * n * g * Real.sqrt (2 * N)))
          / (2 * Real.sqrt (n * g * Real.sqrt (2 * N))))
      atTop (𝓝 1) := by
  have hν : 0 < massiveOrder m R := by
    unfold massiveOrder
    exact Real.sqrt_pos.2 (by nlinarith [sq_nonneg (m * R)])
  obtain ⟨A, hA, he⟩ := flux_factor_nonanalytic (massiveOrder m R) R hν hνZ hR
  refine ⟨twoPointExpansion N (massiveOrder m R) R hν hR A hA he, ?_,
    scaling_dimension_asymptotic n hn N hN⟩
  unfold scalingDimension massiveOrder
  rw [mass_radius_relation n N gYM α' m R hN hg hα hm hR hmass hradius]
