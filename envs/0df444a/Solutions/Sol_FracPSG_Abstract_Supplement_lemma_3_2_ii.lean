-- Prove2me | solution 1 for FracPSG.Abstract.Supplement.lemma_3_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:11.375582+00:00
-- url     : https://prove2.me/submissions/25f1af11-3843-4abb-871c-e131084edbbb

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_FracPSG_Subseq_Basic
import Definitions.Def_FracPSG_Abstract_Supplement_Stationary

open Filter Topology
open scoped InnerProductSpace

open FracPSG
open FracPSG.Abstract
open FracPSG.Abstract.Supplement

open NonconvexSplitting.Shared FracPSG.Subseq

/-- Lemma 3.2(ii) (Boţ–Dao–Li, arXiv:2003.04124v2, p. 7). Let `f` be proper and lower
semicontinuous, `g` lower semicontinuous, `S` and `C` nonempty closed sets with `C ∩ S ≠ ∅`,
`xbar ∈ C ∩ S`, `g(xbar) > 0` and `f = f₁ + ι_C`, where (a) `f₁` is Lipschitz around `xbar` and
`xbar ∈ int(C ∩ S)`, or (b) `f₁` is Lipschitz around `xbar`, `f₁` and `C ∩ S` are regular at `xbar`
and `g > 0` around `xbar`, or (c) `f₁` is strictly differentiable at `xbar` and `g > 0` around
`xbar`. If `g` is strictly differentiable at `xbar`, then (12)
`∂_L(f/g + ι_S)(xbar) = (g(xbar) ∂_L(f + ι_S)(xbar) − f(xbar) ∇g(xbar)) / g(xbar)²`,
and `xbar` is a stationary point of (P) iff it is a lifted stationary point of (P). -/
theorem solution {N : ℕ} {S C : Set (EuclideanSpace ℝ (Fin N))}
    {f f₁ : EuclideanSpace ℝ (Fin N) → EReal} {g : EuclideanSpace ℝ (Fin N) → ℝ}
    {xbar : EuclideanSpace ℝ (Fin N)}
    (hf : IsProperFn f) (hflsc : LowerSemicontinuous f) (hglsc : LowerSemicontinuous g)
    (hS : IsClosed S) (hSne : S.Nonempty) (hC : IsClosed C) (hCne : C.Nonempty)
    (hCS : (C ∩ S).Nonempty) (hxC : xbar ∈ C) (hxS : xbar ∈ S) (hgx : 0 < g xbar)
    (hfeq : f = addInd f₁ C)
    (hcase : (IsLipschitzAround f₁ xbar ∧ xbar ∈ interior (C ∩ S)) ∨
      (IsLipschitzAround f₁ xbar ∧ IsRegularAt f₁ xbar ∧ IsSetRegularAt (C ∩ S) xbar ∧
        ∀ᶠ y in 𝓝 xbar, 0 < g y) ∨
      (IsStrictlyDiffAt f₁ xbar ∧ ∀ᶠ y in 𝓝 xbar, 0 < g y))
    (hgdiff : ∃ L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ, HasStrictFDerivAt g L xbar) :
    LimitingSubdiff (addInd (quotient f g) S) xbar =
      (fun u => (g xbar ^ 2)⁻¹ • (g xbar • u - (f xbar).toReal • gradient g xbar)) ''
        LimitingSubdiff (addInd f S) xbar ∧
    (IsStationary f g S xbar ↔ IsLiftedStationary f g S xbar) := by
      set_option maxHeartbeats 4000000 in
      focus
        classical
        have SD : ∀ (m : EuclideanSpace ℝ (Fin N) → ℝ) (L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ)
            (x0 : EuclideanSpace ℝ (Fin N)), HasStrictFDerivAt m L x0 → ∀ η > 0, ∃ r > 0,
              ∀ y z, dist y x0 < r → dist z x0 < r → |m z - m y - L (z - y)| ≤ η * ‖z - y‖ := by
          intro m L x0 hm η hη
          have h1 := hasStrictFDerivAt_iff_isLittleO.mp hm
          rw [Asymptotics.isLittleO_iff] at h1
          obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (h1 hη)
          refine ⟨r, hr, fun y z hy hz => ?_⟩
          have := hball (y := (z, y)) (by rw [Prod.dist_eq]; exact max_lt hz hy)
          simpa [Real.norm_eq_abs] using this
        have CR : ∀ (ψ : EuclideanSpace ℝ (Fin N) → EReal) (x0 w : EuclideanSpace ℝ (Fin N)),
            ψ x0 ≠ ⊤ → ψ x0 ≠ ⊥ →
            (∀ δ > 0, ∃ y w', dist y x0 < δ ∧ ψ y ≠ ⊤ ∧ ψ y ≠ ⊥ ∧
              |(ψ y).toReal - (ψ x0).toReal| < δ ∧ dist w' w < δ ∧ IsRegularSubgrad ψ y w') →
            w ∈ LimitingSubdiff ψ x0 := by
          intro ψ x0 w htop hbot h
          choose ys ws hy hyt hyb hval hw hreg using
            fun t : ℕ => h (1 / ((t : ℝ) + 1)) (by positivity)
          refine ⟨htop, ys, ws, ?_, ?_, ?_, hreg⟩
          · rw [tendsto_iff_dist_tendsto_zero]
            exact squeeze_zero (fun t => dist_nonneg) (fun t => (hy t).le)
              tendsto_one_div_add_atTop_nhds_zero_nat
          · have hr : Tendsto (fun t => (ψ (ys t)).toReal) atTop (𝓝 (ψ x0).toReal) := by
              rw [tendsto_iff_dist_tendsto_zero]
              exact squeeze_zero (fun t => dist_nonneg)
                (fun t => by rw [Real.dist_eq]; exact (hval t).le)
                tendsto_one_div_add_atTop_nhds_zero_nat
            have hc := (continuous_coe_real_ereal.tendsto _).comp hr
            have e : ψ x0 = ((ψ x0).toReal : EReal) := (EReal.coe_toReal htop hbot).symm
            rw [e]
            exact hc.congr (fun t => EReal.coe_toReal (hyt t) (hyb t))
          · rw [tendsto_iff_dist_tendsto_zero]
            exact squeeze_zero (fun t => dist_nonneg) (fun t => (hw t).le)
              tendsto_one_div_add_atTop_nhds_zero_nat
        have EX : ∀ (ψ : EuclideanSpace ℝ (Fin N) → EReal) (x w : EuclideanSpace ℝ (Fin N)) (ε ρ : ℝ),
            0 < ε → 0 < ρ → LowerSemicontinuousOn ψ (Metric.closedBall x ρ) → ψ x ≠ ⊤ → ψ x ≠ ⊥ →
            (∀ z ∈ Metric.closedBall x ρ, ψ x + ((⟪w, z - x⟫_ℝ - ε * ‖z - x‖ : ℝ) : EReal) ≤ ψ z) →
            ∃ y w', dist y x ≤ ρ / 2 ∧ dist w' w ≤ 2 * ε ∧ ψ y ≠ ⊤ ∧ ψ y ≠ ⊥ ∧
              |(ψ y).toReal - (ψ x).toReal| ≤ (‖w‖ + ε) * ρ ∧ IsRegularSubgrad ψ y w' := by
          intro ψ x w ε ρ hε hρ hlsc hxT hxB hsub
          set K : ℝ := 2 * ε / ρ with hKdef
          have hK : 0 < K := by positivity
          have hKρ : K * (ρ / 2) = ε := by rw [hKdef]; field_simp
          set r : EuclideanSpace ℝ (Fin N) → ℝ := fun z => -⟪w, z - x⟫_ℝ + K * ‖z - x‖ ^ 2 with hrdef
          have hrc : Continuous r := by
            rw [hrdef]; fun_prop
          set Ψ : EuclideanSpace ℝ (Fin N) → EReal := fun z => ψ z + ((r z : ℝ) : EReal) with hΨdef
          have hΨlsc : LowerSemicontinuousOn Ψ (Metric.closedBall x ρ) := by
            intro z hz
            refine LowerSemicontinuousWithinAt.add' (hlsc z hz) ?_ ?_
            · exact (continuous_coe_real_ereal.comp hrc).continuousAt.continuousWithinAt.lowerSemicontinuousWithinAt
            · exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
          obtain ⟨y, hy, hmin⟩ := hΨlsc.exists_isMinOn ⟨x, Metric.mem_closedBall_self hρ.le⟩
            (isCompact_closedBall x ρ)
          have hmin' : ∀ z ∈ Metric.closedBall x ρ, Ψ y ≤ Ψ z := fun z hz => hmin hz
          have hrx : r x = 0 := by simp [hrdef]
          have hΨx : Ψ y ≤ ψ x := by
            have := hmin' x (Metric.mem_closedBall_self hρ.le)
            simpa [hΨdef, hrx] using this
          have hyB : ψ y ≠ ⊥ := by
            intro h
            have := hsub y hy
            rw [h, le_bot_iff] at this
            exact EReal.add_ne_bot_iff.mpr ⟨hxB, EReal.coe_ne_bot _⟩ this
          have hyT : ψ y ≠ ⊤ := by
            intro h
            have : Ψ y = ⊤ := by
              simp only [hΨdef, h]; exact EReal.top_add_coe _
            rw [this, top_le_iff] at hΨx
            exact hxT hΨx
          set a := (ψ x).toReal with ha
          set b := (ψ y).toReal with hb
          have hxa : ψ x = (a : EReal) := (EReal.coe_toReal hxT hxB).symm
          have hyb : ψ y = (b : EReal) := (EReal.coe_toReal hyT hyB).symm
          have h1 : a + (⟪w, y - x⟫_ℝ - ε * ‖y - x‖) ≤ b := by
            have := hsub y hy
            rw [hxa, hyb, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
            exact this
          have h2 : b + r y ≤ a := by
            have := hΨx
            simp only [hΨdef] at this
            rw [hxa, hyb, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
            exact this
          have hry : r y = -⟪w, y - x⟫_ℝ + K * ‖y - x‖ ^ 2 := rfl
          set t := ‖y - x‖ with ht
          have ht0 : 0 ≤ t := norm_nonneg _
          have htρ : t ≤ ρ / 2 := by
            by_contra hc
            rw [not_le] at hc
            have : K * t ^ 2 ≤ ε * t := by linarith
            rw [← hKρ] at this
            have hpos : 0 < K * t * (t - ρ / 2) := by
              apply mul_pos (mul_pos hK (by linarith)) (by linarith)
            have e : K * t * (t - ρ / 2) = K * t ^ 2 - K * (ρ / 2) * t := by ring
            linarith
          have hin : |⟪w, y - x⟫_ℝ| ≤ ‖w‖ * t := abs_real_inner_le_norm _ _
          have hin2 := abs_le.mp hin
          refine ⟨y, w - (2 * K) • (y - x), ?_, ?_, hyT, hyB, ?_, ?_⟩
          · rw [dist_eq_norm]; exact htρ
          · rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
              abs_of_pos (by positivity)]
            rw [← ht]
            have := mul_le_mul_of_nonneg_left htρ hK.le
            linarith
          · rw [abs_le]
            have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
            have hry' := h2
            rw [hry] at hry'
            have htρ' : t ≤ ρ := by linarith
            have m1 := mul_le_mul_of_nonneg_left htρ' hw0
            have m2 := mul_le_mul_of_nonneg_left htρ' hε.le
            have m3 : 0 ≤ K * t ^ 2 := by positivity
            have e : (‖w‖ + ε) * ρ = ‖w‖ * ρ + ε * ρ := by ring
            constructor
            · linarith
            · linarith
          · refine ⟨hyT, fun ε' hε' => ?_⟩
            have hδ : 0 < min (ρ / 2) (ε' / K) := lt_min (by positivity) (by positivity)
            filter_upwards [Metric.ball_mem_nhds y hδ] with z hz
            rw [Metric.mem_ball] at hz
            have hz1 : dist z y < ρ / 2 := lt_of_lt_of_le hz (min_le_left _ _)
            have hz2 : dist z y < ε' / K := lt_of_lt_of_le hz (min_le_right _ _)
            have hzx : z ∈ Metric.closedBall x ρ := by
              rw [Metric.mem_closedBall]
              have := dist_triangle z y x
              rw [dist_eq_norm y x] at this
              linarith
            by_cases hzT : ψ z = ⊤
            · rw [hzT]; exact le_top
            have hzB : ψ z ≠ ⊥ := by
              intro h
              have := hsub z hzx
              rw [h, le_bot_iff] at this
              exact EReal.add_ne_bot_iff.mpr ⟨hxB, EReal.coe_ne_bot _⟩ this
            set c := (ψ z).toReal with hc
            have hzc : ψ z = (c : EReal) := (EReal.coe_toReal hzT hzB).symm
            have h3 : b + r y ≤ c + r z := by
              have := hmin' z hzx
              simp only [hΨdef] at this
              rw [hyb, hzc, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
              exact this
            have hrz : r z = -⟪w, z - x⟫_ℝ + K * ‖z - x‖ ^ 2 := rfl
            have hzsplit : z - x = (z - y) + (y - x) := (sub_add_sub_cancel z y x).symm
            have hexp : ‖z - x‖ ^ 2 = ‖z - y‖ ^ 2 + 2 * ⟪z - y, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
              rw [hzsplit, norm_add_sq_real]
            have hinn : ⟪w, z - x⟫_ℝ = ⟪w, z - y⟫_ℝ + ⟪w, y - x⟫_ℝ := by
              rw [hzsplit, inner_add_right]
            have hw' : ⟪w - (2 * K) • (y - x), z - y⟫_ℝ
                = ⟪w, z - y⟫_ℝ - 2 * K * ⟪z - y, y - x⟫_ℝ := by
              rw [inner_sub_left, real_inner_smul_left, real_inner_comm (y - x) (z - y)]
            set s := ‖z - y‖ with hs
            have hs0 : 0 ≤ s := norm_nonneg _
            have hsK : K * s ≤ ε' := by
              rw [dist_eq_norm] at hz2
              rw [lt_div_iff₀ hK] at hz2
              linarith
            have hKs : K * s ^ 2 ≤ ε' * s := by
              have e := mul_le_mul_of_nonneg_right hsK hs0
              have e2 : K * s ^ 2 = K * s * s := by ring
              linarith
            rw [hyb, hzc, ← EReal.coe_add, EReal.coe_le_coe_iff]
            rw [hw']
            rw [hry, hrz, hexp, hinn] at h3
            have e : K * (s ^ 2 + 2 * ⟪z - y, y - x⟫_ℝ + t ^ 2)
                = K * s ^ 2 + 2 * K * ⟪z - y, y - x⟫_ℝ + K * t ^ 2 := by ring
            linarith
        have hGLm : ∀ (φ ψ : EuclideanSpace ℝ (Fin N) → EReal) (m : EuclideanSpace ℝ (Fin N) → ℝ)
            (L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) (G x0 : EuclideanSpace ℝ (Fin N)) (R : ℝ),
            0 < R → (∀ z, φ z ≠ ⊥) →
            (∀ z, dist z x0 < R → ψ z = if φ z = ⊤ then ⊤ else (((φ z).toReal * m z : ℝ) : EReal)) →
            (∀ z, dist z x0 < R → 0 < m z) → LowerSemicontinuousOn ψ (Metric.ball x0 R) →
            HasStrictFDerivAt m L x0 → (∀ v, L v = ⟪G, v⟫_ℝ) →
            ∀ u ∈ LimitingSubdiff φ x0, m x0 • u + (φ x0).toReal • G ∈ LimitingSubdiff ψ x0 := by
          intro φ ψ m L G x0 R hR hφbot hrel hmpos hψlsc hm hLG u hu
          obtain ⟨hφx0, xs, vs, hxs, hfx, hvs, hreg⟩ := hu
          set a := (φ x0).toReal with ha
          set μ := m x0 with hμ
          have hψx0 : ψ x0 = ((a * μ : ℝ) : EReal) := by
            rw [hrel x0 (by simpa using hR), if_neg hφx0]
          have hψx : ∀ z, dist z x0 < R → φ z ≠ ⊤ → ψ z = (((φ z).toReal * m z : ℝ) : EReal) := by
            intro z hz hz'; rw [hrel z hz, if_neg hz']
          apply CR ψ x0 _ (by rw [hψx0]; exact EReal.coe_ne_top _) (by rw [hψx0]; exact EReal.coe_ne_bot _)
          intro δ hδ
          have hmt : Tendsto (fun t => m (xs t)) atTop (𝓝 μ) := hm.continuousAt.tendsto.comp hxs
          have hbt : Tendsto (fun t => (φ (xs t)).toReal) atTop (𝓝 a) :=
            (EReal.tendsto_toReal hφx0 (hφbot x0)).comp hfx
          have hwt : Tendsto (fun t => m (xs t) • vs t + (φ (xs t)).toReal • G) atTop
              (𝓝 (μ • u + a • G)) := (hmt.smul hvs).add (hbt.smul_const G)
          have hpt : Tendsto (fun t => (φ (xs t)).toReal * m (xs t)) atTop (𝓝 (a * μ)) := hbt.mul hmt
          set ε' := δ / 8 with hε'
          have hε'pos : 0 < ε' := by positivity
          set η := ε' / (3 * (|a| + 1)) with hη
          have hηpos : 0 < η := by positivity
          obtain ⟨r, hr, hSD⟩ := SD m L x0 hm η hηpos
          set r1 := min (min r R) δ / 2 with hr1
          have hr1pos : 0 < r1 := by positivity
          have E1 := hxs.eventually (Metric.ball_mem_nhds x0 hr1pos)
          have E2 := hwt.eventually (Metric.ball_mem_nhds (μ • u + a • G) (half_pos hδ))
          have E3 := hpt.eventually (Metric.ball_mem_nhds (a * μ) (half_pos hδ))
          have E4 := hbt.eventually (Metric.ball_mem_nhds a one_pos)
          have E5 := hvs.eventually (Metric.ball_mem_nhds u one_pos)
          obtain ⟨t, h1, h2, h3, h4, h5⟩ := (E1.and (E2.and (E3.and (E4.and E5)))).exists
          change dist (xs t) x0 < r1 at h1
          change dist _ (μ • u + a • G) < δ / 2 at h2
          change dist _ (a * μ) < δ / 2 at h3
          change dist _ a < 1 at h4
          change dist (vs t) u < 1 at h5
          set x := xs t with hxdef
          set v := vs t with hvdef
          set b := (φ x).toReal with hb
          set wt := m x • v + b • G with hwtdef
          set Mv := ‖u‖ + 1 with hMv
          have hvM : ‖v‖ ≤ Mv := by
            have := norm_le_norm_add_norm_sub' v u
            rw [dist_eq_norm] at h5; linarith
          have hbA : |b| ≤ |a| + 1 := by
            rw [Real.dist_eq] at h4
            have := abs_sub_abs_le_abs_sub b a; linarith
          have hxr : dist x x0 < r1 := h1
          have hr1r : r1 < r := by
            have : min (min r R) δ ≤ r := le_trans (min_le_left _ _) (min_le_left _ _)
            linarith
          have hr1R : r1 < R := by
            have : min (min r R) δ ≤ R := le_trans (min_le_left _ _) (min_le_right _ _)
            linarith
          have hr1r2 : r1 + r1 ≤ r := by
            have : min (min r R) δ ≤ r := le_trans (min_le_left _ _) (min_le_left _ _)
            linarith
          have hr1R2 : r1 + r1 ≤ R := by
            have : min (min r R) δ ≤ R := le_trans (min_le_left _ _) (min_le_right _ _)
            linarith
          have hr1δ : r1 < δ := by
            have : min (min r R) δ ≤ δ := min_le_right _ _
            linarith
          have hφx : φ x ≠ ⊤ := (hreg t).1
          have hφxe : φ x = (b : EReal) := (EReal.coe_toReal hφx (hφbot x)).symm
          have hmx : 0 < m x := hmpos x (by linarith)
          set ε1 := ε' / (3 * (m x + 1)) with hε1
          have hε1pos : 0 < ε1 := by positivity
          obtain ⟨ρ1, hρ1, hfr⟩ := Metric.eventually_nhds_iff.mp ((hreg t).2 ε1 hε1pos)
          set K := ‖G‖ + η with hK
          have hKnn : 0 ≤ K := by positivity
          set ρ := min (min (ρ1 / 2) r1) (min (ε' / (3 * (K * Mv + 1)))
            (min (1 / (K + 1)) (δ / (4 * (‖wt‖ + ε' + 1))))) with hρ
          have hρpos : 0 < ρ := by
            have : 0 ≤ Mv := by positivity
            positivity
          have hρ1' : ρ ≤ ρ1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
          have hρr1 : ρ ≤ r1 := le_trans (min_le_left _ _) (min_le_right _ _)
          have hρ2 : ρ ≤ ε' / (3 * (K * Mv + 1)) := le_trans (min_le_right _ _) (min_le_left _ _)
          have hρ3 : ρ ≤ 1 / (K + 1) :=
            le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
          have hρ4 : ρ ≤ δ / (4 * (‖wt‖ + ε' + 1)) :=
            le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
          have hψxe : ψ x = ((b * m x : ℝ) : EReal) := hψx x (by linarith) hφx
          -- approximate subgradient
          have happrox : ∀ z ∈ Metric.closedBall x ρ,
              ψ x + ((⟪wt, z - x⟫_ℝ - ε' * ‖z - x‖ : ℝ) : EReal) ≤ ψ z := by
            intro z hz
            rw [Metric.mem_closedBall] at hz
            have hzx0 : dist z x0 < r1 + r1 := by
              have := dist_triangle z x x0; linarith
            by_cases hφz : φ z = ⊤
            · rw [hrel z (by linarith), if_pos hφz]; exact le_top
            rw [hψx z (by linarith) hφz, hψxe, ← EReal.coe_add, EReal.coe_le_coe_iff]
            set c := (φ z).toReal with hc
            set d := ‖z - x‖ with hd
            have hdρ : d ≤ ρ := by rw [hd, ← dist_eq_norm]; exact hz
            have hd0 : 0 ≤ d := norm_nonneg _
            have hfz := hfr (show dist z x < ρ1 by linarith)
            rw [hφxe, ← EReal.coe_toReal hφz (hφbot z), ← EReal.coe_add, EReal.coe_le_coe_iff] at hfz
            set p := ⟪v, z - x⟫_ℝ with hp
            set q := ⟪G, z - x⟫_ℝ with hq
            have hwin : ⟪wt, z - x⟫_ℝ = m x * p + b * q := by
              rw [hwtdef, inner_add_left, real_inner_smul_left, real_inner_smul_left]
            rw [hwin]
            have hmz : 0 < m z := hmpos z (by linarith)
            have hSDz := hSD x z (by linarith) (by linarith)
            rw [hLG] at hSDz
            set A := m z - m x with hA
            have hpb : |p| ≤ Mv * d := by
              have := abs_real_inner_le_norm v (z - x)
              calc |p| ≤ ‖v‖ * d := this
                _ ≤ Mv * d := by apply mul_le_mul_of_nonneg_right hvM hd0
            have hqb : |q| ≤ ‖G‖ * d := abs_real_inner_le_norm G (z - x)
            have hAq : |A - q| ≤ η * d := by
              have : A - q = m z - m x - q := by rw [hA]
              rw [this]; exact hSDz
            have hAb : |A| ≤ K * d := by
              have := abs_sub_abs_le_abs_sub A q
              have hKd : K * d = ‖G‖ * d + η * d := by rw [hK]; ring
              linarith
            have hAρ : |A| ≤ K * ρ := le_trans hAb (mul_le_mul_of_nonneg_left hdρ hKnn)
            have h4 : |A| * Mv ≤ ε' / 3 := by
              have hMv0 : 0 ≤ Mv := by positivity
              have h' : K * ρ * Mv ≤ ε' / 3 := by
                have : ρ * (3 * (K * Mv + 1)) ≤ ε' := by
                  have hpos : 0 < 3 * (K * Mv + 1) := by positivity
                  rw [le_div_iff₀ hpos] at hρ2; exact hρ2
                have hpos : 0 < 3 * (K * Mv + 1) := by positivity
                have : K * ρ * Mv * 3 ≤ ε' := by
                  have h0 : K * ρ * Mv * 3 = ρ * (3 * (K * Mv + 1)) - 3 * ρ := by ring
                  linarith
                linarith
              calc |A| * Mv ≤ K * ρ * Mv := mul_le_mul_of_nonneg_right hAρ hMv0
                _ ≤ ε' / 3 := h'
            have hmzb : m z ≤ m x + 1 := by
              have : K * ρ ≤ 1 := by
                have hpos : 0 < K + 1 := by positivity
                have : ρ * (K + 1) ≤ 1 := by rw [le_div_iff₀ hpos] at hρ3; exact hρ3
                have h0 : K * ρ = ρ * (K + 1) - ρ := by ring
                linarith
              have := le_abs_self A
              linarith
            have h5 : m z * ε1 ≤ ε' / 3 := by
              have : (m x + 1) * ε1 = ε' / 3 := by
                rw [hε1]; field_simp
              have : m z * ε1 ≤ (m x + 1) * ε1 := mul_le_mul_of_nonneg_right hmzb hε1pos.le
              linarith
            have h6 : |b| * η ≤ ε' / 3 := by
              have : (|a| + 1) * η = ε' / 3 := by
                rw [hη]; field_simp
              have : |b| * η ≤ (|a| + 1) * η := mul_le_mul_of_nonneg_right hbA hηpos.le
              linarith
            have h1' : m z * (p - ε1 * d) ≤ m z * (c - b) := by
              apply mul_le_mul_of_nonneg_left _ hmz.le; linarith
            have h2' : -(|A| * (Mv * d)) ≤ A * p := by
              have : |A * p| ≤ |A| * (Mv * d) := by
                rw [abs_mul]; exact mul_le_mul_of_nonneg_left hpb (abs_nonneg A)
              have := neg_abs_le (A * p); linarith
            have h3' : -(|b| * (η * d)) ≤ b * (A - q) := by
              have : |b * (A - q)| ≤ |b| * (η * d) := by
                rw [abs_mul]; exact mul_le_mul_of_nonneg_left hAq (abs_nonneg b)
              have := neg_abs_le (b * (A - q)); linarith
            have e1 : |A| * Mv * d ≤ ε' / 3 * d := mul_le_mul_of_nonneg_right h4 hd0
            have e2 : m z * ε1 * d ≤ ε' / 3 * d := mul_le_mul_of_nonneg_right h5 hd0
            have e3 : |b| * η * d ≤ ε' / 3 * d := mul_le_mul_of_nonneg_right h6 hd0
            have hmzA : m z = m x + A := by rw [hA]; ring
            rw [hmzA] at h1' e2
            have k1 : (m x + A) * (p - ε1 * d) = m x * p + A * p - (m x + A) * ε1 * d := by ring
            have k2 : (m x + A) * (c - b) + b * (A - q) = c * (m x + A) - b * m x - b * q := by ring
            have k3 : |A| * (Mv * d) = |A| * Mv * d := by ring
            have k4 : |b| * (η * d) = |b| * η * d := by ring
            rw [hmzA]
            have hε'3 : ε' / 3 * d + ε' / 3 * d + ε' / 3 * d = ε' * d := by ring
            linarith
          have hψxt : ψ x ≠ ⊤ := by rw [hψxe]; exact EReal.coe_ne_top _
          have hψxb : ψ x ≠ ⊥ := by rw [hψxe]; exact EReal.coe_ne_bot _
          have hlscB : LowerSemicontinuousOn ψ (Metric.closedBall x ρ) := by
            apply hψlsc.mono
            intro z hz
            rw [Metric.mem_closedBall] at hz
            rw [Metric.mem_ball]
            have := dist_triangle z x x0; linarith
          obtain ⟨y, w', hy, hw', hyt, hyb, hval, hregy⟩ :=
            EX ψ x wt ε' ρ hε'pos hρpos hlscB hψxt hψxb happrox
          refine ⟨y, w', ?_, hyt, hyb, ?_, ?_, hregy⟩
          · have := dist_triangle y x x0
            have hr1δ2 : r1 + r1 ≤ δ := by
              have : min (min r R) δ ≤ δ := min_le_right _ _
              linarith
            linarith
          · rw [hψxe, EReal.toReal_coe] at hval
            rw [hψx0, EReal.toReal_coe]
            rw [Real.dist_eq] at h3
            have hv2 : (‖wt‖ + ε') * ρ ≤ δ / 4 := by
              have hpos : 0 < 4 * (‖wt‖ + ε' + 1) := by positivity
              have : ρ * (4 * (‖wt‖ + ε' + 1)) ≤ δ := by rw [le_div_iff₀ hpos] at hρ4; exact hρ4
              have e : ρ * (4 * (‖wt‖ + ε' + 1)) = 4 * ((‖wt‖ + ε') * ρ) + 4 * ρ := by ring
              linarith
            have := abs_sub_le ((ψ y).toReal) (b * m x) (a * μ)
            linarith
          · have := dist_triangle w' wt (μ • u + a • G)
            have h2' : dist wt (μ • u + a • G) < δ / 2 := h2
            have : m x0 • u + (φ x0).toReal • G = μ • u + a • G := rfl
            rw [this]; linarith
        obtain ⟨L, hL⟩ := hgdiff
        set G := gradient g xbar with hGdef
        have hGL : ∀ v, L v = ⟪G, v⟫_ℝ := by
          intro v
          have hg : G = (InnerProductSpace.toDual ℝ _).symm L :=
            hL.hasFDerivAt.hasGradientAt.gradient
          rw [hg, InnerProductSpace.toDual_symm_apply]
        -- PieceC: replaces Skel.lean lines 58-64 (hgpos [STATEMENT CHANGED, now proved], obtain, hFlsc, hQlsc).
        -- hQat inside hQlsc is a helper (LowerSemicontinuousAt on the ball).
        have hgpos : ∃ R > 0, (∀ z, dist z xbar < R → 0 < g z) ∧
            ContinuousOn g (Metric.ball xbar R) := by
          obtain ⟨K, s, hs, hK⟩ := hL.exists_lipschitzOnWith
          have hev : ∀ᶠ w in 𝓝 xbar, w ∈ s ∧ 0 < g w :=
            (show ∀ᶠ w in 𝓝 xbar, w ∈ s from hs).and (hL.continuousAt.eventually (lt_mem_nhds hgx))
          obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff.1 hev
          refine ⟨ε, hε, fun z hz => (hεs hz).2, ?_⟩
          exact hK.continuousOn.mono (fun w hw => (hεs (Metric.mem_ball.1 hw)).1)
        obtain ⟨R, hR, hgR, hgc⟩ := hgpos
        have hFlsc : LowerSemicontinuous (addInd f S) := by
          intro x y hy
          by_cases hx : x ∈ S
          · have hy' : y < f x := by simpa [addInd, hx] using hy
            filter_upwards [hflsc x y hy'] with w hw
            by_cases hw' : w ∈ S
            · simpa [addInd, hw'] using hw
            · have : y < ⊤ := lt_of_lt_of_le hw le_top
              simpa [addInd, hw'] using this
          · have hy' : y < ⊤ := by simpa [addInd, hx] using hy
            filter_upwards [hS.isOpen_compl.mem_nhds hx] with w hw
            have hw' : w ∉ S := hw
            simpa [addInd, hw'] using hy'
        have hQlsc : LowerSemicontinuousOn (addInd (quotient f g) S) (Metric.ball xbar R) := by
          -- (C-helper) lower semicontinuity at every point of the open ball
          have hQat : ∀ z ∈ Metric.ball xbar R, LowerSemicontinuousAt (addInd (quotient f g) S) z := by
            intro z hz c hc
            have hgz : 0 < g z := hgR z (Metric.mem_ball.1 hz)
            -- values of Q are never ⊥
            have hQne : ∀ w, addInd (quotient f g) S w ≠ ⊥ := by
              intro w
              by_cases hw : w ∈ S
              · by_cases hfw : f w = ⊤
                · simp [addInd, quotient, hw, hfw]
                · simp [addInd, quotient, hw, hfw]
              · simp [addInd, hw]
            induction c using EReal.rec with
            | bot =>
              exact Filter.Eventually.of_forall (fun w => bot_lt_iff_ne_bot.2 (hQne w))
            | top => exact absurd hc (not_lt.2 le_top)
            | coe c' =>
              -- c' * g z < F z
              have hcF : ((c' * g z : ℝ) : EReal) < addInd f S z := by
                by_cases hzS : z ∈ S
                · by_cases hfz : f z = ⊤
                  · rw [show addInd f S z = ⊤ by simp [addInd, hzS, hfz]]
                    exact EReal.coe_lt_top _
                  · have hfz' : f z ≠ ⊥ := hf.1 z
                    have h1 : c' < (f z).toReal / g z := by
                      simpa [addInd, quotient, hzS, hfz] using hc
                    have h2 : c' * g z < (f z).toReal := (lt_div_iff₀ hgz).1 h1
                    have h3 : ((c' * g z : ℝ) : EReal) < (((f z).toReal : ℝ) : EReal) :=
                      EReal.coe_lt_coe_iff.2 h2
                    rw [EReal.coe_toReal hfz hfz'] at h3
                    simpa [addInd, hzS] using h3
                · rw [show addInd f S z = ⊤ by simp [addInd, hzS]]
                  exact EReal.coe_lt_top _
              obtain ⟨b, hb1, hb2⟩ := exists_between hcF
              have hbtop : b ≠ ⊤ := ne_top_of_lt hb2
              have hbbot : b ≠ ⊥ := ne_bot_of_gt hb1
              set a := b.toReal with ha
              have hab : (a : EReal) = b := EReal.coe_toReal hbtop hbbot
              have hca : c' * g z < a := by
                rw [← hab] at hb1; exact EReal.coe_lt_coe_iff.1 hb1
              have hca' : c' < a / g z := (lt_div_iff₀ hgz).2 hca
              have hev1 : ∀ᶠ w in 𝓝 z, (a : EReal) < addInd f S w := hFlsc z a (by rw [hab]; exact hb2)
              have hgcz : ContinuousAt g z := hgc.continuousAt (Metric.isOpen_ball.mem_nhds hz)
              have hdiv : Tendsto (fun w => a / g w) (𝓝 z) (𝓝 (a / g z)) :=
                tendsto_const_nhds.div hgcz hgz.ne'
              have hev2 : ∀ᶠ w in 𝓝 z, c' < a / g w := hdiv.eventually (lt_mem_nhds hca')
              have hev3 : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball xbar R := Metric.isOpen_ball.mem_nhds hz
              filter_upwards [hev1, hev2, hev3] with w hw1 hw2 hw3
              have hgw : 0 < g w := hgR w (Metric.mem_ball.1 hw3)
              by_cases hwS : w ∈ S
              · by_cases hfw : f w = ⊤
                · simp [addInd, quotient, hwS, hfw]
                · have hfw' : f w ≠ ⊥ := hf.1 w
                  have h1 : (a : EReal) < f w := by simpa [addInd, hwS] using hw1
                  have h2 : a < (f w).toReal := by
                    rw [← EReal.coe_toReal hfw hfw'] at h1; exact EReal.coe_lt_coe_iff.1 h1
                  have h3 : a / g w < (f w).toReal / g w := div_lt_div_of_pos_right h2 hgw
                  have h4 : c' < (f w).toReal / g w := lt_trans hw2 h3
                  simpa [addInd, quotient, hwS, hfw] using h4
              · simp [addInd, hwS]
          intro z hz
          exact (hQat z hz).lowerSemicontinuousWithinAt _
        have hGsub : G ∈ LimitingSubdiff (fun y => (g y : EReal)) xbar := by
          refine ⟨EReal.coe_ne_top _, fun _ => xbar, fun _ => G, tendsto_const_nhds,
            tendsto_const_nhds, tendsto_const_nhds, fun _ => ⟨EReal.coe_ne_top _, fun ε hε => ?_⟩⟩
          obtain ⟨r, hr, hrr⟩ := SD g L xbar hL ε hε
          filter_upwards [Metric.ball_mem_nhds xbar hr] with z hz
          have h := hrr xbar z (by simpa using hr) hz
          rw [hGL] at h
          rw [← EReal.coe_add, EReal.coe_le_coe_iff]
          linarith [(abs_le.mp h).1]
        have hGuniq : ∀ v ∈ LimitingSubdiff (fun y => (g y : EReal)) xbar, v = G := by
          rintro v ⟨-, xs, vs, hxs, -, hvs, hreg⟩
          have key : ∀ δ > 0, ‖v - G‖ ≤ 2 * δ := by
            intro δ hδ
            obtain ⟨r, hr, hrr⟩ := SD g L xbar hL δ hδ
            have hev : ∀ᶠ t in atTop, ‖vs t - G‖ ≤ 2 * δ := by
              filter_upwards [hxs (Metric.ball_mem_nhds xbar (half_pos hr))] with t ht
              have ht' : dist (xs t) xbar < r := by
                have := Metric.mem_ball.mp ht; linarith
              set x := xs t with hx
              set w := vs t - G with hw
              rcases (norm_nonneg w).eq_or_lt with h0 | hwpos
              · rw [← h0]; positivity
              have hF := (hreg t).2 δ hδ
              have hB : ∀ᶠ z in 𝓝 x, dist z xbar < r := Metric.isOpen_ball.mem_nhds ht'
              have hT : Tendsto (fun s : ℝ => x + s • w) (𝓝[>] 0) (𝓝 x) := by
                have : Tendsto (fun s : ℝ => x + s • w) (𝓝 0) (𝓝 (x + (0:ℝ) • w)) :=
                  ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0)
                rw [zero_smul, add_zero] at this
                exact this.mono_left nhdsWithin_le_nhds
              obtain ⟨s, ⟨hFs, hBs⟩, hs⟩ :=
                ((hT.eventually (hF.and hB)).and self_mem_nhdsWithin).exists
              have hs : (0:ℝ) < s := hs
              have hzx : x + s • w - x = s • w := by abel
              have hnorm : ‖x + s • w - x‖ = s * ‖w‖ := by
                rw [hzx, norm_smul, Real.norm_of_nonneg hs.le]
              simp only at hFs
              rw [← EReal.coe_add, EReal.coe_le_coe_iff, hnorm, hzx, real_inner_smul_right] at hFs
              have hU := hrr x (x + s • w) ht' hBs
              rw [hGL, hnorm, hzx, real_inner_smul_right] at hU
              have hU' := (abs_le.mp hU).2
              have hin : ⟪vs t, w⟫_ℝ - ⟪G, w⟫_ℝ = ‖w‖ ^ 2 := by
                rw [← inner_sub_left, ← hw, real_inner_self_eq_norm_sq]
              rw [← hx] at hFs
              have hin' : s * ⟪vs t, w⟫_ℝ - s * ⟪G, w⟫_ℝ = s * (‖w‖ * ‖w‖) := by
                rw [← mul_sub, hin, sq]
              have h1 : s * (‖w‖ * ‖w‖) ≤ s * (2 * δ * ‖w‖) := by
                have e : s * (2 * δ * ‖w‖) = 2 * (δ * (s * ‖w‖)) := by ring
                rw [e]; linarith
              have h2 := le_of_mul_le_mul_left h1 hs
              exact le_of_mul_le_mul_right h2 hwpos
            exact le_of_tendsto ((hvs.sub_const G).norm) hev
          have h0 : ‖v - G‖ = 0 := by
            by_contra hne
            have hpos : 0 < ‖v - G‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
            have := key (‖v - G‖ / 4) (by positivity)
            linarith
          exact sub_eq_zero.mp (norm_eq_zero.mp h0)
        set F := addInd f S with hFdef
        set Q := addInd (quotient f g) S with hQdef
        have hFbot : ∀ z, F z ≠ ⊥ := by
          intro z; simp only [hFdef, addInd]; split_ifs <;> simp [hf.1 z]
        have hQbot : ∀ z, Q z ≠ ⊥ := by
          intro z; simp only [hQdef, addInd, quotient]; split_ifs <;> simp
        have hrel1 : ∀ z, Q z = if F z = ⊤ then ⊤ else (((F z).toReal * (g z)⁻¹ : ℝ) : EReal) := by
          intro z
          by_cases hzS : z ∈ S <;> by_cases hfz : f z = ⊤ <;>
            simp [hQdef, hFdef, addInd, quotient, hzS, hfz, div_eq_mul_inv]
        have hrel2 : ∀ z, g z ≠ 0 → F z = if Q z = ⊤ then ⊤ else (((Q z).toReal * g z : ℝ) : EReal) := by
          intro z hz
          by_cases hzS : z ∈ S
          · by_cases hfz : f z = ⊤
            · simp [hFdef, hQdef, addInd, quotient, hzS, hfz]
            · simp only [hFdef, hQdef, addInd, quotient, hzS, hfz, if_true, if_false, EReal.coe_ne_top,
                EReal.toReal_coe]
              rw [div_mul_cancel₀ _ hz, EReal.coe_toReal hfz (hf.1 z)]
          · simp [hFdef, hQdef, addInd, hzS]
        have hQF : (Q xbar).toReal = (F xbar).toReal * (g xbar)⁻¹ := by
          rw [hrel1 xbar]; split_ifs with h
          · simp [h]
          · rw [EReal.toReal_coe]
        have hFx : F xbar = f xbar := by simp [hFdef, addInd, hxS]
        have hLinv : HasStrictFDerivAt (fun y => (g y)⁻¹) ((-(g xbar ^ 2)⁻¹) • L) xbar :=
          (hasStrictDerivAt_inv hgx.ne').comp_hasStrictFDerivAt xbar hL
        have hGLinv : ∀ v, ((-(g xbar ^ 2)⁻¹) • L) v = ⟪(-(g xbar ^ 2)⁻¹) • G, v⟫_ℝ := by
          intro v; simp [hGL, real_inner_smul_left]
        have hsub1 : ∀ u ∈ LimitingSubdiff F xbar,
            (g xbar ^ 2)⁻¹ • (g xbar • u - (f xbar).toReal • G) ∈ LimitingSubdiff Q xbar := by
          intro u hu
          have := hGLm F Q (fun y => (g y)⁻¹) _ _ xbar R hR hFbot (fun z _ => hrel1 z)
            (fun z hz => inv_pos.mpr (hgR z hz)) hQlsc hLinv hGLinv u hu
          convert this using 1
          rw [hFx]
          match_scalars <;> field_simp <;> ring
        have hsub2 : ∀ w ∈ LimitingSubdiff Q xbar,
            g xbar • w + (Q xbar).toReal • G ∈ LimitingSubdiff F xbar := fun w hw =>
          hGLm Q F g L G xbar R hR hQbot (fun z hz => hrel2 z (hgR z hz).ne') hgR
            (hFlsc.lowerSemicontinuousOn _) hL hGL w hw
        have hmain : LimitingSubdiff Q xbar =
            (fun u => (g xbar ^ 2)⁻¹ • (g xbar • u - (f xbar).toReal • G)) '' LimitingSubdiff F xbar := by
          ext w; constructor
          · intro hw
            refine ⟨_, hsub2 w hw, ?_⟩
            simp only
            rw [hQF, hFx]
            match_scalars <;> field_simp <;> ring
          · rintro ⟨u, hu, rfl⟩; exact hsub1 u hu
        refine ⟨hmain, ?_⟩
        constructor
        · rintro ⟨-, h0⟩
          rw [hmain] at h0
          obtain ⟨u, hu, hu0⟩ := h0
          refine ⟨hxS, u, hu, G, hGsub, ?_⟩
          have hne : (g xbar ^ 2)⁻¹ ≠ 0 := by positivity
          exact (smul_eq_zero.mp hu0).resolve_left hne
        · rintro ⟨-, u, hu, v, hv, huv⟩
          have hvG := hGuniq v hv
          subst hvG
          refine ⟨hxS, ?_⟩
          rw [hmain]
          exact ⟨u, hu, by simp only; rw [huv, smul_zero]⟩
