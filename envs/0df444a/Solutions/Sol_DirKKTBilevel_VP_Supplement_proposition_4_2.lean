-- Prove2me | solution 1 for DirKKTBilevel.VP.Supplement.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:19.060032+00:00
-- url     : https://prove2.me/submissions/15a9d376-2e34-4633-b7d0-6bc075917f63

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model
import Definitions.Def_DirKKTBilevel_VP_Supplement_Variational
import Definitions.Def_DirKKTBilevel_VP_Supplement_Sensitivity

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional DirKKTBilevel.VP

open DirKKTBilevel
open DirKKTBilevel.VP
open DirKKTBilevel.VP.Supplement

/-- Proposition 4.2, p. 15: if the feasible map `𝓕(x) = {y | g(x, y) ≤ 0}` satisfies RS at
`(x̄, ȳ) ∈ gph 𝓕` in direction `u`, then the system `g(x, y) ≤ 0` satisfies the directional MSCQ at
`(x̄, ȳ)` in direction `(u, v)` for every `v ∈ ℝᵐ`. -/
theorem solution {n m p : ℕ} (g : Z n m → E p) (hg : ContDiff ℝ 1 g)
    (x : E n) (y : E m) (u : E n) (hRS : IsRSDir g x y u) :
    ∀ v : E m, DirMSCQ g (WithLp.toLp 2 (x, y) : Z n m) (WithLp.toLp 2 (u, v)) := by
      classical
      rcases hRS with ⟨hfeas, κ, ε, δ, hκ, hε, hδ, hRS⟩
      intro v
      let d : Z n m := WithLp.toLp 2 (u, v)
      have hproj : ∃ η : ℝ, 0 < η ∧ ∀ w : Z n m,
          ‖‖d‖ • w - ‖w‖ • d‖ ≤ η * ‖w‖ * ‖d‖ →
          ‖‖u‖ • w.fst - ‖w.fst‖ • u‖ ≤ δ * ‖w.fst‖ * ‖u‖ := by
        by_cases hu : u = 0
        · refine ⟨1, zero_lt_one, ?_⟩
          intro w hw
          simp [hu]
        have hU : 0 < ‖u‖ := norm_pos_iff.mpr hu
        have hD : 0 < ‖d‖ := lt_of_lt_of_le hU (WithLp.norm_fst_le (E n) d)
        let η : ℝ := min (‖u‖ / (2 * ‖d‖)) (δ * ‖u‖ / (4 * ‖d‖))
        have hη : 0 < η := lt_min (by positivity) (by positivity)
        have hη₁ : η * (2 * ‖d‖) ≤ ‖u‖ :=
          (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
        have hη₂ : η * (4 * ‖d‖) ≤ δ * ‖u‖ :=
          (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
        refine ⟨η, hη, ?_⟩
        intro w hw
        let e : E n := ‖d‖ • w.fst - ‖w‖ • u
        have he : ‖e‖ ≤ η * ‖w‖ * ‖d‖ := by
          exact (WithLp.norm_fst_le (E n) (‖d‖ • w - ‖w‖ • d)).trans hw
        have hr : |‖d‖ * ‖w.fst‖ - ‖w‖ * ‖u‖| ≤ ‖e‖ := by
          simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
            (abs_norm_sub_norm_le (‖d‖ • w.fst) (‖w‖ • u))
        have hlow : ‖w‖ * ‖u‖ ≤ 2 * ‖d‖ * ‖w.fst‖ := by
          have hr' := (abs_le.mp hr).1
          have hh := mul_le_mul_of_nonneg_right hη₁ (norm_nonneg w)
          nlinarith
        have hid : ‖d‖ • (‖u‖ • w.fst - ‖w.fst‖ • u) =
            ‖u‖ • e + (‖w‖ * ‖u‖ - ‖d‖ * ‖w.fst‖) • u := by
          dsimp [e]
          module
        have ht : ‖d‖ * ‖‖u‖ • w.fst - ‖w.fst‖ • u‖ ≤ 2 * ‖u‖ * ‖e‖ := by
          calc
            _ = ‖‖d‖ • (‖u‖ • w.fst - ‖w.fst‖ • u)‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
            _ = ‖‖u‖ • e + (‖w‖ * ‖u‖ - ‖d‖ * ‖w.fst‖) • u‖ := congrArg norm hid
            _ ≤ ‖‖u‖ • e‖ + ‖(‖w‖ * ‖u‖ - ‖d‖ * ‖w.fst‖) • u‖ := norm_add_le _ _
            _ ≤ 2 * ‖u‖ * ‖e‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (norm_nonneg _), abs_sub_comm]
              nlinarith [mul_le_mul_of_nonneg_right hr (norm_nonneg u)]
        have ht' : ‖‖u‖ • w.fst - ‖w.fst‖ • u‖ ≤ 2 * η * (‖w‖ * ‖u‖) := by
          apply (mul_le_mul_iff_right₀ hD).mp
          calc
            _ ≤ 2 * ‖u‖ * ‖e‖ := ht
            _ ≤ 2 * ‖u‖ * (η * ‖w‖ * ‖d‖) :=
              mul_le_mul_of_nonneg_left he (by positivity)
            _ = _ := by ring
        calc
          _ ≤ 2 * η * (‖w‖ * ‖u‖) := ht'
          _ ≤ 2 * η * (2 * ‖d‖ * ‖w.fst‖) :=
            mul_le_mul_of_nonneg_left hlow (by positivity)
          _ ≤ δ * ‖w.fst‖ * ‖u‖ := by
            nlinarith [mul_le_mul_of_nonneg_right hη₂ (norm_nonneg w.fst)]
      rcases hproj with ⟨η, hη, hproj⟩
      refine ⟨hfeas, κ, ε, η, hκ, hε, hη, ?_⟩
      intro z hz
      have hnorm : ‖z - WithLp.toLp 2 (x, y)‖ < ε := hz.1
      have hx : z.fst - x ∈ DirKKTBilevel.VP.dirNbhd ε δ u := by
        refine ⟨?_, ?_⟩
        · exact lt_of_le_of_lt (WithLp.norm_fst_le (E n) (z - WithLp.toLp 2 (x, y))) hnorm
        · exact hproj (z - WithLp.toLp 2 (x, y)) hz.2
      have hy : z.snd ∈ Metric.ball y ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_le_of_lt (WithLp.norm_snd_le (E n) (z - WithLp.toLp 2 (x, y))) hnorm
      have hbound := hRS z.fst hx z.snd hy
      have hdist : Metric.infEDist z {w | ∀ j, g w j ≤ 0} ≤
          Metric.infEDist z.snd (feasLL g z.fst) := by
        apply Metric.le_infEDist.mpr
        intro y' hy'
        have hm : (WithLp.toLp 2 (z.fst, y') : Z n m) ∈ {w | ∀ j, g w j ≤ 0} := hy'
        have hd : edist z (WithLp.toLp 2 (z.fst, y') : Z n m) = edist z.snd y' := by
          rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
          have heq : z - WithLp.toLp 2 (z.fst, y') =
              WithLp.toLp 2 (0, z.snd - y') := by
            apply WithLp.ofLp_injective 2
            change (z.fst - z.fst, z.snd - y') = (0, z.snd - y')
            simp
          rw [heq, WithLp.norm_toLp_snd]
        exact (Metric.infEDist_le_edist_of_mem hm).trans_eq hd
      have hzeta : WithLp.toLp 2 (z.fst, z.snd) = z := WithLp.toLp_ofLp 2 z
      exact hdist.trans (by simpa only [hzeta] using hbound)
