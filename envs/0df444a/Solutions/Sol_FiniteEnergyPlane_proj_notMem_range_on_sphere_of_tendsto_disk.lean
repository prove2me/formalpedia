-- Prove2me | solution 1 for FiniteEnergyPlane.proj_notMem_range_on_sphere_of_tendsto_disk
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T23:53:48.138796+00:00
-- url     : https://prove2.me/submissions/fbe7e5b5-d067-4330-8655-05264c76df49
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_SpanningDisk
import Theorems.Thm_FiniteEnergyPlane_dlambdaDensity_eq_zero_of_proj_mem_range
import Theorems.Thm_FiniteEnergyPlane_false_of_tendstoUniformlyOn_of_boundary_zero
import Theorems.Thm_FiniteEnergyPlane_exists_normalCoord_of_mem_range
import Theorems.Thm_FiniteEnergyPlane_proj_notMem_range_or_forall_mem_of_tendsto
import Theorems.Thm_FiniteEnergyPlane_aCoord_neg_and_boundary_pos_of_isDiskCurve
import Theorems.Thm_FiniteEnergyPlane_proj_smul_eq_of_mem_energySurface



/-! Glue for `proj_notMem_range_on_sphere_of_tendsto_disk` over its children. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Set Filter Topology
open scoped ContDiff ENNReal NNReal Real

theorem pnrb_exists_ccwLoop {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) : ∃ t : ℝ, ccwLoop 1 t = ζ := by
  refine ⟨Complex.arg ζ / (2 * π), ?_⟩
  have hn : ‖ζ‖ = 1 := by simpa using hζ
  unfold ccwLoop
  have : ((2 * π * (Complex.arg ζ / (2 * π)) : ℝ) : ℂ) = (Complex.arg ζ : ℂ) := by
    congr 1; field_simp
  rw [this]
  have := Complex.norm_mul_exp_arg_mul_I ζ
  rw [hn] at this
  push_cast at this ⊢
  simpa using this

theorem proj_notMem_range_on_sphere_of_tendsto_disk_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (e : ℂ → V 1) (z₀ : ℂ)
    (he : IsSpecialSpanningDisk H P e z₀)
    (u : ℂ → V 1) (hu : IsEmbeddedHoloDisk H J e z₀ (closedBall 0 1) u)
    (un : ℕ → ℂ → V 1) (hun : ∀ n, IsEmbeddedHoloDisk H J e z₀ (ball 0 1) (un n))
    (hdis : ∀ n, ∀ z ∈ closedBall (0 : ℂ) 1, proj H (un n z) ∉ Set.range P.x)
    (hconv : TendstoCInftyLocWithin un u (closedBall 0 1) ∅) :
    ∀ z ∈ sphere (0 : ℂ) 1, proj H (u z) ∉ Set.range P.x := by
  intro z₁ hz₁ hmem
  obtain ⟨⟨ρ, heρ, -⟩, -⟩ := id he
  have hρ1 : 1 < ρ := heρ.2.1
  have hsd : closedBall (0 : ℂ) 1 \ ((∅ : Finset ℂ) : Set ℂ) = closedBall 0 1 := by simp
  have hbd : ball (0 : ℂ) 1 \ ((∅ : Finset ℂ) : Set ℂ) = ball 0 1 := by simp
  obtain ⟨⟨-, hcu, hu0, hhol, -, c, hcb, -⟩, -⟩ := id hu
  rw [hsd] at hcu hu0
  rw [hbd] at hhol
  have heS : ∀ ζ ∈ closedBall (0 : ℂ) 1, H (e ζ) = 1 := fun ζ hζ =>
    heρ.2.2.1 (closedBall_subset_ball hρ1 hζ)
  obtain ⟨t₁, ht₁⟩ := pnrb_exists_ccwLoop hz₁
  have hp : u z₁ ∈ Set.range P.x := by
    have hS : H (u z₁) = 1 := by rw [← ht₁, (hcb t₁).2]; exact heS _ (hcb t₁).1
    have h := proj_smul_eq_of_mem_energySurface H hH (u z₁) hS 1 one_pos
    rw [one_smul] at h
    rw [← h]; exact hmem
  -- the interior misses `ℝ × x(ℝ)`
  have hint : ∀ z ∈ ball (0 : ℂ) 1, proj H (u z) ∉ Set.range P.x := by
    have hfe : ∀ w : ℂ → V 1, IsDiskCurve H J e z₀ (closedBall 0 1) ∅ w ∨
        IsDiskCurve H J e z₀ (ball 0 1) ∅ w → IsFiniteEnergyCurve H J (ball 0 1) w := by
      intro w hw
      have key : ∀ A, IsDiskCurve H J e z₀ A ∅ w → IsFiniteEnergyCurve H J (ball 0 1) w := by
        intro A ⟨_, hc, h0, hj, hE, _⟩
        rw [hsd] at hc h0
        rw [hbd] at hj hE
        exact ⟨hc.mono ball_subset_closedBall, fun z hz => h0 z (ball_subset_closedBall hz), hj, hE⟩
      rcases hw with h | h
      · exact key _ h
      · exact key _ h
    have hfu := hfe u (Or.inl hu.1)
    have hfun : ∀ n, IsFiniteEnergyCurve H J (ball 0 1) (un n) := fun n => hfe _ (Or.inr (hun n).1)
    have hui : ∀ z ∈ ball (0 : ℂ) 1, Function.Injective (fderiv ℝ u z) := by
      intro z hz
      have h := hu.2.2 z (by rw [hsd]; exact ball_subset_closedBall hz)
      rwa [fderivWithin_of_mem_nhds (closedBall_mem_nhds_of_mem hz)] at h
    have hconv' : JHolomorphic.TendstoCInftyLocOn un u (ball 0 1) := by
      intro K hK hKc m
      have hK' : K ⊆ closedBall 0 1 \ ∅ := by
        rw [diff_empty]; exact hK.trans ball_subset_closedBall
      have h := hconv K hK' hKc m
      have heq : ∀ f : ℂ → V 1, EqOn (iteratedFDerivWithin ℝ m f (closedBall 0 1))
          (iteratedFDeriv ℝ m f) K := by
        intro f z hz
        have hzb := hK hz
        rw [← iteratedFDerivWithin_inter_open isOpen_ball hzb,
          inter_eq_right.2 ball_subset_closedBall]
        exact iteratedFDerivWithin_of_isOpen m isOpen_ball hzb
      exact (h.congr (Eventually.of_forall fun n => heq (un n))).congr_right (heq u)
    rcases proj_notMem_range_or_forall_mem_of_tendsto H hH J hJ P (ball 0 1) isOpen_ball
      (convex_ball 0 1).isPreconnected u un hfu hui hfun hconv'
      (fun n z hz => hdis n z (ball_subset_closedBall hz)) with h | h
    · exact h
    · exfalso
      have hd := dlambdaDensity_eq_zero_of_proj_mem_range H hH P hP (ball 0 1) isOpen_ball u h
      have hE : dlambdaEnergy H (ball 0 1) u = 0 := by
        unfold dlambdaEnergy
        rw [setLIntegral_congr_fun measurableSet_ball
          (fun z hz => by rw [hd z hz, ENNReal.ofReal_zero])]
        simp
      have hpos := (aCoord_neg_and_boundary_pos_of_isDiskCurve H hH J hJ e ρ heρ z₀
        (closedBall 0 1) (closedBall_subset_ball hρ1) ∅ u hu.1 (by simp)).2.2 rfl
      rw [hE] at hpos
      exact lt_irrefl _ hpos
  -- the normal coordinate near `u z₁`
  obtain ⟨W, N, M, hWo, hpW, hNs, hNz, hNr, hNJ⟩ :=
    exists_normalCoord_of_mem_range H hH J hJ P hP e z₀ he (u z₁) hp
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hWo (u z₁) hpW
  have hKW : closedBall (u z₁) (ε / 2) ⊆ W :=
    (closedBall_subset_ball (by linarith)).trans hεW
  have hz1c : z₁ ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz₁
  obtain ⟨r, hr, hru⟩ := Metric.continuousWithinAt_iff.1 (hcu.continuousOn z₁ hz1c) (ε / 4)
    (by linarith)
  have huK : ∀ z ∈ closedBall (0 : ℂ) 1 ∩ ball z₁ r, u z ∈ closedBall (u z₁) (ε / 2) := by
    intro z hz
    have h := hru hz.1 (mem_ball.1 hz.2)
    rw [mem_closedBall]; linarith
  have hU0 : TendstoUniformlyOn un u atTop (closedBall 0 1) := by
    have h := hconv (closedBall 0 1) (by simp) (isCompact_closedBall 0 1) 0
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro δ hδ
    filter_upwards [h δ hδ] with n hn z hz
    have h' := hn z hz
    simp only [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply,
      LinearIsometryEquiv.dist_map] at h'
    exact h'
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (Metric.tendstoUniformlyOn_iff.1 hU0 (ε / 4) (by linarith))
  have hunK : ∀ n ≥ n₀, ∀ z ∈ closedBall (0 : ℂ) 1 ∩ ball z₁ r,
      un n z ∈ closedBall (u z₁) (ε / 2) := by
    intro n hn z hz
    have h1 := hn₀ n hn z hz.1
    have h2 := hru hz.1 (mem_ball.1 hz.2)
    rw [mem_closedBall]
    calc dist (un n z) (u z₁) ≤ dist (un n z) (u z) + dist (u z) (u z₁) := dist_triangle _ _ _
      _ ≤ ε / 2 := by rw [dist_comm] at h1; linarith
  have hNuc := (isCompact_closedBall (u z₁) (ε / 2)).uniformContinuousOn_of_continuous
    (hNs.continuousOn.mono hKW)
  -- a bound for the derivative of `u`
  have hud : UniqueDiffOn ℝ (closedBall (0 : ℂ) 1) := by
    refine uniqueDiffOn_convex (convex_closedBall 0 1) ?_
    rw [interior_closedBall (0 : ℂ) one_ne_zero]
    exact ⟨0, mem_ball_self one_pos⟩
  have hfdc : ContinuousOn (fderivWithin ℝ u (closedBall 0 1)) (closedBall 0 1) :=
    hcu.continuousOn_fderivWithin hud (by simp)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hfdc
  refine false_of_tendstoUniformlyOn_of_boundary_zero (fun z => N (u z))
    (fun k z => N (un (k + n₀) z)) z₁ hz₁ r hr ?_ (|M| * B) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hNs.comp (hcu.mono inter_subset_left) (fun z hz => hKW (huK z hz))
  · intro z hz
    have hzD : z ∈ closedBall (0 : ℂ) 1 ∩ ball z₁ r := ⟨ball_subset_closedBall hz.1, hz.2⟩
    have hW := hKW (huK z hzD)
    have hudz : DifferentiableAt ℝ u z := (hhol z hz.1).1
    have hdb : JHolomorphic.dbarJ (Jtilde H J) u z = 0 := (hhol z hz.1).2
    have hNd : DifferentiableAt ℝ N (u z) :=
      (hNs.contDiffAt (hWo.mem_nhds hW)).differentiableAt (by simp)
    have hfd : fderiv ℝ (fun z => N (u z)) z = (fderiv ℝ N (u z)).comp (fderiv ℝ u z) :=
      fderiv_comp z hNd hudz
    rw [hfd]
    simp only [ContinuousLinearMap.comp_apply]
    set v := fderiv ℝ u z Complex.I with hv_def
    have hs : fderiv ℝ u z 1 = -Jtilde H J (u z) v := by
      unfold JHolomorphic.dbarJ at hdb
      exact eq_neg_of_add_eq_zero_left hdb
    rw [hs, map_neg]
    have key := hNJ (u z) hW v
    have e1 : -(fderiv ℝ N (u z) (Jtilde H J (u z) v)) + Complex.I * fderiv ℝ N (u z) v =
        Complex.I * (fderiv ℝ N (u z) v +
          Complex.I * fderiv ℝ N (u z) (Jtilde H J (u z) v)) := by
      linear_combination (-(fderiv ℝ N (u z) (Jtilde H J (u z) v))) * Complex.I_sq
    rw [e1, norm_mul, Complex.norm_I, one_mul]
    have hv : ‖v‖ ≤ B := by
      have h1 := hB z hzD.1
      rw [fderivWithin_of_mem_nhds (closedBall_mem_nhds_of_mem hz.1)] at h1
      calc ‖v‖ ≤ ‖fderiv ℝ u z‖ * ‖Complex.I‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ B := by rw [Complex.norm_I, mul_one]; exact h1
    calc _ ≤ M * ‖N (u z)‖ * ‖v‖ := key
      _ ≤ |M| * ‖N (u z)‖ * ‖v‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg _)
      _ ≤ |M| * ‖N (u z)‖ * B :=
          mul_le_mul_of_nonneg_left hv (mul_nonneg (abs_nonneg _) (norm_nonneg _))
      _ = |M| * B * ‖N (u z)‖ := by ring
  · intro z hz hz0
    exact hint z hz.1
      ((hNz _ (hKW (huK z ⟨ball_subset_closedBall hz.1, hz.2⟩))).2.1 hz0)
  · intro z hz
    have hW := hKW (huK z ⟨sphere_subset_closedBall hz.1, hz.2⟩)
    obtain ⟨t, rfl⟩ := pnrb_exists_ccwLoop hz.1
    apply hNr _ hW
    rw [(hcb t).2]
    exact ⟨c t, (hcb t).1, rfl⟩
  · exact (hNz _ hpW).2.2 hmem
  · intro k
    have h := (hun (k + n₀)).1.2.1
    rw [hsd] at h
    exact (hNs.continuousOn.mono hKW).comp (h.continuousOn.mono inter_subset_left)
      (fun z hz => hunK (k + n₀) (Nat.le_add_left n₀ k) z hz)
  · intro k z hz h0
    exact hdis (k + n₀) z hz.1 ((hNz _ (hKW (hunK (k + n₀) (Nat.le_add_left n₀ k) z hz))).2.1 h0)
  · intro k z hz
    obtain ⟨-, -, -, -, -, cn, hcn, -⟩ := (hun (k + n₀)).1
    have hW := hKW (hunK (k + n₀) (Nat.le_add_left n₀ k) z ⟨sphere_subset_closedBall hz.1, hz.2⟩)
    obtain ⟨t, rfl⟩ := pnrb_exists_ccwLoop hz.1
    apply hNr _ hW
    rw [(hcn t).2]
    exact ⟨cn t, ball_subset_closedBall (hcn t).1, rfl⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    obtain ⟨η, hη, hηN⟩ := Metric.uniformContinuousOn_iff.1 hNuc δ hδ
    have h := Metric.tendstoUniformlyOn_iff.1 hU0 η hη
    filter_upwards [(tendsto_add_atTop_nat n₀).eventually h] with k hk z hz
    exact hηN _ (huK z hz) _ (hunK (k + n₀) (Nat.le_add_left n₀ k) z hz) (hk z hz.1)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (e : ℂ → V 1) (z₀ : ℂ)
    (he : IsSpecialSpanningDisk H P e z₀)
    (u : ℂ → V 1) (hu : IsEmbeddedHoloDisk H J e z₀ (closedBall 0 1) u)
    (un : ℕ → ℂ → V 1) (hun : ∀ n, IsEmbeddedHoloDisk H J e z₀ (ball 0 1) (un n))
    (hdis : ∀ n, ∀ z ∈ closedBall (0 : ℂ) 1, proj H (un n z) ∉ Set.range P.x)
    (hconv : TendstoCInftyLocWithin un u (closedBall 0 1) ∅) :
    ∀ z ∈ sphere (0 : ℂ) 1, proj H (u z) ∉ Set.range P.x :=
  proj_notMem_range_on_sphere_of_tendsto_disk_aux H hH J hJ P hP e z₀ he u hu un hun hdis hconv
