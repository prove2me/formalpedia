-- Prove2me | solution 1 for FiniteEnergyPlane.tubeCoords_expDecay
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T18:12:55.130447+00:00
-- url     : https://prove2.me/submissions/3f3c1896-efcc-4350-b8cb-25c23bbd989e

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Theorems.Thm_FiniteEnergyPlane_tubeCoords_bounded_iteratedFDeriv
import Theorems.Thm_FiniteEnergyPlane_tubeCoords_div_sub_le
import Theorems.Thm_FiniteEnergyPlane_tubeCoords_norm_le_rpow
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_of_tendstoZeroCInfty



/-! A3 `tubeCoords_expDecay` 6c8e4509: glue from the children. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

namespace DGA3G

lemma norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

lemma cylInf_ne_zero' (s t : ℝ) : cylInf s t ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_cylInf]; exact (Real.exp_pos _).ne'

lemma contDiff_cylInf : ContDiff ℝ ∞ (fun q : ℝ × ℝ => cylInf q.1 q.2) := by
  have e : (fun q : ℝ × ℝ => cylInf q.1 q.2) = fun q : ℝ × ℝ =>
      Complex.ofRealCLM (Real.exp (2 * π * q.1)) *
        Complex.exp (Complex.ofRealCLM (2 * π * q.2) * Complex.I) := rfl
  rw [e]
  refine (Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst))).mul ?_
  exact Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_snd)).mul contDiff_const)

/-- Bounded derivatives and a `C⁰` exponential rate give `C^∞` decay at any smaller rate. -/
lemma expDecay_of_bounded {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ × ℝ → F) (hg : ContDiff ℝ ∞ g)
    (hB : ∀ m : ℕ, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m g (s, t)‖ ≤ C)
    {β C s₀ : ℝ} (h0 : ∀ s ≥ s₀, ∀ t : ℝ, ‖g (s, t)‖ ≤ C * Real.exp (-(β * s))) (hβ : 0 < β) :
    ∀ b' < β, ExpDecayCInfty g b' := by
  have hT : TendstoZeroUnif g := by
    intro ε hε
    have ht : Tendsto (fun s : ℝ => C * Real.exp (-(β * s))) atTop (𝓝 0) := by
      have : Tendsto (fun s : ℝ => Real.exp (-(β * s))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
          (tendsto_id.const_mul_atTop hβ))
      simpa using this.const_mul C
    obtain ⟨s₂, hs₂⟩ := eventually_atTop.1 ((ht.eventually (ge_mem_nhds hε)).and
      (eventually_ge_atTop s₀))
    exact ⟨s₂, fun s hs t => (h0 s (hs₂ s hs).2 t).trans (hs₂ s hs).1⟩
  have hZ := tendstoZeroCInfty_of_tendstoZeroUnif_of_bdd g 0 hg.contDiffOn hT hB
  exact expDecayCInfty_of_tendstoZeroCInfty g hZ β C s₀ h0

end DGA3G

open DGA3G in
theorem tubeCoords_expDecay_glue (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p))
    (hlow : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (u p.1 + N p.1 p.2) - aCoord H (u q.1 + N q.1 q.2)| +
          ‖proj H (u p.1 + N p.1 p.2) - proj H (u q.1 + N q.1 q.2)‖)
    (b₁ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hstd : IsStdTubeStructure ρ b₁ Jbar Jinf Sinf)
    (r₀ C₀ R₀ : ℝ)
    (hnorm : ∀ ζ w : ℂ, R₀ ≤ ‖ζ‖ → ‖w‖ ≤ r₀ →
      ‖w‖ ≤ C₀ * (infDist (proj H (u ζ + N ζ w)) (Set.range P.x) +
        infDist (proj H (u ζ)) (Set.range P.x)))
    (δ : ℝ) (hδ : δ < 0)
    (hδu : ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (u z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)))
    (f : ℂ → V 1) (df cf bf : ℝ) (hbf : 0 < bf)
    (hfa : ExpDecayCInfty (fun p : ℝ × ℝ => endA H f cylInf p - P.T * p.1 - df) bf)
    (hfw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H f cylInf p - P.x (P.T * p.2 + cf)) bf)
    (hδf : ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (f z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)))
    (ψ : ℂ ≃ₜ ℂ) (v : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hψs : ContDiff ℝ ∞ ψ.symm)
    (hv : ContDiff ℝ ∞ v) (hvρ : ∀ z, ‖v z‖ ≤ ρ / 2) (hvr : ∀ z, ‖v z‖ ≤ r₀)
    (hf : ∀ z, f z = u (ψ z) + N (ψ z) (v z))
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2)
    (hDv : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ v z‖ ≤ 1)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z)) :
    ∃ (κ : ℂ) (b' : ℝ), κ ≠ 0 ∧ 0 < b' ∧
      ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b' ∧
      ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ) := by
  obtain ⟨μ, hμ, Cv, hCv⟩ := tubeCoords_norm_le_rpow H P u N f r₀ C₀ R₀ hnorm δ hδ hδu hδf ψ
    (hψ.differentiable (by simp)) v hvr hf hDψ
  have hμ0 : μ < 0 := lt_trans hμ hδ
  have he : μ / (2 * π) < 0 := div_neg_of_neg_of_pos hμ0 (by positivity)
  have hCv0 : 0 ≤ Cv := by
    have := (norm_nonneg _).trans (hCv 0)
    simpa using this
  have hv0 : Tendsto v (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 : Tendsto (fun z : ℂ => 1 + ‖z‖) (cocompact ℂ) atTop :=
      tendsto_atTop_add_const_left _ 1 tendsto_norm_cocompact_atTop
    have h3 := (tendsto_rpow_neg_atTop (y := -(μ / (2 * π))) (by linarith)).comp h2
    have h4 : Tendsto (fun z : ℂ => Cv * (1 + ‖z‖) ^ (μ / (2 * π))) (cocompact ℂ) (𝓝 0) := by
      simpa [Function.comp_def] using h3.const_mul Cv
    exact squeeze_zero (fun z => norm_nonneg _) (fun z => hCv z) h4
  have hbd := tubeCoords_bounded_iteratedFDeriv H hH J P u hu hu0 d b hb ha hw N hN hNinj M hM
    hNM f df cf bf hbf hfa hfw ψ v hψ hv hf hDψ hv0
  obtain ⟨κ, hκ, β, hβ, Cq, sq, hq⟩ := tubeCoords_div_sub_le H P u d b hb ha hw N ρ c hρ hc
    hlow f df cf bf hbf hfa hfw ψ v (hψ.differentiable (by simp)) hvρ hf hDψ
  have hcyl := contDiff_cylInf
  have hqs : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2) := by
    have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2)) := hψ.comp hcyl
    have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (cylInf p.1 p.2)⁻¹) :=
      hcyl.inv fun p => cylInf_ne_zero' p.1 p.2
    simpa [div_eq_mul_inv] using h1.mul h2
  have hVs : ContDiff ℝ ∞ (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) := hv.comp hcyl
  refine ⟨κ, β / 2, hκ, by positivity, ?_, ?_⟩
  · refine expDecay_of_bounded _ (hqs.sub contDiff_const) (fun m => ?_) hq hβ (β / 2)
      (by linarith)
    obtain ⟨C, s₁, h⟩ := hbd m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨C + ‖κ‖, s₁, fun s hs t => ?_⟩
      have := (h s hs t).1
      rw [norm_iteratedFDeriv_zero] at this ⊢
      exact (norm_sub_le _ _).trans (by linarith)
    · refine ⟨C, s₁, fun s hs t => ?_⟩
      rw [show (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) =
          (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2) - fun _ => κ from rfl,
        iteratedFDeriv_sub_apply (hqs.contDiffAt.of_le (by exact_mod_cast le_top))
          contDiffAt_const, iteratedFDeriv_const_of_ne hm.ne']
      simpa using (h s hs t).1
  · have h0 : ∀ s ≥ (0 : ℝ), ∀ t : ℝ,
        ‖v (cylInf s t)‖ ≤ Cv * Real.exp (-((-μ) * s)) := by
      intro s hs t
      refine (hCv _).trans (mul_le_mul_of_nonneg_left ?_ hCv0)
      rw [norm_cylInf]
      calc (1 + Real.exp (2 * π * s)) ^ (μ / (2 * π))
          ≤ (Real.exp (2 * π * s)) ^ (μ / (2 * π)) :=
            Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) (by linarith) he.le
        _ = Real.exp (-((-μ) * s)) := by
            rw [← Real.exp_mul]; congr 1; field_simp
    refine expDecay_of_bounded _ hVs (fun m => ?_) h0 (by linarith) (-δ) (by linarith)
    obtain ⟨C, s₁, h⟩ := hbd m
    exact ⟨C, s₁, fun s hs t => (h s hs t).2⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p))
    (hlow : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      c * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (u p.1 + N p.1 p.2) - aCoord H (u q.1 + N q.1 q.2)| +
          ‖proj H (u p.1 + N p.1 p.2) - proj H (u q.1 + N q.1 q.2)‖)
    (b₁ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hstd : IsStdTubeStructure ρ b₁ Jbar Jinf Sinf)
    (r₀ C₀ R₀ : ℝ)
    (hnorm : ∀ ζ w : ℂ, R₀ ≤ ‖ζ‖ → ‖w‖ ≤ r₀ →
      ‖w‖ ≤ C₀ * (infDist (proj H (u ζ + N ζ w)) (Set.range P.x) +
        infDist (proj H (u ζ)) (Set.range P.x)))
    (δ : ℝ) (hδ : δ < 0)
    (hδu : ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (u z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)))
    (f : ℂ → V 1) (df cf bf : ℝ) (hbf : 0 < bf)
    (hfa : ExpDecayCInfty (fun p : ℝ × ℝ => endA H f cylInf p - P.T * p.1 - df) bf)
    (hfw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H f cylInf p - P.x (P.T * p.2 + cf)) bf)
    (hδf : ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (f z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)))
    (ψ : ℂ ≃ₜ ℂ) (v : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hψs : ContDiff ℝ ∞ ψ.symm)
    (hv : ContDiff ℝ ∞ v) (hvρ : ∀ z, ‖v z‖ ≤ ρ / 2) (hvr : ∀ z, ‖v z‖ ≤ r₀)
    (hf : ∀ z, f z = u (ψ z) + N (ψ z) (v z))
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2)
    (hDv : ∀ z, (1 + ‖z‖) * ‖fderiv ℝ v z‖ ≤ 1)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z)) :
    ∃ (κ : ℂ) (b' : ℝ), κ ≠ 0 ∧ 0 < b' ∧
      ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b' ∧
      ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ) :=
  FiniteEnergyPlane.tubeCoords_expDecay_glue H hH J hJ P u hu hu0 d b hb ha hw N hN hNinj M hM hNM ρ c hρ hc hΦ hlow b₁ Jbar Jinf Sinf hstd r₀ C₀ R₀ hnorm δ hδ hδu f df cf bf hbf hfa hfw hδf ψ v hψ hψs hv hvρ hvr hf hDψ hDv hhol
