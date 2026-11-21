-- Prove2me | solution 1 for FiniteEnergyPlane.exists_tubeGraph_of_isCylCloseTo
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T09:49:05.529189+00:00
-- url     : https://prove2.me/submissions/ea08e177-ba62-4533-954a-e944724e9e0c

import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_exists_mul_le_tubeMap_of_mul_le
import Theorems.Thm_FiniteEnergyPlane_exists_tubeCoords_of_isCylCloseTo
import Theorems.Thm_FiniteEnergyPlane_tubeCoords_expDecay
import Theorems.Thm_FiniteEnergyPlane_exists_lt_infDist_proj_le_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_exists_mul_norm_sub_le_of_isEmbeddedPlane
import Theorems.Thm_FiniteEnergyPlane_exists_norm_le_infDist_tubeMap
import Theorems.Thm_FiniteEnergyPlane_isPrime_of_isFastPlane_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitzOnWith_reeb
import Theorems.Thm_FiniteEnergyPlane_exists_normalFrame_of_isFastPlane
import Theorems.Thm_FiniteEnergyPlane_exists_stdTube_of_normalFrame
import Theorems.Thm_FiniteEnergyPlane_hasEigenWind_succ_of_unitaryXiFrame
import Theorems.Thm_FiniteEnergyPlane_exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_hasEigenWind_iff_of_shift
import Theorems.Thm_FiniteEnergyPlane_exists_hasEigenWind_window



/-!
# A `exists_tubeGraph_of_isCylCloseTo` (9fff83ec): glue against children A1-A4

Tube `Φ(z, w) = u z + N z w` from the normal frame N (`exists_normalFrame_of_isFastPlane`) and
S (`exists_stdTube_of_normalFrame`) over the shifted orbit `P'`; A1 gives the weighted lower
bound (hence `InjOn`) on a smaller width; A2 the graph `f = Φ(ψ, v)`; the intertwining
`DΦ ∘ Jbar = J̃ ∘ DΦ` with `DΦ` injective makes `(ψ, v)` `Jbar`-holomorphic; A4 gives rates of
`u` and `f` below the window and A3 the asymptotics of `(ψ, v)`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma dga_expDecayCInftyTube_mono {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ × ℂ → F} {ρ ρ' b : ℝ} (h : ExpDecayCInftyTube f ρ b) (hρ : ρ' ≤ ρ) :
    ExpDecayCInftyTube f ρ' b := by
  obtain ⟨⟨s₀, hs₀⟩, hb⟩ := h
  have hsub : Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ' ⊆
      Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ :=
    Set.prod_mono le_rfl (Set.prod_mono le_rfl (ball_subset_ball hρ))
  refine ⟨⟨s₀, hs₀.mono hsub⟩, fun m => ?_⟩
  obtain ⟨C, s₁, hC⟩ := hb m
  exact ⟨C, s₁, fun s hs t w hw => hC s hs t w (ball_subset_ball hρ hw)⟩

lemma dga_isStdTubeStructure_mono {ρ ρ' b : ℝ} {Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ}
    {Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ} {Sinf : ℝ → CauchyRiemannIndex.Mat 1}
    (h : IsStdTubeStructure ρ b Jbar Jinf Sinf) (hρ : ρ' ≤ ρ) :
    IsStdTubeStructure ρ' b Jbar Jinf Sinf := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hsub : (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ' ⊆ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ :=
    Set.prod_mono le_rfl (ball_subset_ball hρ)
  have hsub' : (Set.univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ' ⊆ (Set.univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ :=
    Set.prod_mono le_rfl (ball_subset_ball hρ)
  exact ⟨h1.mono hsub, fun p hp => h2 p (hsub hp), h3, h4.mono hsub', h5,
    dga_expDecayCInftyTube_mono h6 hρ, h7, h8⟩

/-- A complex-linear identity on `ℂ` is checked on `1` and `I`. -/
lemma dga_clm_ext_one_I {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : ℂ →L[ℝ] E} (h1 : A 1 = B 1) (hI : A Complex.I = B Complex.I) : A = B := by
  ext w
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  rw [hw, map_add, map_add, map_smul, map_smul, map_smul, map_smul, h1, hI]

/-- Holomorphy transfers through an injective intertwining derivative. -/
lemma dga_hol {G : ℂ → ℂ × ℂ} {Φ : ℂ × ℂ → V 1} {Jt : V 1 → V 1 →L[ℝ] V 1}
    {Jb : ℂ × ℂ →L[ℝ] ℂ × ℂ} (z : ℂ) (hG : DifferentiableAt ℝ G z)
    (hΦ : DifferentiableAt ℝ Φ (G z))
    (hdbar : fderiv ℝ (fun x => Φ (G x)) z 1 +
      Jt (Φ (G z)) (fderiv ℝ (fun x => Φ (G x)) z Complex.I) = 0)
    (hinj : Function.Injective (fderiv ℝ Φ (G z)))
    (hint : (fderiv ℝ Φ (G z)).comp Jb = (Jt (Φ (G z))).comp (fderiv ℝ Φ (G z)))
    (hsq : Jb.comp Jb = -ContinuousLinearMap.id ℝ (ℂ × ℂ)) :
    (fderiv ℝ G z).comp (Complex.I • ContinuousLinearMap.id ℝ ℂ) = Jb.comp (fderiv ℝ G z) := by
  set A := fderiv ℝ G z
  set D := fderiv ℝ Φ (G z)
  have hch : fderiv ℝ (fun x => Φ (G x)) z = D.comp A := fderiv_comp z hΦ hG
  rw [hch] at hdbar
  simp only [ContinuousLinearMap.comp_apply] at hdbar
  have hJI : Jb (A Complex.I) = -A 1 := by
    apply hinj
    have h := congrArg (fun L => L (A Complex.I)) hint
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h, map_neg]
    exact (neg_eq_of_add_eq_zero_right hdbar).symm
  have hJ1 : Jb (A 1) = A Complex.I := by
    have h := congrArg (fun L => L (A Complex.I)) hsq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, hJI, map_neg] at h
    exact neg_injective h
  apply dga_clm_ext_one_I
  · simp [hJ1]
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, Complex.I_mul_I, hJI]
    rw [show (-1 : ℂ) = -(1 : ℂ) from rfl, map_neg]

lemma dga_range_shift {H : V 1 → ℝ} (P P' : ReebOrbit H) (c : ℝ)
    (hx : ∀ τ : ℝ, P'.x τ = P.x (τ + c)) : Set.range P'.x = Set.range P.x := by
  ext y
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨τ + c, (hx τ).symm⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨τ - c, by rw [hx, sub_add_cancel]⟩

/-- A periodic Reeb orbit passing twice through one point is periodic with the time difference. -/
lemma dga_orbit_shift {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (Q : ReebOrbit H)
    (σ₁ σ₂ : ℝ) (h : Q.x σ₁ = Q.x σ₂) (σ : ℝ) : Q.x (σ₁ + σ) = Q.x (σ₂ + σ) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_reeb H hH
  have huniq : (fun s => Q.x (σ₁ + s)) = fun s => Q.x (σ₂ + s) := by
    refine ODE_solution_unique_univ (v := fun _ => reeb H) (s := fun _ => energySurface H)
      (K := K) (t₀ := 0) (fun _ => hK) (fun s => ⟨?_, Q.mem _⟩) (fun s => ⟨?_, Q.mem _⟩)
      (by simpa using h)
    · simpa using (Q.hasDerivAt (σ₁ + s)).comp_const_add σ₁ s
    · simpa using (Q.hasDerivAt (σ₂ + s)).comp_const_add σ₂ s
  exact congrFun huniq σ

lemma dga_isPrime_shift (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) (P P' : ReebOrbit H)
    (c : ℝ) (hT : P'.T = P.T) (hx : ∀ τ : ℝ, P'.x τ = P.x (τ + c)) (hP : P.IsPrime) :
    P'.IsPrime := by
  intro τ hτ hτT heq
  rw [hx, hx, zero_add] at heq
  have h := dga_orbit_shift H hH P (τ + c) c heq (-c)
  rw [add_neg_cancel_right, add_neg_cancel] at h
  exact hP τ hτ (hT ▸ hτT) h

theorem exists_tubeGraph_of_isCylCloseTo_glue (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) :
    ∃ ρ > 0, ∃ b > 0, ∃ (Φ : ℂ × ℂ → V 1) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
      (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → CauchyRiemannIndex.Mat 1),
      ∃ δ < 0, ∃ ε > 0,
      IsStdTubeStructure ρ b Jbar Jinf Sinf ∧
      Set.InjOn Φ (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      (∀ μ ≤ δ, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ 0) ∧
      ∀ f : ℂ → V 1, IsFastPlane H J f → IsNondegenerateEnd H f cylInf P 1 →
        IsCylCloseTo H ε f u →
        ∃ (ψ : ℂ ≃ₜ ℂ) (v : ℂ → ℂ) (κ : ℂ) (b' : ℝ),
          ContDiff ℝ ∞ ψ ∧ ContDiff ℝ ∞ ψ.symm ∧ ContDiff ℝ ∞ v ∧
          (∀ z, v z ∈ ball (0 : ℂ) ρ) ∧ (∀ z, f z = Φ (ψ z, v z)) ∧
          (∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
              (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
            (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z)) ∧
          κ ≠ 0 ∧ 0 < b' ∧
          ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b' ∧
          ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ) := by
  obtain ⟨hfe, -, -⟩ := id hu
  obtain ⟨d, c, b, P', N, M, hb, hT, hx, ha, hw, hN, hNJ, hNinj, -, hM, hwind, hNM⟩ :=
    exists_normalFrame_of_isFastPlane H hH J hJ P u hu huP
  have huC : ContDiff ℝ ∞ u := contDiffOn_univ.1 hfe.1
  have hu0 : ∀ z, u z ≠ 0 := fun z => hfe.2.1 z (Set.mem_univ _)
  rw [← hT] at ha hw hNM
  obtain ⟨ρS, hρS, b₁, hb₁, Jbar, Jinf, Sinf, hstd, hS', hA, -, htube, -⟩ :=
    exists_stdTube_of_normalFrame H hH J hJ P' u huC hu0 hfe.2.2.1 d b hb ha hw N hN hNJ hNinj M
      hM hNM
  have hE : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → HasEigenWind J P μ (k + 1) :=
    fun μ k h => (hasEigenWind_iff_of_shift J P P' c hT hx μ (k + 1)).2
      (hasEigenWind_succ_of_unitaryXiFrame J P' M hM hwind Sinf hstd.2.2.2.2.2.2.1 hS' hA μ k h)
  obtain ⟨δ, hδ, -, hwin⟩ := exists_hasEigenWind_window H hH J hJ P hcz
  have hrange : Set.range P'.x = Set.range P.x := dga_range_shift P P' c hx
  -- A1: weighted lower bound
  obtain ⟨c₀, hc₀, hslice⟩ :=
    exists_mul_norm_sub_le_of_isEmbeddedPlane H hH J hJ P u hu huP hue
  obtain ⟨ρ₁, hρ₁, c₁, hc₁, hlow₁⟩ :=
    exists_mul_le_tubeMap_of_mul_le H hH J hJ P' u huC hu0 c₀ hc₀ hslice d b hb ha hw N hN hNinj
      M hM hNM
  have hP : P.IsPrime := isPrime_of_isFastPlane_of_isNondegenerateEnd H hH J hJ u hu P huP
  have hP' : P'.IsPrime := dga_isPrime_shift H hH P P' c hT hx hP
  obtain ⟨r₀, hr₀, C₀, R₀, hnorm⟩ :=
    exists_norm_le_infDist_tubeMap H hH J hJ P' hP' u hu0 d b hb ha hw N M hM hNM
  set ρ : ℝ := min (min ρS ρ₁) (2 * r₀) with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρS hρ₁) (by linarith)
  have hρS' : ρ ≤ ρS := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ₁' : ρ ≤ ρ₁ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρr : ρ ≤ 2 * r₀ := min_le_right _ _
  have hsubS : (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ ⊆ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρS :=
    Set.prod_mono le_rfl (ball_subset_ball hρS')
  have hsub₁ : (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ ⊆ (Set.univ : Set ℂ) ×ˢ ball (0 : ℂ) ρ₁ :=
    Set.prod_mono le_rfl (ball_subset_ball hρ₁')
  have hstdρ : IsStdTubeStructure ρ b₁ Jbar Jinf Sinf :=
    dga_isStdTubeStructure_mono hstd hρS'
  have hΦρ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p) :=
    fun p hp => ⟨(htube p (hsubS hp)).1, (htube p (hsubS hp)).2.1⟩
  have hlow : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, ∀ q ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      c₁ * (‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖) ≤
        |aCoord H (u p.1 + N p.1 p.2) - aCoord H (u q.1 + N q.1 q.2)| +
          ‖proj H (u p.1 + N p.1 p.2) - proj H (u q.1 + N q.1 q.2)‖ :=
    fun p hp q hq => hlow₁ p (hsub₁ hp) q (hsub₁ hq)
  -- A2: graph representation
  obtain ⟨ε, hε, hgraph⟩ :=
    exists_tubeCoords_of_isCylCloseTo H hH J hJ P' u huC hu0 d b hb ha hw N hN hNinj M hM hNM
      ρ c₁ hρ hc₁ hΦρ hlow
  -- rate of `u` below the window
  obtain ⟨μu, hμu, Cu, hCu⟩ := exists_lt_infDist_proj_le_of_isFastPlane H hH J hJ P u hu huP δ hwin
  refine ⟨ρ, hρ, b₁, hb₁, fun q => u q.1 + N q.1 q.2, Jbar, Jinf, Sinf, δ, hδ, ε, hε, hstdρ,
    ?_, ?_, ?_⟩
  · -- InjOn from the lower bound
    intro p hp q hq hpq
    have h := hlow p hp q hq
    simp only at hpq
    rw [hpq, sub_self, abs_zero, sub_self, norm_zero, add_zero] at h
    have h1 : 0 ≤ ‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) := by positivity
    have h2 : 0 ≤ ‖p.2 - q.2‖ := norm_nonneg _
    have hsum : ‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) + ‖p.2 - q.2‖ = 0 := by
      have := (mul_nonpos_iff.1 h)
      rcases this with ⟨-, h'⟩ | ⟨h', -⟩
      · linarith
      · linarith
    have he2 : ‖p.2 - q.2‖ = 0 := by linarith
    have he1 : ‖p.1 - q.1‖ / (1 + ‖p.1‖ + ‖q.1‖) = 0 := by linarith
    have hpos : 0 < 1 + ‖p.1‖ + ‖q.1‖ := by positivity
    rw [div_eq_zero_iff] at he1
    rcases he1 with he1 | he1
    · exact Prod.ext (sub_eq_zero.1 (norm_eq_zero.1 he1)) (sub_eq_zero.1 (norm_eq_zero.1 he2))
    · exact absurd he1 hpos.ne'
  · -- hwind
    intro μ hμ k hk
    rcases hwin μ (k + 1) (hE μ k hk) with ⟨-, h⟩ | ⟨h, -⟩
    · omega
    · exact absurd (lt_of_lt_of_le h hμ) (lt_irrefl δ)
  · intro f hf hfP hclose
    have hffe : IsFiniteEnergyCurve H J Set.univ f := hf.1
    have hfC : ContDiff ℝ ∞ f := contDiffOn_univ.1 hffe.1
    have hf0 : ∀ z, f z ≠ 0 := fun z => hffe.2.1 z (Set.mem_univ _)
    obtain ⟨ψ, v, hψ, hψs, hv, hvρ, hfeq, hDψ, hDv⟩ := hgraph f hfC hf0 hclose
    have hvball : ∀ z, v z ∈ ball (0 : ℂ) ρ := fun z =>
      mem_ball_zero_iff.2 (lt_of_le_of_lt (hvρ z) (by linarith))
    have hGd : Differentiable ℝ (fun x : ℂ => (ψ x, v x)) :=
      (hψ.differentiable (by simp)).prodMk (hv.differentiable (by simp))
    have hΦC : ContDiff ℝ ∞ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) :=
      (huC.comp contDiff_fst).add ((hN.comp contDiff_fst).clm_apply contDiff_snd)
    have hfG : f = fun x => (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) ((fun x : ℂ => (ψ x, v x)) x) :=
      funext hfeq
    have hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
        (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z) := by
      intro z
      have hp : (ψ z, v z) ∈ Set.univ ×ˢ ball (0 : ℂ) ρ := ⟨Set.mem_univ _, hvball z⟩
      have hdbar := (hffe.2.2.1 z (Set.mem_univ _)).2
      unfold JHolomorphic.dbarJ at hdbar
      rw [hfG] at hdbar
      exact dga_hol (Φ := fun q : ℂ × ℂ => u q.1 + N q.1 q.2) z hGd.differentiableAt
        (hΦC.differentiable (by simp)).differentiableAt hdbar (htube _ (hsubS hp)).2.1
        (htube _ (hsubS hp)).2.2 (hstdρ.2.1 _ hp)
    -- asymptotics of `f`
    obtain ⟨bf, hbf, df, cf, hfa, hfw⟩ :=
      exists_hasExpAsymptoticsEnd_of_isNondegenerateEnd H hH J hJ f hffe P hfP
    have hfw' : ExpDecayCInfty (fun p : ℝ × ℝ => endW H f cylInf p - P'.x (P.T * p.2 + (cf - c))) bf := by
      have : (fun p : ℝ × ℝ => endW H f cylInf p - P'.x (P.T * p.2 + (cf - c))) =
          fun p : ℝ × ℝ => endW H f cylInf p - P.x (1 * P.T * p.2 + cf) := by
        funext p
        rw [hx, one_mul]
        congr 2
        ring
      rw [this]
      exact hfw
    have hfa' : ExpDecayCInfty (fun p : ℝ × ℝ => endA H f cylInf p - P.T * p.1 - df) bf := by
      simpa only [one_mul] using hfa
    obtain ⟨μf, hμf, Cf, hCf⟩ :=
      exists_lt_infDist_proj_le_of_isFastPlane H hH J hJ P f hf hfP δ hwin
    obtain ⟨κ, b', hκ, hb', hψdec, hvdec⟩ :=
      tubeCoords_expDecay H hH J hJ P' u huC hu0 d b hb ha hw N hN hNinj M hM hNM ρ c₁ hρ hc₁
        hΦρ hlow b₁ Jbar Jinf Sinf hstdρ r₀ C₀ R₀
        (fun ζ w hζ hw' => ((hnorm ζ w hζ hw').2.trans_eq (by rw [hrange]))) δ hδ ⟨μu, hμu, Cu, by rw [hrange]; exact hCu⟩ f df
        (cf - c) bf hbf (by rw [hT]; exact hfa') (by rw [hT]; exact hfw')
        ⟨μf, hμf, Cf, by rw [hrange]; exact hCf⟩ ψ v hψ hψs hv hvρ (fun z => (hvρ z).trans (by linarith)) hfeq hDψ hDv hhol
    exact ⟨ψ, v, κ, b', hψ, hψs, hv, hvball, hfeq, hhol, hκ, hb', hψdec, hvdec⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hue : IsEmbeddedPlane u) :
    ∃ ρ > 0, ∃ b > 0, ∃ (Φ : ℂ × ℂ → V 1) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
      (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → CauchyRiemannIndex.Mat 1),
      ∃ δ < 0, ∃ ε > 0,
      IsStdTubeStructure ρ b Jbar Jinf Sinf ∧
      Set.InjOn Φ (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      (∀ μ ≤ δ, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ 0) ∧
      ∀ f : ℂ → V 1, IsFastPlane H J f → IsNondegenerateEnd H f cylInf P 1 →
        IsCylCloseTo H ε f u →
        ∃ (ψ : ℂ ≃ₜ ℂ) (v : ℂ → ℂ) (κ : ℂ) (b' : ℝ),
          ContDiff ℝ ∞ ψ ∧ ContDiff ℝ ∞ ψ.symm ∧ ContDiff ℝ ∞ v ∧
          (∀ z, v z ∈ ball (0 : ℂ) ρ) ∧ (∀ z, f z = Φ (ψ z, v z)) ∧
          (∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
              (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
            (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z)) ∧
          κ ≠ 0 ∧ 0 < b' ∧
          ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b' ∧
          ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ) :=
  exists_tubeGraph_of_isCylCloseTo_glue H hH J hJ P hcz u hu huP hue
