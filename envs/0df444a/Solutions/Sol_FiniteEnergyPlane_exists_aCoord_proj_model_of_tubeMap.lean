-- Prove2me | solution 1 for FiniteEnergyPlane.exists_aCoord_proj_model_of_tubeMap
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T18:04:49.402282+00:00
-- url     : https://prove2.me/submissions/982b81dd-f3de-478d-8e14-c12b8cb35d95

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_Winding
import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_comp_sub
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_rescaled_sub_model
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul



/-!
# Tube decay algebra (local): lifting decay on the end to the tube, pairs, zero.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff

noncomputable section

namespace SMD

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The projection `(s, t, w) ↦ (s, t)`. -/
def pr : ℝ × ℝ × ℂ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℂ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)))

@[simp] lemma pr_apply (q : ℝ × ℝ × ℂ) : pr q = (q.1, q.2.1) := rfl

lemma norm_pr_le : ‖pr‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun q => by
    simp only [pr_apply, one_mul]
    refine max_le (norm_fst_le q) ((norm_fst_le q.2).trans (norm_snd_le q))

/-- Decay on the end lifts to the tube (constant in `w`). -/
lemma expDecayCInftyTube_of_expDecayCInfty {h : ℝ × ℝ → F} {b : ℝ} (hh : ExpDecayCInfty h b)
    (ρ : ℝ) : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => h (q.1, q.2.1)) ρ b := by
  obtain ⟨⟨s₀, hs⟩, hl⟩ := hh
  set O : Set (ℝ × ℝ) := Ioi s₀ ×ˢ univ with hO
  have hOo : IsOpen O := isOpen_Ioi.prod isOpen_univ
  have hpre : IsOpen (pr ⁻¹' O) := hOo.preimage pr.continuous
  refine ⟨⟨s₀, (hs.comp pr.contDiff.contDiffOn ?_)⟩, fun m => ?_⟩
  · rintro ⟨s, t, w⟩ ⟨hs', -, -⟩
    exact ⟨hs', trivial⟩
  obtain ⟨C, s₁, hC⟩ := hl m
  refine ⟨|C|, max s₁ (s₀ + 1), fun s hs1 t w _ => ?_⟩
  have hsO : pr (s, t, w) ∈ O := ⟨by simp; linarith [le_max_right s₁ (s₀ + 1)], trivial⟩
  have e := ContinuousLinearMap.iteratedFDerivWithin_comp_right pr hs hOo.uniqueDiffOn
    hpre.uniqueDiffOn hsO (i := m) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen m hpre hsO, iteratedFDerivWithin_of_isOpen m hOo hsO] at e
  have e' : (fun q : ℝ × ℝ × ℂ => h (q.1, q.2.1)) = h ∘ pr := rfl
  rw [e', e]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin m, ‖pr‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_pr_le
  have h1 := hC s (le_trans (le_max_left _ _) hs1) t
  simp only [pr_apply] at h1 ⊢
  calc ‖iteratedFDeriv ℝ m h (s, t)‖ * ∏ _i : Fin m, ‖pr‖ ≤ (|C| * Real.exp (-(b * s))) * 1 :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le))
          hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    _ = |C| * Real.exp (-(b * s)) := mul_one _

/-- The zero function decays. -/
lemma expDecayCInftyTube_zero (ρ b : ℝ) :
    ExpDecayCInftyTube (fun _ : ℝ × ℝ × ℂ => (0 : F)) ρ b :=
  ⟨⟨0, contDiffOn_const⟩, fun m => ⟨0, 0, fun s _ t w _ => by
    rw [show (fun _ : ℝ × ℝ × ℂ => (0 : F)) = fun _ => (0 : F) from rfl]
    simp [iteratedFDeriv_const_of_ne, iteratedFDeriv_zero_fun]⟩⟩

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Pairs of decaying maps decay. -/
lemma expDecayCInftyTube_prod {f₁ : ℝ × ℝ × ℂ → F} {f₂ : ℝ × ℝ × ℂ → G} {ρ b : ℝ}
    (h₁ : ExpDecayCInftyTube f₁ ρ b) (h₂ : ExpDecayCInftyTube f₂ ρ b) :
    ExpDecayCInftyTube (fun q => (f₁ q, f₂ q)) ρ b := by
  obtain ⟨⟨s₁, hs₁⟩, hl₁⟩ := h₁
  obtain ⟨⟨s₂, hs₂⟩, hl₂⟩ := h₂
  set S : ℝ := max s₁ s₂
  have hsub₁ : (Ioi S ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ : Set (ℝ × ℝ × ℂ)) ⊆
      Ioi s₁ ×ˢ univ ×ˢ ball (0 : ℂ) ρ :=
    prod_mono (Ioi_subset_Ioi (le_max_left _ _)) subset_rfl
  have hsub₂ : (Ioi S ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ : Set (ℝ × ℝ × ℂ)) ⊆
      Ioi s₂ ×ˢ univ ×ˢ ball (0 : ℂ) ρ :=
    prod_mono (Ioi_subset_Ioi (le_max_right _ _)) subset_rfl
  refine ⟨⟨S, (hs₁.mono hsub₁).prodMk (hs₂.mono hsub₂)⟩, fun m => ?_⟩
  obtain ⟨C₁, t₁, hC₁⟩ := hl₁ m
  obtain ⟨C₂, t₂, hC₂⟩ := hl₂ m
  refine ⟨|C₁| + |C₂|, max (max t₁ t₂) (S + 1), fun s hs t w hw => ?_⟩
  have hsS : S < s := by linarith [le_max_right (max t₁ t₂) (S + 1)]
  have hq : ((s, t, w) : ℝ × ℝ × ℂ) ∈ Ioi S ×ˢ univ ×ˢ ball (0 : ℂ) ρ := ⟨hsS, trivial, hw⟩
  have ho : IsOpen (Ioi S ×ˢ (univ : Set ℝ) ×ˢ ball (0 : ℂ) ρ : Set (ℝ × ℝ × ℂ)) := isOpen_Ioi.prod (isOpen_univ.prod isOpen_ball)
  have ha₁ : ContDiffAt ℝ ∞ f₁ (s, t, w) := (hs₁.mono hsub₁).contDiffAt (ho.mem_nhds hq)
  have ha₂ : ContDiffAt ℝ ∞ f₂ (s, t, w) := (hs₂.mono hsub₂).contDiffAt (ho.mem_nhds hq)
  rw [iteratedFDeriv_prodMk ha₁ ha₂ (by exact_mod_cast le_top),
    ContinuousMultilinearMap.opNorm_prod]
  have e := (Real.exp_pos (-(b * s))).le
  have b₁ := hC₁ s (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs) t w hw
  have b₂ := hC₂ s (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs) t w hw
  have c₁ : C₁ * Real.exp (-(b * s)) ≤ |C₁| * Real.exp (-(b * s)) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) e
  have c₂ : C₂ * Real.exp (-(b * s)) ≤ |C₂| * Real.exp (-(b * s)) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) e
  have d₁ := mul_nonneg (abs_nonneg C₁) e
  have d₂ := mul_nonneg (abs_nonneg C₂) e
  refine max_le ?_ ?_ <;> nlinarith

end SMD

end

end FiniteEnergyPlane

/-!
# S, child C6b (local proof): asymptotics of `aCoord` and `proj` on the tube.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff

noncomputable section

namespace SMF

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Tube decay only depends on the values on the tube. -/
lemma expDecayCInftyTube_congr {f f' : ℝ × ℝ × ℂ → F} {ρ b : ℝ} (h : ExpDecayCInftyTube f ρ b)
    (he : ∀ q : ℝ × ℝ × ℂ, q.2.2 ∈ ball (0 : ℂ) ρ → f q = f' q) :
    ExpDecayCInftyTube f' ρ b := by
  obtain ⟨⟨s₀, hs⟩, hl⟩ := h
  have hO : IsOpen (univ ×ˢ univ ×ˢ ball (0 : ℂ) ρ : Set (ℝ × ℝ × ℂ)) :=
    isOpen_univ.prod (isOpen_univ.prod isOpen_ball)
  refine ⟨⟨s₀, hs.congr fun q hq => (he q hq.2.2).symm⟩, fun m => ?_⟩
  obtain ⟨C, s₁, hC⟩ := hl m
  refine ⟨C, s₁, fun s hs t w hw => ?_⟩
  have hev : f' =ᶠ[𝓝 (s, t, w)] f := by
    filter_upwards [hO.mem_nhds ⟨mem_univ _, mem_univ _, hw⟩] with q hq
    exact (he q hq.2.2).symm
  rw [(hev.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
  exact hC s hs t w hw

/-- `cToVec` as a continuous real-linear map. -/
def cToVecL : ℂ →L[ℝ] CauchyRiemannIndex.Vec 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := cToVec
      map_add' := fun a b => by ext i; rcases i with i | i <;> simp [cToVec]
      map_smul' := fun c a => by ext i; rcases i with i | i <;> simp [cToVec] }

lemma contDiff_cToVec : ContDiff ℝ ∞ (fun w : ℂ => cToVec w) :=
  (cToVecL : ℂ →L[ℝ] _).contDiff

/-- Points of the energy surface: `proj` fixes them and `aCoord` vanishes. -/
lemma proj_aCoord_of_mem {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V 1}
    (hx : H x = 1) : proj H x = x ∧ aCoord H x = 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := hH.2.2 0 hx
    simp at this
  obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 x hx0
  have e1 : ∃ r : ℝ, 0 < r ∧ H (r • x) = 1 := ⟨r, hr0, hr1⟩
  have h1 : scaleToS H x = 1 := by
    unfold scaleToS
    rw [dif_pos e1]
    have hc := Classical.choose_spec e1
    have a := hru _ hc
    have b := hru 1 ⟨one_pos, by simpa using hx⟩
    rw [a, b]
  refine ⟨by simp [proj, h1], by simp [aCoord, h1]⟩

end SMF

theorem exists_aCoord_proj_model_of_tubeMap_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0)
    (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hm : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → P.x (P.T * t) + M t (cToVec w) ≠ 0)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0) :
    ∃ (α : ℝ × ℂ → ℝ) (X : ℝ × ℂ → V 1),
      ContDiffOn ℝ ∞ α (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      ContDiffOn ℝ ∞ X (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      (∀ (t : ℝ) (w : ℂ), α (t + 1, w) = α (t, w) ∧ X (t + 1, w) = X (t, w)) ∧
      (∀ t : ℝ, α (t, 0) = 0 ∧ X (t, 0) = P.x (P.T * t)) ∧
      ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
        aCoord H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - P.T * q.1 - d -
          α (q.2.1, q.2.2)) ρ b ∧
      ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
        proj H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - X (q.2.1, q.2.2)) ρ b := by
  set g : ℝ × ℂ → V 1 := fun p => P.x (P.T * p.1) + M p.1 (cToVec p.2) with hg
  have hcToVec : ContDiff ℝ ∞ (fun w : ℂ => cToVec w) := SMF.contDiff_cToVec
  have hgc : ContDiff ℝ ∞ g := by
    refine ((ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul contDiff_fst)).add ?_
    exact (hM.1.comp contDiff_fst).clm_apply (hcToVec.comp contDiff_snd)
  have hgper : ∀ (t : ℝ) (w : ℂ), g (t + 1, w) = g (t, w) := by
    intro t w
    simp only [hg, mul_add, mul_one, P.periodic, hM.2.1 t]
  have hgU : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → g (t, w) ∈ {y : V 1 | y ≠ 0} :=
    fun t w hw => hm t w hw
  have hUo : IsOpen {y : V 1 | y ≠ 0} := isOpen_ne
  have haC : ContDiffOn ℝ ∞ (aCoord H) {y : V 1 | y ≠ 0} :=
    fun y hy => ((contDiffAt_aCoord_proj H hH y hy).1).contDiffWithinAt
  have hpC : ContDiffOn ℝ ∞ (proj H) {y : V 1 | y ≠ 0} :=
    fun y hy => ((contDiffAt_aCoord_proj H hH y hy).2).contDiffWithinAt
  set f : ℝ × ℝ × ℂ → V 1 := fun q => Real.exp (-(2 * (P.T * q.1 + d))) •
    (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) with hf
  have h3 : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => f q - g (q.2.1, q.2.2)) ρ b :=
    expDecayCInftyTube_rescaled_sub_model H hH P u hu0 d b hb ha hw N M hNM ρ hρ
  have hρ2 : ball (0 : ℂ) ρ ⊆ closedBall 0 ρ := ball_subset_closedBall
  have hmaps : Set.MapsTo g (Set.univ ×ˢ ball (0 : ℂ) ρ) {y : V 1 | y ≠ 0} :=
    fun p hp => hm p.1 p.2 (hρ2 hp.2)
  -- rescaling identity on the tube
  have hscale : ∀ q : ℝ × ℝ × ℂ, q.2.2 ∈ ball (0 : ℂ) ρ →
      proj H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) = proj H (f q) ∧
      aCoord H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) =
        aCoord H (f q) + (P.T * q.1 + d) := by
    intro q hq
    have hy : u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2 ≠ 0 :=
      hΦ (cylInf q.1 q.2.1, q.2.2) ⟨mem_univ _, hq⟩
    have hfy : f q ≠ 0 := smul_ne_zero (Real.exp_pos _).ne' hy
    have e := proj_aCoord_exp_smul H hH (P.T * q.1 + d) (f q) hfy
    have e2 : Real.exp (2 * (P.T * q.1 + d)) • f q =
        u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2 := by
      simp only [hf, smul_smul, ← Real.exp_add]
      rw [show 2 * (P.T * q.1 + d) + -(2 * (P.T * q.1 + d)) = 0 by ring, Real.exp_zero, one_smul]
    rw [e2] at e
    exact e
  refine ⟨fun p => aCoord H (g p), fun p => proj H (g p), haC.comp hgc.contDiffOn hmaps, hpC.comp hgc.contDiffOn hmaps,
    fun t w => ⟨by simp only [hgper], by simp only [hgper]⟩, fun t => ?_, ?_, ?_⟩
  · have hx : H (P.x (P.T * t)) = 1 := P.mem _
    have h0 : g (t, 0) = P.x (P.T * t) := by
      simp only [hg]
      rw [show cToVec (0 : ℂ) = 0 by ext i; rcases i with i | i <;> simp [cToVec], map_zero,
        add_zero]
    show aCoord H (g (t, 0)) = 0 ∧ proj H (g (t, 0)) = P.x (P.T * t)
    rw [h0]
    exact ⟨(SMF.proj_aCoord_of_mem hH hx).2, (SMF.proj_aCoord_of_mem hH hx).1⟩
  · have key := expDecayCInftyTube_comp_sub (aCoord H) {y : V 1 | y ≠ 0} hUo haC ρ b hρ hb g
      hgc.contDiffOn hgper hgU f h3
    refine SMF.expDecayCInftyTube_congr key fun q hq => ?_
    rw [(hscale q hq).2]
    ring
  · have key := expDecayCInftyTube_comp_sub (proj H) {y : V 1 | y ≠ 0} hUo hpC ρ b hρ hb g
      hgc.contDiffOn hgper hgU f h3
    refine SMF.expDecayCInftyTube_congr key fun q hq => ?_
    rw [(hscale q hq).1]

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (u : ℂ → V 1) (hu0 : ∀ z, u z ≠ 0)
    (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hm : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → P.x (P.T * t) + M t (cToVec w) ≠ 0)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0) :
    ∃ (α : ℝ × ℂ → ℝ) (X : ℝ × ℂ → V 1),
      ContDiffOn ℝ ∞ α (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      ContDiffOn ℝ ∞ X (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      (∀ (t : ℝ) (w : ℂ), α (t + 1, w) = α (t, w) ∧ X (t + 1, w) = X (t, w)) ∧
      (∀ t : ℝ, α (t, 0) = 0 ∧ X (t, 0) = P.x (P.T * t)) ∧
      ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
        aCoord H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - P.T * q.1 - d -
          α (q.2.1, q.2.2)) ρ b ∧
      ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
        proj H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - X (q.2.1, q.2.2)) ρ b :=
  exists_aCoord_proj_model_of_tubeMap_aux H hH J P u hu0 d b hb ha hw N M hM hNM ρ hρ hm hΦ
