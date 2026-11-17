-- Prove2me | solution 1 for FiniteEnergyPlane.expDecayCInftyTube_cylJ_sub_of_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T18:15:27.503069+00:00
-- url     : https://prove2.me/submissions/15da8744-c908-47c4-a36e-66aa8e10a387

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_Winding
import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_comp_sub
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_rescaled_sub_model
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_fderiv_tubeMap_apply_zero
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_rescaled_fderiv_sub_model



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

/-!
# S, child C6c (local proof): the pulled-back structure `Jbar` on the tube.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff

noncomputable section

namespace SMFC

lemma finrank_CC : Module.finrank ℝ (ℂ × ℂ) = 4 := by
  rw [Module.finrank_prod, Complex.finrank_real_complex]

lemma finrank_V1 : Module.finrank ℝ (V 1) = 4 := by
  simp [V]

/-- An injective map `ℂ × ℂ → V 1` is an isomorphism. -/
lemma exists_equiv_of_injective (L : ℂ × ℂ →L[ℝ] V 1) (hL : Function.Injective L) :
    ∃ e : (ℂ × ℂ) ≃L[ℝ] V 1, (e : ℂ × ℂ →L[ℝ] V 1) = L := by
  let e₀ := LinearMap.linearEquivOfInjective L.toLinearMap hL (by rw [finrank_CC, finrank_V1])
  refine ⟨e₀.toContinuousLinearEquiv, ?_⟩
  ext h <;> rfl

lemma clm_apply_complex {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (L : ℂ →L[ℝ] X) (w : ℂ) : L w = w.re • L 1 + w.im • L Complex.I := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [map_add, show (w.re : ℂ) = w.re • (1 : ℂ) by simp,
    show (w.im : ℂ) * Complex.I = w.im • Complex.I by simp, map_smul, map_smul]

/-- A map satisfying the Cauchy–Riemann equation for `K` with `K² = -1` is `K`-linear. -/
lemma apply_I_mul (K : V 1 →L[ℝ] V 1) (hK : ∀ v, K (K v) = -v) (D : ℂ →L[ℝ] V 1)
    (h : D 1 + K (D Complex.I) = 0) (Δ : ℂ) : D (Complex.I * Δ) = K (D Δ) := by
  have h1 : D 1 = -K (D Complex.I) := eq_neg_of_add_eq_zero_left h
  have h2 : K (D 1) = D Complex.I := by rw [h1, map_neg, hK, neg_neg]
  rw [clm_apply_complex D (Complex.I * Δ), clm_apply_complex D Δ, map_add, map_smul, map_smul,
    h2, h1]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, add_zero, zero_add]
  module

/-- Conjugation of `K` by an isomorphism. -/
lemma conj_facts (e : (ℂ × ℂ) ≃L[ℝ] V 1) (K : V 1 →L[ℝ] V 1) :
    (e : ℂ × ℂ →L[ℝ] V 1).comp
        ((e : ℂ × ℂ →L[ℝ] V 1).inverse.comp (K.comp (e : ℂ × ℂ →L[ℝ] V 1))) =
      K.comp (e : ℂ × ℂ →L[ℝ] V 1) ∧
    ((∀ v, K (K v) = -v) →
      ((e : ℂ × ℂ →L[ℝ] V 1).inverse.comp (K.comp (e : ℂ × ℂ →L[ℝ] V 1))).comp
        ((e : ℂ × ℂ →L[ℝ] V 1).inverse.comp (K.comp (e : ℂ × ℂ →L[ℝ] V 1))) =
        -ContinuousLinearMap.id ℝ (ℂ × ℂ)) := by
  rw [ContinuousLinearMap.inverse_equiv]
  refine ⟨?_, fun hK => ?_⟩
  · ext v <;> simp
  · ext v <;> simp [hK]

end SMFC

theorem exists_jbar_of_tubeMap_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ u)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNJ : ∀ (z ν : ℂ), N z (Complex.I * ν) = Jtilde H J (u z) (N z ν))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p)) :
    ∃ Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ,
      ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
        (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ)) ∧
      (∀ z : ℂ, Jbar (z, 0) = jStd) ∧
      ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
        (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p).comp (Jbar p) =
          (Jtilde H J (u p.1 + N p.1 p.2)).comp
            (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p) := by
  obtain ⟨⟨hOJ, hJc, hJsq⟩, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hK : ∀ y : V 1, y ≠ 0 → ∀ v, Jtilde H J y (Jtilde H J y v) = -v := fun y hy v => by
    simpa using DFunLike.congr_fun (hJsq y hy) v
  set Φ : ℂ × ℂ → V 1 := fun q => u q.1 + N q.1 q.2 with hΦdef
  have hΦc : ContDiff ℝ ∞ Φ :=
    (hu.comp contDiff_fst).add ((hN.comp contDiff_fst).clm_apply contDiff_snd)
  have hDc : ContDiff ℝ ∞ (fderiv ℝ Φ) := hΦc.fderiv_right (m := ∞) (by simp)
  set Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ := fun p =>
    (fderiv ℝ Φ p).inverse.comp ((Jtilde H J (Φ p)).comp (fderiv ℝ Φ p)) with hJbar
  have hO : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)) := isOpen_univ.prod isOpen_ball
  refine ⟨Jbar, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hp0, hpi⟩ := hΦ p hp
    obtain ⟨e, he⟩ := SMFC.exists_equiv_of_injective _ hpi
    have h1 : ContDiffAt ℝ ∞ (fun q => (fderiv ℝ Φ q).inverse) p := by
      have := contDiffAt_map_inverse (n := ∞) e
      rw [he] at this
      exact this.comp p hDc.contDiffAt
    have h2 : ContDiffAt ℝ ∞ (Jtilde H J ∘ Φ) p :=
      (hJc.contDiffAt (hOJ.mem_nhds hp0)).comp p hΦc.contDiffAt
    exact (h1.clm_comp (h2.clm_comp hDc.contDiffAt)).contDiffWithinAt
  · intro p hp
    obtain ⟨hp0, hpi⟩ := hΦ p hp
    obtain ⟨e, he⟩ := SMFC.exists_equiv_of_injective _ hpi
    have := (SMFC.conj_facts e (Jtilde H J (Φ p))).2 (hK _ hp0)
    rw [he] at this
    exact this
  · intro z
    have hz : ((z, 0) : ℂ × ℂ) ∈ Set.univ ×ˢ ball (0 : ℂ) ρ := ⟨mem_univ _, mem_ball_self hρ⟩
    obtain ⟨hp0, hpi⟩ := hΦ _ hz
    obtain ⟨e, he⟩ := SMFC.exists_equiv_of_injective _ hpi
    have hΦz : Φ (z, 0) = u z := by simp [hΦdef]
    have hu0 : u z ≠ 0 := hΦz ▸ hp0
    have hdb : fderiv ℝ u z 1 + Jtilde H J (u z) (fderiv ℝ u z Complex.I) = 0 :=
      (hhol z (mem_univ z)).2
    have hD : ∀ Δ ν : ℂ, fderiv ℝ Φ (z, 0) (Δ, ν) = fderiv ℝ u z Δ + N z ν :=
      fun Δ ν => fderiv_tubeMap_apply_zero u N (hu.differentiable (by simp))
        (hN.differentiable (by simp)) z Δ ν
    have hcomm : (Jtilde H J (Φ (z, 0))).comp (e : ℂ × ℂ →L[ℝ] V 1) =
        (e : ℂ × ℂ →L[ℝ] V 1).comp jStd := by
      rw [he, hΦz]
      refine ContinuousLinearMap.ext fun v => ?_
      obtain ⟨Δ, ν⟩ := v
      have hj : jStd (Δ, ν) = (Complex.I * Δ, Complex.I * ν) := by simp [jStd]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hj, hD, map_add]
      rw [SMFC.apply_I_mul _ (hK _ hu0) _ hdb, hNJ]
    show (fderiv ℝ Φ (z, 0)).inverse.comp ((Jtilde H J (Φ (z, 0))).comp (fderiv ℝ Φ (z, 0))) = jStd
    rw [← he, hcomm, ContinuousLinearMap.inverse_equiv]
    ext v <;> simp
  · intro p hp
    obtain ⟨-, hpi⟩ := hΦ p hp
    obtain ⟨e, he⟩ := SMFC.exists_equiv_of_injective _ hpi
    have := (SMFC.conj_facts e (Jtilde H J (Φ p))).1
    rw [he] at this
    exact this

end

end FiniteEnergyPlane

/-!
# S, child C6a (local proof): `cylJ Jbar` converges to the model `Jinf` on the tube.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff

noncomputable section

namespace SMFD

lemma cylInf_ne_zero (s t : ℝ) : cylInf s t ≠ 0 := by
  simp only [cylInf, ccwLoop]
  exact mul_ne_zero (by exact_mod_cast (Real.exp_pos _).ne') (Complex.exp_ne_zero _)

lemma cylScale_cylScaleInv (s t : ℝ) (v : ℂ × ℂ) : cylScale s t (cylScaleInv s t v) = v := by
  rcases v with ⟨a, b⟩
  have hz := cylInf_ne_zero s t
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [cylScale, cylScaleInv]
  field_simp

lemma cylScaleInv_cylScale (s t : ℝ) (v : ℂ × ℂ) : cylScaleInv s t (cylScale s t v) = v := by
  rcases v with ⟨a, b⟩
  have hz := cylInf_ne_zero s t
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [cylScale, cylScaleInv]
  field_simp

lemma cylScale_injective (s t : ℝ) : Function.Injective (cylScale s t) :=
  Function.LeftInverse.injective (cylScaleInv_cylScale s t)

/-- An isomorphism intertwining `X` with `K` conjugates `K` back to `X`. -/
lemma inverse_conj_eq (e : (ℂ × ℂ) ≃L[ℝ] V 1) (K : V 1 →L[ℝ] V 1) (X : ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (h : (e : ℂ × ℂ →L[ℝ] V 1).comp X = K.comp (e : ℂ × ℂ →L[ℝ] V 1)) :
    (e : ℂ × ℂ →L[ℝ] V 1).inverse.comp (K.comp (e : ℂ × ℂ →L[ℝ] V 1)) = X := by
  rw [ContinuousLinearMap.inverse_equiv, ← h]
  ext v <;> simp

lemma contDiff_embed : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ((p.1 : ℂ) * Complex.I, p.2)) :=
  ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const).prodMk contDiff_snd

end SMFD

theorem expDecayCInftyTube_cylJ_sub_of_intertwining_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
    (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ →
      P.x (P.T * t) + M t (cToVec w) ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re) •
        (P.x (P.T * q.1.im) + M q.1.im (cToVec q.2))) ((t : ℂ) * Complex.I, w)))
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p))
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJbar : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p).comp (Jbar p) =
        (Jtilde H J (u p.1 + N p.1 p.2)).comp
          (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p))
    (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJinf : ∀ (t : ℝ) (w : ℂ), w ∈ ball (0 : ℂ) ρ →
      (fderiv ℝ (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re) •
        (P.x (P.T * q.1.im) + M q.1.im (cToVec q.2))) ((t : ℂ) * Complex.I, w)).comp
          (Jinf (t, w)) =
        (Jtilde H J (P.x (P.T * t) + M t (cToVec w))).comp
          (fderiv ℝ (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re) •
            (P.x (P.T * q.1.im) + M q.1.im (cToVec q.2))) ((t : ℂ) * Complex.I, w))) :
    ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      cylJ Jbar q.1 q.2.1 q.2.2 - Jinf (q.2.1, q.2.2)) ρ b := by
  obtain ⟨⟨hOJ, hJc, -⟩, -, -, -, hJscale⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hMc : ContDiff ℝ ∞ M := hM.1
  -- decay inputs (stated before `set`, so the lambdas match)
  have h3 := expDecayCInftyTube_rescaled_sub_model H hH P u hu0 d b hb ha hw N M hNM ρ hρ
  have h4 := expDecayCInftyTube_rescaled_fderiv_sub_model H hH P u hu hu0 d b hb ha hw
    N hN M hMc hNM ρ hρ
  set Φ : ℂ × ℂ → V 1 := fun q => u q.1 + N q.1 q.2 with hΦdef
  set Y : ℂ × ℂ → V 1 := fun q => Real.exp (2 * P.T * q.1.re) •
    (P.x (P.T * q.1.im) + M q.1.im (cToVec q.2)) with hYdef
  have hYc : ContDiff ℝ ∞ Y := by
    have him : ContDiff ℝ ∞ (fun q : ℂ × ℂ => q.1.im) := Complex.imCLM.contDiff.comp contDiff_fst
    have h1 : ContDiff ℝ ∞ (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re)) :=
      Real.contDiff_exp.comp (contDiff_const.mul (Complex.reCLM.contDiff.comp contDiff_fst))
    have h2 : ContDiff ℝ ∞ (fun q : ℂ × ℂ => P.x (P.T * q.1.im)) :=
      (ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul him)
    have h5 : ContDiff ℝ ∞ (fun q : ℂ × ℂ => M q.1.im (cToVec q.2)) :=
      (hMc.comp him).clm_apply (SMF.contDiff_cToVec.comp contDiff_snd)
    exact h1.smul (h2.add h5)
  set g : ℝ × ℂ → (ℂ × ℂ →L[ℝ] V 1) × V 1 := fun p =>
    (fderiv ℝ Y ((p.1 : ℂ) * Complex.I, p.2), P.x (P.T * p.1) + M p.1 (cToVec p.2)) with hg
  have hgc : ContDiff ℝ ∞ g := by
    refine ((hYc.fderiv_right (m := ∞) (by simp)).comp SMFD.contDiff_embed).prodMk ?_
    exact ((ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul contDiff_fst)).add
      ((hMc.comp contDiff_fst).clm_apply (SMF.contDiff_cToVec.comp contDiff_snd))
  have hYper : (fun q : ℂ × ℂ => Y (q + ((Complex.I, 0) : ℂ × ℂ))) = Y := by
    funext q
    simp only [hYdef, Prod.fst_add, Prod.snd_add, add_zero, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, mul_add, mul_one, P.periodic, hM.2.1 q.1.im]
  have hgper : ∀ (t : ℝ) (w : ℂ), g (t + 1, w) = g (t, w) := by
    intro t w
    have e1 : ((((t + 1 : ℝ) : ℂ) * Complex.I, w) : ℂ × ℂ) =
        (((t : ℂ) * Complex.I, w) : ℂ × ℂ) + ((Complex.I, 0) : ℂ × ℂ) := by
      ext <;> simp [add_mul]
    have e2 : fderiv ℝ Y ((((t + 1 : ℝ) : ℂ) * Complex.I, w)) =
        fderiv ℝ Y ((t : ℂ) * Complex.I, w) := by
      rw [e1, ← fderiv_comp_add_right, hYper]
    simp only [hg, e2, mul_add, mul_one, P.periodic, hM.2.1 t]
  set U : Set ((ℂ × ℂ →L[ℝ] V 1) × V 1) :=
    {x | x.1 ∈ Set.range ((↑) : ((ℂ × ℂ) ≃L[ℝ] V 1) → ℂ × ℂ →L[ℝ] V 1) ∧ x.2 ≠ 0} with hU
  have hUo : IsOpen U :=
    (ContinuousLinearEquiv.isOpen.preimage continuous_fst).inter
      (isOpen_ne_fun continuous_snd continuous_const)
  set G : (ℂ × ℂ →L[ℝ] V 1) × V 1 → ℂ × ℂ →L[ℝ] ℂ × ℂ := fun x =>
    x.1.inverse.comp ((Jtilde H J x.2).comp x.1) with hG
  have hGc : ContDiffOn ℝ ∞ G U := by
    rintro x ⟨⟨e, he⟩, hy⟩
    have h1 : ContDiffAt ℝ ∞ (fun x : (ℂ × ℂ →L[ℝ] V 1) × V 1 => x.1.inverse) x := by
      have := contDiffAt_map_inverse (n := ∞) e
      rw [he] at this
      exact this.comp x contDiffAt_fst
    have h2 : ContDiffAt ℝ ∞ (Jtilde H J ∘ Prod.snd) x :=
      (hJc.contDiffAt (hOJ.mem_nhds hy)).comp x contDiffAt_snd
    exact (h1.clm_comp (h2.clm_comp contDiffAt_fst)).contDiffWithinAt
  have hgU : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → g (t, w) ∈ U := by
    intro t w hw
    obtain ⟨hm, hi⟩ := hL t w hw
    obtain ⟨e, he⟩ := SMFC.exists_equiv_of_injective _ hi
    exact ⟨⟨e, he⟩, hm⟩
  set f : ℝ × ℝ × ℂ → (ℂ × ℂ →L[ℝ] V 1) × V 1 := fun q =>
    (Real.exp (-(2 * (P.T * q.1 + d))) • (fderiv ℝ Φ (cylInf q.1 q.2.1, q.2.2)).comp
        (cylScale q.1 q.2.1),
      Real.exp (-(2 * (P.T * q.1 + d))) • (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2))
    with hf
  have hdiff : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => f q - g (q.2.1, q.2.2)) ρ b :=
    SMD.expDecayCInftyTube_prod h4 h3
  have key := expDecayCInftyTube_comp_sub G U hUo hGc ρ b hρ hb g hgc.contDiffOn hgper hgU f hdiff
  refine SMF.expDecayCInftyTube_congr key fun q hq => ?_
  obtain ⟨s, t, w⟩ := q
  simp only at hq ⊢
  -- the model term
  have hgm : G (g (t, w)) = Jinf (t, w) := by
    obtain ⟨-, hi⟩ := hL t w (ball_subset_closedBall hq)
    obtain ⟨e, he⟩ := SMFC.exists_equiv_of_injective _ hi
    have hJ' := hJinf t w hq
    rw [← he] at hJ'
    show (fderiv ℝ Y ((t : ℂ) * Complex.I, w)).inverse.comp
      ((Jtilde H J (P.x (P.T * t) + M t (cToVec w))).comp (fderiv ℝ Y ((t : ℂ) * Complex.I, w))) =
        Jinf (t, w)
    rw [← he]
    exact SMFD.inverse_conj_eq e _ _ hJ'
  -- the tube term
  have hft : G (f (s, t, w)) = cylJ Jbar s t w := by
    have hp : ((cylInf s t, w) : ℂ × ℂ) ∈ Set.univ ×ˢ ball (0 : ℂ) ρ := ⟨mem_univ _, hq⟩
    obtain ⟨hy, hD⟩ := hΦ _ hp
    set c : ℝ := Real.exp (-(2 * (P.T * s + d))) with hc
    have hc0 : 0 < c := Real.exp_pos _
    set D := fderiv ℝ Φ (cylInf s t, w) with hDdef
    have hKi : Function.Injective (c • D.comp (cylScale s t)) := by
      intro v v' h
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp',
        Function.comp_apply] at h
      exact SMFD.cylScale_injective s t (hD (smul_right_injective (V 1) hc0.ne' h))
    obtain ⟨e, he⟩ := SMFC.exists_equiv_of_injective _ hKi
    have hJsc : Jtilde H J (c • (u (cylInf s t) + N (cylInf s t) w)) =
        Jtilde H J (u (cylInf s t) + N (cylInf s t) w) := hJscale _ hy c hc0
    have hint := hJbar _ hp
    have hcomm : (e : ℂ × ℂ →L[ℝ] V 1).comp (cylJ Jbar s t w) =
        (Jtilde H J (c • (u (cylInf s t) + N (cylInf s t) w))).comp
          (e : ℂ × ℂ →L[ℝ] V 1) := by
      rw [he, hJsc]
      refine ContinuousLinearMap.ext fun v => ?_
      have hv := DFunLike.congr_fun hint (cylScale s t v)
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hv
      simp only [cylJ, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp',
        Function.comp_apply, SMFD.cylScale_cylScaleInv, map_smul]
      rw [hv]
    show (c • D.comp (cylScale s t)).inverse.comp
      ((Jtilde H J (c • (u (cylInf s t) + N (cylInf s t) w))).comp (c • D.comp (cylScale s t))) =
        cylJ Jbar s t w
    rw [← he]
    exact SMFD.inverse_conj_eq e _ _ hcomm
  rw [hft, hgm]

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
    (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ →
      P.x (P.T * t) + M t (cToVec w) ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re) •
        (P.x (P.T * q.1.im) + M q.1.im (cToVec q.2))) ((t : ℂ) * Complex.I, w)))
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p))
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJbar : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p).comp (Jbar p) =
        (Jtilde H J (u p.1 + N p.1 p.2)).comp
          (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p))
    (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJinf : ∀ (t : ℝ) (w : ℂ), w ∈ ball (0 : ℂ) ρ →
      (fderiv ℝ (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re) •
        (P.x (P.T * q.1.im) + M q.1.im (cToVec q.2))) ((t : ℂ) * Complex.I, w)).comp
          (Jinf (t, w)) =
        (Jtilde H J (P.x (P.T * t) + M t (cToVec w))).comp
          (fderiv ℝ (fun q : ℂ × ℂ => Real.exp (2 * P.T * q.1.re) •
            (P.x (P.T * q.1.im) + M q.1.im (cToVec q.2))) ((t : ℂ) * Complex.I, w))) :
    ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      cylJ Jbar q.1 q.2.1 q.2.2 - Jinf (q.2.1, q.2.2)) ρ b :=
  expDecayCInftyTube_cylJ_sub_of_intertwining_aux H hH J hJ P u hu hu0 d b hb ha hw N hN M hM hNM ρ hρ hL hΦ Jbar hJbar Jinf hJinf
