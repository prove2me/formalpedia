-- Prove2me | solution 1 for FiniteEnergyPlane.expDecayCInftyTube_rescaled_fderiv_sub_model
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-15T18:05:13.707292+00:00
-- url     : https://prove2.me/submissions/0bd33454-c023-47c0-b7e2-d8e33ac06bc1

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_Tube
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_comp_sub
import Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_rescaled_sub_model
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x



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
# S, child C4 (local proof), layer 1: calculus of the cylinder coordinates and fderiv decay.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Real

noncomputable section

namespace SMD

/-- `(ζ, μ) ↦ (Re ζ, Im ζ, μ)`. -/
def iota : ℂ × ℂ →L[ℝ] ℝ × ℝ × ℂ :=
  (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).prod
    ((Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)).prod (ContinuousLinearMap.snd ℝ ℂ ℂ))

@[simp] lemma iota_apply (h : ℂ × ℂ) : iota h = (h.1.re, h.1.im, h.2) := rfl

lemma cylInf_eq (s t : ℝ) :
    cylInf s t = Complex.exp ((2 * π : ℂ) * ((s : ℂ) + (t : ℂ) * Complex.I)) := by
  simp only [cylInf, ccwLoop, Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The derivative of `(s, t, w) ↦ (e^{2π(s+it)}, w)`. -/
def cylD (s t : ℝ) : ℝ × ℝ × ℂ →L[ℝ] ℂ × ℂ :=
  ((((2 * π : ℝ) : ℂ) * cylInf s t) • (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)) +
      Complex.I • (Complex.ofRealCLM.comp ((ContinuousLinearMap.fst ℝ ℝ ℂ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)))))).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℂ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)))

lemma hasFDerivAt_cyl (q : ℝ × ℝ × ℂ) :
    HasFDerivAt (fun q : ℝ × ℝ × ℂ => (cylInf q.1 q.2.1, q.2.2)) (cylD q.1 q.2.1) q := by
  have hlin : HasFDerivAt (fun q : ℝ × ℝ × ℂ => (2 * π : ℂ) * ((q.1 : ℂ) + (q.2.1 : ℂ) * Complex.I))
      ((2 * π : ℂ) • (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)) +
        Complex.I • (Complex.ofRealCLM.comp ((ContinuousLinearMap.fst ℝ ℝ ℂ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)))))) q := by
    have := ((Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)) +
        Complex.I • (Complex.ofRealCLM.comp ((ContinuousLinearMap.fst ℝ ℝ ℂ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ))))).hasFDerivAt (x := q)).const_smul (2 * π : ℂ)
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
    simp [mul_comm]
  have he := (Complex.hasDerivAt_exp _).comp_hasFDerivAt q hlin
  have h1 : HasFDerivAt (fun q : ℝ × ℝ × ℂ => cylInf q.1 q.2.1)
      ((((2 * π : ℝ) : ℂ) * cylInf q.1 q.2.1) • (Complex.ofRealCLM.comp
        (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)) + Complex.I • (Complex.ofRealCLM.comp
          ((ContinuousLinearMap.fst ℝ ℝ ℂ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)))))) q := by
    have e : (fun q : ℝ × ℝ × ℂ => cylInf q.1 q.2.1) =
        Complex.exp ∘ fun q : ℝ × ℝ × ℂ => (2 * π : ℂ) * ((q.1 : ℂ) + (q.2.1 : ℂ) * Complex.I) := by
      funext q; simp [cylInf_eq]
    rw [e]
    refine he.congr_fderiv ?_
    rw [← cylInf_eq, smul_smul]
    push_cast
    ring_nf
  exact h1.prodMk ((ContinuousLinearMap.snd ℝ ℝ ℂ).hasFDerivAt.comp q hasFDerivAt_snd)

lemma cylD_iota (s t : ℝ) : (cylD s t).comp iota = cylScale s t := by
  refine ContinuousLinearMap.ext fun h => ?_
  simp only [cylD, cylScale, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    iota_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Complex.ofRealCLM_apply,
    ContinuousLinearMap.prodMap, ContinuousLinearMap.id_apply, ContinuousLinearMap.coe_prodMap',
    Prod.map, smul_eq_mul]
  refine Prod.ext ?_ rfl
  simp only [smul_eq_mul]
  conv_rhs => rw [← Complex.re_add_im h.1]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of a map decaying on the tube decays on the tube. -/
lemma expDecayCInftyTube_fderiv {D : ℝ × ℝ × ℂ → F} {ρ b : ℝ} (h : ExpDecayCInftyTube D ρ b) :
    ExpDecayCInftyTube (fun q => fderiv ℝ D q) ρ b := by
  obtain ⟨⟨s₀, hs⟩, hl⟩ := h
  refine ⟨⟨s₀, hs.fderiv_of_isOpen (isOpen_Ioi.prod (isOpen_univ.prod isOpen_ball))
    (by exact_mod_cast le_top)⟩, fun m => ?_⟩
  obtain ⟨C, s₁, hC⟩ := hl (m + 1)
  exact ⟨C, s₁, fun s hs t w hw => by
    rw [norm_iteratedFDeriv_fderiv]
    exact hC s hs t w hw⟩

end SMD

end

end FiniteEnergyPlane

/-!
# S, child C4 (local proof): the rescaled derivative of the tube map converges to the model
derivative on the tube.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff Real

noncomputable section

theorem expDecayCInftyTube_rescaled_fderiv_sub_model_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (hM : ContDiff ℝ ∞ M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      Real.exp (-(2 * (P.T * q.1 + d))) •
          (fderiv ℝ (fun p : ℂ × ℂ => u p.1 + N p.1 p.2) (cylInf q.1 q.2.1, q.2.2)).comp
            (cylScale q.1 q.2.1) -
        fderiv ℝ (fun p : ℂ × ℂ => Real.exp (2 * P.T * p.1.re) •
          (P.x (P.T * p.1.im) + M p.1.im (cToVec p.2))) ((q.2.1 : ℂ) * Complex.I, q.2.2)) ρ b := by
  set Φ : ℂ × ℂ → V 1 := fun p => u p.1 + N p.1 p.2 with hΦ
  set e : ℝ × ℝ × ℂ → ℝ := fun q => Real.exp (2 * (P.T * q.1 + d)) with he
  set Ψh : ℝ × ℝ × ℂ → V 1 := fun q =>
    Real.exp (-(2 * (P.T * q.1 + d))) • (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2)
    with hΨh
  set mt : ℝ × ℝ × ℂ → V 1 := fun q => P.x (P.T * q.2.1) + M q.2.1 (cToVec q.2.2) with hmt
  set D : ℝ × ℝ × ℂ → V 1 := fun q => Ψh q - mt q with hDdef
  have hD : ExpDecayCInftyTube D ρ b :=
    expDecayCInftyTube_rescaled_sub_model H hH P u hu0 d b hb ha hw N M hNM ρ hρ
  have hDD := SMD.expDecayCInftyTube_fderiv hD
  -- smoothness
  have hΦc : ContDiff ℝ ∞ Φ := (hu.comp contDiff_fst).add
    ((hN.comp contDiff_fst).clm_apply contDiff_snd)
  have hc3 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ => (cylInf q.1 q.2.1, q.2.2)) :=
    contDiff_iff_contDiffAt.2 fun q => by
      have : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ =>
          Complex.exp ((2 * π : ℂ) * ((q.1 : ℂ) + (q.2.1 : ℂ) * Complex.I))) :=
        Complex.contDiff_exp.comp (contDiff_const.mul
          ((Complex.ofRealCLM.contDiff.comp contDiff_fst).add
            ((Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp contDiff_snd)).mul
              contDiff_const)))
      refine (ContDiff.prodMk ?_ contDiff_snd.snd).contDiffAt
      simpa [SMD.cylInf_eq] using this
  have hcToVec : ContDiff ℝ ∞ cToVec := by
    have : (cToVec : ℂ → CauchyRiemannIndex.Vec 1) = fun z =>
        z.re • cToVec 1 + z.im • cToVec Complex.I := by
      funext z; ext i; rcases i with i | i <;> simp [cToVec]
    rw [this]
    exact (Complex.reCLM.contDiff.smul contDiff_const).add
      (Complex.imCLM.contDiff.smul contDiff_const)
  have hmtc : ContDiff ℝ ∞ mt :=
    ((ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul (contDiff_fst.comp contDiff_snd))).add
      ((hM.comp (contDiff_fst.comp contDiff_snd)).clm_apply (hcToVec.comp
        (contDiff_snd.comp contDiff_snd)))
  have hΦcyl : (fun q : ℝ × ℝ × ℂ => Φ (cylInf q.1 q.2.1, q.2.2)) = fun q => e q • Ψh q := by
    funext q
    simp only [he, hΨh, hΦ, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  have hΨc : ContDiff ℝ ∞ Ψh :=
    (Real.contDiff_exp.comp (by fun_prop)).smul (hΦc.comp hc3)
  have hec : ContDiff ℝ ∞ e := Real.contDiff_exp.comp (by fun_prop)
  -- the comparison map
  set Λ : V 1 × (ℝ × ℝ × ℂ →L[ℝ] V 1) → (ℂ × ℂ →L[ℝ] V 1) := fun y =>
    (((2 * P.T) • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ))).smulRight y.1 + y.2).comp SMD.iota
    with hΛ
  have hΛc : ContDiff ℝ ∞ Λ :=
    ((contDiff_const.smulRight contDiff_fst).add contDiff_snd).clm_comp contDiff_const
  have hΛ0 : Λ 0 = 0 := by simp [hΛ]
  have hpair : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => (D q, fderiv ℝ D q) -
      (fun _ : ℝ × ℂ => (0 : V 1 × (ℝ × ℝ × ℂ →L[ℝ] V 1))) (q.2.1, q.2.2)) ρ b := by
    simpa using SMD.expDecayCInftyTube_prod hD hDD
  have key := expDecayCInftyTube_comp_sub Λ univ isOpen_univ hΛc.contDiffOn ρ b hρ hb
    (fun _ => 0) contDiffOn_const (fun _ _ => rfl) (fun _ _ _ => mem_univ _)
    (fun q => (D q, fderiv ℝ D q)) hpair
  simp only [hΛ0, sub_zero] at key
  convert key using 1
  funext q
  obtain ⟨s, t, w⟩ := q
  -- the tube side
  have hK : Real.exp (-(2 * (P.T * s + d))) •
      (fderiv ℝ Φ (cylInf s t, w)).comp (cylScale s t) =
      (((2 * P.T) • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ))).smulRight (Ψh (s, t, w)) +
        fderiv ℝ Ψh (s, t, w)).comp SMD.iota := by
    have h1 : HasFDerivAt (fun q : ℝ × ℝ × ℂ => Φ (cylInf q.1 q.2.1, q.2.2))
        ((fderiv ℝ Φ (cylInf s t, w)).comp (SMD.cylD s t)) (s, t, w) :=
      ((hΦc.differentiable (by simp)) _).hasFDerivAt.comp (s, t, w) (SMD.hasFDerivAt_cyl (s, t, w))
    have h2 : HasFDerivAt (fun q : ℝ × ℝ × ℂ => e q • Ψh q)
        (e (s, t, w) • fderiv ℝ Ψh (s, t, w) +
          (e (s, t, w) • ((2 * P.T) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ))).smulRight
            (Ψh (s, t, w))) (s, t, w) := by
      have hl : HasFDerivAt (fun q : ℝ × ℝ × ℂ => 2 * (P.T * q.1 + d))
          ((2 * P.T) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)) (s, t, w) := by
        have := (((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)).hasFDerivAt (x := (s, t, w))).const_mul
          P.T).add_const d |>.const_mul 2
        refine this.congr_fderiv ?_
        ext <;> simp [smul_eq_mul] <;> ring
      exact (hl.exp).smul ((hΨc.differentiable (by simp)) _).hasFDerivAt
    rw [hΦcyl] at h1
    have h3 := h1.unique h2
    rw [← SMD.cylD_iota, ← ContinuousLinearMap.comp_assoc, h3]
    refine ContinuousLinearMap.ext fun h => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, he, smul_add,
      smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
    simp only [smul_eq_mul]
    have hx : ∀ x : ℝ, rexp (-(2 * (P.T * s + d))) * (rexp (2 * (P.T * s + d)) * (2 * P.T) * x) =
        2 * P.T * x := fun x => by
      rw [mul_assoc, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    rw [hx, add_comm]
  -- the model side
  have hL : fderiv ℝ (fun p : ℂ × ℂ => Real.exp (2 * P.T * p.1.re) •
      (P.x (P.T * p.1.im) + M p.1.im (cToVec p.2))) ((t : ℂ) * Complex.I, w) =
      (((2 * P.T) • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ))).smulRight (mt (s, t, w)) +
        fderiv ℝ mt (s, t, w)).comp SMD.iota := by
    set Yt : ℝ × ℝ × ℂ → V 1 := fun q => Real.exp (2 * P.T * q.1) • mt q with hYt
    have hY : (fun p : ℂ × ℂ => Real.exp (2 * P.T * p.1.re) •
        (P.x (P.T * p.1.im) + M p.1.im (cToVec p.2))) = Yt ∘ SMD.iota := rfl
    have hmt_s : ∀ s' : ℝ, fderiv ℝ mt (s', t, w) = fderiv ℝ mt (s, t, w) := by
      intro s'
      have hd : DifferentiableAt ℝ (fun p : ℝ × ℂ => P.x (P.T * p.1) + M p.1 (cToVec p.2)) (t, w) :=
        ((((ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul contDiff_fst)).add
          ((hM.comp contDiff_fst).clm_apply (hcToVec.comp contDiff_snd))).differentiable
            (by simp)) _
      have hd' : ∀ s'' : ℝ, HasFDerivAt mt ((fderiv ℝ (fun p : ℝ × ℂ =>
          P.x (P.T * p.1) + M p.1 (cToVec p.2)) (t, w)).comp
            (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ))) (s'', t, w) := fun s'' => by
        have := HasFDerivAt.comp (s'', t, w) hd.hasFDerivAt
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℂ)).hasFDerivAt
        exact this
      rw [(hd' s').fderiv, (hd' s).fderiv]
    have h1 : HasFDerivAt Yt (Real.exp (2 * P.T * 0) • fderiv ℝ mt (0, t, w) +
        (Real.exp (2 * P.T * 0) • ((2 * P.T) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ))).smulRight
          (mt (0, t, w))) (0, t, w) := by
      have hl : HasFDerivAt (fun q : ℝ × ℝ × ℂ => 2 * P.T * q.1)
          ((2 * P.T) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)) (0, t, w) := by
        have := ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℂ)).hasFDerivAt (x := (0, t, w))).const_mul
          (2 * P.T)
        refine this.congr_fderiv ?_
        ext <;> simp [smul_eq_mul]
      exact hl.exp.smul ((hmtc.differentiable (by simp)) _).hasFDerivAt
    have hpt : SMD.iota ((t : ℂ) * Complex.I, w) = (0, t, w) := by simp
    rw [← hpt] at h1
    have h2 := h1.comp ((t : ℂ) * Complex.I, w) (SMD.iota.hasFDerivAt (x := ((t : ℂ) * Complex.I, w)))
    rw [hpt] at h2
    rw [hY, h2.fderiv, hmt_s 0]
    have hm0 : mt (0, t, w) = mt (s, t, w) := rfl
    rw [hm0]
    refine ContinuousLinearMap.ext fun h => ?_
    simp [add_comm]
  have hdD : fderiv ℝ D (s, t, w) = fderiv ℝ Ψh (s, t, w) - fderiv ℝ mt (s, t, w) :=
    fderiv_sub ((hΨc.differentiable (by simp)) _) ((hmtc.differentiable (by simp)) _)
  rw [hK, hL, hdD]
  simp only [hΛ, hDdef]
  refine ContinuousLinearMap.ext fun h => ?_
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, smul_sub]
  abel

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hu0 : ∀ z, u z ≠ 0) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N) (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (hM : ContDiff ℝ ∞ M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      Real.exp (-(2 * (P.T * q.1 + d))) •
          (fderiv ℝ (fun p : ℂ × ℂ => u p.1 + N p.1 p.2) (cylInf q.1 q.2.1, q.2.2)).comp
            (cylScale q.1 q.2.1) -
        fderiv ℝ (fun p : ℂ × ℂ => Real.exp (2 * P.T * p.1.re) •
          (P.x (P.T * p.1.im) + M p.1.im (cToVec p.2))) ((q.2.1 : ℂ) * Complex.I, q.2.2)) ρ b :=
  expDecayCInftyTube_rescaled_fderiv_sub_model_aux H hH P u hu hu0 d b hb ha hw N hN M hM hNM ρ hρ
