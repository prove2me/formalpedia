-- Prove2me | solution 1 for FiniteEnergyPlane.exists_lintegral_le_rpow_of_energy_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-24T23:17:51.767208+00:00
-- url     : https://prove2.me/submissions/0b5d7afb-c55a-4fce-a25e-a88e9e41e922

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_integral_mul_integral_bilin_circleMap_eq
import Theorems.Thm_FiniteEnergyPlane_abs_integral_bilin_sub_le_of_eq
import Theorems.Thm_FiniteEnergyPlane_monotoneOn_div_rpow_of_mul_le
import Theorems.Thm_FiniteEnergyPlane_setIntegral_annulus_eq_integral_circleMap
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real Interval

set_option maxHeartbeats 2000000 in
theorem exists_lintegral_le_rpow_of_energy_lt_top_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (v : ℂ → E) (hc : ContinuousOn v (ball 0 1))
    (hv : ContDiffOn ℝ ∞ v (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) v)
    (hmaps : Set.MapsTo v (ball 0 1) O)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) < ⊤)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * ‖fderiv ℝ v z‖ ≤ C) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ, ∀ s : ℝ, 0 < s → s ≤ r →
      ∫⁻ z in ball 0 s, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) ≤ ENNReal.ofReal (K * s ^ (2 * μ)) := by
  obtain ⟨hO, hJs, hJJ⟩ := hJ
  obtain ⟨rG, hrG, C, hC⟩ := hG
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hSo : IsOpen (ball (0 : ℂ) 1 \ {0}) := isOpen_ball.sdiff isClosed_singleton
  set x₀ := v 0 with hx₀
  have hx₀O : x₀ ∈ O := hmaps h0
  set J₀ := J x₀ with hJ₀
  have hJ₀J₀ : ∀ ξ, J₀ (J₀ ξ) = -ξ := fun ξ => by
    simpa using congrArg (fun T : E →L[ℝ] E => T ξ) (hJJ x₀ hx₀O)
  ------------------------------------------------------------------
  -- a constant 2-form taming `J₀`
  ------------------------------------------------------------------
  set n := Module.finrank ℝ E
  let T : E ≃L[ℝ] EuclideanSpace ℝ (Fin n) := toEuclidean
  let TL : E →L[ℝ] EuclideanSpace ℝ (Fin n) := T.toContinuousLinearMap
  let TS : EuclideanSpace ℝ (Fin n) →L[ℝ] E := T.symm.toContinuousLinearMap
  set m : ℝ := ‖TS‖ + 1 with hmdef
  have hm : 0 < m := by positivity
  have hTlow : ∀ ξ : E, ‖ξ‖ ≤ m * ‖TL ξ‖ := by
    intro ξ
    have h1 : TS (TL ξ) = ξ := T.symm_apply_apply ξ
    have h2 := TS.le_opNorm (TL ξ)
    rw [h1] at h2
    nlinarith [norm_nonneg (TL ξ)]
  let gB : E →L[ℝ] E →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp TL TL + (innerSL ℝ).bilinearComp (TL.comp J₀) (TL.comp J₀)
  have hg : ∀ ξ η, gB ξ η = inner ℝ (TL ξ) (TL η) + inner ℝ (TL (J₀ ξ)) (TL (J₀ η)) :=
    fun ξ η => rfl
  let σ : E →L[ℝ] E →L[ℝ] ℝ := gB.comp J₀
  have hσ : ∀ ξ η, σ ξ η = gB (J₀ ξ) η := fun ξ η => rfl
  have hσanti : ∀ ξ η, σ ξ η = -σ η ξ := by
    intro ξ η
    rw [hσ, hσ, hg, hg, hJ₀J₀, hJ₀J₀, map_neg, map_neg, inner_neg_left, inner_neg_left,
      real_inner_comm (TL (J₀ η)) (TL ξ), real_inner_comm (TL η) (TL (J₀ ξ))]
    ring
  set ε₀ : ℝ := 1 / (2 * m ^ 2 * (‖gB‖ * ‖J₀‖ + 1)) with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  have htame : ∀ A : E →L[ℝ] E, ‖A - J₀‖ ≤ ε₀ → ∀ ξ, ‖ξ‖ ^ 2 ≤ 2 * m ^ 2 * σ ξ (A ξ) := by
    intro A hA ξ
    have hsplit : σ ξ (A ξ) = gB (J₀ ξ) (J₀ ξ) + gB (J₀ ξ) ((A - J₀) ξ) := by
      rw [hσ, ← map_add]; congr 1; simp
    have hmain : ‖TL ξ‖ ^ 2 ≤ gB (J₀ ξ) (J₀ ξ) := by
      rw [hg, hJ₀J₀, map_neg, inner_neg_left, inner_neg_right, neg_neg,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      nlinarith [sq_nonneg ‖TL (J₀ ξ)‖]
    have herr : |gB (J₀ ξ) ((A - J₀) ξ)| ≤ ‖gB‖ * ‖J₀‖ * ε₀ * ‖ξ‖ ^ 2 := by
      have h1 := gB.le_opNorm₂ (J₀ ξ) ((A - J₀) ξ)
      have h2 : ‖J₀ ξ‖ ≤ ‖J₀‖ * ‖ξ‖ := J₀.le_opNorm ξ
      have h3 : ‖(A - J₀) ξ‖ ≤ ε₀ * ‖ξ‖ :=
        ((A - J₀).le_opNorm ξ).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
      rw [Real.norm_eq_abs] at h1
      calc |gB (J₀ ξ) ((A - J₀) ξ)| ≤ ‖gB‖ * ‖J₀ ξ‖ * ‖(A - J₀) ξ‖ := h1
        _ ≤ ‖gB‖ * (‖J₀‖ * ‖ξ‖) * (ε₀ * ‖ξ‖) := by gcongr
        _ = ‖gB‖ * ‖J₀‖ * ε₀ * ‖ξ‖ ^ 2 := by ring
    have hlow : ‖ξ‖ ^ 2 ≤ m ^ 2 * ‖TL ξ‖ ^ 2 := by
      have := hTlow ξ
      nlinarith [norm_nonneg ξ, norm_nonneg (TL ξ)]
    have hkey : ‖gB‖ * ‖J₀‖ * ε₀ * (2 * m ^ 2) ≤ 1 := by
      rw [hε₀]
      have hpos : 0 < 2 * m ^ 2 * (‖gB‖ * ‖J₀‖ + 1) := by positivity
      rw [show ‖gB‖ * ‖J₀‖ * (1 / (2 * m ^ 2 * (‖gB‖ * ‖J₀‖ + 1))) * (2 * m ^ 2) =
        (‖gB‖ * ‖J₀‖) / (‖gB‖ * ‖J₀‖ + 1) by field_simp]
      rw [div_le_one (by positivity)]; linarith
    have hab := neg_abs_le (gB (J₀ ξ) ((A - J₀) ξ))
    have hx2 : 0 ≤ ‖ξ‖ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hkey hx2]
  ------------------------------------------------------------------
  -- pointwise bound on the punctured disc of radius `r₁`
  ------------------------------------------------------------------
  have hJc : ContinuousAt (fun z => J (v z)) 0 :=
    (hJs.continuousOn.continuousAt (hO.mem_nhds hx₀O)).comp
      (hc.continuousAt (isOpen_ball.mem_nhds h0))
  obtain ⟨δJ, hδJ, hδJ'⟩ := Metric.continuousAt_iff.1 hJc ε₀ hε₀pos
  set r₁ : ℝ := min δJ 1 with hr₁
  have hr₁pos : 0 < r₁ := lt_min hδJ one_pos
  have hr₁1 : r₁ ≤ 1 := min_le_right _ _
  set β : ℝ := ‖J₀‖ + ε₀ with hβ
  set c₂ : ℝ := (1 + β) ^ 2 * (2 * m ^ 2) with hc₂
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hDI : ∀ z ∈ ball (0 : ℂ) 1 \ {0},
      fderiv ℝ v z Complex.I = J (v z) (fderiv ℝ v z 1) := by
    intro z hz
    have hd := (hhol z hz).2
    unfold JHolomorphic.dbarJ at hd
    have hvO : v z ∈ O := hmaps hz.1
    have hJz : ∀ ξ, J (v z) (J (v z) ξ) = -ξ := fun ξ => by
      simpa using congrArg (fun T : E →L[ℝ] E => T ξ) (hJJ (v z) hvO)
    have := congrArg (J (v z)) hd
    rw [map_add, hJz, map_zero] at this
    exact (sub_eq_zero.1 (by rw [sub_eq_neg_add]; simpa [add_comm] using this)).symm
  have hpt : ∀ z ∈ ball (0 : ℂ) 1 \ {0}, ‖z‖ < r₁ →
      ‖fderiv ℝ v z‖ ^ 2 ≤ c₂ * σ (fderiv ℝ v z 1) (fderiv ℝ v z Complex.I) := by
    intro z hz hzr
    set A := J (v z)
    have hA : ‖A - J₀‖ ≤ ε₀ := by
      have := hδJ' (show dist z 0 < δJ by
        rw [dist_zero_right]; exact lt_of_lt_of_le hzr (min_le_left _ _))
      rw [dist_eq_norm] at this; exact this.le
    have hAn : ‖A‖ ≤ β := by
      calc ‖A‖ = ‖(A - J₀) + J₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖A - J₀‖ + ‖J₀‖ := norm_add_le _ _
        _ ≤ β := by rw [hβ]; linarith
    set X := fderiv ℝ v z 1
    have hY : fderiv ℝ v z Complex.I = A X := hDI z hz
    have hLh : ∀ h : ℂ, fderiv ℝ v z h = h.re • X + h.im • A X := by
      intro h
      have e : h = h.re • (1 : ℂ) + h.im • Complex.I := by
        apply Complex.ext <;> simp
      conv_lhs => rw [e]
      rw [map_add, map_smul, map_smul, hY]
    have hDn : ‖fderiv ℝ v z‖ ≤ (1 + β) * ‖X‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun h => ?_)
      rw [hLh]
      have hre : |h.re| ≤ ‖h‖ := Complex.abs_re_le_norm h
      have him : |h.im| ≤ ‖h‖ := Complex.abs_im_le_norm h
      have hAX : ‖A X‖ ≤ β * ‖X‖ :=
        (A.le_opNorm X).trans (mul_le_mul_of_nonneg_right hAn (norm_nonneg _))
      calc ‖h.re • X + h.im • A X‖ ≤ |h.re| * ‖X‖ + |h.im| * (β * ‖X‖) := by
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_smul, Real.norm_eq_abs]
            · rw [norm_smul, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_left hAX (abs_nonneg _)
        _ ≤ ‖h‖ * ‖X‖ + ‖h‖ * (β * ‖X‖) := by gcongr
        _ = (1 + β) * ‖X‖ * ‖h‖ := by ring
    have ht := htame A hA X
    rw [hY]
    calc ‖fderiv ℝ v z‖ ^ 2 ≤ ((1 + β) * ‖X‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hDn 2
      _ = (1 + β) ^ 2 * ‖X‖ ^ 2 := by ring
      _ ≤ (1 + β) ^ 2 * (2 * m ^ 2 * σ X (A X)) := by gcongr
      _ = c₂ * σ X (A X) := by rw [hc₂]; ring
  ------------------------------------------------------------------
  -- continuity on circles
  ------------------------------------------------------------------
  have hD1 : ContinuousOn (fderiv ℝ v) (ball (0 : ℂ) 1 \ {0}) :=
    hv.continuousOn_fderiv_of_isOpen hSo (by exact_mod_cast le_top)
  have hcm : ∀ ρ θ : ℝ, 0 < ρ → ρ < 1 → circleMap 0 ρ θ ∈ ball (0 : ℂ) 1 \ {0} := by
    intro ρ θ h1 h2
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos h1]; exact h2
    · intro h; have := congrArg norm h
      simp only [mem_singleton_iff] at h
      rw [norm_circleMap_zero] at this; simp at this; linarith [abs_of_pos h1]
  have hcmc : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    unfold circleMap; fun_prop
  have hpar : ∀ g : ℂ → ℝ, ContinuousOn g (ball (0 : ℂ) 1 \ {0}) →
      ContinuousOn (fun ρ => ∫ θ in (0 : ℝ)..2 * π, g (circleMap 0 ρ θ)) (Ioo 0 1) := by
    intro g hg
    rw [continuousOn_iff_continuous_restrict]
    let G : Ioo (0 : ℝ) 1 → ℝ → ℝ := fun ρ θ => g (circleMap 0 ρ θ)
    have hGc : Continuous G.uncurry := by
      have : G.uncurry = g ∘ (fun p : Ioo (0 : ℝ) 1 × ℝ => circleMap 0 (p.1 : ℝ) p.2) := rfl
      rw [this]
      refine hg.comp_continuous (hcmc.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)) (fun p => hcm _ _ p.1.2.1 p.1.2.2)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hGc 0 (2 * π)
  set nrm : ℂ → ℝ := fun z => ‖fderiv ℝ v z‖ ^ 2 with hnrm
  set aF : ℂ → ℝ := fun z => σ (fderiv ℝ v z 1) (fderiv ℝ v z Complex.I) with haF
  have hnrmc : ContinuousOn nrm (ball (0 : ℂ) 1 \ {0}) := hD1.norm.pow 2
  have haFc : ContinuousOn aF (ball (0 : ℂ) 1 \ {0}) :=
    (σ.continuous.comp_continuousOn (hD1.clm_apply continuousOn_const)).clm_apply
      (hD1.clm_apply continuousOn_const)
  have hcirc : ∀ g : ℂ → ℝ, ContinuousOn g (ball (0 : ℂ) 1 \ {0}) → ∀ ρ, 0 < ρ → ρ < 1 →
      Continuous (fun θ => g (circleMap 0 ρ θ)) := fun g hg ρ h1 h2 =>
    hg.comp_continuous (continuous_circleMap 0 ρ) (fun θ => hcm ρ θ h1 h2)
  set e : ℝ → ℝ := fun ρ => ρ * ∫ θ in (0 : ℝ)..2 * π, nrm (circleMap 0 ρ θ) with he_def
  have he : ContinuousOn e (Ioo 0 1) := continuousOn_id.mul (hpar nrm hnrmc)
  have he0 : ∀ ρ, 0 ≤ ρ → 0 ≤ e ρ := fun ρ hρ =>
    mul_nonneg hρ (intervalIntegral.integral_nonneg (by positivity) (fun θ _ => by positivity))
  ------------------------------------------------------------------
  -- the energy function
  ------------------------------------------------------------------
  set Ebal : ℝ → ℝ≥0∞ := fun s => ∫⁻ z in ball 0 s, ENNReal.ofReal (nrm z) with hEbal
  set Er : ℝ → ℝ := fun s => (Ebal s).toReal with hEr
  have hball1 : Ebal 1 = ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (nrm z) :=
    (setLIntegral_congr (sdiff_null_ae_eq_self (measure_singleton 0))).symm
  have hfin : ∀ s, s ≤ 1 → Ebal s ≠ ⊤ := by
    intro s hs
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_set (ball_subset_ball hs))
    show Ebal 1 ≠ ⊤
    rw [hball1]; exact hE.ne
  have hdiff : ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 → Er b = Er a + ∫ r in a..b, e r := by
    intro a b ha hab hb
    have hsub : closedBall (0 : ℂ) b \ ball 0 a ⊆ ball 0 1 \ {0} := by
      rintro z ⟨hz1, hz2⟩
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall, dist_zero_right] at hz1
        rw [mem_ball, dist_zero_right]; linarith
      · rintro rfl; exact hz2 (mem_ball_self ha)
    have hcont : ContinuousOn nrm (closedBall (0 : ℂ) b \ ball 0 a) := hnrmc.mono hsub
    have hint : IntegrableOn nrm (ball (0 : ℂ) b \ ball 0 a) :=
      (hcont.integrableOn_compact (isCompact_closedBall _ _ |>.diff isOpen_ball)).mono_set
        (diff_subset_diff_left ball_subset_closedBall)
    have hU : ball (0 : ℂ) b = ball 0 a ∪ (ball 0 b \ ball 0 a) :=
      (union_diff_cancel (ball_subset_ball hab)).symm
    have h1 : Ebal b = Ebal a + ∫⁻ z in ball 0 b \ ball 0 a, ENNReal.ofReal (nrm z) := by
      show (∫⁻ z in ball 0 b, ENNReal.ofReal (nrm z)) = _
      conv_lhs => rw [hU]
      exact lintegral_union (measurableSet_ball.diff measurableSet_ball) disjoint_sdiff_right
    have h2 : ∫⁻ z in ball 0 b \ ball 0 a, ENNReal.ofReal (nrm z) =
        ENNReal.ofReal (∫ z in ball 0 b \ ball 0 a, nrm z) :=
      (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun z => by positivity))).symm
    have hnn : 0 ≤ ∫ z in ball 0 b \ ball 0 a, nrm z :=
      setIntegral_nonneg (measurableSet_ball.diff measurableSet_ball) (fun z _ => by positivity)
    have h3 := setIntegral_annulus_eq_integral_circleMap ha hab hcont
    show (Ebal b).toReal = (Ebal a).toReal + _
    rw [h1, h2, ENNReal.toReal_add (hfin a (by linarith)) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hnn, h3]
    simp only [smul_eq_mul, he_def]
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt Er (e s) s := by
    intro s hs
    have ha : 0 < s / 2 := by linarith [hs.1]
    have hsub : uIcc (s / 2) s ⊆ Ioo 0 1 := by
      rw [uIcc_of_le (by linarith [hs.1])]
      exact Icc_subset_Ioo ha hs.2
    have hd := (intervalIntegral.integral_hasDerivAt_right
      ((he.mono hsub).intervalIntegrable)
      (he.stronglyMeasurableAtFilter isOpen_Ioo s hs)
      (he.continuousAt (Ioo_mem_nhds hs.1 hs.2))).const_add (Er (s / 2))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (show s / 2 < s by linarith [hs.1]) hs.2] with t ht
    exact hdiff (s / 2) t ha ht.1.le ht.2
  ------------------------------------------------------------------
  -- boundary terms
  ------------------------------------------------------------------
  set Fb : ℝ → ℝ := fun ρ => ∫ θ in (0 : ℝ)..2 * π, σ (v (circleMap 0 ρ θ) - x₀)
      (fderiv ℝ v (circleMap 0 ρ θ) (circleMap 0 ρ θ * Complex.I)) with hFb
  have h2inf : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by norm_cast <;> exact le_top
  have hstokes : ∀ ε s : ℝ, 0 < ε → ε ≤ s → s < r₁ →
      ∫ r in ε..s, e r ≤ c₂ * ((1 / 2) * Fb s - (1 / 2) * Fb ε) := by
    intro ε s hε hεs hs
    have hs1 : s < 1 := lt_of_lt_of_le hs hr₁1
    have hK := integral_mul_integral_bilin_circleMap_eq σ hσanti hSo
      (hv.of_le h2inf) hε hεs
      (fun z h1 h2 => ⟨by rw [mem_ball, dist_zero_right]; linarith,
        by rintro rfl; simp at h1; linarith⟩) x₀
    have hsub : uIcc ε s ⊆ Ioo 0 1 := by
      rw [uIcc_of_le hεs]; exact Icc_subset_Ioo hε hs1
    rw [show c₂ * ((1 / 2) * Fb s - (1 / 2) * Fb ε) =
      c₂ * ∫ r in ε..s, r * ∫ θ in (0 : ℝ)..2 * π, aF (circleMap 0 r θ) by rw [hK] ]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hεs ((he.mono hsub).intervalIntegrable)
      (((continuousOn_id.mul (hpar aF haFc)).mono hsub).const_smul c₂ |>.intervalIntegrable)
      (fun ρ hρ => ?_)
    have hρ0 : 0 < ρ := lt_of_lt_of_le hε hρ.1
    have hρ1 : ρ < 1 := lt_of_le_of_lt hρ.2 hs1
    have hin : ∫ θ in (0 : ℝ)..2 * π, nrm (circleMap 0 ρ θ) ≤
        ∫ θ in (0 : ℝ)..2 * π, c₂ * aF (circleMap 0 ρ θ) := by
      refine intervalIntegral.integral_mono_on (by positivity)
        ((hcirc nrm hnrmc ρ hρ0 hρ1).intervalIntegrable _ _)
        (((hcirc aF haFc ρ hρ0 hρ1).const_smul c₂).intervalIntegrable _ _) (fun θ _ => ?_)
      refine hpt _ (hcm ρ θ hρ0 hρ1) ?_
      rw [norm_circleMap_zero, abs_of_pos hρ0]; exact lt_of_le_of_lt hρ.2 hs
    rw [intervalIntegral.integral_const_mul] at hin
    show ρ * _ ≤ c₂ * (ρ * _)
    nlinarith [mul_le_mul_of_nonneg_left hin hρ0.le]
  have houter : ∀ s : ℝ, 0 < s → s < 1 → (1 / 2) * Fb s ≤ π * ‖σ‖ * s * e s := by
    intro s hs hs1
    set γ : ℝ → E := fun θ => v (circleMap 0 s θ)
    set γ' : ℝ → E := fun θ => fderiv ℝ v (circleMap 0 s θ) (circleMap 0 s θ * Complex.I)
    have hγ : ∀ θ ∈ Icc (0 : ℝ) (2 * π), HasDerivAt γ (γ' θ) θ := fun θ _ =>
      ((hhol _ (hcm s θ hs hs1)).1.hasFDerivAt).comp_hasDerivAt θ (hasDerivAt_circleMap 0 s θ)
    have hγ'c : Continuous γ' :=
      (hD1.comp_continuous (continuous_circleMap 0 s) (fun θ => hcm s θ hs hs1)).clm_apply
        ((continuous_circleMap 0 s).mul continuous_const)
    have hper : γ 0 = γ (2 * π) := by
      show v _ = v _
      rw [show (2 * π : ℝ) = 0 + 2 * π by ring, periodic_circleMap 0 s 0]
    have hCb := abs_integral_bilin_sub_le_of_eq σ (by positivity : (0 : ℝ) ≤ 2 * π) hγ
      hγ'c.continuousOn hper x₀
    have hsq : ∫ θ in (0 : ℝ)..2 * π, ‖γ' θ‖ ^ 2 ≤ s * e s := by
      have : ∫ θ in (0 : ℝ)..2 * π, ‖γ' θ‖ ^ 2 ≤
          ∫ θ in (0 : ℝ)..2 * π, s ^ 2 * nrm (circleMap 0 s θ) := by
        refine intervalIntegral.integral_mono_on (by positivity)
          ((hγ'c.norm.pow 2).intervalIntegrable _ _)
          (((hcirc nrm hnrmc s hs hs1).const_smul (s ^ 2)).intervalIntegrable _ _)
          (fun θ _ => ?_)
        have h1 : ‖γ' θ‖ ≤ ‖fderiv ℝ v (circleMap 0 s θ)‖ * s := by
          refine ((fderiv ℝ v _).le_opNorm _).trans (le_of_eq ?_)
          rw [norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos hs]
        have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        show ‖γ' θ‖ ^ 2 ≤ s ^ 2 * ‖fderiv ℝ v (circleMap 0 s θ)‖ ^ 2
        nlinarith
      rw [intervalIntegral.integral_const_mul] at this
      show _ ≤ s * (s * _)
      nlinarith
    have hFb' : Fb s = ∫ θ in (0 : ℝ)..2 * π, σ (γ θ - x₀) (γ' θ) := rfl
    rw [hFb']
    have := le_abs_self (∫ θ in (0 : ℝ)..2 * π, σ (γ θ - x₀) (γ' θ))
    have hσ0 : 0 ≤ ‖σ‖ := norm_nonneg σ
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg (norm_nonneg σ) (by linarith [Real.pi_pos]) : (0 : ℝ) ≤ ‖σ‖ * (2 * π - 0))]
  have hinner : Tendsto Fb (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro η hη
    set C' : ℝ := max C 0 + 1
    have hC' : 0 < C' := by positivity
    set κ : ℝ := η / (2 * π * (‖σ‖ + 1) * C') with hκ
    have hκ0 : 0 < κ := by positivity
    obtain ⟨δv, hδv, hδv'⟩ := Metric.continuousAt_iff.1
      (hc.continuousAt (isOpen_ball.mem_nhds h0)) κ hκ0
    refine ⟨min δv (min rG 1), lt_min hδv (lt_min hrG one_pos), fun ε hε hεd => ?_⟩
    have hε0 : 0 < ε := hε
    rw [dist_zero_right] at hεd ⊢
    rw [Real.norm_eq_abs, abs_of_pos hε0] at hεd
    have hε1 : ε < 1 := lt_of_lt_of_le hεd ((min_le_right _ _).trans (min_le_right _ _))
    have hεG : ε < rG := lt_of_lt_of_le hεd ((min_le_right _ _).trans (min_le_left _ _))
    have hεv : ε < δv := lt_of_lt_of_le hεd (min_le_left _ _)
    have hbd : ∀ θ ∈ Ι (0 : ℝ) (2 * π), ‖σ (v (circleMap 0 ε θ) - x₀)
        (fderiv ℝ v (circleMap 0 ε θ) (circleMap 0 ε θ * Complex.I))‖ ≤ ‖σ‖ * κ * C' := by
      intro θ _
      set z := circleMap 0 ε θ
      have hz : ‖z‖ = ε := by rw [norm_circleMap_zero, abs_of_pos hε0]
      have hz0 : z ≠ 0 := (hcm ε θ hε0 hε1).2
      have h1 : ‖v z - x₀‖ ≤ κ := by
        have := hδv' (show dist z 0 < δv by rw [dist_zero_right, hz]; exact hεv)
        rw [dist_eq_norm] at this; exact this.le
      have h2 : ‖fderiv ℝ v z (z * Complex.I)‖ ≤ C' := by
        refine ((fderiv ℝ v z).le_opNorm _).trans ?_
        rw [norm_mul, Complex.norm_I, mul_one, mul_comm]
        exact (hC z hz0 (hz ▸ hεG)).trans ((le_max_left _ _).trans (by linarith))
      calc _ ≤ ‖σ‖ * ‖v z - x₀‖ * ‖fderiv ℝ v z (z * Complex.I)‖ := σ.le_opNorm₂ _ _
        _ ≤ ‖σ‖ * κ * C' := by gcongr
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    have hlt : ‖σ‖ * κ * C' * |2 * π - 0| < η := by
      rw [sub_zero, abs_of_pos (by positivity), hκ]
      have hpos : 0 < 2 * π * (‖σ‖ + 1) * C' := by positivity
      rw [show ‖σ‖ * (η / (2 * π * (‖σ‖ + 1) * C')) * C' * (2 * π) =
        η * (‖σ‖ / (‖σ‖ + 1)) by field_simp]
      have : ‖σ‖ / (‖σ‖ + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
      nlinarith
    exact lt_of_le_of_lt hI hlt
  have hEr0 : Tendsto Er (𝓝[>] 0) (𝓝 0) := by
    set μB := volume.restrict (ball (0 : ℂ) 1 \ {0})
    have hfinB : ∫⁻ z, ENNReal.ofReal (nrm z) ∂μB ≠ ⊤ := hE.ne
    have hmeas : Tendsto (μB ∘ fun s : ℝ => ball (0 : ℂ) s) (𝓝[>] 0) (𝓝 0) := by
      have hvol : Tendsto (fun s : ℝ => ENNReal.ofReal (s ^ Module.finrank ℝ ℂ) *
          volume (ball (0 : ℂ) 1)) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun s : ℝ => ENNReal.ofReal (s ^ Module.finrank ℝ ℂ)) (𝓝[>] 0) (𝓝 0) := by
          rw [← ENNReal.ofReal_zero]
          refine ENNReal.tendsto_ofReal ?_
          have hc0 : Continuous (fun s : ℝ => s ^ Module.finrank ℝ ℂ) := continuous_pow _
          have := hc0.tendsto 0
          rw [Complex.finrank_real_complex] at this ⊢
          simpa using this.mono_left nhdsWithin_le_nhds
        simpa using ENNReal.Tendsto.mul_const this (Or.inr measure_ball_lt_top.ne)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hvol
        (Eventually.of_forall (fun _ => by simp)) ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [Function.comp_apply, ← Measure.addHaar_ball_of_pos volume 0 hs]
      exact Measure.restrict_apply_le _ _
    have hT := tendsto_setLIntegral_zero hfinB hmeas
    have hEq : ∀ᶠ s in 𝓝[>] (0 : ℝ), Ebal s = ∫⁻ z in ball 0 s, ENNReal.ofReal (nrm z) ∂μB := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
      rw [Measure.restrict_restrict measurableSet_ball]
      have : ball (0 : ℂ) s ∩ (ball 0 1 \ {0}) = ball 0 s \ {0} := by
        ext z; simp only [mem_inter_iff, mem_diff, mem_ball, dist_zero_right]
        constructor
        · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith [hs.2], h3⟩
      rw [this]
      exact (setLIntegral_congr (sdiff_null_ae_eq_self (measure_singleton 0))).symm
    have hT' : Tendsto Ebal (𝓝[>] 0) (𝓝 0) := (tendsto_congr' hEq).2 hT
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT'
    rw [ENNReal.toReal_zero] at h
    exact h
  ------------------------------------------------------------------
  -- the differential inequality and its integration
  ------------------------------------------------------------------
  set Acst : ℝ := c₂ * (π * ‖σ‖) with hAcst
  have hA0 : 0 ≤ Acst := by positivity
  have hineq0 : ∀ s ∈ Ioo (0 : ℝ) r₁, Er s ≤ Acst * s * e s := by
    intro s hs
    have hs1 : s < 1 := lt_of_lt_of_le hs.2 hr₁1
    have hlim : Tendsto (fun ε => Acst * s * e s + (Er ε - c₂ * ((1 / 2) * Fb ε))) (𝓝[>] 0)
        (𝓝 (Acst * s * e s + (0 - c₂ * ((1 / 2) * 0)))) :=
      tendsto_const_nhds.add (hEr0.sub ((tendsto_const_nhds.mul hinner).const_mul c₂))
    simp only [mul_zero, sub_zero, add_zero] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hs.1] with ε hε
    have h1 := hdiff ε s hε.1 hε.2.le hs1
    have h2 := hstokes ε s hε.1 hε.2.le hs.2
    have h3 := houter s hs.1 hs1
    have : c₂ * ((1 / 2) * Fb s) ≤ c₂ * (π * ‖σ‖ * s * e s) := mul_le_mul_of_nonneg_left h3 hc₂0
    rw [hAcst]
    nlinarith
  set α : ℝ := 1 / (Acst + 1) with hα
  have hαpos : 0 < α := by positivity
  have hineq : ∀ s ∈ Ioo (0 : ℝ) r₁, α * Er s ≤ s * e s := by
    intro s hs
    have h1 := hineq0 s hs
    have hse : 0 ≤ s * e s := mul_nonneg hs.1.le (he0 s hs.1.le)
    have h2 : Er s ≤ (Acst + 1) * (s * e s) := by nlinarith
    calc α * Er s ≤ α * ((Acst + 1) * (s * e s)) := mul_le_mul_of_nonneg_left h2 hαpos.le
      _ = s * e s := by rw [hα]; field_simp
  have hmono := monotoneOn_div_rpow_of_mul_le
    (fun s hs => hderiv s ⟨hs.1, lt_of_lt_of_le hs.2 hr₁1⟩) hineq
  set r : ℝ := r₁ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrr : r < r₁ := by linarith
  refine ⟨α / 2, by positivity, r, hr0, Er r / r ^ α, fun s hs hsr => ?_⟩
  have hsr' : s ∈ Ioo (0 : ℝ) r₁ := ⟨hs, lt_of_le_of_lt hsr hrr⟩
  have h1 := hmono hsr' ⟨hr0, hrr⟩ hsr
  have hsα : 0 < s ^ α := Real.rpow_pos_of_pos hs α
  have h2 : Er s ≤ Er r / r ^ α * s ^ α := by
    have := (div_le_iff₀ hsα).1 h1
    simpa using this
  rw [show 2 * (α / 2) = α by ring]
  have hfs : Ebal s ≠ ⊤ := hfin s (by linarith [hsr'.2])
  calc ∫⁻ z in ball 0 s, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) = ENNReal.ofReal (Er s) :=
        (ENNReal.ofReal_toReal hfs).symm
    _ ≤ ENNReal.ofReal (Er r / r ^ α * s ^ α) := ENNReal.ofReal_le_ofReal h2

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (v : ℂ → E) (hc : ContinuousOn v (ball 0 1))
    (hv : ContDiffOn ℝ ∞ v (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) v)
    (hmaps : Set.MapsTo v (ball 0 1) O)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) < ⊤)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * ‖fderiv ℝ v z‖ ≤ C) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ r : ℝ, 0 < r ∧ ∃ K : ℝ, ∀ s : ℝ, 0 < s → s ≤ r →
      ∫⁻ z in ball 0 s, ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) ≤ ENNReal.ofReal (K * s ^ (2 * μ)) :=
  exists_lintegral_le_rpow_of_energy_lt_top_aux J O hJ v hc hv hhol hmaps hE hG
