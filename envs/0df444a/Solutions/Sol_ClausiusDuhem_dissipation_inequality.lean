-- Prove2me | solution 1 for ClausiusDuhem.dissipation_inequality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T11:46:51.40143+00:00
-- url     : https://prove2.me/submissions/ca8cdfb4-9202-4d75-aa59-6ab67b8373a6

import Definitions.Def_ClausiusDuhem_thermo_process
namespace LU2CD

open ClausiusDuhem MeasureTheory

theorem slice {β : Type} [NormedAddCommGroup β] [NormedSpace ℝ β]
    (φ : ℝ → Space → β) (h : IsC1Field φ) (t : ℝ) : ContDiff ℝ 1 (φ t) :=
  h.comp (contDiff_const.prodMk contDiff_id)

theorem tdiff (φ : ℝ → Space → ℝ) (h : IsC1Field φ) (t : ℝ) (x : Space) :
    DifferentiableAt ℝ (fun τ => φ τ x) t := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × Space => φ p.1 p.2) (t, x) :=
    (h.differentiable one_ne_zero) (t, x)
  have h1 : HasDerivAt ((fun p : ℝ × Space => φ p.1 p.2) ∘ fun s => (s, x))
      (fderiv ℝ (fun p : ℝ × Space => φ p.1 p.2) (t, x) ((1 : ℝ), (0 : Space))) t :=
    hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact h1.differentiableAt

theorem timeDeriv_eq (φ : ℝ → Space → ℝ) (h : IsC1Field φ) (t : ℝ) (x : Space) :
    timeDeriv φ t x =
      fderiv ℝ (fun p : ℝ × Space => φ p.1 p.2) (t, x) ((1 : ℝ), (0 : Space)) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × Space => φ p.1 p.2) (t, x) :=
    (h.differentiable one_ne_zero) (t, x)
  have h1 : HasDerivAt ((fun p : ℝ × Space => φ p.1 p.2) ∘ fun s => (s, x))
      (fderiv ℝ (fun p : ℝ × Space => φ p.1 p.2) (t, x) ((1 : ℝ), (0 : Space))) t :=
    hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact h1.deriv

theorem timeDeriv_cont (φ : ℝ → Space → ℝ) (h : IsC1Field φ) (t : ℝ) :
    Continuous (fun y => timeDeriv φ t y) := by
  rw [funext (timeDeriv_eq φ h t)]
  exact ((h.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
    (continuous_const.prodMk continuous_id)

theorem div_eq (F : Space → Fin 3 → ℝ) (hF : ContDiff ℝ 1 F) (x : Space) :
    div F x = ∑ i, fderiv ℝ F x (Pi.single i 1) i := by
  unfold div
  apply Finset.sum_congr rfl
  intro i _
  unfold partialDeriv
  have h := (hF.differentiable one_ne_zero x).hasFDerivAt
  have h2 : HasFDerivAt ((fun v : Fin 3 → ℝ => v i) ∘ F)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ F x)) x :=
    (hasFDerivAt_apply i (F x)).comp x h
  rw [show (fun y => F y i) = (fun v : Fin 3 → ℝ => v i) ∘ F from rfl, h2.fderiv]
  rfl

theorem div_cont (F : Space → Fin 3 → ℝ) (hF : ContDiff ℝ 1 F) : Continuous (div F) := by
  have : div F = fun x => ∑ i, fderiv ℝ F x (Pi.single i 1) i := funext (div_eq F hF)
  rw [this]
  have hcont : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  apply continuous_finset_sum
  intro i _
  exact (continuous_apply i).comp (hcont.clm_apply continuous_const)

theorem flux_eq (F : Space → Fin 3 → ℝ) (hF : ContDiff ℝ 1 F) (a b : Space) (hab : a ≤ b) :
    boxOutwardFlux F a b = ∫ x in Set.Icc a b, div F x := by
  rw [funext (div_eq F hF)]
  unfold boxOutwardFlux
  have hcont : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  refine (MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable a b hab F (fderiv ℝ F) ∅
    Set.countable_empty hF.continuous.continuousOn ?_ ?_).symm
  · intro x _
    exact (hF.differentiable one_ne_zero x).hasFDerivAt
  · apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply Continuous.continuousOn
    apply continuous_finset_sum
    intro i _
    exact (continuous_apply i).comp (hcont.clm_apply continuous_const)

theorem amount_deriv (φ : ℝ → Space → ℝ) (hφ : IsC1Field φ) (a b : Space) (t : ℝ) :
    deriv (fun τ => ∫ x in Set.Icc a b, φ τ x) t = ∫ x in Set.Icc a b, timeDeriv φ t x := by
  set Φ : ℝ × Space → ℝ := fun p => φ p.1 p.2 with hΦ
  have hc : ContDiff ℝ 1 Φ := hφ
  have hd : Differentiable ℝ Φ := hc.differentiable one_ne_zero
  set G : ℝ × Space → ℝ := fun q => fderiv ℝ Φ q ((1 : ℝ), (0 : Space))
  have hG : Continuous G := (hc.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hTD : ∀ s y, timeDeriv φ s y = G (s, y) := fun s y => timeDeriv_eq φ hφ s y
  have hK : IsCompact (Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc a b) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  have hρs : ∀ s, Continuous (φ s) := fun s => (slice φ hφ s).continuous
  have hGs : ∀ s, Continuous (fun y => G (s, y)) := fun s =>
    hG.comp (continuous_const.prodMk continuous_id)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc a b)) (F := fun s y => φ s y)
    (F' := fun s y => timeDeriv φ s y) (x₀ := t) (bound := fun _ => M)
    (s := Metric.ball t 1) (Metric.ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s => (hρs s).aestronglyMeasurable)
    ((hρs t).continuousOn.integrableOn_compact isCompact_Icc)
    (by simp_rw [hTD]; exact (hGs t).aestronglyMeasurable)
    (by
      refine (ae_restrict_of_forall_mem measurableSet_Icc ?_)
      intro y hy s hs
      rw [hTD]
      apply hM
      refine ⟨?_, hy⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
      constructor <;> linarith)
    (continuous_const.continuousOn.integrableOn_compact isCompact_Icc)
    (Filter.Eventually.of_forall fun y s _ => (tdiff φ hφ s y).hasDerivAt)
  exact key.2.deriv

theorem pos_box (f : Space → ℝ) (hf : Continuous f) (x : Space) (hx : 0 < f x) :
    ∃ a b : Space, (∀ i, a i < b i) ∧ 0 < ∫ y in Set.Icc a b, f y := by
  have hev : ∀ᶠ y in nhds x, f x / 2 < f y :=
    hf.continuousAt.eventually (lt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨fun i => x i - ε / 2, fun i => x i + ε / 2, fun i => by linarith, ?_⟩
  have hsub : ∀ y ∈ Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2), f x / 2 ≤ f y := by
    intro y hy
    apply le_of_lt
    apply hball
    rw [dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, abs_lt]
    have h1 := hy.1 i
    have h2 := hy.2 i
    simp only at h1 h2
    constructor <;> linarith
  have hvol : 0 < volume.real (Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2)) := by
    rw [measureReal_def, Real.volume_Icc_pi]
    apply ENNReal.toReal_pos
    · rw [Finset.prod_ne_zero_iff]
      intro i _
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
    · exact ENNReal.prod_ne_top (fun i _ => ENNReal.ofReal_ne_top)
  have hmono : ∫ y in Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2), f x / 2 ≤
      ∫ y in Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2), f y := by
    apply setIntegral_mono_on
    · exact continuous_const.continuousOn.integrableOn_compact isCompact_Icc
    · exact hf.continuousOn.integrableOn_compact isCompact_Icc
    · exact measurableSet_Icc
    · exact hsub
  rw [setIntegral_const, smul_eq_mul] at hmono
  have : 0 < volume.real (Set.Icc (fun i => x i - ε / 2) (fun i => x i + ε / 2)) * (f x / 2) :=
    mul_pos hvol (by linarith)
  linarith

theorem nonneg_of_box (f : Space → ℝ) (hf : Continuous f)
    (h : ∀ a b : Space, (∀ i, a i < b i) → 0 ≤ ∫ y in Set.Icc a b, f y) (x : Space) :
    0 ≤ f x := by
  by_contra hne
  obtain ⟨a, b, hab, hpos⟩ := pos_box (fun y => -f y) hf.neg x (by linarith)
  rw [integral_neg] at hpos
  linarith [h a b hab]

theorem loc (P : ThermoProcess) (hP : P.Smooth)
    (hT : ∀ t x, 0 < P.temp t x) (hInt : P.IntegralEntropyInequality) :
    ∀ t x, timeDeriv (fun τ y => P.rho τ y * P.eta τ y) t x ≥
      -div (fun y => (P.rho t y * P.eta t y) • P.vel t y) x
      - div (fun y => (P.temp t y)⁻¹ • P.heatFlux t y) x
      + P.rho t x * P.source t x / P.temp t x := by
  obtain ⟨hρ, hη, hv, hq, hTc, -, hs⟩ := hP
  intro t x
  have hρη : IsC1Field (fun τ y => P.rho τ y * P.eta τ y) := hρ.mul hη
  have hF1 : ContDiff ℝ 1 (fun y => (P.rho t y * P.eta t y) • P.vel t y) :=
    ((slice _ hρ t).mul (slice _ hη t)).smul (slice _ hv t)
  have hF2 : ContDiff ℝ 1 (fun y => (P.temp t y)⁻¹ • P.heatFlux t y) :=
    ((slice _ hTc t).inv (fun y => (hT t y).ne')).smul (slice _ hq t)
  have hsc : Continuous (fun y => P.source t y) :=
    hs.comp (continuous_const.prodMk continuous_id)
  have c1 := timeDeriv_cont _ hρη t
  have c2 := div_cont _ hF1
  have c3 := div_cont _ hF2
  have c4 : Continuous (fun y => P.rho t y * P.source t y / P.temp t y) :=
    ((slice _ hρ t).continuous.mul hsc).div (slice _ hTc t).continuous (fun y => (hT t y).ne')
  have hg : Continuous (fun y => timeDeriv (fun τ y => P.rho τ y * P.eta τ y) t y
      + div (fun y => (P.rho t y * P.eta t y) • P.vel t y) y
      + div (fun y => (P.temp t y)⁻¹ • P.heatFlux t y) y
      - P.rho t y * P.source t y / P.temp t y) := ((c1.add c2).add c3).sub c4
  have hbox : ∀ a b : Space, (∀ i, a i < b i) → 0 ≤ ∫ y in Set.Icc a b,
      (timeDeriv (fun τ y => P.rho τ y * P.eta τ y) t y
      + div (fun y => (P.rho t y * P.eta t y) • P.vel t y) y
      + div (fun y => (P.temp t y)⁻¹ • P.heatFlux t y) y
      - P.rho t y * P.source t y / P.temp t y) := by
    intro a b hab
    have hle : a ≤ b := fun i => (hab i).le
    have h := hInt a b hab t
    have e1 : deriv (fun τ => ∫ x in Set.Icc a b, P.rho τ x * P.eta τ x) t =
        ∫ y in Set.Icc a b, timeDeriv (fun τ y => P.rho τ y * P.eta τ y) t y :=
      amount_deriv _ hρη a b t
    rw [e1, flux_eq _ hF1 a b hle, flux_eq _ hF2 a b hle] at h
    have hint : ∀ f : Space → ℝ, Continuous f → IntegrableOn f (Set.Icc a b) :=
      fun f hf => hf.continuousOn.integrableOn_compact isCompact_Icc
    rw [integral_sub, integral_add, integral_add]
    · linarith
    all_goals first
      | exact hint _ c1 | exact hint _ c2 | exact hint _ c3 | exact hint _ c4
      | exact hint _ (c1.add c2) | exact hint _ ((c1.add c2).add c3)
  have := nonneg_of_box _ hg hbox x
  linarith

end LU2CD
namespace LU2CD2

open ClausiusDuhem

theorem pd_mul (f g : Space → ℝ) (x : Space) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (j : Fin 3) :
    partialDeriv (fun y => f y * g y) j x = partialDeriv f j x * g x + f x * partialDeriv g j x := by
  unfold partialDeriv
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem pd_inv (T : Space → ℝ) (x : Space) (hT : DifferentiableAt ℝ T x) (h0 : T x ≠ 0)
    (j : Fin 3) :
    partialDeriv (fun y => (T y)⁻¹) j x = -(T x ^ 2)⁻¹ * partialDeriv T j x := by
  unfold partialDeriv
  rw [show (fun y => (T y)⁻¹) = (fun u : ℝ => u⁻¹) ∘ T from rfl,
    fderiv_comp x (differentiableAt_inv h0) hT, fderiv_inv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

theorem alg (r h T ρt ηt et s DD : ℝ) (gρ gη ge gT v q dv dq : Fin 3 → ℝ) (hT : 0 < T)
    (loc : ρt * h + r * ηt ≥ -(∑ j, ((gρ j * h + r * gη j) * v j + r * h * dv j))
      - (∑ j, (-(T ^ 2)⁻¹ * gT j * q j + T⁻¹ * dq j)) + r * s / T)
    (mass : ρt + ∑ j, gρ j * v j + r * ∑ j, dv j = 0)
    (energy : r * (et + ∑ j, ge j * v j) - DD + ∑ j, dq j - r * s = 0) :
    0 ≤ r * (T * (ηt + ∑ j, gη j * v j) - (et + ∑ j, ge j * v j)) + DD
      - (∑ j, q j * gT j) / T := by
  have hu : T * T⁻¹ = 1 := mul_inv_cancel₀ hT.ne'
  have hM' : T * h * (ρt + ∑ j, gρ j * v j + r * ∑ j, dv j) = 0 := by rw [mass]; ring
  have hC : (T * T⁻¹ - 1) * (-(T⁻¹ * ∑ j, gT j * q j) + ∑ j, dq j - r * s) = 0 := by
    rw [hu]; ring
  have hprod := mul_nonneg hT.le (sub_nonneg.2 loc)
  simp only [Fin.sum_univ_three, div_eq_mul_inv, ← inv_pow] at *
  linarith

end LU2CD2

open ClausiusDuhem LU2CD LU2CD2 in
theorem solution (P : ThermoProcess) (hP : P.Smooth)
    (hT : ∀ t x, 0 < P.temp t x) (hInt : P.IntegralEntropyInequality)
    (hMass : P.MassConservation) (hEnergy : P.EnergyBalance) :
    ∀ t x, 0 ≤ P.dissipation t x := by
  intro t x
  have hl := loc P hP hT hInt t x
  obtain ⟨hρ, hη, hv, hq, hTc, -, -⟩ := hP
  have dρ : DifferentiableAt ℝ (P.rho t) x := (slice _ hρ t).differentiable one_ne_zero x
  have dη : DifferentiableAt ℝ (P.eta t) x := (slice _ hη t).differentiable one_ne_zero x
  have dT : DifferentiableAt ℝ (P.temp t) x := (slice _ hTc t).differentiable one_ne_zero x
  have dv : ∀ j, DifferentiableAt ℝ (fun y => P.vel t y j) x := fun j =>
    differentiableAt_pi.1 ((slice _ hv t).differentiable one_ne_zero x) j
  have dq : ∀ j, DifferentiableAt ℝ (fun y => P.heatFlux t y j) x := fun j =>
    differentiableAt_pi.1 ((slice _ hq t).differentiable one_ne_zero x) j
  have hTD : timeDeriv (fun τ y => P.rho τ y * P.eta τ y) t x =
      timeDeriv P.rho t x * P.eta t x + P.rho t x * timeDeriv P.eta t x := by
    unfold timeDeriv
    exact deriv_fun_mul (tdiff _ hρ t x) (tdiff _ hη t x)
  have hd1 : div (fun y => (P.rho t y * P.eta t y) • P.vel t y) x =
      ∑ j, ((partialDeriv (P.rho t) j x * P.eta t x + P.rho t x * partialDeriv (P.eta t) j x)
        * P.vel t x j + P.rho t x * P.eta t x * partialDeriv (fun y => P.vel t y j) j x) := by
    unfold div
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [pd_mul (fun y => P.rho t y * P.eta t y) (fun y => P.vel t y j) x (dρ.mul dη) (dv j),
      pd_mul (P.rho t) (P.eta t) x dρ dη]
  have hd2 : div (fun y => (P.temp t y)⁻¹ • P.heatFlux t y) x =
      ∑ j, (-(P.temp t x ^ 2)⁻¹ * partialDeriv (P.temp t) j x * P.heatFlux t x j
        + (P.temp t x)⁻¹ * partialDeriv (fun y => P.heatFlux t y j) j x) := by
    unfold div
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [pd_mul (fun y => (P.temp t y)⁻¹) (fun y => P.heatFlux t y j) x
      (dT.inv (hT t x).ne') (dq j), pd_inv (P.temp t) x dT (hT t x).ne']
  rw [hTD, hd1, hd2] at hl
  exact alg (P.rho t x) (P.eta t x) (P.temp t x) (timeDeriv P.rho t x) (timeDeriv P.eta t x)
    (timeDeriv P.energy t x) (P.source t x)
    (doubleDot (P.stress t x) (velocityGradient (P.vel t) x))
    (fun j => partialDeriv (P.rho t) j x) (fun j => partialDeriv (P.eta t) j x)
    (fun j => partialDeriv (P.energy t) j x) (fun j => partialDeriv (P.temp t) j x)
    (P.vel t x) (P.heatFlux t x) (fun j => partialDeriv (fun y => P.vel t y j) j x)
    (fun j => partialDeriv (fun y => P.heatFlux t y j) j x) (hT t x) hl (hMass t x) (hEnergy t x)
