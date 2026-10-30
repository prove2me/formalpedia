-- Prove2me | solution 1 for CoVaRMC.Batching.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:02:56.454774+00:00
-- url     : https://prove2.me/submissions/eca6c3a5-fb09-4dcb-a16e-eb5f4facf269

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting
import Theorems.Thm_CoVaRMC_Batching_eq_6
import Theorems.Thm_CoVaRMC_Batching_order_stat_local_moments

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRL3Aux


lemma measurableSet_sort_eq {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (X : Fin N → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (σ : Equiv.Perm (Fin N)) :
    MeasurableSet {ω | Tuple.sort (fun j => X j ω) = σ} := by
  have : {ω | Tuple.sort (fun j => X j ω) = σ} =
      (⋂ i : Fin N, ⋂ j : Fin N, {ω | i ≤ j → X (σ i) ω ≤ X (σ j) ω}) ∩
      (⋂ i : Fin N, ⋂ j : Fin N, {ω | i < j → X (σ i) ω = X (σ j) ω → σ i < σ j}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [eq_comm, Tuple.eq_sort_iff]
    rfl
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
  · by_cases hij : i ≤ j
    · simp only [hij, true_implies]
      exact measurableSet_le (hX _) (hX _)
    · simp [hij]
  · by_cases hij : i < j
    · by_cases hs : σ i < σ j
      · simp [hs]
      · simp only [hij, hs, true_implies, imp_false]
        exact (measurableSet_eq_fun (hX _) (hX _)).compl
    · simp [hij]

lemma measurable_induced {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (X A : Fin N → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (hA : ∀ j, Measurable (A j)) (r : Fin N) :
    Measurable (fun ω => A (Tuple.sort (fun j => X j ω) r) ω) := by
  have heq : (fun ω => A (Tuple.sort (fun j => X j ω) r) ω) = fun ω =>
      ∑ σ : Equiv.Perm (Fin N),
        Set.indicator {ω | Tuple.sort (fun j => X j ω) = σ} (A (σ r)) ω := by
    funext ω
    rw [Finset.sum_eq_single (Tuple.sort (fun j => X j ω))]
    · simp
    · intro σ _ hσ
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_ofPred_eq]
      exact fun h => hσ h.symm
    · simp
  rw [heq]
  exact Finset.measurable_sum _ fun σ _ =>
    (hA _).indicator (measurableSet_sort_eq X hX σ)

open CoVaRMC.Batching

lemma measurable_fX (D : JointDensity) : Measurable D.fX := by
  have : StronglyMeasurable D.f := D.measurable.stronglyMeasurable
  exact (this.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

lemma measurable_condCDF (D : JointDensity) (y : ℝ) : Measurable (fun x => D.condCDF y x) := by
  unfold JointDensity.condCDF
  refine Measurable.div ?_ (measurable_fX D)
  have hm : Measurable (fun p : ℝ × ℝ => (Set.Iic y).indicator (fun v => D.f (p.1, v)) p.2) := by
    have : (fun p : ℝ × ℝ => (Set.Iic y).indicator (fun v => D.f (p.1, v)) p.2) =
        fun p => (Set.Iic y).indicator (fun _ => (1 : ℝ)) p.2 * D.f p := by
      funext p
      by_cases h : p.2 ∈ Set.Iic y <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    rw [this]
    exact ((measurable_const.indicator measurableSet_Iic).comp measurable_snd).mul D.measurable
  have h := hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  have : (fun x => ∫ v in Set.Iic y, D.f (x, v)) =
      fun x => ∫ v, (Set.Iic y).indicator (fun v => D.f (x, v)) v := by
    funext x; rw [integral_indicator measurableSet_Iic]
  rw [this]
  exact h.measurable


open CoVaRMC.Batching

lemma measurable_Xorder {Ω : Type*} [MeasurableSpace Ω] (S : ℕ × ℕ → Ω → ℝ × ℝ)
    (hSm : ∀ p, Measurable (S p)) (α : ℝ) (m i : ℕ) :
    Measurable (fun ω => Xorder S α m i ω) := by
  unfold Xorder
  by_cases hm : 0 < m
  · simp only [dif_pos hm, ImpactInvesting.Portfolio.orderStat]
    exact measurable_induced (fun j : Fin m => fun ω => (S (i, j) ω).1)
      (fun j : Fin m => fun ω => (S (i, j) ω).1) (fun j => (hSm _).fst) (fun j => (hSm _).fst) _
  · simp only [dif_neg hm]; exact measurable_const

lemma condCDF_mem (D : JointDensity) (y x : ℝ) : 0 ≤ D.condCDF y x ∧ D.condCDF y x ≤ 1 := by
  unfold JointDensity.condCDF
  have h0 : 0 ≤ ∫ v in Set.Iic y, D.f (x, v) := setIntegral_nonneg measurableSet_Iic fun _ _ => D.nonneg _
  have hX0 : 0 ≤ D.fX x := integral_nonneg fun _ => D.nonneg _
  refine ⟨div_nonneg h0 hX0, ?_⟩
  by_cases hint : Integrable (fun v => D.f (x, v))
  · have hle : ∫ v in Set.Iic y, D.f (x, v) ≤ D.fX x :=
      setIntegral_le_integral hint (Eventually.of_forall fun _ => D.nonneg _)
    rcases hX0.eq_or_lt with h | h
    · rw [← h, div_zero]; norm_num
    · exact (div_le_one h).mpr hle
  · have : D.fX x = 0 := integral_undef hint
    rw [this, div_zero]; norm_num

/-- Each observation lands a.s. where the marginal density is positive. -/
lemma ae_fX_pos (D : JointDensity) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSl : ∀ p, P.map (S p) = D.law)
    (p : ℕ × ℕ) : ∀ᵐ ω ∂P, 0 < D.fX (S p ω).1 := by
  have hZm : MeasurableSet {x : ℝ | D.fX x ≤ 0} := measurableSet_le (measurable_fX D) measurable_const
  have hE : MeasurableSet {q : ℝ × ℝ | D.fX q.1 ≤ 0} := hZm.preimage measurable_fst
  rw [ae_iff]
  have hset : {ω | ¬ 0 < D.fX (S p ω).1} = S p ⁻¹' {q : ℝ × ℝ | D.fX q.1 ≤ 0} := by
    ext ω; simp
  rw [hset, ← Measure.map_apply (hSm p) hE, hSl p]
  unfold JointDensity.law
  rw [withDensity_apply _ hE]
  have hprod : {q : ℝ × ℝ | D.fX q.1 ≤ 0} = {x : ℝ | D.fX x ≤ 0} ×ˢ Set.univ := by
    ext q; simp
  have hfi : Integrable D.f (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact D.integrable
  have hr : ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
      ({x : ℝ | D.fX x ≤ 0} ×ˢ Set.univ) = ((volume : Measure ℝ).restrict {x : ℝ | D.fX x ≤ 0}).prod
      (volume : Measure ℝ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hprod, Measure.volume_eq_prod, hr, lintegral_prod (fun a => ENNReal.ofReal (D.f a))
    (ENNReal.measurable_ofReal.comp D.measurable).aemeasurable]
  have hae : ∀ᵐ x ∂(volume.restrict {x : ℝ | D.fX x ≤ 0}),
      (∫⁻ y, ENNReal.ofReal (D.f (x, y))) = 0 := by
    filter_upwards [ae_restrict_of_ae hfi.prod_right_ae, ae_restrict_mem hZm] with x hx hxZ
    rw [← ofReal_integral_eq_lintegral_ofReal hx (Eventually.of_forall fun _ => D.nonneg _)]
    exact ENNReal.ofReal_eq_zero.mpr hxZ
  rw [lintegral_congr_ae hae, lintegral_zero]

lemma taylor_bound (g : ℝ → ℝ) (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g))
    (M : ℝ) (hM : ∀ x, |deriv (deriv g) x| ≤ M) (v x : ℝ) :
    |g x - g v - deriv g v * (x - v)| ≤ M * (x - v) ^ 2 := by
  have hd : ∀ x', |deriv g x' - deriv g v| ≤ M * |x' - v| := by
    intro x'
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv g) (s := Set.univ)
      (fun z _ => hg' z) (fun z _ => by rw [Real.norm_eq_abs]; exact hM z) convex_univ
      (Set.mem_univ v) (Set.mem_univ x')
    simpa [Real.norm_eq_abs] using this
  set h : ℝ → ℝ := fun z => g z - deriv g v * z with hhdef
  have hhd : ∀ z, HasDerivAt h (deriv g z - deriv g v) z := by
    intro z
    have := (hg z).hasDerivAt.sub ((hasDerivAt_id z).const_mul (deriv g v))
    rw [mul_one] at this
    exact this
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le (f := h) (s := Set.uIcc v x)
    (C := M * |x - v|) (fun z _ => (hhd z).differentiableAt)
    (fun z hz => by
      rw [(hhd z).deriv, Real.norm_eq_abs]
      refine (hd z).trans ?_
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
      exact mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc hz) hM0)
    (convex_uIcc v x) Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [hhdef, Real.norm_eq_abs] at hb
  have : g x - deriv g v * x - (g v - deriv g v * v) = g x - g v - deriv g v * (x - v) := by ring
  rw [this] at hb
  calc |g x - g v - deriv g v * (x - v)| ≤ M * |x - v| * |x - v| := hb
    _ = M * (x - v) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

end CoVaRL3Aux

open CoVaRL3Aux

open CoVaRMC.Batching in
theorem solution (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β)
    (M : ℝ) (hM : 0 < M)
    (hM1 : ∀ y ∈ 𝒴, |deriv (fun x => Fc y x) v| ≤ M)
    (hM2 : ∀ x : ℝ, ∀ y ∈ 𝒴, |deriv (deriv (fun x => Fc y x)) x| ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law) :
    ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, ∀ y ∈ 𝒴, |pHat P S α m y - Fc y v| ≤ C / m := by
  obtain ⟨h𝒳o, hv𝒳, h𝒴o, hc𝒴, hfXc, hfXpos, -, -, hdiff⟩ := hA1
  obtain ⟨δ, hδ, C, hC⟩ := CoVaRMC.Batching.order_stat_local_moments D α hα v 𝒳 h𝒳o hv𝒳 hfXc
    hfXpos hv P S hSm hSi hSl
  refine ⟨M * |C| + M * |C| + |C|, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with m hCm hm1 y hy
  obtain ⟨h1, h2, h3⟩ := hCm
  have hm : 0 < m := hm1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [CoVaRMC.Batching.eq_6 D α hα P S hSm hSi hSl m hm y]
  set X : Ω → ℝ := fun ω => Xorder S α m 0 ω with hXdef
  have hXm : Measurable X := measurable_Xorder S hSm α m 0
  set g : ℝ → ℝ := fun x => Fc y x with hgdef
  obtain ⟨hgd, hgd'⟩ := hdiff y hy
  have hgm : Measurable g := hgd.continuous.measurable
  -- a.s. the order statistic lies where `f_X > 0`
  have hXpos : ∀ᵐ ω ∂P, 0 < D.fX (X ω) := by
    have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, 0 < D.fX (S (0, j) ω).1 :=
      ae_all_iff.mpr fun j => ae_fX_pos D P S hSm hSl (0, j)
    filter_upwards [hall] with ω hω
    simp only [hXdef, Xorder, dif_pos hm, ImpactInvesting.Portfolio.orderStat]
    exact hω _
  have hgX : ∀ᵐ ω ∂P, D.condCDF y (X ω) = g (X ω) ∧ 0 ≤ g (X ω) ∧ g (X ω) ≤ 1 := by
    filter_upwards [hXpos] with ω hω
    have he : g (X ω) = D.condCDF y (X ω) := hFc _ hω y
    rw [he]
    exact ⟨rfl, condCDF_mem D y (X ω)⟩
  have hgv : 0 ≤ g v ∧ g v ≤ 1 := by
    have he : g v = D.condCDF y v := hFc _ (hfXpos v hv𝒳) y
    rw [he]; exact condCDF_mem D y v
  set A : Set Ω := {ω | |X ω - v| ≤ δ} with hAdef
  have hAm : MeasurableSet A := measurableSet_le ((hXm.sub measurable_const).abs) measurable_const
  set L : Ω → ℝ := A.indicator (fun ω => X ω - v) with hLdef
  set Q2 : Ω → ℝ := A.indicator (fun ω => (X ω - v) ^ 2) with hQ2def
  set T : Ω → ℝ := Aᶜ.indicator (fun _ => (1 : ℝ)) with hTdef
  have hLm : Measurable L := (hXm.sub measurable_const).indicator hAm
  have hQ2m : Measurable Q2 := ((hXm.sub measurable_const).pow_const 2).indicator hAm
  have hTm : Measurable T := measurable_const.indicator hAm.compl
  have hLb : ∀ ω, |L ω| ≤ δ := by
    intro ω; simp only [hLdef, Set.indicator]; split_ifs with h
    · exact h
    · simp [hδ.le]
  have hQ2b : ∀ ω, |Q2 ω| ≤ δ ^ 2 := by
    intro ω; simp only [hQ2def, Set.indicator]; split_ifs with h
    · rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    · simp [sq_nonneg]
  have hTb : ∀ ω, |T ω| ≤ 1 := by
    intro ω; simp only [hTdef, Set.indicator]; split_ifs <;> simp
  have hint : ∀ (F : Ω → ℝ) (K : ℝ), Measurable F → (∀ ω, |F ω| ≤ K) → Integrable F P :=
    fun F K hF hK => Integrable.mono' (integrable_const K) hF.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hK ω)
  set d := deriv g v with hddef
  -- the error term
  set E : Ω → ℝ := fun ω => g (X ω) - g v - d * L ω with hEdef
  have hEm : Measurable E := ((hgm.comp hXm).sub measurable_const).sub (measurable_const.mul hLm)
  have hEb : ∀ᵐ ω ∂P, |E ω| ≤ M * Q2 ω + T ω := by
    filter_upwards [hgX] with ω hω
    obtain ⟨-, hg0, hg1⟩ := hω
    by_cases hA : ω ∈ A
    · have hT0 : T ω = 0 := by simp [hTdef, hA]
      have hL : L ω = X ω - v := by simp [hLdef, hA]
      have hQ : Q2 ω = (X ω - v) ^ 2 := by simp [hQ2def, hA]
      rw [hT0, add_zero, hQ]
      simp only [hEdef, hL]
      exact taylor_bound g hgd hgd' M (fun x => hM2 x y hy) v (X ω)
    · have hT1 : T ω = 1 := by simp [hTdef, hA]
      have hL : L ω = 0 := by simp [hLdef, hA]
      have hQ : Q2 ω = 0 := by simp [hQ2def, hA]
      rw [hT1, hQ]
      simp only [hEdef, hL, mul_zero, sub_zero]
      rw [abs_le]; constructor <;> linarith [hgv.1, hgv.2]
  have hEint : Integrable E P := by
    refine Integrable.mono' ((hint Q2 (δ ^ 2) hQ2m hQ2b).const_mul M |>.add (hint T 1 hTm hTb))
      hEm.aestronglyMeasurable ?_
    filter_upwards [hEb] with ω hω
    rw [Real.norm_eq_abs]; exact hω
  -- rewrite the bias
  have hdecomp : ∫ ω, D.condCDF y (X ω) ∂P - Fc y v = d * ∫ ω, L ω ∂P + ∫ ω, E ω ∂P := by
    have h1' : ∫ ω, D.condCDF y (X ω) ∂P = ∫ ω, (g v + d * L ω + E ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [hgX] with ω hω
      obtain ⟨he, -, -⟩ := hω
      rw [he]; simp only [hEdef]; ring
    have hI0 : Integrable (fun ω : Ω => d * L ω) P := (hint L δ hLm hLb).const_mul d
    have hI1 : Integrable (fun ω : Ω => g v + d * L ω) P := (integrable_const (g v)).add hI0
    rw [h1', integral_add hI1 hEint, integral_add (integrable_const (g v)) hI0, integral_const,
      probReal_univ, one_smul, integral_const_mul]
    simp only [hgdef]; ring
  rw [hdecomp]
  have hEbound : |∫ ω, E ω ∂P| ≤ M * ∫ ω, Q2 ω ∂P + ∫ ω, T ω ∂P := by
    calc |∫ ω, E ω ∂P| ≤ ∫ ω, |E ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (M * Q2 ω + T ω) ∂P := integral_mono_ae hEint.abs
          (((hint Q2 (δ ^ 2) hQ2m hQ2b).const_mul M).add (hint T 1 hTm hTb)) hEb
      _ = M * ∫ ω, Q2 ω ∂P + ∫ ω, T ω ∂P := by
          rw [integral_add ((hint Q2 (δ ^ 2) hQ2m hQ2b).const_mul M) (hint T 1 hTm hTb),
            integral_const_mul]
  have hT : ∫ ω, T ω ∂P = (P {ω | δ < |Xorder S α m 0 ω - v|}).toReal := by
    have hAc : Aᶜ = {ω | δ < |Xorder S α m 0 ω - v|} := by
      ext ω; simp [hAdef, hXdef, not_le]
    simp only [hTdef]
    rw [integral_indicator_const _ hAm.compl, smul_eq_mul, mul_one, hAc]
    rfl
  have hL2 : |∫ ω, L ω ∂P| ≤ C / m := h2
  have hQ2' : ∫ ω, Q2 ω ∂P ≤ C / m := h3
  have hd : |d| ≤ M := hM1 y hy
  have hCabs : C / m ≤ |C| / m := div_le_div_of_nonneg_right (le_abs_self C) hmR.le
  have hQ0 : 0 ≤ ∫ ω, Q2 ω ∂P := integral_nonneg fun ω => by
    simp only [hQ2def, Set.indicator]; split_ifs <;> positivity
  calc |d * ∫ ω, L ω ∂P + ∫ ω, E ω ∂P| ≤ |d| * |∫ ω, L ω ∂P| + |∫ ω, E ω ∂P| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ M * (|C| / m) + (M * (|C| / m) + |C| / m) := by
        gcongr
        · exact hL2.trans hCabs
        · calc |∫ ω, E ω ∂P| ≤ M * ∫ ω, Q2 ω ∂P + ∫ ω, T ω ∂P := hEbound
            _ ≤ M * (|C| / m) + |C| / m := by
              rw [hT]
              gcongr
              · exact hQ2'.trans hCabs
              · exact h1.trans hCabs
    _ = (M * |C| + M * |C| + |C|) / m := by ring
