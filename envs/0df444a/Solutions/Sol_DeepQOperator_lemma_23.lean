-- Prove2me | solution 1 for DeepQOperator.lemma_23
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T19:46:21.212124+00:00
-- url     : https://prove2.me/submissions/1b2f331c-7395-44b8-8ba0-458764580c28

import Mathlib

open MeasureTheory

/-! Proof of Lemma 23 (Deep Q-Operator). Write `m = g ∘ Y` for `E[U | Y]`. For a decoder `d`,
the loss equals `c (U - T)₊ + c 1[d] (T - U)`; at each fixed `t`, `E[1[d(Y,t)] U] = E[1[d(Y,t)] m]`,
so the loss is at least `c E[(U - t)₊ - (m - t)₊]`, with equality for `d = 1[t < m]`.
Integrating over the independent uniform `T` gives `c/(4R) E[(U - m)²]`. -/

lemma dq23_max_identity (a : ℝ) : max 0 a = max 0 (-a) + a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

lemma dq23_ib {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC ω)

lemma dq23_unif_int {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (T : Ω → ℝ) (R : ℝ)
    (hR : 0 < R) (hTu : pdf.IsUniform T (Set.Icc (-R) R) P) (h : ℝ → ℝ) :
    ∫ t, h t ∂(P.map T) = (2 * R)⁻¹ * ∫ t in (-R)..R, h t := by
  unfold pdf.IsUniform at hTu
  rw [hTu, ProbabilityTheory.cond, integral_smul_measure, Real.volume_Icc,
    intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
  ring_nf

lemma dq23_unif_ae {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (T : Ω → ℝ) (R : ℝ)
    (hT : Measurable T) (hTu : pdf.IsUniform T (Set.Icc (-R) R) P) :
    ∀ᵐ ω ∂P, T ω ∈ Set.Icc (-R) R := by
  have h : ∀ᵐ t ∂(P.map T), t ∈ Set.Icc (-R) R := by
    unfold pdf.IsUniform at hTu
    rw [hTu, ProbabilityTheory.cond]
    exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
  exact ae_of_ae_map hT.aemeasurable h

lemma dq23_tint (R u : ℝ) (hu : u ∈ Set.Icc (-R) R) :
    ∫ t in (-R)..R, max 0 (u - t) = (u + R) ^ 2 / 2 := by
  have h1 : IntervalIntegrable (fun t => max 0 (u - t)) MeasureTheory.volume (-R) u :=
    (by fun_prop : Continuous (fun t : ℝ => max 0 (u - t))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t => max 0 (u - t)) MeasureTheory.volume u R :=
    (by fun_prop : Continuous (fun t : ℝ => max 0 (u - t))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have e1 : ∫ t in (-R)..u, max 0 (u - t) = ∫ t in (-R)..u, (u - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hu.1] at ht
    exact max_eq_right (by linarith [ht.2])
  have e2 : ∫ t in u..R, max 0 (u - t) = ∫ t in u..R, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hu.2] at ht
    exact max_eq_left (by linarith [ht.1])
  rw [e1, e2, intervalIntegral.integral_comp_sub_left (fun x => x) u, integral_id]
  simp

lemma dq23_tint2 (R c u v : ℝ) (hu : u ∈ Set.Icc (-R) R) (hv : v ∈ Set.Icc (-R) R) :
    ∫ t in (-R)..R, c * (max 0 (u - t) - max 0 (v - t)) =
      c * ((u + R) ^ 2 / 2 - (v + R) ^ 2 / 2) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun t : ℝ => max 0 (u - t))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun t : ℝ => max 0 (v - t))).intervalIntegrable _ _),
    dq23_tint R u hu, dq23_tint R v hv]

lemma dq23_condexp {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (U : Ω → ℝ) (Y : Ω → Fin k → ℝ) (R : ℝ) (hU : Measurable U) (hY : Measurable Y)
    (hUR : ∀ ω, U ω ∈ Set.Icc (-R) R) (g : (Fin k → ℝ) → ℝ)
    (hm : P[U | MeasurableSpace.comap Y inferInstance] =ᵐ[P] fun ω => g (Y ω))
    (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (C : ℝ) (hC : ∀ y, |h y| ≤ C) :
    ∫ ω, h (Y ω) * U ω ∂P = ∫ ω, h (Y ω) * g (Y ω) ∂P := by
  have hle : MeasurableSpace.comap Y inferInstance ≤ ‹MeasurableSpace Ω› := hY.comap_le
  have hUi : Integrable U P := Integrable.of_bound hU.aestronglyMeasurable R
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_le]; exact hUR ω)
  have hhm : Measurable[MeasurableSpace.comap Y inferInstance] (fun ω => h (Y ω)) :=
    hh.comp (Measurable.of_comap_le le_rfl)
  have hhUi : Integrable ((fun ω => h (Y ω)) * U) P :=
    Integrable.of_bound ((hh.comp hY).mul hU).aestronglyMeasurable (C * R)
      (ae_of_all _ fun ω => by
        simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hC _) (abs_le.mpr (hUR ω)) (abs_nonneg _)
          ((abs_nonneg _).trans (hC (Y ω))))
  calc ∫ ω, h (Y ω) * U ω ∂P
      = ∫ ω, (P[(fun ω => h (Y ω)) * U | MeasurableSpace.comap Y inferInstance]) ω ∂P :=
        (integral_condExp hle).symm
    _ = ∫ ω, ((fun ω => h (Y ω)) * P[U | MeasurableSpace.comap Y inferInstance]) ω ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hhm.stronglyMeasurable hhUi hUi)
    _ = _ := integral_congr_ae (hm.mono fun ω hω => by simp only [Pi.mul_apply, hω])

lemma dq23_prod_ae {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (U T : Ω → ℝ) (Y : Ω → Fin k → ℝ) (R : ℝ)
    (hU : Measurable U) (hT : Measurable T) (hY : Measurable Y)
    (hUR : ∀ ω, U ω ∈ Set.Icc (-R) R) (hTu : pdf.IsUniform T (Set.Icc (-R) R) P)
    (hind : ProbabilityTheory.IndepFun T (fun ω => (U ω, Y ω)) P) :
    P.map (fun ω => (T ω, (U ω, Y ω))) = (P.map T).prod (P.map (fun ω => (U ω, Y ω))) ∧
    ∀ᵐ z ∂((P.map T).prod (P.map (fun ω => (U ω, Y ω)))),
      z.1 ∈ Set.Icc (-R) R ∧ z.2.1 ∈ Set.Icc (-R) R := by
  have hprod : P.map (fun ω => (T ω, (U ω, Y ω))) =
      (P.map T).prod (P.map (fun ω => (U ω, Y ω))) :=
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hT.aemeasurable
      (hU.prodMk hY).aemeasurable).mp hind
  refine ⟨hprod, ?_⟩
  rw [← hprod]
  have hs : MeasurableSet {z : ℝ × (ℝ × (Fin k → ℝ)) |
      z.1 ∈ Set.Icc (-R) R ∧ z.2.1 ∈ Set.Icc (-R) R} :=
    (measurableSet_Icc.preimage measurable_fst).inter
      (measurableSet_Icc.preimage measurable_snd.fst)
  rw [ae_map_iff (hT.prodMk (hU.prodMk hY)).aemeasurable hs]
  filter_upwards [dq23_unif_ae P T R hT hTu] with ω hω using ⟨hω, hUR ω⟩

lemma dq23_fub {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (U T : Ω → ℝ) (Y : Ω → Fin k → ℝ) (R : ℝ)
    (hU : Measurable U) (hT : Measurable T) (hY : Measurable Y)
    (hUR : ∀ ω, U ω ∈ Set.Icc (-R) R) (hTu : pdf.IsUniform T (Set.Icc (-R) R) P)
    (hind : ProbabilityTheory.IndepFun T (fun ω => (U ω, Y ω)) P)
    (F : ℝ × (ℝ × (Fin k → ℝ)) → ℝ) (hF : Measurable F) (C : ℝ)
    (hFb : ∀ t u y, t ∈ Set.Icc (-R) R → u ∈ Set.Icc (-R) R → |F (t, (u, y))| ≤ C) :
    (∫ ω, F (T ω, (U ω, Y ω)) ∂P = ∫ t, (∫ ω, F (t, (U ω, Y ω)) ∂P) ∂(P.map T)) ∧
    Integrable (fun t => ∫ ω, F (t, (U ω, Y ω)) ∂P) (P.map T) ∧
    (∫ ω, F (T ω, (U ω, Y ω)) ∂P = ∫ ω, (∫ t, F (t, (U ω, Y ω)) ∂(P.map T)) ∂P) := by
  obtain ⟨hprod, hae⟩ := dq23_prod_ae P U T Y R hU hT hY hUR hTu hind
  have hint : Integrable F ((P.map T).prod (P.map (fun ω => (U ω, Y ω)))) :=
    Integrable.of_bound hF.aestronglyMeasurable C (by
      filter_upwards [hae] with z hz
      rw [Real.norm_eq_abs]
      exact hFb z.1 z.2.1 z.2.2 hz.1 hz.2)
  have hin : ∀ t, ∫ x, F (t, x) ∂(P.map (fun ω => (U ω, Y ω))) = ∫ ω, F (t, (U ω, Y ω)) ∂P :=
    fun t => integral_map (hU.prodMk hY).aemeasurable
      (hF.comp measurable_prodMk_left).aestronglyMeasurable
  have hout : (∫ ω, F (T ω, (U ω, Y ω)) ∂P) =
      ∫ z, F z ∂(P.map (fun ω => (T ω, (U ω, Y ω)))) :=
    (integral_map (hT.prodMk (hU.prodMk hY)).aemeasurable hF.aestronglyMeasurable).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hout, hprod, integral_prod F hint]
    congr 1
    funext t
    exact hin t
  · exact (hint.integral_prod_left).congr (ae_of_all _ fun t => hin t)
  · rw [hout, hprod, integral_prod_symm F hint]
    exact integral_map (hU.prodMk hY).aemeasurable hint.integral_prod_right.aestronglyMeasurable

lemma dq23_stepA {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (U : Ω → ℝ) (Y : Ω → Fin k → ℝ) (R c : ℝ) (hR : 0 < R) (hU : Measurable U)
    (hY : Measurable Y)
    (hUR : ∀ ω, U ω ∈ Set.Icc (-R) R) (g : (Fin k → ℝ) → ℝ) (hg : Measurable g)
    (hgR : ∀ y, g y ∈ Set.Icc (-R) R)
    (hm : P[U | MeasurableSpace.comap Y inferInstance] =ᵐ[P] fun ω => g (Y ω))
    (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hh1 : ∀ y, |h y| ≤ 1) (t : ℝ) :
    ∫ ω, (c * max 0 (U ω - t) + c * (h (Y ω) * (t - U ω))) ∂P =
      ∫ ω, (c * max 0 (U ω - t) + c * (h (Y ω) * (t - g (Y ω)))) ∂P := by
  have hUb : ∀ ω, |U ω| ≤ R := fun ω => abs_le.mpr (hUR ω)
  have hgb : ∀ y, |g y| ≤ R := fun y => abs_le.mpr (hgR y)
  have hmax : ∀ ω, |c * max 0 (U ω - t)| ≤ |c| * (R + |t|) := fun ω => by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le (by positivity) (by linarith [hUb ω, neg_abs_le t, le_abs_self (U ω)])
  have i0 : Integrable (fun ω => c * max 0 (U ω - t)) P :=
    dq23_ib P _ (by fun_prop) _ hmax
  have iht : Integrable (fun ω => h (Y ω) * t) P :=
    dq23_ib P _ (by fun_prop) (1 * |t|) fun ω => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hh1 _) (abs_nonneg _)
  have ihU : Integrable (fun ω => h (Y ω) * U ω) P :=
    dq23_ib P _ (by fun_prop) (1 * R) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hh1 _) (hUb ω) (abs_nonneg _) zero_le_one
  have ihg : Integrable (fun ω => h (Y ω) * g (Y ω)) P :=
    dq23_ib P _ (by fun_prop) (1 * R) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hh1 _) (hgb _) (abs_nonneg _) zero_le_one
  have e1 : ∀ s : Ω → ℝ, (fun ω => c * (h (Y ω) * (t - s ω))) =
      fun ω => c * (h (Y ω) * t - h (Y ω) * s ω) := fun s => by
    funext ω; ring
  rw [integral_add i0 ((iht.sub ihU).const_mul c |>.congr (ae_of_all _ fun ω => by
      simp only [Pi.sub_apply]; ring)),
    integral_add i0 ((iht.sub ihg).const_mul c |>.congr (ae_of_all _ fun ω => by
      simp only [Pi.sub_apply]; ring))]
  congr 1
  rw [e1 U, e1 (fun ω => g (Y ω)), integral_const_mul, integral_const_mul,
    integral_sub iht ihU, integral_sub iht ihg,
    dq23_condexp P U Y R hU hY hUR g hm h hh 1 hh1]

lemma dq23_core {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (U : Ω → ℝ) (Y : Ω → Fin k → ℝ) (R c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (hU : Measurable U) (hY : Measurable Y)
    (hUR : ∀ ω, U ω ∈ Set.Icc (-R) R) (g : (Fin k → ℝ) → ℝ) (hg : Measurable g)
    (hgR : ∀ y, g y ∈ Set.Icc (-R) R)
    (hm : P[U | MeasurableSpace.comap Y inferInstance] =ᵐ[P] fun ω => g (Y ω))
    (d : (Fin k → ℝ) → Bool) (hd : Measurable d) (t : ℝ) :
    ∫ ω, c * (max 0 (U ω - t) - max 0 (g (Y ω) - t)) ∂P ≤
      ∫ ω, (if d (Y ω) then c * max 0 (t - U ω) else c * max 0 (U ω - t)) ∂P ∧
    ((∀ y, d y = decide (t < g y)) →
      ∫ ω, c * (max 0 (U ω - t) - max 0 (g (Y ω) - t)) ∂P =
      ∫ ω, (if d (Y ω) then c * max 0 (t - U ω) else c * max 0 (U ω - t)) ∂P) := by
  let h : (Fin k → ℝ) → ℝ := fun y => if d y then 1 else 0
  have hh : Measurable h := Measurable.ite (hd (measurableSet_singleton true))
    measurable_const measurable_const
  have hh1 : ∀ y, |h y| ≤ 1 := fun y => by
    simp only [h]; split_ifs <;> simp
  have hpt : ∀ ω, (if d (Y ω) then c * max 0 (t - U ω) else c * max 0 (U ω - t)) =
      c * max 0 (U ω - t) + c * (h (Y ω) * (t - U ω)) := fun ω => by
    simp only [h]
    split_ifs
    · have := dq23_max_identity (t - U ω)
      rw [neg_sub] at this
      rw [this]; ring
    · ring
  have hA := dq23_stepA P U Y R c hR hU hY hUR g hg hgR hm h hh hh1 t
  simp_rw [hpt]
  rw [hA]
  have hUb : ∀ ω, |U ω| ≤ R := fun ω => abs_le.mpr (hUR ω)
  have hgb : ∀ y, |g y| ≤ R := fun y => abs_le.mpr (hgR y)
  have i1 : Integrable (fun ω => c * (max 0 (U ω - t) - max 0 (g (Y ω) - t))) P :=
    dq23_ib P _ (by fun_prop) (|c| * (2 * (R + |t|))) fun ω => by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (le_max_left _ _), abs_of_nonneg (le_max_left _ _)]
      have := max_le (show (0:ℝ) ≤ R + |t| by positivity)
        (show U ω - t ≤ R + |t| by linarith [hUb ω, neg_abs_le t, le_abs_self (U ω)])
      have := max_le (show (0:ℝ) ≤ R + |t| by positivity)
        (show g (Y ω) - t ≤ R + |t| by linarith [hgb (Y ω), neg_abs_le t, le_abs_self (g (Y ω))])
      linarith
  have i2 : Integrable (fun ω => c * max 0 (U ω - t) + c * (h (Y ω) * (t - g (Y ω)))) P :=
    dq23_ib P _ (by fun_prop) (|c| * (R + |t|) + |c| * (1 * (R + |t|))) fun ω => by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_of_nonneg (le_max_left _ _)]
        exact max_le (by positivity) (by linarith [hUb ω, neg_abs_le t, le_abs_self (U ω)])
      · rw [abs_mul, abs_mul]
        refine mul_le_mul_of_nonneg_left (mul_le_mul (hh1 _) ?_ (abs_nonneg _) zero_le_one)
          (abs_nonneg _)
        exact (abs_sub _ _).trans (by linarith [hgb (Y ω)])
  have hptw : ∀ ω, c * (max 0 (U ω - t) - max 0 (g (Y ω) - t)) ≤
      c * max 0 (U ω - t) + c * (h (Y ω) * (t - g (Y ω))) := fun ω => by
    have : -max 0 (g (Y ω) - t) ≤ h (Y ω) * (t - g (Y ω)) := by
      simp only [h]
      split_ifs
      · rw [one_mul]; linarith [le_max_right 0 (g (Y ω) - t)]
      · rw [zero_mul]; linarith [le_max_left 0 (g (Y ω) - t)]
    nlinarith
  refine ⟨integral_mono i1 i2 hptw, fun hdstar => ?_⟩
  apply integral_congr_ae
  refine ae_of_all _ fun ω => ?_
  simp only [h, hdstar]
  by_cases hlt : t < g (Y ω)
  · simp only [hlt, decide_true, if_true, one_mul]
    rw [max_eq_right (show (0:ℝ) ≤ g (Y ω) - t by linarith)]; ring
  · simp only [hlt, decide_false, Bool.false_eq_true, if_false, zero_mul]
    rw [max_eq_left (show g (Y ω) - t ≤ 0 by linarith)]; ring

lemma dq23_val {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (U T : Ω → ℝ) (Y : Ω → Fin k → ℝ) (R c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (hU : Measurable U) (hY : Measurable Y)
    (hUR : ∀ ω, U ω ∈ Set.Icc (-R) R) (hTu : pdf.IsUniform T (Set.Icc (-R) R) P)
    (g : (Fin k → ℝ) → ℝ) (hg : Measurable g)
    (hgR : ∀ y, g y ∈ Set.Icc (-R) R)
    (hm : P[U | MeasurableSpace.comap Y inferInstance] =ᵐ[P] fun ω => g (Y ω)) :
    ∫ ω, (∫ t, c * (max 0 (U ω - t) - max 0 (g (Y ω) - t)) ∂(P.map T)) ∂P =
      c / (4 * R) * ∫ ω, (U ω - g (Y ω)) ^ 2 ∂P := by
  have hpt : ∀ ω, ∫ t, c * (max 0 (U ω - t) - max 0 (g (Y ω) - t)) ∂(P.map T) =
      c / (4 * R) * (U ω - g (Y ω)) ^ 2 +
        c / (2 * R) * ((g (Y ω) + R) * U ω - (g (Y ω) + R) * g (Y ω)) := by
    intro ω
    rw [dq23_unif_int P T R hR hTu, dq23_tint2 R c _ _ (hUR ω) (hgR _)]
    field_simp
    ring
  simp_rw [hpt]
  have hUb : ∀ ω, |U ω| ≤ R := fun ω => abs_le.mpr (hUR ω)
  have hgb : ∀ y, |g y + R| ≤ 2 * R := fun y => by
    rw [abs_le]; constructor <;> linarith [(hgR y).1, (hgR y).2]
  have hgb' : ∀ y, |g y| ≤ R := fun y => abs_le.mpr (hgR y)
  have isq : Integrable (fun ω => (U ω - g (Y ω)) ^ 2) P :=
    dq23_ib P _ (by fun_prop) (4 * R ^ 2) fun ω => by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [mul_nonneg (show 0 ≤ 2 * R - (U ω - g (Y ω)) by
          linarith [(hUR ω).2, (hgR (Y ω)).1])
        (show 0 ≤ 2 * R + (U ω - g (Y ω)) by linarith [(hUR ω).1, (hgR (Y ω)).2])]
  have ia : Integrable (fun ω => (g (Y ω) + R) * U ω) P :=
    dq23_ib P _ (by fun_prop) (2 * R * R) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hgb _) (hUb ω) (abs_nonneg _) (by linarith)
  have ib : Integrable (fun ω => (g (Y ω) + R) * g (Y ω)) P :=
    dq23_ib P _ (by fun_prop) (2 * R * R) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hgb _) (hgb' _) (abs_nonneg _) (by linarith)
  have hce := dq23_condexp P U Y R hU hY hUR g hm (fun y => g y + R) (hg.add_const R)
    (2 * R) hgb
  beta_reduce at hce
  have i1 : Integrable (fun ω => c / (4 * R) * (U ω - g (Y ω)) ^ 2) P := isq.const_mul _
  have i2 : Integrable (fun ω => c / (2 * R) *
      ((g (Y ω) + R) * U ω - (g (Y ω) + R) * g (Y ω))) P := (ia.sub ib).const_mul _
  rw [integral_add i1 i2, integral_const_mul,
    integral_const_mul, integral_sub ia ib, hce, sub_self, mul_zero, add_zero]

lemma dq23_ite_bound (R c t u : ℝ) (hc : 0 < c) (ht : t ∈ Set.Icc (-R) R)
    (hu : u ∈ Set.Icc (-R) R) (b : Bool) :
    |if b then c * max 0 (t - u) else c * max 0 (u - t)| ≤ c * (2 * R) := by
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [abs_of_nonneg (mul_nonneg hc.le (le_max_left _ _))]
    exact mul_le_mul_of_nonneg_left (max_le (by linarith [ht.1, ht.2])
      (by linarith [ht.1, hu.2])) hc.le
  · simp only [if_true]
    rw [abs_of_nonneg (mul_nonneg hc.le (le_max_left _ _))]
    exact mul_le_mul_of_nonneg_left (max_le (by linarith [ht.1, ht.2])
      (by linarith [ht.2, hu.1])) hc.le

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {k : ℕ}
    (U T : Ω → ℝ) (Y : Ω → Fin k → ℝ) (R c : ℝ) (hR : 0 < R) (hc : 0 < c)
    (hU : Measurable U) (hT : Measurable T) (hY : Measurable Y)
    (hUR : ∀ ω, U ω ∈ Set.Icc (-R) R) (hTu : pdf.IsUniform T (Set.Icc (-R) R) P)
    (hind : ProbabilityTheory.IndepFun T (fun ω => (U ω, Y ω)) P) :
    (∀ dec : (Fin k → ℝ) → ℝ → Bool, Measurable (fun p : (Fin k → ℝ) × ℝ => dec p.1 p.2) →
      c / (4 * R) * ∫ ω, (U ω - (P[U | MeasurableSpace.comap Y inferInstance]) ω) ^ 2 ∂P ≤
        ∫ ω, (if dec (Y ω) (T ω) then c * max 0 (T ω - U ω) else c * max 0 (U ω - T ω)) ∂P) ∧
    (∃ dec : (Fin k → ℝ) → ℝ → Bool, Measurable (fun p : (Fin k → ℝ) × ℝ => dec p.1 p.2) ∧
      ∫ ω, (if dec (Y ω) (T ω) then c * max 0 (T ω - U ω) else c * max 0 (U ω - T ω)) ∂P =
        c / (4 * R) * ∫ ω, (U ω - (P[U | MeasurableSpace.comap Y inferInstance]) ω) ^ 2 ∂P) ∧
    (∀ (Ω' : Type) [MeasurableSpace Ω'] [StandardBorelSpace Ω'] (ν : Measure Ω')
        [IsProbabilityMeasure ν] (dec : Ω' → (Fin k → ℝ) → ℝ → Bool),
      Measurable (fun p : Ω' × (Fin k → ℝ) × ℝ => dec p.1 p.2.1 p.2.2) →
      c / (4 * R) * ∫ ω, (U ω - (P[U | MeasurableSpace.comap Y inferInstance]) ω) ^ 2 ∂P ≤
        ∫ q, (if dec q.2 (Y q.1) (T q.1) then c * max 0 (T q.1 - U q.1)
          else c * max 0 (U q.1 - T q.1)) ∂(P.prod ν)) := by
  have hsm : StronglyMeasurable[MeasurableSpace.comap Y inferInstance]
      (P[U | MeasurableSpace.comap Y inferInstance]) := stronglyMeasurable_condExp
  obtain ⟨g0, hg0, hg0eq⟩ := hsm.measurable.exists_eq_measurable_comp
  let g : (Fin k → ℝ) → ℝ := fun y => max (-R) (min R (g0 y))
  have hg : Measurable g := measurable_const.max (measurable_const.min hg0)
  have hgR : ∀ y, g y ∈ Set.Icc (-R) R := fun y =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hbdd := ae_bdd_abs_condExp_of_ae_bdd_abs (m := MeasurableSpace.comap Y inferInstance)
    (μ := P) (f := U) (R := R) (ae_of_all _ fun ω => abs_le.mpr (hUR ω))
  have hm : P[U | MeasurableSpace.comap Y inferInstance] =ᵐ[P] fun ω => g (Y ω) := by
    filter_upwards [hbdd] with ω hω
    have h1 : (P[U | MeasurableSpace.comap Y inferInstance]) ω = g0 (Y ω) := congrFun hg0eq ω
    rw [abs_le] at hω
    show _ = max (-R) (min R (g0 (Y ω)))
    rw [← h1, min_eq_right hω.2, max_eq_right hω.1]
  have hV : ∫ ω, (U ω - (P[U | MeasurableSpace.comap Y inferInstance]) ω) ^ 2 ∂P =
      ∫ ω, (U ω - g (Y ω)) ^ 2 ∂P :=
    integral_congr_ae (hm.mono fun ω hω => by beta_reduce; rw [hω])
  rw [hV]
  let FW : ℝ × (ℝ × (Fin k → ℝ)) → ℝ :=
    fun z => c * (max 0 (z.2.1 - z.1) - max 0 (g z.2.2 - z.1))
  have hFW : Measurable FW := by fun_prop
  have hFWb : ∀ t u y, t ∈ Set.Icc (-R) R → u ∈ Set.Icc (-R) R →
      |FW (t, (u, y))| ≤ c * (2 * R) := fun t u y ht hu => by
    show |c * (max 0 (u - t) - max 0 (g y - t))| ≤ c * (2 * R)
    rw [abs_mul, abs_of_pos hc]
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    have h1 := le_max_left 0 (u - t)
    have h2 := le_max_left 0 (g y - t)
    have h3 : max 0 (u - t) ≤ 2 * R := max_le (by linarith) (by linarith [ht.1, hu.2])
    have h4 : max 0 (g y - t) ≤ 2 * R := max_le (by linarith) (by linarith [ht.1, (hgR y).2])
    rw [abs_le]; constructor <;> linarith
  obtain ⟨eW1, iW, eW2⟩ := dq23_fub P U T Y R hU hT hY hUR hTu hind FW hFW _ hFWb
  have hval : ∫ ω, FW (T ω, (U ω, Y ω)) ∂P = c / (4 * R) * ∫ ω, (U ω - g (Y ω)) ^ 2 ∂P := by
    rw [eW2]
    exact dq23_val P U T Y R c hR hc hU hY hUR hTu g hg hgR hm
  have hlb : ∀ dec : (Fin k → ℝ) → ℝ → Bool,
      Measurable (fun p : (Fin k → ℝ) × ℝ => dec p.1 p.2) →
      c / (4 * R) * ∫ ω, (U ω - g (Y ω)) ^ 2 ∂P ≤
        ∫ ω, (if dec (Y ω) (T ω) then c * max 0 (T ω - U ω)
          else c * max 0 (U ω - T ω)) ∂P := by
    intro dec hdec
    let Fd : ℝ × (ℝ × (Fin k → ℝ)) → ℝ := fun z =>
      if dec z.2.2 z.1 then c * max 0 (z.1 - z.2.1) else c * max 0 (z.2.1 - z.1)
    have hFd : Measurable Fd := Measurable.ite
      ((hdec.comp (measurable_snd.snd.prodMk measurable_fst)) (measurableSet_singleton true))
      (by fun_prop) (by fun_prop)
    obtain ⟨eD1, iD, -⟩ := dq23_fub P U T Y R hU hT hY hUR hTu hind Fd hFd (c * (2 * R))
      (fun t u y ht hu => dq23_ite_bound R c t u hc ht hu _)
    rw [← hval]
    show ∫ ω, FW (T ω, (U ω, Y ω)) ∂P ≤ ∫ ω, Fd (T ω, (U ω, Y ω)) ∂P
    rw [eW1, eD1]
    refine integral_mono iW iD fun t => ?_
    exact (dq23_core P U Y R c hR hc hU hY hUR g hg hgR hm (fun y => dec y t)
      (hdec.comp (measurable_id.prodMk measurable_const)) t).1
  refine ⟨hlb, ⟨fun y t => decide (t < g y), ?_, ?_⟩, ?_⟩
  · apply measurable_to_bool
    convert measurableSet_lt measurable_snd (hg.comp measurable_fst) using 1
    ext p; simp
  · have hdm : Measurable (fun p : (Fin k → ℝ) × ℝ => decide (p.2 < g p.1)) := by
      apply measurable_to_bool
      convert measurableSet_lt measurable_snd (hg.comp measurable_fst) using 1
      ext p; simp
    let Fd : ℝ × (ℝ × (Fin k → ℝ)) → ℝ := fun z =>
      if decide (z.1 < g z.2.2) then c * max 0 (z.1 - z.2.1) else c * max 0 (z.2.1 - z.1)
    have hFd : Measurable Fd := Measurable.ite
      ((hdm.comp (measurable_snd.snd.prodMk measurable_fst)) (measurableSet_singleton true))
      (by fun_prop) (by fun_prop)
    obtain ⟨eD1, iD, -⟩ := dq23_fub P U T Y R hU hT hY hUR hTu hind Fd hFd (c * (2 * R))
      (fun t u y ht hu => dq23_ite_bound R c t u hc ht hu _)
    rw [← hval]
    show ∫ ω, Fd (T ω, (U ω, Y ω)) ∂P = ∫ ω, FW (T ω, (U ω, Y ω)) ∂P
    rw [eW1, eD1]
    congr 1
    funext t
    exact ((dq23_core P U Y R c hR hc hU hY hUR g hg hgR hm (fun y => decide (t < g y))
      (hdm.comp (measurable_id.prodMk measurable_const)) t).2 (fun y => rfl)).symm
  · intro Ω' _ _ ν _ dec hdec
    have hf : Measurable (fun q : Ω × Ω' => if dec q.2 (Y q.1) (T q.1)
        then c * max 0 (T q.1 - U q.1) else c * max 0 (U q.1 - T q.1)) :=
      Measurable.ite ((hdec.comp (measurable_snd.prodMk
        ((hY.comp measurable_fst).prodMk (hT.comp measurable_fst))))
        (measurableSet_singleton true)) (by fun_prop) (by fun_prop)
    have hae : ∀ᵐ q ∂(P.prod ν), T q.1 ∈ Set.Icc (-R) R :=
      Measure.quasiMeasurePreserving_fst.ae (dq23_unif_ae P T R hT hTu)
    have hint : Integrable (fun q : Ω × Ω' => if dec q.2 (Y q.1) (T q.1)
        then c * max 0 (T q.1 - U q.1) else c * max 0 (U q.1 - T q.1)) (P.prod ν) :=
      Integrable.of_bound hf.aestronglyMeasurable (c * (2 * R)) (by
        filter_upwards [hae] with q hq
        rw [Real.norm_eq_abs]
        exact dq23_ite_bound R c _ _ hc hq (hUR q.1) _)
    rw [integral_prod_symm _ hint]
    have hconst : c / (4 * R) * ∫ ω, (U ω - g (Y ω)) ^ 2 ∂P =
        ∫ _s : Ω', c / (4 * R) * ∫ ω, (U ω - g (Y ω)) ^ 2 ∂P ∂ν := by
      simp
    rw [hconst]
    exact integral_mono (integrable_const _) hint.integral_prod_right fun s =>
      hlb (dec s) (hdec.comp (measurable_const.prodMk measurable_id))
