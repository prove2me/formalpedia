-- Prove2me | solution 2 for AvramDividend.Classical.avram_p4_f7_mixed_finitecap_physical_HJB_mean
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:11:33.531918+00:00
-- url     : https://prove2.me/submissions/e8647bd8-7632-4ea7-8685-548b3b37a606
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_finitecap_jump_discounted_clipped_driver_mesh_upper_limit
import Theorems.Thm_AvramDividend_Classical_avram_gfinite74_cap_gap_of_grad
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_same_actual_clipped_grid_fourterm_cash_L1_certificate
import Theorems.Thm_AvramDividend_Classical_avram_b241_original_ruinclipped_allcap_physical_cash_left_to_right_discount_mesh_correction
import Theorems.Thm_AvramDividend_Classical_avram_jump6_finitecap_original_stopped_reward_integrable
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_positive_clock_cash_lastmesh_L1_auto_20261122

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

set_option maxHeartbeats 800000 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hFinite : C ≠ ⊤) :
    (∫ ω, Term ω + Cash ω ∂P) ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let V : ℝ → ℝ := fun z => if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let dPaid : ℝ≥0 → Ω → ℝ := fun t ω =>
    if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω then rightLimit D t ω else D t ω
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X.X t ω - dPaid t ω
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let g : ℕ → ℕ → Ω → ℝ≥0 := fun m i ω => min ((i : ℝ≥0) * Δ m) (τ ω)
  let cell : ℝ≥0 → ℝ≥0 → Ω → ℝ := fun s t ω =>
    (E t - E s) * V (Y t ω) +
      E s * (V (x + X.X t ω - dPaid s ω) - V (Y s ω))
  let Source : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ Finset.range (m + 1),
    cell (g m i ω) (g m (i + 1) ω) ω
  let Err : ℕ → Ω → ℝ := fun m ω =>
    q * (Δ m : ℝ) * (dividendMeasure D ω (Ioo (0 : ℝ) (τ ω : ℝ))).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioo ((τ ω - Δ m : ℝ≥0) : ℝ) (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let active : Ω → Set ℝ := fun ω => paymentTimes (ruinTime X x D ω)
  let discount : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-(q * s)))
  let cash : ℝ≥0 → Ω → ℝ := fun t ω =>
    (∫⁻ s in active ω ∩ Iic (t : ℝ), discount s ∂(dividendMeasure D ω)).toReal
  let cashCell : ℝ≥0 → ℝ≥0 → Ω → ℝ := fun a b ω =>
    (∫⁻ s in active ω ∩ Ioc (a : ℝ) (b : ℝ), discount s ∂(dividendMeasure D ω)).toReal
  let Tail : ℕ → Ω → ℝ := fun m ω =>
    (∫⁻ s in active ω ∩ Ioo ((τ ω - Δ m : ℝ≥0) : ℝ) (τ ω : ℝ),
      discount s ∂(dividendMeasure D ω)).toReal
  have hXcap : x ≤ C.toReal := (ENNReal.ofReal_le_iff_le_toReal hFinite).mp hxc
  have hCnn : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hVl (z : ℝ) (hz : z ≤ C.toReal) : V z = w z := if_pos hz
  have hWhg (p r : ℝ) (hp : 0 ≤ p) (hpr : p ≤ r) (hr : r ≤ C.toReal) :
      r - p ≤ w r - w p := by
    have hInside (z : ℝ) (hz : z ∈ Ioo p r) : 0 < z ∧ ENNReal.ofReal z < C :=
      ⟨hp.trans_lt hz.1, (ENNReal.ofReal_lt_iff_lt_toReal (hp.trans hz.1.le) hFinite).mpr
        (hz.2.trans_le hr)⟩
    apply sub_nonneg.mp
    exact avram_gfinite74_cap_gap_of_grad w p r hpr
      (hw_cont.mono fun z hz => hp.trans hz.1)
      (fun z hz => (hw_smooth.differentiableOn (by norm_num) z (hInside z hz)).differentiableAt
        (mem_of_superset (Ioo_mem_nhds hz.1 hz.2) (fun _ hz' => hInside _ hz')))
      (fun z hz => hw_grad z (hInside z hz).1 (hInside z hz).2)
  have hWmono (p r : ℝ) (hpr : p ≤ r) (hr : r ≤ C.toReal) : w p ≤ w r := by
    by_cases hp : 0 ≤ p
    · linarith only [hWhg p r hp hpr hr, hpr]
    · rw [hw_neg p (lt_of_not_ge hp)]
      by_cases hr0 : 0 ≤ r
      · linarith only [hWhg 0 r le_rfl hr0 hr, hw0, hr0]
      · rw [hw_neg r (lt_of_not_ge hr0)]
  have hVmono : Monotone V := by
    intro p r hpr
    by_cases hr : r ≤ C.toReal
    · rw [hVl _ (hpr.trans hr), hVl _ hr]
      exact hWmono p r hpr hr
    · by_cases hp : p ≤ C.toReal
      · rw [hVl _ hp]
        change w p ≤ (if r ≤ C.toReal then w r else w C.toReal + (r - C.toReal))
        rw [if_neg hr]
        linarith only [hWmono p C.toReal hp le_rfl, lt_of_not_ge hr]
      · simp only [V, if_neg hp, if_neg hr]
        linarith only [hpr]
  have hBefore (ω : Ω) : (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
    rw [hτeq]
    exact ENNReal.coe_toNNReal_le_self.trans (min_le_left _ _)
  have hPreCap (t : ℝ≥0) (ω : Ω) : riskProcess X x D t ω ≤ C.toReal := by
    by_cases ht : t = 0
    · simpa [ht, riskProcess, X.X_zero, hD.1.1.1 ω] using hXcap
    · exact (ENNReal.ofReal_le_iff_le_toReal hFinite).mp
        (hD.2 ω t (lt_of_le_of_ne bot_le (Ne.symm ht)))
  have hYCap (t : ℝ≥0) (ω : Ω) : Y t ω ≤ C.toReal := by
    dsimp only [Y, dPaid]
    split_ifs
    · exact (sub_le_sub_left (dividendStrategy_le_rightLimit D hD.1.1 ω t) _).trans (hPreCap t ω)
    · exact hPreCap t ω
  have hPayFinite (ω : Ω) (t : ℝ≥0) {s : Set ℝ} (hs : s ⊆ Icc (0 : ℝ) (t : ℝ)) :
      (∫⁻ r in s, discount r ∂(dividendMeasure D ω)) < ⊤ := by
    calc
      _ ≤ ∫⁻ r in Icc (0 : ℝ) (t : ℝ), discount r ∂(dividendMeasure D ω) :=
        lintegral_mono_set hs
      _ ≤ ∫⁻ _ in Icc (0 : ℝ) (t : ℝ), (1 : ℝ≥0∞) ∂(dividendMeasure D ω) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        have hr' : 0 ≤ r := hr.1
        have hz : -(q * r) ≤ 0 := neg_nonpos.mpr (mul_nonneg hq.le hr')
        exact (ENNReal.ofReal_le_ofReal (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hz)).trans_eq ENNReal.ofReal_one
      _ < ⊤ := by
        rw [lintegral_one, Measure.restrict_apply_univ,
          avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD.1.1 ω t]
        exact ENNReal.ofReal_lt_top
  have hCashAdd (a b : ℝ≥0) (ω : Ω) (hab : a ≤ b) : cash b ω = cash a ω + cashCell a b ω := by
    have hAB : active ω ∩ Iic (b : ℝ) =
        (active ω ∩ Iic (a : ℝ)) ∪ (active ω ∩ Ioc (a : ℝ) (b : ℝ)) := by
      rw [← inter_union_distrib_left, Iic_union_Ioc_eq_Iic (by exact_mod_cast hab)]
    have hDisjoint : Disjoint (active ω ∩ Iic (a : ℝ)) (active ω ∩ Ioc (a : ℝ) (b : ℝ)) :=
      (Iic_disjoint_Ioi le_rfl).mono inter_subset_right (inter_subset_right.trans Ioc_subset_Ioi_self)
    have hMeas : MeasurableSet (active ω ∩ Ioc (a : ℝ) (b : ℝ)) :=
      (paymentTimes_measurable _).inter measurableSet_Ioc
    have hFa : (∫⁻ r in active ω ∩ Iic (a : ℝ), discount r ∂(dividendMeasure D ω)) ≠ ⊤ :=
      (hPayFinite ω a (fun _ hs => ⟨hs.1.1, hs.2⟩)).ne
    have hFab : (∫⁻ r in active ω ∩ Ioc (a : ℝ) (b : ℝ), discount r ∂(dividendMeasure D ω)) ≠ ⊤ :=
      (hPayFinite ω b (fun _ hs => ⟨hs.1.1, hs.2.2⟩)).ne
    dsimp only [cash, cashCell]
    rw [hAB, lintegral_union hMeas hDisjoint, ENNReal.toReal_add hFa hFab]
  have hInitial (ω : Ω) : cash 0 ω + E 0 * V (Y 0 ω) ≤ w x := by
    have hA0 : active ω ∩ Iic ((0 : ℝ≥0) : ℝ) = ({0} : Set ℝ) := by
      ext s
      simp only [NNReal.coe_zero, active, paymentTimes, mem_inter_iff, mem_setOf_eq,
        mem_Iic, mem_singleton_iff]
      exact ⟨fun h => le_antisymm h.2 h.1.1, fun hz => hz.symm ▸ ⟨⟨le_rfl, Or.inl rfl⟩, le_rfl⟩⟩
    have hR0 : 0 ≤ rightLimit D 0 ω := by
      simpa only [hD.1.1.1 ω] using dividendStrategy_le_rightLimit D hD.1.1 ω 0
    have hAtom : dividendMeasure D ω ({0} : Set ℝ) = ENNReal.ofReal (rightLimit D 0 ω) := by
      simpa only [NNReal.coe_zero, hD.1.1.1 ω, sub_zero] using
        dividendMeasure_singleton_eq_rightLimit_sub D hD.1.1 ω 0
    have hCash0 : cash 0 ω = rightLimit D 0 ω := by
      dsimp only [cash]
      rw [hA0, lintegral_singleton, hAtom]
      simp [discount, ENNReal.toReal_ofReal hR0]
    have hy : Y 0 ω = x - rightLimit D 0 ω := by simp [Y, dPaid, X.X_zero]
    have hJ := hjump ω 0 (Or.inl rfl)
    rw [hCash0, hVl _ (hYCap 0 ω), hy]
    simp only [riskProcess, X.X_zero, hD.1.1.1 ω, add_zero, sub_zero] at hJ
    simp only [E, NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero, one_mul]
    linarith only [hJ]
  have hGridStep (m i : ℕ) (ω : Ω) :
      g m i ω ≤ g m (i + 1) ω ∧ g m (i + 1) ω ≤ g m i ω + Δ m := by
    dsimp only [g]
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact ⟨min_le_min (le_add_of_nonneg_right (by positivity)) le_rfl, by
      rw [← min_add_add_right]
      exact min_le_min le_rfl (le_add_of_nonneg_right (by positivity))⟩
  have hGridClock (m i : ℕ) (ω : Ω) : g m i ω ≤ τ ω := min_le_right _ _
  have hFinal (m : ℕ) (ω : Ω) : g m (m + 1) ω = τ ω := by
    have hc := (avram_pj_workerC_same_actual_clipped_grid_fourterm_cash_L1_certificate
      X hX x C D hD q hq n hn τ τ hτeq hτstop (fun _ => le_rfl) w m ω).1.1
    simpa only [g, Δ, min_self] using hc
  have hOneCell (m i : ℕ) (ω : Ω) :
      cash (g m (i + 1) ω) ω + E (g m (i + 1) ω) * V (Y (g m (i + 1) ω) ω) ≤
        (cash (g m i ω) ω + E (g m i ω) * V (Y (g m i ω) ω)) +
        cell (g m i ω) (g m (i + 1) ω) ω +
        ((if g m (i + 1) ω = τ ω then Tail m ω else 0) -
          (if g m i ω = τ ω then Tail m ω else 0)) := by
    let a := g m i ω
    let b := g m (i + 1) ω
    change cash b ω + E b * V (Y b ω) ≤
      (cash a ω + E a * V (Y a ω)) + cell a b ω +
        ((if b = τ ω then Tail m ω else 0) - (if a = τ ω then Tail m ω else 0))
    have hab : a ≤ b := (hGridStep m i ω).1
    have hbτ : b ≤ τ ω := hGridClock m (i + 1) ω
    by_cases hSame : a = b
    · simp [hSame, cell, Y]
    have hab' : a < b := lt_of_le_of_ne hab hSame
    have haτ : a ≠ τ ω := ne_of_lt (hab'.trans_le hbτ)
    have hbR : (b : ℝ≥0∞) ≤ ruinTime X x D ω :=
      (ENNReal.coe_le_coe.mpr hbτ).trans (hBefore ω)
    have haR : (a : ℝ≥0∞) < ruinTime X x D ω :=
      (ENNReal.coe_lt_coe.mpr hab').trans_le hbR
    have hPaidA : dPaid a ω = rightLimit D a ω := if_pos (Or.inr haR)
    have hTailNN : 0 ≤ Tail m ω := ENNReal.toReal_nonneg
    have hCashStep := hCashAdd a b ω hab
    have hCellBound : cashCell a b ω + E a *
        (V (Y b ω) - V (x + X.X b ω - dPaid a ω)) ≤
        (if b = τ ω then Tail m ω else 0) := by
      by_cases hbPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω
      · have hbSurv : (b : ℝ≥0∞) < ruinTime X x D ω := by
          rcases hbPre with hz | hp
          · exfalso
            exact (not_lt_of_ge bot_le) (hz ▸ hab')
          · exact hp
        have hDomain : active ω ∩ Ioc (a : ℝ) (b : ℝ) = Ioc (a : ℝ) (b : ℝ) := by
          apply inter_eq_right.mpr
          intro s hs
          have hs0 : 0 ≤ s := (NNReal.coe_nonneg a).trans hs.1.le
          exact ⟨hs0, Or.inr ((ENNReal.ofReal_le_ofReal hs.2).trans_lt
            (by simpa only [ENNReal.ofReal_coe_nnreal] using hbSurv))⟩
        have hPaidB : dPaid b ω = rightLimit D b ω := if_pos hbPre
        have hDisc := avram_b241_original_ruinclipped_allcap_physical_cash_left_to_right_discount_mesh_correction
          X x q hq.le C hC w hw_cont (hw_smooth.of_le (by norm_num)) hw_grad D hD ω a b hab hbPre
        have hDisc' : cashCell a b ω + E b *
            (V (Y b ω) - V (x + X.X b ω - dPaid a ω)) ≤
          (E a - E b) * (V (x + X.X b ω - dPaid a ω) - V (Y b ω)) := by
          simpa only [cashCell, hDomain, discount, E, Y, hPaidA, hPaidB, V, if_neg hFinite] using hDisc
        have h0 : cashCell a b ω + E a *
            (V (Y b ω) - V (x + X.X b ω - dPaid a ω)) ≤ 0 := by
          linarith only [hDisc']
        exact h0.trans (by split_ifs <;> positivity)
      · have hEqR : (b : ℝ≥0∞) = ruinTime X x D ω :=
          le_antisymm hbR (le_of_not_gt fun h => hbPre (Or.inr h))
        have hEqτ : b = τ ω := le_antisymm hbτ (ENNReal.coe_le_coe.mp (hEqR ▸ hBefore ω))
        have hPaidB : dPaid b ω = D b ω := if_neg hbPre
        have hRight : rightLimit D a ω ≤ D b ω := by
          have hLower : BddBelow (Set.range (fun s : Ioi a => D s.1 ω)) := by
            refine ⟨D a ω, ?_⟩
            rintro _ ⟨s, rfl⟩
            exact hD.1.1.2.1 ω s.2.le
          exact ciInf_le hLower (⟨b, hab'⟩ : Ioi a)
        have hVle : V (Y b ω) ≤ V (x + X.X b ω - dPaid a ω) :=
          hVmono (by dsimp only [Y]; rw [hPaidA, hPaidB]; linarith only [hRight])
        have hDist : τ ω - Δ m ≤ a :=
          tsub_le_iff_right.mpr (hEqτ ▸ (hGridStep m i ω).2)
        have hSub : active ω ∩ Ioc (a : ℝ) (b : ℝ) ⊆
            active ω ∩ Ioo ((τ ω - Δ m : ℝ≥0) : ℝ) (τ ω : ℝ) := by
          intro s hs
          refine ⟨hs.1, (by exact_mod_cast hDist : ((τ ω - Δ m : ℝ≥0) : ℝ) ≤ (a : ℝ)).trans_lt hs.2.1, ?_⟩
          have h0 : 0 ≤ s := hs.1.1
          have hlt : ENNReal.ofReal s < (b : ℝ≥0∞) := by
            rw [hEqR]
            rcases hs.1.2 with hz | hl
            · exact False.elim ((not_lt_of_ge (NNReal.coe_nonneg a)) (hz ▸ hs.2.1))
            · exact hl
          rw [← ENNReal.ofNNReal_toNNReal] at hlt
          have hltn : s.toNNReal < b := ENNReal.coe_lt_coe.mp hlt
          have hltr : (s.toNNReal : ℝ) < (b : ℝ) := by exact_mod_cast hltn
          simpa only [Real.coe_toNNReal s h0, hEqτ] using hltr
        have hTailfinite : (∫⁻ s in active ω ∩ Ioo ((τ ω - Δ m : ℝ≥0) : ℝ) (τ ω : ℝ),
            discount s ∂(dividendMeasure D ω)) ≠ ⊤ :=
          (hPayFinite ω (τ ω) (fun _ hs => ⟨hs.1.1, hs.2.2.le⟩)).ne
        have hCashLe : cashCell a b ω ≤ Tail m ω :=
          ENNReal.toReal_mono hTailfinite (lintegral_mono_set hSub)
        rw [if_pos hEqτ]
        have hEa : 0 ≤ E a := (Real.exp_pos _).le
        exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hEa (sub_nonpos.mpr hVle))).trans hCashLe
    rw [if_neg haτ]
    dsimp only [cell]
    linarith only [hCashStep, hCellBound]
  have hPath (m : ℕ) (ω : Ω) : Term ω + Cash ω ≤ w x + Source m ω + Err m ω := by
    have hLedger (j : ℕ) : cash (g m j ω) ω + E (g m j ω) * V (Y (g m j ω) ω) ≤
        w x + (∑ i ∈ Finset.range j, cell (g m i ω) (g m (i + 1) ω) ω) +
          (if g m j ω = τ ω then Tail m ω else 0) := by
      induction j with
      | zero =>
        have h00 : g m 0 ω = 0 := by simp [g]
        rw [h00]
        simp only [Finset.range_zero, Finset.sum_empty, add_zero]
        apply (hInitial ω).trans
        apply le_add_of_nonneg_right
        split_ifs
        · exact ENNReal.toReal_nonneg
        · exact le_rfl
      | succ j ih =>
        rw [Finset.sum_range_succ]
        linarith only [ih, hOneCell m j ω]
    have hEnd := hLedger (m + 1)
    rw [hFinal m ω, if_pos rfl, hVl _ (hYCap (τ ω) ω)] at hEnd
    have hY : Y (τ ω) ω = W ω := by
      rw [hW ω]
      dsimp only [Y, dPaid, riskProcess]
      split_ifs <;> rfl
    have hCeq : cash (τ ω) ω = Cash ω := (hCash ω).symm
    rw [hY, hCeq, show E (τ ω) * w (W ω) = Term ω by exact (hTerm ω).symm] at hEnd
    have hTailLe : Tail m ω ≤ Err m ω := by
      apply le_add_of_nonneg_left
      positivity
    linarith only [hEnd, hTailLe]
  have hFI := avram_jump6_finitecap_original_stopped_reward_integrable
    X x C hFinite hxc D hD q hq.le w hw_cont hw_neg n hn τ hτeq hτstop
    W Cash Term hW hCash hTerm
  by_contra! hFail
  let ε : ℝ := ((∫ ω, Term ω + Cash ω ∂P) - w x) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith only [hFail]
  obtain ⟨N₁, hN₁⟩ := finitecap_jump_discounted_clipped_driver_mesh_upper_limit
    X hX hBV hν q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop hFinite ε hε
  obtain ⟨N₂, hN₂⟩ := avram_oai_original_positive_clock_cash_lastmesh_L1_auto_20261122
    X hX x C D hD q hq n hn τ hτeq (fun _ => τ) (fun _ => hτstop) (fun _ _ => le_rfl) 0 ε hε
  let m := max N₁ N₂
  have hS : Integrable (Source m) P ∧ (∫ ω, Source m ω ∂P) ≤ ε := hN₁ m (le_max_left _ _)
  have hErr : Integrable (Err m) P ∧ (∫ ω, |Err m ω| ∂P) ≤ ε := hN₂ m (le_max_right _ _)
  have hErrLe : (∫ ω, Err m ω ∂P) ≤ ε :=
    (integral_mono_ae hErr.1 hErr.1.abs (Eventually.of_forall fun ω => le_abs_self _)).trans hErr.2
  have hUpper := integral_mono_ae hFI
      (((integrable_const (w x)).add hS.1).add hErr.1)
      (Eventually.of_forall (hPath m))
  have hSplitInt : (∫ ω, w x + Source m ω + Err m ω ∂P) =
      w x + (∫ ω, Source m ω ∂P) + (∫ ω, Err m ω ∂P) := by
    have hConst : Integrable (fun _ : Ω => w x) P := integrable_const _
    have hFirst : (∫ ω, w x + Source m ω ∂P) =
        (∫ _ : Ω, w x ∂P) + (∫ ω, Source m ω ∂P) := by
      simpa only [Pi.add_apply] using integral_add hConst hS.1
    have hSecond : (∫ ω, w x + Source m ω + Err m ω ∂P) =
        (∫ ω, w x + Source m ω ∂P) + (∫ ω, Err m ω ∂P) := by
      simpa only [Pi.add_apply] using integral_add (hConst.add hS.1) hErr.1
    rw [hSecond, hFirst]
    simp
  have hh := hUpper.trans_eq hSplitInt
  dsimp only [ε] at hS hErrLe
  linarith only [hh, hS.2, hErrLe, hFail]
