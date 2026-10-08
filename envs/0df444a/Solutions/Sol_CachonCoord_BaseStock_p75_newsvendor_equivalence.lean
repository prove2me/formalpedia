-- Prove2me | solution 1 for CachonCoord.BaseStock.p75_newsvendor_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:50:22.687603+00:00
-- url     : https://prove2.me/submissions/c3752ca2-a222-441d-b4a7-abc854a41873

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory


namespace CachonCoord.BaseStock

namespace Model

theorem bsF_mono (M : Model) : Monotone M.F := by
  intro a b h; exact ProbabilityTheory.monotone_cdf M.law h

theorem bsF_zero (M : Model) : M.F 0 = 0 := M.cdfZero

theorem bsF_nonpos (M : Model) {y : ℝ} (hy : y ≤ 0) : M.F y = 0 := by
  have h1 := bsF_mono M hy
  rw [bsF_zero] at h1
  have h2 : 0 ≤ M.F y := ProbabilityTheory.cdf_nonneg _ _
  linarith

theorem bsF_cont (M : Model) : Continuous M.F := M.cdfContinuous

theorem bsF_lt (M : Model) {a b : ℝ} (hab : a < b) (hb : 0 < b) : M.F a < M.F b := by
  have h1 : M.F a ≤ M.F (max a 0) := bsF_mono M (le_max_left _ _)
  have h2 : M.F (max a 0) < M.F b :=
    M.cdfStrict (Set.mem_Ici.2 (le_max_right _ _)) (Set.mem_Ici.2 hb.le) (max_lt hab hb)
  linarith

theorem bsF_lt' (M : Model) {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) : M.F a < M.F b :=
  M.cdfStrict (Set.mem_Ici.2 ha) (Set.mem_Ici.2 (ha.trans hab.le)) hab

theorem bs_int_max (M : Model) (y : ℝ) : Integrable (fun x => max (y - x) 0) M.law := by
  have := M.probability
  exact ((integrable_const y).sub M.finiteMean).pos_part

theorem bs_int_max' (M : Model) (y : ℝ) : Integrable (fun x => max (x - y) 0) M.law := by
  have := M.probability
  exact (M.finiteMean.sub (integrable_const y)).pos_part

theorem bs_eq29 (M : Model) (y : ℝ) : M.B y = M.meanDemand - y + M.I y := by
  have := M.probability
  unfold B meanDemand I
  have h : (fun x : ℝ => max (x - y) 0) = fun x => (x - y) + max (y - x) 0 := by
    funext x
    rcases le_total x y with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hid : Integrable (fun x : ℝ => x) M.law := M.finiteMean
  have h1 : Integrable (fun x : ℝ => x - y) M.law := hid.sub (integrable_const y)
  rw [h, integral_add h1 (bs_int_max M y), integral_sub hid (integrable_const y)]
  simp

theorem bs_ae_nonneg (M : Model) : ∀ᵐ x ∂M.law, 0 ≤ x := by
  have := (measure_eq_zero_iff_ae_notMem.1 M.nonnegativeDemand)
  filter_upwards [this] with x hx
  simpa using hx

theorem bs_density_int (M : Model) {y : ℝ} (hy : 0 ≤ y) :
    IntervalIntegrable M.density volume 0 y := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy]
  exact intervalIntegral.integrableOn_deriv_of_nonneg (M.cdfContinuous.continuousOn)
    (fun x hx => M.cdfHasDeriv x hx.1) (fun x _ => M.density_nonneg x)

theorem bs_I_density (M : Model) {y : ℝ} (hy : 0 ≤ y) :
    M.I y = ∫ x in (0 : ℝ)..y, (y - x) * M.density x := by
  unfold I
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero (s := Set.Icc 0 y)]
  swap
  · filter_upwards [bs_ae_nonneg M] with x hx hxs
    have : y < x := by
      by_contra h; exact hxs ⟨hx, not_lt.1 h⟩
    exact max_eq_right (by linarith)
  rw [M.law_eq_withDensity, restrict_withDensity measurableSet_Icc,
    integral_withDensity_eq_integral_toReal_smul (f := fun y => ENNReal.ofReal (M.density y))
      M.density_measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [intervalIntegral.integral_of_le hy, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc ?_
  intro x hx
  simp only [Function.comp, smul_eq_mul, ENNReal.toReal_ofReal (M.density_nonneg x)]
  rw [max_eq_left (by linarith [hx.2])]; ring

theorem bs_I_F_nonneg (M : Model) {y : ℝ} (hy : 0 ≤ y) :
    M.I y = ∫ x in (0 : ℝ)..y, M.F x := by
  rw [bs_I_density M hy]
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) y,
      HasDerivAt (fun x => (y - x) * M.F x) (-M.F x + (y - x) * M.density x) x := by
    intro x hx
    have := ((hasDerivAt_id x).const_sub y).mul (M.cdfHasDeriv x hx.1)
    exact this.congr_deriv (by simp only [id, F]; ring)
  have hint1 : IntervalIntegrable (fun x => (y - x) * M.density x) volume 0 y :=
    (bs_density_int M hy).continuousOn_mul (by fun_prop)
  have hint2 : IntervalIntegrable M.F volume 0 y := (bsF_cont M).intervalIntegrable _ _
  have hint2' : IntervalIntegrable (fun x => -M.F x) volume 0 y := hint2.neg
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hy
    (by have := bsF_cont M; fun_prop) hderiv (hint2'.add hint1)
  rw [intervalIntegral.integral_add hint2' hint1, intervalIntegral.integral_neg] at key
  simp only [sub_self, zero_mul, bsF_zero, mul_zero, sub_zero] at key
  linarith

theorem bs_I_F (M : Model) (y : ℝ) : M.I y = ∫ x in (0 : ℝ)..y, M.F x := by
  rcases le_total 0 y with hy | hy
  · exact bs_I_F_nonneg M hy
  · have h1 : M.I y = 0 := by
      unfold I
      rw [integral_eq_zero_of_ae]
      filter_upwards [bs_ae_nonneg M] with x hx
      simp only [Pi.zero_apply]
      exact max_eq_right (by linarith)
    rw [h1, intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro x hx
      rw [Set.uIcc_of_ge hy] at hx
      exact bsF_nonpos M hx.2

theorem bs_I_deriv (M : Model) (y : ℝ) : HasDerivAt M.I (M.F y) y := by
  have : M.I = fun u => ∫ x in (0 : ℝ)..u, M.F x := funext (bs_I_F M)
  rw [this]
  exact ((bsF_cont M).integral_hasStrictDerivAt 0 y).hasDerivAt

theorem bs_chain_formula (M : Model) (s : ℝ) :
    M.chainCost s = M.beta * (M.meanDemand - s) + (M.hr + M.beta) * M.I s := by
  unfold chainCost retailerCost supplierCost beta
  rw [bs_eq29]; ring

theorem bs_retailer_formula (M : Model) (s : ℝ) :
    M.retailerCost s = M.br * (M.meanDemand - s) + (M.hr + M.br) * M.I s := by
  unfold retailerCost
  rw [bs_eq29]; ring

/-- generic analysis of `A (μ - s) + C I(s)` -/
theorem bs_generic (M : Model) (A C : ℝ) (hA : 0 < A) (hAC : A < C) :
    StrictConvexOn ℝ (Set.Ici 0) (fun s => A * (M.meanDemand - s) + C * M.I s) ∧
    ∃ so : ℝ, 0 < so ∧ M.F so = A / C ∧
      ∀ s, s ≠ so → (A * (M.meanDemand - so) + C * M.I so) < A * (M.meanDemand - s) + C * M.I s := by
  set f : ℝ → ℝ := fun s => A * (M.meanDemand - s) + C * M.I s with hf
  have hC : 0 < C := by linarith
  have hd : ∀ s, HasDerivAt f (-A + C * M.F s) s := by
    intro s
    have := ((hasDerivAt_id s).const_sub M.meanDemand).const_mul A |>.add
      ((bs_I_deriv M s).const_mul C)
    exact this.congr_deriv (by ring)
  have hderiv : deriv f = fun s => -A + C * M.F s := funext fun s => (hd s).deriv
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun s => (hd s).continuousAt
  refine ⟨?_, ?_⟩
  · apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0) hcont.continuousOn
    rw [hderiv, interior_Ici]
    intro a ha b hb hab
    have := bsF_lt' M hab (le_of_lt ha)
    nlinarith
  · have ht : A / C < 1 := by rw [div_lt_one hC]; exact hAC
    have ht0 : 0 < A / C := div_pos hA hC
    obtain ⟨b, hb⟩ := ((ProbabilityTheory.tendsto_cdf_atTop M.law).eventually
      (lt_mem_nhds ht)).exists
    have hb' : A / C < M.F b := hb
    have hb0 : 0 < b := by
      by_contra h
      rw [bsF_nonpos M (not_lt.1 h)] at hb'; linarith
    obtain ⟨so, hso, hFso⟩ := intermediate_value_Icc hb0.le (bsF_cont M).continuousOn
      ⟨by rw [bsF_zero]; exact ht0.le, hb'.le⟩
    have hso0 : 0 < so := by
      rcases hso.1.eq_or_lt with h | h
      · rw [← h, bsF_zero] at hFso; linarith
      · exact h
    refine ⟨so, hso0, hFso, ?_⟩
    intro s hs
    show f so < f s
    rcases lt_or_gt_of_ne hs with h | h
    · have := strictAntiOn_of_deriv_neg (convex_Icc s so) hcont.continuousOn (by
        intro x hx
        rw [interior_Icc] at hx
        rw [hderiv]
        have := bsF_lt M hx.2 hso0
        rw [hFso] at this
        have : C * M.F x < C * (A / C) := mul_lt_mul_of_pos_left this hC
        rw [mul_div_cancel₀ _ hC.ne'] at this
        linarith)
      exact this ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h
    · have := strictMonoOn_of_deriv_pos (convex_Icc so s) hcont.continuousOn (by
        intro x hx
        rw [interior_Icc] at hx
        rw [hderiv]
        have := bsF_lt' M hx.1 hso0.le
        rw [hFso] at this
        have : C * (A / C) < C * M.F x := mul_lt_mul_of_pos_left this hC
        rw [mul_div_cancel₀ _ hC.ne'] at this
        linarith)
      exact this ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h

theorem bs_isMin_of_strict {f : ℝ → ℝ} {so : ℝ} (h : ∀ s, s ≠ so → f so < f s) :
    IsMinOn f Set.univ so ∧ ∀ s, IsMinOn f Set.univ s → s = so := by
  refine ⟨fun s _ => ?_, fun s hs => ?_⟩
  · by_cases hs : s = so
    · show f so ≤ f s
      rw [hs]
    · exact (h s hs).le
  · by_contra hne
    have := hs (Set.mem_univ so)
    have := h s hne
    simp only [Set.mem_setOf_eq] at *
    linarith

end Model

open Model

theorem eq_29_core (M : Model) : ∀ y : ℝ, M.B y = M.meanDemand - y + M.I y :=
  fun y => bs_eq29 M y

theorem eq_28_core (M : Model) :
    ∀ y : ℝ, 0 ≤ y →
      M.I y = ∫ x in (0 : ℝ)..y, (y - x) * M.density x ∧
      M.I y = ∫ x in (0 : ℝ)..y, M.F x :=
  fun _ hy => ⟨bs_I_density M hy, bs_I_F M _⟩

theorem p75_transfer_decomposition_core (M : Model) :
    ∀ tI tB y : ℝ,
      tI * M.I y + tB * M.B y = (tI + tB) * M.I y + tB * (M.meanDemand - y) := by
  intro tI tB y; rw [bs_eq29]; ring

theorem bs_contracted (M : Model) (lam s : ℝ) :
    M.contractedRetailerCost lam s = lam * M.chainCost s ∧
    M.contractedSupplierCost lam s = (1 - lam) * M.chainCost s := by
  unfold contractedRetailerCost contractedSupplierCost transfer tI tB chainCost
    retailerCost supplierCost Model.beta
  constructor <;> ring

theorem eq_32_core (M : Model) :
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      (∀ s : ℝ, M.contractedRetailerCost lam s =
        (M.br - M.tB lam) * (M.meanDemand - s) +
          (M.hr + M.br - M.tI lam - M.tB lam) * M.I s) ∧
      M.br - M.tB lam = lam * M.beta ∧
      0 < M.br - M.tB lam ∧
      M.hr + M.br - M.tI lam - M.tB lam = lam * (M.hr + M.beta) ∧
      0 < M.hr + M.br - M.tI lam - M.tB lam := by
  intro lam hl _
  have hb : 0 < M.beta := by unfold Model.beta; linarith [M.br_pos, M.bs_pos]
  have e1 : M.br - M.tB lam = lam * M.beta := by unfold tB; ring
  have e2 : M.hr + M.br - M.tI lam - M.tB lam = lam * (M.hr + M.beta) := by
    unfold tB tI Model.beta; ring
  refine ⟨fun s => ?_, e1, by rw [e1]; positivity, e2, by rw [e2]; have := M.hr_pos; positivity⟩
  rw [(bs_contracted M lam s).1, bs_chain_formula, e1, e2]; ring

theorem p74_transfer_signs_core (M : Model) :
    (∀ lam : ℝ, 0 < lam → lam ≤ 1 → 0 ≤ M.tI lam ∧ (0 < M.tI lam ↔ lam < 1)) ∧
    M.tB '' Set.Ioc 0 1 = Set.Ico (-M.bs) M.br ∧
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ 0 < M.tB lam := by
  have hr := M.hr_pos
  have hbr := M.br_pos
  have hbs := M.bs_pos
  have hb : 0 < M.beta := by unfold Model.beta; linarith
  refine ⟨fun lam _ hl1 => ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold tI; nlinarith
  · unfold tI
    constructor
    · intro h; by_contra h'; push_neg at h'; nlinarith
    · intro h; nlinarith
  · ext t
    simp only [Set.mem_image, Set.mem_Ioc, Set.mem_Ico]
    constructor
    · rintro ⟨l, ⟨h0, h1⟩, rfl⟩
      unfold tB Model.beta at *
      constructor <;> nlinarith
    · rintro ⟨h0, h1⟩
      refine ⟨(M.br - t) / M.beta, ⟨div_pos (by linarith) hb, ?_⟩, ?_⟩
      · rw [div_le_one hb]; unfold Model.beta; linarith
      · unfold tB; field_simp; ring
  · refine ⟨M.br / (2 * M.beta), div_pos hbr (by linarith), ?_, ?_⟩
    · rw [div_le_one (by linarith)]; unfold Model.beta; linarith
    · have : M.br / (2 * M.beta) * M.beta = M.br / 2 := by field_simp
      unfold tB; rw [this]; linarith

theorem eq_30_core (M : Model) :
    (∀ s : ℝ, M.chainCost s =
      M.beta * (M.meanDemand - s) + (M.hr + M.beta) * M.I s) ∧
    StrictConvexOn ℝ (Set.Ici 0) M.chainCost := by
  have hb : 0 < M.beta := by unfold Model.beta; linarith [M.br_pos, M.bs_pos]
  have hf : M.chainCost = fun s => M.beta * (M.meanDemand - s) + (M.hr + M.beta) * M.I s :=
    funext (bs_chain_formula M)
  refine ⟨bs_chain_formula M, ?_⟩
  rw [hf]
  exact (bs_generic M M.beta (M.hr + M.beta) hb (by linarith [M.hr_pos])).1

theorem bs_chain_opt (M : Model) :
    ∃ so : ℝ, 0 < so ∧ M.F so = M.beta / (M.hr + M.beta) ∧
      IsMinOn M.chainCost Set.univ so ∧
      ∀ s : ℝ, IsMinOn M.chainCost Set.univ s → s = so := by
  have hb : 0 < M.beta := by unfold Model.beta; linarith [M.br_pos, M.bs_pos]
  have hf : M.chainCost = fun s => M.beta * (M.meanDemand - s) + (M.hr + M.beta) * M.I s :=
    funext (bs_chain_formula M)
  obtain ⟨so, h0, hF, hs⟩ := (bs_generic M M.beta (M.hr + M.beta) hb (by linarith [M.hr_pos])).2
  rw [hf]
  exact ⟨so, h0, hF, bs_isMin_of_strict (f := fun s => M.beta * (M.meanDemand - s) + (M.hr + M.beta) * M.I s) hs⟩

theorem eq_31_core (M : Model) :
    ∃ so : ℝ, 0 < so ∧ HasDerivAt M.I (M.F so) so ∧
      M.F so = M.beta / (M.hr + M.beta) ∧
      IsMinOn M.chainCost Set.univ so ∧
      ∀ s : ℝ, IsMinOn M.chainCost Set.univ s → s = so := by
  obtain ⟨so, h0, hF, h1, h2⟩ := bs_chain_opt M
  exact ⟨so, h0, bs_I_deriv M so, hF, h1, h2⟩

theorem p73_retailer_bias_core (M : Model) :
    StrictConvexOn ℝ (Set.Ici 0) M.retailerCost ∧
    ∃ sr so : ℝ, 0 < sr ∧ sr < so ∧
      M.F sr = M.br / (M.hr + M.br) ∧
      M.F so = M.beta / (M.hr + M.beta) ∧
      IsMinOn M.retailerCost Set.univ sr ∧
      IsMinOn M.chainCost Set.univ so ∧
      (∀ s : ℝ, IsMinOn M.retailerCost Set.univ s → s = sr) ∧
      (∀ s : ℝ, IsMinOn M.chainCost Set.univ s → s = so) := by
  have hr := M.hr_pos
  have hbr := M.br_pos
  have hbs := M.bs_pos
  have hf : M.retailerCost = fun s => M.br * (M.meanDemand - s) + (M.hr + M.br) * M.I s :=
    funext (bs_retailer_formula M)
  have G := bs_generic M M.br (M.hr + M.br) hbr (by linarith)
  obtain ⟨sr, hsr0, hFr, hsr⟩ := G.2
  obtain ⟨so, h0, hF, h1, h2⟩ := bs_chain_opt M
  have hm := bs_isMin_of_strict (f := fun s => M.br * (M.meanDemand - s) + (M.hr + M.br) * M.I s) hsr
  rw [← hf] at hm
  refine ⟨hf ▸ G.1, sr, so, hsr0, ?_, hFr, hF, hm.1, h1, hm.2, h2⟩
  by_contra hle
  push_neg at hle
  have := bsF_mono M hle
  rw [hFr, hF] at this
  have hb : M.beta = M.br + M.bs := rfl
  rw [div_le_div_iff₀ (by linarith) (by linarith), hb] at this
  nlinarith

theorem bs_chain_pos (M : Model) (s : ℝ) : 0 < M.chainCost s := by
  obtain ⟨so, h0, _, hmin, _⟩ := bs_chain_opt M
  have hle : M.chainCost so ≤ M.chainCost s := hmin (Set.mem_univ s)
  have hI : 0 < M.I so := by
    rw [bs_I_F M so]
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      ((bsF_cont M).intervalIntegrable _ _) _ h0
    intro x hx
    have := bsF_lt' M hx.1 le_rfl
    rwa [bsF_zero] at this
  have hB : 0 ≤ M.B so := integral_nonneg (fun x => le_max_right _ _)
  have : 0 < M.chainCost so := by
    unfold chainCost retailerCost supplierCost
    have := M.hr_pos; have := M.br_pos; have := M.bs_pos
    positivity
  linarith

theorem eq_33_core (M : Model) :
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      (∀ s : ℝ, M.contractedRetailerCost lam s = lam * M.chainCost s ∧
        M.contractedSupplierCost lam s = (1 - lam) * M.chainCost s) ∧
      (∀ s : ℝ, StrictMonoOn (fun l => M.contractedRetailerCost l s) (Set.Ioc 0 1)) ∧
      ∃ so : ℝ, 0 < so ∧ M.F so = M.beta / (M.hr + M.beta) ∧
        IsMinOn M.chainCost Set.univ so ∧
        IsMinOn (M.contractedRetailerCost lam) Set.univ so ∧
        (∀ s : ℝ, IsMinOn M.chainCost Set.univ s → s = so) ∧
        (∀ s : ℝ, IsMinOn (M.contractedRetailerCost lam) Set.univ s → s = so) := by
  intro lam hl _
  have hc : ∀ l, M.contractedRetailerCost l = fun s => l * M.chainCost s :=
    fun l => funext fun s => (bs_contracted M l s).1
  refine ⟨bs_contracted M lam, fun s => ?_, ?_⟩
  · intro a _ b _ hab
    simp only [hc]
    exact mul_lt_mul_of_pos_right hab (bs_chain_pos M s)
  · obtain ⟨so, h0, hF, hmin, huniq⟩ := bs_chain_opt M
    refine ⟨so, h0, hF, hmin, ?_, huniq, ?_⟩
    · intro s _
      rw [hc]
      show lam * M.chainCost so ≤ lam * M.chainCost s
      exact mul_le_mul_of_nonneg_left (hmin (Set.mem_univ s)) hl.le
    · intro s hs
      apply huniq
      intro t _
      have := hs (Set.mem_univ t)
      rw [hc] at this
      change lam * M.chainCost s ≤ lam * M.chainCost t at this
      show M.chainCost s ≤ M.chainCost t
      exact le_of_mul_le_mul_left this hl

theorem bs_int_min (M : Model) (q : ℝ) : Integrable (fun d => min q d) M.law := by
  have := M.probability
  have h : (fun d : ℝ => min q d) = fun d => q - max (q - d) 0 := by
    funext d
    rcases le_total q d with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  rw [h]
  exact (integrable_const q).sub (bs_int_max M q)

theorem bs_sales (M : Model) (q : ℝ) :
    SupplyChainTheory.expSales M.law q = q - SupplyChainTheory.expLeftover M.law q := by
  have := M.probability
  unfold SupplyChainTheory.expSales SupplyChainTheory.expLeftover
  have h : (fun d : ℝ => min q d) = fun d => q - max (q - d) 0 := by
    funext d
    rcases le_total q d with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  rw [h, integral_sub (integrable_const q) (bs_int_max M q)]
  simp

theorem p75_newsvendor_equivalence_core (M : Model) :
    (∀ p w q : ℝ,
      p * SupplyChainTheory.expSales M.law q - w * q =
        (p - w) * q - p * SupplyChainTheory.expLeftover M.law q) ∧
    (∀ q : ℝ,
      (M.hr + M.br) * SupplyChainTheory.expSales M.law q - M.hr * q =
        M.br * q - (M.hr + M.br) * M.I q ∧
      M.br * q - (M.hr + M.br) * M.I q = -M.retailerCost q + M.br * M.meanDemand) ∧
    ∀ q : ℝ,
      IsMaxOn (fun x => (M.hr + M.br) * SupplyChainTheory.expSales M.law x - M.hr * x)
          Set.univ q ↔
        IsMinOn M.retailerCost Set.univ q := by
  have hL : ∀ q, SupplyChainTheory.expLeftover M.law q = M.I q := fun q => rfl
  have key : ∀ q, (M.hr + M.br) * SupplyChainTheory.expSales M.law q - M.hr * q =
      -M.retailerCost q + M.br * M.meanDemand := by
    intro q; rw [bs_sales, hL, bs_retailer_formula]; ring
  refine ⟨fun p w q => by rw [bs_sales]; ring, fun q => ⟨by rw [bs_sales, hL]; ring,
    by rw [bs_retailer_formula]; ring⟩, fun q => ?_⟩
  simp only [key]
  constructor
  · intro h s _
    have := h (Set.mem_univ s)
    change -M.retailerCost s + M.br * M.meanDemand ≤ -M.retailerCost q + M.br * M.meanDemand at this
    show M.retailerCost q ≤ M.retailerCost s
    linarith
  · intro h s _
    have := h (Set.mem_univ s)
    change M.retailerCost q ≤ M.retailerCost s at this
    show -M.retailerCost s + M.br * M.meanDemand ≤ -M.retailerCost q + M.br * M.meanDemand
    linarith

end CachonCoord.BaseStock

open CachonCoord.BaseStock


theorem solution (M : Model) :
    (∀ p w q : ℝ,
      p * SupplyChainTheory.expSales M.law q - w * q =
        (p - w) * q - p * SupplyChainTheory.expLeftover M.law q) ∧
    (∀ q : ℝ,
      (M.hr + M.br) * SupplyChainTheory.expSales M.law q - M.hr * q =
        M.br * q - (M.hr + M.br) * M.I q ∧
      M.br * q - (M.hr + M.br) * M.I q = -M.retailerCost q + M.br * M.meanDemand) ∧
    ∀ q : ℝ,
      IsMaxOn (fun x => (M.hr + M.br) * SupplyChainTheory.expSales M.law x - M.hr * x)
          Set.univ q ↔
        IsMinOn M.retailerCost Set.univ q := by
  exact p75_newsvendor_equivalence_core M
