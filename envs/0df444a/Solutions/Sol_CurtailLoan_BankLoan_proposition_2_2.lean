-- Prove2me | solution 1 for CurtailLoan.BankLoan.proposition_2_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:58:59.808143+00:00
-- url     : https://prove2.me/submissions/fe7b5b31-5f67-4215-af88-0ad8591c3830
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model
import Theorems.Thm_CurtailLoan_BankLoan_proposition_1_1b
import Theorems.Thm_CurtailLoan_BankLoan_prop2_area2_profits
import Theorems.Thm_CurtailLoan_BankLoan_wt2_areaII_statics
import Theorems.Thm_CurtailLoan_BankLoan_supplier_profit_strictMonoOn_wE

open MeasureTheory ProbabilityTheory Set Filter Topology
open CurtailLoan.BankLoan

lemma cl_D_singleton (P : Params) (hR : P.Regular) (a : ℝ) : P.D {a} = 0 := by
  rw [hR.2.2.1, withDensity_apply _ (measurableSet_singleton a)]
  exact setLIntegral_measure_zero _ _ (Real.volume_singleton)

lemma cl_cdf_cont (P : Params) (hR : P.Regular) : Continuous (cdf P.D) := by
  haveI := hR.1
  rw [continuous_iff_continuousAt]; intro a
  have hm : Monotone (cdf P.D) := monotone_cdf _
  have h1 : (cdf P.D).measure {a} = 0 := by rw [measure_cdf]; exact cl_D_singleton P hR a
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at h1
  have h2 : Function.leftLim (cdf P.D) a = cdf P.D a :=
    le_antisymm (hm.leftLim_le le_rfl) (by linarith)
  rw [continuousAt_iff_continuous_left_right]
  exact ⟨continuousWithinAt_Iio_iff_Iic.1 (hm.continuousWithinAt_Iio_iff_leftLim_eq.2 h2),
    (cdf P.D).right_continuous a⟩

lemma cl_cdf_zero (P : Params) (hR : P.Regular) : cdf P.D 0 = 0 := by
  haveI := hR.1
  have hIio : P.D (Iio 0) = 0 := by
    rw [hR.2.2.1, withDensity_apply _ measurableSet_Iio]
    rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
      (fun x hx => by simp [hR.2.2.2.1 x hx])]
    simp
  have hIic : P.D (Iic 0) = 0 := by
    have : Iic (0:ℝ) = Iio 0 ∪ {0} := by ext x; simp [le_iff_lt_or_eq]
    rw [this]
    exact le_antisymm ((measure_union_le _ _).trans (by rw [hIio, cl_D_singleton P hR]; simp))
      bot_le
  rw [cdf_eq_real, measureReal_def, hIic]; simp

/-- representation of increments of the cdf as integrals of the density, on a stretch where
the density is continuous and nonnegative -/
lemma cl_cdf_sub (P : Params) (hR : P.Regular) (a b : ℝ) (hab : a ≤ b)
    (hc : ContinuousOn P.f (Icc a b)) (hnn : ∀ x ∈ Icc a b, 0 ≤ P.f x) :
    cdf P.D b - cdf P.D a = ∫ x in a..b, P.f x := by
  haveI := hR.1
  have h1 : P.D (Ioc a b) = ENNReal.ofReal (cdf P.D b - cdf P.D a) := by
    rw [← StieltjesFunction.measure_Ioc, measure_cdf]
  have h2 : P.D (Ioc a b) = ∫⁻ x in Ioc a b, ENNReal.ofReal (P.f x) := by
    rw [hR.2.2.1, withDensity_apply _ measurableSet_Ioc]
  have hint : IntegrableOn P.f (Ioc a b) volume :=
    (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h3 : ∫⁻ x in Ioc a b, ENNReal.ofReal (P.f x) = ENNReal.ofReal (∫ x in Ioc a b, P.f x) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint]
    exact (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => hnn x (Ioc_subset_Icc_self hx)))
  have hge : 0 ≤ cdf P.D b - cdf P.D a := by linarith [monotone_cdf P.D hab]
  have hge2 : 0 ≤ ∫ x in Ioc a b, P.f x :=
    setIntegral_nonneg measurableSet_Ioc (fun x hx => hnn x (Ioc_subset_Icc_self hx))
  rw [intervalIntegral.integral_of_le hab]
  rw [h1, h3] at h2
  exact (ENNReal.ofReal_eq_ofReal_iff hge hge2).1 h2

def cl_Supp (P : Params) : Set ℝ := {x : ℝ | 0 < x ∧ cdf P.D x < 1}

lemma cl_cdf_hasDerivAt (P : Params) (hR : P.Regular) (Q : ℝ) (hQ : Q ∈ cl_Supp P) :
    HasDerivAt (cdf P.D) (P.f Q) Q := by
  obtain ⟨hQ0, hQ1⟩ := hQ
  have hcont := cl_cdf_cont P hR
  -- a right end inside the support
  have hev : ∀ᶠ y in 𝓝 Q, cdf P.D y < 1 :=
    (hcont.continuousAt).eventually (gt_mem_nhds hQ1)
  obtain ⟨b, hQb, hb⟩ : ∃ b, Q < b ∧ cdf P.D b < 1 := by
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨Q + ε / 2, by linarith, hball ?_⟩
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  set a := Q / 2 with ha
  have haQ : a < Q := by rw [ha]; linarith
  have ha0 : 0 < a := by rw [ha]; linarith
  have hsub : Icc a b ⊆ cl_Supp P := fun x hx =>
    ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt (monotone_cdf P.D hx.2) hb⟩
  have hfc : ContinuousOn P.f (Icc a b) := hR.2.2.2.2.1.mono hsub
  have hfnn : ∀ x ∈ Icc a b, 0 ≤ P.f x := fun x hx => (hR.2.2.2.2.2.1 x (hsub hx).1 (hsub hx).2).le
  have hderiv : HasDerivAt (fun y => cdf P.D a + ∫ x in a..y, P.f x) (P.f Q) Q := by
    have hII : IntervalIntegrable P.f volume a Q :=
      (hfc.mono (Icc_subset_Icc le_rfl (le_of_lt hQb))).intervalIntegrable_of_Icc haQ.le
    have hopen : Ioo a b ∈ 𝓝 Q := Ioo_mem_nhds haQ hQb
    have hcQ : ContinuousAt P.f Q := (hfc.mono Ioo_subset_Icc_self).continuousAt hopen
    have hsm : StronglyMeasurableAtFilter P.f (𝓝 Q) volume :=
      (hfc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo Q ⟨haQ, hQb⟩
    exact (intervalIntegral.integral_hasDerivAt_right hII hsm hcQ).const_add _
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds haQ hQb] with y hy
  have := cl_cdf_sub P hR a y hy.1.le (hfc.mono (Icc_subset_Icc le_rfl hy.2.le))
    (fun x hx => hfnn x ⟨hx.1, hx.2.trans hy.2.le⟩)
  linarith

lemma cl_cdf_strictMonoOn (P : Params) (hR : P.Regular) (b : ℝ) (hb : cdf P.D b < 1) :
    StrictMonoOn (cdf P.D) (Icc 0 b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 b) (cl_cdf_cont P hR).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  have hs : x ∈ cl_Supp P := ⟨hx.1, lt_of_le_of_lt (monotone_cdf P.D hx.2.le) hb⟩
  rw [(cl_cdf_hasDerivAt P hR x hs).deriv]
  exact hR.2.2.2.2.2.1 x hs.1 hs.2

lemma cl_Finv_one (P : Params) : Finv P 1 = 0 := by
  unfold Finv
  apply le_antisymm
  · apply csInf_le ⟨0, fun x hx => hx.1⟩
    refine ⟨le_rfl, ?_⟩
    unfold Fbar
    have := cdf_nonneg P.D 0
    linarith
  · exact Real.sInf_nonneg (fun x hx => hx.1)

lemma cl_Finv_spec (P : Params) (hR : P.Regular) (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1) :
    Fbar P (Finv P w) = w ∧ Finv P w ∈ cl_Supp P := by
  haveI := hR.1
  have hcont := cl_cdf_cont P hR
  set S : Set ℝ := {Q : ℝ | 0 ≤ Q ∧ Fbar P Q ≤ w} with hS
  have hne : S.Nonempty := by
    have := (tendsto_cdf_atTop P.D).eventually (lt_mem_nhds (show 1 - w < 1 by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.1 this
    refine ⟨max N 0, le_max_right _ _, ?_⟩
    have := hN (max N 0) (le_max_left _ _)
    unfold Fbar; linarith
  have hclosed : IsClosed S := by
    apply IsClosed.inter isClosed_Ici
    exact isClosed_le ((continuous_const.sub hcont)) continuous_const
  have hmem : Finv P w ∈ S := hclosed.csInf_mem hne ⟨0, fun x hx => hx.1⟩
  have hF0 : 0 ≤ Finv P w := hmem.1
  have hcdf0 := cl_cdf_zero P hR
  obtain ⟨y, hy, hyv⟩ : 1 - w ∈ cdf P.D '' Icc 0 (Finv P w) := by
    apply intermediate_value_Icc hF0 hcont.continuousOn
    refine ⟨by rw [hcdf0]; linarith, ?_⟩
    have := hmem.2; unfold Fbar at this; linarith
  have hyS : y ∈ S := ⟨hy.1, by unfold Fbar; linarith⟩
  have hle : Finv P w ≤ y := csInf_le ⟨0, fun x hx => hx.1⟩ hyS
  have hyeq : y = Finv P w := le_antisymm hy.2 hle
  rw [hyeq] at hyv
  refine ⟨by unfold Fbar; linarith, ?_, by linarith⟩
  rcases hF0.lt_or_eq with h | h
  · exact h
  · rw [← h, hcdf0] at hyv; linarith

lemma cl_Finv_Fbar (P : Params) (hR : P.Regular) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : cdf P.D x < 1) :
    Finv P (Fbar P x) = x := by
  have hsm := cl_cdf_strictMonoOn P hR x hx1
  unfold Finv
  apply le_antisymm
  · exact csInf_le ⟨0, fun y hy => hy.1⟩ ⟨hx0, le_rfl⟩
  · apply le_csInf (⟨x, hx0, le_rfl⟩ : Set.Nonempty {Q : ℝ | 0 ≤ Q ∧ Fbar P Q ≤ Fbar P x})
    intro q hq
    by_contra hlt
    push_neg at hlt
    have := hsm ⟨hq.1, hlt.le⟩ ⟨hx0, le_rfl⟩ hlt
    have h2 := hq.2; unfold Fbar at h2; linarith


lemma cl_Finv_anti (P : Params) (hR : P.Regular) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Finv P b ≤ Finv P a := by
  haveI := hR.1
  have hne : ({Q : ℝ | 0 ≤ Q ∧ Fbar P Q ≤ a}).Nonempty := by
    have := (tendsto_cdf_atTop P.D).eventually (lt_mem_nhds (show 1 - a < 1 by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.1 this
    refine ⟨max N 0, le_max_right _ _, ?_⟩
    have := hN (max N 0) (le_max_left _ _)
    unfold Fbar; linarith
  unfold Finv
  exact csInf_le_csInf ⟨0, fun x hx => hx.1⟩ hne (fun x hx => ⟨hx.1, le_trans hx.2 hab⟩)

lemma cl_wt2_lt_one (Q : Params) (hR : Q.Regular) (hL : 0 < L Q) (hpos : 0 < wt2 Q) :
    wt2 Q < 1 := by
  have hcdf0 := cl_cdf_zero Q hR
  have hFL : Fbar Q (L Q) < 1 := by
    unfold Fbar
    by_cases h : cdf Q.D (L Q) < 1
    · have := cl_cdf_strictMonoOn Q hR (L Q) h ⟨le_rfl, hL.le⟩ ⟨hL.le, le_rfl⟩ hL
      linarith
    · push_neg at h; linarith
  have hFL0 : 0 ≤ Fbar Q (L Q) := by
    unfold Fbar; linarith [cdf_le_one Q.D (L Q)]
  have hwu2 : wu2 Q ≤ Fbar Q (L Q) := by
    unfold wu2
    apply Real.sSup_le _ hFL0
    intro w hw
    by_contra h
    push_neg at h
    have hF : Finv Q w ≤ L Q := csInf_le ⟨0, fun x hx => hx.1⟩ ⟨hL.le, h.le⟩
    have hF0 : 0 ≤ Finv Q w := Real.sInf_nonneg (fun x hx => hx.1)
    have : w * Finv Q w ≤ Finv Q w := by nlinarith [hw.1.2]
    linarith [hw.2]
  have hwu2' : wt2 Q ≤ wu2 Q := by
    unfold wt2
    apply Real.sSup_le (fun x hx => hx.1.2.le)
    unfold wu2; exact Real.sSup_nonneg (fun x hx => hx.1.1.le)
  linarith

theorem solution (P : Params) (hR : P.Regular) :
    (∀ u₁ u₂ : ℝ, u₁ < u₂ →
      (∀ x ∈ Set.Icc u₁ u₂, Standing (P.withU x) ∧ AreaII (P.withU x)) →
      ∀ o₁ o₂ : Outcome, IsEquilibrium (P.withU u₁) o₁ → IsEquilibrium (P.withU u₂) o₂ →
        PiS (P.withU u₂) o₂ < PiS (P.withU u₁) o₁ ∧
        PiB (P.withU u₁) o₁ < PiB (P.withU u₂) o₂) ∧
    (∀ τ₁ τ₂ : ℝ, τ₁ < τ₂ →
      (∀ x ∈ Set.Icc τ₁ τ₂, Standing (P.withTau x) ∧ AreaII (P.withTau x)) →
      ∀ o₁ o₂ : Outcome, IsEquilibrium (P.withTau τ₁) o₁ → IsEquilibrium (P.withTau τ₂) o₂ →
        PiB (P.withTau τ₂) o₂ < PiB (P.withTau τ₁) o₁ ∧
        ((∀ x ∈ Set.Icc τ₁ τ₂, InsuredSlack (P.withTau x)) →
          PiS (P.withTau τ₁) o₁ < PiS (P.withTau τ₂) o₂)) := by
  obtain ⟨hWu, hWtau⟩ := wt2_areaII_statics P hR
  refine ⟨?_, ?_⟩
  · -- the initial loan limit `u`
    intro u₁ u₂ hu hseg o₁ o₂ ho₁ ho₂
    have h₁ := hseg u₁ ⟨le_rfl, hu.le⟩
    have h₂ := hseg u₂ ⟨hu.le, le_rfl⟩
    have hR₁ : (P.withU u₁).Regular := hR
    have hR₂ : (P.withU u₂).Regular := hR
    obtain ⟨hw₁, hm₁, hQ₁⟩ := (proposition_1_1b _ hR₁ h₁.1 h₁.2).2 o₁ ho₁
    obtain ⟨hw₂, hm₂, hQ₂⟩ := (proposition_1_1b _ hR₂ h₂.1 h₂.2).2 o₂ ho₂
    have hlt : wt2 (P.withU u₂) < wt2 (P.withU u₁) := hWu u₁ u₂ hu hseg
    have hfe₁ := ho₁.1.2.1.1.1
    have hfe₂ := ho₂.1.2.1.1.1
    have hwpos₁ : 0 < o₁.w := ho₁.1.1.1
    have hwpos₂ : 0 < o₂.w := ho₂.1.1.1
    -- notation
    set K : ℝ := P.v + P.l - P.tau - P.t with hK
    have hww : o₂.w < o₁.w := by rw [hw₁, hw₂]; exact hlt
    obtain ⟨hc0, hc1, hl, ht0, htau0, -, htu, -, huv⟩ := h₁.1.1
    have hPiS₁ : PiS (P.withU u₁) o₁ = (o₁.w - P.c) * o₁.Q := rfl
    have hPiS₂ : PiS (P.withU u₂) o₂ = (o₂.w - P.c) * o₂.Q := rfl
    have hQ₁nn : 0 ≤ o₁.Q := hfe₁.1
    have hQ₂nn : 0 ≤ o₂.Q := hfe₂.1
    have hcap₁ : o₁.w * o₁.Q ≤ K := by
      have := hfe₁.2; rw [hm₁] at this; exact this
    -- the insured cap is positive (otherwise the buyer would rather not order at all)
    have hKpos : 0 < K := by
      by_contra hK0
      push_neg at hK0
      have h0 : o₁.w * o₁.Q = 0 :=
        le_antisymm (by linarith) (mul_nonneg hwpos₁.le hQ₁nn)
      have hQ0 : o₁.Q = 0 := by
        rcases mul_eq_zero.1 h0 with h | h
        · linarith
        · exact h
      have hopt := ho₁.1.2.1.1.2 Mode.noLoan 0
        ⟨le_rfl, by show o₁.w * 0 ≤ P.l; rw [mul_zero]; exact hl⟩
      have e1 : buyerProfit (P.withU u₁) o₁.w Mode.noLoan 0 = S P 0 - o₁.w * 0 - 0 := rfl
      have e2 : buyerProfit (P.withU u₁) o₁.w o₁.m o₁.Q = S P 0 - o₁.w * 0 - (P.tau + P.t) := by
        rw [hm₁, hQ0]; rfl
      rw [e1, e2] at hopt
      change P.tau < u₁ at htu
      change u₁ < P.v at huv
      change 0 ≤ P.l at hl
      change 0 ≤ P.t at ht0
      change 0 ≤ P.tau at htau0
      linarith
    have hw₁1 : o₁.w < 1 := by
      rw [hw₁]
      apply cl_wt2_lt_one _ hR₁
      · show 0 < u₁ + P.l - P.tau
        change P.tau < u₁ at htu
        change 0 ≤ P.l at hl
        linarith
      · rw [← hw₁]; exact hwpos₁
    have hF₁pos : 0 < Finv P o₁.w := (cl_Finv_spec P hR o₁.w hwpos₁ hw₁1).2.1
    have hQ₁' : o₁.Q = min (K / o₁.w) (Finv P o₁.w) := by
      rw [hw₁]; exact hQ₁
    have hQ₂' : o₂.Q = min (K / o₂.w) (Finv P o₂.w) := by
      rw [hw₂]; exact hQ₂
    have hQ₁pos : 0 < o₁.Q := by
      rw [hQ₁']; exact lt_min (div_pos hKpos hwpos₁) hF₁pos
    have hQ₁₂ : o₁.Q ≤ o₂.Q := by
      rw [hQ₁', hQ₂']
      exact min_le_min (div_le_div_of_nonneg_left hKpos.le hwpos₂ hww.le)
        (cl_Finv_anti P hR o₂.w o₁.w hwpos₂ hww.le)
    refine ⟨?_, ?_⟩
    · -- supplier
      rcases le_or_gt o₂.w P.c with hcw | hcw₂
      · -- a price at or below cost
        rw [hPiS₁, hPiS₂]
        have a1 : (o₂.w - P.c) * o₂.Q ≤ (o₂.w - P.c) * o₁.Q :=
          mul_le_mul_of_nonpos_left hQ₁₂ (by linarith)
        have a2 : (o₂.w - P.c) * o₁.Q < (o₁.w - P.c) * o₁.Q :=
          mul_lt_mul_of_pos_right (by linarith) hQ₁pos
        linarith
      rw [hPiS₁, hPiS₂]
      by_cases hb : K / o₁.w ≤ Finv P o₁.w
      · -- the insured cap binds at `o₁.w`
        have e₁ : o₁.Q = K / o₁.w := by rw [hQ₁']; exact min_eq_left hb
        have hle : (o₂.w - P.c) * o₂.Q ≤ (o₂.w - P.c) * (K / o₂.w) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [hQ₂']; exact min_le_left _ _
        have key : (o₂.w - P.c) * (K / o₂.w) < (o₁.w - P.c) * (K / o₁.w) := by
          have a1 : (o₂.w - P.c) * (K / o₂.w) = K - P.c * K / o₂.w := by
            field_simp
          have a2 : (o₁.w - P.c) * (K / o₁.w) = K - P.c * K / o₁.w := by
            field_simp
          rw [a1, a2]
          have : P.c * K / o₁.w < P.c * K / o₂.w :=
            div_lt_div_of_pos_left (mul_pos hc0 hKpos) (by linarith) hww
          linarith
        rw [e₁]; linarith
      · -- the insured cap does not bind at `o₁.w`
        push_neg at hb
        have e₁ : o₁.Q = Finv P o₁.w := by rw [hQ₁']; exact min_eq_right hb.le
        have hslack : wt2 (P.withU u₁) * Finv (P.withU u₁) (wt2 (P.withU u₁)) ≤
            (P.withU u₁).v + (P.withU u₁).l - (P.withU u₁).tau - (P.withU u₁).t := by
          rw [← hw₁]
          have : o₁.w * Finv P o₁.w < K := by
            have := (lt_div_iff₀ hwpos₁).1 hb
            linarith [mul_comm o₁.w (Finv P o₁.w)]
          exact this.le
        have hwE : wt2 (P.withU u₁) ≤ wE (P.withU u₁) :=
          ((prop2_area2_profits _ hR₁ h₁.1 h₁.2 o₁ ho₁).2 hslack).2.2
        have hwE' : o₁.w ≤ wE P := by rw [hw₁]; exact hwE
        have hmono := supplier_profit_strictMonoOn_wE P hR hc0 hc1
        have hlt' : (o₂.w - P.c) * Finv P o₂.w < (o₁.w - P.c) * Finv P o₁.w :=
          hmono ⟨hwpos₂, by linarith⟩ ⟨hwpos₁, hwE'⟩ hww
        have hle : (o₂.w - P.c) * o₂.Q ≤ (o₂.w - P.c) * Finv P o₂.w := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [hQ₂']; exact min_le_right _ _
        rw [e₁]; linarith
    · -- buyer
      have hfeas : Feasible (P.withU u₂) o₂.w Mode.insured o₁.Q := by
        refine ⟨hQ₁nn, ?_⟩
        have : o₂.w * o₁.Q ≤ o₁.w * o₁.Q := mul_le_mul_of_nonneg_right hww.le hQ₁nn
        show o₂.w * o₁.Q ≤ P.v + P.l - P.tau - P.t
        linarith
      have hopt := ho₂.1.2.1.1.2 Mode.insured o₁.Q hfeas
      have hB₁ : PiB (P.withU u₁) o₁ = S P o₁.Q - o₁.w * o₁.Q - (P.tau + P.t) := by
        show buyerProfit (P.withU u₁) o₁.w o₁.m o₁.Q = _
        rw [hm₁]; rfl
      have hB₂ : buyerProfit (P.withU u₂) o₂.w Mode.insured o₁.Q =
          S P o₁.Q - o₂.w * o₁.Q - (P.tau + P.t) := rfl
      have hstrict : o₂.w * o₁.Q < o₁.w * o₁.Q := mul_lt_mul_of_pos_right hww hQ₁pos
      have : PiB (P.withU u₂) o₂ = buyerProfit (P.withU u₂) o₂.w o₂.m o₂.Q := rfl
      rw [hB₁, this]
      linarith
  · -- the fixed bank fee `τ`
    intro τ₁ τ₂ hτ hseg o₁ o₂ ho₁ ho₂
    have h₁ := hseg τ₁ ⟨le_rfl, hτ.le⟩
    have h₂ := hseg τ₂ ⟨hτ.le, le_rfl⟩
    have hR₁ : (P.withTau τ₁).Regular := hR
    have hR₂ : (P.withTau τ₂).Regular := hR
    obtain ⟨hw₁, hm₁, -⟩ := (proposition_1_1b _ hR₁ h₁.1 h₁.2).2 o₁ ho₁
    obtain ⟨hw₂, hm₂, -⟩ := (proposition_1_1b _ hR₂ h₂.1 h₂.2).2 o₂ ho₂
    have hlt : wt2 (P.withTau τ₁) < wt2 (P.withTau τ₂) := hWtau τ₁ τ₂ hτ hseg
    have hfe₂ := ho₂.1.2.1.1.1
    have hwpos₁ : 0 < o₁.w := ho₁.1.1.1
    have hwpos₂ : 0 < o₂.w := ho₂.1.1.1
    have hww : o₁.w < o₂.w := by rw [hw₁, hw₂]; exact hlt
    have hc0 : 0 < P.c := h₁.1.1.1
    have hc1 : P.c < 1 := h₁.1.1.2.1
    refine ⟨?_, ?_⟩
    · -- buyer
      have hQ₂nn : 0 ≤ o₂.Q := hfe₂.1
      have hcap₂ : o₂.w * o₂.Q ≤ P.v + P.l - τ₂ - P.t := by
        have := hfe₂.2; rw [hm₂] at this; exact this
      have hmul : o₁.w * o₂.Q ≤ o₂.w * o₂.Q := mul_le_mul_of_nonneg_right hww.le hQ₂nn
      have hfeas : Feasible (P.withTau τ₁) o₁.w Mode.insured o₂.Q := by
        refine ⟨hQ₂nn, ?_⟩
        show o₁.w * o₂.Q ≤ P.v + P.l - τ₁ - P.t
        linarith
      have hopt := ho₁.1.2.1.1.2 Mode.insured o₂.Q hfeas
      have hB₂ : PiB (P.withTau τ₂) o₂ = S P o₂.Q - o₂.w * o₂.Q - (τ₂ + P.t) := by
        show buyerProfit (P.withTau τ₂) o₂.w o₂.m o₂.Q = _
        rw [hm₂]; rfl
      have hB₁ : buyerProfit (P.withTau τ₁) o₁.w Mode.insured o₂.Q =
          S P o₂.Q - o₁.w * o₂.Q - (τ₁ + P.t) := rfl
      have : PiB (P.withTau τ₁) o₁ = buyerProfit (P.withTau τ₁) o₁.w o₁.m o₁.Q := rfl
      rw [hB₂, this]
      linarith
    · -- supplier, when the insured cap does not bind at `w^t_2`
      intro hslack
      have s₁ := hslack τ₁ ⟨le_rfl, hτ.le⟩
      have s₂ := hslack τ₂ ⟨hτ.le, le_rfl⟩
      have p₁ := (prop2_area2_profits _ hR₁ h₁.1 h₁.2 o₁ ho₁).2 s₁
      have p₂ := (prop2_area2_profits _ hR₂ h₂.1 h₂.2 o₂ ho₂).2 s₂
      rw [p₁.2.1, p₂.2.1]
      have hmono := supplier_profit_strictMonoOn_wE P hR hc0 hc1
      have hwE : wt2 (P.withTau τ₂) ≤ wE P := p₂.2.2
      have a₁ : 0 < wt2 (P.withTau τ₁) := by rw [← hw₁]; exact hwpos₁
      exact hmono ⟨a₁, by linarith⟩ ⟨by linarith, hwE⟩ hlt
