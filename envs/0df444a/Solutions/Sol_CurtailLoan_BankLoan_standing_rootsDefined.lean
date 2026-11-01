-- Prove2me | solution 1 for CurtailLoan.BankLoan.standing_rootsDefined
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:56:52.389316+00:00
-- url     : https://prove2.me/submissions/fde97adf-0feb-4daa-ad45-ffecf257a460

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CurtailLoan_BankLoan_Model

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


lemma cl_tail (P : Params) (hR : P.Regular) :
    Tendsto (fun Q : ℝ => ∫ x in Ioi Q, x ∂P.D) atTop (𝓝 0) := by
  haveI := hR.1
  apply hR.2.1.tendsto_setIntegral_nhds_zero
  have h1 : ∀ Q : ℝ, P.D (Ioi Q) = ENNReal.ofReal (1 - cdf P.D Q) := by
    intro Q
    have : P.D.real (Ioi Q) = 1 - cdf P.D Q := by
      rw [cdf_eq_real, ← compl_Iic, measureReal_compl measurableSet_Iic]; simp
    rw [← this, ofReal_measureReal]
  have h2 : Tendsto (fun Q : ℝ => ENNReal.ofReal (1 - cdf P.D Q)) atTop (𝓝 (ENNReal.ofReal 0)) := by
    apply (ENNReal.continuous_ofReal.tendsto 0).comp
    have := (tendsto_cdf_atTop P.D).const_sub (1:ℝ)
    simpa using this
  simp only [ENNReal.ofReal_zero] at h2
  refine h2.congr' (Eventually.of_forall fun Q => ?_)
  simp [h1]

lemma cl_psi_le_tail (P : Params) (hR : P.Regular) (Q : ℝ) (hQ : 0 ≤ Q) :
    Q * (1 - cdf P.D Q) ≤ ∫ x in Ioi Q, x ∂P.D := by
  haveI := hR.1
  have h1 : P.D.real (Ioi Q) = 1 - cdf P.D Q := by
    rw [cdf_eq_real, ← compl_Iic, measureReal_compl measurableSet_Iic]; simp
  have h2 : ∫ x in Ioi Q, Q ∂P.D = P.D.real (Ioi Q) * Q := by
    rw [setIntegral_const, smul_eq_mul]
  have h3 : ∫ x in Ioi Q, Q ∂P.D ≤ ∫ x in Ioi Q, x ∂P.D :=
    setIntegral_mono_on (integrableOn_const (by simp)) hR.2.1.integrableOn measurableSet_Ioi
      (fun x hx => hx.le)
  rw [h2, h1] at h3; linarith

theorem solution (P : Params) (hR : P.Regular) (hS : Standing P) :
    RootsDefined P := by
  haveI := hR.1
  obtain ⟨hG, hLE⟩ := hS
  obtain ⟨hc0, hc1, hl, -, -, -, htu, -, -⟩ := hG
  have hcont := cl_cdf_cont P hR
  have hcdf0 := cl_cdf_zero P hR
  have hLpos : 0 < L P := by unfold L; linarith
  -- `0 < w^E < 1`
  set SE : Set ℝ := {w : ℝ | w ∈ Set.Ioc (0 : ℝ) 1 ∧ P.c ≤ w * (1 - Finv P w * hr P (Finv P w))}
    with hSE
  have hbddE : BddBelow SE := ⟨0, fun x hx => hx.1.1.le⟩
  have hE1 : wE P ≤ 1 := by
    apply csInf_le hbddE
    refine ⟨⟨zero_lt_one, le_rfl⟩, ?_⟩
    rw [cl_Finv_one]; simp; exact hc1.le
  have hE0 : 0 ≤ wE P := Real.sInf_nonneg (fun x hx => hx.1.1.le)
  have hLE' : L P < wE P * Finv P (wE P) := hLE
  have hwE1 : wE P < 1 := by
    rcases hE1.lt_or_eq with h | h
    · exact h
    · rw [h, cl_Finv_one] at hLE'; linarith
  have hwE0 : 0 < wE P := by
    rcases hE0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hLE'; linarith
  obtain ⟨hFE, hSuppE⟩ := cl_Finv_spec P hR (wE P) hwE0 hwE1
  set QE := Finv P (wE P) with hQE
  set p := wE P * QE with hp
  have hppos : 0 < p := lt_trans hLpos hLE'
  set ψ : ℝ → ℝ := fun Q => Q * (1 - cdf P.D Q) with hψ
  have hψc : Continuous ψ := continuous_id.mul (continuous_const.sub hcont)
  have hψE : ψ QE = p := by
    simp only [hψ, hp]; unfold Fbar at hFE; rw [hFE]; ring
  have hψle : ∀ Q, 0 ≤ Q → ψ Q ≤ Q := by
    intro Q hQ
    have := cdf_nonneg P.D Q
    simp only [hψ]; nlinarith
  -- the tail
  obtain ⟨β₀, hβ₀⟩ := eventually_atTop.1 ((cl_tail P hR).eventually (gt_mem_nhds hppos))
  set β := max β₀ (max QE 0) with hβ
  have htail : ∀ Q, β < Q → ψ Q < p := by
    intro Q hQ
    have hQ0 : 0 ≤ Q := by
      have : 0 ≤ β := le_trans (le_max_right _ _) (le_max_right _ _); linarith
    exact lt_of_le_of_lt (cl_psi_le_tail P hR Q hQ0) (hβ₀ Q (by
      have := le_max_left β₀ (max QE 0); linarith))
  set α := p / 2 with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  have hQEα : α < QE := by
    have := hψle QE hSuppE.1.le
    rw [hψE] at this; rw [hα]; linarith
  have hQEβ : QE ≤ β := le_trans (le_max_left _ _) (le_max_right _ _)
  obtain ⟨Qs, hQsK, hQsmax⟩ := (isCompact_Icc (a := α) (b := β)).exists_isMaxOn
    ⟨QE, hQEα.le, hQEβ⟩ hψc.continuousOn
  have hps : p ≤ ψ Qs := by rw [← hψE]; exact hQsmax ⟨hQEα.le, hQEβ⟩
  have hglob : ∀ Q, 0 ≤ Q → ψ Q ≤ ψ Qs := by
    intro Q hQ
    by_cases h1 : Q < α
    · have := hψle Q hQ; rw [hα] at h1; linarith
    · by_cases h2 : β < Q
      · have := htail Q h2; linarith
      · push_neg at h1 h2
        exact hQsmax ⟨h1, h2⟩
  set Astar : Set ℝ := Icc α β ∩ {Q | ψ Qs ≤ ψ Q} with hAstar
  have hAc : IsCompact Astar :=
    isCompact_Icc.inter_right (isClosed_le continuous_const hψc)
  have hsupp : ∀ Q, α ≤ Q → p ≤ ψ Q → 0 < Q ∧ cdf P.D Q < 1 := by
    intro Q hQ hpQ
    refine ⟨lt_of_lt_of_le hα0 hQ, ?_⟩
    by_contra h; push_neg at h
    have : ψ Q ≤ 0 := by
      simp only [hψ]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  have hFbar01 : ∀ Q, 0 < Q → cdf P.D Q < 1 → Fbar P Q ∈ Ioo (0:ℝ) 1 := by
    intro Q hQ0 hQ1
    have hsm := cl_cdf_strictMonoOn P hR Q hQ1
    have : cdf P.D 0 < cdf P.D Q := hsm ⟨le_rfl, hQ0.le⟩ ⟨hQ0.le, le_rfl⟩ hQ0
    unfold Fbar; constructor <;> linarith
  have hphi : ∀ w, w ∈ Ioo (0:ℝ) 1 → w * Finv P w = ψ (Finv P w) := by
    intro w hw
    have := (cl_Finv_spec P hR w hw.1 hw.2).1
    simp only [hψ]; unfold Fbar at this; rw [this]; ring
  have hQs := hsupp Qs hQsK.1 hps
  have hQsFbar := hFbar01 Qs hQs.1 hQs.2
  have hFinvQs : Finv P (Fbar P Qs) = Qs := cl_Finv_Fbar P hR Qs hQs.1.le hQs.2
  set M : Set ℝ := {w : ℝ | w ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∀ w' ∈ Set.Ioo (0 : ℝ) 1, w' * Finv P w' ≤ w * Finv P w} with hM
  have hMeq : M = Fbar P '' Astar := by
    ext w
    constructor
    · rintro ⟨hw, hmax⟩
      obtain ⟨hFw, hSw⟩ := cl_Finv_spec P hR w hw.1 hw.2
      have h1 := hmax (Fbar P Qs) hQsFbar
      rw [hphi _ hQsFbar, hphi w hw, hFinvQs] at h1
      have hpQ : p ≤ ψ (Finv P w) := le_trans hps h1
      have hQα : α ≤ Finv P w := by
        by_contra h; push_neg at h
        have := hψle _ hSw.1.le; rw [hα] at h; linarith
      have hQβ : Finv P w ≤ β := by
        by_contra h; push_neg at h
        have := htail _ h; linarith
      exact ⟨Finv P w, ⟨⟨hQα, hQβ⟩, h1⟩, hFw⟩
    · rintro ⟨Q, ⟨hQK, hQv⟩, rfl⟩
      have hQ := hsupp Q hQK.1 (le_trans hps hQv)
      have hw := hFbar01 Q hQ.1 hQ.2
      refine ⟨hw, fun w' hw' => ?_⟩
      rw [hphi w' hw', hphi _ hw, cl_Finv_Fbar P hR Q hQ.1.le hQ.2]
      have := hglob (Finv P w') (Real.sInf_nonneg (fun x hx => hx.1))
      exact le_trans this hQv
  have hFbarc : Continuous (Fbar P) := by
    unfold Fbar; exact continuous_const.sub hcont
  have hwhat : what P ∈ M := by
    have : what P = sSup M := rfl
    rw [this, hMeq]
    exact (hAc.image hFbarc).sSup_mem ⟨Fbar P Qs, Qs, ⟨hQsK, (le_refl (ψ Qs) : ψ Qs ≤ ψ Qs)⟩, rfl⟩
  have := hwhat.2 (wE P) ⟨hwE0, hwE1⟩
  show L P < what P * Finv P (what P)
  linarith
