-- Prove2me | solution 1 for CurtailLoan.BankLoan.supplier_profit_strictMonoOn_wE
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:54:31.764177+00:00
-- url     : https://prove2.me/submissions/072f3e21-b1cd-46f6-ba91-acc73466925f

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

theorem solution (P : Params) (hR : P.Regular)
    (hc0 : 0 < P.c) (hc1 : P.c < 1) :
    StrictMonoOn (fun w => (w - P.c) * Finv P w) (Set.Ioc 0 (wE P)) := by
  haveI := hR.1
  have hcont := cl_cdf_cont P hR
  have hcdf0 := cl_cdf_zero P hR
  -- `w^E ≤ 1`
  set SE : Set ℝ := {w : ℝ | w ∈ Set.Ioc (0 : ℝ) 1 ∧ P.c ≤ w * (1 - Finv P w * hr P (Finv P w))}
    with hSE
  have hbddE : BddBelow SE := ⟨0, fun x hx => hx.1.1.le⟩
  have hE1 : wE P ≤ 1 := by
    apply csInf_le hbddE
    refine ⟨⟨zero_lt_one, le_rfl⟩, ?_⟩
    rw [cl_Finv_one]; simp; exact hc1.le
  have hGlt : ∀ w, 0 < w → w < wE P → w * (1 - Finv P w * hr P (Finv P w)) < P.c := by
    intro w hw0 hwE
    have hnot : w ∉ SE := notMem_of_lt_csInf hwE hbddE
    by_contra hge
    push_neg at hge
    exact hnot ⟨⟨hw0, by linarith⟩, hge⟩
  intro w₁ hw₁ w₂ hw₂ hlt
  simp only
  have hw₁1 : w₁ < 1 := lt_of_lt_of_le hlt (hw₂.2.trans hE1)
  obtain ⟨hF₁, hS₁⟩ := cl_Finv_spec P hR w₁ hw₁.1 hw₁1
  set Q₁ := Finv P w₁ with hQ₁
  set Q₂ := Finv P w₂ with hQ₂
  -- facts on `Q₂`
  have hQ₂nn : 0 ≤ Q₂ := Real.sInf_nonneg (fun x hx => hx.1)
  have hQ₂F : 1 - cdf P.D Q₂ = w₂ ∨ (w₂ = 1 ∧ Q₂ = 0) := by
    rcases (hw₂.2.trans hE1).lt_or_eq with h | h
    · left; have := (cl_Finv_spec P hR w₂ hw₂.1 h).1; unfold Fbar at this; exact this
    · right; refine ⟨h, ?_⟩; rw [hQ₂, h, cl_Finv_one]
  have hcdfQ₂ : cdf P.D Q₂ = 1 - w₂ := by
    rcases hQ₂F with h | ⟨h1, h2⟩
    · linarith
    · rw [h2, hcdf0, h1]; ring
  have hF₁' : cdf P.D Q₁ = 1 - w₁ := by unfold Fbar at hF₁; linarith
  have hQ12 : Q₂ < Q₁ := by
    by_contra h
    push_neg at h
    have := monotone_cdf P.D h
    linarith
  -- the supplier's profit as a function of the order quantity
  set Ψ : ℝ → ℝ := fun Q => (1 - cdf P.D Q - P.c) * Q with hPsi
  have hPsianti : StrictAntiOn Ψ (Icc Q₂ Q₁) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc Q₂ Q₁)
    · exact ((continuous_const.sub hcont).sub continuous_const |>.mul continuous_id).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have hx1 : cdf P.D x < 1 := lt_of_le_of_lt (monotone_cdf P.D hx.2.le) hS₁.2
      have hs : x ∈ cl_Supp P := ⟨lt_of_le_of_lt hQ₂nn hx.1, hx1⟩
      have hd : HasDerivAt Ψ ((-P.f x) * x + (1 - cdf P.D x - P.c) * 1) x := by
        have h1 : HasDerivAt (fun y => 1 - cdf P.D y - P.c) (-P.f x) x := by
          have := ((cl_cdf_hasDerivAt P hR x hs).const_sub 1).sub_const P.c
          simpa using this
        exact h1.mul (hasDerivAt_id' x)
      rw [hd.deriv]
      -- `w = F̄(x)` lies strictly between `w₁` and `w₂`
      have hsm := cl_cdf_strictMonoOn P hR Q₁ hS₁.2
      have hlo : cdf P.D Q₂ < cdf P.D x := hsm ⟨hQ₂nn, hQ12.le⟩ ⟨hs.1.le, hx.2.le⟩ hx.1
      set w := 1 - cdf P.D x with hw
      have hw0 : 0 < w := by rw [hw]; linarith
      have hwE : w < wE P := by
        have : w < w₂ := by rw [hw]; linarith
        exact lt_of_lt_of_le this hw₂.2
      have hG := hGlt w hw0 hwE
      have hFinv : Finv P w = x := by
        have := cl_Finv_Fbar P hR x hs.1.le hx1
        unfold Fbar at this; rw [hw]; exact this
      rw [hFinv] at hG
      have hhr : hr P x = P.f x / w := by unfold hr Fbar; rw [hw]
      rw [hhr] at hG
      have : w * (1 - x * (P.f x / w)) = w - x * P.f x := by field_simp
      rw [this] at hG
      nlinarith
  have hres := hPsianti ⟨le_rfl, hQ12.le⟩ ⟨hQ12.le, le_rfl⟩ hQ12
  simp only [hPsi] at hres
  rw [hF₁', hcdfQ₂] at hres
  have e1 : (1 - (1 - w₁) - P.c) * Q₁ = (w₁ - P.c) * Q₁ := by ring
  have e2 : (1 - (1 - w₂) - P.c) * Q₂ = (w₂ - P.c) * Q₂ := by ring
  rw [e1, e2] at hres
  exact hres
