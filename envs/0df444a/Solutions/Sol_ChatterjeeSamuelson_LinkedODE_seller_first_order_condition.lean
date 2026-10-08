-- Prove2me | solution 1 for ChatterjeeSamuelson.LinkedODE.seller_first_order_condition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T17:12:05.241869+00:00
-- url     : https://prove2.me/submissions/08430955-1119-4ad4-a582-c1ebc69ce20a

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_RegularBelief
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_ClassA
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_IsEquilibrium

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics

namespace P42f5f242

/-- No atom at an interior point. -/
theorem atom_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ)
    (hc : ContinuousAt (cdf μ) t) : μ {t} = 0 := by
  rw [← measure_cdf μ, StieltjesFunction.measure_singleton,
    hc.continuousWithinAt.leftLim_eq, sub_self, ENNReal.ofReal_zero]

theorem real_Ioc (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℝ} (hab : a ≤ b) :
    μ.real (Ioc a b) = cdf μ b - cdf μ a := by
  have h := (cdf μ).measure_Ioc a b
  rw [measure_cdf] at h
  rw [Measure.real, h, ENNReal.toReal_ofReal (sub_nonneg.2 ((cdf μ).mono hab))]

theorem piece (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : ℝ → ℝ) (hm : Monotone h)
    (hi : Integrable h μ) {a b : ℝ} (hab : a ≤ b) (c : ℝ) (hc1 : h a ≤ c) (hc2 : c ≤ h b) :
    ‖(∫ z in Iic b, h z ∂μ - ∫ z in Iic a, h z ∂μ) - c * (cdf μ b - cdf μ a)‖ ≤
      |h b - h a| * (cdf μ b - cdf μ a) := by
  have hU : ∫ z in Iic b, h z ∂μ = ∫ z in Iic a, h z ∂μ + ∫ z in Ioc a b, h z ∂μ := by
    rw [← Iic_union_Ioc_eq_Iic hab]
    exact setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hi.integrableOn
      hi.integrableOn
  rw [hU, ← real_Ioc μ hab]
  have hE : ∫ z in Iic a, h z ∂μ + ∫ z in Ioc a b, h z ∂μ - ∫ z in Iic a, h z ∂μ
      - c * μ.real (Ioc a b) = ∫ z in Ioc a b, (h z - c) ∂μ := by
    rw [integral_sub hi.integrableOn (integrable_const c), setIntegral_const, smul_eq_mul]
    ring
  rw [hE]
  have hfin : μ (Ioc a b) < ⊤ := measure_lt_top μ _
  refine (norm_setIntegral_le_of_norm_le_const hfin ?_).trans (le_of_eq rfl)
  intro z hz
  have h1 := hm hz.1.le
  have h2 := hm hz.2
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have : 0 ≤ h b - h a := by linarith
    rw [abs_of_nonneg this]; linarith
  · have : 0 ≤ h b - h a := by linarith
    rw [abs_of_nonneg this]; linarith

/-- Derivative of `t ↦ ∫_{Iic t} h dμ`. -/
theorem hasDerivAt_Iic (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : ℝ → ℝ) (hm : Monotone h)
    (hi : Integrable h μ) (x f : ℝ) (hF : HasDerivAt (cdf μ) f x) (hc : ContinuousAt h x) :
    HasDerivAt (fun t => ∫ z in Iic t, h z ∂μ) (h x * f) x := by
  rw [hasDerivAt_iff_isLittleO]
  refine IsLittleO.congr_left (f₁ := fun t => ((∫ z in Iic t, h z ∂μ) - (∫ z in Iic x, h z ∂μ)
      - h x * (cdf μ t - cdf μ x)) + h x * (cdf μ t - cdf μ x - (t - x) • f)) ?_
    (fun t => by simp only [smul_eq_mul]; ring)
  set K : ℝ → ℝ := fun t => ∫ z in Iic t, h z ∂μ with hK
  refine IsLittleO.add ?_ ?_
  · have hb : ∀ t, ‖K t - K x - h x * (cdf μ t - cdf μ x)‖ ≤ 1 * ‖(h t - h x) * (cdf μ t - cdf μ x)‖ := by
      intro t
      simp only [one_mul, norm_mul, Real.norm_eq_abs]
      rcases le_total x t with hxt | htx
      · have := piece μ h hm hi hxt (h x) le_rfl (hm hxt)
        rw [abs_of_nonneg (sub_nonneg.2 ((cdf μ).mono hxt))]
        rw [Real.norm_eq_abs] at this
        exact this
      · have := piece μ h hm hi htx (h x) (hm htx) le_rfl
        rw [abs_sub_comm (h t), abs_of_nonpos (sub_nonpos.2 ((cdf μ).mono htx))]
        have e : K t - K x - h x * (cdf μ t - cdf μ x) =
            -((∫ z in Iic x, h z ∂μ - ∫ z in Iic t, h z ∂μ) - h x * (cdf μ x - cdf μ t)) := by
          simp only [hK]; ring
        rw [e, abs_neg]
        calc _ = _ := (Real.norm_eq_abs _).symm
          _ ≤ _ := this
          _ = _ := by ring
    have h1 : (fun t => h t - h x) =o[𝓝 x] (fun _ => (1 : ℝ)) := by
      rw [isLittleO_one_iff]
      have := hc.tendsto
      simpa using this.sub_const (h x)
    have h2 : (fun t => cdf μ t - cdf μ x) =O[𝓝 x] (fun t => t - x) := hF.isBigO_sub
    have h3 := h1.mul_isBigO h2
    simp only [one_mul] at h3
    exact (IsBigO.of_bound 1 (Eventually.of_forall hb)).trans_isLittleO h3
  · exact (hasDerivAt_iff_isLittleO.1 hF).const_mul_left (h x)

/-- Local inverse of a continuous strictly increasing function. -/
theorem local_inverse (B : ℝ → ℝ) (a c x : ℝ) (hx : x ∈ Ioo a c)
    (hmono : StrictMonoOn B (Ioo a c)) (hcont : ContinuousOn B (Ioo a c))
    (hB : HasDerivAt B (deriv B x) x) (hne : deriv B x ≠ 0) :
    ∃ g : ℝ → ℝ, g (B x) = x ∧ HasDerivAt g (deriv B x)⁻¹ (B x) ∧
      ∀ᶠ s in 𝓝 (B x), B (g s) = s ∧ g s ∈ Ioo a c := by
  set g := Function.invFunOn B (Ioo a c) with hg
  have hleft : LeftInvOn g B (Ioo a c) := hmono.injOn.leftInvOn_invFunOn
  have hgx : g (B x) = x := hleft hx
  obtain ⟨a', ha'1, ha'2⟩ := exists_between hx.1
  obtain ⟨c', hc'1, hc'2⟩ := exists_between hx.2
  have hsub : Icc a' c' ⊆ Ioo a c := Icc_subset_Ioo ha'1 hc'2
  have hN : B '' Ioo a c ∈ 𝓝 (B x) := by
    have hivt := intermediate_value_Icc (ha'2.trans hc'1).le (hcont.mono hsub)
    have h1 : B a' < B x := hmono (hsub ⟨le_rfl, (ha'2.trans hc'1).le⟩) hx ha'2
    have h2 : B x < B c' := hmono hx (hsub ⟨(ha'2.trans hc'1).le, le_rfl⟩) hc'1
    refine Filter.mem_of_superset (Ioo_mem_nhds h1 h2) ?_
    exact Ioo_subset_Icc_self.trans (hivt.trans (image_mono hsub))
  have hgmono : StrictMonoOn g (B '' Ioo a c) := by
    rintro _ ⟨u1, hu1, rfl⟩ _ ⟨u2, hu2, rfl⟩ hlt
    rw [hleft hu1, hleft hu2]
    by_contra hh
    push Not at hh
    exact absurd hlt (not_lt.2 (hmono.monotoneOn hu2 hu1 hh))
  have hgim : g '' (B '' Ioo a c) = Ioo a c := hleft.image_image
  have hgc : ContinuousAt g (B x) := by
    refine hgmono.continuousAt_of_image_mem_nhds hN ?_
    rw [hgim, hgx]; exact Ioo_mem_nhds hx.1 hx.2
  have hev : ∀ᶠ s in 𝓝 (B x), B (g s) = s ∧ g s ∈ Ioo a c := by
    filter_upwards [hN] with s hs
    obtain ⟨u, hu, rfl⟩ := hs
    rw [hleft hu]; exact ⟨rfl, hu⟩
  refine ⟨g, hgx, ?_, hev⟩
  have hB' : HasDerivAt B (deriv B x) (g (B x)) := by rw [hgx]; exact hB
  exact HasDerivAt.of_local_left_inverse hgc hB' hne (hev.mono fun s hs => hs.1)

end P42f5f242

open MeasureTheory ProbabilityTheory Set ChatterjeeSamuelson.LinkedODE ChatterjeeSamuelson in
theorem solution (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (μb μs : Measure ℝ) (loS hiS loB hiB : ℝ) (fs S B : ℝ → ℝ)
    (hμs : RegularBelief μs loB hiB fs) (hB : ClassA B loB hiB)
    (a c x : ℝ) (ha : loB ≤ a) (hc : c ≤ hiB) (hx : x ∈ Ioo a c)
    (hmono : StrictMonoOn B (Ioo a c)) (hderiv : 0 < deriv B x) :
    (∀ v : ℝ, HasDerivAt (fun s => Shared.sellerProfit k μs B s v)
        ((v - B x) * (fs x / deriv B x) + (1 - k) * (1 - cdf μs x)) (B x)) ∧
      (Shared.IsEquilibrium k μb μs loS hiS loB hiB S B →
        ∀ y ∈ Icc loS hiS, S y = B x →
          (y - B x) * (fs x / deriv B x) + (1 - k) * (1 - cdf μs x) = 0) := by
  obtain ⟨hP, hlohi, hF0, hF1, hFmono, hFd⟩ := hμs
  obtain ⟨hbddA, hbddB, hBmono, hflat, hdiff⟩ := hB
  have hIoo : Ioo a c ⊆ Ioo loB hiB := Ioo_subset_Ioo ha hc
  -- B is differentiable on (a, c)
  have hBd : ∀ z ∈ Ioo a c, DifferentiableAt ℝ B z := by
    intro z hz
    obtain ⟨z1, hz1a, hz1b⟩ := exists_between hz.1
    obtain ⟨z2, hz2a, hz2b⟩ := exists_between hz.2
    have m1 : z1 ∈ Ioo a c := ⟨hz1a, hz1b.trans hz.2⟩
    have m2 : z2 ∈ Ioo a c := ⟨hz.1.trans hz2a, hz2b⟩
    refine hdiff z (hIoo hz) ?_ ?_
    · exact lt_of_le_of_lt (csInf_le hbddB ⟨z1, Ioo_subset_Icc_self (hIoo m1), rfl⟩)
        (hmono m1 hz hz1b)
    · exact lt_of_lt_of_le (hmono hz m2 hz2a)
        (le_csSup hbddA ⟨z2, Ioo_subset_Icc_self (hIoo m2), rfl⟩)
  have hBcont : ContinuousOn B (Ioo a c) := fun z hz => (hBd z hz).continuousAt.continuousWithinAt
  have hBx : HasDerivAt B (deriv B x) x := (hBd x hx).hasDerivAt
  obtain ⟨g, hgx, hgd, hgev⟩ := P42f5f242.local_inverse B a c x hx hmono hBcont hBx hderiv.ne'
  -- the clamped strategy
  set Bc : ℝ → ℝ := fun z => B (max loB (min z hiB)) with hBc
  have hclamp : ∀ z, max loB (min z hiB) ∈ Icc loB hiB := fun z =>
    ⟨le_max_left _ _, max_le hlohi.le (min_le_right _ _)⟩
  have hBcmono : Monotone Bc := by
    intro z w hzw
    exact hBmono (hclamp z) (hclamp w) (max_le_max le_rfl (min_le_min hzw le_rfl))
  have hBcEq : ∀ z ∈ Icc loB hiB, Bc z = B z := by
    intro z hz
    simp only [hBc, min_eq_left hz.2, max_eq_right hz.1]
  obtain ⟨U, hU⟩ := hbddA
  obtain ⟨L, hL⟩ := hbddB
  have hBcint : Integrable Bc μs := by
    refine Integrable.of_bound hBcmono.measurable.aestronglyMeasurable (max |L| |U|) ?_
    refine Eventually.of_forall fun z => ?_
    have h1 : Bc z ≤ U := hU ⟨_, hclamp z, rfl⟩
    have h2 : L ≤ Bc z := hL ⟨_, hclamp z, rfl⟩
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := neg_abs_le L; have := le_max_left |L| |U|; linarith
    · have := le_abs_self U; have := le_max_right |L| |U|; linarith
  have hxI : x ∈ Ioo loB hiB := hIoo hx
  have hFx : HasDerivAt (cdf μs) (fs x) x :=
    (hFd x (Ioo_subset_Icc_self hxI)).hasDerivAt (Icc_mem_nhds hxI.1 hxI.2)
  have hBccont : ContinuousAt Bc x := by
    have : Bc =ᶠ[𝓝 x] B := by
      filter_upwards [Icc_mem_nhds hxI.1 hxI.2] with z hz using hBcEq z hz
    exact (hBd x hx).continuousAt.congr this.symm
  have hK := P42f5f242.hasDerivAt_Iic μs Bc hBcmono hBcint x (fs x) hFx hBccont
  have hBcx : Bc x = B x := hBcEq x (Ioo_subset_Icc_self hxI)
  rw [hBcx] at hK
  -- a.e. support
  have hsupp : ∀ᵐ z ∂μs, z ∈ Icc loB hiB := by
    rw [ae_iff]
    have hsub : {z | ¬ z ∈ Icc loB hiB} ⊆ Iic loB ∪ (Iic hiB)ᶜ := by
      intro z hz
      simp only [mem_setOf_eq, mem_Icc, not_and_or, not_le] at hz
      rcases hz with hz | hz
      · exact Or.inl hz.le
      · exact Or.inr (by simpa using hz)
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · rw [← ofReal_cdf, hF0, ENNReal.ofReal_zero]
    · rw [prob_compl_eq_zero_iff measurableSet_Iic, ← ofReal_cdf, hF1, ENNReal.ofReal_one]
  have part1 : ∀ v : ℝ, HasDerivAt (fun s => Shared.sellerProfit k μs B s v)
      ((v - B x) * (fs x / deriv B x) + (1 - k) * (1 - cdf μs x)) (B x) := by
    intro v
    set I : ℝ := ∫ z, Bc z ∂μs
    set K : ℝ → ℝ := fun t => ∫ z in Iic t, Bc z ∂μs
    have hrep : (fun s => Shared.sellerProfit k μs B s v) =ᶠ[𝓝 (B x)]
        (fun s => k * (I - K (g s)) + ((1 - k) * s - v) * (1 - cdf μs (g s))) := by
      filter_upwards [hgev] with s hs
      obtain ⟨hBg, hgI⟩ := hs
      set t := g s
      have htI : t ∈ Ioo loB hiB := hIoo hgI
      have hFt : ContinuousAt (cdf μs) t :=
        ((hFd t (Ioo_subset_Icc_self htI)).hasDerivAt (Icc_mem_nhds htI.1 htI.2)).continuousAt
      have hat := P42f5f242.atom_zero μs t hFt
      have hne : ∀ᵐ z ∂μs, z ≠ t := by
        rw [ae_iff]; simpa using hat
      have hae : (fun z => if s ≤ B z then k * B z + (1 - k) * s - v else 0) =ᵐ[μs]
          (Ioi t).indicator (fun z => k * Bc z + ((1 - k) * s - v)) := by
        filter_upwards [hsupp, hne] with z hz hzt
        rcases lt_or_gt_of_ne hzt with hlt | hgt
        · have hnot : ¬ (z ∈ Ioi t) := fun h => absurd (mem_Ioi.1 h) (not_lt.2 hlt.le)
          rw [indicator_of_notMem hnot]
          have : B z < s := by
            rw [← hBg]
            by_cases hza : a < z
            · exact hmono ⟨hza, hlt.trans hgI.2⟩ hgI hlt
            · push Not at hza
              have hm : (a + t) / 2 ∈ Ioo a c := ⟨by linarith [hgI.1], by linarith [hgI.2, hgI.1]⟩
              have hm2 : (a + t) / 2 < t := by linarith [hgI.1]
              calc B z ≤ B ((a + t) / 2) :=
                    hBmono hz (Ioo_subset_Icc_self (hIoo hm)) (by linarith [hgI.1])
                _ < B t := hmono hm hgI hm2
          rw [if_neg (not_le.2 this)]
        · rw [indicator_of_mem (mem_Ioi.2 hgt)]
          have : s ≤ B z := by
            rw [← hBg]; exact hBmono (Ioo_subset_Icc_self htI) hz hgt.le
          rw [if_pos this, hBcEq z hz]; ring
      unfold Shared.sellerProfit
      rw [integral_congr_ae hae, integral_indicator measurableSet_Ioi,
        integral_add (hBcint.integrableOn.const_mul k) (integrable_const _),
        integral_const_mul, setIntegral_const, smul_eq_mul]
      have h1 : ∫ z in Ioi t, Bc z ∂μs = I - K t := by
        have := integral_add_compl (measurableSet_Iic (a := t)) hBcint
        rw [compl_Iic] at this
        simp only [I, K]; linarith
      have h2 : μs.real (Ioi t) = 1 - cdf μs t := by
        rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, cdf_eq_real]
      rw [h1, h2]
      ring
    refine HasDerivAt.congr_of_eventuallyEq ?_ hrep
    have hKg : HasDerivAt (fun s => K (g s)) (B x * fs x * (deriv B x)⁻¹) (B x) := by
      have hK' : HasDerivAt K (B x * fs x) (g (B x)) := by rw [hgx]; exact hK
      exact hK'.comp (B x) hgd
    have hFg : HasDerivAt (fun s => cdf μs (g s)) (fs x * (deriv B x)⁻¹) (B x) := by
      have hF' : HasDerivAt (cdf μs) (fs x) (g (B x)) := by rw [hgx]; exact hFx
      exact hF'.comp (B x) hgd
    have hlin : HasDerivAt (fun s => (1 - k) * s - v) (1 - k) (B x) := by
      simpa using ((hasDerivAt_id (B x)).const_mul (1 - k)).sub_const v
    have htot := ((hKg.const_sub I).const_mul k).add (hlin.mul (hFg.const_sub 1))
    refine htot.congr_deriv ?_
    rw [hgx]
    field_simp
    ring
  refine ⟨part1, ?_⟩
  intro heq y hy hSy
  have hmax : IsLocalMax (fun s => Shared.sellerProfit k μs B s y) (B x) := by
    refine Eventually.of_forall fun s => ?_
    have := heq.2 y hy s
    rw [hSy] at this
    exact this
  exact hmax.hasDerivAt_eq_zero (part1 y)
