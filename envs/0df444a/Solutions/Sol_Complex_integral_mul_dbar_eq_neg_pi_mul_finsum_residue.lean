-- Prove2me | solution 1 for Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b5d61594-7446-5929-b79b-4b451fe686c6

import Mathlib
import Theorems.Thm_Complex_integral_mul_dbar_eq_zero_of_differentiableOn
import Theorems.Thm_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue

open MeasureTheory Filter Complex Metric Set
open scoped Topology Real

namespace CauchyPompeiuResidue

noncomputable def D (f : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2

theorem D_continuous {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (D f) := by
  unfold D
  have hc : ∀ v : ℂ, Continuous fun z => fderiv ℝ f z v := fun v =>
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact ((hc 1).add (continuous_const.mul (hc I))).div_const _

theorem D_eq_zero_of_notMem_tsupport {f : ℂ → ℂ} {z : ℂ} (hz : z ∉ tsupport f) : D f z = 0 := by
  simp [D, fderiv_of_notMem_tsupport ℝ hz]

theorem D_hasCompactSupport {f : ℂ → ℂ} (hf : HasCompactSupport f) : HasCompactSupport (D f) :=
  HasCompactSupport.intro hf fun _ hz => D_eq_zero_of_notMem_tsupport hz

theorem tsupport_D_subset (f : ℂ → ℂ) : tsupport (D f) ⊆ tsupport f :=
  closure_minimal (fun _ hz => by
    by_contra h'
    exact hz (D_eq_zero_of_notMem_tsupport h')) (isClosed_tsupport f)

theorem integrableOn_inv (r : ℝ) : IntegrableOn (fun x : ℂ => x⁻¹) (ball 0 r) := by
  have hd : 1 ≤ Module.finrank ℝ ℂ := by rw [Complex.finrank_real_complex]; norm_num
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) hd (C := 1) (α := 1) ?_ ?_ ?_
  · rw [Complex.finrank_real_complex]; norm_num
  · refine Eventually.of_forall fun x => le_of_eq ?_
    rw [norm_inv, Real.rpow_neg_one, one_mul]
  · exact measurable_inv.aestronglyMeasurable

theorem integrableOn_inv_sub (a : ℂ) (r : ℝ) :
    IntegrableOn (fun z : ℂ => (z - a)⁻¹) (ball a r) := by
  have hT := (measurePreserving_add_right (volume : Measure ℂ) a).integrableOn_comp_preimage
    (measurableEmbedding_addRight a) (f := fun z : ℂ => (z - a)⁻¹) (s := ball a r)
  rw [← hT]
  have hpre : (fun x : ℂ => x + a) ⁻¹' ball a r = ball 0 r := by
    ext x
    simp only [mem_preimage, mem_ball_iff_norm, add_sub_cancel_right, sub_zero]
  rw [hpre]
  simp only [Function.comp_def, add_sub_cancel_right]
  exact integrableOn_inv r

theorem integrable_inv_sub_mul (a : ℂ) {u : ℂ → ℂ} (hu : Continuous u)
    (hus : HasCompactSupport u) : Integrable fun z => (z - a)⁻¹ * u z := by
  obtain ⟨R, hR⟩ := hus.isCompact.isBounded.subset_closedBall a
  have hq : IntegrableOn (fun z : ℂ => (z - a)⁻¹) (closedBall a (R + 1)) :=
    (integrableOn_inv_sub a (R + 2)).mono_set (closedBall_subset_ball (by linarith))
  have h1 : IntegrableOn (fun z => (z - a)⁻¹ * u z) (closedBall a (R + 1)) :=
    hq.mul_continuousOn hu.continuousOn (isCompact_closedBall _ _)
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h1
  intro z hz
  have huz : u z ≠ 0 := fun h0 => hz (by simp [h0])
  exact closedBall_subset_closedBall (by linarith) (hR (subset_tsupport _ huz))

theorem continuous_mul_of_tsupport_subset {V : Set ℂ} {f g : ℂ → ℂ} (hV : IsOpen V)
    (hf : ContinuousOn f V) (hg : Continuous g) (hgV : tsupport g ⊆ V) :
    Continuous fun z => f z * g z := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z ∈ V
  · exact (hf.continuousAt (hV.mem_nhds hz)).mul hg.continuousAt
  · have hz' : z ∉ tsupport g := fun h' => hz (hgV h')
    have h0 : g =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz'
    have : (fun w => f w * g w) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h0] with w hw
      simp [hw]
    exact (continuousAt_congr this).2 continuousAt_const

theorem integrable_mul_of_tsupport_subset {V : Set ℂ} {f g : ℂ → ℂ} (hV : IsOpen V)
    (hf : ContinuousOn f V) (hg : Continuous g) (hgs : HasCompactSupport g)
    (hgV : tsupport g ⊆ V) : Integrable fun z => f z * g z :=
  (continuous_mul_of_tsupport_subset hV hf hg hgV).integrable_of_hasCompactSupport hgs.mul_left

noncomputable def Freg (F c : ℂ → ℂ) (z : ℂ) : ℂ :=
  limUnder (𝓝[≠] z) fun w => F w - c z / (w - z)

theorem Freg_eq {F c : ℂ → ℂ} {a : ℂ} {g : ℂ → ℂ} (hg : ContinuousAt g a)
    (hev : ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z) : Freg F c a = g a := by
  have ht : Tendsto (fun w => F w - c a / (w - a)) (𝓝[≠] a) (𝓝 (g a)) := by
    refine ((hg.tendsto).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hev] with w hw
    rw [hw]
    ring
  exact ht.limUnder_eq

section

variable {U : Set ℂ} {F c : ℂ → ℂ} (hU : IsOpen U)
  (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
include hU hloc

theorem local_ball {a : ℂ} (ha : a ∈ U) : ∃ g : ℂ → ℂ, ∃ r > 0, ball a r ⊆ U ∧
    (∀ z ∈ ball a r, AnalyticAt ℂ g z) ∧ ∀ z ∈ ball a r, z ≠ a → F z = c a / (z - a) + g z := by
  obtain ⟨g, hg, hev⟩ := hloc a ha
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhds_iff.1 hg.eventually_analyticAt
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε₂, hε₂, hball₂⟩ := hev
  obtain ⟨ε₃, hε₃, hball₃⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds ha)
  have h1 : min ε₁ (min ε₂ ε₃) ≤ ε₁ := min_le_left _ _
  have h2 : min ε₁ (min ε₂ ε₃) ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : min ε₁ (min ε₂ ε₃) ≤ ε₃ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨g, min ε₁ (min ε₂ ε₃), by positivity, (ball_subset_ball h3).trans hball₃,
    fun z hz => hball₁ (ball_subset_ball h1 hz), fun z hz hza => ?_⟩
  exact hball₂ (mem_ball.1 (ball_subset_ball h2 hz)) hza

omit hU in

theorem c_eq_zero_near {a : ℂ} {g : ℂ → ℂ} {r : ℝ} (hsub : ball a r ⊆ U)
    (hg : ∀ z ∈ ball a r, AnalyticAt ℂ g z)
    (hF : ∀ z ∈ ball a r, z ≠ a → F z = c a / (z - a) + g z) {z : ℂ} (hz : z ∈ ball a r)
    (hza : z ≠ a) : c z = 0 := by
  obtain ⟨gz, hgz, hevz⟩ := hloc z (hsub hz)
  have hnhds : ∀ᶠ w in 𝓝 z, w ∈ ball a r ∧ w ≠ a :=
    (isOpen_ball.inter isOpen_ne).mem_nhds ⟨hz, hza⟩
  have hΦ : ContinuousAt (fun w => c a / (w - a) + g w - gz w) z := by
    have h1 : ContinuousAt (fun w => c a / (w - a)) z :=
      continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 hza)
    exact (h1.add (hg z hz).continuousAt).sub hgz.continuousAt
  have hev : (fun w => (c a / (w - a) + g w - gz w) * (w - z)) =ᶠ[𝓝[≠] z] fun _ => c z := by
    filter_upwards [hevz, mem_nhdsWithin_of_mem_nhds hnhds, self_mem_nhdsWithin]
      with w hw1 hw2 hw3
    have hwz : w - z ≠ 0 := sub_ne_zero.2 hw3
    have : c z / (w - z) = c a / (w - a) + g w - gz w := by
      rw [← hF w hw2.1 hw2.2, hw1]
      ring
    exact ((div_eq_iff hwz).1 this).symm
  have ht : Tendsto (fun w => (c a / (w - a) + g w - gz w) * (w - z)) (𝓝[≠] z) (𝓝 0) := by
    have h2 : Tendsto (fun w : ℂ => w - z) (𝓝 z) (𝓝 0) := by
      have := ((continuous_id.sub continuous_const).tendsto z : Tendsto (fun w : ℂ => w - z) _ _)
      simp at this
      exact this
    have := (hΦ.tendsto.mul h2).mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
    simpa using this
  exact tendsto_const_nhds_iff.1 (ht.congr' hev)

theorem clean {a : ℂ} (ha : a ∈ U) : ∃ g : ℂ → ℂ, ∃ r > 0, ball a r ⊆ U ∧
    (∀ z ∈ ball a r, AnalyticAt ℂ g z) ∧
    (∀ z ∈ ball a r, Freg F c z = c a / (z - a) + g z) ∧
    ∀ z ∈ ball a r, z ≠ a → c z = 0 ∧ F z = Freg F c z := by
  obtain ⟨g, r, hr, hsub, hg, hF⟩ := local_ball hU hloc ha
  have hc0 : ∀ z ∈ ball a r, z ≠ a → c z = 0 := fun z hz hza =>
    c_eq_zero_near hloc hsub hg hF hz hza
  have hFF : ∀ z ∈ ball a r, z ≠ a → F z = Freg F c z := by
    intro z hz hza
    obtain ⟨gz, hgz, hevz⟩ := hloc z (hsub hz)
    rw [Freg_eq hgz.continuousAt hevz]
    have hnhds : ∀ᶠ w in 𝓝 z, w ∈ ball a r ∧ w ≠ a :=
      (isOpen_ball.inter isOpen_ne).mem_nhds ⟨hz, hza⟩
    have hΦc : ContinuousAt (fun w => c a / (w - a) + g w) z :=
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.2 hza)).add (hg z hz).continuousAt
    have h1 : Tendsto (fun w => c a / (w - a) + g w) (𝓝[≠] z) (𝓝 (gz z)) := by
      refine ((hgz.continuousAt.tendsto).mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [hevz, mem_nhdsWithin_of_mem_nhds hnhds] with w hw1 hw2
      rw [← hF w hw2.1 hw2.2, hw1, hc0 z hz hza, zero_div, zero_add]
    have h2 : Tendsto (fun w => c a / (w - a) + g w) (𝓝[≠] z) (𝓝 (c a / (z - a) + g z)) :=
      hΦc.tendsto.mono_left nhdsWithin_le_nhds
    rw [hF z hz hza]
    exact tendsto_nhds_unique h2 h1
  refine ⟨g, r, hr, hsub, hg, fun z hz => ?_, fun z hz hza => ⟨hc0 z hz hza, hFF z hz hza⟩⟩
  by_cases hza : z = a
  · rw [hza, sub_self, div_zero, zero_add]
    refine Freg_eq (hg a (mem_ball_self hr)).continuousAt ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a hr), self_mem_nhdsWithin]
      with w hw hwa
    exact hF w hw hwa
  · rw [← hFF z hz hza, hF z hz hza]

theorem finite_exceptional {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    {z ∈ K | c z ≠ 0 ∨ F z ≠ Freg F c z}.Finite := by
  choose g r hr hsub hg hFreg hexc using fun (x : ℂ) (hx : x ∈ K) => clean hU hloc (hKU hx)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx => ball x (r x hx))
    fun x hx => ball_mem_nhds x (hr x hx)
  refine (t.finite_toSet.image (fun x : K => (x : ℂ))).subset ?_
  rintro z ⟨hzK, hz⟩
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (ht hzK)
  refine ⟨x, hxt, ?_⟩
  by_contra hne
  have := hexc x x.2 z hzx (fun h' => hne h'.symm)
  rcases hz with hz | hz
  · exact hz this.1
  · exact hz this.2

end

theorem main (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, F z * D h z = -π * ∑ᶠ a, c a * h a := by
  have hK : IsCompact (tsupport h) := hsupp
  have hfin := finite_exceptional hU hloc hK hU'

  obtain ⟨T, hmemT⟩ : ∃ T : Finset ℂ, ∀ p, p ∈ T ↔ p ∈ tsupport h ∧ c p ≠ 0 := by
    have hfinT : {z ∈ tsupport h | c z ≠ 0}.Finite :=
      hfin.subset fun z hz => ⟨hz.1, Or.inl hz.2⟩
    exact ⟨hfinT.toFinset, fun p => by simp [Set.Finite.mem_toFinset]⟩

  obtain ⟨R, hR⟩ : ∃ R : ℂ → ℂ, ∀ z, R z = ∑ p ∈ T, c p / (z - p) := ⟨_, fun z => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, ∀ z, G z = Freg F c z - R z := ⟨_, fun z => rfl⟩

  obtain ⟨V, hV⟩ : ∃ V : Set ℂ, ∀ z, z ∈ V ↔ z ∈ U ∧ (c z ≠ 0 → z ∈ tsupport h) :=
    ⟨{z | z ∈ U ∧ (c z ≠ 0 → z ∈ tsupport h)}, fun z => Iff.rfl⟩
  have hKV : tsupport h ⊆ V := fun z hz => (hV z).2 ⟨hU' hz, fun _ => hz⟩
  have hVo : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro x hxV
    obtain ⟨hxU, hx⟩ := (hV x).1 hxV
    obtain ⟨g, r, hr, hsub, hg, hFreg, hexc⟩ := clean hU hloc hxU
    refine mem_of_superset (ball_mem_nhds x hr) fun z hz => (hV z).2 ⟨hsub hz, fun hcz => ?_⟩
    by_cases hzx : z = x
    · rw [hzx]
      exact hx (hzx ▸ hcz)
    · exact absurd (hexc z hz hzx).1 hcz
  have hGd : DifferentiableOn ℂ G V := by
    intro x hxV
    obtain ⟨hxU, hx⟩ := (hV x).1 hxV
    obtain ⟨g, r, hr, hsub, hg, hFreg, hexc⟩ := clean hU hloc hxU
    have hGev : G =ᶠ[𝓝 x] fun w => c x / (w - x) + g w - R w := by
      filter_upwards [ball_mem_nhds x hr] with w hw
      rw [hG w, hFreg w hw]
    have hRd : ∀ s : Finset ℂ, x ∉ s →
        DifferentiableAt ℂ (fun w => ∑ p ∈ s, c p / (w - p)) x := by
      intro s hxs
      refine DifferentiableAt.fun_sum fun p hp => ?_
      have hxp : x - p ≠ 0 := sub_ne_zero.2 fun h' => hxs (h' ▸ hp)
      exact (differentiableAt_const _).div (differentiableAt_id.sub_const p) hxp
    have hΦ : DifferentiableAt ℂ (fun w => c x / (w - x) + g w - R w) x := by
      by_cases hxT : x ∈ T
      · have hfun : (fun w => c x / (w - x) + g w - R w)
            = fun w => g w - ∑ p ∈ T.erase x, c p / (w - p) := by
          funext w
          rw [hR w, ← Finset.add_sum_erase T (fun p => c p / (w - p)) hxT]
          ring
        rw [hfun]
        exact (hg x (mem_ball_self hr)).differentiableAt.sub (hRd _ (Finset.notMem_erase x T))
      · have hcx : c x = 0 := by
          by_contra hcx
          exact hxT ((hmemT x).2 ⟨hx hcx, hcx⟩)
        have hfun : (fun w => c x / (w - x) + g w - R w)
            = fun w => g w - ∑ p ∈ T, c p / (w - p) := by
          funext w
          rw [hR w, hcx, zero_div, zero_add]
        rw [hfun]
        exact (hg x (mem_ball_self hr)).differentiableAt.sub (hRd _ hxT)
    exact (hΦ.congr_of_eventuallyEq hGev).differentiableWithinAt

  have hDh_cont : Continuous (D h) := D_continuous hh
  have hDh_supp : HasCompactSupport (D h) := D_hasCompactSupport hsupp
  have hIG : Integrable fun z => G z * D h z :=
    integrable_mul_of_tsupport_subset hVo hGd.continuousOn hDh_cont hDh_supp
      ((tsupport_D_subset h).trans hKV)
  have hIp : ∀ p, Integrable fun z => c p * ((z - p)⁻¹ * D h z) := fun p =>
    (integrable_inv_sub_mul p hDh_cont hDh_supp).const_mul _
  have hIR : Integrable fun z => ∑ p ∈ T, c p * ((z - p)⁻¹ * D h z) :=
    integrable_finsetSum _ fun p _ => hIp p

  have hae : (fun z => F z * D h z)
      =ᵐ[volume] fun z => G z * D h z + ∑ p ∈ T, c p * ((z - p)⁻¹ * D h z) := by
    filter_upwards [hfin.countable.ae_notMem volume] with z hz
    by_cases hzK : z ∈ tsupport h
    · have hFz : F z = Freg F c z := by
        by_contra hne
        exact hz ⟨hzK, Or.inr hne⟩
      have hsum : ∑ p ∈ T, c p / (z - p) * D h z = ∑ p ∈ T, c p * ((z - p)⁻¹ * D h z) :=
        Finset.sum_congr rfl fun p _ => by ring
      rw [hFz, hG z, hR z, sub_mul, Finset.sum_mul, hsum]
      ring
    · have h0 : D h z = 0 := D_eq_zero_of_notMem_tsupport hzK
      simp [h0]

  have hHG : ∫ z, G z * D h z = 0 :=
    Complex.integral_mul_dbar_eq_zero_of_differentiableOn V hVo G hGd h hh hsupp hKV
  have hHp : ∀ p, ∫ z, (z - p)⁻¹ * D h z = -π * h p := fun p =>
    Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul p h hh hsupp

  have hfs : ∑ᶠ a, c a * h a = ∑ p ∈ T, c p * h p := by
    apply finsum_eq_sum_of_support_subset
    intro a ha
    rw [Function.mem_support, mul_ne_zero_iff] at ha
    rw [Finset.mem_coe, hmemT]
    exact ⟨subset_tsupport _ ha.2, ha.1⟩
  rw [integral_congr_ae hae, integral_add hIG hIR, integral_finsetSum _ (fun p _ => hIp p), hHG,
    zero_add, hfs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_const_mul, hHp p]
  ring

end CauchyPompeiuResidue

open Complex MeasureTheory in
open scoped Real Topology in
theorem solution
    (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, F z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * ∑ᶠ a, c a * h a :=
  CauchyPompeiuResidue.main U hU F c hloc h hh hsupp hU'

end S_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue
end P2MW
export P2MW.S_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue (solution)
