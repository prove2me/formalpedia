-- Prove2me | solution 1 for EquilibriumExperiment.Gradient.lemma_4_muLim_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T13:41:59.476426+00:00
-- url     : https://prove2.me/submissions/0eaeb5ce-13a4-4700-a88c-adec5488b7a4

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model
import Theorems.Thm_EquilibriumExperiment_Gradient_lemma_2

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace EqExpL4MAux

open EquilibriumExperiment.Gradient

lemma implicit_hasDerivAt {u : ℝ → ℝ} {p μ₀ : ℝ} {F : ℝ × ℝ → ℝ} {F' : ℝ × ℝ →L[ℝ] ℝ}
    (hF : HasFDerivAt F F' (μ₀, p)) (hu : ContinuousAt u p) (hu0 : u p = μ₀)
    (hzero : ∀ᶠ q in 𝓝 p, F (u q, q) = F (μ₀, p)) (ha : F' (1, 0) ≠ 0) :
    HasDerivAt u (-(F' (0, 1)) / F' (1, 0)) p := by
  set a := F' (1, 0) with ha_def
  set b := F' (0, 1) with hb_def
  have hlin : ∀ v : ℝ × ℝ, F' v = a * v.1 + b * v.2 := by
    intro v
    have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hv]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hφ : Tendsto (fun q => (u q, q)) (𝓝 p) (𝓝 (μ₀, p)) := by
    have := hu.tendsto.prodMk_nhds (tendsto_id (x := 𝓝 p))
    rwa [hu0] at this
  have hlo := hF.isLittleO.comp_tendsto hφ
  have haa : 0 < |a| := abs_pos.mpr ha
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  set R := |b| / |a| + 1 with hR
  have hR1 : 1 ≤ R := by have : 0 ≤ |b| / |a| := by positivity
                         linarith
  set c' := min (|a| / 2) (c * |a| / (2 * R)) with hc'
  have hc'0 : 0 < c' := lt_min (by linarith) (by positivity)
  have hc'1 : c' ≤ |a| / 2 := min_le_left _ _
  have hc'2 : c' ≤ c * |a| / (2 * R) := min_le_right _ _
  filter_upwards [isLittleO_iff.mp hlo hc'0, hzero] with q hq hq0
  simp only [Function.comp_apply, hq0, sub_self, zero_sub, norm_neg] at hq
  rw [hlin] at hq
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.norm_def, Real.norm_eq_abs] at hq
  set du := u q - μ₀ with hdu
  set dq := q - p with hdq
  set E := a * du + b * dq with hE
  have hmax : max |du| |dq| ≤ |du| + |dq| :=
    max_le (by linarith [abs_nonneg dq]) (by linarith [abs_nonneg du])
  have hE1 : |E| ≤ c' * (|du| + |dq|) :=
    le_trans hq (mul_le_mul_of_nonneg_left hmax hc'0.le)
  have hdu1 : |a| * |du| ≤ |E| + |b| * |dq| := by
    have : a * du = E - b * dq := by rw [hE]; ring
    rw [← abs_mul, this, ← abs_mul]
    exact abs_sub _ _
  have hdu2 : |du| ≤ (|E| + |b| * |dq|) / |a| := by
    rw [le_div_iff₀ haa]; linarith
  have hE2 : |E| ≤ 2 * c' * R * |dq| := by
    have h6 : |E| ≤ 2 * c' * (|b| / |a|) * |dq| + 2 * c' * |dq| := by
      -- from |E| ≤ c'|du| + c'|dq| and |du| ≤ (|E| + |b||dq|)/|a|
      have k1 : |E| ≤ c' * ((|E| + |b| * |dq|) / |a|) + c' * |dq| := by nlinarith
      have k2 : c' / |a| ≤ 1 / 2 := by rw [div_le_iff₀ haa]; linarith
      have k3 : c' * ((|E| + |b| * |dq|) / |a|) = (c' / |a|) * |E| + c' * (|b| / |a|) * |dq| := by
        field_simp
      rw [k3] at k1
      have k4 : (c' / |a|) * |E| ≤ 1 / 2 * |E| := mul_le_mul_of_nonneg_right k2 (abs_nonneg _)
      linarith
    have : 2 * c' * (|b| / |a|) * |dq| + 2 * c' * |dq| = 2 * c' * R * |dq| := by rw [hR]; ring
    linarith
  -- conclude
  have hgoal : u q - u p - (q - p) • (-b / a) = E / a := by
    rw [hu0, smul_eq_mul, hE, hdu, hdq]; field_simp; ring
  rw [hgoal, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, div_le_iff₀ haa]
  have : 2 * c' * R ≤ c * |a| := by
    rw [le_div_iff₀ (by positivity)] at hc'2; linarith
  calc |E| ≤ 2 * c' * R * |dq| := hE2
    _ ≤ c * |a| * |dq| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ = c * |q - p| * |a| := by rw [hdq]; ring

section FInt
variable {B : Type} [MeasurableSpace B] (β : Measure B) [IsProbabilityMeasure β]
  (f : B → ℝ → ℝ) (hf01 : ∀ b x, 0 ≤ x → f b x ∈ Set.Icc (0 : ℝ) 1)
  (hfmeas : Measurable (Function.uncurry f))

include hfmeas in
lemma fmeas (x : ℝ) : Measurable (fun b => f b x) :=
  hfmeas.comp (measurable_id.prodMk measurable_const)

include hf01 hfmeas in
lemma fint {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun b => f b x) β ∧ ∫ b, f b x ∂β ∈ Set.Icc (0 : ℝ) 1 := by
  have hint : Integrable (fun b => f b x) β := by
    refine (integrable_const (1 : ℝ)).mono' (fmeas f hfmeas x).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun b => ?_
    have := hf01 b x hx
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  refine ⟨hint, integral_nonneg fun b => (hf01 b x hx).1, ?_⟩
  have : ∫ b, f b x ∂β ≤ ∫ _b, (1 : ℝ) ∂β :=
    integral_mono hint (integrable_const _) fun b => (hf01 b x hx).2
  simpa using this

include hf01 hfmeas in
lemma fint_mono (hfmono : ∀ b, MonotoneOn (f b) (Set.Ici 0)) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) : ∫ b, f b x ∂β ≤ ∫ b, f b y ∂β :=
  integral_mono (fint β f hf01 hfmeas hx).1 (fint β f hf01 hfmeas (le_trans hx hxy)).1
    fun b => hfmono b (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (le_trans hx hxy)) hxy

include hf01 hfmeas in
lemma fint_continuousOn (hfcont : ∀ b, ContinuousOn (f b) (Set.Ici 0)) (c : ℝ → ℝ) (s : Set ℝ)
    (hc : ContinuousOn c s) (hc0 : ∀ μ ∈ s, 0 ≤ c μ) :
    ContinuousOn (fun μ => ∫ b, f b (c μ) ∂β) s := by
  apply continuousOn_of_dominated (bound := fun _ => 1)
  · intro μ _
    exact (fmeas f hfmeas (c μ)).aestronglyMeasurable
  · intro μ hμ
    refine Filter.Eventually.of_forall fun b => ?_
    have := hf01 b _ (hc0 μ hμ)
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun b => ?_
    exact (hfcont b).comp hc (fun μ hμ => Set.mem_Ici.mpr (hc0 μ hμ))

include hf01 hfmeas in
lemma fint_tendsto (hfcont : ∀ b, ContinuousOn (f b) (Set.Ici 0)) {ι : Type} {l : Filter ι}
    [l.IsCountablyGenerated] (u : ι → ℝ) {x : ℝ} (hx : 0 ≤ x) (hu : Tendsto u l (𝓝 x))
    (hu0 : ∀ᶠ i in l, 0 ≤ u i) :
    Tendsto (fun i => ∫ b, f b (u i) ∂β) l (𝓝 (∫ b, f b x ∂β)) := by
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => 1)
  · exact Filter.Eventually.of_forall fun i => (fmeas f hfmeas (u i)).aestronglyMeasurable
  · filter_upwards [hu0] with i hi
    refine Filter.Eventually.of_forall fun b => ?_
    have := hf01 b _ hi
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun b => ?_
    have h1 : Tendsto u l (𝓝[Set.Ici 0] x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hu, hu0⟩
    exact ((hfcont b) x (Set.mem_Ici.mpr hx)).tendsto.comp h1

end FInt

lemma omega_facts (ω : ℝ → ℝ) (hω : IsRegularAllocation ω) {d : ℝ} (hd : 0 < d) :
    ∃ L, sSup (ω '' Set.Ici 0) = L ∧ Tendsto (fun μ => ω (d / μ)) (𝓝[>] 0) (𝓝 L) ∧ 0 ≤ L := by
  obtain ⟨L, -, hL⟩ := hω.2.2.2.2.2.1
  have hmono := hω.2.2.2.1
  have hle : ∀ x, 0 ≤ x → ω x ≤ L := by
    intro x hx
    exact ge_of_tendsto hL ((eventually_ge_atTop x).mono fun y hy =>
      hmono (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (le_trans hx hy)) hy)
  refine ⟨L, ?_, ?_, ?_⟩
  · apply csSup_eq_of_forall_le_of_forall_lt_exists_gt (Set.Nonempty.image _ ⟨0, le_refl _⟩)
    · rintro _ ⟨x, hx, rfl⟩; exact hle x hx
    · intro w hw
      obtain ⟨y, hy1, hy2⟩ := ((hL.eventually (lt_mem_nhds hw)).and (eventually_ge_atTop 0)).exists
      exact ⟨ω y, ⟨y, hy2, rfl⟩, hy1⟩
  · have h : Tendsto (fun μ : ℝ => d / μ) (𝓝[>] 0) atTop := by
      simp only [div_eq_mul_inv]
      exact tendsto_inv_nhdsGT_zero.const_mul_atTop hd
    exact hL.comp h
  · exact le_trans (hω.1 0 le_rfl).1 (hle 0 le_rfl)

lemma accPt_Ici {x : ℝ} (hx : 0 ≤ x) : AccPt x (𝓟 (Set.Ici 0)) := by
  rw [accPt_iff_nhds]
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨x + ε / 2, ⟨hball ?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]; linarith
  · simp only [Set.mem_Ici]; linarith
  · intro h; linarith


lemma fprime_bounds (g g' g'' : ℝ → ℝ) (h01 : ∀ x, 0 ≤ x → g x ∈ Set.Icc (0 : ℝ) 1)
    (hmono : MonotoneOn g (Set.Ici 0))
    (hder : ∀ x, 0 ≤ x → HasDerivWithinAt g (g' x) (Set.Ici 0) x ∧
      HasDerivWithinAt g' (g'' x) (Set.Ici 0) x)
    (K : ℝ) (hK : ∀ x, 0 ≤ x → |g'' x| ≤ K) :
    ∀ x, 0 ≤ x → 0 ≤ g' x ∧ g' x ≤ 1 + K := by
  intro x hx
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0 le_rfl)
  refine ⟨(hder x hx).1.nonneg_of_monotoneOn (accPt_Ici hx) hmono, ?_⟩
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope g g' (lt_add_one x)
    (fun t ht => ((hder t (le_trans hx ht.1)).1.continuousWithinAt).mono
      (fun y hy => Set.mem_Ici.mpr (le_trans hx hy.1)))
    (fun t ht => (hder t (by linarith [ht.1])).1.hasDerivAt (Ici_mem_nhds (by linarith [ht.1])))
  have hgc : g' c ≤ 1 := by
    rw [hcs, add_sub_cancel_left, div_one]
    have h1 := h01 (x + 1) (by linarith)
    have h2 := h01 x hx
    linarith [h1.2, h2.1]
  have hlip := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g') (f' := g'')
    (s := Set.Icc x c) (x := x) (y := c) (C := K)
    (fun y hy => ((hder y (le_trans hx hy.1)).2).mono
      (fun z hz => Set.mem_Ici.mpr (le_trans hx hz.1)))
    (fun y hy => by rw [Real.norm_eq_abs]; exact hK y (le_trans hx hy.1))
    (convex_Icc x c) ⟨le_rfl, hc.1.le⟩ ⟨hc.1.le, le_rfl⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hlip
  have hcx : |c - x| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hc.1, hc.2]
  have : K * |c - x| ≤ K := by nlinarith [abs_nonneg (c - x)]
  have := (abs_le.mp hlip).1
  linarith

end EqExpL4MAux

open EqExpL4MAux EquilibriumExperiment.Gradient

theorem solution {B : Type} [MeasurableSpace B] (M : EquilibriumExperiment.Gradient.Market B)
    (hM : M.Standing) {p : ℝ} (hp : 0 < p) (hpos : 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β) :
    HasDerivAt M.muLim (M.muLimDeriv p) p := by
  have hL2 := lemma_2 M hM
  obtain ⟨hd, -, -, -, -, hβ, hω, -, -, -, -, -, -, hf01, hfmono, hfderiv, hf'', hfmeas,
    hf'meas, -, -, -⟩ := hM
  haveI := hβ
  have hfcont : ∀ b, ContinuousOn (M.f b) (Set.Ici 0) := by
    intro b x hx
    exact (hfderiv b x hx).1.continuousWithinAt
  obtain ⟨K₂, hK₂⟩ := hf''
  have hf'b : ∀ b x, 0 ≤ x → 0 ≤ M.f' b x ∧ M.f' b x ≤ 1 + K₂ := fun b =>
    fprime_bounds (M.f b) (M.f' b) (M.f'' b) (hf01 b) (hfmono b) (hfderiv b) K₂ (hK₂ b)
  obtain ⟨L, hLsup, -, hL0⟩ := omega_facts M.ω hω hd
  have hωsup0 : 0 ≤ M.omegaSup := by rw [Market.omegaSup, hLsup]; exact hL0
  -- the mean-field map `Φ(μ, q) = 𝔼 f_B(q ω(d/μ))`
  set Φ : ℝ → ℝ → ℝ := fun μ q => ∫ b, M.f b (q * M.ω (M.d / μ)) ∂M.β with hΦ
  have hωd0 : ∀ μ, 0 < μ → 0 ≤ M.ω (M.d / μ) := fun μ hμ =>
    (hω.1 _ (div_nonneg hd.le hμ.le)).1
  have hΦanti : ∀ q, 0 < q → ∀ x y, 0 < x → 0 < y → x ≤ y → Φ y q ≤ Φ x q := by
    intro q hq x y hx hy hxy
    apply fint_mono M.β M.f hf01 hfmeas hfmono (mul_nonneg hq.le (hωd0 y hy))
    apply mul_le_mul_of_nonneg_left _ hq.le
    exact hω.2.2.2.1 (Set.mem_Ici.mpr (div_nonneg hd.le hy.le))
      (Set.mem_Ici.mpr (div_nonneg hd.le hx.le)) (div_le_div_of_nonneg_left hd.le hx hxy)
  have hΦcont : ∀ μ, 0 < μ → Tendsto (fun q => Φ μ q) (𝓝 p) (𝓝 (Φ μ p)) := by
    intro μ hμ
    apply fint_tendsto M.β M.f hf01 hfmeas hfcont (fun q => q * M.ω (M.d / μ))
      (mul_nonneg hp.le (hωd0 μ hμ)) ((tendsto_id).mul_const _)
    filter_upwards [lt_mem_nhds hp] with q hq
    exact mul_nonneg hq.le (hωd0 μ hμ)
  -- near `p`, `μ_a(q)` exists and solves the mean-field equation
  have hposev : ∀ᶠ q in 𝓝 p, 0 < q ∧ 0 < ∫ b, M.f b (q * M.omegaSup) ∂M.β := by
    have ht : Tendsto (fun q => ∫ b, M.f b (q * M.omegaSup) ∂M.β) (𝓝 p)
        (𝓝 (∫ b, M.f b (p * M.omegaSup) ∂M.β)) := by
      apply fint_tendsto M.β M.f hf01 hfmeas hfcont (fun q => q * M.omegaSup)
        (mul_nonneg hp.le hωsup0) ((tendsto_id).mul_const _)
      filter_upwards [lt_mem_nhds hp] with q hq
      exact mul_nonneg hq.le hωsup0
    exact (lt_mem_nhds hp).and (ht.eventually (lt_mem_nhds hpos))
  have hfix : ∀ q, 0 < q → 0 < ∫ b, M.f b (q * M.omegaSup) ∂M.β →
      M.muLim q ∈ Set.Ioc (0 : ℝ) 1 ∧ M.muLim q = Φ (M.muLim q) q := by
    intro q hq hqpos
    have hexL : ∃ μ ∈ Set.Ioc (0 : ℝ) 1, μ = ∫ b, M.f b (q * M.ω (M.d / μ)) ∂M.β := by
      obtain ⟨μ, ⟨h1, h2⟩, -⟩ := (hL2.1 q hq hqpos).1
      exact ⟨μ, h1, h2⟩
    unfold Market.muLim
    rw [dif_pos hexL]
    exact hexL.choose_spec
  have hfixev : ∀ᶠ q in 𝓝 p, M.muLim q ∈ Set.Ioc (0 : ℝ) 1 ∧
      M.muLim q = Φ (M.muLim q) q := hposev.mono fun q hq => hfix q hq.1 hq.2
  have hmu0 := hfix p hp hpos
  set μ₀ := M.muLim p with hμ₀
  -- continuity of `μ_a` at `p`
  have hcont : ContinuousAt M.muLim p := by
    rw [ContinuousAt, tendsto_order]
    constructor
    · intro a ha
      set s := max a (μ₀ / 2) with hs
      have hs0 : 0 < s := lt_of_lt_of_le (by linarith [hmu0.1.1]) (le_max_right _ _)
      have hsμ : s < μ₀ := max_lt ha (by linarith [hmu0.1.1])
      have hΦs : s < Φ s p := by
        have := hΦanti p hp s μ₀ hs0 hmu0.1.1 hsμ.le
        linarith [hmu0.2]
      filter_upwards [(hΦcont s hs0).eventually (lt_mem_nhds hΦs), hfixev, hposev]
        with q hq hqf hqp
      refine lt_of_le_of_lt (le_max_left a (μ₀ / 2)) ?_
      by_contra hcon
      push Not at hcon
      have := hΦanti q hqp.1 (M.muLim q) s hqf.1.1 hs0 hcon
      linarith [hqf.2]
    · intro b hb
      by_cases hμ1 : μ₀ = 1
      · filter_upwards [hfixev] with q hq
        exact lt_of_le_of_lt hq.1.2 (by linarith)
      · have hμlt : μ₀ < 1 := lt_of_le_of_ne hmu0.1.2 hμ1
        set t := min b 1 with ht
        have htμ : μ₀ < t := lt_min hb hμlt
        have ht0 : 0 < t := lt_trans hmu0.1.1 htμ
        have hΦt : Φ t p < t := by
          have := hΦanti p hp μ₀ t hmu0.1.1 ht0 htμ.le
          linarith [hmu0.2]
        filter_upwards [(hΦcont t ht0).eventually (gt_mem_nhds hΦt), hfixev, hposev]
          with q hq hqf hqp
        refine lt_of_lt_of_le ?_ (min_le_left b 1)
        by_contra hcon
        push Not at hcon
        have := hΦanti q hqp.1 t (M.muLim q) ht0 hqf.1.1 hcon
        linarith [hqf.2]
  set w := M.d / μ₀ with hw
  have hw0 : 0 < w := div_pos hd hmu0.1.1
  have hωw := hω.1 w hw0.le
  rcases eq_or_lt_of_le hωw.1 with hω0 | hωpos
  · -- `ω(w) = 0`: `ω ≡ 0` on `[0, ∞)` and `μ_a` is locally constant
    have hzero : ∀ x, 0 ≤ x → M.ω x = 0 := by
      intro x hx
      rcases le_or_gt x w with hxw | hxw
      · have := hω.2.2.2.1 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hw0.le) hxw
        linarith [(hω.1 x hx).1]
      · have hx0 : 0 < x := lt_trans hw0 hxw
        have hc := hω.2.2.1.2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx)
          (show (0 : ℝ) ≤ 1 - w / x by rw [sub_nonneg, div_le_one hx0]; exact hxw.le)
          (show (0 : ℝ) ≤ w / x from div_nonneg hw0.le hx0.le)
          (show 1 - w / x + w / x = 1 by ring)
        simp only [smul_eq_mul, mul_zero, zero_add] at hc
        rw [div_mul_cancel₀ _ hx0.ne', ← hω0] at hc
        have h0 := (hω.1 0 le_rfl).1
        have h1 := (hω.1 x hx).1
        have h2 : 0 ≤ (1 - w / x) * M.ω 0 :=
          mul_nonneg (by rw [sub_nonneg, div_le_one hx0]; exact hxw.le) h0
        have h3 : w / x * M.ω x ≤ 0 := by linarith
        have h4 : 0 < w / x := div_pos hw0 hx0
        nlinarith
    have hconst : M.muLim =ᶠ[𝓝 p] fun _ => ∫ b, M.f b 0 ∂M.β := by
      filter_upwards [hfixev] with q hq
      rw [hq.2]
      simp only [Φ]
      rw [hzero _ (div_nonneg hd.le hq.1.1.le), mul_zero]
    have hder0 : M.muLimDeriv p = 0 := by
      rw [Market.muLimDeriv, Market.DeltaLim, ← hμ₀, ← hw, ← hω0, zero_mul, zero_div]
    rw [hder0]
    exact (hasDerivAt_const p _).congr_of_eventuallyEq hconst
  · -- `ω(w) > 0`: implicit differentiation
    have hωs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M.ω (Set.Ioi 0) := hω.2.1
    have hopen : Set.Ioi (0 : ℝ) ∈ 𝓝 w := Ioi_mem_nhds hw0
    have hωd : HasDerivAt M.ω (deriv M.ω w) w :=
      ((hωs.differentiableOn (by simp)).differentiableAt hopen).hasDerivAt
    have hω'0 : 0 ≤ deriv M.ω w :=
      (hωd.hasDerivWithinAt (s := Set.Ici 0)).nonneg_of_monotoneOn (accPt_Ici hw0.le)
        hω.2.2.2.1
    set y₀ := p * M.ω w with hy₀
    have hy₀pos : 0 < y₀ := mul_pos hp hωpos
    -- derivative of `y ↦ 𝔼 f_B(y)` at `y₀`
    set e := ∫ b, M.f' b y₀ ∂M.β with he
    have he0 : 0 ≤ e := integral_nonneg fun b => (hf'b b y₀ hy₀pos.le).1
    have hFbar : HasDerivAt (fun y => ∫ b, M.f b y ∂M.β) e y₀ := by
      have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := M.β)
        (F := fun y b => M.f b y) (F' := fun y b => M.f' b y) (x₀ := y₀)
        (bound := fun _ => 1 + K₂) (Ioi_mem_nhds hy₀pos)
        (Filter.Eventually.of_forall fun y => (fmeas M.f hfmeas y).aestronglyMeasurable)
        (fint M.β M.f hf01 hfmeas hy₀pos.le).1
        ((hf'meas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun b y hy => by
          have := hf'b b y (le_of_lt hy)
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2])
        (integrable_const _)
        (Filter.Eventually.of_forall fun b y hy =>
          (hfderiv b y (le_of_lt hy)).1.hasDerivAt (Ici_mem_nhds hy))
      exact this.2
    -- derivative of `μ ↦ ω(d/μ)` at `μ₀`
    have hdiv : HasDerivAt (fun μ => M.d / μ) ((0 * μ₀ - M.d * 1) / μ₀ ^ 2) μ₀ :=
      (hasDerivAt_const μ₀ M.d).div (hasDerivAt_id μ₀) hmu0.1.1.ne'
    set h' := deriv M.ω w * ((0 * μ₀ - M.d * 1) / μ₀ ^ 2) with hh'
    have hh : HasDerivAt (fun μ => M.ω (M.d / μ)) h' μ₀ := hωd.comp μ₀ hdiv
    -- the joint map
    have hh2 : HasFDerivAt ((fun μ => M.ω (M.d / μ)) ∘ (Prod.fst : ℝ × ℝ → ℝ))
        (h' • ContinuousLinearMap.fst ℝ ℝ ℝ) (μ₀, p) :=
      hh.comp_hasFDerivAt (μ₀, p) hasFDerivAt_fst
    have hg : HasFDerivAt (fun x : ℝ × ℝ => x.2 * M.ω (M.d / x.1))
        ((μ₀, p).2 • (h' • ContinuousLinearMap.fst ℝ ℝ ℝ) +
          M.ω (M.d / (μ₀, p).1) • ContinuousLinearMap.snd ℝ ℝ ℝ) (μ₀, p) :=
      (hasFDerivAt_snd).mul hh2
    have hG := hFbar.comp_hasFDerivAt (μ₀, p) hg
    have hF := (hasFDerivAt_fst (𝕜 := ℝ) (p := (μ₀, p))).sub hG
    have hlem := implicit_hasDerivAt (u := M.muLim) hF hcont rfl ?_ ?_
    · convert hlem using 1
      simp only [sub_apply, ContinuousLinearMap.coe_fst',
        smul_apply, add_apply,
        ContinuousLinearMap.coe_snd', smul_eq_mul]
      rw [Market.muLimDeriv, Market.DeltaLim, ← hμ₀, ← hw, ← hy₀, ← he, hh']
      have hμne : μ₀ ≠ 0 := hmu0.1.1.ne'
      have hωne : M.ω w ≠ 0 := hωpos.ne'
      have hden1 : 1 + p * M.d * (M.ω w * e) * deriv M.ω w / (μ₀ ^ 2 * M.ω w) ≠ 0 := by
        have : 0 ≤ p * M.d * (M.ω w * e) * deriv M.ω w / (μ₀ ^ 2 * M.ω w) := by positivity
        linarith
      have hden2 : 1 - e * (p * (deriv M.ω w * ((0 * μ₀ - M.d * 1) / μ₀ ^ 2)) * 1 +
          M.ω w * 0) ≠ 0 := by
        have : 0 ≤ e * p * deriv M.ω w * M.d / μ₀ ^ 2 := by positivity
        have e1 : e * (p * (deriv M.ω w * ((0 * μ₀ - M.d * 1) / μ₀ ^ 2)) * 1 + M.ω w * 0) =
            -(e * p * deriv M.ω w * M.d / μ₀ ^ 2) := by ring
        rw [e1]; linarith
      have hden3 : e * p * M.d * deriv M.ω w + μ₀ ^ 2 ≠ 0 := by
        have : 0 ≤ e * p * M.d * deriv M.ω w := by positivity
        have : 0 < μ₀ ^ 2 := by positivity
        linarith
      have key : (e * p * M.d * deriv M.ω w + μ₀ ^ 2) * (e * p * M.d * deriv M.ω w + μ₀ ^ 2)⁻¹
          = 1 := mul_inv_cancel₀ hden3
      field_simp
      linear_combination (-(M.ω w * e * μ₀ ^ 2)) * key
    · filter_upwards [hfixev] with q hq
      show (M.muLim q - ∫ b, M.f b (q * M.ω (M.d / M.muLim q)) ∂M.β) =
        (μ₀ - ∫ b, M.f b (p * M.ω (M.d / μ₀)) ∂M.β)
      have h1 : M.muLim q - ∫ b, M.f b (q * M.ω (M.d / M.muLim q)) ∂M.β = 0 := by
        have := hq.2; simp only [Φ] at this; linarith
      have h2 : μ₀ - ∫ b, M.f b (p * M.ω (M.d / μ₀)) ∂M.β = 0 := by
        have := hmu0.2; simp only [Φ] at this; linarith
      rw [h1, h2]
    · simp only [sub_apply, ContinuousLinearMap.coe_fst',
        smul_apply, add_apply,
        ContinuousLinearMap.coe_snd', smul_eq_mul]
      have : 0 ≤ e * p * deriv M.ω w * M.d / μ₀ ^ 2 := by positivity
      have e1 : e * ((μ₀, p).2 * (h' * (1 : ℝ)) + M.ω (M.d / (μ₀, p).1) * 0) =
          -(e * p * deriv M.ω w * M.d / μ₀ ^ 2) := by
        simp only [hh']; ring
      rw [e1]; linarith
