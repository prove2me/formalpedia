-- Prove2me | solution 1 for EthierKurtz.martingale_solution_has_semigroup_conditional_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T23:33:05.751773+00:00
-- url     : https://prove2.me/submissions/dc60775c-0a7b-4b1a-9b59-99aaae2e0318

import Mathlib
import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

namespace Pa99bfd3f

/-! ## Part 1: abstract semigroup uniqueness (EK Thm 4.4.1 core). -/

section semigroup
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

structure SG (T : ℝ → V →L[ℝ] V) : Prop where
  zero : T 0 = ContinuousLinearMap.id ℝ V
  add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)
  contr : ∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1
  cont : ∀ f : V, Tendsto (fun t : ℝ => T t f) (𝓝[>] (0 : ℝ)) (𝓝 f)

def IsGen (T : ℝ → V →L[ℝ] V) (h g : V) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (T t h - h)) (𝓝[>] (0 : ℝ)) (𝓝 g)

variable {T : ℝ → V →L[ℝ] V}

lemma SG.apply_le (hT : SG T) {t : ℝ} (ht : 0 ≤ t) (x : V) : ‖T t x‖ ≤ ‖x‖ := by
  calc ‖T t x‖ ≤ ‖T t‖ * ‖x‖ := (T t).le_opNorm x
    _ ≤ 1 * ‖x‖ := by gcongr; exact hT.contr t ht
    _ = ‖x‖ := one_mul _

lemma SG.add_apply (hT : SG T) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : V) :
    T (s + t) x = T s (T t x) := by
  rw [hT.add s t hs ht]; rfl

lemma SG.comm (hT : SG T) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : V) :
    T s (T t x) = T t (T s x) := by
  rw [← hT.add_apply hs ht, ← hT.add_apply ht hs, add_comm]

lemma SG.dist_le (hT : SG T) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (x : V) :
    ‖T w x - T v x‖ ≤ ‖T (w - v) x - x‖ := by
  have : T w x = T v (T (w - v) x) := by
    rw [← hT.add_apply hv (by linarith), show v + (w - v) = w by ring]
  rw [this, ← map_sub]
  exact hT.apply_le hv _

lemma SG.tendsto_zero (hT : SG T) (x : V) :
    Tendsto (fun δ : ℝ => ‖T δ x - x‖) (𝓝[>] 0) (𝓝 0) := by
  have := (hT.cont x).sub_const x
  simp only [sub_self] at this
  exact tendsto_norm_zero.comp this

lemma SG.continuousOn (hT : SG T) (x : V) : ContinuousOn (fun v => T v x) (Set.Ici 0) := by
  intro v0 hv0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.tendsto_nhdsWithin_nhds.1 (hT.tendsto_zero x) ε hε
  refine ⟨δ, hδ, fun {v} hv hd => ?_⟩
  simp only [Set.mem_Ici] at hv hv0
  have key : ∀ a b : ℝ, 0 ≤ a → a < b → b - a < δ → dist (T b x) (T a x) < ε := by
    intro a b ha hab hba
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (hT.dist_le ha hab.le x) ?_
    have h1 := hδ' (x := b - a) (Set.mem_Ioi.2 (by linarith))
      (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    simpa [Real.dist_eq] using h1
  rw [Real.dist_eq, abs_lt] at hd
  rcases lt_trichotomy v v0 with h | h | h
  · rw [dist_comm]; exact key v v0 hv h (by linarith)
  · subst h; simpa using hε
  · exact key v0 v hv0 h (by linarith)

lemma SG.isGen_apply (hT : SG T) {v : ℝ} (hv : 0 ≤ v) {h g : V} (hg : IsGen T h g) :
    IsGen T (T v h) (T v g) := by
  have := ((T v).continuous.tendsto g).comp hg
  refine this.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
  simp only [Function.comp_apply, map_smul, map_sub]
  rw [hT.comm hv (le_of_lt ht)]

lemma joint (φ : ℝ → V →L[ℝ] ℝ) (hφb : ∀ u, ‖φ u‖ ≤ 1)
    (hφc : ∀ k : V, Continuous (fun u => φ u k))
    {ι : Type*} {l : Filter ι} {y : ι → ℝ} {r : ℝ} (hy : Tendsto y l (𝓝 r))
    {a : ι → V} {a0 : V} (ha : Tendsto a l (𝓝 a0)) :
    Tendsto (fun i => φ (y i) (a i)) l (𝓝 (φ r a0)) := by
  have h1 : Tendsto (fun i => φ (y i) a0) l (𝓝 (φ r a0)) := ((hφc a0).tendsto r).comp hy
  have h3 : Tendsto (fun i => ‖a i - a0‖) l (𝓝 0) := by
    have := ha.sub_const a0
    simp only [sub_self] at this
    exact tendsto_norm_zero.comp this
  have h2 : Tendsto (fun i => φ (y i) (a i - a0)) l (𝓝 0) := by
    refine squeeze_zero_norm (fun i => ?_) h3
    calc ‖φ (y i) (a i - a0)‖ ≤ ‖φ (y i)‖ * ‖a i - a0‖ := (φ (y i)).le_opNorm _
      _ ≤ 1 * ‖a i - a0‖ := by gcongr; exact hφb _
      _ = ‖a i - a0‖ := one_mul _
  have := h2.add h1
  simp only [zero_add] at this
  refine this.congr (fun i => ?_)
  simp [map_sub]

theorem core (hT : SG T) (φ : ℝ → V →L[ℝ] ℝ) (hφb : ∀ u, ‖φ u‖ ≤ 1)
    (hφc : ∀ k : V, Continuous (fun u => φ u k))
    (hφm : ∀ h g : V, IsGen T h g → ∀ u, 0 ≤ u → φ u h - φ 0 h = ∫ w in (0:ℝ)..u, φ w g)
    {h g : V} (hg : IsGen T h g) {t : ℝ} (ht : 0 ≤ t) : φ t h = φ 0 (T t h) := by
  have hTc : ∀ x : V, ContinuousOn (fun r => T (t - r) x) (Set.Icc 0 t) := by
    intro x
    refine (hT.continuousOn x).comp (continuousOn_const.sub continuousOn_id) ?_
    intro r hr; simp only [Set.mem_Ici]; linarith [hr.2]
  have hcont : ContinuousOn (fun r => φ r (T (t - r) h)) (Set.Icc 0 t) := by
    intro r0 hr0
    exact joint φ hφb hφc (y := fun r => r) (a := fun r => T (t - r) h)
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) (hTc h r0 hr0)
  have hderiv : ∀ r ∈ Set.Ico 0 t,
      HasDerivWithinAt (fun r => φ r (T (t - r) h)) 0 (Set.Ici r) r := by
    intro r hr
    obtain ⟨hr0, hrt⟩ := hr
    have hIoi : Set.Ici r \ {r} = Set.Ioi r := by
      ext y
      simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
      constructor
      · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
      · intro h1; exact ⟨h1.le, h1.ne'⟩
    rw [hasDerivWithinAt_iff_tendsto_slope, hIoi]
    have hk : IsGen T (T (t - r) h) (T (t - r) g) := hT.isGen_apply (by linarith) hg
    have hG : Tendsto (slope (fun y => ∫ w in r..y, φ w (T (t - r) g)) r) (𝓝[>] r)
        (𝓝 (φ r (T (t - r) g))) := by
      have := ((hφc (T (t - r) g)).integral_hasStrictDerivAt r r).hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope] at this
      exact this.mono_left (nhdsWithin_mono _ (fun y hy => ne_of_gt hy))
    have hq : Tendsto (fun y => (y - r)⁻¹ • (T (y - r) h - h)) (𝓝[>] r) (𝓝 g) := by
      refine hg.comp ?_
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun y : ℝ => y - r) (𝓝 r) (𝓝 (r - r)) := tendsto_id.sub_const r
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun y hy => Set.mem_Ioi.2 (sub_pos.2 hy)
    have hev : ∀ᶠ y in 𝓝[>] r, y ∈ Set.Ioo r t := Ioo_mem_nhdsGT hrt
    have hTg : Tendsto (fun y => T (t - y) g) (𝓝[>] r) (𝓝 (T (t - r) g)) := by
      refine ((hT.continuousOn g) (t - r) (by simp only [Set.mem_Ici]; linarith)).tendsto.comp ?_
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((tendsto_const_nhds (x := t)).sub tendsto_id).mono_left nhdsWithin_le_nhds
      · filter_upwards [hev] with y hy
        simp only [Set.mem_Ici]; linarith [hy.2]
    have hdiff : Tendsto (fun y => T (t - y) ((y - r)⁻¹ • (T (y - r) h - h) - g)) (𝓝[>] r)
        (𝓝 0) := by
      have h3 : Tendsto (fun y => ‖(y - r)⁻¹ • (T (y - r) h - h) - g‖) (𝓝[>] r) (𝓝 0) := by
        have := hq.sub_const g
        simp only [sub_self] at this
        exact tendsto_norm_zero.comp this
      refine squeeze_zero_norm' ?_ h3
      filter_upwards [hev] with y hy
      exact hT.apply_le (by linarith [hy.2]) _
    have ha : Tendsto (fun y => T (t - y) ((y - r)⁻¹ • (T (y - r) h - h))) (𝓝[>] r)
        (𝓝 (T (t - r) g)) := by
      have := hdiff.add hTg
      simp only [zero_add] at this
      refine this.congr (fun y => ?_)
      simp [map_sub]
    have hJ := joint φ hφb hφc (y := fun y => y) (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) ha
    have hlim := hG.sub hJ
    rw [sub_self] at hlim
    refine hlim.congr' ?_
    filter_upwards [hev] with y hy
    obtain ⟨hry, hyt⟩ := hy
    have hd : y - r ≠ 0 := by linarith
    have hkeq : T (t - r) h = T (t - y) (T (y - r) h) := by
      rw [← hT.add_apply (by linarith) (by linarith), show t - y + (y - r) = t - r by ring]
    have hI : (∫ w in r..y, φ w (T (t - r) g)) = φ y (T (t - r) h) - φ r (T (t - r) h) := by
      have h1 := hφm _ _ hk y (by linarith)
      have h2 := hφm _ _ hk r hr0
      have hii : ∀ c : ℝ, IntervalIntegrable (fun w => φ w (T (t - r) g)) volume 0 c :=
        fun c => (hφc _).intervalIntegrable _ _
      rw [← intervalIntegral.integral_interval_sub_left (hii y) (hii r), ← h1, ← h2]
      ring
    simp only [slope, vsub_eq_sub, smul_eq_mul, intervalIntegral.integral_same, sub_zero]
    rw [hI, hkeq]
    simp only [map_smul, map_sub, smul_eq_mul]
    ring
  have := constant_of_has_deriv_right_zero hcont hderiv t ⟨ht, le_rfl⟩
  simp only [sub_self, sub_zero] at this
  rw [hT.zero] at this
  simpa using this

theorem core_all (hT : SG T) (φ : ℝ → V →L[ℝ] ℝ) (hφb : ∀ u, ‖φ u‖ ≤ 1)
    (hφc : ∀ k : V, Continuous (fun u => φ u k))
    (hφm : ∀ h g : V, IsGen T h g → ∀ u, 0 ≤ u → φ u h - φ 0 h = ∫ w in (0:ℝ)..u, φ w g)
    (D : Set V) (hD : Dense D) (hDg : ∀ h ∈ D, ∃ g, IsGen T h g)
    {t : ℝ} (ht : 0 ≤ t) (x : V) : φ t x = φ 0 (T t x) := by
  have hcl : IsClosed {x : V | φ t x = φ 0 (T t x)} :=
    isClosed_eq (φ t).continuous ((φ 0).continuous.comp (T t).continuous)
  have hsub : D ⊆ {x : V | φ t x = φ 0 (T t x)} := fun h hh => by
    obtain ⟨g, hg⟩ := hDg h hh
    exact core hT φ hφb hφc hφm hg ht
  exact (hcl.closure_subset_iff.2 hsub) (hD x)

end semigroup

/-! ## Part 2: application to the martingale problem. -/

section app
open EthierKurtz
variable {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]

lemma ev_le (f : UniformBoundedFunction E) (x : E) : |f x| ≤ ‖f‖ := by
  have := lp.norm_apply_le_norm (E := fun _ : E => ℝ) ENNReal.top_ne_zero f x
  simpa [Real.norm_eq_abs] using this

noncomputable def ind (B : Set E) : UniformBoundedFunction E :=
  ⟨B.indicator 1, memℓp_infty_iff.2 ⟨1, by
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ B <;> simp [hx]⟩⟩

lemma ind_apply (B : Set E) (x : E) : (ind B : E → ℝ) x = B.indicator 1 x := rfl

lemma integrable_bdd {P : Measure Ω} [IsFiniteMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z)
    (C : ℝ) (h : ∀ ω, |Z ω| ≤ C) : Integrable Z P :=
  Integrable.of_bound hZ.aestronglyMeasurable C (ae_of_all _ fun ω => by
    simpa [Real.norm_eq_abs] using h ω)

lemma meas_X (X : ℝ≥0 → Ω → E) (hj : Measurable fun z : ℝ≥0 × Ω => X z.1 z.2) (r : ℝ≥0) :
    Measurable (X r) :=
  hj.comp (measurable_const.prodMk measurable_id)

lemma past_le (X : ℝ≥0 → Ω → E) (hj : Measurable fun z : ℝ≥0 × Ω => X z.1 z.2) (s : ℝ≥0) :
    processPast X s ≤ ‹MeasurableSpace Ω› :=
  iSup_le fun i => (meas_X X hj i.val).comap_le

abbrev piS (X : ℝ≥0 → Ω → E) (s : ℝ≥0) : Set (Set Ω) :=
  piiUnionInter (fun i : Set.Iic s =>
    {S | MeasurableSet[MeasurableSpace.comap (X i.val) ‹MeasurableSpace E›] S}) Set.univ

lemma past_gen (X : ℝ≥0 → Ω → E) (s : ℝ≥0) :
    processPast X s = MeasurableSpace.generateFrom (piS X s) := by
  have := generateFrom_piiUnionInter_measurableSet
    (fun i : Set.Iic s => MeasurableSpace.comap (X i.val) ‹MeasurableSpace E›) Set.univ
  rw [this, iSup_univ]

lemma piS_isPi (X : ℝ≥0 → Ω → E) (s : ℝ≥0) : IsPiSystem (piS X s) :=
  isPiSystem_piiUnionInter _ (fun i : Set.Iic s =>
    @MeasurableSpace.isPiSystem_measurableSet Ω (MeasurableSpace.comap (X i.val) _)) _

lemma pi_prod (X : ℝ≥0 → Ω → E) (s : ℝ≥0) {U : Set Ω} (hU : U ∈ piS X s) :
    ∃ (n : ℕ) (r : Fin n → ℝ≥0) (h : Fin n → UniformBoundedFunction E),
      (∀ i, r i ≤ s) ∧ (∀ i, Measurable (h i : E → ℝ)) ∧
      ∀ ω, ∏ i, h i (X (r i) ω) = U.indicator 1 ω := by
  obtain ⟨t, -, f, hf, rfl⟩ := hU
  have hB : ∀ x ∈ t, ∃ B : Set E, MeasurableSet B ∧ X x.val ⁻¹' B = f x :=
    fun x hx => MeasurableSpace.measurableSet_comap.1 (hf x hx)
  choose! B hBm hBe using hB
  let e := t.equivFin
  refine ⟨t.card, fun i => (e.symm i).val.val, fun i => ind (B (e.symm i).val),
    fun i => (e.symm i).val.2, fun i => ?_, fun ω => ?_⟩
  · exact measurable_one.indicator (hBm _ (e.symm i).2)
  · rw [Fintype.prod_equiv e.symm (fun i => (ind (B (e.symm i).val) : E → ℝ)
      (X (e.symm i).val.val ω)) (fun x : t => (ind (B x.val) : E → ℝ) (X x.val.val ω))
      (fun _ => rfl)]
    rw [Finset.prod_coe_sort t (fun x => (ind (B x) : E → ℝ) (X x.val ω))]
    by_cases hω : ω ∈ ⋂ x ∈ t, f x
    · rw [Set.indicator_of_mem hω]
      refine Finset.prod_eq_one fun x hx => ?_
      have h1 : ω ∈ f x := Set.mem_iInter₂.1 hω x hx
      rw [← hBe x hx] at h1
      simp [ind_apply, Set.indicator_of_mem (show X x.val ω ∈ B x from h1)]
    · rw [Set.indicator_of_notMem hω]
      simp only [Set.mem_iInter, not_forall] at hω
      obtain ⟨x, hx, hωx⟩ := hω
      refine Finset.prod_eq_zero hx ?_
      rw [← hBe x hx] at hωx
      simp [ind_apply, Set.indicator_of_notMem (show X x.val ω ∉ B x from hωx)]

lemma dynkin {P : Measure Ω} {Gs : Set (Set Ω)}
    (hm : MeasurableSpace.generateFrom Gs ≤ ‹MeasurableSpace Ω›) (hpi : IsPiSystem Gs)
    {Z : Ω → ℝ} (hZ : Integrable Z P) (huniv : ∫ ω, Z ω ∂P = 0)
    (hGs : ∀ U ∈ Gs, ∫ ω in U, Z ω ∂P = 0) :
    ∀ U, MeasurableSet[MeasurableSpace.generateFrom Gs] U → ∫ ω in U, Z ω ∂P = 0 := by
  intro U hU
  induction U, hU using MeasurableSpace.induction_on_inter rfl hpi with
  | empty => simp
  | basic t ht => exact hGs t ht
  | compl t htm ih => rw [setIntegral_compl (hm _ htm) hZ, ih, huniv, sub_zero]
  | iUnion f hd hfm ih =>
    rw [integral_iUnion (fun i => hm _ (hfm i)) hd hZ.integrableOn]
    simp [ih]

lemma meas_time (X : ℝ≥0 → Ω → E) (hj : Measurable fun z : ℝ≥0 × Ω => X z.1 z.2)
    {g : E → ℝ} (hg : Measurable g) (a b : ℝ) :
    Measurable fun ω => ∫ u in a..b, g (X u.toNNReal ω) := by
  have hF : StronglyMeasurable (fun p : ℝ × Ω => g (X p.1.toNNReal p.2)) :=
    (hg.comp (hj.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      measurable_snd))).stronglyMeasurable
  show Measurable fun ω => (∫ u in Set.Ioc a b, g (X u.toNNReal ω)) -
    ∫ u in Set.Ioc b a, g (X u.toNNReal ω)
  exact (hF.integral_prod_left' (μ := volume.restrict (Set.Ioc a b))).measurable.sub
    (hF.integral_prod_left' (μ := volume.restrict (Set.Ioc b a))).measurable

lemma time_bound (X : ℝ≥0 → Ω → E) (g : UniformBoundedFunction E) (a b : ℝ) (ω : Ω) :
    |∫ u in a..b, g (X u.toNNReal ω)| ≤ ‖g‖ * |b - a| := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun u => g (X u.toNNReal ω)) (C := ‖g‖) (fun u _ => by
      simpa [Real.norm_eq_abs] using ev_le g (X u.toNNReal ω))
  simpa [Real.norm_eq_abs] using this

theorem mart_past (A : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (μ : Measure E) (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hX : SolvesMartingaleProblem A μ P X) {f g : UniformBoundedFunction E}
    (hfg : (f, g) ∈ A) (hf : Measurable (f : E → ℝ)) (hg : Measurable (g : E → ℝ))
    {s t : ℝ≥0} (hst : s ≤ t) {U : Set Ω} (hU : MeasurableSet[processPast X s] U) :
    ∫ ω in U, (f (X t ω) - f (X s ω) - ∫ u in (s : ℝ)..(t : ℝ), g (X u.toNNReal ω)) ∂P
      = 0 := by
  have hj := hX.1
  have hZm : Measurable fun ω => f (X t ω) - f (X s ω) -
      ∫ u in (s : ℝ)..(t : ℝ), g (X u.toNNReal ω) :=
    ((hf.comp (meas_X X hj t)).sub (hf.comp (meas_X X hj s))).sub (meas_time X hj hg _ _)
  have hZ : Integrable (fun ω => f (X t ω) - f (X s ω) -
      ∫ u in (s : ℝ)..(t : ℝ), g (X u.toNNReal ω)) P := by
    refine integrable_bdd hZm (‖f‖ + ‖f‖ + ‖g‖ * |(t : ℝ) - s|) fun ω => ?_
    have h1 := ev_le f (X t ω)
    have h2 := ev_le f (X s ω)
    have h3 := time_bound X g s t ω
    calc _ ≤ |f (X t ω) - f (X s ω)| + |∫ u in (s : ℝ)..(t : ℝ), g (X u.toNNReal ω)| :=
          abs_sub _ _
      _ ≤ |f (X t ω)| + |f (X s ω)| + _ := by gcongr; exact abs_sub _ _
      _ ≤ _ := by gcongr
  refine dynkin ((past_gen X s) ▸ past_le X hj s) (piS_isPi X s) hZ ?_ ?_ U ((past_gen X s) ▸ hU)
  · have := hX.2.2 (f, g) hfg s t hst 0 (fun i => i.elim0) (fun i => i.elim0)
      (fun i => i.elim0) (fun i => i.elim0)
    simpa using this
  · intro V hV
    obtain ⟨n, r, h, hr, hm, hprod⟩ := pi_prod X s hV
    have := hX.2.2 (f, g) hfg s t hst n r hr h hm
    simp only [hprod] at this
    have hVm : MeasurableSet V :=
      past_le X hj s _ ((past_gen X s) ▸ MeasurableSpace.measurableSet_generateFrom hV)
    rw [← integral_indicator hVm, ← this]
    congr 1
    funext ω
    by_cases hω : ω ∈ V <;> simp [hω]

lemma finite_uIoc (a b : ℝ) : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) :=
  isFiniteMeasure_restrict.2 (show volume (Set.Ioc (min a b) (max a b)) ≠ ∞ from
    measure_Ioc_lt_top.ne)

lemma Lmeas (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hAmeas : ∀ fg ∈ A, Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    (hsub : A' ≤ A) (L : Submodule ℝ (UniformBoundedFunction E))
    (hL : closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set (UniformBoundedFunction E)))
    (k : L) : Measurable (k.val : E → ℝ) := by
  have hk : k.val ∈ closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
      fg.1) '' (A' : Set _)) := by rw [hL]; exact k.2
  obtain ⟨b, hb, hlim⟩ := mem_closure_iff_seq_limit.1 hk
  have hbm : ∀ n, Measurable (b n : E → ℝ) := fun n => by
    obtain ⟨p, hp, hpe⟩ := hb n
    rw [← hpe]; exact (hAmeas p (hsub hp)).1
  refine measurable_of_tendsto_metrizable hbm (tendsto_pi_nhds.2 fun x => ?_)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_iff_norm_sub_tendsto_zero.1 hlim)
  have := ev_le (b n - k.val) x
  simpa [Real.norm_eq_abs] using this

noncomputable def phi (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hj : Measurable fun z : ℝ≥0 × Ω => X z.1 z.2) (U : Set Ω) (s : ℝ≥0)
    (L : Submodule ℝ (UniformBoundedFunction E)) (hLm : ∀ k : L, Measurable (k.val : E → ℝ))
    (u : ℝ) : L →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun k => ∫ ω in U, (k.val : E → ℝ) (X (s + u.toNNReal) ω) ∂P
      map_add' := fun k k' => by
        simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply]
        exact integral_add
          (integrable_bdd ((hLm k).comp (meas_X X hj _)) _ fun ω => ev_le _ _)
          (integrable_bdd ((hLm k').comp (meas_X X hj _)) _ fun ω => ev_le _ _)
      map_smul' := fun c k => by
        simp only [Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        exact integral_const_mul c _ }
    1 (fun k => by
      have h1 : (P.restrict U).real Set.univ ≤ 1 := by
        show ((P.restrict U) Set.univ).toReal ≤ 1
        refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
        rw [Measure.restrict_apply_univ, ENNReal.ofReal_one]; exact prob_le_one
      calc ‖∫ ω in U, (k.val : E → ℝ) (X (s + u.toNNReal) ω) ∂P‖
          ≤ ‖k.val‖ * (P.restrict U).real Set.univ :=
            norm_integral_le_of_norm_le_const (ae_of_all _ fun ω => by
              simpa [Real.norm_eq_abs] using ev_le k.val _)
        _ ≤ ‖k.val‖ * 1 := by gcongr
        _ = 1 * ‖k‖ := by rw [mul_one, one_mul]; rfl)

lemma phi_apply (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hj : Measurable fun z : ℝ≥0 × Ω => X z.1 z.2) (U : Set Ω) (s : ℝ≥0)
    (L : Submodule ℝ (UniformBoundedFunction E)) (hLm : ∀ k : L, Measurable (k.val : E → ℝ))
    (u : ℝ) (k : L) :
    phi P X hj U s L hLm u k = ∫ ω in U, (k.val : E → ℝ) (X (s + u.toNNReal) ω) ∂P := rfl

lemma phi_ii (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hj : Measurable fun z : ℝ≥0 × Ω => X z.1 z.2) (U : Set Ω) (s : ℝ≥0)
    (L : Submodule ℝ (UniformBoundedFunction E)) (hLm : ∀ k : L, Measurable (k.val : E → ℝ))
    (k : L) (a b : ℝ) : IntervalIntegrable (fun w => phi P X hj U s L hLm w k) volume a b := by
  have hF : StronglyMeasurable (fun p : ℝ × Ω => (k.val : E → ℝ) (X (s + p.1.toNNReal) p.2)) :=
    ((hLm k).comp (hj.comp ((measurable_const.add (measurable_real_toNNReal.comp
      measurable_fst)).prodMk measurable_snd))).stronglyMeasurable
  have hm : Measurable (fun w => phi P X hj U s L hLm w k) :=
    (hF.integral_prod_right' (ν := P.restrict U)).measurable
  have := finite_uIoc a b
  rw [intervalIntegrable_iff]
  refine integrable_bdd hm ‖k‖ fun w => ?_
  have := (phi P X hj U s L hLm w).le_opNorm k
  have h2 : ‖phi P X hj U s L hLm w‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  rw [← Real.norm_eq_abs]
  calc _ ≤ _ := this
    _ ≤ 1 * ‖k‖ := by gcongr
    _ = ‖k‖ := one_mul _

lemma phi_norm (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hj : Measurable fun z : ℝ≥0 × Ω => X z.1 z.2) (U : Set Ω) (s : ℝ≥0)
    (L : Submodule ℝ (UniformBoundedFunction E)) (hLm : ∀ k : L, Measurable (k.val : E → ℝ))
    (u : ℝ) : ‖phi P X hj U s L hLm u‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

lemma fubini_shift (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hj : Measurable fun z : ℝ≥0 × Ω => X z.1 z.2) {g : E → ℝ} (hg : Measurable g)
    (C : ℝ) (hC : ∀ x, |g x| ≤ C) (U : Set Ω) (s : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) :
    ∫ ω in U, (∫ v in (s : ℝ)..((s + u.toNNReal : ℝ≥0) : ℝ), g (X v.toNNReal ω)) ∂P =
      ∫ w in (0 : ℝ)..u, ∫ ω in U, g (X (s + w.toNNReal) ω) ∂P := by
  have e1 : ∀ ω, ∫ v in (s : ℝ)..((s + u.toNNReal : ℝ≥0) : ℝ), g (X v.toNNReal ω) =
      ∫ w in (0 : ℝ)..u, g (X (s + w.toNNReal) ω) := by
    intro ω
    rw [NNReal.coe_add, Real.coe_toNNReal _ hu]
    have := intervalIntegral.integral_comp_add_left (fun v => g (X v.toNNReal ω)) (s : ℝ)
      (a := 0) (b := u)
    rw [add_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun w hw => ?_
    have hw0 : 0 ≤ w := by rw [Set.uIcc_of_le hu] at hw; exact hw.1
    have key : ((s : ℝ) + w).toNNReal = s + w.toNNReal := by
      rw [Real.toNNReal_add (NNReal.coe_nonneg s) hw0, Real.toNNReal_coe]
    simp only [key]
  simp_rw [e1]
  have := finite_uIoc 0 u
  refine (intervalIntegral_integral_swap ?_).symm
  exact integrable_bdd (hg.comp (hj.comp ((measurable_const.add (measurable_real_toNNReal.comp
      measurable_fst)).prodMk measurable_snd))) C fun p => hC _

theorem mart_phi (A : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (μ : Measure E) (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → E)
    (hX : SolvesMartingaleProblem A μ P X) (U : Set Ω) (s : ℝ≥0)
    (hU : MeasurableSet[processPast X s] U)
    (L : Submodule ℝ (UniformBoundedFunction E)) (hLm : ∀ k : L, Measurable (k.val : E → ℝ))
    (h g : L) (hfg : (h.val, g.val) ∈ A) {u : ℝ} (hu : 0 ≤ u) :
    phi P X hX.1 U s L hLm u h - phi P X hX.1 U s L hLm 0 h =
      ∫ w in (0 : ℝ)..u, phi P X hX.1 U s L hLm w g := by
  have hj := hX.1
  have m := mart_past A μ P X hX hfg (hLm h) (hLm g) (t := s + u.toNNReal) le_self_add hU
  have i1 : Integrable (fun ω => (h.val : E → ℝ) (X (s + u.toNNReal) ω)) (P.restrict U) :=
    integrable_bdd ((hLm h).comp (meas_X X hj _)) _ fun ω => ev_le _ _
  have i2 : Integrable (fun ω => (h.val : E → ℝ) (X s ω)) (P.restrict U) :=
    integrable_bdd ((hLm h).comp (meas_X X hj _)) _ fun ω => ev_le _ _
  have i3 : Integrable (fun ω => ∫ v in (s : ℝ)..((s + u.toNNReal : ℝ≥0) : ℝ),
      (g.val : E → ℝ) (X v.toNNReal ω)) (P.restrict U) :=
    integrable_bdd (meas_time X hj (hLm g) _ _) _ fun ω => time_bound X g.val _ _ ω
  have e1 : ∫ ω in U, ((h.val : E → ℝ) (X (s + u.toNNReal) ω) - (h.val : E → ℝ) (X s ω) -
      ∫ v in (s : ℝ)..((s + u.toNNReal : ℝ≥0) : ℝ), (g.val : E → ℝ) (X v.toNNReal ω)) ∂P =
      (∫ ω in U, (h.val : E → ℝ) (X (s + u.toNNReal) ω) ∂P -
        ∫ ω in U, (h.val : E → ℝ) (X s ω) ∂P) -
      ∫ ω in U, (∫ v in (s : ℝ)..((s + u.toNNReal : ℝ≥0) : ℝ),
        (g.val : E → ℝ) (X v.toNNReal ω)) ∂P := by
    rw [← integral_sub i1 i2]; exact integral_sub (i1.sub i2) i3
  rw [e1, fubini_shift P X hj (hLm g) ‖g.val‖ (fun x => ev_le _ x) U s hu] at m
  rw [phi_apply, phi_apply, Real.toNNReal_zero, add_zero]
  simp only [phi_apply]
  linarith

end app

end Pa99bfd3f

open Pa99bfd3f

set_option maxHeartbeats 1000000 in
open EthierKurtz MeasureTheory Filter TopologicalSpace Topology NNReal ENNReal in
theorem solution
    {E Ω Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MetricSpace E] [BorelSpace E]
    [SeparableSpace E]
    (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hAmeas : ∀ fg ∈ A, Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    (hsub : A' ≤ A)
    (hdiss : ∀ fg ∈ A, ∀ a : ℝ, 0 < a →
      a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖)
    (L : Submodule ℝ (UniformBoundedFunction E))
    (hrange : ∃ a : ℝ, 0 < a ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        a • fg.1 - fg.2) '' (A' : Set _)) = (L : Set _) ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set (UniformBoundedFunction E)))
    (hsep : ∀ (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ →
      IsProbabilityMeasure ν₂ →
      (∀ f : L, (∫ x, (f.val : E → ℝ) x ∂ν₁) =
        ∫ x, (f.val : E → ℝ) x ∂ν₂) → ν₁ = ν₂)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → E)
    (hX : SolvesMartingaleProblem A μ P X)

    (T : ℝ → L →L[ℝ] L)
    (hT : (T 0 = ContinuousLinearMap.id ℝ L ∧
       (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)) ∧
       (∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1) ∧
       (∀ f : L, Tendsto (fun t : ℝ => T t f) (𝓝[>] (0 : ℝ)) (𝓝 f))))
    (hTgen : (∀ f g : L,
        Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[>] (0 : ℝ)) (𝓝 g) ↔
          (f.val, g.val) ∈ closure (A' : Set _))) :
    ∀ (s t : ℝ≥0) (f : L),
      P[fun ω => (f.val : E → ℝ) (X (s + t) ω) | processPast X s] =ᵐ[P]
        fun ω => ((T (t : ℝ) f).val : E → ℝ) (X s ω) := by
  intro s t f
  obtain ⟨a, -, hr1, hr2⟩ := hrange
  have hLm : ∀ k : L, Measurable (k.val : E → ℝ) := Lmeas A A' hAmeas hsub L hr2
  have hj := hX.1
  have hSG : SG T := ⟨hT.1, hT.2.1, hT.2.2.1, hT.2.2.2⟩
  have hfst : ∀ p ∈ A', p.1 ∈ L := fun p hp => by
    rw [← SetLike.mem_coe, ← hr2]; exact subset_closure ⟨p, hp, rfl⟩
  have hsnd : ∀ p ∈ A', p.2 ∈ L := fun p hp => by
    have h1 : a • p.1 - p.2 ∈ L := by
      rw [← SetLike.mem_coe, ← hr1]; exact subset_closure ⟨p, hp, rfl⟩
    have h2 : a • p.1 ∈ L := L.smul_mem a (hfst p hp)
    have := L.sub_mem h2 h1
    rwa [_root_.sub_sub_cancel] at this
  have hdense : ∀ k : L, ∀ ε > 0, ∃ k' : L, dist k k' < ε ∧ ∃ g : L, (k'.val, g.val) ∈ A' := by
    intro k ε hε
    have hk : k.val ∈ closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) := by rw [hr2]; exact k.2
    obtain ⟨b, ⟨p, hp, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 hk ε hε
    exact ⟨⟨p.1, hfst p hp⟩, hb, ⟨p.2, hsnd p hp⟩, hp⟩
  have key : ∀ U, MeasurableSet[processPast X s] U →
      ∫ ω in U, (f.val : E → ℝ) (X (s + t) ω) ∂P =
        ∫ ω in U, ((T (t : ℝ) f).val : E → ℝ) (X s ω) ∂P := by
    intro U hU
    set φ : ℝ → L →L[ℝ] ℝ := phi P X hj U s L hLm with hφdef
    have hφA : ∀ h g : L, (h.val, g.val) ∈ A' → ∀ u, 0 ≤ u →
        φ u h - φ 0 h = ∫ w in (0 : ℝ)..u, φ w g :=
      fun h g hhg u hu => mart_phi A μ P X hX U s hU L hLm h g (hsub hhg) hu
    have hφcl : ∀ h g : L, (h.val, g.val) ∈ closure (A' : Set _) → ∀ u, 0 ≤ u →
        φ u h - φ 0 h = ∫ w in (0 : ℝ)..u, φ w g := by
      intro h g hcl u hu
      obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
      let h' : ℕ → L := fun n => ⟨(q n).1, hfst _ (hq n)⟩
      let g' : ℕ → L := fun n => ⟨(q n).2, hsnd _ (hq n)⟩
      have hh : Tendsto h' atTop (𝓝 h) := by
        rw [tendsto_subtype_rng]; exact (continuous_fst.tendsto _).comp hlim
      have hg : Tendsto g' atTop (𝓝 g) := by
        rw [tendsto_subtype_rng]; exact (continuous_snd.tendsto _).comp hlim
      have L1 : Tendsto (fun n => φ u (h' n) - φ 0 (h' n)) atTop (𝓝 (φ u h - φ 0 h)) :=
        (((φ u).continuous.tendsto _).comp hh).sub (((φ 0).continuous.tendsto _).comp hh)
      have L2 : Tendsto (fun n => ∫ w in (0 : ℝ)..u, φ w (g' n)) atTop
          (𝓝 (∫ w in (0 : ℝ)..u, φ w g)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        have hn : Tendsto (fun n => ‖g' n - g‖) atTop (𝓝 0) :=
          tendsto_iff_norm_sub_tendsto_zero.1 hg
        have hn' : Tendsto (fun n => ‖g' n - g‖ * |u - 0|) atTop (𝓝 0) := by
          have := hn.mul_const |u - 0|; rwa [zero_mul] at this
        refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hn'
        rw [← intervalIntegral.integral_sub (phi_ii P X hj U s L hLm _ _ _)
          (phi_ii P X hj U s L hLm _ _ _)]
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun w _ => ?_
        rw [← map_sub]
        calc ‖φ w (g' n - g)‖ ≤ ‖φ w‖ * ‖g' n - g‖ := (φ w).le_opNorm _
          _ ≤ 1 * ‖g' n - g‖ := by gcongr; exact phi_norm P X hj U s L hLm w
          _ = ‖g' n - g‖ := one_mul _
      have heq : ∀ n, φ u (h' n) - φ 0 (h' n) = ∫ w in (0 : ℝ)..u, φ w (g' n) :=
        fun n => hφA _ _ (hq n) u hu
      exact tendsto_nhds_unique (L1.congr heq) L2
    have hφm : ∀ h g : L, IsGen T h g → ∀ u, 0 ≤ u →
        φ u h - φ 0 h = ∫ w in (0 : ℝ)..u, φ w g :=
      fun h g hg => hφcl h g ((hTgen h g).1 hg)
    have hc0 : ∀ k g : L, (k.val, g.val) ∈ A' → Continuous fun u => φ u k := by
      intro k g hkg
      have e : (fun u => φ u k) = fun u => φ 0 k + ∫ w in (0 : ℝ)..(max u 0), φ w g := by
        funext u
        rcases le_total 0 u with hu | hu
        · rw [max_eq_left hu, ← hφA k g hkg u hu]; ring
        · rw [max_eq_right hu, intervalIntegral.integral_same, add_zero]
          simp only [hφdef, phi_apply, Real.toNNReal_of_nonpos hu, Real.toNNReal_zero]
      rw [e]
      exact continuous_const.add ((intervalIntegral.continuous_primitive
        (fun a b => phi_ii P X hj U s L hLm g a b) 0).comp (continuous_id.max continuous_const))
    have hφc : ∀ k : L, Continuous fun u => φ u k := by
      intro k
      refine continuous_of_uniform_approx_of_continuous fun V hV => ?_
      obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.1 hV
      obtain ⟨k', hk', g, hg⟩ := hdense k ε hε
      refine ⟨fun u => φ u k', hc0 k' g hg, fun u => hεV ?_⟩
      rw [Real.dist_eq, ← map_sub]
      calc |φ u (k - k')| = ‖φ u (k - k')‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖φ u‖ * ‖k - k'‖ := (φ u).le_opNorm _
        _ ≤ 1 * ‖k - k'‖ := by gcongr; exact phi_norm P X hj U s L hLm u
        _ < ε := by rw [one_mul, ← dist_eq_norm]; exact hk'
    have hD : Dense {k : L | ∃ g, IsGen T k g} := by
      rw [Metric.dense_iff]
      intro k r hr
      obtain ⟨k', hk', g, hg⟩ := hdense k r hr
      exact ⟨k', by rw [Metric.mem_ball, dist_comm]; exact hk', g,
        (hTgen k' g).2 (subset_closure hg)⟩
    have := core_all hSG φ (phi_norm P X hj U s L hLm) hφc hφm _ hD (fun h hh => hh)
      (NNReal.coe_nonneg t) f
    simp only [hφdef, phi_apply, Real.toNNReal_coe, Real.toNNReal_zero, add_zero] at this
    exact this
  have hm := past_le X hj s
  have hfi : Integrable (fun ω => (f.val : E → ℝ) (X (s + t) ω)) P :=
    integrable_bdd ((hLm f).comp (meas_X X hj _)) _ fun ω => ev_le _ _
  have hXs : @Measurable Ω E (processPast X s) _ (X s) :=
    measurable_iff_comap_le.2 (le_iSup (fun r : Set.Iic s =>
      MeasurableSpace.comap (X r.val) ‹MeasurableSpace E›) ⟨s, Set.mem_Iic.2 le_rfl⟩)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hfi ?_ ?_ ?_).symm
  · intro U _ _
    exact (integrable_bdd ((hLm (T t f)).comp (meas_X X hj s)) _ fun ω => ev_le _ _).integrableOn
  · intro U hU _
    exact (key U hU).symm
  · exact ((hLm (T t f)).comp hXs).stronglyMeasurable.aestronglyMeasurable
