-- Prove2me | solution 1 for BertsekasShreve.SemicontSelection.prop7_31_semicontinuous_integral
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:57:59.679987+00:00
-- url     : https://prove2.me/submissions/bf130674-9067-4959-809f-c18442e603c3

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect



namespace BertsekasShreve.SemicontSelection

section P730


open MeasureTheory TopologicalSpace Filter Topology

theorem p730_core {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [SeparableSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (q : X → ProbabilityMeasure Y) (hq : Continuous q) (f : BoundedContinuousFunction (X × Y) ℝ) :
    Continuous (fun x => ∫ y, f (x, y) ∂(q x : Measure Y)) := by
  rw [continuous_iff_seqContinuous]
  intro xs x hxs
  -- slice functions
  let sl : X → BoundedContinuousFunction Y ℝ := fun z => f.compContinuous ⟨fun y => (z, y), by fun_prop⟩
  have hsl : ∀ z y, sl z y = f (z, y) := fun z y => rfl
  have hqs : Tendsto (fun n => q (xs n)) atTop (𝓝 (q x)) := (hq.tendsto x).comp hxs
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hqs
  -- compact tails
  let S : ℕ → Set X := fun N => insert x (Set.range fun m => xs (N + m))
  have hS : ∀ N, IsCompact (S N) := fun N =>
    Tendsto.isCompact_insert_range (hxs.comp (tendsto_atTop_atTop_of_monotone
      (fun a b h => by omega) (fun b => ⟨b, by omega⟩)))
  let φ : Y → X → ℝ := fun y z => |f (z, y) - f (x, y)|
  have hφc : Continuous ↿φ := by
    show Continuous (fun p : Y × X => |f (p.2, p.1) - f (x, p.1)|)
    fun_prop
  have hφb : ∀ y z, φ y z ≤ 2 * ‖f‖ := by
    intro y z
    have := f.dist_le_two_norm (z, y) (x, y)
    rwa [Real.dist_eq] at this
  have hφ0 : ∀ y z, 0 ≤ φ y z := fun y z => abs_nonneg _
  let hN : ℕ → Y → ℝ := fun N y => sSup (φ y '' S N)
  have hNc : ∀ N, Continuous (hN N) := fun N => (hS N).continuous_sSup hφc
  have hNne : ∀ N, (S N).Nonempty := fun N => ⟨x, Set.mem_insert _ _⟩
  have hNbdd : ∀ N y, BddAbove (φ y '' S N) := fun N y =>
    ⟨2 * ‖f‖, by rintro _ ⟨z, -, rfl⟩; exact hφb y z⟩
  have hNle : ∀ N y, hN N y ≤ 2 * ‖f‖ := fun N y =>
    csSup_le ((hNne N).image _) (by rintro _ ⟨z, -, rfl⟩; exact hφb y z)
  have hNge : ∀ N y z, z ∈ S N → φ y z ≤ hN N y := fun N y z hz =>
    le_csSup (hNbdd N y) ⟨z, hz, rfl⟩
  have hN0 : ∀ N y, 0 ≤ hN N y := fun N y => le_trans (hφ0 y x) (hNge N y x (Set.mem_insert _ _))
  let H : ℕ → BoundedContinuousFunction Y ℝ := fun N => BoundedContinuousFunction.ofNormedAddCommGroup (hN N) (hNc N)
    (2 * ‖f‖) (fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hN0 N y)]; exact hNle N y)
  have hH : ∀ N y, H N y = hN N y := fun N y => rfl
  -- pointwise convergence of hN to 0
  have hNlim : ∀ y, Tendsto (fun N => hN N y) atTop (𝓝 0) := by
    intro y
    have hc : Tendsto (fun n => f (xs n, y)) atTop (𝓝 (f (x, y))) :=
      ((f.continuous.comp (Continuous.prodMk_left y)).tendsto x).comp hxs
    rw [Metric.tendsto_atTop] at hc ⊢
    intro ε hε
    obtain ⟨N0, hN0'⟩ := hc (ε / 2) (by linarith)
    refine ⟨N0, fun N hNN => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hN0 N y)]
    have : hN N y ≤ ε / 2 := by
      apply csSup_le ((hNne N).image _)
      rintro _ ⟨z, hz, rfl⟩
      rcases hz with rfl | ⟨m, rfl⟩
      · simp [φ]; linarith
      · have := hN0' (N + m) (by omega)
        rw [Real.dist_eq] at this
        exact this.le
    linarith
  -- integral of hN against q x tends to 0
  have hint : Tendsto (fun N => ∫ y, hN N y ∂(q x : Measure Y)) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := (q x : Measure Y)) (fun _ => 2 * ‖f‖)
      (fun N => (hNc N).aestronglyMeasurable) (integrable_const _)
      (fun N => Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hN0 N y)]; exact hNle N y))
      (Filter.Eventually.of_forall hNlim)
    simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hNε⟩ := (Metric.tendsto_atTop.mp hint) (ε / 3) (by linarith)
  have hNε' := hNε N le_rfl
  rw [Real.dist_eq, sub_zero] at hNε'
  obtain ⟨M1, hM1⟩ := (Metric.tendsto_atTop.mp (hqs (H N))) (ε / 3) (by linarith)
  obtain ⟨M2, hM2⟩ := (Metric.tendsto_atTop.mp (hqs (sl x))) (ε / 3) (by linarith)
  refine ⟨max N (max M1 M2), fun m hm => ?_⟩
  have hmN : N ≤ m := le_trans (le_max_left _ _) hm
  have h1 := hM1 m (by omega)
  have h2 := hM2 m (by omega)
  simp only [hH, hsl] at h1 h2
  rw [Real.dist_eq] at h1 h2 ⊢
  -- bound the slice difference
  have hdiff : |∫ y, f (xs m, y) ∂(q (xs m) : Measure Y) - ∫ y, f (x, y) ∂(q (xs m) : Measure Y)|
      ≤ ∫ y, hN N y ∂(q (xs m) : Measure Y) := by
    have hsub := integral_sub ((sl (xs m)).integrable (q (xs m) : Measure Y)) ((sl x).integrable (q (xs m) : Measure Y))
    simp only [hsl] at hsub
    rw [← hsub]
    refine le_trans (abs_integral_le_integral_abs) (integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun y => abs_nonneg _)) ((H N).integrable _)
      (Filter.Eventually.of_forall (fun y => ?_)))
    have hm' : xs m ∈ S N := Set.mem_insert_of_mem _ ⟨m - N, by show xs (N + (m - N)) = xs m; congr 1; omega⟩
    exact hNge N y (xs m) hm'
  have h3 := abs_lt.mp h1
  have h4 := abs_lt.mp h2
  have h5 := abs_le.mp hdiff
  have h6 := abs_lt.mp hNε'
  show |∫ y, f (xs m, y) ∂(q (xs m) : Measure Y) - ∫ y, f (x, y) ∂(q x : Measure Y)| < ε
  rw [abs_lt]
  constructor <;> linarith [h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

end P730

section L714


open TopologicalSpace Filter Topology

/-- backward direction: monotone limit of continuous functions is lsc and bounded below -/
theorem l714_back {X : Type*} [TopologicalSpace X] (f : X → EReal)
    (g : ℕ → BoundedContinuousFunction X ℝ) (hmono : ∀ n x, g n x ≤ g (n + 1) x)
    (hlim : ∀ x, Tendsto (fun n => ((g n x : ℝ) : EReal)) atTop (𝓝 (f x))) :
    LowerSemicontinuous f ∧ ∃ b : ℝ, ∀ x, (b : EReal) ≤ f x := by
  have hm : ∀ x, Monotone (fun n => ((g n x : ℝ) : EReal)) := fun x =>
    monotone_nat_of_le_succ (fun n => EReal.coe_le_coe_iff.mpr (hmono n x))
  have hsup : ∀ x, f x = ⨆ n, ((g n x : ℝ) : EReal) := fun x =>
    tendsto_nhds_unique (hlim x) (tendsto_atTop_iSup (hm x))
  constructor
  · have : f = fun x => ⨆ n, ((g n x : ℝ) : EReal) := funext hsup
    rw [this]
    exact lowerSemicontinuous_iSup (fun n =>
      (continuous_coe_real_ereal.comp (g n).continuous).lowerSemicontinuous)
  · refine ⟨-‖g 0‖, fun x => ?_⟩
    rw [hsup x]
    refine le_trans ?_ (le_iSup _ 0)
    exact EReal.coe_le_coe_iff.mpr (neg_le_of_abs_le ((g 0).norm_coe_le_norm x |>.trans' (le_of_eq (Real.norm_eq_abs _).symm)))

/-- forward direction in a pseudometric space -/
theorem l714_fwd {X : Type*} [PseudoMetricSpace X] (f : X → EReal)
    (hf : LowerSemicontinuous f) (b : ℝ) (hb : ∀ x, (b : EReal) ≤ f x) :
    ∃ g : ℕ → BoundedContinuousFunction X ℝ, (∀ n x, g n x ≤ g (n + 1) x) ∧
        ∀ x, Tendsto (fun n => ((g n x : ℝ) : EReal)) atTop (𝓝 (f x)) := by
  let K : ℕ → ℝ := fun n => (n : ℝ) + |b|
  have hKb : ∀ n, b ≤ K n := fun n => by
    have := le_abs_self b; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; simp only [K]; linarith
  have hKmono : ∀ n, K n ≤ K (n + 1) := fun n => by simp only [K]; push_cast; linarith
  let t : ℕ → X → ℝ := fun n y => (min (f y) (K n : EReal)).toReal
  have ht_eq : ∀ n y, ((t n y : ℝ) : EReal) = min (f y) (K n : EReal) := by
    intro n y
    apply EReal.coe_toReal
    · exact ne_of_lt (lt_of_le_of_lt (min_le_right _ _) (EReal.coe_lt_top _))
    · exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe b) (le_min (hb y) (EReal.coe_le_coe_iff.mpr (hKb n))))
  have ht_lb : ∀ n y, b ≤ t n y := fun n y => by
    have : ((b : ℝ) : EReal) ≤ (t n y : EReal) := by
      rw [ht_eq]; exact le_min (hb y) (EReal.coe_le_coe_iff.mpr (hKb n))
    exact EReal.coe_le_coe_iff.mp this
  have ht_ub : ∀ n y, t n y ≤ K n := fun n y => by
    have : ((t n y : ℝ) : EReal) ≤ (K n : EReal) := by rw [ht_eq]; exact min_le_right _ _
    exact EReal.coe_le_coe_iff.mp this
  have ht_le_f : ∀ n y, ((t n y : ℝ) : EReal) ≤ f y := fun n y => by rw [ht_eq]; exact min_le_left _ _
  have ht_mono : ∀ n y, t n y ≤ t (n + 1) y := fun n y => by
    have : ((t n y : ℝ) : EReal) ≤ (t (n+1) y : EReal) := by
      rw [ht_eq, ht_eq]; exact min_le_min le_rfl (EReal.coe_le_coe_iff.mpr (hKmono n))
    exact EReal.coe_le_coe_iff.mp this
  let G : ℕ → X → ℝ := fun n x => ⨅ y, (t n y + n * dist x y)
  have hbdd : ∀ n x, BddBelow (Set.range fun y => t n y + n * dist x y) := fun n x =>
    ⟨b, by rintro _ ⟨y, rfl⟩; have := ht_lb n y; have : (0:ℝ) ≤ n * dist x y := by positivity
           linarith⟩
  have hG_lb : ∀ n x, b ≤ G n x := fun n x => haveI : Nonempty X := ⟨x⟩; le_ciInf (fun y => by
    have := ht_lb n y; have : (0:ℝ) ≤ n * dist x y := by positivity
    linarith)
  have hG_le : ∀ n x, G n x ≤ t n x := fun n x => by
    have := ciInf_le (hbdd n x) x
    simp only [dist_self, mul_zero, add_zero] at this
    exact this
  have hG_lip : ∀ n x x', G n x ≤ G n x' + n * dist x x' := fun n x x' => by
    have hne : Nonempty X := ⟨x⟩
    rw [← sub_le_iff_le_add]
    apply le_ciInf
    intro y
    rw [sub_le_iff_le_add]
    refine le_trans (ciInf_le (hbdd n x) y) ?_
    have := dist_triangle x x' y
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hG_cont : ∀ n, Continuous (G n) := fun n => by
    apply LipschitzWith.continuous (K := ⟨n, Nat.cast_nonneg n⟩)
    apply LipschitzWith.of_le_add_mul
    intro x x'
    exact hG_lip n x x'
  have hG_bound : ∀ n x, ‖G n x‖ ≤ |b| + K n := fun n x => by
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hG_lb n x; have h2 := hG_le n x; have h3 := ht_ub n x
    have h4 := neg_abs_le b; have h5 := le_abs_self b; have h6 := hKb n
    have h7 : (0:ℝ) ≤ K n := by simp only [K]; positivity
    constructor <;> linarith
  let g : ℕ → BoundedContinuousFunction X ℝ := fun n =>
    BoundedContinuousFunction.ofNormedAddCommGroup (G n) (hG_cont n) (|b| + K n) (hG_bound n)
  refine ⟨g, fun n x => ?_, fun x => ?_⟩
  · show G n x ≤ G (n+1) x
    haveI : Nonempty X := ⟨x⟩
    apply le_ciInf
    intro y
    refine le_trans (ciInf_le (hbdd n x) y) ?_
    have := ht_mono n y
    have : (n : ℝ) * dist x y ≤ ((n + 1 : ℕ) : ℝ) * dist x y := by
      apply mul_le_mul_of_nonneg_right _ dist_nonneg; push_cast; linarith
    linarith
  · show Tendsto (fun n => ((G n x : ℝ) : EReal)) atTop (𝓝 (f x))
    rw [tendsto_order]
    constructor
    · intro a ha
      obtain ⟨r, har, hrf⟩ := EReal.lt_iff_exists_real_btwn.mp ha
      obtain ⟨r', hrr', hr'f⟩ := EReal.lt_iff_exists_real_btwn.mp hrf
      have hev := hf x r' hr'f
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
      -- choose n large
      obtain ⟨N, hN⟩ := exists_nat_gt (max (|r'| + |b|) ((|r'| + |b|) / δ))
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      refine lt_of_lt_of_le har (EReal.coe_le_coe_iff.mpr ?_)
      have hnN : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
      have hnpos : (|r'| + |b|) < n := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hN hnN)
      have hnδ : (|r'| + |b|) / δ < n := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hN hnN)
      have hr'K : r' ≤ K n := by
        simp only [K]; have := le_abs_self r'; have := abs_nonneg b; linarith
      haveI : Nonempty X := ⟨x⟩
      apply le_ciInf
      intro y
      by_cases hy : dist x y < δ
      · have hfy := hball (by rwa [dist_comm] at hy)
        have : (r' : EReal) ≤ (t n y : EReal) := by
          rw [ht_eq]; exact le_min hfy.le (EReal.coe_le_coe_iff.mpr hr'K)
        have h1 := EReal.coe_le_coe_iff.mp this
        have : (0:ℝ) ≤ n * dist x y := by positivity
        have : (r : ℝ) < r' := EReal.coe_lt_coe_iff.mp hrr'
        linarith
      · push_neg at hy
        have h1 := ht_lb n y
        have hnd : (|r'| + |b|) ≤ n * δ := by
          rw [div_lt_iff₀ hδ] at hnδ; linarith
        have : (n : ℝ) * δ ≤ n * dist x y :=
          mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg n)
        have : (r : ℝ) < r' := EReal.coe_lt_coe_iff.mp hrr'
        have := le_abs_self r'; have := neg_abs_le b
        linarith
    · intro a ha
      exact Filter.Eventually.of_forall (fun n =>
        lt_of_le_of_lt (le_trans (EReal.coe_le_coe_iff.mpr (hG_le n x)) (ht_le_f n x)) ha)

theorem usc_iff_lsc_neg {X : Type*} [TopologicalSpace X] (f : X → EReal) :
    UpperSemicontinuous f ↔ LowerSemicontinuous (fun x => -f x) := by
  constructor
  · intro h x y hy
    have hy' : y < -f x := hy
    have := h x (-y) (by rwa [EReal.lt_neg_comm] at hy')
    filter_upwards [this] with x' hx'
    have hx'' : f x' < -y := hx'
    show y < -f x'
    rwa [EReal.lt_neg_comm]
  · intro h x y hy
    have := h x (-y) (show -y < -f x by rwa [EReal.neg_lt_neg_iff])
    filter_upwards [this] with x' hx'
    have hx'' : -y < -f x' := hx'
    rwa [EReal.neg_lt_neg_iff] at hx''

theorem l714_core {X : Type*} [TopologicalSpace X] [MetrizableSpace X]
    (f : X → EReal) :
    ((LowerSemicontinuous f ∧ ∃ b : ℝ, ∀ x, (b : EReal) ≤ f x) ↔
      ∃ g : ℕ → (BoundedContinuousFunction X ℝ), (∀ n x, g n x ≤ g (n + 1) x) ∧
        ∀ x, Filter.Tendsto (fun n => ((g n x : ℝ) : EReal)) Filter.atTop (nhds (f x))) ∧
    ((UpperSemicontinuous f ∧ ∃ b : ℝ, ∀ x, f x ≤ (b : EReal)) ↔
      ∃ g : ℕ → (BoundedContinuousFunction X ℝ), (∀ n x, g (n + 1) x ≤ g n x) ∧
        ∀ x, Filter.Tendsto (fun n => ((g n x : ℝ) : EReal)) Filter.atTop (nhds (f x))) := by
  letI := metrizableSpaceMetric X
  have A : ∀ f : X → EReal, ((LowerSemicontinuous f ∧ ∃ b : ℝ, ∀ x, (b : EReal) ≤ f x) ↔
      ∃ g : ℕ → (BoundedContinuousFunction X ℝ), (∀ n x, g n x ≤ g (n + 1) x) ∧
        ∀ x, Filter.Tendsto (fun n => ((g n x : ℝ) : EReal)) Filter.atTop (nhds (f x))) := by
    intro f
    constructor
    · rintro ⟨hf, b, hb⟩
      exact l714_fwd f hf b hb
    · rintro ⟨g, hm, hl⟩
      exact l714_back f g hm hl
  refine ⟨A f, ?_⟩
  have hneg : Continuous (fun z : EReal => -z) := continuous_neg
  constructor
  · rintro ⟨hf, b, hb⟩
    obtain ⟨g, hm, hl⟩ := (A (fun x => -f x)).mp ⟨(usc_iff_lsc_neg f).mp hf, -b, fun x => by
      rw [EReal.coe_neg, EReal.neg_le_neg_iff]; exact hb x⟩
    refine ⟨fun n => -g n, fun n x => by simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply]; linarith [hm n x], fun x => ?_⟩
    have := (hneg.tendsto _).comp (hl x)
    simp only [neg_neg] at this
    convert this using 2 with n
    simp
  · rintro ⟨g, hm, hl⟩
    obtain ⟨hl', b, hb⟩ := (A (fun x => -f x)).mpr ⟨fun n => -g n,
      fun n x => by simp only [BoundedContinuousFunction.coe_neg, Pi.neg_apply]; linarith [hm n x],
      fun x => by
        have := (hneg.tendsto _).comp (hl x)
        convert this using 2 with n
        simp⟩
    refine ⟨(usc_iff_lsc_neg f).mpr hl', -b, fun x => ?_⟩
    have := hb x
    rw [← EReal.neg_le_neg_iff, EReal.coe_neg, neg_neg]; exact this

end L714

open MeasureTheory TopologicalSpace Filter Topology in
theorem expect_tendsto_aux {Y : Type*} [MeasurableSpace Y] (Q : Measure Y) [IsProbabilityMeasure Q]
    (h : Y → EReal) (v : ℕ → Y → ℝ) (hv : ∀ n, Measurable (v n))
    (hvb : ∀ n, ∃ C : ℝ, ∀ y, |v n y| ≤ C)
    (hlim : ∀ y, Tendsto (fun n => (v n y : EReal)) atTop (𝓝 (h y)))
    (hmono : (∀ n y, v n y ≤ v (n+1) y) ∨ (∀ n y, v (n+1) y ≤ v n y)) :
    Tendsto (fun n => ((∫ y, v n y ∂Q : ℝ) : EReal)) atTop
      (𝓝 (DupacovaWets.Consistency.expect Q h)) := by
  set A : ℕ → ENNReal := fun n => ∫⁻ y, ENNReal.ofReal (v n y) ∂Q with hAdef
  set B : ℕ → ENNReal := fun n => ∫⁻ y, ENNReal.ofReal (-v n y) ∂Q with hBdef
  set A' : ENNReal := ∫⁻ y, (h y).toENNReal ∂Q with hA'def
  set B' : ENNReal := ∫⁻ y, (-h y).toENNReal ∂Q with hB'def
  have hpt1 : ∀ y, Tendsto (fun n => ENNReal.ofReal (v n y)) atTop (𝓝 ((h y).toENNReal)) := fun y =>
    (EReal.continuous_toENNReal.tendsto _).comp (hlim y)
  have hpt2 : ∀ y, Tendsto (fun n => ENNReal.ofReal (-v n y)) atTop (𝓝 ((-h y).toENNReal)) := by
    intro y
    have := (EReal.continuous_toENNReal.tendsto _).comp ((continuous_neg.tendsto _).comp (hlim y))
    convert this using 2 with n
    simp [Function.comp, ← EReal.coe_neg]
  have hmeas1 : ∀ n, Measurable (fun y => ENNReal.ofReal (v n y)) := fun n =>
    ENNReal.measurable_ofReal.comp (hv n)
  have hmeas2 : ∀ n, Measurable (fun y => ENNReal.ofReal (-v n y)) := fun n =>
    ENNReal.measurable_ofReal.comp (hv n).neg
  have hconst : ∀ c : ℝ, ∫⁻ _y, ENNReal.ofReal c ∂Q ≠ ⊤ := fun c => by
    rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top
  have hAfin : ∀ n, A n ≠ ⊤ := fun n => by
    obtain ⟨C, hC⟩ := hvb n
    refine ne_top_of_le_ne_top (hconst C) (lintegral_mono (fun y => ENNReal.ofReal_le_ofReal ?_))
    exact le_trans (le_abs_self _) (hC y)
  have hBfin : ∀ n, B n ≠ ⊤ := fun n => by
    obtain ⟨C, hC⟩ := hvb n
    refine ne_top_of_le_ne_top (hconst C) (lintegral_mono (fun y => ENNReal.ofReal_le_ofReal ?_))
    exact le_trans (neg_le_abs _) (hC y)
  -- convergence of the parts
  have hconv : Tendsto A atTop (𝓝 A') ∧ Tendsto B atTop (𝓝 B') ∧ (A' ≠ ⊤ ∨ B' ≠ ⊤) := by
    obtain ⟨C0, hC0⟩ := hvb 0
    rcases hmono with hm | hm
    · have hm' : ∀ y, Monotone (fun n => v n y) := fun y => monotone_nat_of_le_succ (fun n => hm n y)
      have hB : Tendsto B atTop (𝓝 B') :=
        tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal C0) hmeas2
          (fun n => Filter.Eventually.of_forall (fun y => ENNReal.ofReal_le_ofReal (by
            have := hm' y (Nat.zero_le n); have := neg_le_abs (v 0 y); have := hC0 y; linarith)))
          (hconst C0) (Filter.Eventually.of_forall hpt2)
      refine ⟨lintegral_tendsto_of_tendsto_of_monotone (fun n => (hmeas1 n).aemeasurable)
        (Filter.Eventually.of_forall (fun y a b hab => ENNReal.ofReal_le_ofReal (hm' y hab)))
        (Filter.Eventually.of_forall hpt1), hB, Or.inr ?_⟩
      refine ne_top_of_le_ne_top (hconst C0) (le_of_tendsto' hB (fun n => lintegral_mono (fun y =>
        ENNReal.ofReal_le_ofReal ?_)))
      have := hm' y (Nat.zero_le n); have := neg_le_abs (v 0 y); have := hC0 y; linarith
    · have hm' : ∀ y, Antitone (fun n => v n y) := fun y => antitone_nat_of_succ_le (fun n => hm n y)
      have hA : Tendsto A atTop (𝓝 A') :=
        tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal C0) hmeas1
          (fun n => Filter.Eventually.of_forall (fun y => ENNReal.ofReal_le_ofReal (by
            have := hm' y (Nat.zero_le n); have := le_abs_self (v 0 y); have := hC0 y; linarith)))
          (hconst C0) (Filter.Eventually.of_forall hpt1)
      refine ⟨hA, lintegral_tendsto_of_tendsto_of_monotone (fun n => (hmeas2 n).aemeasurable)
        (Filter.Eventually.of_forall (fun y a b hab => ENNReal.ofReal_le_ofReal (by
          have := hm' y hab; linarith)))
        (Filter.Eventually.of_forall hpt2), Or.inl ?_⟩
      refine ne_top_of_le_ne_top (hconst C0) (le_of_tendsto' hA (fun n => lintegral_mono (fun y =>
        ENNReal.ofReal_le_ofReal ?_)))
      have := hm' y (Nat.zero_le n); have := le_abs_self (v 0 y); have := hC0 y; linarith
  obtain ⟨hA, hB, hfin⟩ := hconv
  have hexp : DupacovaWets.Consistency.expect Q h = (A' : EReal) - (B' : EReal) := by
    unfold DupacovaWets.Consistency.expect
    split_ifs with hh
    · have hB' : B' ≠ ⊤ := by
        rcases hfin with h1 | h1
        · exact absurd hh h1
        · exact h1
      rw [show A' = ⊤ from hh, ← EReal.coe_ennreal_toReal hB']
      simp
    · rfl
  have hint : ∀ n, ((∫ y, v n y ∂Q : ℝ) : EReal) = (A n : EReal) + -(B n : EReal) := by
    intro n
    obtain ⟨C, hC⟩ := hvb n
    have hI : Integrable (v n) Q := by
      refine Integrable.of_bound (hv n).aestronglyMeasurable C (Filter.Eventually.of_forall
        (fun y => by rw [Real.norm_eq_abs]; exact hC y))
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI]
    rw [EReal.coe_sub, EReal.coe_ennreal_toReal (hAfin n), EReal.coe_ennreal_toReal (hBfin n)]
    rfl
  simp_rw [hint]
  rw [hexp]
  show Tendsto (fun n => (A n : EReal) + -(B n : EReal)) atTop (𝓝 ((A' : EReal) + -(B' : EReal)))
  have hc := EReal.continuousAt_add (p := ((A' : EReal), -(B' : EReal)))
    (by
      rcases hfin with h1 | h1
      · left; simp only; rw [Ne, ← EReal.coe_ennreal_top, EReal.coe_ennreal_eq_coe_ennreal_iff]; exact h1
      · right; simp only; rw [Ne, EReal.neg_eq_bot_iff, ← EReal.coe_ennreal_top, EReal.coe_ennreal_eq_coe_ennreal_iff]; exact h1)
    (Or.inl (EReal.coe_ennreal_ne_bot _))
  exact hc.tendsto.comp (Tendsto.prodMk_nhds ((continuous_coe_ennreal_ereal.tendsto _).comp hA)
    ((continuous_neg.tendsto _).comp ((continuous_coe_ennreal_ereal.tendsto _).comp hB)))


open MeasureTheory TopologicalSpace Filter Topology in
theorem p731_core {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [SeparableSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (q : X → ProbabilityMeasure Y) (hq : Continuous q) (f : X × Y → EReal) :
    ((LowerSemicontinuous f ∧ ∃ b : ℝ, ∀ z, (b : EReal) ≤ f z) →
      LowerSemicontinuous (fun x => DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y))) ∧
      ∃ b : ℝ, ∀ x, (b : EReal) ≤ DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y))) ∧
    ((UpperSemicontinuous f ∧ ∃ b : ℝ, ∀ z, f z ≤ (b : EReal)) →
      UpperSemicontinuous (fun x => DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y))) ∧
      ∃ b : ℝ, ∀ x, DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y)) ≤ (b : EReal)) := by
  set L : X → EReal := fun x => DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y)) with hL
  let sl : BoundedContinuousFunction (X × Y) ℝ → X → BoundedContinuousFunction Y ℝ :=
    fun g z => g.compContinuous ⟨fun y => (z, y), by fun_prop⟩
  have key : ∀ g : ℕ → BoundedContinuousFunction (X × Y) ℝ,
      ((∀ n z, g n z ≤ g (n + 1) z) ∨ (∀ n z, g (n + 1) z ≤ g n z)) →
      (∀ z, Tendsto (fun n => ((g n z : ℝ) : EReal)) atTop (𝓝 (f z))) →
      ∀ x, Tendsto (fun n => ((∫ y, g n (x, y) ∂(q x : Measure Y) : ℝ) : EReal)) atTop (𝓝 (L x)) := by
    intro g hm hl x
    apply expect_tendsto_aux (q x : Measure Y) (fun y => f (x, y)) (fun n y => g n (x, y))
    · intro n
      exact ((g n).continuous.comp (by fun_prop : Continuous fun y : Y => (x, y))).measurable
    · intro n
      exact ⟨‖g n‖, fun y => by have := (g n).norm_coe_le_norm (x, y); rwa [Real.norm_eq_abs] at this⟩
    · intro y; exact hl (x, y)
    · rcases hm with hm | hm
      · exact Or.inl (fun n y => hm n (x, y))
      · exact Or.inr (fun n y => hm n (x, y))
  have hbnd : ∀ (g : BoundedContinuousFunction (X × Y) ℝ) x,
      |∫ y, g (x, y) ∂(q x : Measure Y)| ≤ ‖g‖ := by
    intro g x
    have h1 := (sl g x).norm_integral_le_norm (μ := (q x : Measure Y))
    have h2 : ‖sl g x‖ ≤ ‖g‖ := by
      rw [BoundedContinuousFunction.norm_le (norm_nonneg _)]
      intro y; exact g.norm_coe_le_norm (x, y)
    rw [← Real.norm_eq_abs]
    exact le_trans h1 h2
  have hcont : ∀ (g : BoundedContinuousFunction (X × Y) ℝ),
      Continuous (fun x => ((∫ y, g (x, y) ∂(q x : Measure Y) : ℝ) : EReal)) := fun g =>
    continuous_coe_real_ereal.comp (p730_core q hq g)
  have hintg : ∀ (g : BoundedContinuousFunction (X × Y) ℝ) x,
      Integrable (fun y => g (x, y)) (q x : Measure Y) := fun g x => (sl g x).integrable _
  constructor
  · rintro ⟨hlsc, b, hb⟩
    obtain ⟨g, hm, hl⟩ := ((l714_core f).1).mp ⟨hlsc, b, hb⟩
    have hmono : ∀ x, Monotone (fun n => ((∫ y, g n (x, y) ∂(q x : Measure Y) : ℝ) : EReal)) :=
      fun x => monotone_nat_of_le_succ (fun n => EReal.coe_le_coe_iff.mpr
        (integral_mono (hintg _ x) (hintg _ x) (fun y => hm n (x, y))))
    have hsup : ∀ x, L x = ⨆ n, ((∫ y, g n (x, y) ∂(q x : Measure Y) : ℝ) : EReal) := fun x =>
      tendsto_nhds_unique (key g (Or.inl hm) hl x) (tendsto_atTop_iSup (hmono x))
    refine ⟨?_, -‖g 0‖, fun x => ?_⟩
    · have : L = fun x => ⨆ n, ((∫ y, g n (x, y) ∂(q x : Measure Y) : ℝ) : EReal) := funext hsup
      rw [this]
      exact lowerSemicontinuous_iSup (fun n => (hcont (g n)).lowerSemicontinuous)
    · show _ ≤ L x
      rw [hsup x]
      refine le_trans ?_ (le_iSup _ 0)
      exact EReal.coe_le_coe_iff.mpr (abs_le.mp (hbnd (g 0) x)).1
  · rintro ⟨husc, b, hb⟩
    obtain ⟨g, hm, hl⟩ := ((l714_core f).2).mp ⟨husc, b, hb⟩
    have hanti : ∀ x, Antitone (fun n => ((∫ y, g n (x, y) ∂(q x : Measure Y) : ℝ) : EReal)) :=
      fun x => antitone_nat_of_succ_le (fun n => EReal.coe_le_coe_iff.mpr
        (integral_mono (hintg _ x) (hintg _ x) (fun y => hm n (x, y))))
    have hinf : ∀ x, L x = ⨅ n, ((∫ y, g n (x, y) ∂(q x : Measure Y) : ℝ) : EReal) := fun x =>
      tendsto_nhds_unique (key g (Or.inr hm) hl x) (tendsto_atTop_iInf (hanti x))
    refine ⟨?_, ‖g 0‖, fun x => ?_⟩
    · have : L = fun x => ⨅ n, ((∫ y, g n (x, y) ∂(q x : Measure Y) : ℝ) : EReal) := funext hinf
      rw [this]
      exact upperSemicontinuous_iInf (fun n => (hcont (g n)).upperSemicontinuous)
    · show L x ≤ _
      rw [hinf x]
      refine le_trans (iInf_le _ 0) ?_
      exact EReal.coe_le_coe_iff.mpr (abs_le.mp (hbnd (g 0) x)).2

end BertsekasShreve.SemicontSelection

open BertsekasShreve.SemicontSelection
open MeasureTheory TopologicalSpace BertsekasShreve.SemicontSelection

theorem solution {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [SeparableSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (q : X → ProbabilityMeasure Y) (hq : Continuous q) (f : X × Y → EReal)
    (hf : @Measurable (X × Y) EReal (borel (X × Y)) _ f) :
    ((LowerSemicontinuous f ∧ ∃ b : ℝ, ∀ z, (b : EReal) ≤ f z) →
      LowerSemicontinuous (fun x => DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y))) ∧
      ∃ b : ℝ, ∀ x, (b : EReal) ≤ DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y))) ∧
    ((UpperSemicontinuous f ∧ ∃ b : ℝ, ∀ z, f z ≤ (b : EReal)) →
      UpperSemicontinuous (fun x => DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y))) ∧
      ∃ b : ℝ, ∀ x, DupacovaWets.Consistency.expect (q x : Measure Y) (fun y => f (x, y)) ≤ (b : EReal)) := by
  exact p731_core q hq f
