-- Prove2me | solution 1 for BertsekasShreve.SemicontSelection.lemma7_14_lsc_iff_monotone_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:54:26.377978+00:00
-- url     : https://prove2.me/submissions/693d762b-e8f5-4e19-af38-00263da20726

import Mathlib



namespace BertsekasShreve.SemicontSelection

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

end BertsekasShreve.SemicontSelection

open BertsekasShreve.SemicontSelection
open TopologicalSpace BertsekasShreve.SemicontSelection

theorem solution {X : Type*} [TopologicalSpace X] [MetrizableSpace X]
    (f : X → EReal) :
    ((LowerSemicontinuous f ∧ ∃ b : ℝ, ∀ x, (b : EReal) ≤ f x) ↔
      ∃ g : ℕ → (BoundedContinuousFunction X ℝ), (∀ n x, g n x ≤ g (n + 1) x) ∧
        ∀ x, Filter.Tendsto (fun n => ((g n x : ℝ) : EReal)) Filter.atTop (nhds (f x))) ∧
    ((UpperSemicontinuous f ∧ ∃ b : ℝ, ∀ x, f x ≤ (b : EReal)) ↔
      ∃ g : ℕ → (BoundedContinuousFunction X ℝ), (∀ n x, g (n + 1) x ≤ g n x) ∧
        ∀ x, Filter.Tendsto (fun n => ((g n x : ℝ) : EReal)) Filter.atTop (nhds (f x))) := by
  exact l714_core f
