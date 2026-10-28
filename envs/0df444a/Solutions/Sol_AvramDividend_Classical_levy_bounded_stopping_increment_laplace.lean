-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_increment_laplace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:59:07.787967+00:00
-- url     : https://prove2.me/submissions/32495071-0903-4b56-bdb9-ce9ffa860734

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace S107Dy

lemma le_iff (t : ℝ≥0) (n m : ℕ) :
    (t : ℝ) * (2 : ℝ) ^ n ≤ m ↔ t ≤ (m : ℝ≥0) / (2 : ℝ≥0) ^ n := by
  rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast,
    le_div_iff₀ (by positivity)]
  norm_num

lemma fibre {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (n k : ℕ) :
    MeasurableSet[𝓕 ((k : ℝ≥0) / (2 : ℝ≥0) ^ n)]
      {ω : Ω | Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) = k} := by
  have hle : ∀ m : ℕ, MeasurableSet[𝓕 ((m : ℝ≥0) / (2 : ℝ≥0) ^ n)]
      {ω | (τ ω : ℝ) * (2 : ℝ) ^ n ≤ m} := by
    intro m
    have h := hstop ((m : ℝ≥0) / (2 : ℝ≥0) ^ n)
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe, le_iff]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · convert hle 0 using 1
    ext ω; simp only [Set.mem_ofPred_eq, Nat.ceil_eq_zero, Nat.cast_zero]
  · have hmono : (((k - 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ≤ (k : ℝ≥0) / (2 : ℝ≥0) ^ n := by
      gcongr; exact_mod_cast Nat.sub_le k 1
    have h1 := 𝓕.mono hmono _ (hle (k - 1))
    have : {ω : Ω | Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) = k} =
        {ω | (τ ω : ℝ) * (2 : ℝ) ^ n ≤ k} \ {ω | (τ ω : ℝ) * (2 : ℝ) ^ n ≤ ((k - 1 : ℕ) : ℝ)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_diff, Nat.ceil_eq_iff hk.ne', not_le]
      tauto
    rw [this]
    exact (hle k).diff h1

end S107Dy
open MeasureTheory Set Filter Topology
open scoped NNReal
namespace S107Dy
theorem grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) :
    ∃ (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0),
      (∀ n ω, τn n ω ∈ grid n) ∧
      (∀ n s, s ∈ grid n →
        MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s}) ∧
      (∀ ω n, τ ω ≤ τn n ω) ∧
      (∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) := by
  let c : ℕ → Ω → ℕ := fun n ω => Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n)
  refine ⟨fun n ω => (c n ω : ℝ≥0) / (2 : ℝ≥0) ^ n,
    fun n => (Finset.range (Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n) + 1)).image
      (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n), ?_, ?_, ?_, ?_⟩
  · intro n ω
    refine Finset.mem_image.2 ⟨c n ω, Finset.mem_range.2 (Nat.lt_succ_of_le ?_), rfl⟩
    exact Nat.ceil_mono (mul_le_mul_of_nonneg_right (by exact_mod_cast hbound ω) (by positivity))
  · intro n s hs
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hs
    have hinj : ∀ a b : ℕ, (a : ℝ≥0) / (2 : ℝ≥0) ^ n = (b : ℝ≥0) / (2 : ℝ≥0) ^ n → a = b := by
      intro a b h
      have h2 : (2 : ℝ≥0) ^ n ≠ 0 := by positivity
      rw [div_left_inj' h2] at h; exact_mod_cast h
    have : {ω : Ω | (c n ω : ℝ≥0) / (2 : ℝ≥0) ^ n = (k : ℝ≥0) / (2 : ℝ≥0) ^ n} =
        {ω : Ω | Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) = k} := by
      ext ω; simp only [Set.mem_ofPred_eq]
      exact ⟨fun h => hinj _ _ h, fun h => by simp only [c, h]⟩
    rw [this]; exact S107Dy.fibre 𝓕 τ hstop n k
  · intro ω n
    have := Nat.le_ceil ((τ ω : ℝ) * (2 : ℝ) ^ n)
    exact (S107Dy.le_iff (τ ω) n (c n ω)).1 this
  · intro ω
    rw [← NNReal.tendsto_coe]
    have hup : ∀ n, (((c n ω : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ≤ τ ω + (1 / 2 : ℝ) ^ n := by
      intro n
      have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (τ ω : ℝ) * (2 : ℝ) ^ n by positivity)
      rw [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, div_le_iff₀ (by positivity)]
      have : (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
      push_cast
      nlinarith
    have hlo : ∀ n, (τ ω : ℝ) ≤ (((c n ω : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
      intro n
      exact_mod_cast (S107Dy.le_iff (τ ω) n (c n ω)).1 (Nat.le_ceil _)
    have hlim : Tendsto (fun n : ℕ => (τ ω : ℝ) + (1 / 2 : ℝ) ^ n) atTop (𝓝 (τ ω)) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_add (τ ω : ℝ)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlo hup
end S107Dy

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace S107LA

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

lemma measX (X : SpectrallyNegativeLevy P 𝓕) (r : ℝ≥0) : Measurable (X.X r) :=
  (X.adapted r).mono (𝓕.le r) le_rfl

/-- Laplace transform of a fixed-time increment. -/
lemma fixed (X : SpectrallyNegativeLevy P 𝓕) (g h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (X.X (g + h) ω - X.X g ω))) ∂P =
      ENNReal.ofReal (Real.exp ((h : ℝ) * X.ψ θ)) := by
  haveI := X.isProbability
  have hid := X.stationaryIncrements g (g + h) le_self_add
  rw [add_tsub_cancel_left] at hid
  have hu : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (θ * y)) := by fun_prop
  have e1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (X.X (g + h) ω - X.X g ω))) ∂P =
      ∫⁻ y, ENNReal.ofReal (Real.exp (θ * y)) ∂(P.map fun ω => X.X (g + h) ω - X.X g ω) := by
    have hm : Measurable fun ω => X.X (g + h) ω - X.X g ω := (measX X _).sub (measX X _)
    exact (lintegral_map hu hm).symm
  have e2 : ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X.X h ω)) ∂P =
      ∫⁻ y, ENNReal.ofReal (Real.exp (θ * y)) ∂(P.map (X.X h)) := by
    exact (lintegral_map hu (measX X _)).symm
  rw [e1, hid.map_eq, ← e2]
  obtain ⟨hint, hval⟩ := X.laplace h θ hθ
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    hval]
  rfl

/-- Discrete stopping times on a finite grid. -/
lemma discrete (X : SpectrallyNegativeLevy P 𝓕) (τ : Ω → ℝ≥0) (G : Finset ℝ≥0)
    (hG : ∀ ω, τ ω ∈ G) (hfib : ∀ g ∈ G, MeasurableSet[𝓕 g] {ω | τ ω = g})
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Measurable (fun ω => ENNReal.ofReal (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)))) ∧
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) ∂P =
      ENNReal.ofReal (Real.exp ((h : ℝ) * X.ψ θ)) := by
  classical
  haveI := X.isProbability
  set Y : ℝ≥0 → Ω → ℝ≥0∞ := fun g ω => ENNReal.ofReal (Real.exp (θ * (X.X (g + h) ω - X.X g ω)))
    with hY
  have hYm : ∀ g, Measurable (Y g) := fun g => by
    have hm : Measurable fun ω => X.X (g + h) ω - X.X g ω := (measX X _).sub (measX X _)
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hm.const_mul θ))
  have hsum : (fun ω => ENNReal.ofReal (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)))) =
      fun ω => ∑ g ∈ G, {ω | τ ω = g}.indicator 1 ω * Y g ω := by
    funext ω
    rw [Finset.sum_eq_single (τ ω)]
    · simp [Y]
    · intro b _ hb
      rw [indicator_of_notMem (show ω ∉ {ω | τ ω = b} from fun h => hb h.symm), zero_mul]
    · intro h'; exact absurd (hG ω) h'
  have hfibm : ∀ g ∈ G, MeasurableSet {ω | τ ω = g} := fun g hg => 𝓕.le g _ (hfib g hg)
  refine ⟨?_, ?_⟩
  · rw [hsum]
    refine Finset.measurable_sum _ fun g hg => ?_
    exact ((measurable_one.indicator (hfibm g hg))).mul (hYm g)
  rw [hsum, lintegral_finset_sum (f := fun g ω => {ω | τ ω = g}.indicator 1 ω * Y g ω) G
    (fun g hg => ((measurable_one.indicator (hfibm g hg))).mul (hYm g))]
  have hterm : ∀ g ∈ G, ∫⁻ ω, {ω | τ ω = g}.indicator 1 ω * Y g ω ∂P =
      P {ω | τ ω = g} * ENNReal.ofReal (Real.exp ((h : ℝ) * X.ψ θ)) := by
    intro g hg
    have hind : Indep (𝓕 g) (MeasurableSpace.comap (fun ω => X.X (g + h) ω - X.X g ω) inferInstance) P :=
      (X.indepIncrements g (g + h) le_self_add).symm
    have hYc : Measurable[MeasurableSpace.comap (fun ω => X.X (g + h) ω - X.X g ω) inferInstance] (Y g) := by
      have hc : Measurable[MeasurableSpace.comap (fun ω => X.X (g + h) ω - X.X g ω) inferInstance]
          (fun ω => X.X (g + h) ω - X.X g ω) := comap_measurable _
      have hu : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (θ * y)) := by fun_prop
      exact hu.comp hc
    have hI : Measurable[𝓕 g] ({ω | τ ω = g}.indicator (1 : Ω → ℝ≥0∞)) :=
      Measurable.indicator (by exact measurable_const) (hfib g hg)
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace (𝓕.le g)
      ((((measX X _).sub (measX X _))).comap_le) hind hI hYc]
    rw [lintegral_indicator (hfibm g hg), Pi.one_def, setLIntegral_const, one_mul, fixed X g h θ hθ]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  have hP : ∑ g ∈ G, P {ω | τ ω = g} = 1 := by
    rw [← measure_biUnion_finset (fun a _ b _ hab => Set.disjoint_left.2 fun ω h1 h2 =>
      hab (h1.symm.trans h2)) hfibm]
    have : (⋃ g ∈ G, {ω | τ ω = g}) = Set.univ := by
      ext ω; simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨τ ω, hG ω, rfl⟩
    rw [this, measure_univ]
  rw [hP, one_mul]

end S107LA

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)) ∂P =
      Real.exp ((h : ℝ) * X.ψ θ) := by
  haveI := X.isProbability
  obtain ⟨τn, grid, hgrid, hfib, hle, hlim⟩ := S107Dy.grid 𝓕 τ hτ T hbounded
  have hd := fun n => S107LA.discrete X (τn n) (grid n) (hgrid n) (hfib n) h θ hθ
  have hd2 := fun n => S107LA.discrete X (τn n) (grid n) (hgrid n) (hfib n) h (2 * θ) (by linarith)
  -- pointwise convergence of the increments (right-continuity)
  have hconv : ∀ ω, Tendsto (fun n => θ * (X.X (τn n ω + h) ω - X.X (τn n ω) ω)) atTop
      (𝓝 (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) := by
    intro ω
    have h1 : Tendsto (fun n => τn n ω + h) atTop (𝓝[Set.Ici (τ ω + h)] (τ ω + h)) :=
      tendsto_nhdsWithin_iff.2 ⟨(hlim ω).add_const h,
        Eventually.of_forall fun n => add_le_add_left (hle ω n) h⟩
    have h2 : Tendsto (fun n => τn n ω) atTop (𝓝[Set.Ici (τ ω)] (τ ω)) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim ω, Eventually.of_forall fun n => hle ω n⟩
    exact (((X.rightCont ω _).tendsto.comp h1).sub ((X.rightCont ω _).tendsto.comp h2)).const_mul θ
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal (Real.exp (θ * (X.X (τn n ω + h) ω - X.X (τn n ω) ω))) with hf
  set g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)))
    with hg
  have hfg : ∀ ω, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := fun ω =>
    (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_exp.tendsto _).comp (hconv ω))
  have hfm : ∀ n, Measurable (f n) := fun n => (hd n).1
  have hgm : Measurable g := measurable_of_tendsto_metrizable' atTop hfm (tendsto_pi_nhds.2 hfg)
  set c := ENNReal.ofReal (Real.exp ((h : ℝ) * X.ψ θ)) with hc
  set C2 := ENNReal.ofReal (Real.exp ((h : ℝ) * X.ψ (2 * θ))) with hC2
  have hfint : ∀ n, ∫⁻ ω, f n ω ∂P = c := fun n => (hd n).2
  -- upper bound by Fatou
  have hup : ∫⁻ ω, g ω ∂P ≤ c := by
    calc ∫⁻ ω, g ω ∂P = ∫⁻ ω, liminf (fun n => f n ω) atTop ∂P := by
          congr 1; funext ω; exact ((hfg ω).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop :=
          lintegral_liminf_le' (fun n => (hfm n).aemeasurable)
      _ = c := by simp only [hfint, liminf_const]
  -- lower bound by truncation
  have hlow : c ≤ ∫⁻ ω, g ω ∂P := by
    have hM : ∀ M : ℕ, c ≤ ∫⁻ ω, g ω ∂P + C2 * ENNReal.ofReal (1 / ((M : ℝ) + 1)) := by
      intro M
      set m : ℝ := (M : ℝ) + 1 with hm
      have hm0 : 0 < m := by positivity
      have hpt : ∀ n ω, f n ω ≤ min (f n ω) (ENNReal.ofReal m) +
          ENNReal.ofReal (Real.exp (2 * θ * (X.X (τn n ω + h) ω - X.X (τn n ω) ω))) *
            ENNReal.ofReal (1 / m) := by
        intro n ω
        set a := Real.exp (θ * (X.X (τn n ω + h) ω - X.X (τn n ω) ω)) with ha
        have ha0 : 0 < a := Real.exp_pos _
        have hsq : Real.exp (2 * θ * (X.X (τn n ω + h) ω - X.X (τn n ω) ω)) = a ^ 2 := by
          rw [ha, sq, ← Real.exp_add]; ring_nf
        rw [hsq]
        by_cases ham : a ≤ m
        · rw [min_eq_left (ENNReal.ofReal_le_ofReal ham)]; exact le_self_add
        · rw [not_le] at ham
          refine le_trans ?_ le_add_self
          rw [← ENNReal.ofReal_mul (sq_nonneg a)]
          apply ENNReal.ofReal_le_ofReal
          rw [mul_one_div, le_div_iff₀ hm0]
          nlinarith
      have hfm2 : ∀ n, Measurable fun ω =>
          ENNReal.ofReal (Real.exp (2 * θ * (X.X (τn n ω + h) ω - X.X (τn n ω) ω))) :=
        fun n => (hd2 n).1
      have hstep : ∀ n, c ≤ ∫⁻ ω, min (f n ω) (ENNReal.ofReal m) ∂P + C2 * ENNReal.ofReal (1 / m) := by
        intro n
        rw [← hfint n]
        calc ∫⁻ ω, f n ω ∂P ≤ ∫⁻ ω, (min (f n ω) (ENNReal.ofReal m) +
            ENNReal.ofReal (Real.exp (2 * θ * (X.X (τn n ω + h) ω - X.X (τn n ω) ω))) *
              ENNReal.ofReal (1 / m)) ∂P := lintegral_mono (hpt n)
          _ = ∫⁻ ω, min (f n ω) (ENNReal.ofReal m) ∂P + C2 * ENNReal.ofReal (1 / m) := by
            rw [lintegral_add_right _ ((hfm2 n).mul_const _), lintegral_mul_const _ (hfm2 n),
              (hd2 n).2]
      have htr : Tendsto (fun n => ∫⁻ ω, min (f n ω) (ENNReal.ofReal m) ∂P) atTop
          (𝓝 (∫⁻ ω, min (g ω) (ENNReal.ofReal m) ∂P)) := by
        refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal m)
          (fun n => (hfm n).min measurable_const)
          (fun n => Eventually.of_forall fun ω => min_le_right _ _) ?_
          (Eventually.of_forall fun ω => ((hfg ω).min tendsto_const_nhds))
        rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top
      have hlim2 := htr.add_const (C2 * ENNReal.ofReal (1 / m))
      have := ge_of_tendsto' hlim2 hstep
      refine this.trans (add_le_add_left (lintegral_mono fun ω => min_le_left _ _) _)
    have hT : Tendsto (fun M : ℕ => ∫⁻ ω, g ω ∂P + C2 * ENNReal.ofReal (1 / ((M : ℝ) + 1)))
        atTop (𝓝 (∫⁻ ω, g ω ∂P + C2 * 0)) := by
      refine tendsto_const_nhds.add (ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top))
      have := (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [Function.comp_def] using this
    rw [mul_zero, add_zero] at hT
    exact ge_of_tendsto' hT hM
  have heq : ∫⁻ ω, g ω ∂P = c := le_antisymm hup hlow
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  · rw [show (fun ω => ENNReal.ofReal (Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω)))) = g from rfl,
      heq, hc, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  · have : (fun ω => Real.exp (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) = fun ω => (g ω).toReal := by
      funext ω; simp only [hg, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [this]; exact hgm.ennreal_toReal.aestronglyMeasurable
