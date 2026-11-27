-- Prove2me | solution 1 for GEPPGrowth.Main.proposition_5_1
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T22:14:32.571797+00:00
-- url     : https://prove2.me/submissions/97f68633-2a76-4689-ad0a-d17d8a1c4494

import Mathlib
import Definitions.Def_GEPPGrowth_Main_Process
import Theorems.Thm_MathlibGap_absolutelyContinuous_pi

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal

noncomputable section

namespace GEPP51

open GEPPGrowth.Main

/-- The standard Gaussian on `Fin n → ℝ`. -/
abbrev gam (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => gaussianReal 0 1)

open scoped MatrixOrder in
lemma normal_one (n : ℕ) : normal (1 : Mat n) = gam n := by
  unfold normal multivariateGaussian
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop), CFC.sqrt_one]
  convert Measure.map_id
  funext x i
  simp

/-- Coordinate permutations preserve the standard Gaussian. -/
lemma perm_preserving {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun y : Fin n → ℝ => y ∘ σ) (gam n) (gam n) := by
  refine ⟨by fun_prop, (Measure.pi_eq fun s hs => ?_).symm⟩
  have hpre : (fun y : Fin n → ℝ => y ∘ σ) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun j => s (σ.symm j)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply]
    constructor
    · intro h j; simpa using h (σ.symm j)
    · intro h j; simpa using h (σ j)
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs), hpre, Measure.pi_pi]
  exact Equiv.prod_comp σ.symm (fun i => gaussianReal 0 1 (s i))

/-- Flipping the sign of every coordinate except `i` preserves the standard Gaussian. -/
lemma flip_preserving {n : ℕ} (i : Fin n) :
    MeasurePreserving (fun y : Fin n → ℝ => fun j => if j = i then y j else -y j) (gam n) (gam n) := by
  have hF : Measurable (fun y : Fin n → ℝ => fun j => if j = i then y j else -y j) := by
    refine measurable_pi_lambda _ fun j => ?_
    split_ifs
    · exact measurable_pi_apply j
    · exact (measurable_pi_apply j).neg
  refine ⟨hF, (Measure.pi_eq fun s hs => ?_).symm⟩
  have hneg : ∀ t : Set ℝ, MeasurableSet t →
      gaussianReal 0 1 ((fun x => -x) ⁻¹' t) = gaussianReal 0 1 t := fun t ht => by
    rw [← Measure.map_apply measurable_neg ht, gaussianReal_map_neg, neg_zero]
  have hpre : (fun y : Fin n → ℝ => fun j => if j = i then y j else -y j) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun j => if j = i then s j else (fun x => -x) ⁻¹' s j) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    refine forall_congr' fun j => ?_
    split_ifs <;> rfl
  rw [Measure.map_apply hF (MeasurableSet.univ_pi hs), hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs
  · rfl
  · exact hneg _ (hs j)

/-- Gaussian ties between two coordinates in absolute value have probability zero. -/
lemma ties_null {n : ℕ} {j k : Fin n} (hjk : j ≠ k) : gam n {y | |y j| = |y k|} = 0 := by
  have hac : gam n ≪ volume := by
    rw [volume_pi]
    exact MathlibGap.absolutelyContinuous_pi fun _ =>
      gaussianReal_absolutelyContinuous 0 one_ne_zero
  set L : ℝ → (Fin n → ℝ) →ₗ[ℝ] ℝ := fun c => LinearMap.proj j + c • LinearMap.proj k
  have key : ∀ c : ℝ, volume ((LinearMap.ker (L c) : Submodule ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)) = 0 :=
    fun c => Measure.addHaar_submodule _ _ (by
      intro h
      have : Pi.single j (1 : ℝ) ∈ LinearMap.ker (L c) := h ▸ Submodule.mem_top
      simp [L, hjk.symm] at this)
  refine hac (measure_mono_null ?_ (measure_union_null (key (-1)) (key 1)))
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy
  rcases abs_eq_abs.1 hy with h | h
  · left; simp [L, LinearMap.mem_ker, h]
  · right; simp [L, LinearMap.mem_ker, h]

/-- Third-order Taylor lower bound for the Gaussian kernel on `x² ≤ 2`. -/
lemma exp_lower (x : ℝ) (hx : x ^ 2 ≤ 2) :
    1 - x ^ 2 / 2 + x ^ 4 / 8 - x ^ 6 / 36 ≤ Real.exp (-(x ^ 2) / 2) := by
  have h := Real.exp_bound (x := -(x ^ 2) / 2)
    (by rw [abs_le]; constructor <;> nlinarith [sq_nonneg x]) (n := 3) (by norm_num)
  have h' := (abs_le.1 h).1
  simp [Finset.sum_range_succ, Nat.factorial] at h'
  have habs : |-x ^ 2 / 2| = x ^ 2 / 2 := by
    rw [abs_of_nonpos (by nlinarith [sq_nonneg x])]; ring
  have e1 : (x ^ 2 / 2) ^ 3 * (4 / (6 * 3)) = x ^ 6 / 36 := by ring
  have e2 : (-x ^ 2 / 2) ^ 2 / 2 = x ^ 4 / 8 := by ring
  rw [habs, e1, e2] at h'
  have e3 : -(x ^ 2) / 2 = -x ^ 2 / 2 := by ring
  rw [e3]
  linarith

/-- Lower bound for the standard normal density on `[-1, 1]`. -/
lemma pdf_lower (x : ℝ) (hx : x ^ 2 ≤ 1) :
    (1 / 2.5067) * (1 - x ^ 2 / 2 + x ^ 4 / 8 - x ^ 6 / 36) ≤ gaussianPDFReal 0 1 x := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hs : √(2 * Real.pi) ≤ 2.5067 := by
    rw [show (2.5067 : ℝ) = √(2.5067 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d4])
  have hc : 1 / 2.5067 ≤ (√(2 * Real.pi))⁻¹ := by
    rw [one_div]
    exact inv_anti₀ (by positivity) hs
  have hx6 : x ^ 6 ≤ 1 := by
    rw [show x ^ 6 = (x ^ 2) ^ 3 by ring]
    exact pow_le_one₀ (sq_nonneg x) hx
  have hP : 0 ≤ 1 - x ^ 2 / 2 + x ^ 4 / 8 - x ^ 6 / 36 := by nlinarith [sq_nonneg (x ^ 2)]
  have he := exp_lower x (by linarith)
  have e3 : -(x ^ 2) / 2 = -x ^ 2 / 2 := by ring
  rw [e3] at he
  exact mul_le_mul hc (by simpa [pow_two] using he) hP (by positivity)

/-- `∫ g` over `[a, b] ⊆ [-1, 1]` bounds the Gaussian mass of `[a, b]` from below. -/
lemma interval_lower {a b : ℝ} (hab : a ≤ b) (ha : -1 ≤ a) (hb : b ≤ 1) :
    ENNReal.ofReal (∫ x in a..b, (1 / 2.5067) * (1 - x ^ 2 / 2 + x ^ 4 / 8 - x ^ 6 / 36)) ≤
      gaussianReal 0 1 (Set.Icc a b) := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  refine ENNReal.ofReal_le_ofReal (intervalIntegral.integral_mono_on hab
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (integrable_gaussianPDFReal 0 1).intervalIntegrable fun x hx => pdf_lower x ?_)
  nlinarith [hx.1, hx.2]

lemma integral_g (a b : ℝ) :
    ∫ x in a..b, (1 / 2.5067 : ℝ) * (1 - x ^ 2 / 2 + x ^ 4 / 8 - x ^ 6 / 36) =
      (1 / 2.5067) * ((b - a) - (b ^ 3 - a ^ 3) / 6 + (b ^ 5 - a ^ 5) / 40 - (b ^ 7 - a ^ 7) / 252) := by
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_sub]
  all_goals try simp [intervalIntegral.integral_div, integral_pow]
  · left; ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- One coordinate: `P(0.7072 ≤ |x| ≤ 1) ≥ 0.16`. -/
lemma coord_bound : ENNReal.ofReal 0.16 ≤ gaussianReal 0 1 {x : ℝ | 0.7072 ≤ |x| ∧ |x| ≤ 1} := by
  have hsub : Set.Icc (0.7072 : ℝ) 1 ∪ Set.Icc (-1) (-0.7072) ⊆ {x : ℝ | 0.7072 ≤ |x| ∧ |x| ≤ 1} := by
    rintro x (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨by rw [abs_of_nonneg (by linarith)]; exact h1, by rw [abs_of_nonneg (by linarith)]; exact h2⟩
    · exact ⟨by rw [abs_of_neg (by linarith)]; linarith, by rw [abs_of_neg (by linarith)]; linarith⟩
  have hdisj : Disjoint (Set.Icc (0.7072 : ℝ) 1) (Set.Icc (-1) (-0.7072)) :=
    Set.disjoint_left.2 fun x h1 h2 => by linarith [h1.1, h2.2]
  calc ENNReal.ofReal 0.16
      ≤ ENNReal.ofReal (∫ x in (0.7072 : ℝ)..1, (1 / 2.5067 : ℝ) * (1 - x ^ 2 / 2 + x ^ 4 / 8 - x ^ 6 / 36)) +
        ENNReal.ofReal (∫ x in (-1 : ℝ)..(-0.7072), (1 / 2.5067 : ℝ) * (1 - x ^ 2 / 2 + x ^ 4 / 8 - x ^ 6 / 36)) := by
        rw [integral_g, integral_g, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
    _ ≤ gaussianReal 0 1 (Set.Icc 0.7072 1) + gaussianReal 0 1 (Set.Icc (-1) (-0.7072)) :=
        add_le_add (interval_lower (by norm_num) (by norm_num) (by norm_num))
          (interval_lower (by norm_num) (by norm_num) (by norm_num))
    _ = gaussianReal 0 1 (Set.Icc 0.7072 1 ∪ Set.Icc (-1) (-0.7072)) :=
        (measure_union hdisj measurableSet_Icc).symm
    _ ≤ _ := measure_mono hsub

end GEPP51

open GEPP51 GEPPGrowth.Main in
theorem solution (d : ℕ) (hd : 3 ≤ d) (v : GEPPGrowth.Main.Vec (d+1))
    (hv : GEPPGrowth.Main.sqLength v = 1)
    (p : GEPPGrowth.Main.Vec (d+1) → Fin (d+1))
    (hmax : ∀ y, GEPPGrowth.Main.IsMaxPivot y (p y)) :
    (0.16:ℝ)^(d+1) / (2*((d+1:ℕ):ℝ)) ≤
      GEPPGrowth.Main.prob (GEPPGrowth.Main.normal (1 : GEPPGrowth.Main.Mat (d+1)))
        (GEPPGrowth.Main.growthConeWith p v) := by
  set μ := gam (d + 1)
  -- a coordinate carrying at least the average mass of `v`
  obtain ⟨i, hvi⟩ : ∃ i, 1 / ((d + 1 : ℕ) : ℝ) ≤ v i ^ 2 := by
    by_contra h
    push Not at h
    have hlt : ∑ j, v j ^ 2 < ∑ _j : Fin (d + 1), 1 / ((d + 1 : ℕ) : ℝ) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => h j
    unfold sqLength at hv
    rw [hv, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div_cancel (by positivity)] at hlt
    exact lt_irrefl _ hlt
  set S : Set ℝ := {x | 0.7072 ≤ |x| ∧ |x| ≤ 1}
  set B : Set (Vec (d + 1)) := Set.univ.pi (fun _ => S)
  set A : Fin (d + 1) → Set (Vec (d + 1)) := fun k => B ∩ {y | ∀ j, j ≠ k → |y j| < |y k|}
  set Q : Vec (d + 1) → ℝ := fun y => v i * deletedInner i v (ratiosAt y i)
  set H : Set (Vec (d + 1)) := A i ∩ {y | Q y ≤ 0}
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_abs).inter
      (measurableSet_le measurable_abs measurable_const)
  have hAm : ∀ k, MeasurableSet (A k) := by
    intro k
    refine (MeasurableSet.univ_pi fun _ => hSm).inter ?_
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_lt (by fun_prop) (by fun_prop)
  have hQm : Measurable Q := by
    unfold Q deletedInner ratiosAt
    refine Measurable.const_mul (Finset.measurable_sum _ fun j _ => ?_) _
    split_ifs
    · exact measurable_const
    · fun_prop
  have hHm : MeasurableSet H := (hAm i).inter (measurableSet_le hQm measurable_const)
  have hB : ENNReal.ofReal 0.16 ^ (d + 1) ≤ μ B := by
    rw [Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
    exact coord_bound
  have hperm : ∀ k, μ (A k) = μ (A i) := by
    intro k
    have hpre : (fun y : Vec (d + 1) => y ∘ Equiv.swap i k) ⁻¹' A i = A k := by
      ext y
      simp only [Set.mem_preimage, A, B, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
        true_implies, Set.mem_ofPred_eq, Function.comp_apply, Equiv.swap_apply_left]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun j => by simpa using h1 (Equiv.swap i k j), fun j hj => ?_⟩
        have := h2 (Equiv.swap i k j) (by
          rwa [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left])
        simpa using this
      · rintro ⟨h1, h2⟩
        exact ⟨fun j => h1 _, fun j hj => h2 _ (by
          rwa [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right])⟩
    rw [← hpre, (perm_preserving _).measure_preimage (hAm i).nullMeasurableSet]
  have hcover : μ B ≤ ((d + 1 : ℕ) : ℝ≥0∞) * μ (A i) := by
    set N : Set (Vec (d + 1)) := ⋃ j, ⋃ k, ⋃ (_ : j ≠ k), {y : Vec (d + 1) | |y j| = |y k|}
    have hN : μ N = 0 := measure_iUnion_null fun j => measure_iUnion_null fun k =>
      measure_iUnion_null fun hjk => ties_null hjk
    have hsubB : B ⊆ (⋃ k, A k) ∪ N := by
      intro y hy
      by_cases hyN : y ∈ N
      · exact Or.inr hyN
      left
      obtain ⟨k, hk⟩ := Finite.exists_max (fun j => |y j|)
      refine Set.mem_iUnion.2 ⟨k, hy, fun j hj => lt_of_le_of_ne (hk j) (fun h => hyN ?_)⟩
      exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hj, h⟩⟩⟩
    calc μ B ≤ μ ((⋃ k, A k) ∪ N) := measure_mono hsubB
      _ ≤ μ (⋃ k, A k) + μ N := measure_union_le _ _
      _ ≤ ∑ k, μ (A k) := by rw [hN, add_zero]; exact measure_iUnion_fintype_le _ _
      _ = ((d + 1 : ℕ) : ℝ≥0∞) * μ (A i) := by simp [hperm]
  have hflip : μ (A i) ≤ 2 * μ H := by
    set F : Vec (d + 1) → Vec (d + 1) := fun y j => if j = i then y j else -y j
    have hFA : ∀ y ∈ A i, F y ∈ A i := by
      rintro y ⟨hyB, hyT⟩
      refine ⟨fun j _ => ?_, fun j hj => ?_⟩
      · have := hyB j (Set.mem_univ _)
        by_cases hji : j = i <;> simp_all [F, S]
      · have := hyT j hj
        simp_all [F]
    have hFQ : ∀ y, Q (F y) = - Q y := by
      intro y
      simp only [Q, deletedInner, ratiosAt, F]
      rw [← mul_neg, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    have hAH : A i ⊆ H ∪ F ⁻¹' H := by
      intro y hy
      by_cases hq : Q y ≤ 0
      · exact Or.inl ⟨hy, hq⟩
      · refine Or.inr ⟨hFA y hy, ?_⟩
        show Q (F y) ≤ 0
        rw [hFQ]
        linarith
    calc μ (A i) ≤ μ (H ∪ F ⁻¹' H) := measure_mono hAH
      _ ≤ μ H + μ (F ⁻¹' H) := measure_union_le _ _
      _ = 2 * μ H := by
        rw [(flip_preserving i).measure_preimage hHm.nullMeasurableSet, two_mul]
  have hsub : H ⊆ growthConeWith p v := by
    rintro y ⟨⟨hyB, hyT⟩, hQ⟩
    have hp : p y = i := by
      by_contra h
      have h1 := hyT (p y) h
      have h2 : |y i| ≤ |y (p y)| := hmax y i
      linarith
    simp only [growthConeWith, Set.mem_ofPred_eq, hp]
    refine ⟨hvi, ?_, hQ⟩
    have hyi := hyB i (Set.mem_univ _)
    have hj : ∀ j, (1 / 2 : ℝ) ≤ ratiosAt y i j ^ 2 := by
      intro j
      have hyj := hyB j (Set.mem_univ _)
      simp only [S, Set.mem_ofPred_eq] at hyi hyj
      have hpos : 0 < y i ^ 2 := by
        rw [← sq_abs]; nlinarith
      unfold ratiosAt
      rw [div_pow, le_div_iff₀ hpos]
      nlinarith [sq_abs (y j), sq_abs (y i), abs_nonneg (y i), abs_nonneg (y j)]
    unfold sqLength
    calc ((d + 1 : ℕ) : ℝ) / 2 = ∑ _j : Fin (d + 1), (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun j _ => hj j
  have hle : μ H ≤ normal (1 : Mat (d + 1)) (growthConeWith p v) := by
    rw [normal_one]; exact measure_mono hsub
  unfold prob
  have h1 : (0.16 : ℝ) ^ (d + 1) ≤ (μ B).toReal := by
    rw [← ENNReal.ofReal_pow (by norm_num)] at hB
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hB
  have h2 : (μ B).toReal ≤ ((d + 1 : ℕ) : ℝ) * (2 * (μ H).toReal) := by
    have := ENNReal.toReal_mono (by finiteness) (hcover.trans
      (by gcongr : ((d + 1 : ℕ) : ℝ≥0∞) * μ (A i) ≤ ((d + 1 : ℕ) : ℝ≥0∞) * (2 * μ H)))
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat] at this
  have h3 : (μ H).toReal ≤ (normal (1 : Mat (d + 1)) (growthConeWith p v)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) hle
  have hDpos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * ((d + 1 : ℕ) : ℝ))
  push_cast at h2 this ⊢
  linarith
