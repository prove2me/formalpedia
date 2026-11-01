-- Prove2me | solution 1 for DurrettProbability.donsker
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T16:01:14.153624+00:00
-- url     : https://prove2.me/submissions/63a12858-c5c5-4fa9-9b41-1393c2c231bc

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
import Definitions.Def_DurrettProbability_Donsker

set_option autoImplicit false

section part_k2
/-! Random-walk tools for TightPrim (755ffe80): fourth moments of sums of independent centred
bounded variables, and Etemadi's maximal inequality. -/

namespace RW

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma int_of_bdd {f : Ω → ℝ} (B : ℝ) (hf : Measurable f) (hB : ∀ ω, |f ω| ≤ B) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hB ω)

/-- second and fourth moments of a sum of independent centred bounded variables. -/
lemma moments (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (C : ℝ) (hb : ∀ i ω, |Y i ω| ≤ C) (h0 : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (σ2 M4 : ℝ) (h2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ σ2) (h4 : ∀ i, ∫ ω, Y i ω ^ 4 ∂μ ≤ M4)
    (j : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range j, Y i ω) ^ 2 ∂μ ≤ j * σ2 ∧
    ∫ ω, (∑ i ∈ Finset.range j, Y i ω) ^ 4 ∂μ ≤ 3 * j ^ 2 * σ2 ^ 2 + j * M4 := by
  have hσ : 0 ≤ σ2 := (integral_nonneg fun ω => sq_nonneg (Y 0 ω)).trans (h2 0)
  induction j with
  | zero => simp [hσ]
  | succ j ih =>
    set T : Ω → ℝ := fun ω => ∑ i ∈ Finset.range j, Y i ω with hTdef
    have hT : Measurable T := Finset.measurable_sum _ fun i _ => hmeas i
    have hTb : ∀ ω, |T ω| ≤ j * C := by
      intro ω
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hb i ω).trans ?_
      simp
    have hind' : IndepFun T (Y j) μ := by
      have := hind.indepFun_finsetSum_of_notMem hmeas (s := Finset.range j) (i := j) (by simp)
      convert this using 1
      funext ω; simp [hTdef, Finset.sum_apply]
    have hI : ∀ a b : ℕ, Integrable (fun ω => T ω ^ a * Y j ω ^ b) μ := fun a b =>
      int_of_bdd ((j * C) ^ a * C ^ b) ((hT.pow_const a).mul ((hmeas j).pow_const b))
        fun ω => by
          rw [abs_mul, abs_pow, abs_pow]
          exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hTb ω) a)
            (pow_le_pow_left₀ (abs_nonneg _) (hb j ω) b) (by positivity)
            (pow_nonneg ((abs_nonneg _).trans (hTb ω)) a)
    have hE : ∀ a b : ℕ, ∫ ω, T ω ^ a * Y j ω ^ b ∂μ =
        (∫ ω, T ω ^ a ∂μ) * ∫ ω, Y j ω ^ b ∂μ := fun a b =>
      (hind'.comp (measurable_id.pow_const a) (measurable_id.pow_const b)).integral_mul_eq_mul_integral
        (hT.pow_const a).aestronglyMeasurable ((hmeas j).pow_const b).aestronglyMeasurable
    have hexp : ∀ n : ℕ, ∫ ω, (T ω + Y j ω) ^ n ∂μ = ∑ m ∈ Finset.range (n + 1),
        (∫ ω, T ω ^ m ∂μ) * (∫ ω, Y j ω ^ (n - m) ∂μ) * n.choose m := by
      intro n
      simp_rw [add_pow]
      rw [integral_finsetSum _ fun m _ => (hI m (n - m)).mul_const _]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [integral_mul_const, hE]
    have i1 : ∫ ω, T ω ∂μ = 0 := by
      rw [hTdef, integral_finsetSum _ fun i _ => int_of_bdd C (hmeas i) (hb i)]
      simp [h0]
    have hsum : ∀ ω, ∑ i ∈ Finset.range (j + 1), Y i ω = T ω + Y j ω :=
      fun ω => Finset.sum_range_succ _ _
    simp only [hsum, hexp]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, zero_add]
    norm_num only [pow_zero, pow_one, integral_const, probReal_univ, smul_eq_mul, mul_one,
      one_mul, zero_mul, i1, h0]
    have hT2 : 0 ≤ ∫ ω, T ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have hY2 : 0 ≤ ∫ ω, Y j ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    obtain ⟨ih1, ih2⟩ := ih
    change ∫ ω, T ω ^ 2 ∂μ ≤ _ at ih1
    have hm := mul_le_mul ih1 (h2 j) hY2 (by positivity)
    change ∫ ω, T ω ^ 4 ∂μ ≤ _ at ih2
    have h4j := h4 j
    have h2j := h2 j
    push_cast
    constructor <;> nlinarith

/-- partial sums `S_j = ∑_{i<j} Y_i`. -/
noncomputable def psum (Y : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range j, Y i ω

/-- Etemadi's maximal inequality. -/
lemma etemadi (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (L : ℕ) (x : ℝ) (q : ENNReal)
    (hq : ∀ j ≤ L, μ {ω | x ≤ |psum Y j ω|} ≤ q) :
    μ {ω | ∃ j ≤ L, 3 * x ≤ |psum Y j ω|} ≤ 3 * q := by
  classical
  let F : ∀ j : ℕ, (Finset.range j → ℝ) → (ℕ → ℝ) :=
    fun j v i => if h : i ∈ Finset.range j then v ⟨i, h⟩ else 0
  have hF : ∀ j, Measurable (F j) := fun j => measurable_pi_lambda _ fun i => by
    by_cases h : i ∈ Finset.range j
    · simp only [F, dif_pos h]; exact measurable_pi_apply _
    · simp only [F, dif_neg h]; exact measurable_const
  let V1 : ∀ j, Ω → (Finset.range j → ℝ) := fun j ω i => Y i ω
  have hV1 : ∀ j, Measurable (V1 j) := fun j => measurable_pi_lambda _ fun i => hmeas i
  have hFV : ∀ j ω, ∀ i' ≤ j, ∑ i ∈ Finset.range i', F j (V1 j ω) i = psum Y i' ω := by
    intro j ω i' hi'
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i ∈ Finset.range j := Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hi')
    simp only [F, V1, dif_pos this]
  have hV2 : ∀ j ≤ L, ∀ ω, (∑ i : Finset.Ico j L, Y i ω) = psum Y L ω - psum Y j ω := by
    intro j hj ω
    rw [Finset.sum_coe_sort (Finset.Ico j L) (fun i => Y i ω), psum, psum,
      ← Finset.sum_range_add_sum_Ico _ hj]
    ring
  have hg : ∀ m, Measurable fun y : ℕ → ℝ => |∑ i ∈ Finset.range m, y i| := fun m =>
    continuous_abs.measurable.comp (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  let s : ℕ → Set (ℕ → ℝ) := fun j => {y | 3 * x ≤ |∑ i ∈ Finset.range j, y i| ∧
    ∀ i' ∈ Finset.range j, |∑ i ∈ Finset.range i', y i| < 3 * x}
  have hsm : ∀ j, MeasurableSet (s j) := by
    intro j
    have : s j = {y | 3 * x ≤ |∑ i ∈ Finset.range j, y i|} ∩
        ⋂ i' ∈ Finset.range j, {y | |∑ i ∈ Finset.range i', y i| < 3 * x} := by
      ext y; simp [s]
    rw [this]
    exact (measurableSet_le measurable_const (hg j)).inter
      (Finset.measurableSet_biInter _ fun i' _ => measurableSet_lt (hg i') measurable_const)
  let E : ℕ → Set Ω := fun j => (F j ∘ V1 j) ⁻¹' (s j)
  have hEm : ∀ j, MeasurableSet (E j) := fun j => ((hF j).comp (hV1 j)) (hsm j)
  let D : ℕ → Set Ω := fun j =>
    ((fun v : Finset.Ico j L → ℝ => ∑ i, v i) ∘ (fun ω (i : Finset.Ico j L) => Y i ω)) ⁻¹'
      {r | 2 * x ≤ |r|}
  have hind2 : ∀ j, μ (E j ∩ D j) = μ (E j) * μ (D j) := by
    intro j
    have h1 := hind.indepFun_finset (Finset.range j) (Finset.Ico j L)
      (Finset.disjoint_left.2 fun i hi hi' => by
        simp only [Finset.mem_range, Finset.mem_Ico] at hi hi'; omega) hmeas
    have h2 := h1.comp (hF j) (Finset.measurable_sum Finset.univ fun i _ => measurable_pi_apply i)
    exact h2.measure_inter_preimage_eq_mul _ _ (hsm j)
      (measurableSet_le measurable_const continuous_abs.measurable)
  have hD : ∀ j ≤ L, μ (D j) ≤ 2 * q := by
    intro j hj
    have hsub : D j ⊆ {ω | x ≤ |psum Y L ω|} ∪ {ω | x ≤ |psum Y j ω|} := by
      intro ω hω
      have hω' : 2 * x ≤ |∑ i : Finset.Ico j L, Y i ω| := hω
      rw [hV2 j hj ω] at hω'
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
      have := abs_sub (psum Y L ω) (psum Y j ω)
      linarith [hcon.1, hcon.2]
    calc μ (D j) ≤ _ := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ q + q := add_le_add (hq L le_rfl) (hq j hj)
      _ = 2 * q := by ring
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (L + 1))) E := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω ha hb
    have ha' : F a (V1 a ω) ∈ s a := ha
    have hb' : F b (V1 b ω) ∈ s b := hb
    simp only [s, Set.mem_setOf_eq] at ha' hb'
    rcases lt_or_gt_of_ne hab with h | h
    · have h1 := ha'.1
      have h2 := hb'.2 a (Finset.mem_range.2 h)
      rw [hFV a ω a le_rfl] at h1; rw [hFV b ω a h.le] at h2; linarith
    · have h1 := hb'.1
      have h2 := ha'.2 b (Finset.mem_range.2 h)
      rw [hFV b ω b le_rfl] at h1; rw [hFV a ω b h.le] at h2; linarith
  have hsub : {ω | ∃ j ≤ L, 3 * x ≤ |psum Y j ω|} ⊆
      {ω | x ≤ |psum Y L ω|} ∪ ⋃ j ∈ Finset.range (L + 1), (E j ∩ D j) := by
    rintro ω ⟨j, hjL, hj⟩
    by_cases hL : x ≤ |psum Y L ω|
    · left; exact hL
    · right
      have hex : ∃ j, j ≤ L ∧ 3 * x ≤ |psum Y j ω| := ⟨j, hjL, hj⟩
      have hj0 := Nat.find_spec hex
      have hmin : ∀ i < Nat.find hex, ¬ (i ≤ L ∧ 3 * x ≤ |psum Y i ω|) :=
        fun i hi => Nat.find_min hex hi
      refine Set.mem_biUnion (x := Nat.find hex)
        (Finset.mem_coe.2 (Finset.mem_range.2 (by omega))) ⟨?_, ?_⟩
      · show F (Nat.find hex) (V1 (Nat.find hex) ω) ∈ s (Nat.find hex)
        refine ⟨by rw [hFV _ ω _ le_rfl]; exact hj0.2, fun i' hi' => ?_⟩
        rw [hFV _ ω i' (Finset.mem_range.1 hi').le]
        have := hmin i' (Finset.mem_range.1 hi')
        push_neg at this
        exact this (by have := Finset.mem_range.1 hi'; omega)
      · show 2 * x ≤ |∑ i : Finset.Ico (Nat.find hex) L, Y i ω|
        rw [hV2 _ hj0.1 ω]
        push_neg at hL
        have := abs_sub_abs_le_abs_sub (psum Y (Nat.find hex) ω) (psum Y L ω)
        rw [abs_sub_comm] at this
        linarith [hj0.2]
  calc μ {ω | ∃ j ≤ L, 3 * x ≤ |psum Y j ω|}
      ≤ μ ({ω | x ≤ |psum Y L ω|} ∪ ⋃ j ∈ Finset.range (L + 1), (E j ∩ D j)) := measure_mono hsub
    _ ≤ μ {ω | x ≤ |psum Y L ω|} + ∑ j ∈ Finset.range (L + 1), μ (E j ∩ D j) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ q + ∑ j ∈ Finset.range (L + 1), μ (E j) * (2 * q) := by
        refine add_le_add (hq L le_rfl) (Finset.sum_le_sum fun j hj => ?_)
        rw [hind2 j]
        gcongr
        exact hD j (by have := Finset.mem_range.1 hj; omega)
    _ = q + μ (⋃ j ∈ Finset.range (L + 1), E j) * (2 * q) := by
        rw [← Finset.sum_mul, measure_biUnion_finset hdisj fun j _ => hEm j]
    _ ≤ q + 1 * (2 * q) := by gcongr; exact prob_le_one
    _ = 3 * q := by ring

lemma markov4 (Z : Ω → ℝ) (hint : Integrable (fun ω => Z ω ^ 4) μ) {x : ℝ} (hx : 0 < x) :
    μ {ω | x ≤ |Z ω|} ≤ ENNReal.ofReal ((∫ ω, Z ω ^ 4 ∂μ) / x ^ 4) := by
  have hx4 : 0 < x ^ 4 := by positivity
  have h := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun ω => by positivity : 0 ≤ᵐ[μ] fun ω => Z ω ^ 4) hint (x ^ 4)
  have hsub : {ω | x ≤ |Z ω|} ⊆ {ω | x ^ 4 ≤ Z ω ^ 4} := by
    intro ω hω
    have h1 : x ^ 4 ≤ |Z ω| ^ 4 := pow_le_pow_left₀ hx.le hω 4
    rwa [Even.pow_abs (⟨2, rfl⟩ : Even 4)] at h1
  calc μ {ω | x ≤ |Z ω|} ≤ μ {ω | x ^ 4 ≤ Z ω ^ 4} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | x ^ 4 ≤ Z ω ^ 4}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal ((∫ ω, Z ω ^ 4 ∂μ) / x ^ 4) :=
        ENNReal.ofReal_le_ofReal (by rw [le_div_iff₀ hx4]; linarith [h])

/-- maximal inequality for one block of a centred bounded independent sequence. -/
lemma block_bound (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (B : ℝ) (hb : ∀ i ω, |Y i ω| ≤ B) (h0 : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    (σ2 : ℝ) (h2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ σ2) (a L : ℕ) {x : ℝ} (hx : 0 < x) :
    μ {ω | ∃ l ≤ L, 3 * x ≤ |psum (Y ∘ (fun i => a + i)) l ω|} ≤
      3 * ENNReal.ofReal ((3 * L ^ 2 * σ2 ^ 2 + L * (B ^ 2 * σ2)) / x ^ 4) := by
  have hσ : 0 ≤ σ2 := (integral_nonneg fun ω => sq_nonneg (Y 0 ω)).trans (h2 0)
  have hind' : iIndepFun (Y ∘ (fun i => a + i)) μ := iIndepFun.precomp (g := fun i : ℕ => a + i) (add_right_injective a) hind
  have hmeas' : ∀ i, Measurable ((Y ∘ (fun i => a + i)) i) := fun i => hmeas _
  have hb' : ∀ i ω, |(Y ∘ (fun i => a + i)) i ω| ≤ B := fun i ω => hb _ ω
  have h4 : ∀ i, ∫ ω, (Y ∘ (fun i => a + i)) i ω ^ 4 ∂μ ≤ B ^ 2 * σ2 := by
    intro i
    have hY := hmeas (a + i)
    have hi2 : Integrable (fun ω => Y (a + i) ω ^ 2) μ :=
      int_of_bdd (B ^ 2) (hY.pow_const 2) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb _ ω) 2
    have hi4 : Integrable (fun ω => Y (a + i) ω ^ 4) μ :=
      int_of_bdd (B ^ 4) (hY.pow_const 4) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb _ ω) 4
    calc ∫ ω, Y (a + i) ω ^ 4 ∂μ ≤ ∫ ω, B ^ 2 * Y (a + i) ω ^ 2 ∂μ := by
          refine integral_mono hi4 (hi2.const_mul _) fun ω => ?_
          have h1 : Y (a + i) ω ^ 2 ≤ B ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb _ ω) 2
          have h2' : 0 ≤ Y (a + i) ω ^ 2 := sq_nonneg _
          show Y (a + i) ω ^ 4 ≤ B ^ 2 * Y (a + i) ω ^ 2
          nlinarith
      _ = B ^ 2 * ∫ ω, Y (a + i) ω ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ B ^ 2 * σ2 := mul_le_mul_of_nonneg_left (h2 _) (sq_nonneg _)
  refine etemadi _ hind' hmeas' L x _ fun j hj => ?_
  have hmom := (moments _ hind' hmeas' B hb' (fun i => h0 _) σ2 (B ^ 2 * σ2)
    (fun i => h2 _) h4 j).2
  have hpm : Measurable (psum (Y ∘ (fun i => a + i)) j) :=
    Finset.measurable_sum _ fun i _ => hmeas' i
  have hint : Integrable (fun ω => psum (Y ∘ (fun i => a + i)) j ω ^ 4) μ := by
    refine int_of_bdd ((j * B) ^ 4) (hpm.pow_const 4) fun ω => ?_
    rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 4
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hb' i ω).trans ?_
    simp
  refine (markov4 _ hint hx).trans (ENNReal.ofReal_le_ofReal ?_)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hjL : (j:ℝ) ≤ L := by exact_mod_cast hj
  have hB2 : 0 ≤ B ^ 2 * σ2 := mul_nonneg (sq_nonneg _) hσ
  refine hmom.trans ?_
  have : (j:ℝ) ^ 2 ≤ (L:ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hjL 2
  nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg σ2),
    mul_le_mul_of_nonneg_right hjL hB2]

/-- truncation at level `τ`. -/
noncomputable def trunc (τ : ℝ) (x : ℝ) : ℝ := if |x| ≤ τ then x else 0

lemma trunc_meas (τ : ℝ) : Measurable (trunc τ) :=
  Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) measurable_id
    measurable_const

lemma trunc_abs {τ : ℝ} (hτ : 0 ≤ τ) (x : ℝ) : |trunc τ x| ≤ τ := by
  unfold trunc; split_ifs with h
  · exact h
  · simpa using hτ

lemma trunc_sq (τ x : ℝ) : trunc τ x ^ 2 ≤ x ^ 2 := by
  unfold trunc; split_ifs
  · exact le_rfl
  · simpa using sq_nonneg x

lemma trunc_tail {τ : ℝ} (hτ : 0 < τ) (x : ℝ) : |x - trunc τ x| ≤ x ^ 2 / τ := by
  unfold trunc; split_ifs with h
  · simp only [sub_self, abs_zero]; positivity
  · push_neg at h
    rw [sub_zero, le_div_iff₀ hτ, ← sq_abs]
    nlinarith [abs_nonneg x]

/-- one-space modulus bound for a centred i.i.d. square-integrable sequence, by truncation at
`τ`, block decomposition and Etemadi's inequality. -/
lemma mod_bound (ξ : ℕ → Ω → ℝ) (hind : iIndepFun ξ μ) (hmeas : ∀ i, Measurable (ξ i))
    (hid : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ) (hL2 : MemLp (ξ 0) 2 μ)
    (h0 : ∫ ω, ξ 0 ω ∂μ = 0) (σ2 : ℝ) (hσ : ∫ ω, ξ 0 ω ^ 2 ∂μ ≤ σ2)
    {τ : ℝ} (hτ : 0 < τ) (Nmax L : ℕ) (hL : 1 ≤ L) {x : ℝ} (hx : 0 < x)
    (hdrift : (L:ℝ) * (σ2 / τ) ≤ x / 2) :
    μ {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ i + L ∧ j ≤ Nmax ∧ x ≤ |psum ξ j ω - psum ξ i ω|} ≤
      Nmax * μ {ω | τ < |ξ 0 ω|} + ((Nmax / L + 1 : ℕ) : ENNReal) *
        (3 * ENNReal.ofReal ((3 * ((2 * L : ℕ) : ℝ) ^ 2 * σ2 ^ 2 +
          ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * σ2)) / (x / 12) ^ 4)) := by
  classical
  set c := ∫ ω, trunc τ (ξ 0 ω) ∂μ with hc
  set Y : ℕ → Ω → ℝ := fun i => (fun r => trunc τ r - c) ∘ ξ i with hY
  have hYind : iIndepFun Y μ := hind.comp (fun _ r => trunc τ r - c)
    (fun _ => (trunc_meas τ).sub_const c)
  have hYm : ∀ i, Measurable (Y i) := fun i => ((trunc_meas τ).sub_const c).comp (hmeas i)
  have htr_int : ∀ i, Integrable (fun ω => trunc τ (ξ i ω)) μ := fun i =>
    int_of_bdd τ ((trunc_meas τ).comp (hmeas i)) fun ω => trunc_abs hτ.le _
  have hcabs : |c| ≤ τ := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => trunc τ (ξ 0 ω)) (C := τ)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact trunc_abs hτ.le _)
    simpa [Real.norm_eq_abs] using this
  have hYb : ∀ i ω, |Y i ω| ≤ 2 * τ := by
    intro i ω
    simp only [hY, Function.comp]
    have := abs_sub (trunc τ (ξ i ω)) c
    linarith [trunc_abs hτ.le (ξ i ω)]
  have hY0 : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    simp only [hY, Function.comp]
    rw [integral_sub (htr_int i) (integrable_const c), integral_const, probReal_univ, one_smul]
    have := ((hid i).comp (trunc_meas τ)).integral_eq
    simp only [Function.comp] at this
    rw [this, hc, sub_self]
  have hY2 : ∀ i, ∫ ω, Y i ω ^ 2 ∂μ ≤ σ2 := by
    intro i
    have e : ∫ ω, Y i ω ^ 2 ∂μ = ∫ ω, (trunc τ (ξ 0 ω) - c) ^ 2 ∂μ := by
      have := ((hid i).comp (((trunc_meas τ).sub_const c).pow_const 2)).integral_eq
      simpa [hY, Function.comp] using this
    rw [e]
    have hsq : Integrable (fun ω => trunc τ (ξ 0 ω) ^ 2) μ :=
      int_of_bdd (τ ^ 2) (((trunc_meas τ).comp (hmeas 0)).pow_const 2) fun ω => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (trunc_abs hτ.le _) 2
    have e2 : ∫ ω, (trunc τ (ξ 0 ω) - c) ^ 2 ∂μ = ∫ ω, trunc τ (ξ 0 ω) ^ 2 ∂μ - c ^ 2 := by
      have hp : ∀ ω, (trunc τ (ξ 0 ω) - c) ^ 2 =
          trunc τ (ξ 0 ω) ^ 2 + ((-2 * c) * trunc τ (ξ 0 ω) + c ^ 2) := fun ω => by ring
      simp only [hp]
      have hg1 : Integrable (fun ω => -2 * c * trunc τ (ξ 0 ω)) μ := (htr_int 0).const_mul _
      have hg : Integrable (fun ω => -2 * c * trunc τ (ξ 0 ω) + c ^ 2) μ :=
        hg1.add (integrable_const _)
      rw [integral_add hsq hg, integral_add hg1 (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, one_smul, ← hc]
      ring
    rw [e2]
    have h1 : ∫ ω, trunc τ (ξ 0 ω) ^ 2 ∂μ ≤ ∫ ω, ξ 0 ω ^ 2 ∂μ :=
      integral_mono hsq hL2.integrable_sq fun ω => trunc_sq τ _
    nlinarith [sq_nonneg c]
  have hcσ : |c| ≤ σ2 / τ := by
    have hξi : Integrable (ξ 0) μ := hL2.integrable one_le_two
    have e : c = -∫ ω, (ξ 0 ω - trunc τ (ξ 0 ω)) ∂μ := by
      rw [integral_sub hξi (htr_int 0), h0, hc]; ring
    rw [e, abs_neg]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |ξ 0 ω - trunc τ (ξ 0 ω)| ∂μ ≤ ∫ ω, ξ 0 ω ^ 2 / τ ∂μ :=
          integral_mono (hξi.sub (htr_int 0)).abs (hL2.integrable_sq.div_const τ)
            fun ω => trunc_tail hτ _
      _ = (∫ ω, ξ 0 ω ^ 2 ∂μ) / τ := integral_div _ _
      _ ≤ σ2 / τ := div_le_div_of_nonneg_right hσ hτ.le
  -- the event inclusion
  set Blk : ℕ → Set Ω := fun b =>
    {ω | ∃ l ≤ 2 * L, 3 * (x / 12) ≤ |psum (Y ∘ (fun i => b * L + i)) l ω|} with hBlk
  have hsub : {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ i + L ∧ j ≤ Nmax ∧ x ≤ |psum ξ j ω - psum ξ i ω|} ⊆
      (⋃ i ∈ Finset.range Nmax, {ω | τ < |ξ i ω|}) ∪ ⋃ b ∈ Finset.range (Nmax / L + 1), Blk b := by
    rintro ω ⟨i, j, hij, hjL, hjN, hxij⟩
    by_cases hbad : ∃ i' < Nmax, τ < |ξ i' ω|
    · obtain ⟨i', hi', h'⟩ := hbad
      left; exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hi')) h'
    · right
      push_neg at hbad
      have hpsum : ∀ k ≤ Nmax, psum ξ k ω = psum Y k ω + k * c := by
        intro k hk
        have e : ∀ i ∈ Finset.range k, ξ i ω = Y i ω + c := fun i hi => by
          simp only [hY, Function.comp, trunc,
            if_pos (hbad i (by have := Finset.mem_range.1 hi; omega))]
          ring
        rw [psum, psum, Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
      have hdiff : x / 2 ≤ |psum Y j ω - psum Y i ω| := by
        rw [hpsum j hjN, hpsum i (hij.trans hjN)] at hxij
        have hji : ((j:ℝ) - i) ≤ L := by
          have : (j:ℝ) ≤ i + L := by exact_mod_cast hjL
          linarith
        have hji0 : 0 ≤ (j:ℝ) - i := by
          have : (i:ℝ) ≤ j := by exact_mod_cast hij
          linarith
        have hcd : |((j:ℝ) - i) * c| ≤ L * (σ2 / τ) := by
          rw [abs_mul, abs_of_nonneg hji0]
          exact mul_le_mul hji hcσ (abs_nonneg _) (Nat.cast_nonneg _)
        have e : psum Y j ω + j * c - (psum Y i ω + i * c) =
            (psum Y j ω - psum Y i ω) + ((j:ℝ) - i) * c := by ring
        rw [e] at hxij
        have := abs_add_le (psum Y j ω - psum Y i ω) (((j:ℝ) - i) * c)
        linarith
      set b := i / L with hb
      have ha : b * L ≤ i := Nat.div_mul_le_self i L
      have ha2 : i < b * L + L := Nat.lt_div_mul_add hL
      have hshift : ∀ k, b * L ≤ k →
          psum (Y ∘ (fun i => b * L + i)) (k - b * L) ω = psum Y k ω - psum Y (b * L) ω := by
        intro k hk
        have : psum Y k ω = psum Y (b * L) ω + psum (Y ∘ (fun i => b * L + i)) (k - b * L) ω := by
          simp only [psum, Function.comp]
          rw [← Finset.sum_range_add (fun i => Y i ω) (b * L) (k - b * L), Nat.add_sub_cancel' hk]
        linarith
      refine Set.mem_biUnion (x := b) (Finset.mem_coe.2 (Finset.mem_range.2 ?_)) ?_
      · have : b ≤ Nmax / L := Nat.div_le_div_right (hij.trans hjN)
        omega
      · by_contra hno
        simp only [hBlk, Set.mem_setOf_eq, not_exists, not_and, not_le] at hno
        have h1 := hno (j - b * L) (by omega)
        have h2 := hno (i - b * L) (by omega)
        rw [hshift j (by omega)] at h1
        rw [hshift i ha] at h2
        have := abs_sub_le (psum Y j ω) (psum Y (b * L) ω) (psum Y i ω)
        rw [abs_sub_comm (psum Y (b * L) ω)] at this
        linarith
  calc μ {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ i + L ∧ j ≤ Nmax ∧ x ≤ |psum ξ j ω - psum ξ i ω|}
      ≤ μ ((⋃ i ∈ Finset.range Nmax, {ω | τ < |ξ i ω|}) ∪
          ⋃ b ∈ Finset.range (Nmax / L + 1), Blk b) := measure_mono hsub
    _ ≤ μ (⋃ i ∈ Finset.range Nmax, {ω | τ < |ξ i ω|}) +
          μ (⋃ b ∈ Finset.range (Nmax / L + 1), Blk b) := measure_union_le _ _
    _ ≤ ∑ i ∈ Finset.range Nmax, μ {ω | τ < |ξ i ω|} +
          ∑ b ∈ Finset.range (Nmax / L + 1), μ (Blk b) :=
        add_le_add (measure_biUnion_finset_le _ _) (measure_biUnion_finset_le _ _)
    _ ≤ ∑ i ∈ Finset.range Nmax, μ {ω | τ < |ξ 0 ω|} +
          ∑ b ∈ Finset.range (Nmax / L + 1), (3 * ENNReal.ofReal ((3 * ((2 * L : ℕ) : ℝ) ^ 2 *
            σ2 ^ 2 + ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * σ2)) / (x / 12) ^ 4)) := by
        refine add_le_add (le_of_eq (Finset.sum_congr rfl fun i _ =>
          (hid i).measure_mem_eq (measurableSet_lt measurable_const continuous_abs.measurable)))
          (Finset.sum_le_sum fun b _ => ?_)
        exact block_bound Y hYind hYm (2 * τ) hYb hY0 σ2 hY2 (b * L) (2 * L) (by positivity)
    _ = _ := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
          nsmul_eq_mul, nsmul_eq_mul]

section Tri

variable {Ωs : ℕ → Type*} [∀ n, MeasurableSpace (Ωs n)]

/-- lattice modulus tightness of the scaled partial-sum process of a triangular array of centred
i.i.d. rows with bounded variances and a Lindeberg-type jump condition. -/
lemma rw_tight (P : ∀ n, Measure (Ωs n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (ξ : ∀ n, ℕ → Ωs n → ℝ) (hind : ∀ n, iIndepFun (ξ n) (P n))
    (hmeas : ∀ n i, Measurable (ξ n i)) (hid : ∀ n i, IdentDistrib (ξ n i) (ξ n 0) (P n) (P n))
    (hL2 : ∀ n, MemLp (ξ n 0) 2 (P n)) (h0 : ∀ n, ∫ ω, ξ n 0 ω ∂(P n) = 0)
    (σ2 : ℝ) (hσ : ∀ᶠ n in atTop, ∫ ω, ξ n 0 ω ^ 2 ∂(P n) ≤ σ2)
    (hUI : ∀ θ : ℝ, 0 < θ → Tendsto (fun n : ℕ => (n : ENNReal) *
      P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) atTop (𝓝 0))
    (T : ℝ) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, P n {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧
      (j:ℝ) ≤ T * n ∧ ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ≤
        ENNReal.ofReal η := by
  set s' := max σ2 1 with hs'
  have hs'1 : 1 ≤ s' := le_max_right _ _
  have hs'0 : 0 < s' := by linarith
  set K := 6 * 12 ^ 4 * T / ε ^ 4 with hK
  have hK0 : 0 < K := by positivity
  set θ := Real.sqrt (η / (64 * K * s')) with hθ
  have hθ0 : 0 < θ := Real.sqrt_pos.2 (by positivity)
  have hθ2 : θ ^ 2 = η / (64 * K * s') := Real.sq_sqrt (by positivity)
  set δ := min T (min (η / (192 * K * s' ^ 2)) (θ * ε / (4 * s'))) with hδ
  have hδ0 : 0 < δ := lt_min hT (lt_min (by positivity) (by positivity))
  have hδT : δ ≤ T := min_le_left _ _
  have hδ1 : δ ≤ η / (192 * K * s' ^ 2) := (min_le_right _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ θ * ε / (4 * s') := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ0, ?_⟩
  have hJ : ∀ᶠ n : ℕ in atTop, ((⌈T⌉₊ : ℕ) : ENNReal) *
      ((n : ENNReal) * P n {ω | θ * Real.sqrt n < |ξ n 0 ω|}) < ENNReal.ofReal (η / 2) := by
    have := ENNReal.Tendsto.const_mul (a := ((⌈T⌉₊ : ℕ) : ENNReal)) (hUI θ hθ0)
      (Or.inr (ENNReal.natCast_ne_top _))
    rw [mul_zero] at this
    exact (tendsto_order.1 this).2 _ (ENNReal.ofReal_pos.2 (by linarith))
  filter_upwards [hJ, hσ, eventually_ge_atTop ⌈1 / δ⌉₊, eventually_ge_atTop 1]
    with n hJn hσn hnδ hn1
  have := hP n
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hδn : 1 ≤ δ * n := by
    have h1 : 1 / δ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnδ)
    rw [div_le_iff₀ hδ0] at h1; linarith
  set Nmax := ⌊T * n⌋₊ with hNmax
  set L := ⌈δ * n⌉₊ with hLdef
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by positivity)).ne'
  have hLr : (L:ℝ) ≤ 2 * δ * n := by
    have := Nat.ceil_lt_add_one (by positivity : 0 ≤ δ * n); linarith
  have hLr' : δ * n ≤ L := Nat.le_ceil _
  have hNr : (Nmax:ℝ) ≤ T * n := Nat.floor_le (by positivity)
  set τ := θ * Real.sqrt n with hτdef
  have hτ : 0 < τ := by positivity
  set x := ε * Real.sqrt n with hxdef
  have hx : 0 < x := by positivity
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
  have hdrift : (L:ℝ) * (s' / τ) ≤ x / 2 := by
    rw [mul_div_assoc', div_le_iff₀ hτ]
    have hxτ : x / 2 * τ = ε * θ * n / 2 := by
      rw [hxdef, hτdef, show ε * Real.sqrt n / 2 * (θ * Real.sqrt n) =
        ε * θ * (Real.sqrt n * Real.sqrt n) / 2 by ring, hsn]
    rw [hxτ]
    calc (L:ℝ) * s' ≤ 2 * δ * n * s' := mul_le_mul_of_nonneg_right hLr hs'0.le
      _ ≤ 2 * (θ * ε / (4 * s')) * n * s' := by gcongr
      _ = ε * θ * n / 2 := by field_simp; ring
  have hmb := mod_bound (ξ n) (hind n) (hmeas n) (hid n) (hL2 n) (h0 n) s'
    (hσn.trans (le_max_left _ _)) hτ Nmax L hL1 hx hdrift
  have hsub : {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧
      (j:ℝ) ≤ T * n ∧ ε * Real.sqrt n ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} ⊆
      {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ i + L ∧ j ≤ Nmax ∧ x ≤ |psum (ξ n) j ω - psum (ξ n) i ω|} := by
    rintro ω ⟨i, j, hij, hj1, hj2, hjx⟩
    refine ⟨i, j, hij, ?_, Nat.le_floor hj2, hjx⟩
    have : (j:ℝ) ≤ i + L := hj1.trans (by linarith [hLr'])
    exact_mod_cast this
  refine (measure_mono hsub).trans (hmb.trans ?_)
  have hjump : (Nmax : ENNReal) * P n {ω | τ < |ξ n 0 ω|} ≤ ENNReal.ofReal (η / 2) := by
    refine le_trans ?_ hJn.le
    rw [← mul_assoc]
    gcongr
    have : Nmax ≤ ⌈T⌉₊ * n := by
      have h1 : (Nmax:ℝ) ≤ ⌈T⌉₊ * n :=
        hNr.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) hnpos.le)
      exact_mod_cast h1
    exact_mod_cast this
  set Z := 48 * δ * s' ^ 2 + 16 * θ ^ 2 * s' with hZ
  have hZ0 : 0 < Z := by positivity
  set r := (3 * ((2 * L : ℕ) : ℝ) ^ 2 * s' ^ 2 + ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * s')) /
    (x / 12) ^ 4 with hr
  have hr0 : 0 ≤ r := by positivity
  have hx4 : (x / 12) ^ 4 = ε ^ 4 * (n:ℝ) ^ 2 / 12 ^ 4 := by
    rw [hxdef, div_pow, mul_pow, show Real.sqrt n ^ 4 = (Real.sqrt n * Real.sqrt n) ^ 2 by ring, hsn]
  have h2L : ((2 * L : ℕ) : ℝ) ≤ 4 * δ * n := by push_cast; linarith
  have hτ2 : (2 * τ) ^ 2 = 4 * θ ^ 2 * n := by
    rw [hτdef, show (2 * (θ * Real.sqrt n)) ^ 2 = 4 * θ ^ 2 * (Real.sqrt n * Real.sqrt n) by ring,
      hsn]
  have hnum : 3 * ((2 * L : ℕ) : ℝ) ^ 2 * s' ^ 2 + ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * s') ≤
      (n:ℝ) ^ 2 * δ * Z := by
    rw [hτ2]
    have h0' : 0 ≤ ((2 * L : ℕ) : ℝ) := Nat.cast_nonneg _
    calc 3 * ((2 * L : ℕ) : ℝ) ^ 2 * s' ^ 2 + ((2 * L : ℕ) : ℝ) * (4 * θ ^ 2 * n * s')
        ≤ 3 * (4 * δ * n) ^ 2 * s' ^ 2 + (4 * δ * n) * (4 * θ ^ 2 * n * s') := by
          gcongr
      _ = (n:ℝ) ^ 2 * δ * Z := by rw [hZ]; ring
  have hrb : r ≤ 12 ^ 4 * δ * Z / ε ^ 4 := by
    calc r = (3 * ((2 * L : ℕ) : ℝ) ^ 2 * s' ^ 2 + ((2 * L : ℕ) : ℝ) * ((2 * τ) ^ 2 * s')) /
          (ε ^ 4 * (n:ℝ) ^ 2 / 12 ^ 4) := by rw [hr, hx4]
      _ ≤ ((n:ℝ) ^ 2 * δ * Z) / (ε ^ 4 * (n:ℝ) ^ 2 / 12 ^ 4) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = 12 ^ 4 * δ * Z / ε ^ 4 := by field_simp
  have hk : (((Nmax / L + 1 : ℕ)) : ℝ) ≤ 2 * T / δ := by
    push_cast
    have h1 : ((Nmax / L : ℕ) : ℝ) ≤ (Nmax : ℝ) / L := Nat.cast_div_le
    have h2 : (Nmax : ℝ) / L ≤ T / δ := by
      rw [div_le_div_iff₀ (by positivity) hδ0]
      calc (Nmax:ℝ) * δ ≤ T * n * δ := mul_le_mul_of_nonneg_right hNr hδ0.le
        _ = T * (δ * n) := by ring
        _ ≤ T * L := mul_le_mul_of_nonneg_left hLr' hT.le
    have h3 : 1 ≤ T / δ := by rw [le_div_iff₀ hδ0]; linarith
    have : 2 * T / δ = T / δ + T / δ := by ring
    linarith
  have hblock : (((Nmax / L + 1 : ℕ)) : ENNReal) * (3 * ENNReal.ofReal r) ≤
      ENNReal.ofReal (η / 2) := by
    rw [← ENNReal.ofReal_natCast, show (3 : ENNReal) = ENNReal.ofReal 3 by simp,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hk0 : (0:ℝ) ≤ ((Nmax / L + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (((Nmax / L + 1 : ℕ)) : ℝ) * (3 * r) ≤ (2 * T / δ) * (3 * (12 ^ 4 * δ * Z / ε ^ 4)) :=
          mul_le_mul hk (by linarith) (by positivity) (by positivity)
      _ = K * (48 * δ * s' ^ 2) + K * (16 * θ ^ 2 * s') := by rw [hK, hZ]; field_simp; ring
      _ ≤ K * (48 * (η / (192 * K * s' ^ 2)) * s' ^ 2) + K * (16 * θ ^ 2 * s') := by gcongr
      _ = η / 2 := by rw [hθ2]; field_simp; ring
  calc (Nmax : ENNReal) * P n {ω | τ < |ξ n 0 ω|} +
        (((Nmax / L + 1 : ℕ)) : ENNReal) * (3 * ENNReal.ofReal r)
      ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := add_le_add hjump hblock
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring

end Tri

end RW

namespace DonskerK

open MeasureTheory ProbabilityTheory Filter Topology

/-- the Lindeberg-type tail condition for a fixed square-integrable law. -/
lemma tail_condition {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY : Measurable Y) (hint : Integrable (fun ω => Y ω ^ 2) P)
    (θ : ℝ) (hθ : 0 < θ) :
    Tendsto (fun n : ℕ => (n : ENNReal) * P {ω | θ * Real.sqrt n < |Y ω|}) atTop (𝓝 0) := by
  set F : Ω → ENNReal := fun ω => ENNReal.ofReal (Y ω ^ 2 / θ ^ 2) with hF
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp ((hY.pow_const 2).div_const _)
  set A : ℕ → Set Ω := fun n => {ω | θ * Real.sqrt n < |Y ω|} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hY)
  set g : ℕ → Ω → ENNReal := fun n => (A n).indicator F with hg
  have hle : ∀ n : ℕ, (n : ENNReal) * P (A n) ≤ ∫⁻ ω, g n ω ∂P := by
    intro n
    rw [← lintegral_indicator_const (hAm n), hg]
    refine lintegral_mono fun ω => ?_
    beta_reduce
    by_cases h : ω ∈ A n
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, hF]
      have h1 : θ * Real.sqrt n < |Y ω| := h
      have h2 : (θ * Real.sqrt n) ^ 2 < |Y ω| ^ 2 := by
        have : 0 ≤ θ * Real.sqrt n := by positivity
        nlinarith
      have h3 : (n : ℝ) ≤ Y ω ^ 2 / θ ^ 2 := by
        rw [le_div_iff₀ (by positivity), sq_abs] at *
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)] at h2
        linarith
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal h3
    · rw [Set.indicator_of_notMem h]
      exact bot_le
  have hlim : Tendsto (fun n => ∫⁻ ω, g n ω ∂P) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := P) (f := fun _ => 0) F
      (fun n => hFm.indicator (hAm n))
      (fun n => ae_of_all _ fun ω => Set.indicator_le_self _ _ ω) ?_ ?_
    · simpa using this
    · have : ∫⁻ ω, F ω ∂P = ENNReal.ofReal (∫ ω, Y ω ^ 2 / θ ^ 2 ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal (hint.div_const _)
          (ae_of_all _ fun ω => by positivity)).symm
      rw [this]
      exact ENNReal.ofReal_ne_top
    · refine ae_of_all _ fun ω => ?_
      have hev : ∀ᶠ n : ℕ in atTop, ω ∉ A n := by
        have ht : Tendsto (fun n : ℕ => θ * Real.sqrt n) atTop atTop :=
          (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hθ
        filter_upwards [ht.eventually_ge_atTop |Y ω|] with n hn
        simp only [hA, Set.mem_setOf_eq, not_lt]
        exact hn
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      simp [hg, Set.indicator_of_notMem hn]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => bot_le) hle

/-- **Lattice modulus** of the Donsker walk (Billingsley's tightness condition on the lattice). -/
theorem walk_lattice_mod {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (X k))
    (hindep : iIndepFun X P) (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hint : Integrable (fun ω => X 0 ω ^ 2) P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (hvar : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    (ε : ℝ) (hε : 0 < ε) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, P {ω | ∃ i j : ℕ, i ≤ j ∧ (j:ℝ) ≤ i + δ * n ∧
      (j:ℝ) ≤ 2 * n ∧ ε * Real.sqrt n ≤ |RW.psum X j ω - RW.psum X i ω|} ≤
        ENNReal.ofReal η := by
  have hL2 : MemLp (X 0) 2 P :=
    (memLp_two_iff_integrable_sq (hmeas 0).aestronglyMeasurable).2 hint
  exact RW.rw_tight (Ωs := fun _ => Ω) (fun _ => P) (fun _ => inferInstance) (fun _ => X)
    (fun _ => hindep) (fun _ => hmeas) (fun _ => hident) (fun _ => hL2) (fun _ => hmean) 1
    (Eventually.of_forall fun _ => hvar.le) (fun θ hθ => tail_condition (hmeas 0) hint θ hθ)
    2 two_pos ε hε η hη

end DonskerK

end part_k2

section part_k6
open Filter MeasureTheory ProbabilityTheory Complex
open scoped NNReal Topology

namespace DonskerK


lemma norm_prod_sub_prod_le (s : Finset ℕ) (a b : ℕ → ℂ) (ha : ∀ k, ‖a k‖ ≤ 1)
    (hb : ∀ k, ‖b k‖ ≤ 1) :
    ‖∏ k ∈ s, a k - ∏ k ∈ s, b k‖ ≤ ∑ k ∈ s, ‖a k - b k‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have h1 : a i * ∏ k ∈ s, a k - b i * ∏ k ∈ s, b k
        = a i * (∏ k ∈ s, a k - ∏ k ∈ s, b k) + (a i - b i) * ∏ k ∈ s, b k := by ring
    have hQ : ‖∏ k ∈ s, b k‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun k _ => hb k)
    rw [h1]
    calc ‖a i * (∏ k ∈ s, a k - ∏ k ∈ s, b k) + (a i - b i) * ∏ k ∈ s, b k‖
        ≤ ‖a i‖ * ‖∏ k ∈ s, a k - ∏ k ∈ s, b k‖ + ‖a i - b i‖ * ‖∏ k ∈ s, b k‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ 1 * (∑ k ∈ s, ‖a k - b k‖) + ‖a i - b i‖ * 1 :=
          add_le_add (mul_le_mul (ha i) ih (norm_nonneg _) zero_le_one)
            (mul_le_mul_of_nonneg_left hQ (norm_nonneg _))
      _ = ‖a i - b i‖ + ∑ k ∈ s, ‖a k - b k‖ := by ring

lemma gauss_cast (u : ℝ) : (-(u : ℂ) ^ 2 / 2) = ((-u ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring

lemma norm_gauss_le_one (u : ℝ) : ‖cexp (-(u : ℂ) ^ 2 / 2)‖ ≤ 1 := by
  rw [gauss_cast, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])

/-- local comparison of a standardized characteristic function with the Gaussian one. -/
lemma charFun_near_gauss (φ : ℝ → ℂ)
    (hφ : (fun t : ℝ => φ t - (1 - (t : ℂ) ^ 2 / 2)) =o[𝓝 0] fun t : ℝ => t ^ 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℝ, |u| < δ → ‖φ u - cexp (-(u : ℂ) ^ 2 / 2)‖ ≤ ε * u ^ 2 := by
  have h1 := hφ.def (half_pos hε)
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.eventually_nhds_iff.1 h1
  refine ⟨min δ1 (min 1 (Real.sqrt ε)), lt_min hδ1 (lt_min one_pos (Real.sqrt_pos.2 hε)), ?_⟩
  intro u hu
  have hu1 : |u| < δ1 := lt_of_lt_of_le hu (min_le_left _ _)
  have hu2 : |u| < 1 := lt_of_lt_of_le hu ((min_le_right _ _).trans (min_le_left _ _))
  have hu3 : |u| < Real.sqrt ε := lt_of_lt_of_le hu ((min_le_right _ _).trans (min_le_right _ _))
  have husq : u ^ 2 ≤ 1 := by
    have := sq_abs u; nlinarith [abs_nonneg u]
  have huε : u ^ 2 ≤ ε := by
    have h := Real.sq_sqrt hε.le
    have := sq_abs u; nlinarith [abs_nonneg u, Real.sqrt_nonneg ε]
  have hA : ‖φ u - (1 - (u : ℂ) ^ 2 / 2)‖ ≤ ε / 2 * u ^ 2 := by
    have := hδ1' (by rw [Real.dist_eq, sub_zero]; exact hu1)
    rwa [Real.norm_of_nonneg (sq_nonneg u)] at this
  have hB : ‖(1 - (u : ℂ) ^ 2 / 2) - cexp (-(u : ℂ) ^ 2 / 2)‖ ≤ ε / 2 * u ^ 2 := by
    have hx : |(-u ^ 2 / 2 : ℝ)| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg u]
    have hE := Real.abs_exp_sub_one_sub_id_le hx
    have hcast : (1 - (u : ℂ) ^ 2 / 2) - cexp (-(u : ℂ) ^ 2 / 2)
        = ((-(Real.exp (-u ^ 2 / 2) - 1 - (-u ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [gauss_cast, ← Complex.ofReal_exp]; push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    refine hE.trans ?_
    nlinarith [sq_nonneg u]
  calc ‖φ u - cexp (-(u : ℂ) ^ 2 / 2)‖
      = ‖(φ u - (1 - (u : ℂ) ^ 2 / 2)) + ((1 - (u : ℂ) ^ 2 / 2) - cexp (-(u : ℂ) ^ 2 / 2))‖ := by
        congr 1; ring
    _ ≤ ε / 2 * u ^ 2 + ε / 2 * u ^ 2 := (norm_add_le _ _).trans (add_le_add hA hB)
    _ = ε * u ^ 2 := by ring

/-- **Weighted CLT** for bounded triangular weights. -/
theorem weighted_clt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (X k)) (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (hvar : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    (c : ℕ → ℕ → ℝ) (C : ℝ) (hc : ∀ n k, |c n k| ≤ C) (v : ℝ)
    (hv : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, c n k ^ 2) / n) atTop (𝓝 v)) :
    Tendsto (fun n : ℕ =>
      charFun (P.map (fun ω => ∑ k ∈ Finset.range n, (√n)⁻¹ * c n k * X k ω)) 1)
      atTop (𝓝 (cexp (-(v : ℂ) / 2))) := by
  have : IsProbabilityMeasure (P.map (X 0)) := Measure.isProbabilityMeasure_map (hmeas 0).aemeasurable
  set φ : ℝ → ℂ := charFun (P.map (X 0)) with hφdef
  set a : ℕ → ℕ → ℝ := fun n k => (√n)⁻¹ * c n k with ha
  -- product formula
  have hprod : ∀ n : ℕ,
      charFun (P.map (fun ω => ∑ k ∈ Finset.range n, (√n)⁻¹ * c n k * X k ω)) 1
        = ∏ k ∈ Finset.range n, φ (a n k) := by
    intro n
    have hind2 : iIndepFun (fun k => (fun x : ℝ => a n k * x) ∘ X k) P :=
      hindep.comp (fun k x => a n k * x) (fun k => measurable_const_mul _)
    have h := iIndepFun.charFun_map_fun_finsetSum_eq_prod (s := Finset.range n) (E := ℝ)
      (X := fun k => (fun x : ℝ => a n k * x) ∘ X k)
      (fun k _ => ((measurable_const_mul _).comp (hmeas k)).aemeasurable) (hind2.restrict _)
    have h1 := congrFun h 1
    simp only [Function.comp_apply, Finset.prod_apply] at h1
    rw [h1]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [show ((fun x : ℝ => a n k * x) ∘ X k) = fun ω => a n k * X k ω from rfl,
      charFun_map_mul_comp (hmeas k).aemeasurable, (hident k).map_eq, mul_one]
  -- gaussian product
  have hsq : ∀ n : ℕ, ∑ k ∈ Finset.range n, a n k ^ 2 = (∑ k ∈ Finset.range n, c n k ^ 2) / n := by
    intro n
    have hs : ((√(n : ℝ))⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    simp only [ha, mul_pow, hs]
    rw [← Finset.mul_sum, div_eq_inv_mul]
  have hgprod : ∀ n : ℕ, ∏ k ∈ Finset.range n, cexp (-(a n k : ℂ) ^ 2 / 2)
      = cexp (-(((∑ k ∈ Finset.range n, c n k ^ 2) / n : ℝ) : ℂ) / 2) := by
    intro n
    rw [← Complex.exp_sum, ← hsq n]
    congr 1
    push_cast
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
  have hG : Tendsto (fun n : ℕ => ∏ k ∈ Finset.range n, cexp (-(a n k : ℂ) ^ 2 / 2))
      atTop (𝓝 (cexp (-(v : ℂ) / 2))) := by
    simp_rw [hgprod]
    have hc' : Continuous fun x : ℝ => cexp (-(x : ℂ) / 2) := by fun_prop
    exact (hc'.tendsto v).comp hv
  -- the difference tends to zero
  have hT := taylor_charFun_two (hmeas 0).aemeasurable hmean (by simpa [Pi.pow_apply] using hvar)
  have hD : Tendsto (fun n : ℕ => ∏ k ∈ Finset.range n, φ (a n k)
      - ∏ k ∈ Finset.range n, cexp (-(a n k : ℂ) ^ 2 / 2)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hc 0 0)
    set ε' := ε / (2 * (C ^ 2 + 1)) with hε'
    have hε'0 : 0 < ε' := by positivity
    obtain ⟨δ, hδ, hδ'⟩ := charFun_near_gauss φ hT ε' hε'0
    -- eventually C / √n < δ
    have hev : ∀ᶠ n : ℕ in atTop, C * (√(n : ℝ))⁻¹ < δ := by
      have h0 : Tendsto (fun n : ℕ => C * (√(n : ℝ))⁻¹) atTop (𝓝 (C * 0)) :=
        (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
          tendsto_natCast_atTop_atTop)).const_mul C
      rw [mul_zero] at h0
      exact (tendsto_order.1 h0).2 δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    have hbound := norm_prod_sub_prod_le (Finset.range n) (fun k => φ (a n k))
      (fun k => cexp (-(a n k : ℂ) ^ 2 / 2)) (fun k => norm_charFun_le_one _)
      (fun k => norm_gauss_le_one _)
    have hinv0 : 0 ≤ (√(n : ℝ))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
    have hterm : ∀ k ∈ Finset.range n,
        ‖φ (a n k) - cexp (-(a n k : ℂ) ^ 2 / 2)‖ ≤ ε' * a n k ^ 2 := by
      intro k _
      refine hδ' _ ?_
      have : |a n k| ≤ C * (√(n : ℝ))⁻¹ := by
        simp only [ha, abs_mul, abs_of_nonneg hinv0]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hc n k) hinv0
      exact lt_of_le_of_lt this (hN n hn)
    have hsum : ∑ k ∈ Finset.range n, a n k ^ 2 ≤ C ^ 2 := by
      rw [hsq n]
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp; positivity
      · have hnpos : (0 : ℝ) < n := by exact_mod_cast h
        rw [div_le_iff₀ hnpos]
        have : ∑ k ∈ Finset.range n, c n k ^ 2 ≤ ∑ k ∈ Finset.range n, C ^ 2 :=
          Finset.sum_le_sum fun k _ => by
            have := hc n k
            have h2 := sq_abs (c n k)
            nlinarith [abs_nonneg (c n k)]
        simpa [Finset.sum_const, Finset.card_range, mul_comm] using this
    calc ‖∏ k ∈ Finset.range n, φ (a n k) - ∏ k ∈ Finset.range n, cexp (-(a n k : ℂ) ^ 2 / 2)‖
        ≤ ∑ k ∈ Finset.range n, ‖φ (a n k) - cexp (-(a n k : ℂ) ^ 2 / 2)‖ := hbound
      _ ≤ ∑ k ∈ Finset.range n, ε' * a n k ^ 2 := Finset.sum_le_sum hterm
      _ = ε' * ∑ k ∈ Finset.range n, a n k ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ε' * C ^ 2 := mul_le_mul_of_nonneg_left hsum hε'0.le
      _ < ε := by
        rw [hε']
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [sq_nonneg C]
  have := hD.add hG
  rw [zero_add] at this
  refine this.congr fun n => ?_
  rw [hprod n]; ring


open DurrettProbability

noncomputable def fidiSum (w : Set.Icc (0 : ℝ) 1 →₀ ℝ) (f : PathSpace) : ℝ :=
  w.sum fun t r => r * f t

lemma cl_nonneg (v : ℝ) : 0 ≤ max 0 (min 1 v) := le_max_left _ _
lemma cl_le_one (v : ℝ) : max 0 (min 1 v) ≤ 1 := max_le zero_le_one (min_le_left _ _)
lemma cl_mono {u v : ℝ} (h : u ≤ v) : max 0 (min 1 u) ≤ max 0 (min 1 v) :=
  max_le_max le_rfl (min_le_min le_rfl h)

lemma cl_sum (n : ℕ) (u : ℝ) :
    ∑ k ∈ Finset.range n, max 0 (min 1 (u - k)) = max 0 (min (n : ℝ) u) := by
  induction n with
  | zero => simp [max_eq_left (min_le_left (0 : ℝ) u)]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    simp only [max_def, min_def]
    split_ifs <;> linarith

lemma cl_var (v : ℝ) :
    max 0 (min 1 v) * (1 - max 0 (min 1 v)) ≤ max 0 (min 1 (v + 1)) - max 0 (min 1 v) := by
  simp only [max_def, min_def]
  split_ifs <;> nlinarith

lemma cl_prod_bounds (x y k : ℝ) :
    max 0 (min 1 (min x y - k)) ^ 2 ≤ max 0 (min 1 (x - k)) * max 0 (min 1 (y - k)) ∧
    max 0 (min 1 (x - k)) * max 0 (min 1 (y - k)) ≤ max 0 (min 1 (min x y - k)) := by
  have hp0 := cl_nonneg (x - k); have hp1 := cl_le_one (x - k)
  have hq0 := cl_nonneg (y - k); have hq1 := cl_le_one (y - k)
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    have hpq := cl_mono (sub_le_sub_right h k)
    constructor <;> nlinarith
  · rw [min_eq_right h]
    have hpq := cl_mono (sub_le_sub_right h k)
    constructor <;> nlinarith

lemma sum_prod_bounds (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hm : min x y ≤ n) :
    min x y - 1 ≤ ∑ k ∈ Finset.range n, max 0 (min 1 (x - k)) * max 0 (min 1 (y - k)) ∧
    ∑ k ∈ Finset.range n, max 0 (min 1 (x - k)) * max 0 (min 1 (y - k)) ≤ min x y := by
  set m := min x y with hmdef
  have hm0 : 0 ≤ m := le_min hx hy
  have hA : ∑ k ∈ Finset.range n, max 0 (min 1 (m - k)) = m := by
    rw [cl_sum, min_eq_right hm, max_eq_right hm0]
  constructor
  · set f : ℕ → ℝ := fun i => max 0 (min 1 (m + 1 - i)) with hf
    have htel : ∑ k ∈ Finset.range n, (f k - f (k + 1)) = f 0 - f n := Finset.sum_range_sub' f n
    have hterm : ∀ k : ℕ, max 0 (min 1 (m - k)) * (1 - max 0 (min 1 (m - k))) ≤ f k - f (k + 1) := by
      intro k
      have h1 := cl_var (m - k)
      have e1 : f k = max 0 (min 1 (m - k + 1)) := by simp only [hf]; ring_nf
      have e2 : f (k + 1) = max 0 (min 1 (m - k)) := by simp only [hf]; push_cast; ring_nf
      rw [e1, e2]; exact h1
    have hsq : ∑ k ∈ Finset.range n, max 0 (min 1 (m - k)) ^ 2
        ≤ ∑ k ∈ Finset.range n, max 0 (min 1 (x - k)) * max 0 (min 1 (y - k)) :=
      Finset.sum_le_sum fun k _ => (cl_prod_bounds x y k).1
    have hsplit : ∑ k ∈ Finset.range n, max 0 (min 1 (m - k)) ^ 2
        = ∑ k ∈ Finset.range n, max 0 (min 1 (m - k))
          - ∑ k ∈ Finset.range n, max 0 (min 1 (m - k)) * (1 - max 0 (min 1 (m - k))) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
    have hvar : ∑ k ∈ Finset.range n, max 0 (min 1 (m - k)) * (1 - max 0 (min 1 (m - k))) ≤ 1 := by
      refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
      rw [htel]
      have := cl_le_one (m + 1 - (0 : ℕ)); have := cl_nonneg (m + 1 - (n : ℕ))
      simp only [hf]; linarith
    linarith
  · calc ∑ k ∈ Finset.range n, max 0 (min 1 (x - k)) * max 0 (min 1 (y - k))
        ≤ ∑ k ∈ Finset.range n, max 0 (min 1 (m - k)) :=
          Finset.sum_le_sum fun k _ => (cl_prod_bounds x y k).2
      _ = m := hA

lemma cov_limit (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hs1 : s ≤ 1) (ht1 : t ≤ 1) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n,
      max 0 (min 1 (n * s - k)) * max 0 (min 1 (n * t - k))) / n) atTop (𝓝 (min s t)) := by
  have hlow : Tendsto (fun n : ℕ => min s t - 1 / (n : ℝ)) atTop (𝓝 (min s t)) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_sub (min s t)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hmin : min ((n : ℝ) * s) (n * t) = n * min s t := (mul_min_of_nonneg _ _ hnpos.le).symm
    have hb := (sum_prod_bounds n (n * s) (n * t) (by positivity) (by positivity)
      (by rw [hmin]; nlinarith [min_le_left s t])).1
    rw [hmin] at hb
    rw [le_div_iff₀ hnpos, sub_mul, div_mul_cancel₀ _ hnpos.ne']
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hmin : min ((n : ℝ) * s) (n * t) = n * min s t := (mul_min_of_nonneg _ _ hnpos.le).symm
    have hb := (sum_prod_bounds n (n * s) (n * t) (by positivity) (by positivity)
      (by rw [hmin]; nlinarith [min_le_left s t])).2
    rw [hmin] at hb
    rw [div_le_iff₀ hnpos]
    linarith


/-- the weight of step `k` in the fidi functional of the `n`-th walk path. -/
noncomputable def walkW (w : Set.Icc (0 : ℝ) 1 →₀ ℝ) (n k : ℕ) : ℝ :=
  ∑ t ∈ w.support, w t * max 0 (min 1 ((n : ℝ) * (t : ℝ) - k))

lemma fidiSum_walkPath {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (w : Set.Icc (0 : ℝ) 1 →₀ ℝ) :
    fidiSum w (walkPath X n ω) = ∑ k ∈ Finset.range n, (√n)⁻¹ * walkW w n k * X k ω := by
  have hpt : ∀ t : Set.Icc (0 : ℝ) 1, walkPath X n ω t
      = (∑ k ∈ Finset.range n, X k ω * max 0 (min 1 ((n : ℝ) * (t : ℝ) - k))) / √n := fun t => rfl
  unfold fidiSum Finsupp.sum
  rw [Finset.sum_congr rfl fun t _ => by
    beta_reduce; rw [hpt t, Finset.sum_div, Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold walkW
  rw [Finset.mul_sum, Finset.sum_mul]
  all_goals exact Finset.sum_congr rfl fun t _ => by ring

lemma abs_walkW_le (w : Set.Icc (0 : ℝ) 1 →₀ ℝ) (n k : ℕ) :
    |walkW w n k| ≤ ∑ t ∈ w.support, |w t| := by
  unfold walkW
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  rw [abs_mul, abs_of_nonneg (cl_nonneg _)]
  have := cl_le_one ((n : ℝ) * (t : ℝ) - k)
  nlinarith [abs_nonneg (w t)]

lemma walkW_sq_limit (w : Set.Icc (0 : ℝ) 1 →₀ ℝ) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, walkW w n k ^ 2) / n) atTop
      (𝓝 (∑ s ∈ w.support, ∑ t ∈ w.support, w s * w t * min (s : ℝ) (t : ℝ))) := by
  have hd2 : ∀ n : ℕ, (∑ k ∈ Finset.range n, walkW w n k ^ 2) / n
      = ∑ s ∈ w.support, ∑ t ∈ w.support, w s * w t * ((∑ k ∈ Finset.range n,
          max 0 (min 1 ((n : ℝ) * (s : ℝ) - k)) * max 0 (min 1 ((n : ℝ) * (t : ℝ) - k))) / n) := by
    intro n
    simp only [walkW, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [hd2]
  refine tendsto_finsetSum _ fun s _ => tendsto_finsetSum _ fun t _ => ?_
  exact (cov_limit (s : ℝ) (t : ℝ) s.2.1 t.2.1 s.2.2 t.2.2).const_mul _

/-- **Walk finite-dimensional characteristic functions** converge to the Brownian ones. -/
theorem walk_fidi_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (X k)) (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (hvar : ∫ ω, X 0 ω ^ 2 ∂P = 1) (w : Set.Icc (0 : ℝ) 1 →₀ ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, cexp (fidiSum w (walkPath X n ω) * I) ∂P) atTop
      (𝓝 (cexp (-((∑ s ∈ w.support, ∑ t ∈ w.support, w s * w t * min (s : ℝ) (t : ℝ) : ℝ) : ℂ)
        / 2))) := by
  have key : ∀ n : ℕ, ∫ ω, cexp (fidiSum w (walkPath X n ω) * I) ∂P
      = charFun (P.map (fun ω => ∑ k ∈ Finset.range n, (√n)⁻¹ * walkW w n k * X k ω)) 1 := by
    intro n
    rw [charFun_apply_real, integral_map
      (Finset.measurable_sum _ fun k _ => (hmeas k).const_mul _).aemeasurable (by fun_prop)]
    congr 1
    funext ω
    rw [fidiSum_walkPath]
    simp
  simp_rw [key]
  exact weighted_clt hmeas hindep hident hmean hvar (walkW w) _ (abs_walkW_le w) _
    (walkW_sq_limit w)

end DonskerK

end part_k6

section part_k4
open Filter MeasureTheory ProbabilityTheory Complex
open scoped NNReal Topology

namespace DonskerK

open DurrettProbability


/-- the time `t ∈ [0,1]` as an element of `ℝ≥0`. -/
def tnn (t : Set.Icc (0 : ℝ) 1) : ℝ≥0 := ⟨t, t.2.1⟩

lemma fidiSum_brownianPath {Ω' : Type*} {B : ℝ≥0 → Ω' → ℝ} (ω : Ω')
    (hBc : Continuous fun t => B t ω) (w : Set.Icc (0 : ℝ) 1 →₀ ℝ) :
    fidiSum w (brownianPath B ω) = ∑ t ∈ w.support, w t * B (tnn t) ω := by
  unfold fidiSum brownianPath toPath
  rw [dif_pos hBc]
  rfl

/-- **Brownian finite-dimensional characteristic functions.** -/
theorem brownian_fidi {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P')
    (hBc : ∀ ω, Continuous fun t => B t ω) (w : Set.Icc (0 : ℝ) 1 →₀ ℝ) :
    ∫ ω, cexp (fidiSum w (brownianPath B ω) * I) ∂P'
      = cexp (-((∑ s ∈ w.support, ∑ t ∈ w.support, w s * w t * min (s : ℝ) (t : ℝ) : ℝ) : ℂ)
          / 2) := by
  have hG := hB.toIsPreBrownianReal.isGaussianProcess
  set Y : Set.Icc (0 : ℝ) 1 → Ω' → ℝ := fun s ω => w s * B (tnn s) ω with hY
  have hYG : IsGaussianProcess Y P' := by
    refine hG.of_isGaussianProcess fun s => ?_
    refine ⟨{tnn s}, w s • ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : ({tnn s} : Finset ℝ≥0) => ℝ) ⟨tnn s, Finset.mem_singleton_self _⟩,
      fun ω => ?_⟩
    simp [hY, Finset.restrict_def]
  set Z : Ω' → ℝ := fun ω => ∑ t ∈ w.support, Y t ω with hZ
  have hZG : HasGaussianLaw Z P' := hYG.hasGaussianLaw_fun_sum
  have hmem : ∀ t, MemLp (Y t) 2 P' := fun t =>
    (hYG.hasGaussianLaw_eval t).memLp_two
  have hmeanZ : P'[Z] = 0 := by
    simp only [hZ]
    rw [integral_finsetSum _ fun t _ => (hmem t).integrable one_le_two]
    refine Finset.sum_eq_zero fun t _ => ?_
    simp only [hY]
    rw [integral_const_mul, hB.toIsPreBrownianReal.integral_eval, mul_zero]
  have hvarZ : Var[Z; P'] = ∑ s ∈ w.support, ∑ t ∈ w.support, w s * w t * min (s : ℝ) (t : ℝ) := by
    simp only [hZ]
    rw [variance_fun_sum' fun t _ => hmem t]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    simp only [hY]
    rw [covariance_const_mul_left, covariance_const_mul_right,
      hB.toIsPreBrownianReal.covariance_fun_eval, NNReal.coe_min, ← mul_assoc]
    rfl
  have hint : ∀ ω, fidiSum w (brownianPath B ω) = Z ω := fun ω => by
    rw [fidiSum_brownianPath ω (hBc ω)]
  simp_rw [hint]
  have hmap := hZG.map_eq_gaussianReal
  have hchar := charFun_gaussianReal (μ := P'[Z]) (v := Var[Z; P'].toNNReal) 1
  rw [← hmap, charFun_apply_real, integral_map hZG.aemeasurable (by fun_prop)] at hchar
  simp only [one_mul, Complex.ofReal_one] at hchar
  rw [hchar, hmeanZ, Real.coe_toNNReal _ (variance_nonneg _ _), hvarZ]
  congr 1
  push_cast
  ring

end DonskerK

end part_k4

section part_k5
open Filter MeasureTheory ProbabilityTheory Complex BoundedContinuousFunction
open scoped NNReal Topology

namespace DonskerK

open DurrettProbability


/-- the evaluation pairing between paths and finitely supported weights. -/
noncomputable def evalPair : PathSpace →ₗ[ℝ] (Set.Icc (0 : ℝ) 1 →₀ ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f w => fidiSum w f)
    (fun f g w => by
      simp only [fidiSum, Finsupp.sum, ContinuousMap.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c f w => by
      simp only [fidiSum, Finsupp.sum, ContinuousMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring)
    (fun f w w' => by
      simp only [fidiSum]
      exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring))
    (fun c f w => by
      simp only [fidiSum, smul_eq_mul]
      rw [Finsupp.sum_smul_index (fun _ => by simp), Finsupp.mul_sum]
      exact Finsupp.sum_congr fun t _ => by ring)

lemma evalPair_apply (f : PathSpace) (w : Set.Icc (0 : ℝ) 1 →₀ ℝ) :
    evalPair f w = fidiSum w f := rfl

lemma continuous_fidiSum (w : Set.Icc (0 : ℝ) 1 →₀ ℝ) : Continuous (fidiSum w) := by
  unfold fidiSum Finsupp.sum
  exact continuous_finsetSum _ fun t _ =>
    continuous_const.mul (continuous_eval_const t)

/-- **Assembly**: tightness plus convergence of all finite-dimensional characteristic
functions gives weak convergence on `C[0,1]`. -/
theorem tendsto_of_tight_of_fidi {μ : ℕ → ProbabilityMeasure PathSpace}
    {μ₀ : ProbabilityMeasure PathSpace}
    (ht : IsTightMeasureSet {(μ n : Measure PathSpace) | n})
    (h : ∀ w : Set.Icc (0 : ℝ) 1 →₀ ℝ,
      Tendsto (fun n => ∫ f, cexp (fidiSum w f * I) ∂(μ n : Measure PathSpace)) atTop
        (𝓝 (∫ f, cexp (fidiSum w f * I) ∂(μ₀ : Measure PathSpace)))) :
    Tendsto μ atTop (𝓝 μ₀) := by
  let _ : TopologicalSpace (Set.Icc (0 : ℝ) 1 →₀ ℝ) := ⊥
  have _ : DiscreteTopology (Set.Icc (0 : ℝ) 1 →₀ ℝ) := ⟨rfl⟩
  have hL : Continuous fun p : PathSpace × (Set.Icc (0 : ℝ) 1 →₀ ℝ) => evalPair p.1 p.2 :=
    continuous_prod_of_discrete_right.2 fun w => continuous_fidiSum w
  have hL' : ∀ v : PathSpace, v ≠ 0 → evalPair v ≠ 0 := by
    intro v hv hzero
    apply hv
    ext t
    have := LinearMap.congr_fun hzero (Finsupp.single t 1)
    simpa [evalPair_apply, fidiSum, Finsupp.sum_single_index] using this
  refine ProbabilityMeasure.tendsto_of_tight_of_separatesPoints ℂ ht
    (A := charPoly Real.continuous_probChar hL) (separatesPoints_charPoly Real.continuous_probChar
      Real.probChar_ne_one hL hL') ?_
  intro g hg
  rw [mem_charPoly] at hg
  obtain ⟨w, hw⟩ := hg
  have h_eq (ν : Measure PathSpace) (hν : IsProbabilityMeasure ν) :
      ∫ x, g x ∂ν = w.coeff.sum (fun a z ↦ z * ∫ x, cexp (fidiSum a x * I) ∂ν) := by
    simp_rw [hw, Finsupp.sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [integral_const_mul]
      rfl
    · refine fun i _ ↦ Integrable.const_mul ?_ _
      exact BoundedContinuousFunction.integrable ν (char Real.continuous_probChar hL i)
  simp_rw [h_eq (μ _) inferInstance, h_eq μ₀ inferInstance]
  exact tendsto_finsetSum _ fun y _ ↦ Tendsto.const_mul _ (h y)

end DonskerK

end part_k5

section part_k7
open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology unitInterval

namespace DonskerK

open DurrettProbability

/-- the hat functions of the polygonal walk, already rescaled by `1/√n`. -/
noncomputable def hatPath (n k : ℕ) : PathSpace :=
  ⟨fun t => max 0 (min 1 (n * (t : ℝ) - k)) / Real.sqrt n, by fun_prop⟩

lemma walkPath_eq_sum {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    walkPath X n ω = ∑ k : Fin n, X k ω • hatPath n k := by
  ext t
  simp only [walkPath, walkInterp, hatPath, ContinuousMap.coe_mk, ContinuousMap.coe_sum,
    Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_div,
    ← Fin.sum_univ_eq_sum_range (fun k => X k ω * max 0 (min 1 (n * (t : ℝ) - k)) / √n)]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma measurable_walkPath {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ}
    (hX : ∀ k, Measurable (X k)) (n : ℕ) : Measurable (walkPath X n) := by
  have hc : Continuous fun v : Fin n → ℝ => ∑ k : Fin n, v k • hatPath n k := by fun_prop
  have hv : Measurable fun ω => fun k : Fin n => X k ω := measurable_pi_lambda _ fun k => hX k
  have h := hc.measurable.comp hv
  convert h using 1
  funext ω
  exact walkPath_eq_sum X n ω

lemma aemeasurable_brownianPath {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P')
    (hBc : ∀ ω, Continuous fun t => B t ω) : AEMeasurable (brownianPath B) P' := by
  have hG := hB.toIsPreBrownianReal.isGaussianProcess
  have hBt : ∀ t, AEMeasurable (B t) P' := fun t => (hG.hasGaussianLaw_eval t).aemeasurable
  refine aemeasurable_of_tendsto_metrizable_ae'
    (f := fun m ω => bernsteinApproximation m (brownianPath B ω)) (fun m => ?_)
    (ae_of_all _ fun ω => bernsteinApproximation_uniform _)
  have hc : Continuous fun v : Fin (m + 1) → ℝ =>
      ∑ k : Fin (m + 1), bernstein m k • ContinuousMap.const I (v k) := by
    refine continuous_finsetSum _ fun k _ => ?_
    exact (continuous_const_smul (bernstein m k)).comp
      (ContinuousMap.continuous_const'.comp (continuous_apply k))
  have hv : AEMeasurable (fun ω => fun k : Fin (m + 1) => brownianPath B ω (bernstein.z k)) P' := by
    refine aemeasurable_pi_lambda _ fun k => ?_
    have : (fun ω => brownianPath B ω (bernstein.z k))
        = B ⟨(bernstein.z k : ℝ), (bernstein.z k).2.1⟩ := by
      funext ω
      simp only [brownianPath, toPath, dif_pos (hBc ω)]
      rfl
    rw [this]
    exact hBt _
  exact hc.measurable.comp_aemeasurable hv

end DonskerK

end part_k7

section part_k3
open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology ENNReal

namespace DonskerK

open DurrettProbability

/-- the time `0` of `[0,1]`. -/
def t0 : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩

/-- paths whose `δ`-modulus of continuity is at most `ε`. -/
def Cset (δ ε : ℝ) : Set PathSpace :=
  {f | ∀ s t : Set.Icc (0 : ℝ) 1, |(s : ℝ) - t| ≤ δ → |f s - f t| ≤ ε}

lemma isClosed_Cset (δ ε : ℝ) : IsClosed (Cset δ ε) := by
  have : Cset δ ε = ⋂ s : Set.Icc (0 : ℝ) 1, ⋂ t : Set.Icc (0 : ℝ) 1,
      ⋂ (_ : |(s : ℝ) - t| ≤ δ), {f : PathSpace | |f s - f t| ≤ ε} := by
    ext f
    simp only [Cset, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  refine isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ => ?_
  exact isClosed_le ((continuous_eval_const s).sub (continuous_eval_const t)).abs
    continuous_const

lemma Cset_anti {δ δ' ε : ℝ} (h : δ ≤ δ') : Cset δ' ε ⊆ Cset δ ε :=
  fun _ hf s t hst => hf s t (hst.trans h)

lemma Cset_compl_mono (μ : Measure PathSpace) {δ δ' ε : ℝ} (h : δ ≤ δ') :
    μ (Cset δ ε)ᶜ ≤ μ (Cset δ' ε)ᶜ :=
  measure_mono (Set.compl_subset_compl.2 (Cset_anti h))

/-- a single law on `C[0,1]` has small modulus of continuity with high probability. -/
lemma single_Cset (μ : Measure PathSpace) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε)
    {η : ℝ≥0∞} (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ μ (Cset δ ε)ᶜ ≤ η := by
  set D : ℕ → Set PathSpace := fun m => (Cset (1 / ((m : ℝ) + 1)) ε)ᶜ with hD
  have hanti : Antitone D := by
    intro m m' hmm'
    refine Set.compl_subset_compl.2 (Cset_anti ?_)
    have : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
    gcongr
  have hempty : (⋂ m, D m) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun f hf => ?_
    have huc := CompactSpace.uniformContinuous_of_continuous f.continuous
    rw [Metric.uniformContinuous_iff] at huc
    obtain ⟨δ, hδ, hf'⟩ := huc ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    apply Set.mem_iInter.1 hf m
    intro s t hst
    have hd : dist s t < δ := by
      rw [Subtype.dist_eq, Real.dist_eq]
      linarith
    have := hf' hd
    rw [Real.dist_eq] at this
    exact this.le
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun m => (isClosed_Cset _ _).isOpen_compl.measurableSet.nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at ht
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds hη)).exists
  exact ⟨1 / ((m : ℝ) + 1), by positivity, hm.le⟩

/-- an eventual modulus bound becomes a uniform one (finitely many single laws). -/
lemma unif_Cset (μ : ℕ → Measure PathSpace) [∀ n, IsFiniteMeasure (μ n)] {ε : ℝ}
    (hε : 0 < ε) {η : ℝ≥0∞} (hη : 0 < η)
    (h : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, μ n (Cset δ ε)ᶜ ≤ η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n, μ n (Cset δ ε)ᶜ ≤ η := by
  obtain ⟨δ₀, hδ₀, hev⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have key : ∀ M : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ ∀ n < M, μ n (Cset δ ε)ᶜ ≤ η := by
    intro M
    induction M with
    | zero => exact ⟨δ₀, hδ₀, le_rfl, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
    | succ M ih =>
      obtain ⟨δ, hδ, hδle, hlt⟩ := ih
      obtain ⟨δ', hδ', hM⟩ := single_Cset (μ M) hε hη
      refine ⟨min δ δ', lt_min hδ hδ', (min_le_left _ _).trans hδle, fun n hn => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
      · exact (Cset_compl_mono _ (min_le_left _ _)).trans (hlt n hn)
      · exact (Cset_compl_mono _ (min_le_right _ _)).trans hM
  obtain ⟨δ, hδ, hδle, hlt⟩ := key N
  refine ⟨δ, hδ, fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · exact hlt n hn
  · exact (Cset_compl_mono _ hδle).trans (hN n hn)

/-- paths vanishing at `0` with modulus `1` at scale `δ` are bounded by `⌈1/δ⌉`. -/
lemma abs_le_of_Cset {δ : ℝ} (hδ : 0 < δ) (f : PathSpace) (hf0 : f t0 = 0)
    (hf : f ∈ Cset δ 1) (t : Set.Icc (0 : ℝ) 1) : |f t| ≤ ⌈1 / δ⌉₊ := by
  have hstep : ∀ j : ℕ, ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ≤ j * δ → |f t| ≤ j := by
    intro j
    induction j with
    | zero =>
      intro t ht
      have h0 : (t : ℝ) = 0 := le_antisymm (by simpa using ht) t.2.1
      have : t = t0 := Subtype.ext h0
      simp [this, hf0]
    | succ j ih =>
      intro t ht
      by_cases h : (t : ℝ) ≤ j * δ
      · exact (ih t h).trans (by push_cast; linarith)
      · push_neg at h
        have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        set s : Set.Icc (0 : ℝ) 1 := ⟨max 0 ((t : ℝ) - δ),
          ⟨le_max_left _ _, max_le zero_le_one (by linarith [t.2.2])⟩⟩ with hs
        have hsj : (s : ℝ) ≤ j * δ := by
          show max 0 ((t : ℝ) - δ) ≤ j * δ
          push_cast at ht
          exact max_le (by positivity) (by linarith)
        have hts : |(t : ℝ) - s| ≤ δ := by
          show |(t : ℝ) - max 0 ((t : ℝ) - δ)| ≤ δ
          rw [abs_le]
          constructor
          · have := le_max_right 0 ((t : ℝ) - δ)
            rcases le_total 0 ((t : ℝ) - δ) with h' | h'
            · rw [max_eq_right h']; linarith
            · rw [max_eq_left h']; linarith [t.2.1]
          · have := le_max_right 0 ((t : ℝ) - δ)
            linarith
        have h1 := hf t s hts
        have h2 := ih s hsj
        have : |f t| ≤ |f t - f s| + |f s| := by
          have := abs_add_le (f t - f s) (f s)
          simpa using this
        push_cast
        linarith
  refine hstep _ t ?_
  have h1 : 1 / δ ≤ ⌈1 / δ⌉₊ := Nat.le_ceil _
  have h2 : 1 ≤ (⌈1 / δ⌉₊ : ℝ) * δ := by
    rw [div_le_iff₀ hδ] at h1
    linarith
  linarith [t.2.2]

/-- the Arzelà–Ascoli compact sets. -/
def Kset (δ : ℕ → ℝ) : Set PathSpace :=
  {f | f t0 = 0} ∩ ⋂ k : ℕ, Cset (δ k) (1 / ((k : ℝ) + 1))

lemma isClosed_Kset (δ : ℕ → ℝ) : IsClosed (Kset δ) :=
  (isClosed_eq (continuous_eval_const _) continuous_const).inter
    (isClosed_iInter fun _ => isClosed_Cset _ _)

lemma isCompact_Kset (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k) : IsCompact (Kset δ) := by
  set e := ContinuousMap.isometryEquivBoundedOfCompact (Set.Icc (0 : ℝ) 1) ℝ with he
  set R : ℝ := (⌈1 / δ 0⌉₊ : ℝ) with hR
  have hA : IsCompact (e.symm ⁻¹' Kset δ) := by
    refine BoundedContinuousFunction.arzela_ascoli₂ (Set.Icc (-R) R) isCompact_Icc
      (e.symm ⁻¹' Kset δ) ((isClosed_Kset δ).preimage e.symm.continuous) ?_ ?_
    · intro f x hf
      have h1 : (e.symm f) t0 = 0 := hf.1
      have h2 : e.symm f ∈ Cset (δ 0) 1 := by
        have := Set.mem_iInter.1 hf.2 0
        simpa using this
      have := abs_le_of_Cset (hδ 0) (e.symm f) h1 h2 x
      exact abs_le.1 this
    · refine UniformEquicontinuous.equicontinuous ?_
      rw [Metric.uniformEquicontinuous_iff]
      intro ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      refine ⟨δ k, hδ k, fun x y hxy i => ?_⟩
      have hi : e.symm i ∈ Cset (δ k) (1 / ((k : ℝ) + 1)) := Set.mem_iInter.1 i.2.2 k
      have hxy' : |(x : ℝ) - y| ≤ δ k := by
        rw [Subtype.dist_eq, Real.dist_eq] at hxy
        exact hxy.le
      have := hi x y hxy'
      rw [Real.dist_eq]
      exact lt_of_le_of_lt this hk
  have : e.symm '' (e.symm ⁻¹' Kset δ) = Kset δ := Set.image_preimage_eq _ e.symm.surjective
  rw [← this]
  exact hA.image e.symm.continuous

/-- **Tightness criterion** on `C[0,1]`: paths start at `0` and have uniformly small modulus. -/
theorem tight_of_Cset (μ : ℕ → Measure PathSpace) [∀ n, IsProbabilityMeasure (μ n)]
    (h0 : ∀ n, μ n {f : PathSpace | f t0 = 0}ᶜ = 0)
    (hmod : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ≥0∞, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ n, μ n (Cset δ ε)ᶜ ≤ η) :
    IsTightMeasureSet {ν | ∃ n, μ n = ν} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  choose δ hδ hδμ using fun k : ℕ =>
    hmod (1 / ((k : ℝ) + 1)) (by positivity) (ε' k) (by exact_mod_cast hε'pos k)
  refine ⟨Kset δ, isCompact_Kset δ hδ, ?_⟩
  rintro ν ⟨n, rfl⟩
  have hc : (Kset δ)ᶜ = {f : PathSpace | f t0 = 0}ᶜ ∪
      ⋃ k : ℕ, (Cset (δ k) (1 / ((k : ℝ) + 1)))ᶜ := by
    simp only [Kset, Set.compl_inter, Set.compl_iInter]
  rw [hc]
  calc μ n ({f : PathSpace | f t0 = 0}ᶜ ∪ ⋃ k : ℕ, (Cset (δ k) (1 / ((k : ℝ) + 1)))ᶜ)
      ≤ μ n {f : PathSpace | f t0 = 0}ᶜ + μ n (⋃ k : ℕ, (Cset (δ k) (1 / ((k : ℝ) + 1)))ᶜ) :=
        measure_union_le _ _
    _ ≤ 0 + ∑' k, (ε' k : ℝ≥0∞) :=
        add_le_add (h0 n).le ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun k => hδμ k n))
    _ ≤ ε := by rw [zero_add]; exact hε'sum.le

/-! ### the polygon modulus from the lattice modulus -/

lemma interp_eq (x : ℕ → ℝ) (a : ℕ) (u : ℝ) (hau : (a : ℝ) ≤ u) (hu : u ≤ a + 1) :
    ∀ n, a < n → ∑ k ∈ Finset.range n, x k * max 0 (min 1 (u - k)) =
      (∑ k ∈ Finset.range a, x k) + (u - a) * x a := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : (k : ℝ) + 1 ≤ a := by exact_mod_cast Finset.mem_range.1 hk
      rw [show max 0 (min 1 (u - k)) = 1 by
        rw [min_eq_left (by linarith), max_eq_right zero_le_one]]
      ring
    · rw [show max 0 (min 1 (u - a)) = u - a by
        rw [min_eq_right (by linarith), max_eq_right (by linarith)]]
      ring
  | succ m hm ih =>
    rw [Finset.sum_range_succ, ih]
    have hm' : (a : ℝ) + 1 ≤ m := by exact_mod_cast hm
    rw [show max 0 (min 1 (u - m)) = 0 by
      rw [max_eq_left (min_le_of_right_le (by linarith))]]
    ring

lemma interp_conv (x : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu0 : 0 ≤ u) (hun : u ≤ n) :
    ∃ a : ℕ, a + 1 ≤ n ∧ (a : ℝ) ≤ u ∧ u ≤ a + 1 ∧
      ∑ k ∈ Finset.range n, x k * max 0 (min 1 (u - k)) =
        (1 - (u - a)) * (∑ k ∈ Finset.range a, x k) +
          (u - a) * (∑ k ∈ Finset.range (a + 1), x k) := by
  set a := min ⌊u⌋₊ (n - 1) with ha
  have ha1 : a + 1 ≤ n := by omega
  have hau : (a : ℝ) ≤ u := by
    have : (a : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast min_le_left _ _
    exact this.trans (Nat.floor_le hu0)
  have hua : u ≤ a + 1 := by
    rcases le_total ⌊u⌋₊ (n - 1) with h | h
    · have : a = ⌊u⌋₊ := min_eq_left h
      rw [this]
      exact (Nat.lt_floor_add_one u).le
    · have : a = n - 1 := min_eq_right h
      have hn' : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        have : n - 1 + 1 = n := Nat.sub_add_cancel hn
        exact_mod_cast this
      rw [this, hn']
      exact hun
  refine ⟨a, ha1, hau, hua, ?_⟩
  rw [interp_eq x a u hau hua n (by omega), Finset.sum_range_succ]
  ring

lemma convex4 {θ φ A0 A1 B0 B1 c : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (h00 : |A0 - B0| < c) (h01 : |A0 - B1| < c) (h10 : |A1 - B0| < c) (h11 : |A1 - B1| < c) :
    |((1 - θ) * A0 + θ * A1) - ((1 - φ) * B0 + φ * B1)| ≤ c := by
  obtain ⟨a1, a2⟩ := abs_lt.1 h00
  obtain ⟨b1, b2⟩ := abs_lt.1 h01
  obtain ⟨c1, c2⟩ := abs_lt.1 h10
  obtain ⟨d1, d2⟩ := abs_lt.1 h11
  have w1 : 0 ≤ (1 - θ) * (1 - φ) := mul_nonneg (by linarith) (by linarith)
  have w2 : 0 ≤ (1 - θ) * φ := mul_nonneg (by linarith) hφ0
  have w3 : 0 ≤ θ * (1 - φ) := mul_nonneg hθ0 (by linarith)
  have w4 : 0 ≤ θ * φ := mul_nonneg hθ0 hφ0
  have e : ((1 - θ) * A0 + θ * A1) - ((1 - φ) * B0 + φ * B1) =
      (1 - θ) * (1 - φ) * (A0 - B0) + (1 - θ) * φ * (A0 - B1) + θ * (1 - φ) * (A1 - B0) +
        θ * φ * (A1 - B1) := by ring
  have ec : c = (1 - θ) * (1 - φ) * c + (1 - θ) * φ * c + θ * (1 - φ) * c + θ * φ * c := by ring
  rw [e, abs_le]
  constructor
  · have p1 := mul_le_mul_of_nonneg_left (neg_le_of_neg_le a1.le) w1
    have p2 := mul_le_mul_of_nonneg_left (neg_le_of_neg_le b1.le) w2
    have p3 := mul_le_mul_of_nonneg_left (neg_le_of_neg_le c1.le) w3
    have p4 := mul_le_mul_of_nonneg_left (neg_le_of_neg_le d1.le) w4
    have q1 : (1 - θ) * (1 - φ) * (-c) ≤ (1 - θ) * (1 - φ) * (A0 - B0) :=
      mul_le_mul_of_nonneg_left a1.le w1
    have q2 : (1 - θ) * φ * (-c) ≤ (1 - θ) * φ * (A0 - B1) := mul_le_mul_of_nonneg_left b1.le w2
    have q3 : θ * (1 - φ) * (-c) ≤ θ * (1 - φ) * (A1 - B0) := mul_le_mul_of_nonneg_left c1.le w3
    have q4 : θ * φ * (-c) ≤ θ * φ * (A1 - B1) := mul_le_mul_of_nonneg_left d1.le w4
    have : -c = (1 - θ) * (1 - φ) * (-c) + (1 - θ) * φ * (-c) + θ * (1 - φ) * (-c) +
        θ * φ * (-c) := by ring
    linarith
  · have q1 : (1 - θ) * (1 - φ) * (A0 - B0) ≤ (1 - θ) * (1 - φ) * c :=
      mul_le_mul_of_nonneg_left a2.le w1
    have q2 : (1 - θ) * φ * (A0 - B1) ≤ (1 - θ) * φ * c := mul_le_mul_of_nonneg_left b2.le w2
    have q3 : θ * (1 - φ) * (A1 - B0) ≤ θ * (1 - φ) * c := mul_le_mul_of_nonneg_left c2.le w3
    have q4 : θ * φ * (A1 - B1) ≤ θ * φ * c := mul_le_mul_of_nonneg_left d2.le w4
    linarith

lemma poly_mod (x : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (c L : ℝ)
    (hlat : ∀ i j : ℕ, i ≤ j → (j : ℝ) ≤ i + L → j ≤ n →
      |∑ k ∈ Finset.range j, x k - ∑ k ∈ Finset.range i, x k| < c)
    (u v : ℝ) (hu0 : 0 ≤ u) (hun : u ≤ n) (hv0 : 0 ≤ v) (hvn : v ≤ n) (huv : |u - v| + 2 ≤ L) :
    |∑ k ∈ Finset.range n, x k * max 0 (min 1 (u - k)) -
      ∑ k ∈ Finset.range n, x k * max 0 (min 1 (v - k))| ≤ c := by
  have hsym : ∀ i j : ℕ, i ≤ n → j ≤ n → |(i : ℝ) - j| ≤ L →
      |∑ k ∈ Finset.range i, x k - ∑ k ∈ Finset.range j, x k| < c := by
    intro i j hi hj hij
    rcases le_total i j with h | h
    · rw [abs_sub_comm]
      refine hlat i j h ?_ hj
      have := (abs_le.1 hij).1
      linarith
    · refine hlat j i h ?_ hi
      have := (abs_le.1 hij).2
      linarith
  obtain ⟨a, ha1, hau, hua, hA⟩ := interp_conv x n hn u hu0 hun
  obtain ⟨b, hb1, hbv, hvb, hB⟩ := interp_conv x n hn v hv0 hvn
  rw [hA, hB]
  obtain ⟨huv1, huv2⟩ := abs_le.1 (show |u - v| ≤ L - 2 by linarith)
  have ca : ((a + 1 : ℕ) : ℝ) = a + 1 := by push_cast; ring
  have cb : ((b + 1 : ℕ) : ℝ) = b + 1 := by push_cast; ring
  refine convex4 (by linarith) (by linarith) (by linarith) (by linarith) ?_ ?_ ?_ ?_
  · exact hsym a b (by omega) (by omega) (abs_le.2 ⟨by linarith, by linarith⟩)
  · exact hsym a (b + 1) (by omega) hb1 (abs_le.2 ⟨by rw [cb]; linarith, by rw [cb]; linarith⟩)
  · exact hsym (a + 1) b ha1 (by omega) (abs_le.2 ⟨by rw [ca]; linarith, by rw [ca]; linarith⟩)
  · exact hsym (a + 1) (b + 1) ha1 hb1
      (abs_le.2 ⟨by rw [ca, cb]; linarith, by rw [ca, cb]; linarith⟩)

/-- deterministic step: a small lattice modulus gives a small path modulus. -/
lemma walk_Cset {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (ε δ : ℝ)
    (hδ : 0 < δ) (hnδ : 4 ≤ δ * n)
    (hlat : ∀ i j : ℕ, i ≤ j → (j : ℝ) ≤ i + δ * n → (j : ℝ) ≤ 2 * n →
      |∑ k ∈ Finset.range j, X k ω - ∑ k ∈ Finset.range i, X k ω| < ε * Real.sqrt n) :
    walkPath X n ω ∈ Cset (δ / 2) ε := by
  intro s t hst
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  show |walkInterp X n ω (n * (s : ℝ)) / Real.sqrt n -
    walkInterp X n ω (n * (t : ℝ)) / Real.sqrt n| ≤ ε
  rw [← sub_div, abs_div, abs_of_pos hsq, div_le_iff₀ hsq]
  unfold walkInterp
  refine poly_mod (fun k => X k ω) n hn (ε * Real.sqrt n) (δ * n) ?_ _ _ ?_ ?_ ?_ ?_ ?_
  · intro i j hij hjL hjn
    refine hlat i j hij hjL ?_
    have : (j : ℝ) ≤ n := by exact_mod_cast hjn
    linarith
  · exact mul_nonneg hn0.le s.2.1
  · nlinarith [s.2.2]
  · exact mul_nonneg hn0.le t.2.1
  · nlinarith [t.2.2]
  · rw [← mul_sub, abs_mul, abs_of_pos hn0]
    nlinarith

lemma walkPath_t0 {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : walkPath X n ω t0 = 0 := by
  show walkInterp X n ω (n * (0 : ℝ)) / Real.sqrt n = 0
  unfold walkInterp
  rw [Finset.sum_eq_zero, zero_div]
  intro k _
  rw [mul_zero, zero_sub, max_eq_left (min_le_of_right_le (by simp)), mul_zero]

/-- **Tightness of the Donsker walk**, from measurability and the lattice modulus. -/
theorem walk_tight_of_lattice {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hWm : ∀ n, Measurable (walkPath X n))
    (hlat : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      P {ω | ∃ i j : ℕ, i ≤ j ∧ (j : ℝ) ≤ i + δ * n ∧ (j : ℝ) ≤ 2 * n ∧
        ε * Real.sqrt n ≤ |∑ k ∈ Finset.range j, X k ω - ∑ k ∈ Finset.range i, X k ω|} ≤
          ENNReal.ofReal η) :
    IsTightMeasureSet {ν | ∃ n, P.map (walkPath X n) = ν} := by
  have : ∀ n, IsProbabilityMeasure (P.map (walkPath X n)) := fun n =>
    Measure.isProbabilityMeasure_map (hWm n).aemeasurable
  refine tight_of_Cset (fun n => P.map (walkPath X n)) (fun n => ?_) (fun ε hε η hη => ?_)
  · rw [Measure.map_apply (hWm n)
      (isClosed_eq (continuous_eval_const _) continuous_const).isOpen_compl.measurableSet]
    have : walkPath X n ⁻¹' {f : PathSpace | f t0 = 0}ᶜ = ∅ := by
      ext ω
      simp [walkPath_t0]
    rw [this, measure_empty]
  refine unif_Cset _ hε hη ?_
  rcases eq_or_ne η ⊤ with htop | htop
  · exact ⟨1, one_pos, Eventually.of_forall fun n => by rw [htop]; exact le_top⟩
  have hηr : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
  obtain ⟨δ, hδ, hev⟩ := hlat ε hε η.toReal hηr
  refine ⟨δ / 2, by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (max 1 ⌈4 / δ⌉₊)] with n hn hnN
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hnN
  have hnδ : 4 ≤ δ * n := by
    have h1 : 4 / δ ≤ ⌈4 / δ⌉₊ := Nat.le_ceil _
    have h2 : ((⌈4 / δ⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hnN
    rw [div_le_iff₀ hδ] at h1
    nlinarith
  rw [Measure.map_apply (hWm n) (isClosed_Cset _ _).isOpen_compl.measurableSet]
  refine le_trans (measure_mono ?_) (hn.trans (ENNReal.ofReal_toReal htop).le)
  intro ω hω
  by_contra hcon
  apply hω
  refine walk_Cset X n hn1 ω ε δ hδ hnδ fun i j hij hj1 hj2 => ?_
  by_contra hge
  exact hcon ⟨i, j, hij, hj1, hj2, not_lt.1 hge⟩

end DonskerK

end part_k3

open Filter MeasureTheory ProbabilityTheory DurrettProbability NNReal Topology in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (X k)) (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P)
    (hint : Integrable (fun ω => X 0 ω ^ 2) P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (hvar : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous fun t => B t ω) :
    TendstoInDistribution (fun n : ℕ => walkPath X n) atTop (brownianPath B)
      (fun _ => P) P' := by
  have hWm := DonskerK.measurable_walkPath hmeas
  have hBm := DonskerK.aemeasurable_brownianPath hB hBc
  refine ⟨fun n => (hWm n).aemeasurable, hBm, ?_⟩
  apply DonskerK.tendsto_of_tight_of_fidi
  · exact DonskerK.walk_tight_of_lattice hWm
      (fun ε hε η hη => DonskerK.walk_lattice_mod hmeas hindep hident hint hmean hvar ε hε η hη)
  · intro w
    have hc : Continuous fun f : PathSpace => Complex.exp (DonskerK.fidiSum w f * Complex.I) :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (DonskerK.continuous_fidiSum w)).mul continuous_const)
    show Tendsto (fun n => ∫ f, Complex.exp (DonskerK.fidiSum w f * Complex.I) ∂(P.map (walkPath X n))) atTop
      (𝓝 (∫ f, Complex.exp (DonskerK.fidiSum w f * Complex.I) ∂(P'.map (brownianPath B))))
    rw [integral_map hBm hc.aestronglyMeasurable, DonskerK.brownian_fidi hB hBc w]
    have he : (fun n => ∫ f, Complex.exp (DonskerK.fidiSum w f * Complex.I) ∂(P.map (walkPath X n))) =
        fun n => ∫ ω, Complex.exp (DonskerK.fidiSum w (walkPath X n ω) * Complex.I) ∂P := by
      funext n
      exact integral_map (hWm n).aemeasurable hc.aestronglyMeasurable
    rw [he]
    exact DonskerK.walk_fidi_tendsto hmeas hindep hident hmean hvar w
