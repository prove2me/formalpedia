-- Prove2me | solution 1 for GaussPolyReg.Approx.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T19:52:38.06698+00:00
-- url     : https://prove2.me/submissions/e48f9fc2-d806-4e91-b3a3-7fc5a1ee76d9

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Ultra

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx.L33

open GaussPolyReg.Approx

lemma pairing_eq (p q : Original) : pairing p q = @inner ℝ _ _ p q := by
  rw [MeasureTheory.L2.inner_def]
  unfold pairing
  congr 1
  funext x
  simp [mul_comm]

lemma tendsto_lim_of_bdd (U : Ultrafilter ℕ) (f : ℕ → ℝ) (C : ℝ) (hC : ∀ n, |f n| ≤ C) :
    Tendsto f (U : Filter ℕ) (𝓝 (Filter.limUnder (U : Filter ℕ) f)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨x, -, hx⟩ := (isCompact_Icc (a := -C) (b := C)).ultrafilter_le_nhds (U.map f) (by
    rw [Ultrafilter.coe_map, le_principal_iff]
    exact Filter.mem_map.mpr (Filter.Eventually.of_forall (fun (k : ℕ) => abs_le.mp (hC k))))
  exact ⟨x, by rw [Ultrafilter.coe_map] at hx; exact hx⟩

lemma bdd_add {d : ℕ} {p q : Sequence} (hp : boundedLE d p) (hq : boundedLE d q) :
    boundedLE d (p + q) := by
  obtain ⟨hp1, C, hC⟩ := hp
  obtain ⟨hq1, D, hD⟩ := hq
  refine ⟨fun n => (finiteChaosLE n d).add_mem (hp1 n) (hq1 n), C + D, fun n => ?_⟩
  exact (norm_add_le _ _).trans (add_le_add (hC n) (hD n))

lemma bdd_sub {d : ℕ} {p q : Sequence} (hp : boundedLE d p) (hq : boundedLE d q) :
    boundedLE d (p - q) := by
  obtain ⟨hp1, C, hC⟩ := hp
  obtain ⟨hq1, D, hD⟩ := hq
  refine ⟨fun n => (finiteChaosLE n d).sub_mem (hp1 n) (hq1 n), C + D, fun n => ?_⟩
  exact (norm_sub_le _ _).trans (add_le_add (hC n) (hD n))

lemma bdd_smul {d : ℕ} (a : ℝ) {p : Sequence} (hp : boundedLE d p) :
    boundedLE d (a • p) := by
  obtain ⟨hp1, C, hC⟩ := hp
  refine ⟨fun n => (finiteChaosLE n d).smul_mem a (hp1 n), |a| * C, fun n => ?_⟩
  show ‖a • p n‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC n) (abs_nonneg a)

lemma pair_tendsto (U : Ultrafilter ℕ) {d : ℕ} {p q : Sequence}
    (hp : boundedLE d p) (hq : boundedLE d q) :
    Tendsto (fun n => pairing (p n) (q n)) (U : Filter ℕ) (𝓝 (ultraPair U p q)) := by
  obtain ⟨-, C, hC⟩ := hp
  obtain ⟨-, D, hD⟩ := hq
  apply tendsto_lim_of_bdd U _ (C * D)
  intro n
  rw [pairing_eq]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul (hC n) (hD n) (norm_nonneg _) ((norm_nonneg _).trans (hC n)))

lemma norm_tendsto (U : Ultrafilter ℕ) {d : ℕ} {p : Sequence} (hp : boundedLE d p) :
    Tendsto (fun n => ‖p n‖) (U : Filter ℕ) (𝓝 (ultraNorm U p)) := by
  obtain ⟨-, C, hC⟩ := hp
  apply tendsto_lim_of_bdd U _ C
  intro n
  rw [abs_of_nonneg (norm_nonneg _)]
  exact hC n

lemma ultraNorm_nonneg (U : Ultrafilter ℕ) {d : ℕ} {p : Sequence} (hp : boundedLE d p) :
    0 ≤ ultraNorm U p :=
  ge_of_tendsto (norm_tendsto U hp) (Filter.Eventually.of_forall (fun _ => norm_nonneg _))

lemma ultraNorm_triangle (U : Ultrafilter ℕ) {d : ℕ} {p q r : Sequence}
    (hp : boundedLE d p) (hq : boundedLE d q) (hr : boundedLE d r) :
    ultraNorm U (p - r) ≤ ultraNorm U (p - q) + ultraNorm U (q - r) := by
  have h1 := norm_tendsto U (bdd_sub hp hr)
  have h2 := (norm_tendsto U (bdd_sub hp hq)).add (norm_tendsto U (bdd_sub hq hr))
  refine le_of_tendsto_of_tendsto h1 h2 (Filter.Eventually.of_forall (fun n => ?_))
  show ‖p n - r n‖ ≤ ‖p n - q n‖ + ‖q n - r n‖
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

lemma ultraNorm_le_of_eventually (U : Ultrafilter ℕ) {d : ℕ} {p : Sequence}
    (hp : boundedLE d p) {c : ℝ} (h : ∀ᶠ n in (U : Filter ℕ), ‖p n‖ ≤ c) :
    ultraNorm U p ≤ c :=
  le_of_tendsto (norm_tendsto U hp) h

lemma eventually_lt_of_ultraNorm (U : Ultrafilter ℕ) {d : ℕ} {p : Sequence}
    (hp : boundedLE d p) {c : ℝ} (h : ultraNorm U p < c) :
    ∀ᶠ n in (U : Filter ℕ), ‖p n‖ < c :=
  (norm_tendsto U hp).eventually (gt_mem_nhds h)

/-- Completeness: pick indices `J m` beyond the `1/(m+1)`-Cauchy thresholds, and at
coordinate `n` use the largest `k ≤ n` whose closeness set `A k` contains `n`. -/
lemma complete (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) (d : ℕ)
    (p : ℕ → Sequence) (hp : ∀ j, boundedLE d (p j))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ j ≥ K, ∀ k ≥ K, ultraNorm U (p j - p k) < ε) :
    ∃ q : Sequence, boundedLE d q ∧
      Tendsto (fun j => ultraNorm U (p j - q)) atTop (𝓝 0) := by
  classical
  choose K hK using fun m : ℕ => hc (1 / ((m : ℝ) + 1)) (by positivity)
  let J : ℕ → ℕ := fun k => ∑ i ∈ Finset.range (k + 1), K i
  have hJK : ∀ i k, i ≤ k → K i ≤ J k := fun i k hik =>
    Finset.single_le_sum (f := K) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (by omega))
  let A : ℕ → Set ℕ := fun k =>
    {n | k ≤ n ∧ ∀ i ≤ k, ‖p (J i) n - p (J k) n‖ < 1 / ((i : ℝ) + 1)}
  have hA : ∀ k, A k ∈ (U : Filter ℕ) := by
    intro k
    have h1 : {n : ℕ | k ≤ n} ∈ (U : Filter ℕ) := hU (by
      rw [Nat.cofinite_eq_atTop]
      exact Filter.mem_atTop k)
    have h2 : ∀ i ≤ k, ∀ᶠ n in (U : Filter ℕ),
        ‖p (J i) n - p (J k) n‖ < 1 / ((i : ℝ) + 1) := fun i hi =>
      eventually_lt_of_ultraNorm U (bdd_sub (hp _) (hp _))
        (hK i (J i) (hJK i i le_rfl) (J k) (hJK i k hi))
    have h3 : ∀ᶠ n in (U : Filter ℕ), ∀ i ∈ Finset.range (k + 1),
        ‖p (J i) n - p (J k) n‖ < 1 / ((i : ℝ) + 1) :=
      (Filter.eventually_all_finset _).mpr
        (fun i hi => h2 i (by have := Finset.mem_range.mp hi; omega))
    filter_upwards [h1, h3] with n hn1 hn3
    exact ⟨hn1, fun i hi => hn3 i (Finset.mem_range.mpr (by omega))⟩
  let kf : ℕ → ℕ := fun n => Nat.findGreatest (fun k => n ∈ A k) n
  let q : Sequence := fun n => p (J (kf n)) n
  have hmem : ∀ n, n ∈ A (kf n) := by
    intro n
    refine Nat.findGreatest_spec (P := fun k => n ∈ A k) (m := 0) (Nat.zero_le n) ?_
    refine ⟨Nat.zero_le n, fun i hi => ?_⟩
    have : i = 0 := by omega
    subst this
    simp
  have hclose : ∀ m n, n ∈ A m → ‖p (J m) n - q n‖ < 1 / ((m : ℝ) + 1) := by
    intro m n hn
    exact (hmem n).2 m (Nat.le_findGreatest hn.1 hn)
  have hq : boundedLE d q := by
    obtain ⟨-, C, hC⟩ := hp (J 0)
    refine ⟨fun n => (hp (J (kf n))).1 n, C + 1, fun n => ?_⟩
    have h1 : ‖p (J 0) n - q n‖ < 1 := by
      have := (hmem n).2 0 (Nat.zero_le _)
      simpa using this
    have h2 : ‖q n‖ ≤ ‖p (J 0) n‖ + ‖p (J 0) n - q n‖ := by
      have := norm_sub_norm_le (q n) (p (J 0) n)
      rw [norm_sub_rev (q n)] at this
      linarith
    linarith [hC n]
  have hlim : ∀ m, ultraNorm U (p (J m) - q) ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    apply ultraNorm_le_of_eventually U (bdd_sub (hp _) hq)
    filter_upwards [hA m] with n hn
    exact (hclose m n hn).le
  refine ⟨q, hq, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
  refine ⟨J m, fun j hj => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ultraNorm_nonneg U (bdd_sub (hp j) hq))]
  have h1 := ultraNorm_triangle U (hp j) (hp (J m)) hq
  have h2 := hK m j (le_trans (hJK m m le_rfl) hj) (J m) (hJK m m le_rfl)
  have h3 := hlim m
  linarith

end GaussPolyReg.Approx.L33

open GaussPolyReg.Approx GaussPolyReg.Approx.L33 in
theorem solution (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) (d : ℕ) :
    GaussPolyReg.Approx.HilbertSequenceLaws U d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q hp hq
    exact pair_tendsto U hp hq
  · intro p q hp hq
    exact norm_tendsto U (bdd_sub hp hq)
  · intro p p' q q' hp hp' hq hq' hpp hqq
    obtain ⟨-, D, hD⟩ := id hq
    obtain ⟨-, C, hC⟩ := id hp'
    have hdiff : Tendsto (fun n => pairing (p n) (q n) - pairing (p' n) (q' n))
        (U : Filter ℕ) (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n => ‖p n - p' n‖ * D + C * ‖q n - q' n‖)
        (fun n => ?_) ?_
      · have heq : pairing (p n) (q n) - pairing (p' n) (q' n) =
            @inner ℝ _ _ (p n - p' n) (q n) + @inner ℝ _ _ (p' n) (q n - q' n) := by
          rw [pairing_eq, pairing_eq, inner_sub_left, inner_sub_right]
          ring
        rw [heq, Real.norm_eq_abs]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · exact (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (hD n) (norm_nonneg _))
        · exact (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
      · have := (hpp.mul_const D).add (hqq.const_mul C)
        simpa using this
    have := (pair_tendsto U hp' hq').add hdiff
    exact tendsto_nhds_unique (pair_tendsto U hp hq) (by simpa using this)
  · intro p q r hp hq hr
    refine tendsto_nhds_unique (pair_tendsto U (bdd_add hp hq) hr) ?_
    convert (pair_tendsto U hp hr).add (pair_tendsto U hq hr) using 1
    funext n
    show pairing (p n + q n) (r n) = _
    rw [pairing_eq, pairing_eq, pairing_eq, inner_add_left]
  · intro a p q hp hq
    refine tendsto_nhds_unique (pair_tendsto U (bdd_smul a hp) hq) ?_
    convert (pair_tendsto U hp hq).const_mul a using 1
    funext n
    show pairing (a • p n) (q n) = _
    rw [pairing_eq, pairing_eq, real_inner_smul_left]
  · intro p q _ _
    unfold ultraPair
    congr 1
    funext n
    rw [pairing_eq, pairing_eq, real_inner_comm]
  · intro p hp
    have hsq : ultraPair U p p = ultraNorm U p ^ 2 := by
      refine tendsto_nhds_unique (pair_tendsto U hp hp) ?_
      convert (norm_tendsto U hp).pow 2 using 1
      funext n
      rw [pairing_eq, real_inner_self_eq_norm_sq]
    have h0 := ultraNorm_nonneg U hp
    refine ⟨by rw [hsq]; positivity, by rw [hsq, Real.sqrt_sq h0], ?_⟩
    rw [hsq]
    constructor
    · intro h
      have h' : ultraNorm U p = 0 := (pow_eq_zero_iff two_ne_zero).mp h
      unfold sameClass
      have := norm_tendsto U hp
      rw [h'] at this
      simpa using this
    · intro h
      have h' : Tendsto (fun n => ‖p n‖) (U : Filter ℕ) (𝓝 0) := by
        simpa [sameClass] using h
      rw [tendsto_nhds_unique (norm_tendsto U hp) h']
      norm_num
  · exact complete U hU d
