-- Prove2me | solution 1 for CalibratedMA.Randomized.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @Aaron
-- created : 2026-11-13T18:29:26.765056+00:00
-- url     : https://prove2.me/submissions/2f5f6924-cf72-4009-8341-70e47cf71c6a

import Definitions.Def_CalibratedMA_Randomized_Rounding



open MeasureTheory

namespace CalibratedMA.Randomized.LiftedRestriction

/-- At a grid point with nonzero denominator, the sign test reads its index's membership. -/
lemma signTest_grid (K : ℕ) (T : Finset ℕ) (i : ℕ) (hK : 1 ≤ K) :
    signTest K T ((i : ℝ) / K) = if i ∈ T then 1 else -1 := by
  classical
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  simp only [signTest, div_left_inj' hKne, Nat.cast_inj]
  simp

/-- Restricting the sign assignment does not change its values at retained grid indices. -/
lemma signTest_inter_eq_of_mem (K : ℕ) (S T : Finset ℕ) (hK : 1 ≤ K)
    (i : ℕ) (hi : i ∈ S) :
    signTest K T ((i : ℝ) / K) = signTest K (T ∩ S) ((i : ℝ) / K) := by
  rw [signTest_grid K T i hK, signTest_grid K (T ∩ S) i hK]
  simp only [Finset.mem_inter, hi, and_true]

/-- An in-range entry of the sorted index list belongs to the original finite set. -/
lemma sorted_getD_mem (S : Finset ℕ) (K j : ℕ) (hj : j < S.card) :
    (S.sort (· ≤ ·)).getD j K ∈ S := by
  have hlen : j < (S.sort (· ≤ ·)).length := by simpa only [Finset.length_sort] using hj
  rw [List.getD_eq_getElem _ _ hlen]
  exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hlen)

/-- A finite supremum of indices below a positive bound remains below that bound,
even when the filtered set is empty. -/
lemma roundIndex_lt (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) (hM : 0 < M) :
    roundIndex M γ s < M := by
  unfold roundIndex
  apply (Finset.sup_lt_iff hM).2
  intro j hj
  exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1

/-- Integration against the rounding law only uses its two selected endpoints. -/
lemma integral_roundMeasure_test (M : ℕ) (γ : ℕ → ℝ) (s : ℝ) (h : ℝ → ℝ) :
    ∫ p, h p ∂(roundMeasure M γ s) =
      (1 - roundWeight M γ s) * h (γ (roundIndex M γ s)) +
        roundWeight M γ s * h (γ (roundIndex M γ s + 1)) := by
  have hw0 : 0 ≤ roundWeight M γ s := le_max_left _ _
  have hw1 : roundWeight M γ s ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have ha : Integrable h
      (ENNReal.ofReal (1 - roundWeight M γ s) • Measure.dirac (γ (roundIndex M γ s))) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hb : Integrable h
      (ENNReal.ofReal (roundWeight M γ s) • Measure.dirac (γ (roundIndex M γ s + 1))) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [roundMeasure, integral_add_measure ha hb]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hw0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hw1), smul_eq_mul]

/-- Signs outside the chosen partition points never affect the lifted function.
The identity holds on all real scores, including the clamped extension. -/
lemma liftTest_inter_of_card (K : ℕ) (S T : Finset ℕ) (hK : 1 ≤ K) (hS : 2 ≤ S.card) :
    liftTest (partitionOfIndexSet K S).1 (partitionOfIndexSet K S).2 (signTest K T) =
      liftTest (partitionOfIndexSet K S).1 (partitionOfIndexSet K S).2 (signTest K (T ∩ S)) := by
  funext s
  let L := S.card - 1
  let γ : ℕ → ℝ := fun j => ((S.sort (· ≤ ·)).getD j K : ℝ) / K
  change liftTest L γ (signTest K T) s = liftTest L γ (signTest K (T ∩ S)) s
  have hL : 0 < L := by dsimp only [L]; omega
  have hLc : L + 1 = S.card := by dsimp only [L]; omega
  have hj := roundIndex_lt L γ s hL
  have hsign : ∀ j < S.card, signTest K T (γ j) = signTest K (T ∩ S) (γ j) := by
    intro j hjS
    exact signTest_inter_eq_of_mem K S T hK _ (sorted_getD_mem S K j hjS)
  unfold liftTest
  rw [integral_roundMeasure_test, integral_roundMeasure_test]
  rw [hsign (roundIndex L γ s) (by omega)]
  rw [hsign (roundIndex L γ s + 1) (by omega)]

/-- The restriction identity for the endpoint-containing sets used by `liftedClass`. -/
lemma liftTest_inter (K : ℕ) (S T : Finset ℕ) (hK : 1 ≤ K)
    (hzero : 0 ∈ S) (hlast : K ∈ S) :
    liftTest (partitionOfIndexSet K S).1 (partitionOfIndexSet K S).2 (signTest K T) =
      liftTest (partitionOfIndexSet K S).1 (partitionOfIndexSet K S).2 (signTest K (T ∩ S)) := by
  have hpair : ({0, K} : Finset ℕ) ⊆ S := by simp [Finset.insert_subset_iff, hzero, hlast]
  have hcard := Finset.card_le_card hpair
  have hne : (0 : ℕ) ≠ K := by omega
  rw [Finset.card_pair hne] at hcard
  exact liftTest_inter_of_card K S T hK hcard

end CalibratedMA.Randomized.LiftedRestriction


namespace CalibratedMA.Randomized.LiftedCounting

/-- Choosing a set of `n` indices and then signs on that set gives at most
`choose |A| n * 2^n` distinct outputs of any function. -/
lemma card_fixed_size_images_le {α : Type*} [DecidableEq α]
    (A : Finset ℕ) (n : ℕ) (f : Finset ℕ × Finset ℕ → α) :
    ((Finset.powersetCard n A).biUnion
      (fun S => S.powerset.image (fun T => f (S, T)))).card ≤
      Nat.choose A.card n * 2 ^ n := by
  classical
  calc
    _ ≤ ∑ S ∈ Finset.powersetCard n A,
        (S.powerset.image (fun T => f (S, T))).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ Finset.powersetCard n A, 2 ^ n := by
      apply Finset.sum_le_sum
      intro S hS
      calc
        _ ≤ S.powerset.card := Finset.card_image_le
        _ = 2 ^ n := by rw [Finset.card_powerset, (Finset.mem_powersetCard.mp hS).2]
    _ = _ := by simp

/-- Counting outputs by the cardinality of the chosen index set. -/
lemma card_layered_images_le {α : Type*} [DecidableEq α]
    (A : Finset ℕ) (M : ℕ) (f : Finset ℕ × Finset ℕ → α) :
    ((Finset.Icc 1 M).biUnion (fun L =>
      (Finset.powersetCard (L + 1) A).biUnion
        (fun S => S.powerset.image (fun T => f (S, T))))).card ≤
      ∑ L ∈ Finset.Icc 1 M, Nat.choose A.card (L + 1) * 2 ^ (L + 1) := by
  classical
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum (fun L _ => card_fixed_size_images_le A (L + 1) f))

/-- A finite output class represented by index sets of sizes `2` through `M+1`,
with signs specified only on each chosen set, has the advertised counting bound. -/
lemma card_le_of_representatives {α : Type*}
    (F : Finset α) (A : Finset ℕ) (M : ℕ) (f : Finset ℕ × Finset ℕ → α)
    (hrep : ∀ x ∈ F, ∃ S T : Finset ℕ,
      S ⊆ A ∧ 2 ≤ S.card ∧ S.card ≤ M + 1 ∧ T ⊆ S ∧ f (S, T) = x) :
    F.card ≤ ∑ L ∈ Finset.Icc 1 M, Nat.choose A.card (L + 1) * 2 ^ (L + 1) := by
  classical
  have hsubset : F ⊆ (Finset.Icc 1 M).biUnion (fun L =>
      (Finset.powersetCard (L + 1) A).biUnion
        (fun S => S.powerset.image (fun T => f (S, T)))) := by
    intro x hx
    rcases hrep x hx with ⟨S, T, hSA, hScard_lo, hScard_hi, hTS, hf⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨S.card - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨hSA, by omega⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨T, Finset.mem_powerset.mpr hTS, hf⟩
  exact (Finset.card_le_card hsubset).trans (card_layered_images_le A M f)

/-- The same bound stated directly for the union over admissible index sets. -/
lemma card_restricted_images_le {α : Type*} [DecidableEq α]
    (A : Finset ℕ) (M : ℕ) (f : Finset ℕ × Finset ℕ → α) :
    (((A.powerset.filter (fun S => 2 ≤ S.card ∧ S.card ≤ M + 1))).biUnion
      (fun S => S.powerset.image (fun T => f (S, T)))).card ≤
      ∑ L ∈ Finset.Icc 1 M, Nat.choose A.card (L + 1) * 2 ^ (L + 1) := by
  classical
  apply card_le_of_representatives _ A M f
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨S, hS, hx⟩
  rcases Finset.mem_filter.mp hS with ⟨hSA, hScard⟩
  rcases Finset.mem_image.mp hx with ⟨T, hTS, hf⟩
  exact ⟨S, T, Finset.mem_powerset.mp hSA, hScard.1, hScard.2,
    Finset.mem_powerset.mp hTS, hf⟩

end CalibratedMA.Randomized.LiftedCounting


namespace CalibratedMA.Randomized.LiftedLogBound

lemma counting_sum_le (K M : ℕ) :
    (∑ L ∈ Finset.Icc 1 M, Nat.choose (K + 1) (L + 1) * 2 ^ (L + 1)) ≤
      (M + 1) * (2 * (K + 1)) ^ (M + 1) := by
  have hterm (L : ℕ) (hL : L ∈ Finset.Icc 1 M) :
      Nat.choose (K + 1) (L + 1) * 2 ^ (L + 1) ≤ (2 * (K + 1)) ^ (M + 1) := by
    calc
      _ ≤ (K + 1) ^ (L + 1) * 2 ^ (L + 1) :=
        Nat.mul_le_mul_right _ (Nat.choose_le_pow (K + 1) (L + 1))
      _ = (2 * (K + 1)) ^ (L + 1) := by rw [mul_pow, mul_comm]
      _ ≤ _ := pow_le_pow_right' (by omega) (by have := (Finset.mem_Icc.mp hL).2; omega)
  calc
    _ ≤ ∑ _L ∈ Finset.Icc 1 M, (2 * (K + 1)) ^ (M + 1) := Finset.sum_le_sum hterm
    _ = M * (2 * (K + 1)) ^ (M + 1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ M)

lemma log_grid_scale (K : ℕ) (hK : 1 ≤ K) :
    Real.log (Real.exp 1 / (1 / (K : ℝ))) = 1 + Real.log (K : ℝ) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  rw [one_div, div_inv_eq_mul,
    Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hKpos), Real.log_exp]

lemma log_le_of_card_le (K M n : ℕ) (hK : 1 ≤ K) (hM : 1 ≤ M)
    (hn : n ≤ (M + 1) * (2 * (K + 1)) ^ (M + 1)) :
    Real.log (n : ℝ) ≤ 10 * M * Real.log (Real.exp 1 / (1 / (K : ℝ))) := by
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hMreal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hKpos : (0 : ℝ) < K := by linarith
  have hMnonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_natCast_nonneg K
  rw [log_grid_scale K hK]
  by_cases hnzero : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.log_zero]
    positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hnzero)
  have hlogn : Real.log (n : ℝ) ≤
      Real.log (((M : ℝ) + 1) * (2 * ((K : ℝ) + 1)) ^ (M + 1)) := by
    apply Real.log_le_log hnpos
    exact_mod_cast hn
  have hlogM : Real.log ((M : ℝ) + 1) ≤ M := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (M : ℝ) + 1)
    linarith
  have hlogbase : Real.log (2 * ((K : ℝ) + 1)) ≤ 3 * (1 + Real.log (K : ℝ)) := by
    have hcompare : 2 * ((K : ℝ) + 1) ≤ 4 * (K : ℝ) := by linarith
    have hlogcompare := Real.log_le_log (by positivity : 0 < 2 * ((K : ℝ) + 1)) hcompare
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hKpos)] at hlogcompare
    have hlogfour : Real.log (4 : ℝ) ≤ 3 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      norm_num at h ⊢
      exact h
    linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Nat.cast_add, Nat.cast_one] at hlogn
  have hmul : ((M : ℝ) + 1) * Real.log (2 * ((K : ℝ) + 1)) ≤
      ((M : ℝ) + 1) * (3 * (1 + Real.log (K : ℝ))) :=
    mul_le_mul_of_nonneg_left hlogbase (by positivity)
  have hdouble : (M : ℝ) + 1 ≤ 2 * M := by linarith
  have hmul' := mul_le_mul_of_nonneg_right hdouble
    (by positivity : 0 ≤ 3 * (1 + Real.log (K : ℝ)))
  have hMscale : (M : ℝ) ≤ M * (1 + Real.log (K : ℝ)) := by
    nlinarith [mul_nonneg hMnonneg hlogK]
  nlinarith [mul_nonneg hMnonneg hlogK]

end CalibratedMA.Randomized.LiftedLogBound


namespace CalibratedMA.Randomized.LiftedAssembly

lemma liftedClass_card_le (K M : ℕ) (hK : 1 ≤ K) :
    (liftedClass K M).card ≤
      ∑ L ∈ Finset.Icc 1 M, Nat.choose (K + 1) (L + 1) * 2 ^ (L + 1) := by
  classical
  let f : Finset ℕ × Finset ℕ → (ℝ → ℝ) := fun ST =>
    liftTest (partitionOfIndexSet K ST.1).1 (partitionOfIndexSet K ST.1).2
      (signTest K ST.2)
  have hrep : ∀ x ∈ liftedClass K M, ∃ S T : Finset ℕ,
      S ⊆ Finset.range (K + 1) ∧ 2 ≤ S.card ∧ S.card ≤ M + 1 ∧ T ⊆ S ∧ f (S, T) = x := by
    intro x hx
    unfold liftedClass at hx
    obtain ⟨⟨S,T⟩, hST, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hS, _⟩ := Finset.mem_product.mp hST
    obtain ⟨hSA, hzero, hlast, hcard⟩ := Finset.mem_filter.mp hS
    have hpair : ({0, K} : Finset ℕ) ⊆ S := by
      simp [Finset.insert_subset_iff, hzero, hlast]
    have htwo := Finset.card_le_card hpair
    rw [Finset.card_pair (show (0 : ℕ) ≠ K by omega)] at htwo
    refine ⟨S, T ∩ S, Finset.mem_powerset.mp hSA, htwo, hcard,
      Finset.inter_subset_right, ?_⟩
    exact (LiftedRestriction.liftTest_inter K S T hK hzero hlast).symm
  simpa only [Finset.card_range] using
    LiftedCounting.card_le_of_representatives (liftedClass K M) (Finset.range (K + 1)) M f hrep

end CalibratedMA.Randomized.LiftedAssembly

open CalibratedMA.Randomized

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ K M : ℕ, 1 ≤ K → 1 ≤ M →
      (liftedClass K M).card ≤
        ∑ L ∈ Finset.Icc 1 M, Nat.choose (K + 1) (L + 1) * 2 ^ (L + 1) ∧
      (∑ L ∈ Finset.Icc 1 M, Nat.choose (K + 1) (L + 1) * 2 ^ (L + 1)) ≤
        (M + 1) * (2 * (K + 1)) ^ (M + 1) ∧
      Real.log (liftedClass K M).card ≤ C * M * Real.log (Real.exp 1 / (1 / (K : ℝ))) := by
  refine ⟨10, by norm_num, ?_⟩
  intro K M hK hM
  have hcard := LiftedAssembly.liftedClass_card_le K M hK
  have hpoly := LiftedLogBound.counting_sum_le K M
  exact ⟨hcard, hpoly,
    LiftedLogBound.log_le_of_card_le K M _ hK hM (hcard.trans hpoly)⟩
