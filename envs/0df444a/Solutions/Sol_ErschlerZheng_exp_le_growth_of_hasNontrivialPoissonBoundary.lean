-- Prove2me | solution 1 for ErschlerZheng.exp_le_growth_of_hasNontrivialPoissonBoundary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-05T23:00:48.111981+00:00
-- url     : https://prove2.me/submissions/7ca83792-0ab2-445d-90b2-baf93e75bf2c

import Mathlib
import Definitions.Def_ErschlerZheng_Walks
import Theorems.Thm_ErschlerZheng_hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div
import Theorems.Thm_KaimanovichVershik_not_hasNontrivialPoissonBoundary_iff_asymptoticEntropy_eq_zero
import Theorems.Thm_KaimanovichVershik_exists_typical_finset_of_hasFiniteEntropy

section
/-!
# C1: Avez's asymptotic entropy exists (Erschler–Zheng p. 10)

`H(μ^{(n)})/n → h_μ`: entropy is subadditive under convolution, `H(μ ⋆ ν) ≤ H(μ) + H(ν)`,
so `n ↦ H(μ^{(n)})` is subadditive and Fekete's lemma applies.

All bookkeeping is done in `ℝ≥0∞`, where the series need no summability side conditions.
-/

namespace ErschlerZheng

namespace EntropyDev

open scoped ENNReal

set_option linter.unusedSectionVars false

variable {Γ : Type*} [Group Γ]

/-- The entropy series in `[0, ∞]`. -/
noncomputable def entE (μ : Γ → ℝ) : ℝ≥0∞ := ∑' g, ENNReal.ofReal (Real.negMulLog (μ g))

/-- Convolution of `[0, ∞]`-valued functions. -/
noncomputable def convE (a b : Γ → ℝ≥0∞) : Γ → ℝ≥0∞ := fun g => ∑' h, a h * b (h⁻¹ * g)

lemma le_one_of_isProb {μ : Γ → ℝ} (hμ : IsProbability μ) (g : Γ) : μ g ≤ 1 :=
  le_hasSum hμ.2 g (fun j _ => hμ.1 j)

lemma tsum_ofReal_of_isProb {μ : Γ → ℝ} (hμ : IsProbability μ) :
    ∑' g, ENNReal.ofReal (μ g) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg hμ.1 hμ.2.summable, hμ.2.tsum_eq, ENNReal.ofReal_one]

lemma isProb_of_tsum_ofReal {f : Γ → ℝ} (h0 : ∀ g, 0 ≤ f g)
    (h : ∑' g, ENNReal.ofReal (f g) = 1) : IsProbability f := by
  have hs : Summable f := by
    have := ENNReal.summable_toReal (f := fun g => ENNReal.ofReal (f g))
      (by rw [h]; exact ENNReal.one_ne_top)
    simpa [ENNReal.toReal_ofReal (h0 _)] using this
  refine ⟨h0, hs.hasSum_iff.mpr ?_⟩
  have := ENNReal.ofReal_tsum_of_nonneg h0 hs
  rw [h] at this
  exact ENNReal.ofReal_eq_one.mp this

lemma tsum_mulLeft_eq (F : Γ → ℝ≥0∞) (k : Γ) : ∑' m, F (k * m) = ∑' h, F h :=
  (Equiv.mulLeft k).tsum_eq F

lemma conv_summand_summable {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (g : Γ) :
    Summable fun h => μ h * ν (h⁻¹ * g) := by
  refine Summable.of_nonneg_of_le (fun h => mul_nonneg (hμ.1 h) (hν.1 _)) (fun h => ?_)
    hμ.2.summable
  calc μ h * ν (h⁻¹ * g) ≤ μ h * 1 :=
        mul_le_mul_of_nonneg_left (le_one_of_isProb hν _) (hμ.1 h)
    _ = μ h := mul_one _

lemma conv_nonneg {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (g : Γ) :
    0 ≤ conv μ ν g :=
  tsum_nonneg fun h => mul_nonneg (hμ.1 h) (hν.1 _)

lemma ofReal_conv {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) (g : Γ) :
    ENNReal.ofReal (conv μ ν g) =
      convE (fun x => ENNReal.ofReal (μ x)) (fun x => ENNReal.ofReal (ν x)) g := by
  unfold conv convE
  rw [ENNReal.ofReal_tsum_of_nonneg (fun h => mul_nonneg (hμ.1 h) (hν.1 _))
    (conv_summand_summable hμ hν g)]
  congr 1
  ext h
  rw [ENNReal.ofReal_mul (hμ.1 h)]

lemma isProb_conv {μ ν : Γ → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) :
    IsProbability (conv μ ν) := by
  refine isProb_of_tsum_ofReal (conv_nonneg hμ hν) ?_
  simp_rw [ofReal_conv hμ hν]
  unfold convE
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  have : ∀ h : Γ, ∑' g, ENNReal.ofReal (ν (h⁻¹ * g)) = 1 := fun h => by
    rw [tsum_mulLeft_eq (fun x => ENNReal.ofReal (ν x)) h⁻¹]
    exact tsum_ofReal_of_isProb hν
  simp_rw [this, mul_one]
  exact tsum_ofReal_of_isProb hμ

lemma isProb_convPow {μ : Γ → ℝ} (hμ : IsProbability μ) (n : ℕ) :
    IsProbability (convPow μ n) := by
  induction n with
  | zero =>
    classical
    refine ⟨fun g => ?_, ?_⟩
    · simp only [convPow]; split_ifs <;> norm_num
    · have : convPow μ 0 = fun g => if g = 1 then (1 : ℝ) else 0 := by
        ext g; simp only [convPow]
      rw [this]
      convert hasSum_ite_eq (1 : Γ) (1 : ℝ) using 1
  | succ n ih => exact isProb_conv ih hμ

lemma entropy_eq_toReal {μ : Γ → ℝ} (hμ : IsProbability μ) : entropy μ = (entE μ).toReal := by
  unfold entropy entE
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  congr 1
  ext g
  rw [ENNReal.toReal_ofReal (Real.negMulLog_nonneg (hμ.1 g) (le_one_of_isProb hμ g))]

end EntropyDev

end ErschlerZheng
end

section
/-!
# Word balls: word length is subadditive, balls are finite, `v(K r) ⩽ ((2|S|+1) v(r))^K`
-/

namespace ErschlerZheng

namespace WordBallDev

open Pointwise

variable {G : Type*} [Group G]

theorem wordBall_mono (S : Set G) {m n : ℕ} (h : m ≤ n) : Chou.wordBall S m ⊆ Chou.wordBall S n :=
  fun _ ⟨l, hl, hls, he⟩ => ⟨l, le_trans hl h, hls, he⟩

theorem wordBall_mul_subset (S : Set G) (m n : ℕ) :
    Chou.wordBall S m * Chou.wordBall S n ⊆ Chou.wordBall S (m + n) := by
  rintro _ ⟨_, ⟨l, hl, hls, rfl⟩, _, ⟨l', hl', hls', rfl⟩, rfl⟩
  refine ⟨l ++ l', by simp; omega, ?_, by simp⟩
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hls x h
  · exact hls' x h

theorem wordBall_add_subset (S : Set G) (m n : ℕ) :
    Chou.wordBall S (m + n) ⊆ Chou.wordBall S m * Chou.wordBall S n := by
  rintro _ ⟨l, hl, hls, rfl⟩
  refine ⟨(l.take m).prod, ⟨l.take m, by simp, fun x hx => hls x (List.mem_of_mem_take hx), rfl⟩,
    (l.drop m).prod, ⟨l.drop m, by simp; omega, fun x hx => hls x (List.mem_of_mem_drop hx), rfl⟩,
    ?_⟩
  show (l.take m).prod * (l.drop m).prod = l.prod
  rw [← List.prod_append, List.take_append_drop]

theorem one_mem_wordBall (S : Set G) (n : ℕ) : (1 : G) ∈ Chou.wordBall S n :=
  ⟨[], by simp, by simp, rfl⟩

theorem exists_mem_wordBall (S : Set G) (g : G) (hg : g ∈ Subgroup.closure S) :
    ∃ n, g ∈ Chou.wordBall S n := by
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact ⟨1, [s], by simp, by simp [hs], by simp⟩
  | one => exact ⟨0, one_mem_wordBall S 0⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨m, hm⟩ := ihg
    obtain ⟨n, hn⟩ := ihh
    exact ⟨m + n, wordBall_mul_subset S m n ⟨g, hm, h, hn, rfl⟩⟩
  | inv g _ ihg =>
    obtain ⟨m, l, hl, hls, rfl⟩ := ihg
    refine ⟨m, (l.map (·⁻¹)).reverse, by simp; omega, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_reverse, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rcases hls y hy with h | h
      · right; simpa using h
      · left; exact h
    · rw [List.prod_inv_reverse]

theorem mem_wordBall_wordLength (S : Set G) (hS : Subgroup.closure S = ⊤) (g : G) :
    g ∈ Chou.wordBall S (wordLength S g) := by
  obtain ⟨n, hn⟩ := exists_mem_wordBall S g (by rw [hS]; trivial)
  exact Nat.sInf_mem (s := {n | g ∈ Chou.wordBall S n}) ⟨n, hn⟩

theorem mem_wordBall_iff (S : Set G) (hS : Subgroup.closure S = ⊤) (g : G) (n : ℕ) :
    g ∈ Chou.wordBall S n ↔ wordLength S g ≤ n :=
  ⟨fun h => Nat.sInf_le h, fun h => wordBall_mono S h (mem_wordBall_wordLength S hS g)⟩

theorem wordLength_mul_le (S : Set G) (hS : Subgroup.closure S = ⊤) (g h : G) :
    wordLength S (g * h) ≤ wordLength S g + wordLength S h := by
  rw [← mem_wordBall_iff S hS]
  exact wordBall_mul_subset S _ _
    ⟨g, mem_wordBall_wordLength S hS g, h, mem_wordBall_wordLength S hS h, rfl⟩

theorem wordLength_one (S : Set G) : wordLength S (1 : G) = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (one_mem_wordBall S 0))

/-- The letters: `1`, the elements of `S`, and their inverses. -/
def letters (S : Finset G) : Set G := insert 1 ((S : Set G) ∪ (S : Set G)⁻¹)

theorem letters_finite (S : Finset G) : (letters S).Finite :=
  ((S.finite_toSet.union S.finite_toSet.inv)).insert 1

theorem card_letters_le (S : Finset G) : Nat.card (letters S) ≤ 2 * S.card + 1 := by
  rw [Nat.card_coe_set_eq]
  unfold letters
  calc (insert (1 : G) ((S : Set G) ∪ (S : Set G)⁻¹)).ncard
      ≤ ((S : Set G) ∪ (S : Set G)⁻¹).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ (S : Set G).ncard + ((S : Set G)⁻¹).ncard + 1 := by
        gcongr; exact Set.ncard_union_le _ _
    _ = 2 * S.card + 1 := by rw [Set.ncard_inv, Set.ncard_coe_finset]; ring

theorem wordBall_one_subset (S : Finset G) : Chou.wordBall (S : Set G) 1 ⊆ letters S := by
  rintro _ ⟨l, hl, hls, rfl⟩
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
  · simp [letters]
  · simp only [List.prod_cons, List.prod_nil, mul_one]
    rcases hls x (by simp) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · simp at hl

theorem wordBall_finite (S : Finset G) (n : ℕ) : (Chou.wordBall (S : Set G) n).Finite := by
  induction n with
  | zero =>
    refine Set.Finite.subset (Set.finite_singleton 1) ?_
    rintro _ ⟨l, hl, -, rfl⟩
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)]
    simp
  | succ n ih =>
    exact ((ih.mul (letters_finite S)).subset
      ((wordBall_add_subset _ n 1).trans (Set.mul_subset_mul_left (wordBall_one_subset S))))

theorem card_wordBall_succ_le (S : Finset G) (n : ℕ) :
    Nat.card (Chou.wordBall (S : Set G) (n + 1)) ≤
      Nat.card (Chou.wordBall (S : Set G) n) * (2 * S.card + 1) := by
  calc Nat.card (Chou.wordBall (S : Set G) (n + 1))
      ≤ Nat.card (Chou.wordBall (S : Set G) n * letters S : Set G) :=
        Nat.card_mono ((wordBall_finite S n).mul (letters_finite S))
          ((wordBall_add_subset _ n 1).trans (Set.mul_subset_mul_left (wordBall_one_subset S)))
    _ ≤ Nat.card (Chou.wordBall (S : Set G) n) * Nat.card (letters S) := Set.natCard_mul_le
    _ ≤ _ := Nat.mul_le_mul_left _ (card_letters_le S)

theorem card_wordBall_mul_le (S : Finset G) (k m : ℕ) :
    Nat.card (Chou.wordBall (S : Set G) (k * m)) ≤ Nat.card (Chou.wordBall (S : Set G) m) ^ k := by
  induction k with
  | zero =>
    simp only [zero_mul, pow_zero]
    have : Chou.wordBall (S : Set G) 0 ⊆ {1} := by
      rintro _ ⟨l, hl, -, rfl⟩
      rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)]; simp
    calc Nat.card (Chou.wordBall (S : Set G) 0) ≤ Nat.card ({1} : Set G) :=
          Nat.card_mono (Set.finite_singleton 1) this
      _ = 1 := by simp
  | succ k ih =>
    calc Nat.card (Chou.wordBall (S : Set G) ((k + 1) * m))
        ≤ Nat.card (Chou.wordBall (S : Set G) (k * m) * Chou.wordBall (S : Set G) m : Set G) := by
          rw [add_mul, one_mul]
          exact Nat.card_mono ((wordBall_finite S _).mul (wordBall_finite S _))
            (wordBall_add_subset _ _ _)
      _ ≤ Nat.card (Chou.wordBall (S : Set G) (k * m)) * Nat.card (Chou.wordBall (S : Set G) m) :=
          Set.natCard_mul_le
      _ ≤ Nat.card (Chou.wordBall (S : Set G) m) ^ k * Nat.card (Chou.wordBall (S : Set G) m) :=
          Nat.mul_le_mul_right _ ih
      _ = _ := (pow_succ _ _).symm

/-- `v(K r) ⩽ ((2|S|+1) v(r))^K`. -/
theorem growth_mul_le (S : Finset G) (K : ℕ) (r : ℝ) :
    growth (S : Set G) (K * r) ≤ ((2 * S.card + 1) * growth (S : Set G) r) ^ K := by
  unfold growth
  have hfl : ⌊(K : ℝ) * r⌋₊ ≤ K * (⌊r⌋₊ + 1) := by
    have h1 : (K : ℝ) * r ≤ ((K * (⌊r⌋₊ + 1) : ℕ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one r).le (Nat.cast_nonneg K)
    have := Nat.floor_mono h1
    rwa [Nat.floor_natCast] at this
  calc Nat.card (Chou.wordBall (S : Set G) ⌊(K : ℝ) * r⌋₊)
      ≤ Nat.card (Chou.wordBall (S : Set G) (K * (⌊r⌋₊ + 1))) :=
        Nat.card_mono (wordBall_finite S _) (wordBall_mono _ hfl)
    _ ≤ Nat.card (Chou.wordBall (S : Set G) (⌊r⌋₊ + 1)) ^ K := card_wordBall_mul_le S K _
    _ ≤ (Nat.card (Chou.wordBall (S : Set G) ⌊r⌋₊) * (2 * S.card + 1)) ^ K :=
        Nat.pow_le_pow_left (card_wordBall_succ_le S _) K
    _ = _ := by ring

end WordBallDev

end ErschlerZheng
end

section
/-!
# C4: Lemma 2.1 (p. 10), as a reduction to C2 and C3 (Kaimanovich–Vershik)

Route (the paper's). The boundary is non-trivial, so `h_μ > 0` (C2; `h_μ ⩾ 0` from C1). Truncate
`μ` to `ν = μ|_{B(ϱ_n)}`, of mass `⩾ 1 - 1/n`; then `ν^{(n)}` has mass `⩾ (1-1/n)^n ⩾ 1/8` and
`Σ_g ν^{(n)}(g)|g| ⩽ n φ(ϱ_n)` (subadditivity of `|·|`), so by Markov `μ^{(n)}(B(32 n φ(ϱ_n))) ⩾
ν^{(n)}(B(32 n φ(ϱ_n))) ⩾ 1/8 - 1/32`. The typical set of C3 meets that ball in mass `⩾ 5/64` with
points of mass `⩽ e^{-n(h-ε)}`, so `v(32 n φ(ϱ_n)) ⩾ (5/64) e^{n(h-ε)}`; finally
`v(32 r) ⩽ ((2|S|+1) v(r))^{32}`.
-/

open scoped ENNReal

namespace ErschlerZheng

namespace Lemma21Dev

set_option linter.unusedSectionVars false

open EntropyDev WordBallDev

variable {Γ : Type*} [Group Γ]

open scoped Classical in
/-- `[0, ∞]`-valued convolution powers. -/
noncomputable def convPowE (a : Γ → ℝ≥0∞) : ℕ → Γ → ℝ≥0∞
  | 0 => fun g => if g = 1 then 1 else 0
  | n + 1 => convE (convPowE a n) a

theorem ofReal_convPow {μ : Γ → ℝ} (hμ : IsProbability μ) (n : ℕ) (g : Γ) :
    ENNReal.ofReal (convPow μ n g) = convPowE (fun x => ENNReal.ofReal (μ x)) n g := by
  induction n generalizing g with
  | zero =>
    classical
    simp only [convPow, convPowE]
    split_ifs <;> simp
  | succ n ih =>
    simp only [convPow, convPowE]
    rw [ofReal_conv (isProb_convPow hμ n) hμ]
    congr 1
    funext x
    exact ih x

theorem convE_mono {a a' b b' : Γ → ℝ≥0∞} (ha : ∀ g, a g ≤ a' g) (hb : ∀ g, b g ≤ b' g) (g : Γ) :
    convE a b g ≤ convE a' b' g :=
  ENNReal.tsum_le_tsum fun h => mul_le_mul' (ha h) (hb _)

theorem convPowE_mono {a b : Γ → ℝ≥0∞} (hab : ∀ g, a g ≤ b g) (n : ℕ) (g : Γ) :
    convPowE a n g ≤ convPowE b n g := by
  induction n generalizing g with
  | zero => exact le_rfl
  | succ n ih => exact convE_mono ih hab g

theorem tsum_convPowE (a : Γ → ℝ≥0∞) (n : ℕ) : ∑' g, convPowE a n g = (∑' g, a g) ^ n := by
  induction n with
  | zero =>
    classical
    simp only [convPowE, pow_zero]
    rw [tsum_eq_single 1 (fun g hg => by simp [hg])]
    simp
  | succ n ih =>
    simp only [convPowE, convE]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    have : ∀ h : Γ, ∑' g, a (h⁻¹ * g) = ∑' g, a g := fun h => tsum_mulLeft_eq a h⁻¹
    simp_rw [this, ENNReal.tsum_mul_right, ih, pow_succ]

/-- The length moment: `Σ_g ν^{(n)}(g) |g| ⩽ n Σ_g ν(g)|g|` when `ν` has mass `⩽ 1`. -/
theorem length_moment_le (S : Set Γ) (hS : Subgroup.closure S = ⊤) (a : Γ → ℝ≥0∞)
    (ha : ∑' g, a g ≤ 1) (n : ℕ) :
    ∑' g, convPowE a n g * (wordLength S g : ℝ≥0∞) ≤ n * ∑' g, a g * (wordLength S g : ℝ≥0∞) := by
  induction n with
  | zero =>
    classical
    simp only [convPowE, Nat.cast_zero, zero_mul, nonpos_iff_eq_zero, ENNReal.tsum_eq_zero]
    intro g
    split_ifs with h
    · subst h; simp [wordLength_one]
    · simp
  | succ n ih =>
    simp only [convPowE, convE]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    have hre : ∀ h : Γ, ∑' g, convPowE a n h * a (h⁻¹ * g) * (wordLength S g : ℝ≥0∞) =
        ∑' k, convPowE a n h * a k * (wordLength S (h * k) : ℝ≥0∞) := by
      intro h
      rw [← tsum_mulLeft_eq _ h]
      simp only [inv_mul_cancel_left]
    simp_rw [hre]
    have e1 : ∀ h k, convPowE a n h * a k * (wordLength S h : ℝ≥0∞) =
        (convPowE a n h * (wordLength S h : ℝ≥0∞)) * a k := fun h k => by ring
    have e2 : ∀ h k, convPowE a n h * a k * (wordLength S k : ℝ≥0∞) =
        convPowE a n h * (a k * (wordLength S k : ℝ≥0∞)) := fun h k => by ring
    calc ∑' h, ∑' k, convPowE a n h * a k * (wordLength S (h * k) : ℝ≥0∞)
        ≤ ∑' h, ∑' k, convPowE a n h * a k *
            ((wordLength S h : ℝ≥0∞) + (wordLength S k : ℝ≥0∞)) := by
          refine ENNReal.tsum_le_tsum fun h => ENNReal.tsum_le_tsum fun k => ?_
          gcongr
          exact_mod_cast wordLength_mul_le S hS h k
      _ = (∑' h, convPowE a n h * (wordLength S h : ℝ≥0∞)) * ∑' k, a k +
            (∑' h, convPowE a n h) * ∑' g, a g * (wordLength S g : ℝ≥0∞) := by
          simp_rw [mul_add, ENNReal.tsum_add, e1, e2, ENNReal.tsum_mul_left,
            ENNReal.tsum_mul_right]
      _ ≤ n * (∑' g, a g * (wordLength S g : ℝ≥0∞)) * 1 +
            1 * ∑' g, a g * (wordLength S g : ℝ≥0∞) := by
          gcongr
          rw [tsum_convPowE]
          exact pow_le_one₀ bot_le ha
      _ = (n + 1 : ℕ) * ∑' g, a g * (wordLength S g : ℝ≥0∞) := by push_cast; ring


/-! ### Masses in `[0, ∞]` -/

theorem ofReal_mass {μ : Γ → ℝ} (h0 : ∀ g, 0 ≤ μ g) (hs : Summable μ) (X : Set Γ) :
    ENNReal.ofReal (mass μ X) = ∑' g, X.indicator (fun x => ENNReal.ofReal (μ x)) g := by
  unfold mass
  rw [ENNReal.ofReal_tsum_of_nonneg (fun g => Set.indicator_nonneg (fun x _ => h0 x) g)
    (hs.indicator X)]
  congr 1
  funext g
  by_cases hg : g ∈ X <;> simp [Set.indicator, hg]

theorem mass_le_one_div {S : Finset Γ} {μ : Γ → ℝ} (hμ : IsProbability μ) {n : ℕ} (hn : 1 ≤ n)
    {ϱ : ℝ} (hϱ : ϱ = sInf {r : ℝ | 0 < r ∧
      mass μ {g | r ≤ (wordLength (S : Set Γ) g : ℝ)} < 1 / n}) :
    0 ≤ ϱ ∧ mass μ {g | ϱ < (wordLength (S : Set Γ) g : ℝ)} ≤ 1 / n := by
  set A := {r : ℝ | 0 < r ∧ mass μ {g | r ≤ (wordLength (S : Set Γ) g : ℝ)} < 1 / n}
  have hpos : (0 : ℝ) < 1 / n := by positivity
  -- `A` is non-empty: the tail of `μ` outside a finite set is small
  have hne : A.Nonempty := by
    have htot : ∑' g, ENNReal.ofReal (μ g) ≠ ⊤ := by
      rw [tsum_ofReal_of_isProb hμ]; exact ENNReal.one_ne_top
    have hlim := ENNReal.tendsto_tsum_compl_atTop_zero htot
    obtain ⟨F, hF⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hpos))).exists
    refine ⟨((F.sup (wordLength (S : Set Γ)) : ℕ) : ℝ) + 1, by positivity, ?_⟩
    rw [← ENNReal.ofReal_lt_ofReal_iff hpos, ofReal_mass hμ.1 hμ.2.summable]
    refine lt_of_le_of_lt ?_ hF
    rw [show (∑' (b : {x // x ∉ F}), ENNReal.ofReal (μ b)) =
        ∑' g, ({g | g ∉ F} : Set Γ).indicator (fun x => ENNReal.ofReal (μ x)) g from
      tsum_subtype {g | g ∉ F} (fun x => ENNReal.ofReal (μ x))]
    refine ENNReal.tsum_le_tsum fun g => ?_
    by_cases hg : ((F.sup (wordLength (S : Set Γ)) : ℕ) : ℝ) + 1 ≤ (wordLength (S : Set Γ) g : ℝ)
    · have hgF : g ∉ F := by
        intro hgF
        have := Finset.le_sup (f := wordLength (S : Set Γ)) hgF
        have : (wordLength (S : Set Γ) g : ℝ) ≤ F.sup (wordLength (S : Set Γ)) := by
          exact_mod_cast this
        linarith
      simp [Set.indicator, hg, hgF]
    · simp [Set.indicator, hg]
  have hbdd : BddBelow A := ⟨0, fun r hr => hr.1.le⟩
  have hϱ0 : 0 ≤ ϱ := by rw [hϱ]; exact le_csInf hne fun r hr => hr.1.le
  refine ⟨hϱ0, ?_⟩
  obtain ⟨r, hrA, hr⟩ := exists_lt_of_csInf_lt hne
    (show sInf A < ((⌊ϱ⌋₊ + 1 : ℕ) : ℝ) by
      rw [← hϱ]; push_cast; exact Nat.lt_floor_add_one ϱ)
  refine le_trans ?_ hrA.2.le
  unfold mass
  refine Summable.tsum_le_tsum (fun g => ?_) (hμ.2.summable.indicator _) (hμ.2.summable.indicator _)
  by_cases hg : ϱ < (wordLength (S : Set Γ) g : ℝ)
  · have h1 : ⌊ϱ⌋₊ < wordLength (S : Set Γ) g := (Nat.floor_lt hϱ0).mpr hg
    have h2 : r ≤ (wordLength (S : Set Γ) g : ℝ) := by
      have : ((⌊ϱ⌋₊ + 1 : ℕ) : ℝ) ≤ (wordLength (S : Set Γ) g : ℝ) := by exact_mod_cast h1
      linarith
    simp [Set.indicator, hg, h2]
  · simp only [Set.indicator, Set.mem_ofPred_eq, hg, if_false]
    split_ifs
    · exact hμ.1 g
    · exact le_rfl

theorem one_sub_inv_pow_ge (n : ℕ) (hn : 2 ≤ n) : (1 / 8 : ℝ) ≤ (1 - 1 / n) ^ n := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n - 1 := by linarith
  have h1 : Real.exp (-(1 / (n - 1))) ≤ 1 - 1 / n := by
    have := Real.add_one_le_exp (1 / (n - 1))
    have hpos : (0 : ℝ) < 1 / (n - 1) + 1 := by positivity
    have e : 1 - 1 / (n : ℝ) = 1 / (1 / (n - 1) + 1) := by field_simp; ring
    rw [e, Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hpos this
  have h2 : Real.exp (-2) ≤ Real.exp (-(1 / (n - 1))) ^ n := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : (n : ℝ) * (1 / (n - 1)) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hn0]; linarith
    linarith
  have h3 : (1 / 8 : ℝ) ≤ Real.exp (-2) := by
    rw [Real.exp_neg, show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    have := Real.exp_one_lt_d9
    have hp := Real.exp_pos 1
    rw [one_div]
    apply inv_anti₀ (by positivity)
    nlinarith
  calc (1 / 8 : ℝ) ≤ Real.exp (-2) := h3
    _ ≤ Real.exp (-(1 / (n - 1))) ^ n := h2
    _ ≤ (1 - 1 / n) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le h1 n


/-- The ball of radius `32 n φ(ϱ_n)` carries `μ^{(n)}`-mass at least `3/32`. -/
theorem ball_mass_ge (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤) {μ : Γ → ℝ}
    (hμ : IsProbability μ) (n : ℕ) (hn : 2 ≤ n) {ϱ : ℝ}
    (hϱ : ϱ = sInf {r : ℝ | 0 < r ∧ mass μ {g | r ≤ (wordLength (S : Set Γ) g : ℝ)} < 1 / n})
    {φ : ℝ} (hφ : φ = ∑' g : ball (S : Set Γ) ϱ, (wordLength (S : Set Γ) g : ℝ) * μ g) :
    (3 / 32 : ℝ) ≤ mass (convPow μ n) {g | (wordLength (S : Set Γ) g : ℝ) ≤ 32 * n * φ} := by
  obtain ⟨hϱ0, htail⟩ := mass_le_one_div hμ (by omega : 1 ≤ n) hϱ
  set ℓ : Γ → ℕ := wordLength (S : Set Γ) with hℓ
  set μE : Γ → ℝ≥0∞ := fun x => ENNReal.ofReal (μ x) with hμE
  set B0 : Set Γ := {g | (ℓ g : ℝ) ≤ ϱ} with hB0
  set ν : Γ → ℝ≥0∞ := B0.indicator μE with hν
  have hνμ : ∀ g, ν g ≤ μE g := fun g => Set.indicator_le_self _ _ g
  have hμ1 : ∑' g, μE g = 1 := tsum_ofReal_of_isProb hμ
  have hsplit : ∑' g, ν g + ∑' g, B0ᶜ.indicator μE g = 1 := by
    rw [← ENNReal.tsum_add, ← hμ1]
    congr 1; funext g; exact congrFun (Set.indicator_self_add_compl B0 μE) g
  have htail' : ∑' g, B0ᶜ.indicator μE g ≤ ENNReal.ofReal (1 / n) := by
    have hc : B0ᶜ = {g | ϱ < (ℓ g : ℝ)} := by ext g; simp [B0, not_le]
    rw [hc, ← ofReal_mass hμ.1 hμ.2.summable]
    exact ENNReal.ofReal_le_ofReal htail
  have hνmass : ENNReal.ofReal (1 - 1 / n) ≤ ∑' g, ν g := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, tsub_le_iff_right]
    calc (1 : ℝ≥0∞) = ∑' g, ν g + ∑' g, B0ᶜ.indicator μE g := hsplit.symm
      _ ≤ ∑' g, ν g + ENNReal.ofReal (1 / n) := by gcongr
  have hν1 : ∑' g, ν g ≤ 1 := hμ1 ▸ ENNReal.tsum_le_tsum hνμ
  have hφ0 : 0 ≤ φ := by
    rw [hφ]; exact tsum_nonneg fun g => mul_nonneg (Nat.cast_nonneg _) (hμ.1 g)
  have hΦ : ∑' g, ν g * (ℓ g : ℝ≥0∞) = ENNReal.ofReal φ := by
    rw [hφ]
    have hsum : Summable fun g : ball (S : Set Γ) ϱ => (ℓ g : ℝ) * μ g := by
      refine Summable.of_nonneg_of_le (fun g => mul_nonneg (Nat.cast_nonneg _) (hμ.1 g))
        (fun g => ?_) ((hμ.2.summable.subtype _).mul_left ϱ)
      exact mul_le_mul_of_nonneg_right g.2 (hμ.1 g)
    rw [ENNReal.ofReal_tsum_of_nonneg (f := fun g : ball (S : Set Γ) ϱ => (ℓ g : ℝ) * μ g)
        (fun g => mul_nonneg (Nat.cast_nonneg _) (hμ.1 g)) hsum,
      tsum_subtype (ball (S : Set Γ) ϱ) (fun g => ENNReal.ofReal ((ℓ g : ℝ) * μ g))]
    congr 1; funext g
    by_cases hg : g ∈ B0
    · have hg' : g ∈ ball (S : Set Γ) ϱ := hg
      rw [hν, Set.indicator_of_mem hg, Set.indicator_of_mem hg',
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_comm]
    · have hg' : g ∉ ball (S : Set Γ) ϱ := hg
      rw [hν, Set.indicator_of_notMem hg, Set.indicator_of_notMem hg', zero_mul]
  set P := convPowE ν n with hP
  have hmom : ∑' g, P g * (ℓ g : ℝ≥0∞) ≤ n * ENNReal.ofReal φ := by
    rw [← hΦ]; exact length_moment_le (S : Set Γ) hS ν hν1 n
  set T : Set Γ := {g | 32 * n * φ < (ℓ g : ℝ)} with hT
  have hTmass : ∑' g, T.indicator P g ≤ ENNReal.ofReal (1 / 32) := by
    rcases hφ0.lt_or_eq with hφpos | hφz
    · have key : ENNReal.ofReal (32 * n * φ) * ∑' g, T.indicator P g ≤ n * ENNReal.ofReal φ := by
        refine le_trans ?_ hmom
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun g => ?_
        by_cases hg : g ∈ T
        · rw [Set.indicator_of_mem hg, mul_comm]
          gcongr
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hg.le
        · rw [Set.indicator_of_notMem hg, mul_zero]; exact bot_le
      have e : ENNReal.ofReal (32 * n * φ) = (n * ENNReal.ofReal φ) * 32 := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
        simp only [ENNReal.ofReal_ofNat]
        ring
      rw [e, mul_assoc] at key
      have ha0 : (n : ℝ≥0∞) * ENNReal.ofReal φ ≠ 0 := by
        apply mul_ne_zero
        · exact_mod_cast (show n ≠ 0 by omega)
        · exact (ENNReal.ofReal_pos.mpr hφpos).ne'
      have hat : (n : ℝ≥0∞) * ENNReal.ofReal φ ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) ENNReal.ofReal_ne_top
      have k2 := (ENNReal.mul_le_mul_iff_right ha0 hat).mp (key.trans_eq (mul_one _).symm)
      rw [show ENNReal.ofReal (1 / 32) = 1 / 32 by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_comm]
      exact k2
    · have hz : ∑' g, P g * (ℓ g : ℝ≥0∞) = 0 := by
        apply le_antisymm _ bot_le
        rw [← hφz] at hmom
        simpa using hmom
      rw [ENNReal.tsum_eq_zero] at hz
      have : ∑' g, T.indicator P g = 0 := by
        rw [ENNReal.tsum_eq_zero]
        intro g
        by_cases hg : g ∈ T
        · rw [Set.indicator_of_mem hg]
          have hpos : (ℓ g : ℝ≥0∞) ≠ 0 := by
            have : (0 : ℝ) < ℓ g := by
              have := hg; simp only [hT, Set.mem_ofPred_eq, ← hφz, mul_zero] at this; exact this
            exact_mod_cast (Nat.cast_pos.mp this).ne'
          exact (mul_eq_zero.mp (hz g)).resolve_right hpos
        · rw [Set.indicator_of_notMem hg]
      rw [this]; exact bot_le
  have hPmass : ENNReal.ofReal (1 / 8) ≤ ∑' g, P g := by
    rw [hP, tsum_convPowE]
    calc ENNReal.ofReal (1 / 8) ≤ ENNReal.ofReal ((1 - 1 / n) ^ n) :=
          ENNReal.ofReal_le_ofReal (one_sub_inv_pow_ge n hn)
      _ = ENNReal.ofReal (1 - 1 / n) ^ n := by
          rw [ENNReal.ofReal_pow (by
            have : (1 : ℝ) / n ≤ 1 := by
              rw [div_le_one (by positivity)]; exact_mod_cast (by omega : 1 ≤ n)
            linarith)]
      _ ≤ (∑' g, ν g) ^ n := by gcongr
  have hshort : ENNReal.ofReal (3 / 32) ≤ ∑' g, Tᶜ.indicator P g := by
    have hsum : ∑' g, P g = ∑' g, T.indicator P g + ∑' g, Tᶜ.indicator P g := by
      rw [← ENNReal.tsum_add]; congr 1; funext g
      exact (congrFun (Set.indicator_self_add_compl T P) g).symm
    have : ENNReal.ofReal (3 / 32) = ENNReal.ofReal (1 / 8) - ENNReal.ofReal (1 / 32) := by
      rw [← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
    rw [this, tsub_le_iff_right]
    calc ENNReal.ofReal (1 / 8) ≤ ∑' g, P g := hPmass
      _ = ∑' g, Tᶜ.indicator P g + ∑' g, T.indicator P g := by rw [hsum, add_comm]
      _ ≤ ∑' g, Tᶜ.indicator P g + ENNReal.ofReal (1 / 32) := by gcongr
  have hcmp : ∑' g, Tᶜ.indicator P g ≤
      ∑' g, Tᶜ.indicator (fun x => ENNReal.ofReal (convPow μ n x)) g := by
    refine ENNReal.tsum_le_tsum fun g => Set.indicator_le_indicator ?_
    rw [ofReal_convPow hμ n g]
    exact convPowE_mono hνμ n g
  have hTc : Tᶜ = {g | (ℓ g : ℝ) ≤ 32 * n * φ} := by ext g; simp [hT, not_lt]
  have hfin := hshort.trans hcmp
  rw [← ofReal_mass (isProb_convPow hμ n).1 (isProb_convPow hμ n).2.summable, hTc] at hfin
  exact (ENNReal.ofReal_le_ofReal_iff (by
    unfold mass; exact tsum_nonneg fun g => Set.indicator_nonneg
      (fun x _ => (isProb_convPow hμ n).1 x) g)).mp hfin

end Lemma21Dev

end ErschlerZheng
end

section
open scoped ENNReal
open ErschlerZheng
open Lemma21Dev EntropyDev WordBallDev in
theorem solution {Γ : Type*} [Group Γ] (S : Finset Γ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) (μ : Γ → ℝ) (hμ : IsProbability μ)
    (hH : HasFiniteEntropy μ) (hP : HasNontrivialPoissonBoundary μ)
    (ϱ : ℕ → ℝ)
    (hϱ : ∀ n : ℕ, ϱ n =
      sInf {r : ℝ | 0 < r ∧ mass μ {g | r ≤ (wordLength (S : Set Γ) g : ℝ)} < 1 / n})
    (φ : ℝ → ℝ)
    (hφ : ∀ r : ℝ, φ r = ∑' g : ball (S : Set Γ) r, (wordLength (S : Set Γ) g : ℝ) * μ g) :
    ∃ c > 0, ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (c * n) ≤ growth (S : Set Γ) (n * φ (ϱ n)) := by
  -- `Γ` is countable
  have : Countable Γ := by
    have hU : (Set.univ : Set Γ) = ⋃ n : ℕ, Chou.wordBall (S : Set Γ) n := by
      ext g
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      exact exists_mem_wordBall (S : Set Γ) g (by rw [hS]; trivial)
    have : (Set.univ : Set Γ).Countable := by
      rw [hU]; exact Set.countable_iUnion fun n => (wordBall_finite S n).countable
    exact Set.countable_univ_iff.mp this
  -- `h_μ > 0`
  set h := asymptoticEntropy μ with hh
  have hh0 : 0 ≤ h := by
    have T := (hasFiniteEntropy_convPow_and_tendsto_entropy_convPow_div μ hμ hH).2
    refine ge_of_tendsto T (Filter.Eventually.of_forall fun n => ?_)
    rw [entropy_eq_toReal (isProb_convPow hμ n)]
    positivity
  have hhne : h ≠ 0 := fun e =>
    ((KaimanovichVershik.not_hasNontrivialPoissonBoundary_iff_asymptoticEntropy_eq_zero μ hμ
      hH).mpr e) hP
  have hhpos : 0 < h := lt_of_le_of_ne hh0 (Ne.symm hhne)
  set ε := min (h / 2) (1 / 64) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεh : ε ≤ h / 2 := min_le_left _ _
  have hε64 : ε ≤ 1 / 64 := min_le_right _ _
  obtain ⟨N, hN⟩ := KaimanovichVershik.exists_typical_finset_of_hasFiniteEntropy μ hμ hH ε hε0
  set C : ℝ := (2 * S.card + 1 : ℝ) with hC
  have hC1 : 1 ≤ C := by rw [hC]; linarith [(Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)]
  -- large `n`
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → 64 / 5 * C ^ 32 < Real.exp (n * (h / 4)) := by
    refine ⟨⌈64 / 5 * C ^ 32 / (h / 4)⌉₊ + 1, fun n hn => ?_⟩
    have h1 : 64 / 5 * C ^ 32 / (h / 4) < n := by
      have := Nat.le_ceil (64 / 5 * C ^ 32 / (h / 4))
      have : (⌈64 / 5 * C ^ 32 / (h / 4)⌉₊ + 1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h2 : 64 / 5 * C ^ 32 < n * (h / 4) := by
      rwa [div_lt_iff₀ (by positivity)] at h1
    linarith [Real.add_one_le_exp (n * (h / 4))]
  refine ⟨h / 128, by positivity, Filter.eventually_atTop.mpr ⟨max (N + 1) (max 2 N₁),
    fun n hn => ?_⟩⟩
  have hnN : N < n := by omega
  have hn2 : 2 ≤ n := by omega
  have hnN₁ : N₁ ≤ n := by omega
  obtain ⟨V, hVmass, hVpt⟩ := hN n hnN
  set R : ℝ := 32 * n * φ (ϱ n) with hR
  set B : Set Γ := {g | (wordLength (S : Set Γ) g : ℝ) ≤ R} with hB
  have hBmass : (3 / 32 : ℝ) ≤ mass (convPow μ n) B :=
    ball_mass_ge S hS hμ n hn2 (hϱ n) (hφ (ϱ n))
  have hPn := isProb_convPow hμ n
  -- the part of `V` in the ball
  classical
  set W := V.filter (· ∈ B) with hW
  have hVsum : mass (convPow μ n) (V : Set Γ) = ∑ x ∈ V, convPow μ n x := by
    unfold mass; rw [sum_eq_tsum_indicator]
  have hcompl : ∑ x ∈ V with x ∉ B, convPow μ n x ≤ mass (convPow μ n) Bᶜ := by
    rw [sum_eq_tsum_indicator]
    unfold mass
    refine Summable.tsum_le_tsum (fun g => ?_) (hPn.2.summable.indicator _)
      (hPn.2.summable.indicator _)
    by_cases hg : g ∈ ((V.filter (· ∉ B) : Finset Γ) : Set Γ)
    · have hgB : g ∈ Bᶜ := (Finset.mem_filter.mp hg).2
      rw [Set.indicator_of_mem hg, Set.indicator_of_mem hgB]
    · rw [Set.indicator_of_notMem hg]
      exact Set.indicator_nonneg (fun x _ => hPn.1 x) g
  have hBc : mass (convPow μ n) B + mass (convPow μ n) Bᶜ = 1 := by
    unfold mass
    rw [← (hPn.2.summable.indicator B).tsum_add (hPn.2.summable.indicator Bᶜ)]
    rw [show (fun g => B.indicator (convPow μ n) g + Bᶜ.indicator (convPow μ n) g) =
      convPow μ n from funext fun g => congrFun (Set.indicator_self_add_compl B _) g]
    exact hPn.2.tsum_eq
  have hWsum : (5 / 64 : ℝ) ≤ ∑ x ∈ W, convPow μ n x := by
    have := Finset.sum_filter_add_sum_filter_not V (· ∈ B) (convPow μ n)
    rw [← hVsum] at this
    linarith
  have hWcard : (5 / 64 : ℝ) ≤ W.card * Real.exp (-(n * (h - ε))) := by
    refine hWsum.trans ?_
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun x hx => (hVpt x (Finset.mem_filter.mp hx).1).2
  have hWgrowth : W.card ≤ growth (S : Set Γ) R := by
    unfold growth
    have hsub : ((W : Set Γ)) ⊆ Chou.wordBall (S : Set Γ) ⌊R⌋₊ := by
      intro x hx
      have hxB : (wordLength (S : Set Γ) x : ℝ) ≤ R := (Finset.mem_filter.mp hx).2
      rw [mem_wordBall_iff (S : Set Γ) hS]
      exact Nat.le_floor hxB
    have := Nat.card_mono (wordBall_finite S _) hsub
    rwa [Nat.card_coe_set_eq, Set.ncard_coe_finset] at this
  have hgrow := growth_mul_le S 32 (n * φ (ϱ n))
  rw [show ((32 : ℕ) : ℝ) * (n * φ (ϱ n)) = R by rw [hR]; push_cast; ring] at hgrow
  set G := growth (S : Set Γ) (n * φ (ϱ n)) with hG
  -- combine
  have hmain : (5 / 64 : ℝ) * Real.exp (n * (h - ε)) ≤ (C * G) ^ 32 := by
    have e1 : (5 / 64 : ℝ) * Real.exp (n * (h - ε)) ≤ W.card := by
      have hexp : Real.exp (-(n * (h - ε))) * Real.exp (n * (h - ε)) = 1 := by
        rw [← Real.exp_add]; simp
      calc (5 / 64 : ℝ) * Real.exp (n * (h - ε))
          ≤ W.card * Real.exp (-(n * (h - ε))) * Real.exp (n * (h - ε)) := by gcongr
        _ = W.card := by rw [mul_assoc, hexp, mul_one]
    have e2 : (W.card : ℝ) ≤ ((2 * S.card + 1) * G : ℕ) ^ 32 := by
      exact_mod_cast hWgrowth.trans hgrow
    calc (5 / 64 : ℝ) * Real.exp (n * (h - ε)) ≤ W.card := e1
      _ ≤ (((2 * S.card + 1) * G : ℕ) : ℝ) ^ 32 := e2
      _ = (C * G) ^ 32 := by rw [hC]; push_cast; ring
  by_contra hcon
  push Not at hcon
  have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg _
  have hlt : (C * G) ^ 32 < C ^ 32 * Real.exp (n * (h / 4)) := by
    have h1 : C * G < C * Real.exp (h / 128 * n) := by
      exact mul_lt_mul_of_pos_left hcon (by linarith)
    calc (C * G) ^ 32 < (C * Real.exp (h / 128 * n)) ^ 32 :=
          pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
      _ = C ^ 32 * Real.exp (n * (h / 4)) := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hexp2 : Real.exp (n * (h / 4)) * Real.exp (n * (h / 4)) ≤ Real.exp (n * (h - ε)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hE := hN₁ n hnN₁
  have hEpos := Real.exp_pos (n * (h / 4))
  nlinarith [hmain, hlt, hexp2, hE, hEpos]
end
