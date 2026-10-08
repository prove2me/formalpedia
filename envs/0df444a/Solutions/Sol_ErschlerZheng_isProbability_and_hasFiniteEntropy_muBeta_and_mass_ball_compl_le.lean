-- Prove2me | solution 1 for ErschlerZheng.isProbability_and_hasFiniteEntropy_muBeta_and_mass_ball_compl_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T10:10:12.546495+00:00
-- url     : https://prove2.me/submissions/0d12141c-30ac-4f3e-a60c-8b20195221b0

import Mathlib
import Definitions.Def_ErschlerZheng_Walks
import Definitions.Def_ErschlerZheng_Grigorchuk
import Definitions.Def_ErschlerZheng_Construction
import Theorems.Thm_ErschlerZheng_mem_grigorchuk_and_wordLength_le_of_upsilon_ne_zero
import Theorems.Thm_ErschlerZheng_injOn_gTilde_and_ncard_fSet_eq
import Theorems.Thm_ErschlerZheng_two_mul_lengthL_le_lengthL_succ

section
/-!
# Word balls: word length is subadditive, balls are finite, `v(K r) ⩽ ((2|S|+1) v(r))^K`
-/

namespace ErschlerZheng

namespace WordBallDev

open Pointwise

variable {G : Type*} [Group G]

theorem wordBall_mul_subset (S : Set G) (m n : ℕ) :
    Chou.wordBall S m * Chou.wordBall S n ⊆ Chou.wordBall S (m + n) := by
  rintro _ ⟨_, ⟨l, hl, hls, rfl⟩, _, ⟨l', hl', hls', rfl⟩, rfl⟩
  refine ⟨l ++ l', by simp; omega, ?_, by simp⟩
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hls x h
  · exact hls' x h

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

end WordBallDev

end ErschlerZheng
end

section
/-!
# J2: Corollary 8.2 (Erschler–Zheng p. 57), from Lemma 8.1, (7.7) and (8.1)

For `D ∣ n`, `n ⩾ 1`: each `𝔉_{j,n}` is finite and non-empty ((7.7) gives `|𝔉_{j,n}| = 2^{…}`
in the first case, a singleton otherwise), so `Λ_n` is finite and non-empty and `υ_n` is a
probability on `Aut(T)`; by Lemma 8.1 it lives on `G_ω`, and so does `υ̌_n`.

* `μ_β` is a probability: `½ + ½ Σ_n C_β 2^{−nβ}·2 = 1`, by the definition of `C_β`.
* Finite entropy: `−p log p` is subadditive over the pieces of `μ_β`; `H(υ_n) ⩽ log |Λ_n|`
  (`υ_n ⩾ 1/|Λ_n|` on its support) and `log₂ |Λ_n| ⩽ n(1 + 2k_n) ⩽ n + 2n²` eventually.
* Tail: `supp υ_m ⊆ B(2^{2k_m+2D+4} L_m) ⊆ B(2^{2k_n} L_n)` for `m + 2D + 4 ⩽ n` (`k` monotone,
  `L_n ⩾ 2^{n−m} L_m`), so the mass outside is at most `C_β Σ_{m > n−2D−4} 2^{−mβ}`.
-/

namespace ErschlerZheng

namespace P5Cor82Dev

open Garrido Filter Topology

set_option linter.unusedSectionVars false

variable {D : ℕ} {ω : ℕ → Fin 3} {k : ℕ → ℕ}

lemma fSet_finite_nonempty (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ}
    (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j) :
    (fSet D ω k j n).Finite ∧ (fSet D ω k j n).Nonempty := by
  by_cases hc : ω (j - 1) = 2 ∧ n < j + k n ∧ j ≤ n
  · have h := (injOn_gTilde_and_ncard_fSet_eq D ω hω k hk n hn j hj1 hc.1 hc.2.1 hc.2.2).2.2
    have hpos : 0 < (fSet D ω k j n).ncard := by rw [h]; positivity
    exact ⟨Set.finite_of_ncard_pos hpos, Set.nonempty_of_ncard_ne_zero hpos.ne'⟩
  · simp only [fSet, if_neg hc]
    exact ⟨Set.finite_singleton _, Set.singleton_nonempty _⟩

lemma fSet_ncard_le (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ}
    (hn : D ∣ n) (j : ℕ) (hj1 : 1 ≤ j) : (fSet D ω k j n).ncard ≤ 2 ^ (2 * k n) := by
  by_cases hc : ω (j - 1) = 2 ∧ n < j + k n ∧ j ≤ n
  · rw [(injOn_gTilde_and_ncard_fSet_eq D ω hω k hk n hn j hj1 hc.1 hc.2.1 hc.2.2).2.2]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _ |>.trans (Nat.sub_le _ _))
  · simp only [fSet, if_neg hc, Set.ncard_singleton]
    exact Nat.one_le_two_pow

lemma lambda_finite (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ} (hn : D ∣ n) :
    Finite (LambdaN D ω k n) := by
  have : ∀ i : Fin n, Finite (fSet D ω k (i + 1) n) := fun i =>
    (fSet_finite_nonempty hω hk hn (i + 1) (by omega)).1.to_subtype
  infer_instance

lemma lambda_nonempty (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ} (hn : D ∣ n) :
    Nonempty (LambdaN D ω k n) :=
  ⟨(fun _ => false, fun i => ⟨_, (fSet_finite_nonempty hω hk hn (i + 1) (by omega)).2.some_mem⟩)⟩

lemma card_lambda_pos (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ} (hn : D ∣ n) :
    0 < Nat.card (LambdaN D ω k n) := by
  have := lambda_finite hω hk hn
  have := lambda_nonempty hω hk hn
  exact Nat.card_pos

lemma card_lambda_le (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ} (hn : D ∣ n) :
    Nat.card (LambdaN D ω k n) ≤ 2 ^ (n * (1 + 2 * k n)) := by
  have hfin : ∀ i : Fin n, Finite (fSet D ω k (i + 1) n) := fun i =>
    (fSet_finite_nonempty hω hk hn (i + 1) (by omega)).1.to_subtype
  have h1 : Nat.card (Fin n → Bool) = 2 ^ n := by simp
  rw [Nat.card_prod, h1]
  have h2 : Nat.card (fProd D ω k n) ≤ 2 ^ (2 * k n * n) := by
    show Nat.card ((i : Fin n) → ↥(fSet D ω k (i + 1) n)) ≤ _
    rw [Nat.card_pi]
    calc ∏ i : Fin n, Nat.card (fSet D ω k (i + 1) n) ≤ ∏ _i : Fin n, 2 ^ (2 * k n) := by
          apply Finset.prod_le_prod'
          intro i _
          rw [Nat.card_coe_set_eq]
          exact fSet_ncard_le hω hk hn _ (by omega)
      _ = 2 ^ (2 * k n * n) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  calc 2 ^ n * Nat.card (fProd D ω k n) ≤ 2 ^ n * 2 ^ (2 * k n * n) :=
        Nat.mul_le_mul_left _ h2
    _ = 2 ^ (n * (1 + 2 * k n)) := by rw [← pow_add]; congr 1; ring

lemma upsilon_nonneg (n : ℕ) (g : BinaryTreeAut) : 0 ≤ upsilon D ω k n g :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- `υ_n` is a probability on `Aut(T)`. -/
lemma hasSum_upsilon (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ} (hn : D ∣ n) :
    HasSum (upsilon D ω k n) 1 := by
  classical
  have := lambda_finite hω hk hn
  let _ : Fintype (LambdaN D ω k n) := Fintype.ofFinite _
  have hpos := card_lambda_pos hω hk hn
  have hcard : ∀ g, Nat.card {p : LambdaN D ω k n // theta D ω k n p = g} =
      (Finset.univ.filter fun p => theta D ω k n p = g).card := by
    intro g
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsupp : ∀ g ∉ Finset.univ.image (theta D ω k n), upsilon D ω k n g = 0 := by
    intro g hg
    unfold upsilon
    rw [hcard]
    have : (Finset.univ.filter fun p => theta D ω k n p = g) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p _ hp
      exact hg (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hp⟩)
    simp [this]
  have h : HasSum (upsilon D ω k n)
      (∑ g ∈ Finset.univ.image (theta D ω k n), upsilon D ω k n g) :=
    hasSum_sum_of_ne_finset_zero hsupp
  convert h using 1
  unfold upsilon
  rw [← Finset.sum_div]
  simp_rw [hcard]
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_image, Finset.card_univ,
    ← Nat.card_eq_fintype_card, div_self]
  exact_mod_cast hpos.ne'

lemma hasSum_upsilon_sub (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ} (hn : D ∣ n) :
    HasSum (fun g : grigorchuk ω => upsilon D ω k n g) 1 := by
  have hsub : Function.support (upsilon D ω k n) ⊆ (grigorchuk ω : Set BinaryTreeAut) :=
    fun g hg => (mem_grigorchuk_and_wordLength_le_of_upsilon_ne_zero D ω hω k hk n hn g hg).1
  exact (hasSum_subtype_iff_of_support_subset hsub).mpr (hasSum_upsilon hω hk hn)

lemma hasSum_upsilonCheck_sub (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ}
    (hn : D ∣ n) : HasSum (fun g : grigorchuk ω => upsilonCheck D ω k n g) 1 := by
  have h := hasSum_upsilon_sub hω hk hn
  rw [← (Equiv.inv (grigorchuk ω)).hasSum_iff] at h
  convert h using 1
  ext g
  simp [upsilonCheck]

/-! ### `μ_β` is a probability -/

lemma genSet_finite (ω : ℕ → Fin 3) : (genSet ω).Finite := by
  have : (gens ω).Finite := by
    unfold gens
    exact (((Set.finite_singleton _).insert _).insert _).insert _
  exact this.preimage Subtype.val_injective.injOn

lemma grigA_mem (ω : ℕ → Fin 3) : grigA ∈ grigorchuk ω :=
  Subgroup.subset_closure (by simp [gens])

lemma hasSum_uniform (ω : ℕ → Fin 3) : HasSum (uniformMeasure (genSet ω)) 1 := by
  classical
  set F := (genSet_finite ω).toFinset with hF
  have hsupp : ∀ g ∉ F, uniformMeasure (genSet ω) g = 0 := by
    intro g hg
    rw [hF, Set.Finite.mem_toFinset] at hg
    simp [uniformMeasure, hg]
  have h : HasSum (uniformMeasure (genSet ω)) (∑ g ∈ F, uniformMeasure (genSet ω) g) :=
    hasSum_sum_of_ne_finset_zero hsupp
  convert h using 1
  have hmem : ∀ g ∈ F, uniformMeasure (genSet ω) g = (Nat.card (genSet ω) : ℝ)⁻¹ := by
    intro g hg
    rw [hF, Set.Finite.mem_toFinset] at hg
    simp [uniformMeasure, hg]
  rw [Finset.sum_congr rfl hmem, Finset.sum_const, nsmul_eq_mul]
  have hcard : Nat.card (genSet ω) = F.card := by
    rw [hF, Nat.card_eq_card_finite_toFinset]
  have hne : F.Nonempty := ⟨⟨grigA, grigA_mem ω⟩, by rw [hF, Set.Finite.mem_toFinset]; simp [genSet, gens]⟩
  rw [hcard, mul_inv_cancel₀]
  exact_mod_cast hne.card_pos.ne'

/-- The weights `2^{−nβ}` on `n ⩾ 1`, `D ∣ n`. -/
noncomputable def wt (D : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  if 1 ≤ n ∧ D ∣ n then (2 : ℝ) ^ (-((n : ℝ) * β)) else 0

lemma wt_nonneg (D : ℕ) (β : ℝ) (n : ℕ) : 0 ≤ wt D β n := by
  unfold wt; split_ifs <;> positivity

lemma rpow_eq_pow (β : ℝ) (n : ℕ) : (2 : ℝ) ^ (-((n : ℝ) * β)) = ((2 : ℝ) ^ (-β)) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring

lemma summable_wt (D : ℕ) {β : ℝ} (hβ : 0 < β) : Summable (wt D β) := by
  have hr : (2 : ℝ) ^ (-β) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine Summable.of_nonneg_of_le (wt_nonneg D β) (fun n => ?_)
    (summable_geometric_of_lt_one (by positivity) hr)
  unfold wt; split_ifs
  · rw [rpow_eq_pow]
  · positivity

lemma tsum_wt_pos {D : ℕ} (hD : 1 ≤ D) {β : ℝ} (hβ : 0 < β) : 0 < ∑' n, wt D β n := by
  have h := (summable_wt D hβ).le_tsum D (fun j _ => wt_nonneg D β j)
  have : 0 < wt D β D := by
    unfold wt; rw [if_pos ⟨hD, dvd_refl D⟩]; positivity
  linarith

lemma normConst_eq (D : ℕ) (β : ℝ) : normConst D β = (2 * ∑' n, wt D β n)⁻¹ := rfl

/-- The pieces `a_n(g) = C_β 2^{−nβ} (υ_n(g) + υ̌_n(g))` of `μ_β`. -/
noncomputable def piece (D : ℕ) (ω : ℕ → Fin 3) (k : ℕ → ℕ) (β : ℝ) (n : ℕ) (g : grigorchuk ω) : ℝ :=
  if 1 ≤ n ∧ D ∣ n then
    normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) * (upsilon D ω k n g + upsilonCheck D ω k n g)
  else 0

lemma muBeta_eq (β : ℝ) (g : grigorchuk ω) :
    muBeta D ω k β g = 1 / 2 * uniformMeasure (genSet ω) g + 1 / 2 * ∑' n, piece D ω k β n g :=
  rfl

lemma piece_nonneg (β : ℝ) (n : ℕ) (g : grigorchuk ω) : 0 ≤ piece D ω k β n g := by
  have hC : 0 ≤ normConst D β := by
    unfold normConst
    refine inv_nonneg.mpr (mul_nonneg two_pos.le (tsum_nonneg fun n => ?_))
    split_ifs
    · positivity
    · exact le_rfl
  unfold piece; split_ifs
  · exact mul_nonneg (mul_nonneg hC (by positivity))
      (add_nonneg (upsilon_nonneg _ _) (upsilon_nonneg _ _))
  · exact le_rfl

lemma hasSum_piece (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) (β : ℝ) (n : ℕ) :
    HasSum (piece D ω k β n) (2 * normConst D β * wt D β n) := by
  unfold piece wt
  split_ifs with hc
  · have := ((hasSum_upsilon_sub hω hk hc.2).add (hasSum_upsilonCheck_sub hω hk hc.2)).mul_left
      (normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)))
    have e : 2 * normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) =
        normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) * (1 + 1) := by ring
    rw [e]
    exact this
  · simp only [mul_zero]; exact hasSum_zero

lemma hasSum_tsum_piece (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {β : ℝ} (hβ : 0 < β)
    (hD : 1 ≤ D) : HasSum (fun g : grigorchuk ω => ∑' n, piece D ω k β n g) 1 := by
  set F : ℕ × grigorchuk ω → ℝ := fun p => piece D ω k β p.1 p.2 with hF
  have hF0 : 0 ≤ F := fun p => piece_nonneg β p.1 p.2
  have hrow : ∀ n, HasSum (fun g => F (n, g)) (2 * normConst D β * wt D β n) :=
    fun n => hasSum_piece hω hk β n
  have hFs : Summable F := (summable_prod_of_nonneg hF0).mpr
    ⟨fun n => (hrow n).summable, by
      simp_rw [fun n => (hrow n).tsum_eq]
      exact (summable_wt D hβ).mul_left _⟩
  have htot : HasSum (fun n => 2 * normConst D β * wt D β n) (∑' p, F p) :=
    hFs.hasSum.prod_fiberwise hrow
  have hval : ∑' p, F p = 1 := by
    rw [← htot.tsum_eq, tsum_mul_left, normConst_eq]
    have := tsum_wt_pos hD hβ (D := D)
    field_simp
  have hFs' : Summable fun p : grigorchuk ω × ℕ => F p.swap := hFs.prod_symm
  have hcol : ∀ g : grigorchuk ω, HasSum (fun n => F (n, g)) (∑' n, piece D ω k β n g) :=
    fun g => (hFs'.prod_factor g).hasSum
  have := hFs'.hasSum.prod_fiberwise hcol
  rw [← hval, ← (Equiv.prodComm (grigorchuk ω) ℕ).tsum_eq F]
  exact this

lemma isProbability_muBeta (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {β : ℝ}
    (hβ : 0 < β) (hD : 1 ≤ D) : IsProbability (muBeta D ω k β) := by
  refine ⟨fun g => ?_, ?_⟩
  · rw [muBeta_eq]
    have h1 : 0 ≤ uniformMeasure (genSet ω) g := by
      unfold uniformMeasure; split_ifs <;> positivity
    have h2 : 0 ≤ ∑' n, piece D ω k β n g := tsum_nonneg fun n => piece_nonneg β n g
    positivity
  · have := ((hasSum_uniform ω).mul_left (1 / 2)).add
      ((hasSum_tsum_piece hω hk hβ hD).mul_left (1 / 2))
    have h1 : (1 : ℝ) = 1 / 2 * 1 + 1 / 2 * 1 := by norm_num
    rw [h1]
    exact this

/-! ### Finite entropy -/

lemma ofReal_negMulLog_tsum_le {ι : Type*} {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hs : Summable p)
    (h1 : ∑' i, p i ≤ 1) :
    ENNReal.ofReal (Real.negMulLog (∑' i, p i)) ≤ ∑' i, ENNReal.ofReal (Real.negMulLog (p i)) := by
  set q := ∑' i, p i with hq
  have hq0 : 0 ≤ q := tsum_nonneg hp
  have hlog : 0 ≤ -Real.log q := by have := Real.log_nonpos hq0 h1; linarith
  have key : Real.negMulLog q = ∑' i, p i * (-Real.log q) := by
    rw [tsum_mul_right, Real.negMulLog, ← hq]; ring
  rw [key, ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hp i) hlog) (hs.mul_right _)]
  refine ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal ?_
  rcases (hp i).lt_or_eq with hpi | hpi
  · have hpq : p i ≤ q := hs.le_tsum i (fun j _ => hp j)
    have : Real.log (p i) ≤ Real.log q := Real.log_le_log hpi hpq
    rw [Real.negMulLog]; nlinarith
  · rw [← hpi]; simp

lemma negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x + y) ≤ Real.negMulLog x + Real.negMulLog y := by
  unfold Real.negMulLog
  rcases hx.lt_or_eq with hx' | hx'
  · rcases hy.lt_or_eq with hy' | hy'
    · have h1 : Real.log x ≤ Real.log (x + y) := Real.log_le_log hx' (by linarith)
      have h2 : Real.log y ≤ Real.log (x + y) := Real.log_le_log hy' (by linarith)
      nlinarith
    · rw [← hy']; simp
  · rw [← hx']; simp

/-- `Σ_g −cυ(g) log(cυ(g)) ⩽ −c log c + c log L` when `υ ⩾ 1/L` on its support. -/
lemma tsum_negMulLog_le {G : Type*} {υ : G → ℝ} (h0 : ∀ g, 0 ≤ υ g) (h1 : HasSum υ 1) {L : ℝ}
    (hL : 1 ≤ L) (hmin : ∀ g, υ g ≠ 0 → 1 / L ≤ υ g) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∑' g, ENNReal.ofReal (Real.negMulLog (c * υ g)) ≤
      ENNReal.ofReal (Real.negMulLog c + c * Real.log L) := by
  set K := Real.negMulLog c + c * Real.log L with hK
  have hK0 : 0 ≤ K := add_nonneg (Real.negMulLog_nonneg hc0 hc1)
    (mul_nonneg hc0 (Real.log_nonneg hL))
  have hpt : ∀ g, Real.negMulLog (c * υ g) ≤ υ g * K := by
    intro g
    rw [Real.negMulLog_mul]
    have hυ : Real.negMulLog (υ g) ≤ υ g * Real.log L := by
      rcases (h0 g).lt_or_eq with hg | hg
      · have hm := hmin g hg.ne'
        have hLpos : 0 < L := by linarith
        have : -Real.log (υ g) ≤ Real.log L := by
          have h2 : Real.log (1 / L) ≤ Real.log (υ g) := Real.log_le_log (by positivity) hm
          rw [one_div, Real.log_inv] at h2
          linarith
        rw [Real.negMulLog]
        nlinarith [h0 g]
      · rw [← hg]; simp
    have := mul_le_mul_of_nonneg_left hυ hc0
    rw [hK]; nlinarith [h0 g]
  calc ∑' g, ENNReal.ofReal (Real.negMulLog (c * υ g)) ≤ ∑' g, ENNReal.ofReal (υ g * K) :=
        ENNReal.tsum_le_tsum fun g => ENNReal.ofReal_le_ofReal (hpt g)
    _ = ENNReal.ofReal (∑' g, υ g * K) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun g => mul_nonneg (h0 g) hK0) (h1.summable.mul_right K)).symm
    _ = ENNReal.ofReal K := by rw [tsum_mul_right, h1.tsum_eq, one_mul]

lemma upsilon_ge (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ} (hn : D ∣ n)
    (g : BinaryTreeAut) (hg : upsilon D ω k n g ≠ 0) :
    1 / (Nat.card (LambdaN D ω k n) : ℝ) ≤ upsilon D ω k n g := by
  unfold upsilon at hg ⊢
  have hpos : (0 : ℝ) < Nat.card (LambdaN D ω k n) := by exact_mod_cast card_lambda_pos hω hk hn
  apply div_le_div_of_nonneg_right _ hpos.le
  have : Nat.card {p : LambdaN D ω k n // theta D ω k n p = g} ≠ 0 := by
    intro h; apply hg; rw [h]; simp
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

lemma le_one_of_isProb {G : Type*} {μ : G → ℝ} (hμ : IsProbability μ) (g : G) : μ g ≤ 1 :=
  le_hasSum hμ.2 g (fun j _ => hμ.1 j)

lemma normConst_pos {D : ℕ} (hD : 1 ≤ D) {β : ℝ} (hβ : 0 < β) : 0 < normConst D β := by
  rw [normConst_eq]; have := tsum_wt_pos hD hβ (D := D); positivity

lemma normConst_mul_le {D : ℕ} (hD : 1 ≤ D) {β : ℝ} (hβ : 0 < β) {n : ℕ} (hn : 1 ≤ n ∧ D ∣ n) :
    normConst D β * (2 : ℝ) ^ (-((n : ℝ) * β)) ≤ 1 / 2 := by
  have hS := tsum_wt_pos hD hβ (D := D)
  have hle : wt D β n ≤ ∑' m, wt D β m := (summable_wt D hβ).le_tsum n (fun j _ => wt_nonneg D β j)
  have hw : wt D β n = (2 : ℝ) ^ (-((n : ℝ) * β)) := by unfold wt; rw [if_pos hn]
  rw [normConst_eq, ← hw]
  rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
  linarith

lemma upsilon_le_one (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {n : ℕ} (hn : D ∣ n)
    (g : BinaryTreeAut) : upsilon D ω k n g ≤ 1 :=
  le_hasSum (hasSum_upsilon hω hk hn) g (fun j _ => upsilon_nonneg n j)

lemma hasFiniteEntropy_muBeta (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {β : ℝ}
    (hβ : 0 < β) (hD : 1 ≤ D) (hkn : ∀ᶠ n in atTop, k n ≤ n) :
    HasFiniteEntropy (muBeta D ω k β) := by
  have hprob := isProbability_muBeta hω hk hβ hD
  set C := normConst D β with hCdef
  have hC : 0 < C := normConst_pos hD hβ
  set c : ℕ → ℝ := fun n => if 1 ≤ n ∧ D ∣ n then C * (2 : ℝ) ^ (-((n : ℝ) * β)) else 0
    with hcdef
  have hc0 : ∀ n, 0 ≤ c n := fun n => by simp only [hcdef]; split_ifs <;> positivity
  have hc1 : ∀ n, c n ≤ 1 / 2 := fun n => by
    simp only [hcdef]; split_ifs with h
    · exact normConst_mul_le hD hβ h
    · norm_num
  have hpiece : ∀ n (g : grigorchuk ω), 1 / 2 * piece D ω k β n g =
      1 / 2 * c n * upsilon D ω k n g + 1 / 2 * c n * upsilonCheck D ω k n g := by
    intro n g; simp only [piece, hcdef]; split_ifs <;> ring
  have hpiece_le : ∀ n (g : grigorchuk ω), piece D ω k β n g ≤ 2 * C * wt D β n := by
    intro n g
    simp only [piece, wt]
    split_ifs with h
    · have h1 := upsilon_le_one hω hk h.2 (g : BinaryTreeAut)
      have h2 := upsilon_le_one hω hk h.2 ((g : BinaryTreeAut)⁻¹)
      have : upsilonCheck D ω k n g ≤ 1 := h2
      have hp : 0 ≤ C * (2 : ℝ) ^ (-((n : ℝ) * β)) := by positivity
      nlinarith
    · simp
  -- the pointwise bound
  have hpt : ∀ g : grigorchuk ω, ENNReal.ofReal (Real.negMulLog (muBeta D ω k β g)) ≤
      ENNReal.ofReal (Real.negMulLog (1 / 2 * uniformMeasure (genSet ω) g)) +
      ∑' n, (ENNReal.ofReal (Real.negMulLog (1 / 2 * c n * upsilon D ω k n g)) +
        ENNReal.ofReal (Real.negMulLog (1 / 2 * c n * upsilonCheck D ω k n g))) := by
    intro g
    have hu0 : 0 ≤ 1 / 2 * uniformMeasure (genSet ω) g := by
      unfold uniformMeasure; split_ifs <;> positivity
    have hpn : ∀ n, 0 ≤ 1 / 2 * piece D ω k β n g := fun n => by
      have := piece_nonneg (D := D) (k := k) β n g; positivity
    have hps : Summable fun n => 1 / 2 * piece D ω k β n g :=
      Summable.of_nonneg_of_le hpn (fun n => by
        have := hpiece_le n g; linarith [piece_nonneg (D := D) (k := k) β n g])
        (((summable_wt D hβ).mul_left (2 * C)).mul_left (1 / 2))
    have hT0 : 0 ≤ 1 / 2 * ∑' n, piece D ω k β n g := by
      rw [← tsum_mul_left]; exact tsum_nonneg hpn
    have htot : 1 / 2 * uniformMeasure (genSet ω) g + 1 / 2 * ∑' n, piece D ω k β n g ≤ 1 := by
      rw [← muBeta_eq]; exact le_one_of_isProb hprob g
    have hy1 : ∑' n, 1 / 2 * piece D ω k β n g ≤ 1 := by
      rw [tsum_mul_left]; linarith
    calc ENNReal.ofReal (Real.negMulLog (muBeta D ω k β g))
        = ENNReal.ofReal (Real.negMulLog (1 / 2 * uniformMeasure (genSet ω) g +
            1 / 2 * ∑' n, piece D ω k β n g)) := by rw [muBeta_eq]
      _ ≤ ENNReal.ofReal (Real.negMulLog (1 / 2 * uniformMeasure (genSet ω) g) +
            Real.negMulLog (1 / 2 * ∑' n, piece D ω k β n g)) :=
          ENNReal.ofReal_le_ofReal (negMulLog_add_le hu0 hT0)
      _ ≤ ENNReal.ofReal (Real.negMulLog (1 / 2 * uniformMeasure (genSet ω) g)) +
            ENNReal.ofReal (Real.negMulLog (1 / 2 * ∑' n, piece D ω k β n g)) :=
          ENNReal.ofReal_add_le
      _ ≤ ENNReal.ofReal (Real.negMulLog (1 / 2 * uniformMeasure (genSet ω) g)) +
            ∑' n, ENNReal.ofReal (Real.negMulLog (1 / 2 * piece D ω k β n g)) := by
          gcongr
          rw [← tsum_mul_left]
          exact ofReal_negMulLog_tsum_le hpn hps hy1
      _ ≤ _ := by
          gcongr with n
          rw [hpiece]
          refine (ENNReal.ofReal_le_ofReal (negMulLog_add_le ?_ ?_)).trans ENNReal.ofReal_add_le
          · exact mul_nonneg (mul_nonneg (by norm_num) (hc0 n)) (upsilon_nonneg n _)
          · exact mul_nonneg (mul_nonneg (by norm_num) (hc0 n)) (upsilon_nonneg n _)
  -- each block
  set e : ℕ → ℝ := fun n => if 1 ≤ n ∧ D ∣ n then
    Real.negMulLog (1 / 2 * c n) + 1 / 2 * c n * Real.log (Nat.card (LambdaN D ω k n)) else 0
    with hedef
  have hblock : ∀ n, ∑' g : grigorchuk ω, ENNReal.ofReal (Real.negMulLog
      (1 / 2 * c n * upsilon D ω k n g)) ≤ ENNReal.ofReal (e n) ∧
      ∑' g : grigorchuk ω, ENNReal.ofReal (Real.negMulLog
      (1 / 2 * c n * upsilonCheck D ω k n g)) ≤ ENNReal.ofReal (e n) := by
    intro n
    by_cases h : 1 ≤ n ∧ D ∣ n
    · have hL : (1 : ℝ) ≤ Nat.card (LambdaN D ω k n) := by
        exact_mod_cast card_lambda_pos hω hk h.2
      have hce : e n = Real.negMulLog (1 / 2 * c n) +
          1 / 2 * c n * Real.log (Nat.card (LambdaN D ω k n)) := by
        simp only [hedef]; rw [if_pos h]
      rw [hce]
      have hcc0 : 0 ≤ 1 / 2 * c n := by have := hc0 n; positivity
      have hcc1 : 1 / 2 * c n ≤ 1 := by have := hc1 n; linarith
      constructor
      · exact tsum_negMulLog_le (fun g => upsilon_nonneg n _) (hasSum_upsilon_sub hω hk h.2) hL
          (fun g hg => upsilon_ge hω hk h.2 _ hg) hcc0 hcc1
      · exact tsum_negMulLog_le (fun g => upsilon_nonneg n _) (hasSum_upsilonCheck_sub hω hk h.2) hL
          (fun g hg => upsilon_ge hω hk h.2 _ hg) hcc0 hcc1
    · have hcn : c n = 0 := by simp only [hcdef]; rw [if_neg h]
      simp [hcn]
  -- the uniform part
  have hL0 : (1 : ℝ) ≤ Nat.card (genSet ω) := by
    have : 0 < Nat.card (genSet ω) := by
      have := (genSet_finite ω).to_subtype
      exact Nat.card_pos_iff.mpr ⟨⟨⟨⟨grigA, grigA_mem ω⟩, by simp [genSet, gens]⟩⟩, this⟩
    exact_mod_cast this
  have huni : ∑' g : grigorchuk ω, ENNReal.ofReal (Real.negMulLog
      (1 / 2 * uniformMeasure (genSet ω) g)) ≤
      ENNReal.ofReal (Real.negMulLog (1 / 2) + 1 / 2 * Real.log (Nat.card (genSet ω))) := by
    refine tsum_negMulLog_le (fun g => by unfold uniformMeasure; split_ifs <;> positivity)
      (hasSum_uniform ω) hL0 (fun g hg => ?_) (by norm_num) (by norm_num)
    unfold uniformMeasure at hg ⊢
    split_ifs at hg ⊢ with hm
    · rw [one_div]
    · exact absurd rfl hg
  -- summability of the blocks
  have he0 : ∀ n, 0 ≤ e n := fun n => by
    simp only [hedef]; split_ifs
    · have h1 : 0 ≤ Real.negMulLog (1 / 2 * c n) :=
        Real.negMulLog_nonneg (by have := hc0 n; positivity) (by have := hc1 n; linarith)
      have h2 : 0 ≤ Real.log (Nat.card (LambdaN D ω k n)) := Real.log_nonneg (by
        exact_mod_cast card_lambda_pos hω hk ‹1 ≤ n ∧ D ∣ n›.2)
      have := hc0 n
      positivity
    · exact le_rfl
  have hes : Summable e := by
    set r : ℝ := (2 : ℝ) ^ (-β) with hr
    have hr0 : 0 < r := by positivity
    have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hrn : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
    set a := C / 2 with ha
    set B := |Real.log a| + β * Real.log 2 + Real.log 2 + 2 * Real.log 2 with hB
    have hg : Summable fun n : ℕ => a * (B * ((n : ℝ) ^ 0 * r ^ n) + B * ((n : ℝ) ^ 1 * r ^ n) +
        B * ((n : ℝ) ^ 2 * r ^ n)) :=
      ((((summable_pow_mul_geometric_of_norm_lt_one 0 hrn).mul_left B).add
        ((summable_pow_mul_geometric_of_norm_lt_one 1 hrn).mul_left B)).add
        ((summable_pow_mul_geometric_of_norm_lt_one 2 hrn).mul_left B)).mul_left a
    refine Summable.of_norm_bounded_eventually hg ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hkn] with n hkn'
    rw [Real.norm_eq_abs, abs_of_nonneg (he0 n)]
    simp only [hedef]
    split_ifs with h
    · have hcn : c n = C * r ^ n := by
        simp only [hcdef]; rw [if_pos h, rpow_eq_pow]
      rw [hcn]
      have hlogB : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      -- `−log (a rⁿ) = −log a + nβ log 2`
      have hpos : 0 < 1 / 2 * (C * r ^ n) := by positivity
      have hlog : -Real.log (1 / 2 * (C * r ^ n)) ≤ |Real.log a| + n * (β * Real.log 2) := by
        have e1 : 1 / 2 * (C * r ^ n) = a * r ^ n := by rw [ha]; ring
        rw [e1, Real.log_mul (by positivity) (by positivity), Real.log_pow, hr,
          Real.log_rpow (by norm_num)]
        have := neg_abs_le (Real.log a)
        nlinarith
      -- `log |Λ_n| ⩽ n(1 + 2n) log 2`
      have hΛ : Real.log (Nat.card (LambdaN D ω k n)) ≤ (n : ℝ) * (1 + 2 * n) * Real.log 2 := by
        have h1 := card_lambda_le hω hk h.2
        have h2 : (Nat.card (LambdaN D ω k n) : ℝ) ≤ 2 ^ (n * (1 + 2 * n)) := by
          have : n * (1 + 2 * k n) ≤ n * (1 + 2 * n) := Nat.mul_le_mul_left _ (by omega)
          exact_mod_cast h1.trans (Nat.pow_le_pow_right (by norm_num) this)
        have hpos' : (0 : ℝ) < Nat.card (LambdaN D ω k n) := by
          exact_mod_cast card_lambda_pos hω hk h.2
        calc Real.log (Nat.card (LambdaN D ω k n)) ≤ Real.log (2 ^ (n * (1 + 2 * n))) :=
              Real.log_le_log hpos' h2
          _ = (n : ℝ) * (1 + 2 * n) * Real.log 2 := by
              rw [Real.log_pow]; push_cast; ring
      have hx : 0 ≤ 1 / 2 * (C * r ^ n) := hpos.le
      have hrn0 : 0 ≤ r ^ n := by positivity
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [Real.negMulLog]
      have hbound : -(1 / 2 * (C * r ^ n)) * Real.log (1 / 2 * (C * r ^ n)) +
          1 / 2 * (C * r ^ n) * Real.log (Nat.card (LambdaN D ω k n)) ≤
          1 / 2 * (C * r ^ n) * (|Real.log a| + n * (β * Real.log 2) +
            (n : ℝ) * (1 + 2 * n) * Real.log 2) := by
        have := mul_le_mul_of_nonneg_left hlog hx
        have := mul_le_mul_of_nonneg_left hΛ hx
        nlinarith
      refine hbound.trans ?_
      have hl2 : 0 ≤ Real.log 2 := hlogB
      have hB1 : |Real.log a| ≤ B := by rw [hB]; nlinarith [mul_nonneg hβ.le hl2]
      have hB2 : β * Real.log 2 + Real.log 2 ≤ B := by rw [hB]; nlinarith [abs_nonneg (Real.log a)]
      have hB3 : 2 * Real.log 2 ≤ B := by rw [hB]; nlinarith [abs_nonneg (Real.log a), mul_nonneg hβ.le hl2]
      have key : |Real.log a| + n * (β * Real.log 2) + (n : ℝ) * (1 + 2 * n) * Real.log 2 ≤
          B * 1 + B * n + B * n ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_left hB2 hn0
        have h2 := mul_le_mul_of_nonneg_left hB3 (sq_nonneg (n : ℝ))
        nlinarith
      have ha0 : 0 ≤ a * r ^ n := by rw [ha]; positivity
      calc 1 / 2 * (C * r ^ n) * (|Real.log a| + n * (β * Real.log 2) +
            (n : ℝ) * (1 + 2 * n) * Real.log 2)
          = a * r ^ n * (|Real.log a| + n * (β * Real.log 2) +
            (n : ℝ) * (1 + 2 * n) * Real.log 2) := by rw [ha]; ring
        _ ≤ a * r ^ n * (B * 1 + B * n + B * n ^ 2) := mul_le_mul_of_nonneg_left key ha0
        _ = a * (B * ((n : ℝ) ^ 0 * r ^ n) + B * ((n : ℝ) ^ 1 * r ^ n) +
            B * ((n : ℝ) ^ 2 * r ^ n)) := by ring
    · positivity
  -- assemble
  have hfin : ∑' g : grigorchuk ω, ENNReal.ofReal (Real.negMulLog (muBeta D ω k β g)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hpt)
    rw [ENNReal.tsum_add, ENNReal.tsum_comm]
    refine ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top huni, ?_⟩
    have hle : ∑' n, ∑' g : grigorchuk ω,
        (ENNReal.ofReal (Real.negMulLog (1 / 2 * c n * upsilon D ω k n g)) +
          ENNReal.ofReal (Real.negMulLog (1 / 2 * c n * upsilonCheck D ω k n g))) ≤
        ∑' n, (ENNReal.ofReal (e n) + ENNReal.ofReal (e n)) :=
      ENNReal.tsum_le_tsum fun n => by
        rw [ENNReal.tsum_add]; exact add_le_add (hblock n).1 (hblock n).2
    refine ne_top_of_le_ne_top ?_ hle
    rw [ENNReal.tsum_add, ← ENNReal.ofReal_tsum_of_nonneg he0 hes]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hs := ENNReal.summable_toReal hfin
  refine hs.congr fun g => ?_
  exact ENNReal.toReal_ofReal (Real.negMulLog_nonneg (hprob.1 g) (le_one_of_isProb hprob g))

/-! ### The tail -/

lemma inv_mem_wordBall {G : Type*} [Group G] {S : Set G} {g : G} {n : ℕ}
    (h : g ∈ Chou.wordBall S n) : g⁻¹ ∈ Chou.wordBall S n := by
  obtain ⟨l, hlen, hl, rfl⟩ := h
  refine ⟨(l.map fun x => x⁻¹).reverse, by simpa using hlen, fun y hy => ?_, (List.prod_inv_reverse l).symm⟩
  rw [List.mem_reverse, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rcases hl x hx with h | h
  · right; simpa using h
  · left; exact h

lemma lift_wordBall {x : grigorchuk ω} {n : ℕ}
    (h : (x : BinaryTreeAut) ∈ Chou.wordBall (gens ω) n) : x ∈ Chou.wordBall (genSet ω) n := by
  obtain ⟨l, hlen, hl, hprod⟩ := h
  have hmem : ∀ y ∈ l, y ∈ grigorchuk ω := fun y hy => by
    rcases hl y hy with h | h
    · exact Subgroup.subset_closure h
    · have := Subgroup.inv_mem (grigorchuk ω) (Subgroup.subset_closure h : y⁻¹ ∈ grigorchuk ω)
      rwa [inv_inv] at this
  refine ⟨l.pmap (fun y hy => (⟨y, hy⟩ : grigorchuk ω)) hmem, by simpa using hlen, fun z hz => ?_, ?_⟩
  · rw [List.mem_pmap] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rcases hl y hy with h | h
    · left; exact h
    · right; simpa [genSet] using h
  · apply Subtype.ext
    rw [SubmonoidClass.coe_list_prod, ← hprod]
    congr 1
    clear hprod hlen hl
    induction l with
    | nil => rfl
    | cons a t ih => simp [List.pmap, ih]

lemma mem_ball_of_upsilon_ne (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {m : ℕ}
    (hm : D ∣ m) {x : grigorchuk ω} (hx : upsilon D ω k m (x : BinaryTreeAut) ≠ 0) :
    (wordLength (genSet ω) x : ℝ) ≤ 2 ^ (2 * k m + 2 * D + 4) * lengthL ω m := by
  obtain ⟨hG, hlen⟩ := mem_grigorchuk_and_wordLength_le_of_upsilon_ne_zero D ω hω k hk m hm _ hx
  obtain ⟨N, hN⟩ := WordBallDev.exists_mem_wordBall (gens ω) _ hG
  have hmemN : (x : BinaryTreeAut) ∈ Chou.wordBall (gens ω) (wordLength (gens ω) x) :=
    Nat.sInf_mem (s := {n | (x : BinaryTreeAut) ∈ Chou.wordBall (gens ω) n}) ⟨N, hN⟩
  have h1 : wordLength (genSet ω) x ≤ wordLength (gens ω) x := Nat.sInf_le (lift_wordBall hmemN)
  exact_mod_cast h1.trans hlen

lemma mem_ball_of_upsilonCheck_ne (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {m : ℕ}
    (hm : D ∣ m) {x : grigorchuk ω} (hx : upsilonCheck D ω k m (x : BinaryTreeAut) ≠ 0) :
    (wordLength (genSet ω) x : ℝ) ≤ 2 ^ (2 * k m + 2 * D + 4) * lengthL ω m := by
  have hx' : upsilon D ω k m ((x⁻¹ : grigorchuk ω) : BinaryTreeAut) ≠ 0 := by
    rw [Subgroup.coe_inv]; exact hx
  obtain ⟨hG, hlen⟩ := mem_grigorchuk_and_wordLength_le_of_upsilon_ne_zero D ω hω k hk m hm _ hx'
  obtain ⟨N, hN⟩ := WordBallDev.exists_mem_wordBall (gens ω) _ hG
  have hmemN : ((x⁻¹ : grigorchuk ω) : BinaryTreeAut) ∈
      Chou.wordBall (gens ω) (wordLength (gens ω) ((x⁻¹ : grigorchuk ω) : BinaryTreeAut)) :=
    Nat.sInf_mem (s := {n | ((x⁻¹ : grigorchuk ω) : BinaryTreeAut) ∈ Chou.wordBall (gens ω) n})
      ⟨N, hN⟩
  have h2 := inv_mem_wordBall (lift_wordBall hmemN)
  rw [inv_inv] at h2
  have h1 : wordLength (genSet ω) x ≤ wordLength (gens ω) ((x⁻¹ : grigorchuk ω) : BinaryTreeAut) :=
    Nat.sInf_le h2
  exact_mod_cast h1.trans hlen

lemma pow_mul_lengthL_le (ω : ℕ → Fin 3) (a b : ℕ) : 2 ^ b * lengthL ω a ≤ lengthL ω (a + b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have := two_mul_lengthL_le_lengthL_succ ω (a + b)
    rw [pow_succ, ← add_assoc]
    nlinarith

lemma tail (hω : SatisfiesFr D ω) (hk : IsAdmissibleSeq D k) {β : ℝ} (hβ : 0 < β)
    (hD : 1 ≤ D) (n : ℕ) :
    mass (muBeta D ω k β) (ball (genSet ω) ((2 : ℝ) ^ (2 * k n) * lengthL ω n))ᶜ ≤
      normConst D β * (((2 : ℝ) ^ (-β))⁻¹) ^ (2 * D + 3) / (1 - (2 : ℝ) ^ (-β)) *
        ((2 : ℝ) ^ (-β)) ^ n := by
  set R : ℝ := (2 : ℝ) ^ (2 * k n) * lengthL ω n with hR
  set r : ℝ := (2 : ℝ) ^ (-β) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set C := normConst D β with hCdef
  have hC : 0 < C := normConst_pos hD hβ
  set M := 2 * D + 3 with hM
  -- pieces with `m + M < n` vanish off the ball
  have hpz : ∀ m (x : grigorchuk ω), x ∉ ball (genSet ω) R → m + M < n →
      piece D ω k β m x = 0 := by
    intro m x hx hmn
    unfold piece
    split_ifs with hc
    · have hrad : (2 : ℝ) ^ (2 * k m + 2 * D + 4) * lengthL ω m ≤ R := by
        have hkm : k m ≤ k n := hk.1 (by omega)
        have h1 := pow_mul_lengthL_le ω m (n - m)
        rw [show m + (n - m) = n by omega] at h1
        have h1R : (2 : ℝ) ^ (n - m) * lengthL ω m ≤ lengthL ω n := by exact_mod_cast h1
        have h2 : (2 : ℝ) ^ (2 * k m + 2 * D + 4) ≤ 2 ^ (2 * k n) * 2 ^ (n - m) := by
          rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
        have hL : (0 : ℝ) ≤ lengthL ω m := Nat.cast_nonneg _
        calc (2 : ℝ) ^ (2 * k m + 2 * D + 4) * lengthL ω m
            ≤ 2 ^ (2 * k n) * 2 ^ (n - m) * lengthL ω m := by gcongr
          _ = 2 ^ (2 * k n) * (2 ^ (n - m) * lengthL ω m) := by ring
          _ ≤ 2 ^ (2 * k n) * lengthL ω n := by gcongr
      have hυ : upsilon D ω k m (x : BinaryTreeAut) = 0 := by
        by_contra hne
        exact hx ((mem_ball_of_upsilon_ne hω hk hc.2 hne).trans hrad)
      have hυ' : upsilonCheck D ω k m (x : BinaryTreeAut) = 0 := by
        by_contra hne
        exact hx ((mem_ball_of_upsilonCheck_ne hω hk hc.2 hne).trans hrad)
      rw [hυ, hυ']; ring
    · rfl
  -- the uniform part vanishes off the ball
  have hu : ∀ x : grigorchuk ω, x ∉ ball (genSet ω) R → uniformMeasure (genSet ω) x = 0 := by
    intro x hx
    have hxS : x ∉ genSet ω := by
      intro hS
      apply hx
      have h1 : x ∈ Chou.wordBall (genSet ω) 1 := ⟨[x], by simp, by simp [hS], by simp⟩
      have h2 : wordLength (genSet ω) x ≤ 1 := Nat.sInf_le h1
      have hR1 : (1 : ℝ) ≤ R := by
        have h3 : (3 : ℝ) ≤ lengthL ω n := by
          have := pow_mul_lengthL_le ω 0 n
          have h0 : lengthL ω 0 = 3 := by simp [lengthL, dotProduct]
          rw [h0, zero_add] at this
          have : 3 ≤ lengthL ω n := by have := Nat.one_le_two_pow (n := n); nlinarith
          exact_mod_cast this
        have h4 : (1 : ℝ) ≤ 2 ^ (2 * k n) := one_le_pow₀ (by norm_num)
        nlinarith
      show (wordLength (genSet ω) x : ℝ) ≤ R
      have : (wordLength (genSet ω) x : ℝ) ≤ 1 := by exact_mod_cast h2
      linarith
    simp [uniformMeasure, hxS]
  -- the truncated pieces
  set P : ℕ → grigorchuk ω → ℝ := fun m x => if n ≤ m + M then piece D ω k β m x else 0 with hP
  have hP0 : ∀ m x, 0 ≤ P m x := fun m x => by
    simp only [hP]; split_ifs
    · exact piece_nonneg β m x
    · exact le_rfl
  have hrow : ∀ m, HasSum (P m) (if n ≤ m + M then 2 * C * wt D β m else 0) := by
    intro m
    simp only [hP]
    split_ifs
    · exact hasSum_piece hω hk β m
    · exact hasSum_zero
  have hrowsum : Summable fun m => if n ≤ m + M then 2 * C * wt D β m else 0 :=
    Summable.of_nonneg_of_le (fun m => by
        split_ifs
        · have := wt_nonneg D β m; positivity
        · exact le_rfl)
      (fun m => by
        split_ifs
        · exact le_rfl
        · have := wt_nonneg D β m; positivity)
      ((summable_wt D hβ).mul_left (2 * C))
  set F : ℕ × grigorchuk ω → ℝ := fun q => P q.1 q.2 with hF
  have hFs : Summable F := (summable_prod_of_nonneg fun q => hP0 q.1 q.2).mpr
    ⟨fun m => (hrow m).summable, by simp_rw [fun m => (hrow m).tsum_eq]; exact hrowsum⟩
  have htot : HasSum (fun m => if n ≤ m + M then 2 * C * wt D β m else 0) (∑' q, F q) :=
    hFs.hasSum.prod_fiberwise hrow
  have hFs' : Summable fun q : grigorchuk ω × ℕ => F q.swap := hFs.prod_symm
  have hcol : ∀ x : grigorchuk ω, HasSum (fun m => F (m, x)) (∑' m, P m x) :=
    fun x => (hFs'.prod_factor x).hasSum
  have hT : HasSum (fun x => ∑' m, P m x) (∑' q, F q) := by
    have := hFs'.hasSum.prod_fiberwise hcol
    rw [← (Equiv.prodComm (grigorchuk ω) ℕ).tsum_eq F]
    exact this
  -- pointwise domination of the indicator
  have hpt : ∀ x, (ball (genSet ω) R)ᶜ.indicator (muBeta D ω k β) x ≤ 1 / 2 * ∑' m, P m x := by
    intro x
    by_cases hx : x ∈ (ball (genSet ω) R)ᶜ
    · rw [Set.indicator_of_mem hx, muBeta_eq, hu x hx, mul_zero, zero_add]
      apply le_of_eq
      congr 1
      refine tsum_congr fun m => ?_
      simp only [hP]
      split_ifs with h
      · rfl
      · exact hpz m x hx (by omega)
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonneg (by norm_num) (tsum_nonneg fun m => hP0 m x)
  have hmass : mass (muBeta D ω k β) (ball (genSet ω) R)ᶜ ≤
      1 / 2 * ∑' m, (if n ≤ m + M then 2 * C * wt D β m else 0) := by
    unfold mass
    have hind : Summable ((ball (genSet ω) R)ᶜ.indicator (muBeta D ω k β)) :=
      (isProbability_muBeta hω hk hβ hD).2.summable.indicator _
    calc ∑' x, (ball (genSet ω) R)ᶜ.indicator (muBeta D ω k β) x
        ≤ ∑' x, 1 / 2 * ∑' m, P m x := hind.tsum_le_tsum hpt (hT.summable.mul_left _)
      _ = 1 / 2 * ∑' q, F q := by rw [tsum_mul_left, hT.tsum_eq]
      _ = 1 / 2 * ∑' m, (if n ≤ m + M then 2 * C * wt D β m else 0) := by rw [htot.tsum_eq]
  -- the geometric tail
  set s := n - M with hs
  have hgeo : ∑' m, (if n ≤ m + M then 2 * C * wt D β m else 0) ≤ 2 * C * (r ^ s / (1 - r)) := by
    have hle : ∀ m, (if n ≤ m + M then 2 * C * wt D β m else 0) ≤
        2 * C * (if s ≤ m then r ^ m else 0) := by
      intro m
      split_ifs with h1 h2 h2
      · unfold wt; split_ifs
        · rw [rpow_eq_pow]
        · simp only [mul_zero]; positivity
      · omega
      · positivity
      · simp
    have hgs : Summable fun m : ℕ => (if s ≤ m then r ^ m else 0) :=
      Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity)
        (fun m => by split_ifs; exact le_rfl; positivity) (summable_geometric_of_lt_one hr0.le hr1)
    have hval : ∑' m : ℕ, (if s ≤ m then r ^ m else 0) = r ^ s / (1 - r) := by
      rw [← hgs.sum_add_tsum_nat_add s]
      have h1 : ∑ i ∈ Finset.range s, (if s ≤ i then r ^ i else 0) = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [Finset.mem_range] at hi; rw [if_neg (by omega)]
      have h2 : ∀ i : ℕ, (if s ≤ i + s then r ^ (i + s) else 0) = r ^ s * r ^ i := fun i => by
        rw [if_pos (by omega), pow_add]; ring
      simp_rw [h1, h2, zero_add]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1]
      ring
    calc ∑' m, (if n ≤ m + M then 2 * C * wt D β m else 0)
        ≤ ∑' m, 2 * C * (if s ≤ m then r ^ m else 0) :=
          hrowsum.tsum_le_tsum hle (hgs.mul_left _)
      _ = 2 * C * (r ^ s / (1 - r)) := by rw [tsum_mul_left, hval]
  have hrs : r ^ s ≤ (r⁻¹) ^ M * r ^ n := by
    have h1 : r ^ (s + M) ≤ r ^ n := pow_le_pow_of_le_one hr0.le hr1.le (by omega)
    rw [pow_add] at h1
    have hrM : 0 < r ^ M := by positivity
    rw [inv_pow, inv_mul_eq_div, le_div_iff₀ hrM]
    linarith
  have h1r : 0 < 1 - r := by linarith
  calc mass (muBeta D ω k β) (ball (genSet ω) R)ᶜ
      ≤ 1 / 2 * (2 * C * (r ^ s / (1 - r))) := hmass.trans (by gcongr)
    _ ≤ 1 / 2 * (2 * C * ((r⁻¹) ^ M * r ^ n / (1 - r))) := by gcongr
    _ = C * (r⁻¹) ^ M / (1 - r) * r ^ n := by ring

end P5Cor82Dev

end ErschlerZheng
end

section
open ErschlerZheng
open P5Cor82Dev in
theorem solution (D : ℕ) (β : ℝ)
    (hβ : 0 < β) :
    ∃ C > (0 : ℝ), ∀ ω : ℕ → Fin 3, SatisfiesFr D ω → ∀ k : ℕ → ℕ, IsAdmissibleSeq D k →
      (∀ᶠ n in Filter.atTop, k n ≤ n) →
        IsProbability (muBeta D ω k β) ∧ HasFiniteEntropy (muBeta D ω k β) ∧
          ∀ n : ℕ, mass (muBeta D ω k β) (ball (genSet ω) (2 ^ (2 * k n) * lengthL ω n))ᶜ ≤
            C / (2 : ℝ) ^ ((n : ℝ) * β) := by
  by_cases hD : 1 ≤ D
  · set r : ℝ := (2 : ℝ) ^ (-β) with hr
    have hr0 : 0 < r := by positivity
    have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hC := normConst_pos hD hβ
    have h1r : 0 < 1 - r := by linarith
    refine ⟨normConst D β * (r⁻¹) ^ (2 * D + 3) / (1 - r), by positivity,
      fun ω hω k hk hkn => ⟨isProbability_muBeta hω hk hβ hD,
        hasFiniteEntropy_muBeta hω hk hβ hD hkn, fun n => ?_⟩⟩
    have h := tail hω hk hβ hD n
    have e : r ^ n = 1 / (2 : ℝ) ^ ((n : ℝ) * β) := by
      rw [hr, ← rpow_eq_pow, Real.rpow_neg (by norm_num), one_div]
    rw [div_eq_mul_one_div, ← e]
    exact h
  · refine ⟨1, one_pos, fun ω hω => ?_⟩
    exfalso
    obtain ⟨m, hm, -⟩ := hω 0
    omega
end
