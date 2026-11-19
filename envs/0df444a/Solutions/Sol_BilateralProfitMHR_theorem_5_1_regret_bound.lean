-- Prove2me | solution 1 for BilateralProfitMHR.theorem_5_1_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T12:38:07.098413+00:00
-- url     : https://prove2.me/submissions/fcdfc861-830d-4df5-8055-6449ab89e5db

import Definitions.Def_BilateralProfitMHR_InitializeMHR
import Mathlib
import Definitions.Def_BilateralProfitMHR_BinaryControl
import Definitions.Def_BilateralProfitMHR_ConvexBandit
import Definitions.Def_BilateralProfitMHR_LogProfitOracle
import Theorems.Thm_BilateralProfitMHR_positive_density_profit_facts
import Theorems.Thm_BilateralProfitMHR_binary_controller_regret_bridge
import Definitions.Def_BilateralProfitMHR_Model
import Theorems.Thm_BilateralProfitMHR_lemma_5_6
import Theorems.Thm_BilateralProfitMHR_lemma_5_3


section BundlePart000


set_option autoImplicit false

namespace BilateralProfitMHR

private theorem bisectAux_bounds (f m M : ℕ) (hmM : m ≤ M) (I : ℕ × ℕ)
    (hI : I ∈ bisectAux f m M) : m ≤ I.1 ∧ I.1 ≤ I.2 ∧ I.2 ≤ M := by
  induction f generalizing m M with
  | zero =>
    have : I = (m, M) := by simpa [bisectAux] using hI
    subst I
    exact ⟨le_rfl, hmM, le_rfl⟩
  | succ f ih =>
    by_cases hlt : m < M
    · simp only [bisectAux, hlt, ↓reduceIte, Finset.mem_insert, Finset.mem_union] at hI
      rcases hI with rfl | hI | hI
      · exact ⟨le_rfl, hmM, le_rfl⟩
      · have hmid : m ≤ (m + M) / 2 ∧ (m + M) / 2 < M := by omega
        obtain ⟨h1, h2, h3⟩ := ih m ((m + M) / 2) hmid.1 hI
        exact ⟨h1, h2, h3.trans hmid.2.le⟩
      · have hmid : m ≤ (m + M) / 2 ∧ (m + M) / 2 < M := by omega
        obtain ⟨h1, h2, h3⟩ := ih ((m + M) / 2 + 1) M (by omega) hI
        exact ⟨by omega, h2, h3⟩
    · have : I = (m, M) := by simpa [bisectAux, hlt] using hI
      subst I
      exact ⟨le_rfl, hmM, le_rfl⟩

private theorem sPairsOf_bounds (I e : ℕ × ℕ) (hI : I.1 ≤ I.2) (he : e ∈ sPairsOf I) :
    I.1 ≤ e.1 ∧ e.1 ≤ e.2 ∧ e.2 ≤ I.2 := by
  have hmid : I.1 ≤ (I.1 + I.2) / 2 ∧ (I.1 + I.2) / 2 ≤ I.2 := by omega
  simp only [sPairsOf, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_Icc] at he
  rcases he with ⟨r, ⟨hr, hrk⟩, rfl⟩ | ⟨r, ⟨hr, hkr⟩, rfl⟩
  · exact ⟨hr.1, hrk, hmid.2⟩
  · exact ⟨hmid.1, hkr.le, hr.2⟩

private theorem Spairs_bounds {K : ℕ} {e : ℕ × ℕ} (he : e ∈ Spairs K) :
    e.1 ≤ e.2 ∧ e.2 ≤ K := by
  obtain ⟨I, hI, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨h1, h2, h3⟩ := bisectAux_bounds (K + 1) 0 K (by omega) I hI
  obtain ⟨_, h4, h5⟩ := sPairsOf_bounds I e h2 he
  exact ⟨h4, h5.trans h3⟩

private theorem sepMidAux_interval (f i j m M : ℕ) (hmi : m ≤ i) (hij : i < j)
    (hjM : j ≤ M) (hf : M - m < f) :
    ∃ I ∈ bisectAux f m M,
      I.1 ≤ i ∧ j ≤ I.2 ∧ i ≤ (I.1 + I.2) / 2 ∧ (I.1 + I.2) / 2 < j ∧
      sepMidAux f i j m M = (I.1 + I.2) / 2 := by
  induction f generalizing m M with
  | zero => omega
  | succ f ih =>
    have hlt : m < M := by omega
    have hmid : m ≤ (m + M) / 2 ∧ (m + M) / 2 < M := by omega
    by_cases hj : j ≤ (m + M) / 2
    · obtain ⟨I, hI, h1, h2, h3, h4, h5⟩ :=
        ih m ((m + M) / 2) hmi hj (by omega)
      refine ⟨I, ?_, h1, h2, h3, h4, ?_⟩
      · simp only [bisectAux, hlt, ↓reduceIte, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inl hI)
      · simpa only [sepMidAux, hlt, hj, ↓reduceIte] using h5
    · by_cases hi : (m + M) / 2 < i
      · obtain ⟨I, hI, h1, h2, h3, h4, h5⟩ :=
          ih ((m + M) / 2 + 1) M (by omega) hjM (by omega)
        refine ⟨I, ?_, h1, h2, h3, h4, ?_⟩
        · simp only [bisectAux, hlt, ↓reduceIte, Finset.mem_insert, Finset.mem_union]
          exact Or.inr (Or.inr hI)
        · simpa only [sepMidAux, hlt, hj, hi, ↓reduceIte] using h5
      · refine ⟨(m, M), ?_, hmi, hjM, by omega, by omega, ?_⟩
        · simp only [bisectAux, hlt, ↓reduceIte, Finset.mem_insert, true_or]
        · simp only [sepMidAux, hlt, hj, hi, ↓reduceIte]

private theorem sepMid_spec {K i j : ℕ} (hij : i < j) (hjK : j ≤ K) :
    i ≤ sepMid K i j ∧ sepMid K i j < j ∧
      (i, sepMid K i j) ∈ Spairs K ∧ (sepMid K i j, j) ∈ Spairs K ∧
      (sepMid K i j, sepMid K i j) ∈ Spairs K := by
  obtain ⟨I, hI, h1, h2, h3, h4, h5⟩ :=
    sepMidAux_interval (K + 1) i j 0 K (by omega) hij hjK (by omega)
  change sepMid K i j = (I.1 + I.2) / 2 at h5
  rw [h5]
  have hmid : I.1 ≤ (I.1 + I.2) / 2 ∧ (I.1 + I.2) / 2 ≤ I.2 := by omega
  refine ⟨h3, h4, ?_, ?_, ?_⟩
  all_goals apply Finset.mem_biUnion.mpr; refine ⟨I, hI, ?_⟩
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, by omega⟩, h3⟩, rfl⟩
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, h2⟩, h4⟩, rfl⟩
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨(I.1 + I.2) / 2,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hmid, le_rfl⟩, rfl⟩

private theorem bisectAux_self (f m : ℕ) : bisectAux f m m = {(m, m)} := by
  cases f <;> simp [bisectAux]

private theorem init_sum_insert_le {α : Type*} [DecidableEq α] (s : Finset α) (a : α)
    (w : α → ℕ) : ∑ i ∈ insert a s, w i ≤ w a + ∑ i ∈ s, w i := by
  by_cases h : a ∈ s
  · simp [Finset.insert_eq_of_mem h]
  · rw [Finset.sum_insert h]

private theorem init_sum_union_le {α : Type*} [DecidableEq α] (s t : Finset α)
    (w : α → ℕ) : ∑ i ∈ s ∪ t, w i ≤ (∑ i ∈ s, w i) + ∑ i ∈ t, w i := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := w)
  omega

/-- At depth at most `d`, each level contributes at most the initial interval length. -/
private theorem bisectAux_total_size_le (d f m M : ℕ) (hmM : m ≤ M)
    (hsize : M - m + 1 ≤ 2 ^ d) :
    ∑ I ∈ bisectAux f m M, (I.2 - I.1 + 1) ≤ (M - m + 1) * (d + 1) := by
  induction d generalizing f m M with
  | zero =>
    have : M = m := by norm_num at hsize; omega
    subst M
    simp [bisectAux_self]
  | succ d ih =>
    by_cases heq : M = m
    · subst M
      simp [bisectAux_self]
    · have hlt : m < M := by omega
      cases f with
      | zero => simp [bisectAux]
      | succ f =>
        have hmid : m ≤ (m + M) / 2 ∧ (m + M) / 2 < M := by omega
        have hsizeL : (m + M) / 2 - m + 1 ≤ 2 ^ d := by
          rw [pow_succ] at hsize
          omega
        have hsizeR : M - ((m + M) / 2 + 1) + 1 ≤ 2 ^ d := by
          rw [pow_succ] at hsize
          omega
        have hL := ih f m ((m + M) / 2) hmid.1 hsizeL
        have hR := ih f ((m + M) / 2 + 1) M (by omega) hsizeR
        rw [bisectAux, if_pos hlt]
        apply (init_sum_insert_le _ _ _).trans
        apply (Nat.add_le_add_left (init_sum_union_le _ _ _) _).trans
        apply (Nat.add_le_add_left (Nat.add_le_add hL hR) _).trans
        simp only [Prod.fst, Prod.snd]
        have hpart : (m + M) / 2 - m + 1 + (M - ((m + M) / 2 + 1) + 1) = M - m + 1 := by
          omega
        nlinarith

private theorem sPairsOf_card_le (I : ℕ × ℕ) : (sPairsOf I).card ≤ I.2 - I.1 + 1 := by
  let F := Finset.Icc I.1 I.2
  have hpart := Finset.card_filter_add_card_filter_not (s := F)
    (p := fun r => r ≤ (I.1 + I.2) / 2)
  have hcard : F.card ≤ I.2 - I.1 + 1 := by simp [F, Nat.card_Icc]; omega
  unfold sPairsOf
  apply (Finset.card_union_le _ _).trans
  apply (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)).trans
  change (F.filter (fun r => r ≤ (I.1 + I.2) / 2)).card +
    (F.filter (fun r => (I.1 + I.2) / 2 < r)).card ≤ _
  simpa only [not_le] using hpart.le.trans hcard

private theorem Spairs_card_le (K : ℕ) :
    (Spairs K).card ≤ (K + 1) * (Nat.clog 2 (K + 1) + 1) := by
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum (fun I _ => sPairsOf_card_le I)).trans
  have h := bisectAux_total_size_le (Nat.clog 2 (K + 1)) (K + 1) 0 K (by omega)
    (by simpa using Nat.le_pow_clog (by omega : 1 < 2) (K + 1))
  simpa only [Nat.sub_zero, bisect] using h

end BilateralProfitMHR
end BundlePart000


section BundlePart001


set_option autoImplicit false

namespace BilateralProfitMHR

open BilateralProfit

private theorem init_delta_pos (h : ℕ) : 0 < delta h := by
  unfold delta
  positivity

private theorem init_delta_inv_pow (h : ℕ) : delta h = ((2 : ℝ) ^ h)⁻¹ := by
  simp [delta, one_div, inv_pow]

private theorem init_delta_succ (h : ℕ) : delta (h + 1) = delta h / 2 := by
  simp [delta, pow_succ, div_eq_mul_inv]

private theorem init_delta_le_one (h : ℕ) : delta h ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

private theorem init_numScales_pos (K : ℕ) : 0 < numScales K := by
  unfold numScales
  omega

private theorem init_numScales_le {K : ℕ} (hK : 0 < K) : numScales K ≤ K := by
  have := Nat.log_lt_self 2 (Nat.ne_of_gt hK)
  unfold numScales
  omega

private theorem init_delta_ge_inv {K h : ℕ} (hK : 0 < K) (hh : h < numScales K) :
    1 / (K : ℝ) ≤ delta h := by
  have hh' : h ≤ Nat.log 2 K := by unfold numScales at hh; omega
  have hpow : 2 ^ h ≤ K :=
    (Nat.pow_le_pow_right (by omega) hh').trans (Nat.pow_log_le_self 2 (Nat.ne_of_gt hK))
  have hpow' : (2 : ℝ) ^ h ≤ K := by exact_mod_cast hpow
  rw [init_delta_inv_pow, one_div]
  exact inv_anti₀ (by positivity) hpow'

private theorem init_last_delta_lt {K : ℕ} (hK : 0 < K) :
    delta (Nat.log 2 K) < 2 / K := by
  have hp : K < 2 ^ (Nat.log 2 K + 1) := Nat.lt_pow_succ_log_self (by omega) K
  have hp' : (K : ℝ) < 2 * (2 : ℝ) ^ (Nat.log 2 K) := by
    exact_mod_cast (by simpa [pow_succ, Nat.mul_comm] using hp : K < 2 * 2 ^ (Nat.log 2 K))
  rw [init_delta_inv_pow]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < K)).2
  have hx := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 K)).2 hp'
  simpa [div_eq_mul_inv, mul_comm] using hx

private theorem init_firstTrigger_spec {K T h : ℕ} {ω : Samples K T}
    (hh : firstTrigger K T ω = some h) :
    h < numScales K ∧ Triggers K T h ω ∧ ∀ j < h, ¬ Triggers K T j ω := by
  classical
  unfold firstTrigger at hh
  split_ifs at hh with hx
  · have heq : Nat.find hx = h := Option.some.inj hh
    subst h
    obtain ⟨hb, ht⟩ := Nat.find_spec hx
    refine ⟨hb, ht, ?_⟩
    intro j hj htr
    have hn := Nat.find_min hx hj
    exact hn ⟨hj.trans hb, htr⟩

private theorem init_firstTrigger_none {K T : ℕ} {ω : Samples K T} :
    firstTrigger K T ω = none ↔ ∀ h < numScales K, ¬ Triggers K T h ω := by
  unfold firstTrigger
  split_ifs with hx
  · constructor
    · simp
    · intro hn
      obtain ⟨h, hb, ht⟩ := hx
      exact False.elim (hn h hb ht)
  · simp only [not_exists, not_and] at hx
    exact ⟨fun _ => hx, fun _ => rfl⟩

private theorem initOut_some {K T h : ℕ} {ω : Samples K T} {R : Set (ℝ × ℝ)}
    (ho : initOut K T ω = some (h, R)) :
    firstTrigger K T ω = some h ∧ R = region K T h ω := by
  unfold initOut at ho
  cases hf : firstTrigger K T ω with
  | none => simp [hf] at ho
  | some j =>
    have heq : (j, region K T j ω) = (h, R) := by simpa [hf] using ho
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨rfl, rfl⟩

private theorem initOut_none {K T : ℕ} {ω : Samples K T} :
    initOut K T ω = none ↔ firstTrigger K T ω = none := by
  simp [initOut]

private theorem init_tested_lt {K T h : ℕ} {ω : Samples K T}
    (hh : h ∈ testedScales K T ω) : h < numScales K := by
  unfold testedScales at hh
  cases hf : firstTrigger K T ω with
  | none => simpa [hf] using hh
  | some j =>
    have hlt : h < j + 1 := by simpa [hf] using hh
    have hj := (init_firstTrigger_spec hf).1
    omega

private theorem init_trigger_mem_tested {K T h : ℕ} {ω : Samples K T}
    (hf : firstTrigger K T ω = some h) : h ∈ testedScales K T ω := by
  simp [testedScales, hf]

private theorem init_preceding_mem_tested {K T h j : ℕ} {ω : Samples K T}
    (hf : firstTrigger K T ω = some h) (hj : j < h) : j ∈ testedScales K T ω := by
  simp [testedScales, hf, Finset.mem_range]
  omega

private theorem init_none_mem_tested {K T h : ℕ} {ω : Samples K T}
    (hf : firstTrigger K T ω = none) (hh : h < numScales K) :
    h ∈ testedScales K T ω := by
  simpa [testedScales, hf] using hh

private theorem init_mem_tested_iff {K T h : ℕ} {ω : Samples K T} :
    h ∈ testedScales K T ω ↔ h < numScales K ∧ ∀ j < h, ¬ Triggers K T j ω := by
  cases hf : firstTrigger K T ω with
  | none =>
    have hn := init_firstTrigger_none.mp hf
    simp only [testedScales, hf, Finset.mem_range]
    exact ⟨fun hh => ⟨hh, fun j hj => hn j (hj.trans hh)⟩, fun hh => hh.1⟩
  | some g =>
    obtain ⟨hg, htr, hprev⟩ := init_firstTrigger_spec hf
    simp only [testedScales, hf, Finset.mem_range]
    constructor
    · intro hh
      refine ⟨by omega, ?_⟩
      intro j hj
      exact hprev j (by omega)
    · rintro ⟨hh, hn⟩
      by_contra hnot
      have : g < h := by omega
      exact hn g this htr

private theorem init_weighted_pos {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : 0 < x) (hy : 0 < y) : 0 < a * x + b * y := by
  by_cases h : 0 < a
  · exact add_pos_of_pos_of_nonneg (mul_pos h hx) (mul_nonneg hb hy.le)
  · have hb' : 0 < b := by linarith
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha hx.le) (mul_pos hb' hy)

private theorem init_convex_intT : Convex ℝ intT := by
  intro x hx y hy a b ha hb hab
  change 0 < a * x.1 + b * y.1 ∧
    a * x.1 + b * y.1 < a * x.2 + b * y.2 ∧ a * x.2 + b * y.2 < 1
  refine ⟨init_weighted_pos ha hb hab hx.1 hy.1, ?_, ?_⟩
  · have hp := init_weighted_pos ha hb hab (sub_pos.mpr hx.2.1) (sub_pos.mpr hy.2.1)
    nlinarith
  · have hp := init_weighted_pos ha hb hab (sub_pos.mpr hx.2.2) (sub_pos.mpr hy.2.2)
    nlinarith

private theorem init_selected_mem_intT {K T h : ℕ} (hK : 0 < K) (ω : Samples K T)
    (e : Act K) (he : 3 * delta h / 4 ≤ muHat K T h ω e) : pt K e.1 ∈ intT := by
  have hδ := init_delta_pos h
  have hh : 0 < muHat K T h ω e := (by positivity : 0 < 3 * delta h / 4).trans_le he
  have hi : 1 ≤ (e.1.1 : ℕ) ∧ (e.1.1 : ℕ) < e.1.2 ∧ (e.1.2 : ℕ) < K := by
    by_contra h
    rw [muHat, if_neg h] at hh
    exact (lt_irrefl 0) hh
  change 0 < (e.1.1 : ℝ) / K ∧ (e.1.1 : ℝ) / K < (e.1.2 : ℝ) / K ∧
    (e.1.2 : ℝ) / K < 1
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨div_pos (by exact_mod_cast (by omega : 0 < (e.1.1 : ℕ))) hKr,
    (div_lt_div_iff_of_pos_right hKr).2 (by exact_mod_cast hi.2.1), ?_⟩
  exact (div_lt_one hKr).2 (by exact_mod_cast hi.2.2)

private theorem init_region_geometry {K T h : ℕ} (hK : 0 < K) (ω : Samples K T)
    (ht : Triggers K T h ω) :
    (region K T h ω).Nonempty ∧ IsCompact (region K T h ω) ∧
      Convex ℝ (region K T h ω) ∧ region K T h ω ⊆ intT := by
  classical
  obtain ⟨e, he⟩ := ht
  have hsel : 3 * delta h / 4 ≤ muHat K T h ω e := by
    have := init_delta_pos h
    linarith
  refine ⟨?_, ?_, convex_convexHull _ _, ?_⟩
  · apply Set.Nonempty.convexHull
    exact ⟨pt K e.1, Set.mem_image_of_mem _ hsel⟩
  · exact (Set.toFinite _).isCompact_convexHull ℝ
  · apply convexHull_min _ init_convex_intT
    rintro _ ⟨e, he, rfl⟩
    exact init_selected_mem_intT hK ω e he

end BilateralProfitMHR
end BundlePart001


section BundlePart002



set_option autoImplicit false

namespace BilateralProfitMHR

open BilateralProfit
open scoped Classical

/-- The pairs sampled by a scale, with their original natural-number indices. -/
private abbrev InitProbePair (K : ℕ) := {z : ℕ × ℕ // z ∈ Spairs K}

/-- The probes of a fixed scale: sampled pair followed by its repetition. -/
private abbrev InitProbe (K T h : ℕ) := InitProbePair K × Fin (nSamp T h)

private noncomputable instance initProbePairFintype (K : ℕ) : Fintype (InitProbePair K) :=
  Fintype.ofFinset (Spairs K) (by simp)

/-- The coordinate in the fresh-sample array read by a scheduled probe. -/
private def initProbeEmbed {K T : ℕ} (h : Fin (numScales K)) (z : InitProbe K T h) : SampleIdx K T :=
  ⟨h, (⟨z.1.1.1, by have := Spairs_bounds z.1.2; omega⟩,
    ⟨z.1.1.2, by have := Spairs_bounds z.1.2; omega⟩), z.2⟩

private theorem initProbeEmbed_injective {K T : ℕ} (h : Fin (numScales K)) :
    Function.Injective (initProbeEmbed (T := T) h) := by
  intro z z' he
  rcases z with ⟨⟨⟨i, j⟩, hz⟩, r⟩
  rcases z' with ⟨⟨⟨i', j'⟩, hz'⟩, r'⟩
  simp [initProbeEmbed, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, Fin.mk.injEq] at he
  rcases he with ⟨⟨rfl, rfl⟩, rfl⟩
  rfl

private theorem initProbe_card (K T h : ℕ) :
    Fintype.card (InitProbe K T h) = (Spairs K).card * nSamp T h := by
  rw [Fintype.card_prod, Fintype.card_fin]
  congr 1
  exact Fintype.card_ofFinset _ _

/-- A fixed finite enumeration of the probes of one scale. -/
private noncomputable def initScaleSchedule {K T : ℕ} (h : Fin (numScales K)) : List (SampleIdx K T) :=
  List.ofFn fun r : Fin (Fintype.card (InitProbe K T h)) =>
    initProbeEmbed h ((Fintype.equivFin (InitProbe K T h)).symm r)

private theorem initScaleSchedule_length {K T : ℕ} (h : Fin (numScales K)) :
    (initScaleSchedule (T := T) h).length = (Spairs K).card * nSamp T h := by
  simp [initScaleSchedule, initProbe_card]

private theorem initScaleSchedule_nodup {K T : ℕ} (h : Fin (numScales K)) :
    (initScaleSchedule (T := T) h).Nodup := by
  apply List.nodup_ofFn.mpr
  exact (initProbeEmbed_injective h).comp (Fintype.equivFin (InitProbe K T h)).symm.injective

private theorem initScaleSchedule_mem_iff {K T : ℕ} (h : Fin (numScales K)) (z : SampleIdx K T) :
    z ∈ initScaleSchedule h ↔ ∃ q : InitProbe K T h, initProbeEmbed h q = z := by
  simp only [initScaleSchedule, List.mem_ofFn]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨(Fintype.equivFin (InitProbe K T h)).symm r, hr⟩
  · rintro ⟨q, rfl⟩
    exact ⟨Fintype.equivFin (InitProbe K T h) q, by simp⟩

private theorem initScaleSchedule_disjoint {K T : ℕ} (h h' : Fin (numScales K)) (hne : h ≠ h') :
    List.Disjoint (initScaleSchedule (T := T) h) (initScaleSchedule h') := by
  intro z hz hz'
  obtain ⟨q, rfl⟩ := (initScaleSchedule_mem_iff h z).mp hz
  obtain ⟨q', he⟩ := (initScaleSchedule_mem_iff h' _).mp hz'
  have heh := congrArg Sigma.fst he
  exact hne heh.symm

/-- Prefix length before the probes of scale `h`. -/
private noncomputable def initScaleStart (K T h : ℕ) : ℕ :=
  ∑ j ∈ Finset.range h, (Spairs K).card * nSamp T j

private theorem initScaleStart_zero (K T : ℕ) : initScaleStart K T 0 = 0 := by
  simp [initScaleStart]

private theorem initScaleStart_succ (K T h : ℕ) : initScaleStart K T (h + 1) =
    initScaleStart K T h + (Spairs K).card * nSamp T h := by
  exact Finset.sum_range_succ _ _

/-- The chronological probe list for scales `0, ..., n-1`. -/
private noncomputable def initPrefixSchedule (K T n : ℕ) (hn : n ≤ numScales K) : List (SampleIdx K T) :=
  (List.ofFn fun h : Fin n => initScaleSchedule (T := T) ⟨h, h.isLt.trans_le hn⟩).flatten

private theorem initPrefixSchedule_length (K T n : ℕ) (hn : n ≤ numScales K) :
    (initPrefixSchedule K T n hn).length = initScaleStart K T n := by
  unfold initPrefixSchedule
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  change (∑ h : Fin n, (initScaleSchedule (T := T) ⟨h, h.isLt.trans_le hn⟩).length) = _
  simp_rw [initScaleSchedule_length]
  exact Fin.sum_univ_eq_sum_range (fun h => (Spairs K).card * nSamp T h) n

private theorem initPrefixSchedule_succ (K T n : ℕ) (hn : n + 1 ≤ numScales K) :
    initPrefixSchedule K T (n + 1) hn =
      initPrefixSchedule K T n (by omega) ++ initScaleSchedule (T := T) ⟨n, by omega⟩ := by
  unfold initPrefixSchedule
  rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rfl

private theorem initPrefixSchedule_nodup (K T n : ℕ) (hn : n ≤ numScales K) :
    (initPrefixSchedule K T n hn).Nodup := by
  apply List.nodup_flatten.mpr
  constructor
  · intro l hl
    obtain ⟨h, rfl⟩ := List.mem_ofFn.mp hl
    exact initScaleSchedule_nodup _
  · rw [List.pairwise_ofFn]
    intro i j hij
    apply initScaleSchedule_disjoint
    intro he
    have heval : (i : ℕ) = j := congrArg (fun h : Fin (numScales K) => h.val) he
    have hij' : i = j := Fin.ext heval
    exact (ne_of_lt hij) hij'

private theorem initPrefixSchedule_mem_iff (K T n : ℕ) (hn : n ≤ numScales K) (z : SampleIdx K T) :
    z ∈ initPrefixSchedule K T n hn ↔
      ∃ h : Fin (numScales K), (h : ℕ) < n ∧ z ∈ initScaleSchedule (T := T) h := by
  unfold initPrefixSchedule
  simp only [List.mem_flatten, List.mem_ofFn]
  constructor
  · rintro ⟨l, ⟨h, rfl⟩, hz⟩
    exact ⟨⟨h, h.isLt.trans_le hn⟩, h.isLt, hz⟩
  · rintro ⟨h, hh, hz⟩
    exact ⟨initScaleSchedule h, ⟨⟨h, hh⟩, rfl⟩, hz⟩

private theorem initRounds_eq_prefix_of_trigger {K T h : ℕ} {ω : Samples K T}
    (hf : firstTrigger K T ω = some h) : initRounds K T ω = initScaleStart K T (h + 1) := by
  simp [initRounds, testedScales, hf, initScaleStart]

private theorem initRounds_eq_prefix_of_none {K T : ℕ} {ω : Samples K T}
    (hf : firstTrigger K T ω = none) : initRounds K T ω = initScaleStart K T (numScales K) := by
  simp [initRounds, testedScales, hf, initScaleStart]

/-- Two sample arrays have the same observable bits on all probes used by the initializer. -/
private def InitSameProbeBits (K T : ℕ) (ω ω' : Samples K T) : Prop :=
  ∀ (h : Fin (numScales K)) (z : InitProbe K T h),
    tradeBit (ω (initProbeEmbed h z)) ((z.1.1.1 : ℝ) / K, (z.1.1.2 : ℝ) / K) =
      tradeBit (ω' (initProbeEmbed h z)) ((z.1.1.1 : ℝ) / K, (z.1.1.2 : ℝ) / K)

/-- Equality of the observed bits on scales strictly before `n`. -/
private def InitSameProbeBitsBefore (K T n : ℕ) (ω ω' : Samples K T) : Prop :=
  ∀ (h : Fin (numScales K)), (h : ℕ) < n → ∀ z : InitProbe K T h,
    tradeBit (ω (initProbeEmbed h z)) ((z.1.1.1 : ℝ) / K, (z.1.1.2 : ℝ) / K) =
      tradeBit (ω' (initProbeEmbed h z)) ((z.1.1.1 : ℝ) / K, (z.1.1.2 : ℝ) / K)

private theorem init_Pbar_eq_of_same_scale_bits {K T h : ℕ} {ω ω' : Samples K T}
    (hh : h < numScales K)
    (hb : ∀ z : InitProbe K T h,
      tradeBit (ω (initProbeEmbed ⟨h, hh⟩ z)) ((z.1.1.1 : ℝ) / K, (z.1.1.2 : ℝ) / K) =
        tradeBit (ω' (initProbeEmbed ⟨h, hh⟩ z)) ((z.1.1.1 : ℝ) / K, (z.1.1.2 : ℝ) / K))
    {z : ℕ × ℕ} (hz : z ∈ Spairs K) : Pbar K T h ω z.1 z.2 = Pbar K T h ω' z.1 z.2 := by
  classical
  unfold Pbar
  split_ifs with hvalid
  · congr 1
    apply Finset.sum_congr rfl
    intro r hr
    exact hb (⟨z, hz⟩, r)
  · rfl

private theorem init_muHat_eq_of_Pbar_eq {K T h : ℕ} {ω ω' : Samples K T}
    (hb : ∀ z ∈ Spairs K, Pbar K T h ω z.1 z.2 = Pbar K T h ω' z.1 z.2)
    (e : Act K) : muHat K T h ω e = muHat K T h ω' e := by
  classical
  unfold muHat
  split_ifs with hi
  · obtain ⟨_, _, hs1, hs2, hs3⟩ := sepMid_spec hi.2.1 (Nat.lt_succ_iff.mp e.1.2.isLt)
    rw [hb _ hs1, hb _ hs2, hb _ hs3]
  · rfl

private theorem init_muHat_eq_of_same_bits_before {K T n h : ℕ} {ω ω' : Samples K T}
    (hb : InitSameProbeBitsBefore K T n ω ω') (hh : h < numScales K) (hhn : h < n)
    (e : Act K) : muHat K T h ω e = muHat K T h ω' e := by
  apply init_muHat_eq_of_Pbar_eq
  intro z hz
  exact init_Pbar_eq_of_same_scale_bits hh (hb ⟨h, hh⟩ hhn) hz

private theorem init_Triggers_eq_of_same_bits_before {K T n h : ℕ} {ω ω' : Samples K T}
    (hb : InitSameProbeBitsBefore K T n ω ω') (hh : h < numScales K) (hhn : h < n) :
    Triggers K T h ω ↔ Triggers K T h ω' := by
  unfold Triggers
  simp_rw [init_muHat_eq_of_same_bits_before hb hh hhn]

private theorem init_reached_eq_of_same_bits_before {K T h : ℕ} {ω ω' : Samples K T}
    (hb : InitSameProbeBitsBefore K T h ω ω') :
    h ∈ testedScales K T ω ↔ h ∈ testedScales K T ω' := by
  rw [init_mem_tested_iff, init_mem_tested_iff]
  constructor
  all_goals
    rintro ⟨hh, hn⟩
    refine ⟨hh, ?_⟩
    intro j hj
    simpa only [init_Triggers_eq_of_same_bits_before hb (hj.trans hh) hj] using hn j hj

private theorem init_firstTrigger_of_spec {K T h : ℕ} {ω : Samples K T}
    (hh : h < numScales K) (ht : Triggers K T h ω)
    (hn : ∀ j < h, ¬ Triggers K T j ω) : firstTrigger K T ω = some h := by
  cases hf : firstTrigger K T ω with
  | none => exact False.elim (init_firstTrigger_none.mp hf h hh ht)
  | some g =>
    obtain ⟨hg, hgt, hprev⟩ := init_firstTrigger_spec hf
    have hge : g = h := by
      rcases lt_trichotomy g h with hlt | heq | hlt
      · exact False.elim (hn g hlt hgt)
      · exact heq
      · exact False.elim (hprev h hlt ht)
    simp [hge]

private theorem init_firstTrigger_preserved_by_prefix {K T h : ℕ} {ω ω' : Samples K T}
    (hf : firstTrigger K T ω = some h)
    (hb : InitSameProbeBitsBefore K T (h + 1) ω ω') : firstTrigger K T ω' = some h := by
  obtain ⟨hh, ht, hn⟩ := init_firstTrigger_spec hf
  apply init_firstTrigger_of_spec hh
  · exact (init_Triggers_eq_of_same_bits_before hb hh (by omega)).mp ht
  · intro j hj
    simpa only [init_Triggers_eq_of_same_bits_before hb (hj.trans hh) (by omega)] using hn j hj

private theorem init_Pbar_eq_of_same_probe_bits {K T : ℕ} {ω ω' : Samples K T}
    (hb : InitSameProbeBits K T ω ω') (h : ℕ) {z : ℕ × ℕ} (hz : z ∈ Spairs K) :
    Pbar K T h ω z.1 z.2 = Pbar K T h ω' z.1 z.2 := by
  classical
  unfold Pbar
  split_ifs with hh
  · congr 1
    apply Finset.sum_congr rfl
    intro r hr
    exact hb ⟨h, hh.1⟩ (⟨z, hz⟩, r)
  · rfl

private theorem init_muHat_eq_of_same_probe_bits {K T : ℕ} {ω ω' : Samples K T}
    (hb : InitSameProbeBits K T ω ω') (h : ℕ) (e : Act K) :
    muHat K T h ω e = muHat K T h ω' e := by
  classical
  unfold muHat
  split_ifs with hi
  · obtain ⟨_, _, hs1, hs2, hs3⟩ := sepMid_spec hi.2.1 (Nat.lt_succ_iff.mp e.1.2.isLt)
    rw [init_Pbar_eq_of_same_probe_bits hb h hs1,
      init_Pbar_eq_of_same_probe_bits hb h hs2,
      init_Pbar_eq_of_same_probe_bits hb h hs3]
  · rfl

private theorem init_Triggers_eq_of_same_probe_bits {K T : ℕ} {ω ω' : Samples K T}
    (hb : InitSameProbeBits K T ω ω') (h : ℕ) :
    Triggers K T h ω ↔ Triggers K T h ω' := by
  unfold Triggers
  simp_rw [init_muHat_eq_of_same_probe_bits hb h]

private theorem init_firstTrigger_eq_of_same_probe_bits {K T : ℕ} {ω ω' : Samples K T}
    (hb : InitSameProbeBits K T ω ω') : firstTrigger K T ω = firstTrigger K T ω' := by
  unfold firstTrigger
  simp_rw [init_Triggers_eq_of_same_probe_bits hb]

private theorem init_region_eq_of_same_probe_bits {K T : ℕ} {ω ω' : Samples K T}
    (hb : InitSameProbeBits K T ω ω') (h : ℕ) : region K T h ω = region K T h ω' := by
  unfold region
  simp_rw [init_muHat_eq_of_same_probe_bits hb]

private theorem initOut_eq_of_same_probe_bits {K T : ℕ} {ω ω' : Samples K T}
    (hb : InitSameProbeBits K T ω ω') : initOut K T ω = initOut K T ω' := by
  unfold initOut
  rw [init_firstTrigger_eq_of_same_probe_bits hb]
  cases firstTrigger K T ω' <;> simp [init_region_eq_of_same_probe_bits hb]

private theorem init_tested_eq_of_same_probe_bits {K T : ℕ} {ω ω' : Samples K T}
    (hb : InitSameProbeBits K T ω ω') : testedScales K T ω = testedScales K T ω' := by
  unfold testedScales
  rw [init_firstTrigger_eq_of_same_probe_bits hb]

private theorem init_rounds_eq_of_same_probe_bits {K T : ℕ} {ω ω' : Samples K T}
    (hb : InitSameProbeBits K T ω ω') : initRounds K T ω = initRounds K T ω' := by
  unfold initRounds
  rw [init_tested_eq_of_same_probe_bits hb]

end BilateralProfitMHR
end BundlePart002


section BundlePart003


namespace BilateralProfitMHR
private theorem init_nat_div_mem_Icc {K i : ℕ} (hK : 0 < K) (hi : i ≤ K) :
    (i : ℝ) / K ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨by positivity, (div_le_one (by positivity : (0 : ℝ) < K)).2 ?_⟩
  exact_mod_cast hi
end BilateralProfitMHR
end BundlePart003


section BundlePart004



set_option autoImplicit false

namespace BilateralProfitMHR

open BilateralProfit

/-- The price attached to an entry of the fixed probing schedule. -/
private noncomputable def initSamplePrice {K T : ℕ} (z : SampleIdx K T) : ℝ × ℝ :=
  ((z.2.1.1 : ℝ) / K, (z.2.1.2 : ℝ) / K)

private theorem initSamplePrice_mem_unitSq {K T : ℕ} (hK : 0 < K) (z : SampleIdx K T) :
    initSamplePrice z ∈ unitSq :=
  ⟨init_nat_div_mem_Icc hK (Nat.lt_succ_iff.mp z.2.1.1.isLt),
    init_nat_div_mem_Icc hK (Nat.lt_succ_iff.mp z.2.1.2.isLt)⟩

private theorem initProbeEmbed_price {K T : ℕ} (h : Fin (numScales K)) (z : InitProbe K T h) :
    initSamplePrice (initProbeEmbed h z) = ((z.1.1.1 : ℝ) / K, (z.1.1.2 : ℝ) / K) := rfl

private theorem initProbeEmbed_price_ordered {K T : ℕ} (h : Fin (numScales K)) (z : InitProbe K T h) :
    (initSamplePrice (initProbeEmbed h z)).1 ≤ (initSamplePrice (initProbeEmbed h z)).2 := by
  change (z.1.1.1 : ℝ) / K ≤ (z.1.1.2 : ℝ) / K
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Spairs_bounds z.1.2).1

private theorem initScaleSchedule_mem_scale {K T : ℕ} (h : Fin (numScales K))
    {z : SampleIdx K T} (hz : z ∈ initScaleSchedule h) : z.1 = h := by
  obtain ⟨q, rfl⟩ := (initScaleSchedule_mem_iff h z).mp hz
  rfl

/-- A valuation pair encoding one trade bit at every legal price. -/
private def initBitValuation (b : Bool) : ℝ × ℝ := if b then (0, 1) else (1, 0)

private theorem initBitValuation_trade (a : ℝ × ℝ) (ha : a ∈ unitSq) (horder : a.1 ≤ a.2)
    (b : Bool) : tradeBit (initBitValuation b) a = if b then 1 else 0 := by
  cases b with
  | true =>
    have ht : Trades (0, 1) a := ⟨ha.1.1, ha.2.2⟩
    simp [initBitValuation, tradeBit, ht]
  | false =>
    have ht : ¬ Trades (1, 0) a := by
      rintro ⟨h1, h2⟩
      change 1 ≤ a.1 at h1
      change a.2 ≤ 0 at h2
      linarith
    simp [initBitValuation, tradeBit, ht]

/-- The observed bit associated with each array coordinate and its fixed grid price. -/
private noncomputable def initReadBits {K T : ℕ} (ω : Samples K T) (z : SampleIdx K T) : Bool :=
  decide (Trades (ω z) (initSamplePrice z))

/-- Reconstruct a sample array from its recorded trade bits. -/
private def initDecodeBits {K T : ℕ} (b : SampleIdx K T → Bool) : Samples K T :=
  fun z => initBitValuation (b z)

private theorem init_read_decode_same_probe_bits {K T : ℕ} (hK : 0 < K) (ω : Samples K T) :
    InitSameProbeBits K T ω (initDecodeBits (initReadBits ω)) := by
  intro h z
  change tradeBit (ω (initProbeEmbed h z)) (initSamplePrice (initProbeEmbed h z)) =
    tradeBit (initBitValuation (initReadBits ω (initProbeEmbed h z)))
      (initSamplePrice (initProbeEmbed h z))
  rw [initBitValuation_trade _ (initSamplePrice_mem_unitSq hK _) (initProbeEmbed_price_ordered h z)]
  simp [initReadBits, tradeBit]

private theorem init_decoded_output {K T : ℕ} (hK : 0 < K) (ω : Samples K T) :
    initOut K T (initDecodeBits (initReadBits ω)) = initOut K T ω :=
  (initOut_eq_of_same_probe_bits (init_read_decode_same_probe_bits hK ω)).symm

private theorem init_decoded_rounds {K T : ℕ} (hK : 0 < K) (ω : Samples K T) :
    initRounds K T (initDecodeBits (initReadBits ω)) = initRounds K T ω :=
  (init_rounds_eq_of_same_probe_bits (init_read_decode_same_probe_bits hK ω)).symm

private theorem init_decode_eq_on_prefix {K T n : ℕ} (hK : 0 < K) (ω : Samples K T)
    (b : SampleIdx K T → Bool)
    (hb : ∀ (h : Fin (numScales K)), (h : ℕ) < n → ∀ z : InitProbe K T h,
      b (initProbeEmbed h z) = initReadBits ω (initProbeEmbed h z)) :
    InitSameProbeBitsBefore K T n ω (initDecodeBits b) := by
  intro h hh z
  change tradeBit (ω (initProbeEmbed h z)) (initSamplePrice (initProbeEmbed h z)) =
    tradeBit (initBitValuation (b (initProbeEmbed h z))) (initSamplePrice (initProbeEmbed h z))
  rw [hb h hh z, initBitValuation_trade _ (initSamplePrice_mem_unitSq hK _)
    (initProbeEmbed_price_ordered h z)]
  simp [initReadBits, tradeBit]

end BilateralProfitMHR
end BundlePart004


section BundlePart005


set_option autoImplicit false

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit

/-- The original natural pair underlying a coordinate of the probing array. -/
private def initSamplePair {K T : ℕ} (z : SampleIdx K T) : ℕ × ℕ :=
  (z.2.1.1, z.2.1.2)

private theorem initScaleSchedule_sum {K T : ℕ} (h : Fin (numScales K)) (w : ℕ × ℕ → ℝ) :
    ((initScaleSchedule (T := T) h).map fun z => w (initSamplePair z)).sum =
      (nSamp T h : ℝ) * ∑ z ∈ Spairs K, w z := by
  classical
  unfold initScaleSchedule
  rw [List.map_ofFn, List.sum_ofFn]
  change (∑ r : Fin (Fintype.card (InitProbe K T h)),
    w (((Fintype.equivFin (InitProbe K T h)).symm r).1.1)) = _
  rw [(Fintype.equivFin (InitProbe K T h)).symm.sum_comp
    (fun q : InitProbe K T h => w q.1.1)]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_coe_sort (Spairs K) w

private theorem initPrefixSchedule_sum (K T n : ℕ) (hn : n ≤ numScales K) (w : ℕ × ℕ → ℝ) :
    ((initPrefixSchedule K T n hn).map fun z => w (initSamplePair z)).sum =
      ∑ h ∈ Finset.range n, (nSamp T h : ℝ) * ∑ z ∈ Spairs K, w z := by
  unfold initPrefixSchedule
  rw [List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn, List.sum_ofFn]
  change (∑ h : Fin n,
    ((initScaleSchedule (T := T) ⟨h, h.isLt.trans_le hn⟩).map fun z => w (initSamplePair z)).sum) = _
  simp_rw [initScaleSchedule_sum]
  exact Fin.sum_univ_eq_sum_range (fun h => (nSamp T h : ℝ) * ∑ z ∈ Spairs K, w z) n

/-- The chronological list of probes actually used up to the first trigger, or all scales. -/
private noncomputable def initRunSchedule (K T : ℕ) (ω : Samples K T) : List (SampleIdx K T) :=
  match hf : firstTrigger K T ω with
  | some h => initPrefixSchedule K T (h + 1) (Nat.succ_le_of_lt (init_firstTrigger_spec hf).1)
  | none => initPrefixSchedule K T (numScales K) le_rfl

private theorem initRunSchedule_length (K T : ℕ) (ω : Samples K T) :
    (initRunSchedule K T ω).length = initRounds K T ω := by
  unfold initRunSchedule
  split
  · rw [initPrefixSchedule_length]
    exact (initRounds_eq_prefix_of_trigger ‹_›).symm
  · rw [initPrefixSchedule_length]
    exact (initRounds_eq_prefix_of_none ‹_›).symm

private theorem initRunSchedule_nodup (K T : ℕ) (ω : Samples K T) :
    (initRunSchedule K T ω).Nodup := by
  unfold initRunSchedule
  split <;> exact initPrefixSchedule_nodup _ _ _ _

private theorem initRunSchedule_sum (K T : ℕ) (ω : Samples K T) (w : ℕ × ℕ → ℝ) :
    ((initRunSchedule K T ω).map fun z => w (initSamplePair z)).sum =
      ∑ h ∈ testedScales K T ω, (nSamp T h : ℝ) * ∑ z ∈ Spairs K, w z := by
  unfold initRunSchedule
  split
  · rw [initPrefixSchedule_sum]
    simp only [testedScales, ‹firstTrigger K T ω = some _›]
  · rw [initPrefixSchedule_sum]
    simp only [testedScales, ‹firstTrigger K T ω = none›]

private theorem initRunSchedule_profit_gap (K T : ℕ) (D : Measure (ℝ × ℝ)) (ω : Samples K T) :
    ((initRunSchedule K T ω).map fun z => muStar D - muP D (initSamplePrice z)).sum =
      filterRegret K T D ω := by
  exact initRunSchedule_sum K T ω
    (fun z => muStar D - muP D ((z.1 : ℝ) / K, (z.2 : ℝ) / K))

end BilateralProfitMHR
end BundlePart005


section BundlePart006



set_option autoImplicit false

namespace BilateralProfitMHR

open BilateralProfit

private theorem init_log_ge_one {T : ℕ} (hT : 2 ≤ T) : 1 ≤ Real.log (2 * T) := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h4 : 1 ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  apply h4.trans
  apply Real.log_le_log (by norm_num)
  exact_mod_cast (by omega : 4 ≤ 2 * T)

private theorem init_Spairs_real_bound {K T : ℕ} (hK : 2 ≤ K) (hKT : K ≤ T) :
    ((Spairs K).card : ℝ) ≤ 6 * K * Real.log (2 * T) := by
  have hT : 2 ≤ T := hK.trans hKT
  have hL := init_log_ge_one hT
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2p : 0 < Real.log 2 := by linarith
  have hd : Nat.clog 2 (K + 1) ≤ Nat.log 2 (K + 1) + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by omega : 1 < 2) (K + 1)).le
  have hd' : (Nat.clog 2 (K + 1) : ℝ) ≤ (Nat.log 2 (K + 1) : ℝ) + 1 := by exact_mod_cast hd
  have hl := Real.natLog_le_logb (K + 1) 2
  rw [Real.logb] at hl
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hl
  have hlogKT : Real.log (K + 1) ≤ Real.log (2 * T) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (by omega : K + 1 ≤ 2 * T)
  have hdiv : Real.log (K + 1) / Real.log 2 ≤ 2 * Real.log (2 * T) := by
    apply (div_le_iff₀ hlog2p).2
    nlinarith [mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ Real.log (2 * T) by linarith)]
  have hdepth : (Nat.clog 2 (K + 1) : ℝ) + 1 ≤ 4 * Real.log (2 * T) := by linarith
  have hc : ((Spairs K).card : ℝ) ≤ (K + 1 : ℝ) * ((Nat.clog 2 (K + 1) : ℝ) + 1) := by
    exact_mod_cast Spairs_card_le K
  have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
  calc
    _ ≤ (K + 1 : ℝ) * ((Nat.clog 2 (K + 1) : ℝ) + 1) := hc
    _ ≤ (K + 1 : ℝ) * (4 * Real.log (2 * T)) := by gcongr
    _ ≤ 6 * K * Real.log (2 * T) := by nlinarith

private theorem init_nSamp_bound {T : ℕ} (hT : 2 ≤ T) (h : ℕ) :
    (nSamp T h : ℝ) ≤ 65537 * Real.log (2 * T) * (2 : ℝ) ^ h := by
  have hL := init_log_ge_one hT
  have hpow : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ (by norm_num)
  have hnonneg : 0 ≤ (2 : ℝ) ^ 16 * Real.log (2 * T) / delta h := by
    exact div_nonneg (mul_nonneg (by norm_num) (by linarith)) (init_delta_pos h).le
  have hc := (Nat.ceil_lt_add_one hnonneg).le
  change (nSamp T h : ℝ) ≤ _
  unfold nSamp
  rw [init_delta_inv_pow, div_inv_eq_mul] at hc ⊢
  norm_num only [show (2 : ℝ) ^ 16 = 65536 by norm_num] at hc ⊢
  nlinarith [mul_le_mul hL hpow (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ Real.log (2 * T))]

private theorem init_sum_pow_two (n : ℕ) :
    (∑ h ∈ Finset.range n, (2 : ℝ) ^ h) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

private theorem init_sample_sum_bound {T : ℕ} (hT : 2 ≤ T) (n : ℕ) :
    (∑ h ∈ Finset.range n, (nSamp T h : ℝ)) ≤
      65537 * Real.log (2 * T) * (2 : ℝ) ^ n := by
  calc
    _ ≤ ∑ h ∈ Finset.range n, 65537 * Real.log (2 * T) * (2 : ℝ) ^ h :=
      Finset.sum_le_sum (fun h _ => init_nSamp_bound hT h)
    _ = 65537 * Real.log (2 * T) * (2 ^ n - 1) := by
      rw [← Finset.mul_sum, init_sum_pow_two]
    _ ≤ _ := by nlinarith [init_log_ge_one hT]

private theorem init_rounds_trigger_bound {K T h : ℕ} (hK : 2 ≤ K) (hKT : K ≤ T)
    {ω : Samples K T} (hf : firstTrigger K T ω = some h) :
    (initRounds K T ω : ℝ) ≤ 786444 * K * Real.log (2 * T) ^ 2 / delta h := by
  have hT := hK.trans hKT
  have hsum := init_sample_sum_bound hT (h + 1)
  have hS := init_Spairs_real_bound hK hKT
  have hL := init_log_ge_one hT
  have hpow : (0 : ℝ) ≤ 2 ^ h := by positivity
  have hc : (initRounds K T ω : ℝ) = (Spairs K).card *
      (∑ j ∈ Finset.range (h + 1), (nSamp T j : ℝ)) := by
    simp only [initRounds, testedScales, hf, Nat.cast_sum, Nat.cast_mul, ← Finset.mul_sum]
  rw [hc, init_delta_inv_pow, div_inv_eq_mul, pow_succ] at *
  calc
    _ ≤ (Spairs K).card * (65537 * Real.log (2 * T) * (2 ^ h * 2)) := by gcongr
    _ ≤ (6 * K * Real.log (2 * T)) * (65537 * Real.log (2 * T) * (2 ^ h * 2)) := by gcongr
    _ = _ := by ring

private theorem init_rounds_all_bound {K T : ℕ} (hK : 2 ≤ K) (hKT : K ≤ T)
    (ω : Samples K T) :
    (initRounds K T ω : ℝ) ≤ 786444 * (K : ℝ) ^ 2 * Real.log (2 * T) ^ 2 := by
  have hT := hK.trans hKT
  have hL := init_log_ge_one hT
  have hS := init_Spairs_real_bound hK hKT
  have hsub : testedScales K T ω ⊆ Finset.range (numScales K) := by
    intro j hj
    exact Finset.mem_range.mpr (init_tested_lt hj)
  have hsum := init_sample_sum_bound hT (numScales K)
  have hp : (2 : ℝ) ^ numScales K ≤ 2 * K := by
    have hn := Nat.pow_log_le_self 2 (show K ≠ 0 by omega)
    have hr : (2 : ℝ) ^ Nat.log 2 K ≤ K := by exact_mod_cast hn
    unfold numScales
    rw [pow_succ]
    linarith
  have hc : (initRounds K T ω : ℝ) ≤ (Spairs K).card *
      (∑ j ∈ Finset.range (numScales K), (nSamp T j : ℝ)) := by
    rw [initRounds, Nat.cast_sum]
    simp only [Nat.cast_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  calc
    _ ≤ (Spairs K).card * (∑ j ∈ Finset.range (numScales K), (nSamp T j : ℝ)) := hc
    _ ≤ (6 * K * Real.log (2 * T)) * (65537 * Real.log (2 * T) * (2 * K)) := by
      apply mul_le_mul hS (hsum.trans ?_) (by positivity) (by positivity)
      gcongr
    _ = _ := by ring

private theorem init_Kpar_T_ge_two {c0 : ℝ} (hc0 : 0 < c0) (hc : c0 ≤ 1 / 2)
    {T : ℕ} (hK : 2 ≤ Kpar c0 T) : 2 ≤ T := by
  by_contra hn
  have ht : T = 0 ∨ T = 1 := by omega
  rcases ht with rfl | rfl
  · simp [Kpar] at hK
  · have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogp : 0 < Real.log 2 := by linarith
    have hx : c0 / Real.log 2 ≤ 1 := by
      apply (div_le_one hlogp).2
      linarith
    have hfloor : Kpar c0 1 ≤ 1 := by
      unfold Kpar
      simp only [Nat.cast_one, Real.sqrt_one, mul_one, mul_one]
      apply Nat.floor_le_of_le
      simpa using hx
    omega

private theorem init_Kpar_real_upper {c0 : ℝ} (hc0 : 0 < c0) {T : ℕ} (hT : 2 ≤ T) :
    (Kpar c0 T : ℝ) ≤ c0 * Real.sqrt T / Real.log (2 * T) := by
  unfold Kpar
  apply Nat.floor_le
  exact div_nonneg (mul_nonneg hc0.le (Real.sqrt_nonneg _)) (by linarith [init_log_ge_one hT])

private theorem init_Kpar_le_T {c0 : ℝ} (hc0 : 0 < c0) (hc : c0 ≤ 1 / 2) {T : ℕ}
    (hT : 2 ≤ T) : Kpar c0 T ≤ T := by
  have hL := init_log_ge_one hT
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hs : Real.sqrt (T : ℝ) ≤ T := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith
  have hx : c0 * Real.sqrt T / Real.log (2 * T) ≤ (T : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log (2 * T))).2
    nlinarith [mul_nonneg (Real.sqrt_nonneg (T : ℝ)) (show 0 ≤ 1 - c0 by linarith),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) T) (show 0 ≤ Real.log (2 * T) - 1 by linarith)]
  exact_mod_cast (init_Kpar_real_upper hc0 hT).trans hx

private theorem init_Kpar_real_lower {c0 : ℝ} {T : ℕ} (hK : 2 ≤ Kpar c0 T) :
    c0 * Real.sqrt T / Real.log (2 * T) ≤ 2 * (Kpar c0 T : ℝ) := by
  have hx := Nat.lt_floor_add_one (c0 * Real.sqrt T / Real.log (2 * T))
  have hKr : (2 : ℝ) ≤ Kpar c0 T := by exact_mod_cast hK
  change c0 * Real.sqrt T / Real.log (2 * T) < (Kpar c0 T : ℝ) + 1 at hx
  linarith

private theorem init_Kpar_rounds {T : ℕ} (hK : 2 ≤ Kpar (1 / 1048576) T)
    (ω : Samples (Kpar (1 / 1048576) T) T) :
    initRounds (Kpar (1 / 1048576) T) T ω ≤ T := by
  have hT := init_Kpar_T_ge_two (c0 := 1 / 1048576) (by norm_num) (by norm_num) hK
  have hKT := init_Kpar_le_T (c0 := 1 / 1048576) (by norm_num) (by norm_num) hT
  have hr := init_rounds_all_bound hK hKT ω
  have hu := init_Kpar_real_upper (c0 := 1 / 1048576) (by norm_num) hT
  have hL := init_log_ge_one hT
  have hmul := (le_div_iff₀ (by linarith : 0 < Real.log (2 * T))).mp hu
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) T)
  have hpow : (Kpar (1 / 1048576) T : ℝ) ^ 2 * Real.log (2 * T) ^ 2 ≤
      (1 / 1048576 : ℝ) ^ 2 * T := by
    have hsq := (sq_le_sq₀ (show 0 ≤ (Kpar (1 / 1048576) T : ℝ) * Real.log (2 * T) by positivity)
      (show 0 ≤ (1 / 1048576 : ℝ) * Real.sqrt T by positivity)).mpr hmul
    simpa only [mul_pow, hs] using hsq
  have hrr : (initRounds (Kpar (1 / 1048576) T) T ω : ℝ) ≤ T := by
    nlinarith [Nat.cast_nonneg (α := ℝ) T]
  exact_mod_cast hrr

end BilateralProfitMHR
end BundlePart006


section BundlePart007



set_option autoImplicit false

/-- A finite decision tree whose internal nodes query one coordinate and branch on its bit. -/
private inductive ProbeTree (I R : Type) where
  | leaf (value : R) : ProbeTree I R
  | node (index : I) (no yes : ProbeTree I R) : ProbeTree I R

namespace ProbeTree

private def eval {I R : Type} : ProbeTree I R → (I → Bool) → List I × R
  | leaf r, _ => ([], r)
  | node i no yes, bits =>
      let next := if bits i then eval yes bits else eval no bits
      (i :: next.1, next.2)

private def ValidSeen {I R : Type} [DecidableEq I] (seen : Finset I) : ProbeTree I R → Prop
  | leaf _ => True
  | node i no yes => i ∉ seen ∧ ValidSeen (insert i seen) no ∧ ValidSeen (insert i seen) yes

private def fillBits {I : Type} [DecidableEq I] (read : List I) (acc bits : I → Bool) : I → Bool :=
  fun i => if i ∈ read then bits i else acc i

private theorem fillBits_nil {I : Type} [DecidableEq I] (acc bits : I → Bool) :
    fillBits [] acc bits = acc := by
  funext i
  simp [fillBits]

private theorem fillBits_cons {I : Type} [DecidableEq I] (i : I) (read : List I) (acc bits : I → Bool) :
    fillBits (i :: read) acc bits = fillBits read (Function.update acc i (bits i)) bits := by
  funext j
  by_cases hj : j ∈ read <;> by_cases hji : j = i <;> simp [fillBits, hj, hji]

private def readBlock {I R : Type} [DecidableEq I] :
    List I → (I → Bool) → ((I → Bool) → ProbeTree I R) → ProbeTree I R
  | [], acc, cont => cont acc
  | i :: rest, acc, cont =>
      node i (readBlock rest (Function.update acc i false) cont)
        (readBlock rest (Function.update acc i true) cont)

private theorem readBlock_eval {I R : Type} [DecidableEq I] (read : List I) (acc bits : I → Bool)
    (cont : (I → Bool) → ProbeTree I R) :
    eval (readBlock read acc cont) bits =
      let next := eval (cont (fillBits read acc bits)) bits
      (read ++ next.1, next.2) := by
  induction read generalizing acc with
  | nil => simp [readBlock, fillBits_nil]
  | cons i rest ih =>
    rw [readBlock, eval]
    have hfill := fillBits_cons i rest acc bits
    cases hb : bits i <;>
      simp only [hb] at hfill ⊢ <;>
      simp only [Bool.false_eq_true, ↓reduceIte, ih, hfill, List.cons_append]

private theorem readBlock_valid {I R : Type} [DecidableEq I] (seen : Finset I) (read : List I)
    (acc : I → Bool) (cont : (I → Bool) → ProbeTree I R)
    (hn : read.Nodup) (hfresh : ∀ i ∈ read, i ∉ seen)
    (hc : ∀ acc', ValidSeen (seen ∪ read.toFinset) (cont acc')) :
    ValidSeen seen (readBlock read acc cont) := by
  induction read generalizing seen acc with
  | nil => simpa [readBlock] using hc acc
  | cons i rest ih =>
    obtain ⟨hi, hn⟩ := List.nodup_cons.mp hn
    have hifresh := hfresh i (by simp)
    have hrestfresh : ∀ j ∈ rest, j ∉ insert i seen := by
      intro j hj
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun he => hi (he ▸ hj), hfresh j (List.mem_cons_of_mem i hj)⟩
    have hset : insert i seen ∪ rest.toFinset = seen ∪ (i :: rest).toFinset := by
      ext j
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      tauto
    have hcont : ∀ acc', ValidSeen (insert i seen ∪ rest.toFinset) (cont acc') := by
      intro acc'
      rw [hset]
      exact hc acc'
    exact ⟨hifresh, ih _ _ hn hrestfresh hcont, ih _ _ hn hrestfresh hcont⟩

end ProbeTree

namespace BilateralProfitMHR

open BilateralProfit
open scoped Classical

private abbrev InitTreeResult := ℕ × Option (ℕ × Set (ℝ × ℝ))

/-- Build the initializer tree by reading each complete scale before testing its trigger. -/
private noncomputable def initBuildStages (K T : ℕ) : List (Fin (numScales K)) →
    (SampleIdx K T → Bool) → ℕ → ProbeTree (SampleIdx K T) InitTreeResult
  | [], _, spent => .leaf (spent, none)
  | h :: rest, acc, spent =>
      ProbeTree.readBlock (initScaleSchedule h) acc fun acc' =>
        let spent' := spent + (initScaleSchedule (T := T) h).length
        if Triggers K T h (initDecodeBits acc') then
          .leaf (spent', some (h, region K T h (initDecodeBits acc')))
        else initBuildStages K T rest acc' spent'

/-- The deterministic path obtained by supplying one fixed sample array. -/
private noncomputable def initStagePath (K T : ℕ) : List (Fin (numScales K)) →
    ℕ → Samples K T → List (SampleIdx K T) × InitTreeResult
  | [], spent, _ => ([], (spent, none))
  | h :: rest, spent, ω =>
      let block := initScaleSchedule (T := T) h
      let spent' := spent + block.length
      if Triggers K T h ω then
        (block, (spent', some (h, region K T h ω)))
      else
        let next := initStagePath K T rest spent' ω
        (block ++ next.1, next.2)

private noncomputable def initTree (K T : ℕ) : ProbeTree (SampleIdx K T) InitTreeResult :=
  initBuildStages K T (List.ofFn fun h : Fin (numScales K) => h) (fun _ => false) 0

private def InitBitsRepresent {K T : ℕ} (bits : SampleIdx K T → Bool) (ω : Samples K T) : Prop :=
  ∀ (h : Fin (numScales K)) (z : InitProbe K T h),
    bits (initProbeEmbed h z) = initReadBits ω (initProbeEmbed h z)

private theorem init_filled_scale_same {K T : ℕ} (hK : 0 < K) (h : Fin (numScales K))
    (acc bits : SampleIdx K T → Bool) (ω : Samples K T) (hb : InitBitsRepresent bits ω) :
    (∀ e : Act K, muHat K T h (initDecodeBits
        (ProbeTree.fillBits (initScaleSchedule h) acc bits)) e = muHat K T h ω e) ∧
      region K T h (initDecodeBits (ProbeTree.fillBits (initScaleSchedule h) acc bits)) = region K T h ω := by
  have hs : ∀ z : InitProbe K T h,
      tradeBit (ω (initProbeEmbed h z)) ((z.1.1.1 : ℝ) / K, (z.1.1.2 : ℝ) / K) =
        tradeBit (initDecodeBits (ProbeTree.fillBits (initScaleSchedule h) acc bits) (initProbeEmbed h z))
          ((z.1.1.1 : ℝ) / K, (z.1.1.2 : ℝ) / K) := by
    intro z
    have hm : initProbeEmbed h z ∈ initScaleSchedule h :=
      (initScaleSchedule_mem_iff h _).mpr ⟨z, rfl⟩
    change _ = tradeBit (initBitValuation
      (ProbeTree.fillBits (initScaleSchedule h) acc bits (initProbeEmbed h z))) _
    rw [ProbeTree.fillBits, if_pos hm, hb h z]
    exact init_read_decode_same_probe_bits hK ω h z
  have hmu : ∀ e : Act K, muHat K T h ω e = muHat K T h
      (initDecodeBits (ProbeTree.fillBits (initScaleSchedule h) acc bits)) e := by
    apply init_muHat_eq_of_Pbar_eq
    intro z hz
    exact init_Pbar_eq_of_same_scale_bits h.isLt hs hz
  refine ⟨fun e => (hmu e).symm, ?_⟩
  unfold region
  simp_rw [← hmu]

private theorem initBuildStages_eval {K T : ℕ} (hK : 0 < K) (stages : List (Fin (numScales K)))
    (acc bits : SampleIdx K T → Bool) (spent : ℕ) (ω : Samples K T)
    (hb : InitBitsRepresent bits ω) :
    ProbeTree.eval (initBuildStages K T stages acc spent) bits = initStagePath K T stages spent ω := by
  induction stages generalizing acc spent with
  | nil => rfl
  | cons h rest ih =>
    rw [initBuildStages, ProbeTree.readBlock_eval]
    have heq := init_filled_scale_same hK h acc bits ω hb
    have ht : Triggers K T h (initDecodeBits (ProbeTree.fillBits (initScaleSchedule h) acc bits)) ↔
        Triggers K T h ω := by
      unfold Triggers
      simp_rw [heq.1]
    by_cases htr : Triggers K T h ω
    · simp only [ht.mpr htr, ↓reduceIte, ProbeTree.eval, List.append_nil, initStagePath,
        htr, heq.2]
    · simp only [not_congr ht |>.mpr htr, ↓reduceIte, ih, initStagePath, htr]

private theorem initBuildStages_valid {K T : ℕ} (stages : List (Fin (numScales K)))
    (seen : Finset (SampleIdx K T)) (acc : SampleIdx K T → Bool) (spent : ℕ)
    (hn : (stages.flatMap (initScaleSchedule (T := T))).Nodup)
    (hfresh : ∀ i ∈ stages.flatMap (initScaleSchedule (T := T)), i ∉ seen) :
    ProbeTree.ValidSeen seen (initBuildStages K T stages acc spent) := by
  induction stages generalizing seen acc spent with
  | nil => trivial
  | cons h rest ih =>
    have hn' : ((initScaleSchedule (T := T) h) ++ rest.flatMap (initScaleSchedule (T := T))).Nodup := by
      simpa only [List.flatMap_cons] using hn
    obtain ⟨hblock, hrest, hdisj⟩ := List.nodup_append.mp hn'
    apply ProbeTree.readBlock_valid seen _ acc _ hblock
    · intro i hi
      exact hfresh i (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inl hi)
    · intro acc'
      dsimp
      split_ifs
      · trivial
      · apply ih _ _ _ hrest
        intro i hi
        simp only [Finset.mem_union, List.mem_toFinset, not_or]
        constructor
        · exact hfresh i (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr hi)
        · intro hib
          exact hdisj i hib i hi rfl

private theorem initStagePath_spent {K T : ℕ} (stages : List (Fin (numScales K)))
    (spent : ℕ) (ω : Samples K T) :
    (initStagePath K T stages spent ω).2.1 = spent + (initStagePath K T stages spent ω).1.length := by
  induction stages generalizing spent with
  | nil => simp [initStagePath]
  | cons h rest ih =>
    unfold initStagePath
    split_ifs
    · rfl
    · simp only [List.length_append]
      rw [ih]
      omega

private theorem initStagePath_append {K T : ℕ} (before after : List (Fin (numScales K)))
    (spent : ℕ) (ω : Samples K T)
    (hn : ∀ h ∈ before, ¬ Triggers K T h ω) :
    initStagePath K T (before ++ after) spent ω =
      let read := before.flatMap (initScaleSchedule (T := T))
      let next := initStagePath K T after (spent + read.length) ω
      (read ++ next.1, next.2) := by
  induction before generalizing spent with
  | nil => simp [initStagePath]
  | cons h rest ih =>
    have hnt := hn h (by simp)
    have hnr : ∀ j ∈ rest, ¬ Triggers K T j ω := fun j hj => hn j (List.mem_cons_of_mem h hj)
    simp only [List.cons_append, initStagePath, hnt, ↓reduceIte, ih _ hnr,
      List.flatMap_cons, List.length_append, Nat.add_assoc, List.append_assoc]

/-- Consecutive scale indices beginning at `h`. -/
private def initStageIndices (K h f : ℕ) (hb : h + f ≤ numScales K) : List (Fin (numScales K)) :=
  List.ofFn fun i : Fin f => ⟨h + i, by omega⟩

private theorem initStageIndices_append (K h a b : ℕ) (hb : h + (a + b) ≤ numScales K) :
    initStageIndices K h (a + b) hb = initStageIndices K h a (by omega) ++
      initStageIndices K (h + a) b (by omega) := by
  unfold initStageIndices
  rw [List.ofFn_add]
  apply congrArg₂ List.append
  · apply congrArg List.ofFn
    funext i
    apply Fin.ext
    rfl
  · apply congrArg List.ofFn
    funext i
    apply Fin.ext
    simp [Nat.add_assoc]

private theorem initStageIndices_succ (K h f : ℕ) (hb : h + (f + 1) ≤ numScales K) :
    initStageIndices K h (f + 1) hb =
      ⟨h, by omega⟩ :: initStageIndices K (h + 1) f (by omega) := by
  unfold initStageIndices
  rw [List.ofFn_succ]
  apply congrArg₂ List.cons
  · apply Fin.ext
    simp
  · apply congrArg List.ofFn
    funext i
    apply Fin.ext
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem initStageIndices_one (K h : ℕ) (hb : h + 1 ≤ numScales K) :
    initStageIndices K h 1 hb = [⟨h, by omega⟩] := by
  simp [initStageIndices]

private theorem initStageIndices_mem {K h f : ℕ} {hb : h + f ≤ numScales K}
    {j : Fin (numScales K)} (hj : j ∈ initStageIndices K h f hb) : h ≤ (j : ℕ) ∧ (j : ℕ) < h + f := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
  change h ≤ h + i ∧ h + i < h + f
  omega

private theorem initStageIndices_zero_reads (K T f : ℕ) (hb : f ≤ numScales K) :
    (initStageIndices K 0 f (by omega)).flatMap (initScaleSchedule (T := T)) =
      initPrefixSchedule K T f hb := by
  simp [initStageIndices, List.flatMap, List.map_ofFn, initPrefixSchedule, Function.comp_def]

private theorem initTree_valid (K T : ℕ) : ProbeTree.ValidSeen ∅ (initTree K T) := by
  apply initBuildStages_valid
  · have hn := initPrefixSchedule_nodup K T (numScales K) le_rfl
    simpa [initPrefixSchedule, List.flatMap, List.map_ofFn, Function.comp_def] using hn
  · intro i hi
    simp

private theorem initStagePath_complete (K T : ℕ) (ω : Samples K T) :
    initStagePath K T (List.ofFn fun h : Fin (numScales K) => h) 0 ω =
      (initRunSchedule K T ω, (initRounds K T ω, initOut K T ω)) := by
  cases hf : firstTrigger K T ω with
  | none =>
    have hn : ∀ h ∈ (List.ofFn fun h : Fin (numScales K) => h), ¬ Triggers K T h ω := by
      intro h hh
      exact init_firstTrigger_none.mp hf h h.isLt
    have he := initStagePath_append (K := K) (T := T)
      (List.ofFn fun h : Fin (numScales K) => h) [] 0 ω hn
    have hread : (List.ofFn fun h : Fin (numScales K) => h).flatMap (initScaleSchedule (T := T)) =
        initRunSchedule K T ω := by
      unfold initRunSchedule
      split
      · rename_i g hfg
        rw [hf] at hfg
        contradiction
      · simp [initPrefixSchedule, List.flatMap, List.map_ofFn, Function.comp_def]
    have hout : initOut K T ω = none := initOut_none.mpr hf
    simpa only [List.append_nil, initStagePath, Nat.zero_add, hread, initRunSchedule_length,
      hout] using he
  | some g =>
    obtain ⟨hg, htr, hprev⟩ := init_firstTrigger_spec hf
    let before := initStageIndices K 0 g (by omega)
    let after := initStageIndices K g (numScales K - g) (by omega)
    have hfull : (List.ofFn fun h : Fin (numScales K) => h) = before ++ after := by
      have he := initStageIndices_append K 0 g (numScales K - g) (by omega)
      have hsum : g + (numScales K - g) = numScales K := by omega
      simpa [hsum, initStageIndices, Nat.zero_add, before, after] using he
    have hafter : after = ⟨g, hg⟩ ::
        initStageIndices K (g + 1) (numScales K - (g + 1)) (by omega) := by
      have he := initStageIndices_succ K g (numScales K - (g + 1)) (by omega)
      have hsize : (numScales K - (g + 1)) + 1 = numScales K - g := by omega
      simpa only [hsize, after] using he
    have hn : ∀ h ∈ before, ¬ Triggers K T h ω := by
      intro h hh
      have hlt := (initStageIndices_mem hh).2
      exact hprev h (by simpa using hlt)
    have hread : before.flatMap (initScaleSchedule (T := T)) ++ initScaleSchedule (T := T) ⟨g, hg⟩ =
        initPrefixSchedule K T (g + 1) (by omega) := by
      have he := congrArg (fun l => l.flatMap (initScaleSchedule (T := T)))
        (initStageIndices_append K 0 g 1 (by omega))
      rw [initStageIndices_zero_reads, List.flatMap_append, initStageIndices_one,
        List.flatMap_cons, List.flatMap_nil, List.append_nil] at he
      simpa only [Nat.zero_add, before] using he.symm
    have hrun : initRunSchedule K T ω = initPrefixSchedule K T (g + 1) (by omega) := by
      unfold initRunSchedule
      split
      · rename_i j hj
        have heq : j = g := Option.some.inj (hj.symm.trans hf)
        subst j
        rfl
      · rename_i hn
        rw [hf] at hn
        contradiction
    have hout : initOut K T ω = some (g, region K T g ω) := by simp [initOut, hf]
    rw [hfull, initStagePath_append before after 0 ω hn, hafter]
    simp only [initStagePath, htr, ↓reduceIte, Nat.zero_add]
    rw [← List.length_append, hread, ← hrun, initRunSchedule_length, hout]

private theorem initTree_eval {K T : ℕ} (hK : 0 < K) (ω : Samples K T) :
    ProbeTree.eval (initTree K T) (initReadBits ω) =
      (initRunSchedule K T ω, (initRounds K T ω, initOut K T ω)) := by
  rw [initTree, initBuildStages_eval hK _ _ _ _ ω (fun _ _ => rfl)]
  exact initStagePath_complete K T ω

private theorem initBitValuation_decide (a : ℝ × ℝ) (ha : a ∈ unitSq) (horder : a.1 ≤ a.2)
    (b : Bool) : decide (Trades (initBitValuation b) a) = b := by
  cases b with
  | false =>
    have ht : ¬ Trades (1, 0) a := by
      rintro ⟨h1, h2⟩
      change 1 ≤ a.1 at h1
      change a.2 ≤ 0 at h2
      linarith
    simp [initBitValuation, ht]
  | true =>
    have ht : Trades (0, 1) a := ⟨ha.1.1, ha.2.2⟩
    simp [initBitValuation, ht]

private theorem initBitsRepresent_decode {K T : ℕ} (hK : 0 < K) (bits : SampleIdx K T → Bool) :
    InitBitsRepresent bits (initDecodeBits bits) := by
  intro h z
  unfold initReadBits initDecodeBits
  exact (initBitValuation_decide _ (initSamplePrice_mem_unitSq hK _)
    (initProbeEmbed_price_ordered h z) _).symm

private theorem initTree_eval_bits {K T : ℕ} (hK : 0 < K) (bits : SampleIdx K T → Bool) :
    ProbeTree.eval (initTree K T) bits =
      (initRunSchedule K T (initDecodeBits bits),
        (initRounds K T (initDecodeBits bits), initOut K T (initDecodeBits bits))) := by
  rw [initTree, initBuildStages_eval hK _ _ _ _ (initDecodeBits bits) (initBitsRepresent_decode hK bits)]
  exact initStagePath_complete K T _

private theorem initTree_eval_length {K T : ℕ} (hK : 0 < K) (bits : SampleIdx K T → Bool) :
    (ProbeTree.eval (initTree K T) bits).1.length = (ProbeTree.eval (initTree K T) bits).2.1 := by
  rw [initTree_eval_bits hK]
  exact initRunSchedule_length _ _ _

private theorem initTree_rounds_bound {T : ℕ} (hK : 2 ≤ Kpar (1 / 1048576) T)
    (bits : SampleIdx (Kpar (1 / 1048576) T) T → Bool) :
    (ProbeTree.eval (initTree (Kpar (1 / 1048576) T) T) bits).2.1 ≤ T := by
  rw [initTree_eval_bits (by omega : 0 < Kpar (1 / 1048576) T)]
  exact init_Kpar_rounds hK _

private theorem initTree_output_geometry {K T : ℕ} (hK : 0 < K) (bits : SampleIdx K T → Bool)
    (h : ℕ) (R : Set (ℝ × ℝ))
    (ho : (ProbeTree.eval (initTree K T) bits).2.2 = some (h, R)) :
    h < numScales K ∧ R.Nonempty ∧ IsCompact R ∧ Convex ℝ R ∧ R ⊆ intT := by
  rw [initTree_eval_bits hK] at ho
  obtain ⟨hf, rfl⟩ := initOut_some ho
  have ht := init_firstTrigger_spec hf
  exact ⟨ht.1, init_region_geometry hK _ ht.2.1⟩

end BilateralProfitMHR

namespace ProbeTree

private def LeafProperty {I R : Type} (P : R → Prop) : ProbeTree I R → Prop
  | leaf r => P r
  | node _ no yes => LeafProperty P no ∧ LeafProperty P yes

private theorem eval_eq_of_eq_off_seen {I R : Type} [DecidableEq I] (seen : Finset I)
    (tree : ProbeTree I R) (hv : ValidSeen seen tree) (bits bits' : I → Bool)
    (hb : ∀ i, i ∉ seen → bits i = bits' i) : eval tree bits = eval tree bits' := by
  induction tree generalizing seen with
  | leaf r => rfl
  | node i no yes ihno ihyes =>
    obtain ⟨hi, hno, hyes⟩ := hv
    have he := hb i hi
    simp only [eval, he]
    have hchild : ∀ j, j ∉ insert i seen → bits j = bits' j := by
      intro j hj
      exact hb j (fun hs => hj (Finset.mem_insert_of_mem hs))
    cases bits' i <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [ihno _ hno hchild]
    · rw [ihyes _ hyes hchild]

private theorem leafProperty_of_eval {I R : Type} [DecidableEq I] (seen : Finset I)
    (tree : ProbeTree I R) (hv : ValidSeen seen tree) (P : R → Prop)
    (hP : ∀ bits : I → Bool, P (eval tree bits).2) : LeafProperty P tree := by
  induction tree generalizing seen with
  | leaf r => exact hP (fun _ => false)
  | node i no yes ihno ihyes =>
    obtain ⟨hi, hno, hyes⟩ := hv
    constructor
    · apply ihno _ hno
      intro bits
      have he := eval_eq_of_eq_off_seen (insert i seen) no hno bits
        (Function.update bits i false) (fun j hj => by
          have hji : j ≠ i := fun he => hj (he ▸ Finset.mem_insert_self i seen)
          simp [Function.update_of_ne hji])
      have hp := hP (Function.update bits i false)
      simpa only [eval, Function.update_self, Bool.false_eq_true, ↓reduceIte, ← he] using hp
    · apply ihyes _ hyes
      intro bits
      have he := eval_eq_of_eq_off_seen (insert i seen) yes hyes bits
        (Function.update bits i true) (fun j hj => by
          have hji : j ≠ i := fun he => hj (he ▸ Finset.mem_insert_self i seen)
          simp [Function.update_of_ne hji])
      have hp := hP (Function.update bits i true)
      simpa only [eval, Function.update_self, ↓reduceIte, ← he] using hp

end ProbeTree

namespace BilateralProfitMHR

private theorem initTree_leaf_rounds_bound {T : ℕ} (hK : 2 ≤ Kpar (1 / 1048576) T) :
    ProbeTree.LeafProperty (fun r : InitTreeResult => r.1 ≤ T)
      (initTree (Kpar (1 / 1048576) T) T) := by
  apply ProbeTree.leafProperty_of_eval ∅ _ (initTree_valid _ _)
  exact initTree_rounds_bound hK

private theorem initTree_leaf_geometry {K T : ℕ} (hK : 0 < K) :
    ProbeTree.LeafProperty (fun r : InitTreeResult => ∀ (h : ℕ) (R : Set (ℝ × ℝ)),
      r.2 = some (h, R) → h < numScales K ∧ R.Nonempty ∧ IsCompact R ∧ Convex ℝ R ∧ R ⊆ intT)
      (initTree K T) := by
  apply ProbeTree.leafProperty_of_eval ∅ _ (initTree_valid _ _)
  intro bits h R ho
  exact initTree_output_geometry hK bits h R ho

end BilateralProfitMHR
end BundlePart007


section BundlePart008




noncomputable section

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit Set
open scoped ENNReal

private theorem binaryValue_mono {X S : Type} (q : X → ℝ) {g h : X → ℝ≥0∞}
    (act : S → X) (step : S → Bool → S) (hgh : ∀ s, g (act s) ≤ h (act s))
    (n : ℕ) (s : S) :
    binaryValue q g act step n s ≤ binaryValue q h act step n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [binaryValue]
    gcongr <;> first | exact hgh s | apply ih

private theorem binaryValue_le_linear {X S : Type} (q : X → ℝ) (g : X → ℝ≥0∞)
    (act : S → X) (step : S → Bool → S) (B : ℝ≥0∞)
    (hq : ∀ s, q (act s) ∈ Icc 0 1) (hg : ∀ s, g (act s) ≤ B) (n : ℕ) (s : S) :
    binaryValue q g act step n s ≤ (n : ℝ≥0∞) * B := by
  induction n generalizing s with
  | zero => simp [binaryValue]
  | succ n ih =>
    have hs : ENNReal.ofReal (q (act s)) + ENNReal.ofReal (1 - q (act s)) = 1 := by
      rw [← ENNReal.ofReal_add (hq s).1 (sub_nonneg.mpr (hq s).2)]
      simp
    simp only [binaryValue]
    calc
      _ ≤ B + (ENNReal.ofReal (q (act s)) * ((n : ℝ≥0∞) * B) +
        ENNReal.ofReal (1 - q (act s)) * ((n : ℝ≥0∞) * B)) := by
          gcongr <;> first | exact hg s | apply ih
      _ = _ := by rw [← add_mul, hs, one_mul, Nat.cast_succ, add_mul, one_mul, add_comm]

private theorem binaryValue_le_add {X S : Type} (q : X → ℝ) (g h : X → ℝ≥0∞)
    (act : S → X) (step : S → Bool → S) (B : ℝ≥0∞)
    (hq : ∀ s, q (act s) ∈ Icc 0 1) (hg : ∀ s, g (act s) ≤ h (act s) + B)
    (n : ℕ) (s : S) :
    binaryValue q g act step n s ≤ binaryValue q h act step n s + (n : ℝ≥0∞) * B := by
  induction n generalizing s with
  | zero => simp [binaryValue]
  | succ n ih =>
    have hs : ENNReal.ofReal (q (act s)) + ENNReal.ofReal (1 - q (act s)) = 1 := by
      rw [← ENNReal.ofReal_add (hq s).1 (sub_nonneg.mpr (hq s).2)]
      simp
    simp only [binaryValue]
    calc
      _ ≤ h (act s) + B + (ENNReal.ofReal (q (act s)) *
          (binaryValue q h act step n (step s true) + (n : ℝ≥0∞)*B) +
        ENNReal.ofReal (1 - q (act s)) *
          (binaryValue q h act step n (step s false) + (n : ℝ≥0∞)*B)) := by
          gcongr <;> first | exact hg s | apply ih
      _ = h (act s) + (ENNReal.ofReal (q (act s)) * binaryValue q h act step n (step s true) +
          ENNReal.ofReal (1 - q (act s)) * binaryValue q h act step n (step s false)) +
        (B + (ENNReal.ofReal (q (act s)) + ENNReal.ofReal (1 - q (act s))) *
          ((n : ℝ≥0∞)*B)) := by ring
      _ = _ := by rw [hs, one_mul, Nat.cast_succ, add_mul, one_mul, add_comm B]

/-- A waiting block stores the completed observations and the failures in the current query. -/
private structure WaitState where
  completed : ℕ
  observations : Fin completed → ℝ
  failures : ℕ

variable {Ω : Type} [MeasurableSpace Ω]

private def waitPrice (A : QueryAlg (ℝ × ℝ) Ω) (ω : Ω) (s : WaitState) : ℝ × ℝ :=
  A.query s.completed ω s.observations

private def waitObservation (x : ℝ × ℝ) (k : ℕ) : ℝ := harm k - Real.log (x.2 - x.1)

private def waitNext (A : QueryAlg (ℝ × ℝ) Ω) (ω : Ω) (s : WaitState) (b : Bool) : WaitState :=
  if b then
    ⟨s.completed + 1, Fin.snoc s.observations (waitObservation (waitPrice A ω s) s.failures), 0⟩
  else ⟨s.completed, s.observations, s.failures + 1⟩

private def waitEmpty : WaitState := ⟨0, Fin.elim0, 0⟩

private def oracleKernel (D : Measure (ℝ × ℝ)) : ObsKernel (ℝ × ℝ) :=
  fun _ _ _ x => oracleLaw D x

private theorem lintegral_oracle_series (D : Measure (ℝ × ℝ)) (x : ℝ × ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ z, F z ∂oracleLaw D x =
      ∑' k : ℕ, ENNReal.ofReal ((1 - Ptrade D x)^k * Ptrade D x) * F (waitObservation x k) := by
  have hm : Measurable (fun N : ℕ => harm (N - 1) - Real.log (x.2 - x.1)) :=
    measurable_of_countable _
  unfold oracleLaw geomLaw
  rw [Measure.map_sum hm.aemeasurable, lintegral_sum_measure]
  apply tsum_congr
  intro k
  rw [Measure.map_smul, Measure.map_dirac' hm, lintegral_smul_measure, lintegral_dirac]
  simp [waitObservation, smul_eq_mul]

private def waitFullCost (D : Measure (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ≥0∞)
    (A : QueryAlg (ℝ × ℝ) Ω) (ω : Ω) (m : ℕ) (s : WaitState) : ℝ≥0∞ :=
  let x := waitPrice A ω s
  let weighted := fun a => g a / ENNReal.ofReal (Ptrade D a)
  match m with
  | 0 => 0
  | m + 1 => weighted x +
      ∑' j : ℕ, ENNReal.ofReal ((1 - Ptrade D x)^j * Ptrade D x) *
        cumLoss A (oracleKernel D) weighted ω m (s.completed+1)
          (Fin.snoc s.observations (waitObservation x (s.failures+j)))

private theorem waitFullCost_fresh (D : Measure (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ≥0∞)
    (A : QueryAlg (ℝ × ℝ) Ω) (ω : Ω) (m τ : ℕ) (y : Fin τ → ℝ) :
    waitFullCost D g A ω m ⟨τ,y,0⟩ =
      cumLoss A (oracleKernel D) (fun a => g a / ENNReal.ofReal (Ptrade D a)) ω m τ y := by
  cases m with
  | zero => rfl
  | succ m =>
    simp only [waitFullCost, waitPrice, cumLoss, oracleKernel, lintegral_oracle_series, zero_add]

private theorem waitFullCost_step (D : Measure (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ≥0∞)
    (A : QueryAlg (ℝ × ℝ) Ω) (ω : Ω) (m : ℕ) (s : WaitState)
    (hp : 0 < Ptrade D (waitPrice A ω s)) (hq : Ptrade D (waitPrice A ω s) ≤ 1) :
    waitFullCost D g A ω (m+1) s =
      g (waitPrice A ω s) +
        (ENNReal.ofReal (Ptrade D (waitPrice A ω s)) * waitFullCost D g A ω m (waitNext A ω s true) +
         ENNReal.ofReal (1 - Ptrade D (waitPrice A ω s)) *
           waitFullCost D g A ω (m+1) (waitNext A ω s false)) := by
  let p := Ptrade D (waitPrice A ω s)
  let v := g (waitPrice A ω s) / ENNReal.ofReal p
  have hs : ENNReal.ofReal p + ENNReal.ofReal (1-p) = 1 := by
    rw [← ENNReal.ofReal_add hp.le (sub_nonneg.mpr hq)]
    simp
  have hg : ENNReal.ofReal p * v = g (waitPrice A ω s) := by
    dsimp [v]
    rw [mul_comm, ENNReal.div_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top]
  have hv : v = g (waitPrice A ω s) + ENNReal.ofReal (1-p) * v := by
    rw [← hg, ← add_mul, hs, one_mul]
  have htrue : waitFullCost D g A ω m (waitNext A ω s true) =
      cumLoss A (oracleKernel D) (fun a => g a / ENNReal.ofReal (Ptrade D a)) ω m
        (s.completed+1) (Fin.snoc s.observations (waitObservation (waitPrice A ω s) s.failures)) := by
    simp only [waitNext, if_true]
    exact waitFullCost_fresh D g A ω m _ _
  let f (j : ℕ) := ENNReal.ofReal ((1-p)^j*p) *
        cumLoss A (oracleKernel D) (fun a => g a / ENNReal.ofReal (Ptrade D a)) ω m
          (s.completed+1) (Fin.snoc s.observations (waitObservation (waitPrice A ω s) (s.failures+j)))
  have hshift (j : ℕ) : f (j+1) = ENNReal.ofReal (1-p) *
      (ENNReal.ofReal ((1-p)^j*p) *
        cumLoss A (oracleKernel D) (fun a => g a / ENNReal.ofReal (Ptrade D a)) ω m
          (s.completed+1) (Fin.snoc s.observations (waitObservation (waitPrice A ω s) (s.failures+1+j)))) := by
    have h1 : 0 ≤ 1 - p := sub_nonneg.mpr hq
    rw [show s.failures + 1 + j = s.failures + (j+1) by omega]
    dsimp [f]
    rw [← mul_assoc, ← ENNReal.ofReal_mul h1]
    congr 2
    ring
  change v + (∑' j, f j) = _
  rw [tsum_eq_zero_add' ENNReal.summable, htrue]
  simp only [f, pow_zero, one_mul, add_zero]
  change v + (ENNReal.ofReal p *
      cumLoss A (oracleKernel D) (fun a => g a / ENNReal.ofReal (Ptrade D a)) ω m
        (s.completed+1) (Fin.snoc s.observations (waitObservation (waitPrice A ω s) s.failures)) +
      ∑' j : ℕ, f (j+1)) = _
  simp only [hshift, ENNReal.tsum_mul_left, waitNext, Bool.false_eq_true, if_false]
  let F (j : ℕ) :=
    cumLoss A (oracleKernel D) (fun a => g a / ENNReal.ofReal (Ptrade D a)) ω m
      (s.completed+1) (Fin.snoc s.observations (waitObservation (waitPrice A ω s) j))
  let Z := ∑' j : ℕ, ENNReal.ofReal ((1-p)^j*p) * F (s.failures+1+j)
  let B := ENNReal.ofReal p * F s.failures
  change v + (B + ENNReal.ofReal (1-p) * Z) =
    g (waitPrice A ω s) + (B + ENNReal.ofReal (1-p) * (v + Z))
  calc
    _ = (g (waitPrice A ω s) + ENNReal.ofReal (1-p)*v) + (B + ENNReal.ofReal (1-p)*Z) :=
      congrArg (fun w => w + (B + ENNReal.ofReal (1-p)*Z)) hv
    _ = _ := by rw [mul_add]; ac_rfl

/-- Cutting a physical run off after `b` rounds costs at most the full cost
of `m` geometric blocks when `b ≤ m`. -/
private theorem waitValue_le_full (D : Measure (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ≥0∞)
    (A : QueryAlg (ℝ × ℝ) Ω) (ω : Ω)
    (hprob : ∀ s : WaitState, 0 < Ptrade D (waitPrice A ω s) ∧ Ptrade D (waitPrice A ω s) ≤ 1)
    (b m : ℕ) (hbm : b ≤ m) (s : WaitState) :
    binaryValue (Ptrade D) g (waitPrice A ω) (waitNext A ω) b s ≤ waitFullCost D g A ω m s := by
  induction b generalizing m s with
  | zero => simp [binaryValue]
  | succ b ih =>
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    rw [waitFullCost_step D g A ω m s (hprob s).1 (hprob s).2]
    simp only [binaryValue]
    gcongr
    · exact ih m (by omega) _
    · exact ih (m+1) (by omega) _

private theorem cumLoss_le_mul_on {X : Type} [MeasurableSpace X] (A : QueryAlg X Ω)
    (ν : ObsKernel X) (g h : X → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (K : Set X) (hA : A.IsOn K) (hh : ∀ x ∈ K, g x ≤ c * h x)
    (ω : Ω) (n τ : ℕ) (y : Fin τ → ℝ) :
    cumLoss A ν g ω n τ y ≤ c * cumLoss A ν h ω n τ y := by
  induction n generalizing τ with
  | zero => simp [cumLoss]
  | succ n ih =>
    simp only [cumLoss, mul_add]
    apply add_le_add (hh _ (hA τ ω y))
    rw [← lintegral_const_mul' c _ hc]
    apply lintegral_mono
    intro z
    exact ih _ _

end BilateralProfitMHR
end
end BundlePart008


section BundlePart009



noncomputable section

namespace ProbeTree

open MeasureTheory Set
open scoped ENNReal

section Split
variable {I V : Type} [Fintype I] [DecidableEq I] [MeasurableSpace V]

private def joinCoordinate (i : I) (d : V × ({j : I // j ≠ i} → V)) (j : I) : V :=
  if h : j = i then d.1 else d.2 ⟨j, h⟩

private theorem measurable_joinCoordinate (i : I) : Measurable (joinCoordinate (V := V) i) := by
  apply measurable_pi_lambda
  intro j
  by_cases h : j = i
  · simpa [joinCoordinate, h] using
      (measurable_fst : Measurable (Prod.fst : V × ({j : I // j ≠ i} → V) → V))
  · simpa [joinCoordinate, h, Function.comp_def] using
      ((measurable_pi_apply (⟨j,h⟩ : {j : I // j ≠ i})).comp measurable_snd :
        Measurable (fun w : V × ({j : I // j ≠ i} → V) => w.2 ⟨j,h⟩))

private theorem measurePreserving_joinCoordinate (D : Measure V) [IsProbabilityMeasure D] (i : I) :
    MeasurePreserving (joinCoordinate i)
      (D.prod (Measure.pi (fun _ : {j : I // j ≠ i} => D)))
      (Measure.pi fun _ : I => D) := by
  refine ⟨measurable_joinCoordinate i, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  have heq : joinCoordinate i ⁻¹' Set.pi univ s =
      s i ×ˢ Set.pi univ (fun j : {j : I // j ≠ i} => s j) := by
    ext w
    simp only [mem_preimage, mem_pi, mem_univ, true_implies, mem_prod]
    constructor
    · intro H
      exact ⟨by simpa [joinCoordinate] using H i,
        fun j => by simpa [joinCoordinate, j.property] using H j⟩
    · rintro ⟨hi,hr⟩ j
      by_cases hj : j = i
      · subst j
        simpa [joinCoordinate] using hi
      · simpa [joinCoordinate, hj] using hr ⟨j,hj⟩
  rw [Measure.map_apply (measurable_joinCoordinate i) (MeasurableSet.univ_pi hs), heq,
    Measure.prod_prod, Measure.pi_pi, Fintype.prod_eq_mul_prod_subtype_ne _ i]

private theorem lintegral_branch_pi (D : Measure V) [IsProbabilityMeasure D] (i : I)
    (e : Set V) (he : MeasurableSet e) (f0 f1 : (I → V) → ℝ≥0∞)
    (h0 : Measurable f0) (h1 : Measurable f1)
    (hind0 : ∀ (x y : I → V), (∀ j, j ≠ i → x j = y j) → f0 x = f0 y)
    (hind1 : ∀ (x y : I → V), (∀ j, j ≠ i → x j = y j) → f1 x = f1 y)
    [DecidablePred fun v : V => v ∈ e] :
    (∫⁻ x, if x i ∈ e then f1 x else f0 x ∂(Measure.pi fun _ : I => D)) =
      D e * (∫⁻ x, f1 x ∂(Measure.pi fun _ : I => D)) +
        D eᶜ * (∫⁻ x, f0 x ∂(Measure.pi fun _ : I => D)) := by
  classical
  obtain ⟨w⟩ : Nonempty V := nonempty_of_isProbabilityMeasure D
  let rest : Measure ({j : I // j ≠ i} → V) := Measure.pi fun _ => D
  let g0 : ({j : I // j ≠ i} → V) → ℝ≥0∞ := fun z => f0 (joinCoordinate i (w,z))
  let g1 : ({j : I // j ≠ i} → V) → ℝ≥0∞ := fun z => f1 (joinCoordinate i (w,z))
  have hcomp0 (x : V) (u : {j : I // j ≠ i} → V) :
      f0 (joinCoordinate i (x,u)) = g0 u :=
    hind0 _ _ (by intro j hj; simp [joinCoordinate,hj])
  have hcomp1 (x : V) (u : {j : I // j ≠ i} → V) :
      f1 (joinCoordinate i (x,u)) = g1 u :=
    hind1 _ _ (by intro j hj; simp [joinCoordinate,hj])
  have hfg (f : (I → V) → ℝ≥0∞) (hf : Measurable f)
      (g : ({j : I // j ≠ i} → V) → ℝ≥0∞)
      (h : ∀ x u, f (joinCoordinate i (x,u)) = g u) :
      (∫⁻ x, f x ∂(Measure.pi fun _ : I => D)) = ∫⁻ u, g u ∂rest := by
    rw [← (measurePreserving_joinCoordinate D i).lintegral_comp hf]
    rw [lintegral_prod (fun z => f (joinCoordinate i z))
      (hf.comp (measurable_joinCoordinate i)).aemeasurable]
    simp only [h, lintegral_const, measure_univ, mul_one, rest]
  have hsel : Measurable (fun x : I → V => if x i ∈ e then f1 x else f0 x) :=
    Measurable.ite (he.preimage (measurable_pi_apply i)) h1 h0
  rw [hfg _ h1 g1 hcomp1,hfg _ h0 g0 hcomp0,
    ← (measurePreserving_joinCoordinate D i).lintegral_comp hsel]
  rw [lintegral_prod (fun z => if joinCoordinate i z i ∈ e then f1 (joinCoordinate i z)
      else f0 (joinCoordinate i z)) (hsel.comp (measurable_joinCoordinate i)).aemeasurable]
  have hinner (x : V) : (∫⁻ u, (if x ∈ e then g1 u else g0 u) ∂rest) =
      if x ∈ e then (∫⁻ u, g1 u ∂rest) else (∫⁻ u, g0 u ∂rest) := by
    split_ifs <;> rfl
  have htranslate (x : V) (u : {j : I // j ≠ i} → V) :
      (if joinCoordinate i (x,u) i ∈ e then f1 (joinCoordinate i (x,u))
        else f0 (joinCoordinate i (x,u))) =
      (if x ∈ e then g1 u else g0 u) := by
    rw [hcomp0,hcomp1]
    simp [joinCoordinate]
  simp only [htranslate]
  change (∫⁻ x, (∫⁻ u, (if x ∈ e then g1 u else g0 u) ∂rest) ∂D) = _
  simp only [hinner]
  have hs (A B : ℝ≥0∞) : (fun x => if x ∈ e then A else B) =
        (fun x => e.indicator (fun _ => A) x + eᶜ.indicator (fun _ => B) x) := by
    funext x
    by_cases hx : x ∈ e <;> simp [hx]
  rw [hs, lintegral_add_left (measurable_const.indicator he),
    lintegral_indicator_const he, lintegral_indicator_const he.compl]
  ac_rfl

end Split

section Tree
variable {I R V : Type} [DecidableEq I]

/-- Expected cost of probing until a leaf, with a continuation of the remaining horizon. -/
private def value (q : I → ℝ) (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞) :
    ℕ → ProbeTree I R → ℝ≥0∞
  | n, leaf r => finish n r
  | 0, node _ _ _ => 0
  | n+1, node i no yes =>
      g i + (ENNReal.ofReal (q i) * value q g finish n yes +
        ENNReal.ofReal (1-q i) * value q g finish n no)

/-- Cost before continuation for a fixed tape of bits, stopping at the physical horizon. -/
private def tapeCost (bits : I → Bool) (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞) :
    ℕ → ProbeTree I R → ℝ≥0∞
  | n, leaf r => finish n r
  | 0, node _ _ _ => 0
  | n+1, node i no yes =>
      g i + if bits i then tapeCost bits g finish n yes else tapeCost bits g finish n no

private theorem tapeCost_congr (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞)
    {seen : Finset I} {tree : ProbeTree I R} (hvalid : ValidSeen seen tree)
    {bits b' : I → Bool} (h : ∀ j, j ∉ seen → bits j = b' j) (n : ℕ) :
    tapeCost bits g finish n tree = tapeCost b' g finish n tree := by
  induction tree generalizing n seen with
  | leaf r => simp [tapeCost]
  | node i no yes ih0 ih1 =>
    cases n with
    | zero => rfl
    | succ n =>
      obtain ⟨hi,hno,hyes⟩ := hvalid
      simp only [tapeCost, h i hi]
      congr 1
      split <;> first
        | apply ih1 hyes (fun j hj => h j (fun hmem => hj (Finset.mem_insert_of_mem hmem)))
        | apply ih0 hno (fun j hj => h j (fun hmem => hj (Finset.mem_insert_of_mem hmem)))

private theorem tapeCost_eval (bits : I → Bool) (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞)
    (n : ℕ) (tree : ProbeTree I R) (h : (tree.eval bits).1.length ≤ n) :
    tapeCost bits g finish n tree =
      ((tree.eval bits).1.map g).sum + finish (n - (tree.eval bits).1.length) (tree.eval bits).2 := by
  induction tree generalizing n with
  | leaf r => simp [tapeCost, eval]
  | node i no yes ih0 ih1 =>
    cases hi : bits i <;> simp [eval,hi] at h ⊢
    · obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
      simp [tapeCost,hi,ih0 n (by omega),Nat.succ_sub_succ_eq_sub, add_assoc]
    · obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
      simp [tapeCost,hi,ih1 n (by omega),Nat.succ_sub_succ_eq_sub, add_assoc]

end Tree

section Integral
variable {I R V : Type} [Fintype I] [DecidableEq I] [MeasurableSpace V]

private def bitsFromSets (e : I → Set V) (w : I → V) : I → Bool :=
  fun i => by classical exact decide (w i ∈ e i)

private theorem measurable_tapeCost (e : I → Set V) (he : ∀ i, MeasurableSet (e i))
    (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞) (n : ℕ) (tree : ProbeTree I R) :
    Measurable (fun w : I → V =>
      tapeCost (bitsFromSets e w) g finish n tree) := by
  classical
  induction tree generalizing n with
  | leaf r => simp only [tapeCost]; exact measurable_const
  | node i no yes ih0 ih1 =>
    cases n with
    | zero => exact measurable_const
    | succ n =>
      simp only [tapeCost, bitsFromSets, decide_eq_true_eq]
      exact measurable_const.add
        (Measurable.ite ((he i).preimage (measurable_pi_apply i)) (ih1 n) (ih0 n))

private theorem value_eq_lintegral (D : Measure V) [IsProbabilityMeasure D]
    (e : I → Set V) (he : ∀ i, MeasurableSet (e i))
    (q : I → ℝ) (hq : ∀ i, q i ∈ Icc 0 1)
    (hmass : ∀ i, D (e i) = ENNReal.ofReal (q i))
    (g : I → ℝ≥0∞) (finish : ℕ → R → ℝ≥0∞)
    {seen : Finset I} (n : ℕ) (tree : ProbeTree I R) (hvalid : ValidSeen seen tree) :
    value q g finish n tree =
      ∫⁻ w, tapeCost (bitsFromSets e w) g finish n tree
        ∂(Measure.pi fun _ : I => D) := by
  classical
  induction tree generalizing n seen with
    | leaf r => simp [value,tapeCost]
    | node i no yes ih0 ih1 =>
      cases n with
      | zero => simp [value,tapeCost]
      | succ n =>
        obtain ⟨hi,hno,hyes⟩ := hvalid
        simp only [value, tapeCost, bitsFromSets, decide_eq_true_eq]
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        rw [lintegral_branch_pi D i (e i) (he i) _ _
          (measurable_tapeCost e he g finish n no)
          (measurable_tapeCost e he g finish n yes)]
        · have hc : D (e i)ᶜ = ENNReal.ofReal (1-q i) := by
            rw [measure_compl (he i) (measure_ne_top D _), measure_univ, hmass]
            rw [← ENNReal.ofReal_one, ENNReal.ofReal_sub _ (hq i).1]
          rw [hc, hmass, ← ih1 n hyes, ← ih0 n hno]
        · intro x y h
          apply tapeCost_congr g finish hno
          intro j hj
          simp only [bitsFromSets, h j (fun hij => hj (by simp [hij]))]
        · intro x y h
          apply tapeCost_congr g finish hyes
          intro j hj
          simp only [bitsFromSets, h j (fun hij => hj (by simp [hij]))]

end Integral
end ProbeTree
end
end BundlePart009


section BundlePart010



set_option autoImplicit false

noncomputable section

namespace BilateralProfitMHR

open MeasureTheory ProbabilityTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem initial_gap_nonneg {K T : ℕ} (hK : 0 < K) (E : Environment)
    (hE : UnitSupport E) (z : SampleIdx K T) :
    0 ≤ muStar E.prior - muP E.prior (initSamplePrice z) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hle, _⟩ := positive_density_profit_facts E hE
  exact sub_nonneg.mpr (hle _ (initSamplePrice_mem_unitSq hK z))

private theorem initial_list_ofReal {I : Type} (l : List I) (f : I → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (l.map fun i => ENNReal.ofReal (f i)).sum = ENNReal.ofReal ((l.map f).sum) := by
  induction l with
  | nil => simp
  | cons i rest ih =>
    have hs : 0 ≤ (rest.map f).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      exact hf j)
    simp only [List.map_cons, List.sum_cons, ih, ENNReal.ofReal_add (hf i) hs]

private theorem initializer_tapeCost_eq {K T : ℕ} (hK : 0 < K) (E : Environment) (hE : UnitSupport E)
    (finish : ℕ → InitTreeResult → ℝ≥0∞) (ω : Samples K T)
    (hround : initRounds K T ω ≤ T) :
    ProbeTree.tapeCost (initReadBits ω)
      (fun z : SampleIdx K T => ENNReal.ofReal (muStar E.prior - muP E.prior (initSamplePrice z)))
      finish T (initTree K T) =
        ENNReal.ofReal (filterRegret K T E.prior ω) +
          finish (T - initRounds K T ω) (initRounds K T ω, initOut K T ω) := by
  have hlen : (ProbeTree.eval (initTree K T) (initReadBits ω)).1.length ≤ T := by
    rw [initTree_eval hK, initRunSchedule_length]
    exact hround
  rw [ProbeTree.tapeCost_eval _ _ _ _ _ hlen, initTree_eval hK, initRunSchedule_length,
    initial_list_ofReal _ _ (initial_gap_nonneg hK E hE), initRunSchedule_profit_gap]

private theorem initializer_then_cost_bound {K T : ℕ} (hT : 2 ≤ T) (hK : 2 ≤ K)
    (E : Environment) (hE : UnitSupport E)
    (finish : ℕ → InitTreeResult → ℝ≥0∞) (I B : ℝ≥0∞)
    (hround : ∀ ω : Samples K T, initRounds K T ω ≤ T)
    (G : Set (Samples K T)) (hG : MeasurableSet G)
    (hGprob : 1 - (T : ℝ≥0∞)⁻¹ ≤ initLaw K T E.prior G)
    (hinit : (∫⁻ ω, ENNReal.ofReal (filterRegret K T E.prior ω +
          if initOut K T ω = none then
            ((T - initRounds K T ω : ℕ) : ℝ) * muStar E.prior else 0)
        ∂(initLaw K T E.prior)) ≤ I)
    (hfinish_all : ∀ b r, finish b r ≤ (b : ℝ≥0∞))
    (hfinish_none : ∀ b t, finish b (t, none) ≤ ENNReal.ofReal ((b : ℝ) * muStar E.prior))
    (hfinish_good : ∀ ω ∈ G, ∀ h R, initOut K T ω = some (h, R) →
      finish (T - initRounds K T ω) (initRounds K T ω, some (h, R)) ≤ B) :
    ProbeTree.value
      (fun z : SampleIdx K T => Ptrade E.prior (initSamplePrice z))
      (fun z : SampleIdx K T => ENNReal.ofReal (muStar E.prior - muP E.prior (initSamplePrice z)))
      finish T (initTree K T) ≤ I + B + 1 := by
  classical
  obtain ⟨hprob, _, hPbounds, _, _, _, _, _, _, hstar, hle, _⟩ := positive_density_profit_facts E hE
  letI := hprob
  letI : IsProbabilityMeasure (initLaw K T E.prior) := by unfold initLaw; infer_instance
  let q := fun z : SampleIdx K T => Ptrade E.prior (initSamplePrice z)
  let g := fun z : SampleIdx K T => ENNReal.ofReal (muStar E.prior - muP E.prior (initSamplePrice z))
  let e := fun z : SampleIdx K T => {v : ℝ × ℝ | Trades v (initSamplePrice z)}
  have he : ∀ z, MeasurableSet (e z) := fun z =>
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_const measurable_snd)
  have hmass z : E.prior (e z) = ENNReal.ofReal (q z) := by
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hvalue := ProbeTree.value_eq_lintegral E.prior e he q
    (fun z => hPbounds (initSamplePrice z)) hmass g finish T (initTree K T) (initTree_valid K T)
  change ProbeTree.value q g finish T (initTree K T) ≤ _
  rw [hvalue]
  have hbits (ω : Samples K T) : ProbeTree.bitsFromSets e ω = initReadBits ω := by
    funext z
    apply Bool.eq_iff_iff.mpr
    simp [ProbeTree.bitsFromSets, initReadBits, e]
  simp_rw [hbits]
  change (∫⁻ ω : Samples K T, ProbeTree.tapeCost (initReadBits ω) g finish T (initTree K T)
    ∂(initLaw K T E.prior)) ≤ _
  let M := fun ω : Samples K T => ENNReal.ofReal (filterRegret K T E.prior ω +
    if initOut K T ω = none then
      ((T - initRounds K T ω : ℕ) : ℝ) * muStar E.prior else 0)
  let bad := Gᶜ.indicator (fun _ : Samples K T => (T : ℝ≥0∞))
  have hpoint (ω : Samples K T) :
      ProbeTree.tapeCost (initReadBits ω) g finish T (initTree K T) ≤ M ω + (B + bad ω) := by
    rw [initializer_tapeCost_eq (by omega) E hE finish ω (hround ω)]
    have hfilter : 0 ≤ filterRegret K T E.prior ω := by
      rw [← initRunSchedule_profit_gap]
      apply List.sum_nonneg
      intro x hx
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
      exact initial_gap_nonneg (by omega) E hE z
    cases ho : initOut K T ω with
    | none =>
      have hf := hfinish_none (T - initRounds K T ω) (initRounds K T ω)
      have hrem : 0 ≤ ((T - initRounds K T ω : ℕ) : ℝ) * muStar E.prior :=
        mul_nonneg (Nat.cast_nonneg _) hstar.1.le
      have hM : M ω = ENNReal.ofReal (filterRegret K T E.prior ω) +
          ENNReal.ofReal (((T - initRounds K T ω : ℕ) : ℝ) * muStar E.prior) := by
        simp only [M, ho, ↓reduceIte, ENNReal.ofReal_add hfilter hrem]
      rw [hM]
      exact (add_le_add_right hf _).trans le_self_add
    | some z =>
      rcases z with ⟨h, R⟩
      have hM : M ω = ENNReal.ofReal (filterRegret K T E.prior ω) := by simp [M, ho]
      rw [hM]
      by_cases hω : ω ∈ G
      · have hf := hfinish_good ω hω h R ho
        exact add_le_add_right (hf.trans le_self_add) _
      · have hf := (hfinish_all (T - initRounds K T ω) (initRounds K T ω, some (h, R))).trans
          (show ((T - initRounds K T ω : ℕ) : ℝ≥0∞) ≤ T by exact_mod_cast Nat.sub_le T (initRounds K T ω))
        have hbad : bad ω = T := by simp [bad, hω]
        rw [hbad]
        exact add_le_add_right (hf.trans le_add_self) _
  have hbadprob : initLaw K T E.prior Gᶜ ≤ (T : ℝ≥0∞)⁻¹ := by
    rw [measure_compl hG (measure_ne_top _ _), measure_univ]
    apply tsub_le_iff_right.mpr
    simpa only [add_comm] using (tsub_le_iff_right.mp hGprob)
  have hbadcost : (T : ℝ≥0∞) * initLaw K T E.prior Gᶜ ≤ 1 := by
    calc
      _ ≤ (T : ℝ≥0∞) * (T : ℝ≥0∞)⁻¹ := by gcongr
      _ = 1 := ENNReal.mul_inv_cancel (by exact_mod_cast (show T ≠ 0 by omega)) (by finiteness)
  have hbadmeas : Measurable bad := measurable_const.indicator hG.compl
  calc
    _ ≤ ∫⁻ ω, M ω + (B + bad ω) ∂(initLaw K T E.prior) := lintegral_mono hpoint
    _ = (∫⁻ ω, M ω ∂(initLaw K T E.prior)) +
        (B + (T : ℝ≥0∞) * initLaw K T E.prior Gᶜ) := by
      rw [lintegral_add_right M (g := fun ω => B + bad ω) (measurable_const.add hbadmeas),
        lintegral_add_left (f := fun _ : Samples K T => B) measurable_const bad,
        lintegral_const, lintegral_indicator_const hG.compl]
      simp only [measure_univ, mul_one]
    _ ≤ I + (B + 1) := add_le_add hinit (add_le_add_right hbadcost B)
    _ = I + B + 1 := by ac_rfl

end BilateralProfitMHR
end
end BundlePart010


section BundlePart011



noncomputable section
namespace BilateralProfitMHR

open MeasureTheory Set BilateralProfit
open scoped ENNReal

/-- The state of probing followed by repeated queries from the selected bandit policy. -/
private inductive TradeControlState (I R : Type) where
  | probe (i : I) (no yes : ProbeTree I R)
  | wait (r : R) (s : WaitState)

variable {I R Ω : Type} [MeasurableSpace Ω]

private def enterTradeControl : ProbeTree I R → TradeControlState I R
  | .leaf r => .wait r waitEmpty
  | .node i no yes => .probe i no yes

private def tradeControlPrice (prices : I → ℝ × ℝ) (A : R → QueryAlg (ℝ × ℝ) Ω)
    (ω : Ω) : TradeControlState I R → ℝ × ℝ
  | .probe i _ _ => prices i
  | .wait r w => waitPrice (A r) ω w

private def tradeControlNext (A : R → QueryAlg (ℝ × ℝ) Ω) (ω : Ω) :
    TradeControlState I R → Bool → TradeControlState I R
  | .probe _ no yes, bit => enterTradeControl (if bit then yes else no)
  | .wait r w, bit => .wait r (waitNext (A r) ω w bit)

/-- For a fixed bit history the probe position or the chosen leaf and query
counters are determined. Only the completed real observations depend on the seed. -/
private inductive MeasurableTradeState : (Ω → TradeControlState I R) → Prop where
  | probe (i : I) (no yes : ProbeTree I R) :
      MeasurableTradeState (fun _ => .probe i no yes)
  | wait (r : R) (τ k : ℕ) (obs : Ω → Fin τ → ℝ) (h : Measurable obs) :
      MeasurableTradeState (fun ω => .wait r ⟨τ, obs ω, k⟩)

private theorem measurable_enterTradeControl (tree : ProbeTree I R) :
    MeasurableTradeState (Ω := Ω) (fun _ => enterTradeControl tree) := by
  cases tree with
  | leaf r => exact .wait r 0 0 (fun _ => Fin.elim0) measurable_const
  | node i no yes => exact .probe i no yes

private theorem tradeControlPrice_measurable (prices : I → ℝ × ℝ)
    (A : R → QueryAlg (ℝ × ℝ) Ω) {s : Ω → TradeControlState I R}
    (hs : MeasurableTradeState s) :
    Measurable fun ω => tradeControlPrice prices A ω (s ω) := by
  cases hs with
  | probe i no yes => exact measurable_const
  | wait r τ k obs ho =>
    exact (A r).query_measurable τ |>.comp (measurable_id.prodMk ho)

private theorem tradeControlNext_measurable (A : R → QueryAlg (ℝ × ℝ) Ω)
    {s : Ω → TradeControlState I R} (hs : MeasurableTradeState s) (b : Bool) :
    MeasurableTradeState fun ω => tradeControlNext A ω (s ω) b := by
  cases hs with
  | probe i no yes => exact measurable_enterTradeControl (if b then yes else no)
  | wait r τ k obs ho =>
    cases b with
    | false => exact .wait r τ (k+1) obs ho
    | true =>
      let a := fun ω => (A r).query τ ω (obs ω)
      have ha : Measurable a := (A r).query_measurable τ |>.comp (measurable_id.prodMk ho)
      have hf : Measurable fun ω => waitObservation (a ω) k :=
        measurable_const.sub (Real.measurable_log.comp ((measurable_snd.comp ha).sub
          (measurable_fst.comp ha)))
      refine .wait r (τ+1) 0 (fun ω => Fin.snoc (obs ω) (waitObservation (a ω) k)) ?_
      apply measurable_pi_lambda
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using hf
      · simpa [Function.comp_def] using ((measurable_pi_apply i).comp ho)

private theorem tradeControl_fixed_history (A : R → QueryAlg (ℝ × ℝ) Ω) (tree : ProbeTree I R)
    (τ : ℕ) (h : Fin τ → Bool) :
    MeasurableTradeState fun ω =>
      binaryRunState (tradeControlNext A) (fun _ => enterTradeControl tree) τ h ω := by
  induction τ with
  | zero => exact measurable_enterTradeControl tree
  | succ τ ih =>
    exact tradeControlNext_measurable A (ih (Fin.init h)) (h (Fin.last τ))

private theorem tradeControl_cost_measurable (D : Measure (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ≥0∞)
    (hD : Measurable (Ptrade D)) (hg : Measurable g) (prices : I → ℝ × ℝ)
    (A : R → QueryAlg (ℝ × ℝ) Ω) (b : ℕ) (s : Ω → TradeControlState I R)
    (hs : MeasurableTradeState s) :
    Measurable fun ω => binaryValue (Ptrade D) g (tradeControlPrice prices A ω)
      (tradeControlNext A ω) b (s ω) := by
  induction b generalizing s with
  | zero => exact measurable_const
  | succ b ih =>
    have hp := tradeControlPrice_measurable prices A hs
    have hq := hD.comp hp
    simp only [binaryValue]
    exact (hg.comp hp).add ((hq.ennreal_ofReal.mul
      (ih _ (tradeControlNext_measurable A hs true))).add
      ((measurable_const.sub hq).ennreal_ofReal.mul
        (ih _ (tradeControlNext_measurable A hs false))))

private theorem tradeControl_wait_value (D : Measure (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ≥0∞)
    (prices : I → ℝ × ℝ) (A : R → QueryAlg (ℝ × ℝ) Ω) (ω : Ω) (r : R)
    (b : ℕ) (s : WaitState) :
    binaryValue (Ptrade D) g (tradeControlPrice prices A ω) (tradeControlNext A ω) b (.wait r s) =
      binaryValue (Ptrade D) g (waitPrice (A r) ω) (waitNext (A r) ω) b s := by
  induction b generalizing s with
  | zero => rfl
  | succ b ih => simp only [binaryValue, tradeControlPrice, tradeControlNext, ih]

private def optCost (P : Measure Ω) (D : Measure (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ≥0∞)
    (A : QueryAlg (ℝ × ℝ) Ω) (b : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, binaryValue (Ptrade D) g (waitPrice A ω) (waitNext A ω) b waitEmpty ∂P

private theorem tradeControl_lintegral (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure (ℝ × ℝ)) (g : (ℝ × ℝ) → ℝ≥0∞) (hD : Measurable (Ptrade D))
    (hg : Measurable g) (prices : I → ℝ × ℝ) (A : R → QueryAlg (ℝ × ℝ) Ω)
    (b : ℕ) (tree : ProbeTree I R) :
    (∫⁻ ω, binaryValue (Ptrade D) g (tradeControlPrice prices A ω) (tradeControlNext A ω)
        b (enterTradeControl tree) ∂P) =
      ProbeTree.value (Ptrade D ∘ prices) (g ∘ prices) (fun n r => optCost P D g (A r) n)
        b tree := by
  induction b generalizing tree with
  | zero =>
    cases tree <;> simp [binaryValue, ProbeTree.value, optCost]
  | succ b ih =>
    cases tree with
    | leaf r =>
      simp only [enterTradeControl, ProbeTree.value, optCost, tradeControl_wait_value]
    | node i no yes =>
      simp only [ProbeTree.value, binaryValue, enterTradeControl, tradeControlPrice,
        tradeControlNext, Bool.false_eq_true, if_false, if_true, Function.comp_apply]
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      rw [lintegral_add_left]
      · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        erw [ih yes, ih no]
      · exact measurable_const.mul
          (tradeControl_cost_measurable D g hD hg prices A b _ (measurable_enterTradeControl yes))

private theorem optCost_pull_seed {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {f : Ω' → Ω} (hf : MeasurePreserving f P' P) (D : Measure (ℝ × ℝ))
    (hD : Measurable (Ptrade D)) {g : (ℝ × ℝ) → ℝ≥0∞} (hg : Measurable g)
    (A : QueryAlg (ℝ × ℝ) Ω) (b : ℕ) :
    optCost P' D g
      ⟨fun τ ω y => A.query τ (f ω) y,
        fun τ => (A.query_measurable τ).comp ((hf.measurable.comp measurable_fst).prodMk measurable_snd)⟩
        b = optCost P D g A b := by
  let A' : QueryAlg (ℝ × ℝ) Ω' :=
    ⟨fun τ ω y => A.query τ (f ω) y,
        fun τ => (A.query_measurable τ).comp ((hf.measurable.comp measurable_fst).prodMk measurable_snd)⟩
  have hval (ω : Ω') (n : ℕ) (w : WaitState) :
      binaryValue (Ptrade D) g (waitPrice A' ω) (waitNext A' ω) n w =
      binaryValue (Ptrade D) g (waitPrice A (f ω)) (waitNext A (f ω)) n w := by
    induction n generalizing w with
    | zero => rfl
    | succ n ih =>
      have he (b : Bool) : waitNext A' ω w b = waitNext A (f ω) w b := by
        cases b <;> rfl
      simp only [binaryValue,he,ih]
      rfl
  change optCost P' D g A' b = optCost P D g A b
  unfold optCost
  simp only [hval]
  refine hf.lintegral_comp (f := fun ω =>
    binaryValue (Ptrade D) g (waitPrice A ω) (waitNext A ω) b waitEmpty) ?_
  let u : Unit → QueryAlg (ℝ × ℝ) Ω := fun _ => A
  have hm := tradeControl_cost_measurable (I := Unit) D g hD hg (fun _ => (0,0)) u b
    (fun _ => .wait () waitEmpty)
    (MeasurableTradeState.wait () 0 0 (fun _ => Fin.elim0) measurable_const)
  simpa only [tradeControl_wait_value,u] using hm

end BilateralProfitMHR
end
end BundlePart011


section BundlePart012




noncomputable section

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit Set
open scoped ENNReal

private theorem gap_div_trade_le_log (u v Q : ℝ) (hu : 0 < u) (huQ : u ≤ Q)
    (huv : u ≤ v) (hvu : v ≤ 12 * u) :
    (v - u) / Q ≤ 12 * Real.log (v / u) := by
  have hQ : 0 < Q := hu.trans_le huQ
  let z := v / u
  have hz : 0 < z := div_pos (hu.trans_le huv) hu
  have hz1 : 1 ≤ z := (one_le_div hu).mpr huv
  have hz12 : z ≤ 12 := (div_le_iff₀ hu).mpr hvu
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz1
  have hbase := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hz) hz.le
  simp only [mul_sub, mul_one, mul_inv_cancel₀ hz.ne'] at hbase
  calc
    _ ≤ (v - u) / u := div_le_div_of_nonneg_left (sub_nonneg.mpr huv) hu huQ
    _ = z - 1 := by dsimp [z]; field_simp
    _ ≤ z * Real.log z := hbase
    _ ≤ 12 * Real.log z := mul_le_mul_of_nonneg_right hz12 hlog

private theorem sSup_mu_eq_of_max (D : Measure (ℝ × ℝ)) (R : Set (ℝ × ℝ)) (xstar : ℝ × ℝ)
    (hxstar : xstar ∈ R) (hmax : ∀ x ∈ R, muP D x ≤ muP D xstar) :
    sSup (muP D '' R) = muP D xstar := by
  have hne : (muP D '' R).Nonempty := ⟨muP D xstar, xstar, hxstar, rfl⟩
  have hbd : BddAbove (muP D '' R) := by
    refine ⟨muP D xstar, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    exact hmax x hx
  exact le_antisymm (csSup_le hne (by rintro v ⟨x, hx, rfl⟩; exact hmax x hx))
    (le_csSup hbd ⟨xstar, hxstar, rfl⟩)

private theorem optPhysical_bound {Ω : Type} [MeasurableSpace Ω]
    (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : QueryAlg (ℝ × ℝ) Ω)
    (T K b : ℕ) (hK : 2 ≤ K) (hKT : K ≤ T) (hb1 : 1 ≤ b) (hbT : b ≤ T)
    (δ : ℝ) (hδ : 1 / (K : ℝ) ≤ δ) (R : Set (ℝ × ℝ))
    (hR : R ⊆ unitSq) (hA : A.IsOn R)
    (hsafe : ∀ x ∈ R, δ / 2 ≤ muP D x ∧ muP D x ≤ 6 * δ)
    (xstar : ℝ × ℝ) (hxstar : xstar ∈ R) (hmax : ∀ x ∈ R, muP D x ≤ muP D xstar)
    (M C : ℝ) (hnear : M - muP D xstar ≤ 2 / (K : ℝ)) (hC : 0 ≤ C)
    (hreg : expectedCumLoss A P (oracleKernel D)
      (fun x => ENNReal.ofReal (Real.log (sSup (muP D '' R) / muP D x))) b ≤
      ENNReal.ofReal (C * Real.sqrt (b * Real.log T) * Real.log (2 * b) ^ 2)) :
    (∫⁻ ω, binaryValue (Ptrade D) (fun x => ENNReal.ofReal (M - muP D x))
      (waitPrice A ω) (waitNext A ω) b waitEmpty ∂P) ≤
      ENNReal.ofReal (2 * (b : ℝ) / K +
        12 * C * Real.sqrt (b * Real.log T) * Real.log (2 * b) ^ 2) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hδ0 : 0 < δ := (by positivity : 0 < 1 / (K : ℝ)).trans_le hδ
  have hQ (x : ℝ × ℝ) (hx : x ∈ R) :
      0 < muP D x ∧ muP D x ≤ Ptrade D x ∧ Ptrade D x ≤ 1 := by
    have hmu : 0 < muP D x := (by positivity : 0 < δ / 2).trans_le (hsafe x hx).1
    have hmQ : muP D x ≤ Ptrade D x := by
      unfold muP
      apply mul_le_of_le_one_left ENNReal.toReal_nonneg
      have hh := hR hx
      change x ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 at hh
      linarith [hh.1.1, hh.2.2]
    have hQ1 : Ptrade D x ≤ 1 := by
      unfold Ptrade
      exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr prob_le_one
    exact ⟨hmu, hmQ, hQ1⟩
  have hsup := sSup_mu_eq_of_max D R xstar hxstar hmax
  let g := fun x => ENNReal.ofReal (muP D xstar - muP D x)
  let ell := fun x => ENNReal.ofReal (Real.log (sSup (muP D '' R) / muP D x))
  have hweighted : ∀ x ∈ R, g x / ENNReal.ofReal (Ptrade D x) ≤ 12 * ell x := by
    intro x hx
    obtain ⟨hmu, hmQ, hQ1⟩ := hQ x hx
    have hQ0 := hmu.trans_le hmQ
    have hvu : muP D xstar ≤ 12 * muP D x := by
      have hs := hsafe x hx
      have ht := hsafe xstar hxstar
      linarith
    have hreal := gap_div_trade_le_log (muP D x) (muP D xstar) (Ptrade D x)
      hmu hmQ (hmax x hx) hvu
    dsimp [g, ell]
    rw [← ENNReal.ofReal_div_of_pos hQ0, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12), hsup]
    exact ENNReal.ofReal_le_ofReal hreal
  have hpref (ω : Ω) :
      binaryValue (Ptrade D) (fun x => ENNReal.ofReal (M - muP D x))
          (waitPrice A ω) (waitNext A ω) b waitEmpty ≤
        12 * cumLoss A (oracleKernel D) ell ω b 0 Fin.elim0 +
          (b : ℝ≥0∞) * ENNReal.ofReal (2 / (K : ℝ)) := by
    have hact : ∀ s : WaitState, waitPrice A ω s ∈ R := fun s => hA _ ω _
    have hprob : ∀ s : WaitState, 0 < Ptrade D (waitPrice A ω s) ∧
        Ptrade D (waitPrice A ω s) ≤ 1 := fun s =>
      ⟨(hQ _ (hact s)).1.trans_le (hQ _ (hact s)).2.1, (hQ _ (hact s)).2.2⟩
    calc
      _ ≤ binaryValue (Ptrade D) g (waitPrice A ω) (waitNext A ω) b waitEmpty +
          (b : ℝ≥0∞) * ENNReal.ofReal (2 / (K : ℝ)) := by
        apply binaryValue_le_add
        · intro s
          exact ⟨(hprob s).1.le, (hprob s).2⟩
        · intro s
          have hreal : M - muP D (waitPrice A ω s) ≤
              (muP D xstar - muP D (waitPrice A ω s)) + 2 / (K : ℝ) := by linarith
          have he := ENNReal.ofReal_le_ofReal hreal
          rw [ENNReal.ofReal_add (sub_nonneg.mpr (hmax _ (hact s))) (by positivity)] at he
          exact he
      _ ≤ waitFullCost D g A ω b waitEmpty +
          (b : ℝ≥0∞) * ENNReal.ofReal (2 / (K : ℝ)) :=
        add_le_add (waitValue_le_full D g A ω hprob b b le_rfl waitEmpty) le_rfl
      _ = cumLoss A (oracleKernel D) (fun x => g x / ENNReal.ofReal (Ptrade D x))
          ω b 0 Fin.elim0 + (b : ℝ≥0∞) * ENNReal.ofReal (2 / (K : ℝ)) := by
        rw [waitEmpty, waitFullCost_fresh]
      _ ≤ _ := add_le_add
        (cumLoss_le_mul_on A (oracleKernel D) _ ell 12 (by norm_num) R hA hweighted ω b 0 Fin.elim0) le_rfl
  have hconst : (b : ℝ≥0∞) * ENNReal.ofReal (2 / (K : ℝ)) =
      ENNReal.ofReal (2 * (b : ℝ) / K) := by
    rw [← ENNReal.ofReal_natCast b, ← ENNReal.ofReal_mul (Nat.cast_nonneg b)]
    congr 1
    ring
  calc
    _ ≤ ∫⁻ ω, (12 * cumLoss A (oracleKernel D) ell ω b 0 Fin.elim0 +
        (b : ℝ≥0∞) * ENNReal.ofReal (2 / (K : ℝ))) ∂P := lintegral_mono hpref
    _ = 12 * expectedCumLoss A P (oracleKernel D) ell b +
        ENNReal.ofReal (2 * (b : ℝ) / K) := by
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul' 12 _ (by norm_num),
        lintegral_const, measure_univ, mul_one, hconst]
      rfl
    _ ≤ 12 * ENNReal.ofReal (C * Real.sqrt (b * Real.log T) * Real.log (2 * b) ^ 2) +
        ENNReal.ofReal (2 * (b : ℝ) / K) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hreg (by norm_num)) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

private theorem optimization_rate_le_main (T b : ℕ) (hT : 2 ≤ T) (hb : 1 ≤ b) (hbT : b ≤ T) :
    Real.sqrt (b * Real.log T) * Real.log (2 * b) ^ 2 ≤
      4 * Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hb0 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hL : 0 < Real.log T := Real.log_pos (by exact_mod_cast hT)
  have hlogT : Real.log 2 ≤ Real.log T :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have hlogb : Real.log (2 * (b : ℝ)) ≤ 2 * Real.log T := by
    calc
      _ ≤ Real.log (2 * (T : ℝ)) := Real.log_le_log (by positivity) (by exact_mod_cast (Nat.mul_le_mul_left 2 hbT))
      _ = Real.log 2 + Real.log T := Real.log_mul (by norm_num) hT0.ne'
      _ ≤ _ := by linarith
  have hlogb0 : 0 ≤ Real.log (2 * (b : ℝ)) := Real.log_nonneg (by linarith)
  have hsq : Real.log (2 * (b : ℝ)) ^ 2 ≤ 4 * Real.log T ^ 2 := by nlinarith
  have hs : Real.sqrt ((b : ℝ) * Real.log T) ≤ Real.sqrt T * Real.sqrt (Real.log T) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ b)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast hbT)) (Real.sqrt_nonneg _)
  have hpow : Real.sqrt (Real.log T) * Real.log T ^ 2 = Real.log T ^ ((5 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_add hL]
    norm_num
  calc
    _ ≤ (Real.sqrt T * Real.sqrt (Real.log T)) * (4 * Real.log T ^ 2) :=
      mul_le_mul hs hsq (sq_nonneg _) (by positivity)
    _ = _ := by rw [← hpow]; ring

private theorem initialization_rate_le_main (T : ℕ) (hT : 2 ≤ T) :
    Real.sqrt T * Real.log (2 * T) ≤
      8 * Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2) := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogT : Real.log 2 ≤ Real.log T :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hT)
  have hL : (1 / 2 : ℝ) ≤ Real.log T := hlog2.trans hlogT
  have hLpos : 0 < Real.log T := by linarith
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt (Real.log T) := by
    have hsq := Real.sq_sqrt hLpos.le
    have hnn := Real.sqrt_nonneg (Real.log T)
    nlinarith
  have hprod : (1 / 4 : ℝ) ≤ Real.log T * Real.sqrt (Real.log T) := by nlinarith
  have hprod' := mul_le_mul_of_nonneg_left hprod hLpos.le
  have hpow : Real.sqrt (Real.log T) * Real.log T ^ 2 = Real.log T ^ ((5 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_add hLpos]
    norm_num
  have hlog : Real.log (2 * (T : ℝ)) ≤ 8 * Real.log T ^ ((5 : ℝ) / 2) := by
    rw [← hpow, Real.log_mul (by norm_num) hT0.ne']
    nlinarith
  exact (mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg T)).trans_eq (by ring)




end BilateralProfitMHR
end
end BundlePart012


section BundlePart013



set_option autoImplicit false

namespace BilateralProfitMHR

private lemma main_grid_le_horizon {c0 : ℝ} (hc0 : 0 < c0) (hc : c0 ≤ 1 / 2)
    {T : ℕ} (hT : 2 ≤ T) : Kpar c0 T ≤ T := init_Kpar_le_T hc0 hc hT

private lemma main_grid_error_le {c0 : ℝ} (hc0 : 0 < c0) {T : ℕ} (hT : 2 ≤ T)
    (hK : 2 ≤ Kpar c0 T) :
    2 * (T : ℝ) / Kpar c0 T ≤ (4 / c0) * Real.sqrt T * Real.log (2 * T) := by
  have hL := init_log_ge_one hT
  have hLpos : 0 < Real.log (2 * (T : ℝ)) := by linarith
  have hKr : (0 : ℝ) < Kpar c0 T := by exact_mod_cast (by omega : 0 < Kpar c0 T)
  have hl := (div_le_iff₀ hLpos).mp (init_Kpar_real_lower hK)
  have hm := mul_le_mul_of_nonneg_right hl (Real.sqrt_nonneg (T : ℝ))
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) T)
  rw [mul_assoc, ← pow_two, hs] at hm
  apply (div_le_iff₀ hKr).mpr
  apply (mul_le_mul_iff_right₀ hc0).mp
  calc
    c0 * (2 * (T : ℝ)) ≤ 4 * Real.sqrt T * Real.log (2 * T) * Kpar c0 T := by nlinarith
    _ = c0 * ((4 / c0) * Real.sqrt T * Real.log (2 * T) * Kpar c0 T) := by field_simp

private lemma main_short_horizon_cost {c0 : ℝ} (hc0 : 0 < c0) {T : ℕ} (hT : 2 ≤ T)
    (hK : Kpar c0 T < 2) :
    (T : ℝ) ≤ (2 / c0) * Real.sqrt T * Real.log (2 * T) := by
  have hL := init_log_ge_one hT
  have hLpos : 0 < Real.log (2 * (T : ℝ)) := by linarith
  have hfloor := Nat.lt_floor_add_one (c0 * Real.sqrt T / Real.log (2 * T))
  have hKr : (Kpar c0 T : ℝ) ≤ 1 := by exact_mod_cast (by omega : Kpar c0 T ≤ 1)
  change c0 * Real.sqrt T / Real.log (2 * T) < (Kpar c0 T : ℝ) + 1 at hfloor
  have hx : c0 * Real.sqrt T / Real.log (2 * T) ≤ 2 := by linarith
  have hl := (div_le_iff₀ hLpos).mp hx
  have hm := mul_le_mul_of_nonneg_right hl (Real.sqrt_nonneg (T : ℝ))
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) T)
  rw [mul_assoc, ← pow_two, hs] at hm
  apply (mul_le_mul_iff_right₀ hc0).mp
  calc
    c0 * (T : ℝ) ≤ 2 * Real.sqrt T * Real.log (2 * T) := by nlinarith
    _ = c0 * ((2 / c0) * Real.sqrt T * Real.log (2 * T)) := by field_simp

private lemma main_rate_ge_constant (T : ℕ) (hT : 2 ≤ T) :
    (1 / 8 : ℝ) ≤ Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2) := by
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hTr
  have hL : (1 / 2 : ℝ) ≤ Real.log T := hlog2.trans hlogT
  have hLpos : 0 < Real.log T := by linarith
  have hsL : (1 / 2 : ℝ) ≤ Real.sqrt (Real.log T) := by
    have hs := Real.sq_sqrt hLpos.le
    have hn := Real.sqrt_nonneg (Real.log T)
    nlinarith
  have hsq : (1 / 4 : ℝ) ≤ Real.log T ^ 2 := by nlinarith
  have hprod : (1 / 8 : ℝ) ≤ Real.sqrt (Real.log T) * Real.log T ^ 2 := by
    have h := mul_le_mul hsL hsq (by norm_num : (0:ℝ) ≤ 1/4) (Real.sqrt_nonneg (Real.log T))
    norm_num at h ⊢
    exact h
  have hpow : Real.sqrt (Real.log T) * Real.log T ^ 2 = Real.log T ^ ((5 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_add hLpos]
    norm_num
  rw [hpow] at hprod
  have hsT : 1 ≤ Real.sqrt (T : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith)
  exact hprod.trans (le_mul_of_one_le_left (Real.rpow_nonneg hLpos.le _) hsT)

private lemma main_failure_one_le (T : ℕ) (hT : 2 ≤ T) :
    (1 : ℝ) ≤ 8 * Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2) := by
  have h := main_rate_ge_constant T hT
  nlinarith

private lemma main_grid_error_le_main {c0 : ℝ} (hc0 : 0 < c0) {T : ℕ} (hT : 2 ≤ T)
    (hK : 2 ≤ Kpar c0 T) :
    2 * (T : ℝ) / Kpar c0 T ≤ (32 / c0) * Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2) := by
  calc
    _ ≤ (4 / c0) * (Real.sqrt T * Real.log (2 * T)) := by
      simpa only [mul_assoc] using main_grid_error_le hc0 hT hK
    _ ≤ (4 / c0) * (8 * Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (initialization_rate_le_main T hT) (by positivity)
    _ = _ := by ring

private lemma main_short_horizon_cost_le_main {c0 : ℝ} (hc0 : 0 < c0) {T : ℕ} (hT : 2 ≤ T)
    (hK : Kpar c0 T < 2) :
    (T : ℝ) ≤ (16 / c0) * Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2) := by
  calc
    _ ≤ (2 / c0) * (Real.sqrt T * Real.log (2 * T)) := by
      simpa only [mul_assoc] using main_short_horizon_cost hc0 hT hK
    _ ≤ (2 / c0) * (8 * Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (initialization_rate_le_main T hT) (by positivity)
    _ = _ := by ring






end BilateralProfitMHR
end BundlePart013


section BundlePart014



noncomputable section

namespace BilateralProfitMHR

open BilateralProfit MeasureTheory Set
open scoped ENNReal

private def mhrMainRate (T : ℕ) : ℝ :=
  Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2)

private theorem mhrMainRate_nonneg (T : ℕ) (hT : 2 ≤ T) : 0 ≤ mhrMainRate T :=
  (show (0 : ℝ) ≤ 1 / 8 by norm_num).trans (main_rate_ge_constant T hT)

private theorem mhr_intTriangle_subset_square : intT ⊆ unitSq := by
  intro x hx
  change 0 < x.1 ∧ x.1 < x.2 ∧ x.2 < 1 at hx
  exact ⟨⟨hx.1.le, (hx.2.1.trans hx.2.2).le⟩,
    ⟨(hx.1.trans hx.2.1).le, hx.2.2.le⟩⟩

private theorem controllerPolicy_oneBit {Ω S : Type} [MeasurableSpace Ω] (T : ℕ)
    (act : Ω → S → ℝ × ℝ) (step : Ω → S → Bool → S) (sinit : Ω → S)
    (hlegal : ∀ ω s, act ω s ∈ unitSq)
    (hmeas : ∀ t (h : Fin t → Bool),
      Measurable fun ω => act ω (binaryRunState step sinit t h ω)) :
    (controllerPolicy T act step sinit hlegal hmeas).OneBit := by
  intro t ω h h' hh
  have hb : (fun i => (h i).1 && (h i).2) = (fun i => (h' i).1 && (h' i).2) :=
    funext hh
  change act ω (binaryRunState step sinit t _ ω) =
    act ω (binaryRunState step sinit t _ ω)
  rw [hb]

private theorem measurable_profitGap (D : Measure (ℝ × ℝ)) (hD : Measurable (Ptrade D))
    (M : ℝ) : Measurable fun x => ENNReal.ofReal (M - muP D x) :=
  (measurable_const.sub ((measurable_snd.sub measurable_fst).mul hD)).ennreal_ofReal

private theorem optCost_le_of_price_bound {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure (ℝ × ℝ)) (hq : ∀ x, Ptrade D x ∈ Icc 0 1)
    (g : ℝ × ℝ → ℝ≥0∞) (A : QueryAlg (ℝ × ℝ) Ω) (B : ℝ≥0∞)
    (hA : ∀ t ω y, g (A.query t ω y) ≤ B) (b : ℕ) :
    optCost P D g A b ≤ (b : ℝ≥0∞) * B := by
  unfold optCost
  calc
    _ ≤ ∫⁻ _ : Ω, (b : ℝ≥0∞) * B ∂P :=
      lintegral_mono fun ω =>
        binaryValue_le_linear (Ptrade D) g (waitPrice A ω) (waitNext A ω) B
          (fun s => hq _) (fun s => hA s.completed ω s.observations) b waitEmpty
    _ = _ := by simp

private theorem optCost_rate_of_region {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : QueryAlg (ℝ × ℝ) Ω)
    (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    {c0 : ℝ} (hc0 : 0 < c0) {T : ℕ} (hT : 2 ≤ T)
    (hK : 2 ≤ Kpar c0 T) (hKT : Kpar c0 T ≤ T)
    {b : ℕ} (hb : 1 ≤ b) (hbT : b ≤ T)
    (δ : ℝ) (hδ : 1 / (Kpar c0 T : ℝ) ≤ δ)
    (R : Set (ℝ × ℝ)) (hR : R ⊆ intT) (hA : A.IsOn R)
    (hsafe : ∀ x ∈ R, δ / 2 ≤ muP D x ∧ muP D x ≤ 6 * δ)
    (xstar : ℝ × ℝ) (hxstar : xstar ∈ R) (hmax : ∀ x ∈ R, muP D x ≤ muP D xstar)
    (M C : ℝ) (hnear : M - muP D xstar ≤ 2 / (Kpar c0 T : ℝ)) (hC : 0 ≤ C)
    (hreg : expectedCumLoss A P (oracleKernel D)
      (fun x => ENNReal.ofReal (Real.log (sSup (muP D '' R) / muP D x))) b ≤
      ENNReal.ofReal (C * Real.sqrt (b * Real.log T) * Real.log (2 * b) ^ 2)) :
    optCost P D (fun x => ENNReal.ofReal (M - muP D x)) A b ≤
      ENNReal.ofReal ((32 / c0 + 48 * C) * mhrMainRate T) := by
  refine (optPhysical_bound D P A T (Kpar c0 T) b hK hKT hb hbT δ hδ R
    (hR.trans mhr_intTriangle_subset_square) hA hsafe xstar hxstar hmax M C
    hnear hC hreg).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hcast : (b : ℝ) ≤ T := by exact_mod_cast hbT
  have hgrid : 2 * (b : ℝ) / (Kpar c0 T : ℝ) ≤ (32 / c0) * mhrMainRate T :=
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcast (by norm_num)) (Nat.cast_nonneg _)).trans
      (by simpa only [mhrMainRate, mul_assoc] using main_grid_error_le_main hc0 hT hK)
  have hopt : Real.sqrt (b * Real.log T) * Real.log (2 * b) ^ 2 ≤ 4 * mhrMainRate T :=
    by simpa only [mhrMainRate, mul_assoc] using optimization_rate_le_main T b hT hb hbT
  calc
    _ ≤ (32 / c0) * mhrMainRate T + (12 * C) * (4 * mhrMainRate T) :=
      add_le_add hgrid (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hopt (by positivity))
    _ = _ := by ring

private theorem main_phase_budget (T : ℕ) (hT : 2 ≤ T) (CI C c0 : ℝ)
    (hC : 0 ≤ C) (hc0 : 0 < c0) :
    ENNReal.ofReal (CI * Real.sqrt T * Real.log T) +
        ENNReal.ofReal ((32 / c0 + 48 * C) * mhrMainRate T) + 1 ≤
      ENNReal.ofReal ((8 * max CI 0 + 32 / c0 + 48 * C + 8) * mhrMainRate T) := by
  have hrate := mhrMainRate_nonneg T hT
  have hlog : 0 ≤ Real.log (T : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T))
  have hlog' : Real.log (T : ℝ) ≤ Real.log (2 * T) :=
    Real.log_le_log (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) T])
  have hinit : CI * Real.sqrt T * Real.log T ≤ (8 * max CI 0) * mhrMainRate T := by
    calc
      _ ≤ max CI 0 * (Real.sqrt T * Real.log T) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max CI 0 * (Real.sqrt T * Real.log (2 * T)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog' (Real.sqrt_nonneg _))
          (le_max_right _ _)
      _ ≤ max CI 0 * (8 * mhrMainRate T) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [mhrMainRate, mul_assoc] using initialization_rate_le_main T hT)
          (le_max_right _ _)
      _ = _ := by ring
  have hbad : (1 : ℝ) ≤ 8 * mhrMainRate T :=
    by simpa only [mhrMainRate, mul_assoc] using main_failure_one_le T hT
  calc
    _ ≤ ENNReal.ofReal ((8 * max CI 0) * mhrMainRate T) +
        ENNReal.ofReal ((32 / c0 + 48 * C) * mhrMainRate T) +
        ENNReal.ofReal (8 * mhrMainRate T) :=
      add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hinit) le_rfl)
        (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hbad)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end BilateralProfitMHR
end
end BundlePart014


section BundlePart015





noncomputable section

namespace BilateralProfitMHR

open MeasureTheory ProbabilityTheory BilateralProfit MechanismDesign.BilateralTrade Set
open scoped ENNReal

private structure OptWitness (T K : ℕ) (C : ℝ) (r : InitTreeResult) where
  Seed : Type
  seedMeasurable : MeasurableSpace Seed
  law : @Measure Seed seedMeasurable
  probability : @IsProbabilityMeasure Seed seedMeasurable law
  alg : @QueryAlg (ℝ × ℝ) Seed inferInstance seedMeasurable
  square : ∀ τ ω y, alg.query τ ω y ∈ unitSq
  ordered : ∀ τ ω y, (alg.query τ ω y).1 ≤ (alg.query τ ω y).2
  no_trigger : r.2 = none → ∀ τ ω y, alg.query τ ω y = (0, 0)
  good : ∀ h R, r.2 = some (h, R) → 1 ≤ T - r.1 → 1 / (K : ℝ) ≤ delta h →
    R.Nonempty → IsCompact R → Convex ℝ R → R ⊆ intT →
    alg.IsOn R ∧
      ∀ E : Environment, UnitSupport E → IsMHR E →
        (∀ x ∈ R, delta h / 2 ≤ muP E.prior x ∧ muP E.prior x ≤ 6 * delta h) →
        expectedCumLoss alg law (oracleKernel E.prior)
            (fun x => ENNReal.ofReal (lossL E.prior x - sInf (lossL E.prior '' R))) (T - r.1) =
          expectedCumLoss alg law (oracleKernel E.prior)
            (fun x => ENNReal.ofReal (Real.log (sSup (muP E.prior '' R) / muP E.prior x))) (T - r.1) ∧
        expectedCumLoss alg law (oracleKernel E.prior)
            (fun x => ENNReal.ofReal (lossL E.prior x - sInf (lossL E.prior '' R))) (T - r.1) ≤
          ENNReal.ofReal (C * Real.sqrt (((T - r.1 : ℕ) : ℝ) * Real.log T) * Real.log (2 * ((T - r.1 : ℕ) : ℝ)) ^ 2) ∧
        expectedCumLoss alg law (oracleKernel E.prior)
            (fun x => ENNReal.ofReal (Real.log (sSup (muP E.prior '' R) / muP E.prior x))) (T - r.1) ≤
          ENNReal.ofReal (C * Real.sqrt (((T - r.1 : ℕ) : ℝ) * Real.log T) * Real.log (2 * ((T - r.1 : ℕ) : ℝ)) ^ 2)

attribute [instance] OptWitness.seedMeasurable OptWitness.probability

private def zeroQuery : QueryAlg (ℝ × ℝ) Unit where
  query _ _ _ := (0, 0)
  query_measurable _ := measurable_const

private theorem intT_square_of_mem {x : ℝ × ℝ} (hx : x ∈ intT) : x ∈ unitSq := by
  exact ⟨⟨hx.1.le, by linarith [hx.2.1, hx.2.2]⟩,
    ⟨by linarith [hx.1, hx.2.1], hx.2.2.le⟩⟩

private theorem optWitnesses_exist :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T K : ℕ, 2 ≤ K → K ≤ T →
      ∀ r : InitTreeResult, Nonempty (OptWitness T K C r) := by
  classical
  obtain ⟨C0, hC0⟩ := lemma_5_6
  refine ⟨max C0 0, le_max_right _ _, ?_⟩
  intro T K hK hKT r
  let Valid : Prop := ∃ h R, r.2 = some (h, R) ∧ 1 ≤ T - r.1 ∧ 1 / (K : ℝ) ≤ delta h ∧
    R.Nonempty ∧ IsCompact R ∧ Convex ℝ R ∧ R ⊆ intT
  by_cases hv : Valid
  · obtain ⟨h, R, hr, hb, hδ, hne, hc, hcv, hi⟩ := hv
    obtain ⟨Ω, mΩ, P, hp, A, hA, hreg⟩ := hC0 T K hK hKT (delta h) hδ R hne hc hcv hi
      (T - r.1) hb
    refine ⟨{
      Seed := Ω
      seedMeasurable := mΩ
      law := P
      probability := hp
      alg := A
      square := fun τ ω y => intT_square_of_mem (hi (hA τ ω y))
      ordered := fun τ ω y => (hi (hA τ ω y)).2.1.le
      no_trigger := by intro hnone; rw [hr] at hnone; contradiction
      good := ?_
    }⟩
    intro h' R' hr' hb' hδ' hne' hc' hcv' hi'
    have heq : (h, R) = (h', R') := Option.some.inj (hr.symm.trans hr')
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    refine ⟨hA, ?_⟩
    intro E hE hM hsafe
    obtain ⟨he, hbound⟩ := hreg E hE hM hsafe
    have henlarge : ENNReal.ofReal (C0 * Real.sqrt (((T - r.1 : ℕ) : ℝ) * Real.log T) *
        Real.log (2 * ((T - r.1 : ℕ) : ℝ)) ^ 2) ≤
        ENNReal.ofReal (max C0 0 * Real.sqrt (((T - r.1 : ℕ) : ℝ) * Real.log T) *
          Real.log (2 * ((T - r.1 : ℕ) : ℝ)) ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C0 0) (Real.sqrt_nonneg _)) (sq_nonneg _)
    refine ⟨he, hbound.trans henlarge, ?_⟩
    exact he.symm.trans_le (hbound.trans henlarge)
  · refine ⟨{
      Seed := Unit
      seedMeasurable := inferInstance
      law := Measure.dirac ()
      probability := inferInstance
      alg := zeroQuery
      square := by intro τ ω y; norm_num [zeroQuery, unitSq]
      ordered := by intro τ ω y; exact le_rfl
      no_trigger := by intro _ τ ω y; rfl
      good := ?_
    }⟩
    intro h R hr hb hδ hne hc hcv hi
    exact (hv ⟨h, R, hr, hb, hδ, hne, hc, hcv, hi⟩).elim

private def QueryAlg.pullSeed {X Ω Ω' : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (A : QueryAlg X Ω) (f : Ω' → Ω) (hf : Measurable f) : QueryAlg X Ω' where
  query τ ω y := A.query τ (f ω) y
  query_measurable τ := (A.query_measurable τ).comp (hf.comp measurable_fst |>.prodMk measurable_snd)

private theorem QueryAlg.pullSeed_isOn {X Ω Ω' : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (A : QueryAlg X Ω) (f : Ω' → Ω) (hf : Measurable f)
    (R : Set X) (hA : A.IsOn R) : (A.pullSeed f hf).IsOn R := by
  intro τ ω y
  exact hA τ (f ω) y

private def OptWitness.productSeed {T K : ℕ} {C : ℝ} (W : ∀ r, OptWitness T K C r) : Type :=
  ∀ r : InitTreeResult, (W r).Seed

private instance OptWitness.productSeedMeasurable {T K : ℕ} {C : ℝ} (W : ∀ r, OptWitness T K C r) :
    MeasurableSpace (OptWitness.productSeed W) := inferInstanceAs (MeasurableSpace (∀ r, (W r).Seed))

private def OptWitness.productLaw {T K : ℕ} {C : ℝ} (W : ∀ r, OptWitness T K C r) :
    Measure (OptWitness.productSeed W) := Measure.infinitePi (fun r => (W r).law)

private instance OptWitness.productLaw_probability {T K : ℕ} {C : ℝ} (W : ∀ r, OptWitness T K C r) :
    IsProbabilityMeasure (OptWitness.productLaw W) := by
  letI : ∀ r, IsProbabilityMeasure (W r).law := fun r => (W r).probability
  unfold OptWitness.productLaw
  exact Measure.instIsProbabilityMeasureForallInfinitePi (fun r => (W r).law)

private theorem OptWitness.product_eval_preserving {T K : ℕ} {C : ℝ}
    (W : ∀ r, OptWitness T K C r) (r : InitTreeResult) :
    MeasurePreserving (fun ω : OptWitness.productSeed W => ω r)
      (OptWitness.productLaw W) (W r).law := by
  letI : ∀ r, IsProbabilityMeasure (W r).law := fun r => (W r).probability
  exact measurePreserving_eval_infinitePi (fun r => (W r).law) r

private def OptWitness.productAlg {T K : ℕ} {C : ℝ} (W : ∀ r, OptWitness T K C r) (r : InitTreeResult) :
    QueryAlg (ℝ × ℝ) (OptWitness.productSeed W) :=
  (W r).alg.pullSeed (fun ω => ω r) (by fun_prop)

private theorem OptWitness.productAlg_square {T K : ℕ} {C : ℝ}
    (W : ∀ r, OptWitness T K C r) (r : InitTreeResult) :
    ∀ τ ω y, (OptWitness.productAlg W r).query τ ω y ∈ unitSq := by
  intro τ ω y
  exact (W r).square τ (ω r) y

private theorem OptWitness.productAlg_ordered {T K : ℕ} {C : ℝ}
    (W : ∀ r, OptWitness T K C r) (r : InitTreeResult) :
    ∀ τ ω y, ((OptWitness.productAlg W r).query τ ω y).1 ≤
      ((OptWitness.productAlg W r).query τ ω y).2 := by
  intro τ ω y
  exact (W r).ordered τ (ω r) y

private theorem OptWitness.productAlg_none {T K : ℕ} {C : ℝ}
    (W : ∀ r, OptWitness T K C r) (r : InitTreeResult) (hr : r.2 = none) :
    ∀ τ ω y, (OptWitness.productAlg W r).query τ ω y = (0, 0) := by
  intro τ ω y
  exact (W r).no_trigger hr τ (ω r) y



end BilateralProfitMHR
end
end BundlePart015


section BundlePart016



namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade Set
open scoped ENNReal

variable {T : ℕ} {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']

private def Policy.pullSeed (π : Policy T Ω) (f : Ω' → Ω) (hf : Measurable f) : Policy T Ω' where
  price t ω h := π.price t (f ω) h
  price_mem t ω h := π.price_mem t (f ω) h
  price_measurable t h := (π.price_measurable t h).comp hf

private theorem Policy.pullSeed_oneBit (π : Policy T Ω) (hπ : π.OneBit)
    (f : Ω' → Ω) (hf : Measurable f) : (π.pullSeed f hf).OneBit := by
  intro t ω h h' heq
  exact hπ t (f ω) h h' heq

private theorem Policy.hist_pullSeed (π : Policy T Ω) (f : Ω' → Ω) (hf : Measurable f)
    (ω : Ω') (v : Fin T → ℝ × ℝ) (t : ℕ) (ht : t ≤ T) :
    (π.pullSeed f hf).hist ω v t ht = π.hist (f ω) v t ht := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [Policy.hist, ih]
      rfl

private theorem Policy.runPrice_pullSeed (π : Policy T Ω) (f : Ω' → Ω) (hf : Measurable f)
    (ω : Ω') (v : Fin T → ℝ × ℝ) (t : Fin T) :
    (π.pullSeed f hf).runPrice ω v t = π.runPrice (f ω) v t := by
  unfold Policy.runPrice
  rw [Policy.hist_pullSeed]
  rfl

private theorem feedback_measurable :
    Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => feedback w.1 w.2) := by
  apply Measurable.prodMk
  · apply measurable_to_bool
    convert! (show MeasurableSet {w : (ℝ × ℝ) × (ℝ × ℝ) | w.1.1 ≤ w.2.1} from
      measurableSet_le measurable_fst.fst measurable_snd.fst) using 1
    ext w
    simp [feedback]
  · apply measurable_to_bool
    convert! (show MeasurableSet {w : (ℝ × ℝ) × (ℝ × ℝ) | w.2.2 ≤ w.1.2} from
      measurableSet_le measurable_snd.snd measurable_fst.snd) using 1
    ext w
    simp [feedback]

private theorem Policy.price_joint_measurable (π : Policy T Ω) (t : Fin T) :
    Measurable (fun w : Ω × (Fin t → Bool × Bool) => π.price t w.1 w.2) :=
  measurable_from_prod_countable_left fun h => π.price_measurable t h

private theorem Policy.hist_measurable (π : Policy T Ω) (t : ℕ) (ht : t ≤ T) :
    Measurable (fun w : Ω × (Fin T → ℝ × ℝ) => π.hist w.1 w.2 t ht) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hh := ih (Nat.le_of_succ_le ht)
      have hp : Measurable (fun w : Ω × (Fin T → ℝ × ℝ) =>
          π.price ⟨t, by omega⟩ w.1 (π.hist w.1 w.2 t (by omega))) :=
        (π.price_joint_measurable ⟨t, by omega⟩).comp (measurable_fst.prodMk hh)
      have hb : Measurable (fun w : Ω × (Fin T → ℝ × ℝ) =>
          feedback (w.2 ⟨t, by omega⟩)
            (π.price ⟨t, by omega⟩ w.1 (π.hist w.1 w.2 t (by omega)))) := by
        have hm : Measurable (fun w : Ω × (Fin T → ℝ × ℝ) => w.2 ⟨t, by omega⟩) := by fun_prop
        exact feedback_measurable.comp (hm.prodMk hp)
      apply measurable_pi_lambda
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Policy.hist, Fin.snoc_last] using hb
      · simpa only [Policy.hist, Fin.snoc_castSucc, Function.comp_def] using (measurable_pi_apply j).comp hh

private theorem Policy.runPrice_measurable (π : Policy T Ω) (t : Fin T) :
    Measurable (fun w : Ω × (Fin T → ℝ × ℝ) => π.runPrice w.1 w.2 t) :=
  (π.price_joint_measurable t).comp (measurable_fst.prodMk (π.hist_measurable t t.isLt.le))

private theorem profit_joint_measurable :
    Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => profit w.1 w.2) := by
  unfold profit tradeBit
  apply Measurable.mul (by fun_prop)
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_le measurable_fst.fst measurable_snd.fst).inter
    (measurableSet_le measurable_snd.snd measurable_fst.snd)

private theorem Policy.realizedProfit_measurable (π : Policy T Ω) (t : Fin T) :
    Measurable (fun w : Ω × (Fin T → ℝ × ℝ) => profit (w.2 t) (π.runPrice w.1 w.2 t)) :=
  profit_joint_measurable.comp (((measurable_pi_apply t).comp measurable_snd).prodMk
    (π.runPrice_measurable t))

private theorem Policy.expProfit_pullSeed (π : Policy T Ω) (f : Ω' → Ω) (hf : Measurable f)
    (P' : Measure Ω') [SFinite P'] (P : Measure Ω) (hm : MeasurePreserving f P' P)
    (D : Measure (ℝ × ℝ)) [SigmaFinite D] (t : Fin T) :
    (π.pullSeed f hf).expProfit P' D t = π.expProfit P D t := by
  let Q := Measure.pi fun _ : Fin T => D
  haveI : SFinite Q := by dsimp [Q]; infer_instance
  have hprod := hm.prod (MeasurePreserving.id Q)
  unfold Policy.expProfit runLaw
  simp only [Policy.runPrice_pullSeed]
  rw [← hprod.map_eq, integral_map hprod.measurable.aemeasurable
    (π.realizedProfit_measurable t).aestronglyMeasurable]
  rfl

private theorem Policy.regret_pullSeed (π : Policy T Ω) (f : Ω' → Ω) (hf : Measurable f)
    (P' : Measure Ω') [SFinite P'] (P : Measure Ω) (hm : MeasurePreserving f P' P)
    (D : Measure (ℝ × ℝ)) [SigmaFinite D] (a : ℝ × ℝ) :
    (π.pullSeed f hf).regret P' D a = π.regret P D a := by
  simp only [Policy.regret, Policy.expProfit_pullSeed π f hf P' P hm D]

end BilateralProfitMHR
end BundlePart016


section BundlePart017



namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade Set

private def zeroPolicy (T : ℕ) : Policy T Unit where
  price _ _ _ := (0, 0)
  price_mem _ _ _ := by norm_num [unitSq]
  price_measurable _ _ := measurable_const

private theorem simultaneous_horizon_policies (Bound : ℕ → ℝ)
    (h : ∀ T : ℕ, 2 ≤ T →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ π : Policy T Ω, π.OneBit ∧
          ∀ E : Environment, UnitSupport E → IsMHR E →
            ∀ p q : ℝ, p ∈ Icc (0 : ℝ) 1 → q ∈ Icc (0 : ℝ) 1 →
              π.regret P E.prior (p, q) ≤ Bound T) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ π : (T : ℕ) → Policy T Ω, (∀ T, (π T).OneBit) ∧
        ∀ T : ℕ, 2 ≤ T → ∀ E : Environment, UnitSupport E → IsMHR E →
          ∀ p q : ℝ, p ∈ Icc (0 : ℝ) 1 → q ∈ Icc (0 : ℝ) 1 →
            (π T).regret P E.prior (p, q) ≤ Bound T := by
  classical
  have hall : ∀ T : ℕ,
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ π : Policy T Ω, π.OneBit ∧
          (2 ≤ T → ∀ E : Environment, UnitSupport E → IsMHR E →
            ∀ p q : ℝ, p ∈ Icc (0 : ℝ) 1 → q ∈ Icc (0 : ℝ) 1 →
              π.regret P E.prior (p, q) ≤ Bound T) := by
    intro T
    by_cases hT : 2 ≤ T
    · obtain ⟨Ω, mΩ, P, hP, π, hπ, hreg⟩ := h T hT
      exact ⟨Ω, mΩ, P, hP, π, hπ, fun _ => hreg⟩
    · refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance, zeroPolicy T, ?_, ?_⟩
      · intro t ω hs hs' heq
        rfl
      · intro hT'
        exact (hT hT').elim
  choose Ω mΩ P hP π hπ hreg using hall
  letI : ∀ T, MeasurableSpace (Ω T) := mΩ
  letI : ∀ T, IsProbabilityMeasure (P T) := hP
  let Q := Measure.infinitePi P
  let π' : (T : ℕ) → Policy T ((T : ℕ) → Ω T) :=
    fun T => (π T).pullSeed (Function.eval T) (by fun_prop)
  refine ⟨(T : ℕ) → Ω T, inferInstance, Q, inferInstance, π', ?_, ?_⟩
  · intro T
    exact Policy.pullSeed_oneBit (π T) (hπ T) _ _
  · intro T hT E hE hM p q hp hq
    letI := (positive_density_profit_facts E hE).1
    change ((π T).pullSeed (Function.eval T) _).regret Q E.prior (p, q) ≤ Bound T
    rw [Policy.regret_pullSeed (π T) (Function.eval T) (by fun_prop)
      Q (P T) (measurePreserving_eval_infinitePi P T) E.prior]
    exact hreg T hT E hE hM p q hp hq


end BilateralProfitMHR
end BundlePart017


section BundlePart018






noncomputable section

namespace BilateralProfitMHR

open BilateralProfit MechanismDesign.BilateralTrade MeasureTheory Set
open scoped ENNReal

private theorem short_grid_policy {T : ℕ} (hT : 2 ≤ T)
    {c0 C : ℝ} (hc0 : 0 < c0) (hC : 16 / c0 ≤ C) (hK : Kpar c0 T < 2) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ π : Policy T Ω, π.OneBit ∧
        ∀ E : Environment, UnitSupport E → IsMHR E →
          ∀ p q : ℝ, p ∈ Icc (0 : ℝ) 1 → q ∈ Icc (0 : ℝ) 1 →
            π.regret P E.prior (p, q) ≤ C * mhrMainRate T := by
  let P : Measure Unit := Measure.dirac ()
  let act : Unit → Unit → ℝ × ℝ := fun _ _ => (0, 0)
  let step : Unit → Unit → Bool → Unit := fun _ _ _ => ()
  let sinit : Unit → Unit := fun _ => ()
  have hlegal (ω s : Unit) : act ω s ∈ unitSq := by norm_num [act, unitSq]
  have hmeas (t : ℕ) (h : Fin t → Bool) :
      Measurable fun ω => act ω (binaryRunState step sinit t h ω) := measurable_const
  haveI : IsProbabilityMeasure P := Measure.dirac.isProbabilityMeasure
  refine ⟨Unit, inferInstance, P, inferInstance, controllerPolicy T act step sinit hlegal hmeas,
    controllerPolicy_oneBit T act step sinit hlegal hmeas, ?_⟩
  intro E hE _ p q hp hq
  obtain ⟨hprob, _, hprobBounds, _, _, _, _, _, _, hstar, hle, _⟩ :=
    positive_density_profit_facts E hE
  letI := hprob
  let M := muStar E.prior
  let g : ℝ × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (M - muP E.prior x)
  have hbound (ω : Unit) :
      binaryValue (Ptrade E.prior) g (act ω) (step ω) T (sinit ω) ≤ (T : ℝ≥0∞) := by
    have hcost (s : Unit) : g (act ω s) ≤ 1 := by
      have h := ENNReal.ofReal_le_ofReal hstar.2
      simpa [g, M, act, muP] using h
    simpa using binaryValue_le_linear (Ptrade E.prior) g (act ω) (step ω) 1
      (fun s => hprobBounds _) hcost T (sinit ω)
  have hvalue : (∫⁻ ω, binaryValue (Ptrade E.prior) g (act ω) (step ω) T (sinit ω) ∂P) ≤
      ENNReal.ofReal (T : ℝ) := by
    simpa only [lintegral_const, measure_univ, mul_one, ENNReal.ofReal_natCast] using
      (lintegral_mono hbound (μ := P))
  have hactual := (binary_controller_regret_bridge T P E.prior act step sinit hlegal hmeas).2
    M (fun ω s => hle _ (hlegal ω s)) (p, q) (hle _ ⟨hp, hq⟩)
  have hvalue' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvalue
  rw [ENNReal.toReal_ofReal (Nat.cast_nonneg _)] at hvalue'
  exact hactual.trans (hvalue'.trans
    ((by simpa only [mhrMainRate, mul_assoc] using main_short_horizon_cost_le_main hc0 hT hK :
      (T : ℝ) ≤ (16 / c0) * mhrMainRate T).trans
        (mul_le_mul_of_nonneg_right hC (mhrMainRate_nonneg T hT))))

private theorem theorem_5_1_regret_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P ∧ ∃ π : (T : ℕ) → Policy T Ω, (∀ T, (π T).OneBit) ∧
        ∀ T : ℕ, 2 ≤ T → ∀ E : Environment, UnitSupport E → IsMHR E →
          ∀ p q : ℝ, p ∈ Set.Icc (0 : ℝ) 1 → q ∈ Set.Icc (0 : ℝ) 1 →
            (π T).regret P E.prior (p, q) ≤
              C * Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2) := by
  classical
  obtain ⟨hGeometry, c0, CI, hc0, hc0half, hInit⟩ := lemma_5_3
  obtain ⟨CQ, hCQ, hWitness⟩ := optWitnesses_exist
  let C := 8 * max CI 0 + 32 / c0 + 48 * CQ + 8
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hForT : ∀ T : ℕ, 2 ≤ T →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ π : Policy T Ω, π.OneBit ∧
          ∀ E : Environment, UnitSupport E → IsMHR E →
            ∀ p q : ℝ, p ∈ Icc (0 : ℝ) 1 → q ∈ Icc (0 : ℝ) 1 →
              π.regret P E.prior (p, q) ≤ C * mhrMainRate T := by
    intro T hT
    by_cases hK : 2 ≤ Kpar c0 T
    swap
    · have hCsmall : 16 / c0 ≤ C := by
        dsimp [C]
        have hdiv : (16 : ℝ) / c0 ≤ 32 / c0 :=
          div_le_div_of_nonneg_right (by norm_num) hc0.le
        linarith [le_max_right CI (0 : ℝ)]
      exact short_grid_policy hT hc0 hCsmall (by omega)
    let K := Kpar c0 T
    have hKpos : 0 < K := by change 0 < Kpar c0 T; omega
    have hKT : K ≤ T := main_grid_le_horizon hc0 hc0half hT
    let W : ∀ r, OptWitness T K CQ r :=
      fun r => Classical.choice (hWitness T K hK hKT r)
    let P := OptWitness.productLaw W
    let A := OptWitness.productAlg W
    let price := initSamplePrice (K := K) (T := T)
    let tree := initTree K T
    let act := tradeControlPrice price A
    let step := tradeControlNext A (I := SampleIdx K T)
    let sinit : OptWitness.productSeed W → TradeControlState (SampleIdx K T) InitTreeResult :=
      fun _ => enterTradeControl tree
    have hlegal (ω : OptWitness.productSeed W) (s : TradeControlState (SampleIdx K T) InitTreeResult) :
        act ω s ∈ unitSq := by
      cases s with
      | probe i _ _ => exact initSamplePrice_mem_unitSq hKpos i
      | wait r w => exact OptWitness.productAlg_square W r w.completed ω w.observations
    have hmeas (t : ℕ) (h : Fin t → Bool) :
        Measurable fun ω => act ω (binaryRunState step sinit t h ω) :=
      tradeControlPrice_measurable price A (tradeControl_fixed_history A tree t h)
    letI : IsProbabilityMeasure P := OptWitness.productLaw_probability W
    refine ⟨OptWitness.productSeed W, inferInstance, P, inferInstance,
      controllerPolicy T act step sinit hlegal hmeas,
      controllerPolicy_oneBit T act step sinit hlegal hmeas, ?_⟩
    intro E hE hM p q hp hq
    obtain ⟨hprob, hmP, hprobBounds, _, _, _, _, _, _, hstar, hle, _⟩ :=
      positive_density_profit_facts E hE
    letI := hprob
    let M := muStar E.prior
    let g : ℝ × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (M - muP E.prior x)
    have hg : Measurable g := measurable_profitGap E.prior hmP M
    let finish := fun b r => optCost P E.prior g (A r) b
    let I := ENNReal.ofReal (CI * Real.sqrt T * Real.log T)
    let B := ENNReal.ofReal ((32 / c0 + 48 * CQ) * mhrMainRate T)
    obtain ⟨hGeo, hClean⟩ := hGeometry T K hK hKT
    obtain ⟨G, hG, hGprob, hGout⟩ := hClean E hE hM
    obtain ⟨hround, hInitCost⟩ := hInit T hK
    have hfinish_all (b : ℕ) (r : InitTreeResult) : finish b r ≤ (b : ℝ≥0∞) := by
      have hprice (t : ℕ) (ω : OptWitness.productSeed W) (y : Fin t → ℝ) :
          g ((A r).query t ω y) ≤ 1 := by
        have hmu : 0 ≤ muP E.prior ((A r).query t ω y) :=
          mul_nonneg (sub_nonneg.mpr (OptWitness.productAlg_ordered W r t ω y))
            (hprobBounds _).1
        have h := ENNReal.ofReal_le_ofReal (sub_le_self M hmu |>.trans hstar.2)
        simpa only [g, ENNReal.ofReal_one] using h
      simpa only [finish, mul_one] using
        optCost_le_of_price_bound P E.prior hprobBounds g (A r) 1 hprice b
    have hfinish_none (b t : ℕ) :
        finish b (t, none) ≤ ENNReal.ofReal ((b : ℝ) * M) := by
      have hprice (n : ℕ) (ω : OptWitness.productSeed W) (y : Fin n → ℝ) :
          g ((A (t, none)).query n ω y) ≤ ENNReal.ofReal M := by
        simpa [g, muP, A, OptWitness.productAlg_none W (t, none) rfl n ω y]
      refine (optCost_le_of_price_bound P E.prior hprobBounds g (A (t, none)) _ hprice b).trans_eq ?_
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have hfinish_good (ω : Samples K T) (hω : ω ∈ G) (h : ℕ) (R : Set (ℝ × ℝ))
        (hout : initOut K T ω = some (h, R)) :
        finish (T - initRounds K T ω) (initRounds K T ω, some (h, R)) ≤ B := by
      let r : InitTreeResult := (initRounds K T ω, some (h, R))
      let b := T - r.1
      change optCost P E.prior g (A r) b ≤ B
      by_cases hb : 1 ≤ b
      swap
      · have hbzero : b = 0 := by omega
        simp [hbzero, optCost, binaryValue]
      have hbT : b ≤ T := Nat.sub_le _ _
      obtain ⟨hne, hc, hcv, hi⟩ := hGeo ω h R hout
      obtain ⟨hscale, hLower, _, xstar, hxstar, hmax, hnear⟩ := (hGout ω hω).2 h R hout
      have hδ := init_delta_ge_inv hKpos (init_firstTrigger_spec (initOut_some hout).1).1
      have hsafe (x : ℝ × ℝ) (hx : x ∈ R) :
          delta h / 2 ≤ muP E.prior x ∧ muP E.prior x ≤ 6 * delta h :=
        ⟨(hLower x hx).1, (hle x (mhr_intTriangle_subset_square (hi hx))).trans hscale.2.le⟩
      obtain ⟨hA, hbandit⟩ := (W r).good h R rfl hb hδ hne hc hcv hi
      have hpull : optCost P E.prior g (A r) b = optCost (W r).law E.prior g (W r).alg b :=
        optCost_pull_seed (OptWitness.product_eval_preserving W r) E.prior hmP hg (W r).alg b
      rw [hpull]
      exact optCost_rate_of_region (W r).law (W r).alg E.prior hc0 hT hK hKT hb hbT
        (delta h) hδ R hi hA hsafe xstar hxstar hmax M CQ (by dsimp [M]; linarith)
        hCQ (hbandit E hE hM hsafe).2.2
    have hvalue : (∫⁻ ω, binaryValue (Ptrade E.prior) g (act ω) (step ω) T (sinit ω) ∂P) ≤
        I + B + 1 := by
      change (∫⁻ ω, binaryValue (Ptrade E.prior) g
        (tradeControlPrice price A ω) (tradeControlNext A ω) T (enterTradeControl tree) ∂P) ≤ _
      rw [tradeControl_lintegral P E.prior g hmP hg price A T tree]
      exact initializer_then_cost_bound hT hK E hE finish I B hround G hG hGprob
        (hInitCost E hE hM).2 hfinish_all hfinish_none hfinish_good
    have hvalue' := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hvalue.trans (main_phase_budget T hT CI CQ c0 hCQ hc0))
    rw [ENNReal.toReal_ofReal (mul_nonneg hC.le (mhrMainRate_nonneg T hT))] at hvalue'
    exact ((binary_controller_regret_bridge T P E.prior act step sinit hlegal hmeas).2
      M (fun ω s => hle _ (hlegal ω s)) (p, q) (hle _ ⟨hp, hq⟩)).trans hvalue'
  simpa only [mhrMainRate, mul_assoc] using simultaneous_horizon_policies _ hForT


end BilateralProfitMHR
end
end BundlePart018

open MeasureTheory ProbabilityTheory BilateralProfit BilateralProfitMHR MechanismDesign.BilateralTrade Set
open scoped ENNReal

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P ∧ ∃ π : (T : ℕ) → Policy T Ω, (∀ T, (π T).OneBit) ∧
        ∀ T : ℕ, 2 ≤ T → ∀ E : Environment, UnitSupport E → IsMHR E →
          ∀ p q : ℝ, p ∈ Set.Icc (0 : ℝ) 1 → q ∈ Set.Icc (0 : ℝ) 1 →
            (π T).regret P E.prior (p, q) ≤
              C * Real.sqrt T * Real.log T ^ ((5 : ℝ) / 2) := by
  exact BilateralProfitMHR.theorem_5_1_regret_bound
