-- Prove2me | solution 1 for BilateralProfitMHR.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T11:58:13.068417+00:00
-- url     : https://prove2.me/submissions/125c26ec-f172-4e31-9e4e-b32349d7372b

import Mathlib
import Definitions.Def_BilateralProfitMHR_InitializeMHR
import Theorems.Thm_BilateralProfitMHR_lemma_5_3

noncomputable section
namespace BilateralProfitMHR
open MeasureTheory BilateralProfit
private lemma ptrade_nonneg (D : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : 0 ≤ Ptrade D a := ENNReal.toReal_nonneg
private lemma mu_nonneg {D : Measure (ℝ × ℝ)} {a : ℝ × ℝ} (ha : a.1 ≤ a.2) :
    0 ≤ muP D a := mul_nonneg (sub_nonneg.mpr ha) (ptrade_nonneg D a)


end BilateralProfitMHR


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

namespace BilateralProfitMHR
open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade
private theorem init_filterRegret_le_rounds {K T : ℕ} (hK : 0 < K) (E : Environment)
    (ω : Samples K T) :
    filterRegret K T E.prior ω ≤ (initRounds K T ω : ℝ) * muStar E.prior := by
  unfold filterRegret
  calc
    _ ≤ ∑ h ∈ testedScales K T ω, (nSamp T h : ℝ) *
        ∑ _z ∈ Spairs K, muStar E.prior := by
      apply Finset.sum_le_sum
      intro h hh
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro z hz
      have hz' := Spairs_bounds hz
      have hnonneg : 0 ≤ muP E.prior ((z.1 : ℝ) / K, (z.2 : ℝ) / K) := by
        apply mu_nonneg
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast hz'.1
      linarith
    _ = _ := by
      simp only [initRounds, Nat.cast_sum, Nat.cast_mul, Finset.sum_const,
        nsmul_eq_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h hh
      ring

private theorem init_filterRegret_trigger_bound {K T h : ℕ} (hK : 2 ≤ K) (hKT : K ≤ T)
    (E : Environment) {ω : Samples K T} (hf : firstTrigger K T ω = some h)
    (hstar : muStar E.prior ≤ 6 * delta h) :
    filterRegret K T E.prior ω ≤ 4718664 * K * Real.log (2 * T) ^ 2 := by
  have hr := init_rounds_trigger_bound hK hKT hf
  have hδ := init_delta_pos h
  have hleft := init_filterRegret_le_rounds (by omega : 0 < K) E ω
  calc
    _ ≤ (initRounds K T ω : ℝ) * (6 * delta h) := by
      exact hleft.trans (mul_le_mul_of_nonneg_left hstar (Nat.cast_nonneg _))
    _ ≤ (786444 * K * Real.log (2 * T) ^ 2 / delta h) * (6 * delta h) := by gcongr
    _ = _ := by field_simp; ring


end BilateralProfitMHR

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal


private theorem lemma33_main :
    ∃ c C C' : ℝ, 0 < c ∧ c < C ∧ ∀ T K : ℕ, 2 ≤ K → K ≤ T →
      ∀ E : Environment, UnitSupport E → IsMHR E →
        ∃ G : Set (Samples K T), MeasurableSet G ∧ 1 - (T : ℝ≥0∞)⁻¹ ≤ initLaw K T E.prior G ∧
          ∀ ω ∈ G,
            (initOut K T ω = none ∧ muStar E.prior ≤ C / K) ∨
            ∃ (h : ℕ) (R : Set (ℝ × ℝ)), initOut K T ω = some (h, R) ∧ 1 / (K : ℝ) ≤ delta h ∧
              R.Nonempty ∧ IsCompact R ∧ Convex ℝ R ∧ R ⊆ intT ∧
              (∀ x ∈ R, c * delta h ≤ muP E.prior x) ∧
              (delta h ≤ muStar E.prior ∧ muStar E.prior ≤ C * delta h) ∧
              (∀ e : Act K, IsGridMax K E.prior e → pt K e.1 ∈ R) ∧
              (∃ x ∈ R, (∀ y ∈ R, muP E.prior y ≤ muP E.prior x) ∧
                muStar E.prior ≤ muP E.prior x + C / K) ∧
              filterRegret K T E.prior ω ≤ C' * K * Real.log (2 * T) ^ 2 := by
  refine ⟨1 / 2, 6, 4718664, by norm_num, by norm_num, ?_⟩
  intro T K hK hKT E hE hM
  obtain ⟨hgeom, hres⟩ := (BilateralProfitMHR.lemma_5_3).1 T K hK hKT
  obtain ⟨G, hm, hprob, hresults⟩ := hres E hE hM
  refine ⟨G, hm, hprob, ?_⟩
  intro ω hω
  have hgood := hresults ω hω
  cases ho : initOut K T ω with
  | none => exact Or.inl ⟨rfl, (hgood.1 ho).le⟩
  | some z =>
    rcases z with ⟨h, R⟩
    have hg := hgeom ω h R ho
    have hb := hgood.2 h R ho
    have hf := (initOut_some ho).1
    have hδK := init_delta_ge_inv (by omega : 0 < K) (init_firstTrigger_spec hf).1
    refine Or.inr ⟨h, R, rfl, hδK, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2,
      ?_, ⟨hb.1.1, hb.1.2.le⟩, hb.2.2.1, ?_, ?_⟩
    · intro x hx
      have hs := (hb.2.1 x hx).1
      linarith
    · obtain ⟨x, hx, hmax, happrox⟩ := hb.2.2.2
      refine ⟨x, hx, hmax, ?_⟩
      have hround : (2 : ℝ) / K ≤ 6 / K := by
        apply div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)
      linarith
    · exact init_filterRegret_trigger_bound hK hKT E hf hb.1.2.le


end BilateralProfitMHR
open BilateralProfitMHR MeasureTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal
theorem solution :
    ∃ c C C' : ℝ, 0 < c ∧ c < C ∧ ∀ T K : ℕ, 2 ≤ K → K ≤ T →
      ∀ E : Environment, UnitSupport E → IsMHR E →
        ∃ G : Set (Samples K T), MeasurableSet G ∧ 1 - (T : ℝ≥0∞)⁻¹ ≤ initLaw K T E.prior G ∧
          ∀ ω ∈ G,
            (initOut K T ω = none ∧ muStar E.prior ≤ C / K) ∨
            ∃ (h : ℕ) (R : Set (ℝ × ℝ)), initOut K T ω = some (h, R) ∧ 1 / (K : ℝ) ≤ delta h ∧
              R.Nonempty ∧ IsCompact R ∧ Convex ℝ R ∧ R ⊆ intT ∧
              (∀ x ∈ R, c * delta h ≤ muP E.prior x) ∧
              (delta h ≤ muStar E.prior ∧ muStar E.prior ≤ C * delta h) ∧
              (∀ e : Act K, IsGridMax K E.prior e → pt K e.1 ∈ R) ∧
              (∃ x ∈ R, (∀ y ∈ R, muP E.prior y ≤ muP E.prior x) ∧
                muStar E.prior ≤ muP E.prior x + C / K) ∧
              filterRegret K T E.prior ω ≤ C' * K * Real.log (2 * T) ^ 2 := BilateralProfitMHR.lemma33_main

