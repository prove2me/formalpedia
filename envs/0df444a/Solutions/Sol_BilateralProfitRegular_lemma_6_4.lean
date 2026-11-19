-- Prove2me | solution 1 for BilateralProfitRegular.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T15:48:28.767395+00:00
-- url     : https://prove2.me/submissions/ea148d8d-8915-4d02-89a0-0a0a7977aced

import Theorems.Thm_BilateralProfitMHR_positive_density_profit_facts
import Definitions.Def_BilateralProfitRegular_Stochastic
import Definitions.Def_BilateralProfitRegular_Auxiliary
import Definitions.Def_BilateralProfitRegular_InitRegular
import Definitions.Def_BilateralProfitMHR_InitializeMHR
import Mathlib
import Theorems.Thm_BilateralProfit_lemma_A_6


section BundlePart000




namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade BilateralProfit MeasureTheory

private theorem intT_subset_unitSq : intT ⊆ BilateralProfitMHR.unitSq := by
  intro x hx
  exact ⟨⟨hx.1.le, (hx.2.1.trans hx.2.2).le⟩,
    ⟨(hx.1.trans hx.2.1).le, hx.2.2.le⟩⟩

private theorem onUnit_facts (E : Environment) (hE : OnUnit E) :
    (∀ a, 0 ≤ P E a ∧ P E a ≤ 1) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, P E a = E.cdfS a.1 * (1 - E.cdfB a.2)) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, 0 < mu E a ↔ a ∈ intT) ∧
    (0 < muStar E ∧ muStar E ≤ 1) ∧
    (∀ a ∈ BilateralProfitMHR.unitSq, mu E a ≤ muStar E) ∧
    (∃ a ∈ intT, mu E a = muStar E) := by
  obtain ⟨_, _, hp, hf, _, _, _, _, hm, hs, hu, he, _⟩ :=
    BilateralProfitMHR.positive_density_profit_facts E hE
  exact ⟨hp, hf, hm, hs, hu, he⟩

private theorem P_factor (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ}
    (hx : x ∈ BilateralProfitMHR.unitSq) :
    P E x = E.cdfS x.1 * (1 - E.cdfB x.2) :=
  (onUnit_facts E hE).2.1 x hx

private theorem mu_formula (E : Environment) (x : ℝ × ℝ) :
    mu E x = (x.2 - x.1) * P E x := rfl

private theorem mu_le_muStar (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ}
    (hx : x ∈ BilateralProfitMHR.unitSq) : mu E x ≤ muStar E :=
  (onUnit_facts E hE).2.2.2.2.1 x hx

private theorem cdfS_pos (E : Environment) (hE : OnUnit E) {p : ℝ} (hp : p ∈ Ioc 0 1) :
    0 < E.cdfS p := by
  have hf := E.fS_intervalIntegrable
  rw [hE.1, hE.2.1] at hf
  unfold Environment.cdfS
  rw [hE.1]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hp.1
  · apply hf.mono_set
    rw [uIcc_of_le hp.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hp.2
  · intro t ht
    exact E.fS_pos t (by rw [hE.1, hE.2.1]; exact ⟨ht.1.le, ht.2.le.trans hp.2⟩)

private theorem tailB_eq_integral (E : Environment) (hE : OnUnit E) {q : ℝ} (hq : q ∈ Icc 0 1) :
    1 - E.cdfB q = ∫ t in q..1, E.fB t := by
  have hf := E.fB_intervalIntegrable
  have ht := E.fB_integral
  rw [hE.2.2.1, hE.2.2.2] at hf ht
  have h₁ := hf.mono_set (show uIcc 0 q ⊆ uIcc 0 1 by
    rw [uIcc_of_le hq.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hq.2)
  have h₂ := hf.mono_set (show uIcc q 1 ⊆ uIcc 0 1 by
    rw [uIcc_of_le hq.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hq.1 le_rfl)
  rw [Environment.cdfB, hE.2.2.1]
  linarith [intervalIntegral.integral_add_adjacent_intervals h₁ h₂]

private theorem tailB_pos (E : Environment) (hE : OnUnit E) {q : ℝ} (hq : q ∈ Ico 0 1) :
    0 < 1 - E.cdfB q := by
  rw [tailB_eq_integral E hE ⟨hq.1, hq.2.le⟩]
  have hf := E.fB_intervalIntegrable
  rw [hE.2.2.1, hE.2.2.2] at hf
  apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hq.2
  · apply hf.mono_set
    rw [uIcc_of_le hq.2.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hq.1 le_rfl
  · intro t ht
    exact E.fB_pos t (by rw [hE.2.2.1, hE.2.2.2]; exact ⟨hq.1.trans ht.1.le, ht.2.le⟩)

private theorem intT_cdf_pos (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 < E.cdfS x.1 ∧ 0 < 1 - E.cdfB x.2 :=
  ⟨cdfS_pos E hE ⟨hx.1, (intT_subset_unitSq hx).1.2⟩,
    tailB_pos E hE ⟨(intT_subset_unitSq hx).2.1, hx.2.2⟩⟩

private theorem balance_pos (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 < balance E x :=
  Real.sqrt_pos.2 (div_pos (intT_cdf_pos E hE hx).1 (intT_cdf_pos E hE hx).2)

private theorem balance_sq (E : Environment) (hE : OnUnit E) {x : ℝ × ℝ} (hx : x ∈ intT) :
    balance E x ^ 2 = E.cdfS x.1 / (1 - E.cdfB x.2) :=
  Real.sq_sqrt (div_pos (intT_cdf_pos E hE hx).1 (intT_cdf_pos E hE hx).2).le

private theorem auxProfit_pos (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) : 0 < auxProfit E lam x := by
  have hm := intT_cdf_pos E hE hx
  unfold auxProfit
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hx.2.1))
    (pow_pos (add_pos (div_pos hlam hm.1) (div_pos (inv_pos.mpr hlam) hm.2)) _)

private theorem eq_42 (E : Environment) (hE : RegularUnit E) (x z : ℝ × ℝ) (hx : x ∈ intT)
    (hz : z ∈ intT) (ρ : ℝ) (hρ : 0 < ρ) :
    1 / auxProfit E (ρ * balance E z) x =
      P E z / (4 * (x.2 - x.1)) * (ρ / P E (x.1, z.2) + ρ⁻¹ / P E (z.1, x.2)) ^ 2 := by
  have hX := intT_subset_unitSq hx
  have hZ := intT_subset_unitSq hz
  rw [P_factor E hE.1 hZ, P_factor E hE.1 (x := (x.1,z.2)) ⟨hX.1,hZ.2⟩,
    P_factor E hE.1 (x := (z.1,x.2)) ⟨hZ.1,hX.2⟩]
  have hsX := (intT_cdf_pos E hE.1 hx).1.ne'
  have hbX := (intT_cdf_pos E hE.1 hx).2.ne'
  have hsZ := (intT_cdf_pos E hE.1 hz).1.ne'
  have hbZ := (intT_cdf_pos E hE.1 hz).2.ne'
  have hlZ := (balance_pos E hE.1 hz).ne'
  have hs := balance_sq E hE.1 hz
  have hei : (balance E z)⁻¹ = balance E z * (1 - E.cdfB z.2) / E.cdfS z.1 := by
    apply inv_eq_of_mul_eq_one_left
    calc
      balance E z * (1 - E.cdfB z.2) / E.cdfS z.1 * balance E z =
          (balance E z ^ 2 * (1 - E.cdfB z.2)) / E.cdfS z.1 := by ring
      _ = 1 := by rw [hs, div_mul_cancel₀ _ hbZ, div_self hsZ]
  have he :
      ρ * balance E z / E.cdfS x.1 + (ρ * balance E z)⁻¹ / (1 - E.cdfB x.2) =
      (balance E z * (1 - E.cdfB z.2)) *
        (ρ / (E.cdfS x.1 * (1 - E.cdfB z.2)) + ρ⁻¹ / (E.cdfS z.1 * (1 - E.cdfB x.2))) := by
    rw [mul_inv, hei]
    field_simp
  have hsq : (balance E z * (1 - E.cdfB z.2)) ^ 2 =
      E.cdfS z.1 * (1 - E.cdfB z.2) := by
    rw [mul_pow, hs, pow_two, ← mul_assoc, div_mul_cancel₀ _ hbZ]
  simp only [auxProfit, one_div, inv_div]
  rw [he, mul_pow, hsq]
  ring

private theorem eq_47 (E : Environment) (hE : RegularUnit E) (x z : ℝ × ℝ) (hx : x ∈ intT)
    (hz : z ∈ intT) :
    Real.log (balance E x / balance E z) =
      1 / 2 * Real.log (P E (x.1, z.2) / P E (z.1, x.2)) := by
  have hX := intT_subset_unitSq hx
  have hZ := intT_subset_unitSq hz
  have hbX := (intT_cdf_pos E hE.1 hx).2.ne'
  have hsZ := (intT_cdf_pos E hE.1 hz).1.ne'
  have hbZ := (intT_cdf_pos E hE.1 hz).2.ne'
  have he : (balance E x / balance E z)^2 = P E (x.1, z.2) / P E (z.1, x.2) := by
    rw [div_pow, balance_sq E hE.1 hx, balance_sq E hE.1 hz,
      P_factor E hE.1 (x := (x.1,z.2)) ⟨hX.1,hZ.2⟩,
      P_factor E hE.1 (x := (z.1,x.2)) ⟨hZ.1,hX.2⟩]
    dsimp
    field_simp
  rw [← he, Real.log_pow]
  ring

end BilateralProfitRegular
end BundlePart000


section BundlePart001


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
end BundlePart001


section BundlePart002



namespace BilateralProfitRegular

private theorem bisect_toFinset (f m M : ℕ) :
    (bisect f m M).toFinset = BilateralProfitMHR.bisectAux f m M := by
  induction f generalizing m M with
  | zero => simp [bisect, BilateralProfitMHR.bisectAux]
  | succ f ih =>
    by_cases h : m < M <;> simp [bisect, BilateralProfitMHR.bisectAux, h, ih]

private theorem sampledPairs_toFinset (I : ℕ × ℕ) :
    (sampledPairs I).toFinset = BilateralProfitMHR.sPairsOf I := by
  ext e
  simp only [sampledPairs, List.mem_toFinset, List.mem_map, List.mem_filter,
    List.mem_range, decide_eq_true_eq, BilateralProfitMHR.sPairsOf, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨r, ⟨hr, hr'⟩, he⟩
    split at he <;> rename_i h
    · exact Or.inl ⟨r, ⟨⟨hr', by omega⟩, h⟩, he⟩
    · exact Or.inr ⟨r, ⟨⟨hr', by omega⟩, by omega⟩, he⟩
  · rintro (⟨r, ⟨⟨hr', hr⟩, h⟩, rfl⟩ | ⟨r, ⟨⟨hr', hr⟩, h⟩, rfl⟩)
    · exact ⟨r, ⟨by omega, hr'⟩, if_pos h⟩
    · exact ⟨r, ⟨by omega, hr'⟩, if_neg (Nat.not_le.mpr h)⟩

private theorem sampleSet_eq_MHR (K : ℕ) : sampleSet K = BilateralProfitMHR.Spairs K := by
  ext e
  simp only [sampleSet, List.mem_toFinset, List.mem_flatMap, BilateralProfitMHR.Spairs, Finset.mem_biUnion]
  simp_rw [← List.mem_toFinset]
  simp only [bisect_toFinset, sampledPairs_toFinset, BilateralProfitMHR.bisect]

private theorem sampleSet_bounds {K : ℕ} {e : ℕ × ℕ} (he : e ∈ sampleSet K) :
    e.1 ≤ e.2 ∧ e.2 ≤ K :=
  BilateralProfitMHR.Spairs_bounds (sampleSet_eq_MHR K ▸ he)

private theorem sepMid_eq_aux {f m M i j : ℕ} (hm : m ≤ i) (hij : i < j) (hM : j ≤ M) (hf : M - m + 1 ≤ f) :
    sepMid f m M i j = BilateralProfitMHR.sepMidAux f i j m M := by
  induction f generalizing m M with
  | zero => omega
  | succ f ih =>
    have hstrict : m < M := by omega
    simp only [sepMid, BilateralProfitMHR.sepMidAux, hstrict, if_true]
    split
    · rename_i hj
      exact ih hm hj (by omega)
    · split
      · rename_i hi
        exact ih (Nat.succ_le_of_lt hi) hM (by omega)
      · rfl

private theorem sepMid_spec {K i j : ℕ} (hij : i < j) (hjK : j ≤ K) :
    let k := sepMid (K + 1) 0 K i j
    i ≤ k ∧ k < j ∧ (i, k) ∈ sampleSet K ∧ (k, j) ∈ sampleSet K ∧ (k, k) ∈ sampleSet K := by
  simpa only [sepMid_eq_aux (Nat.zero_le i) hij hjK (by omega : K - 0 + 1 ≤ K + 1), sampleSet_eq_MHR,
    BilateralProfitMHR.sepMid] using BilateralProfitMHR.sepMid_spec hij hjK

private theorem sampleSet_diagonal {K i : ℕ} (hi : i < K) : (i, i) ∈ sampleSet K := by
  obtain ⟨hlo, hup, _, _, hmem⟩ := sepMid_spec (Nat.lt_succ_self i) (Nat.succ_le_of_lt hi)
  have he : sepMid (K + 1) 0 K i i.succ = i := by omega
  simpa only [he] using hmem

private theorem init_log_ge_one {T : ℕ} (hT : 2 ≤ T) : 1 ≤ Real.log (2 * T) := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h4 : 1 ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith
  refine h4.trans (Real.log_le_log (by norm_num) ?_)
  have : (2 : ℝ) ≤ T := by exact_mod_cast hT
  linarith

private theorem sampleSet_real_card_le {K T : ℕ} (hK : 2 ≤ K) (hKT : K ≤ T) :
    ((sampleSet K).card : ℝ) ≤ 6 * K * Real.log (2 * T) := by
  rw [sampleSet_eq_MHR]
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
  have hc : ((BilateralProfitMHR.Spairs K).card : ℝ) ≤
      (K + 1 : ℝ) * ((Nat.clog 2 (K + 1) : ℝ) + 1) := by
    exact_mod_cast BilateralProfitMHR.Spairs_card_le K
  have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
  calc
    _ ≤ (K + 1 : ℝ) * ((Nat.clog 2 (K + 1) : ℝ) + 1) := hc
    _ ≤ (K + 1 : ℝ) * (4 * Real.log (2 * T)) := by gcongr
    _ ≤ 6 * K * Real.log (2 * T) := by nlinarith

end BilateralProfitRegular
end BundlePart002


section BundlePart003


set_option autoImplicit false

namespace BilateralProfitRegular

open MeasureTheory ProbabilityTheory

private theorem init_bernoulli_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hv : ∀ ω, X ω = 0 ∨ X ω = 1) : Integrable X P := by
  apply (integrable_const (1 : ℝ)).mono' hX.aestronglyMeasurable
  exact ae_of_all _ (fun ω => by rcases hv ω with h | h <;> simp [h])

private theorem init_bernoulli_mgf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hv : ∀ ω, X ω = 0 ∨ X ω = 1) (p : ℝ) (hp : ∫ ω, X ω ∂P = p)
    (t : ℝ) (ht : |t| ≤ 1) :
    Integrable (fun ω => Real.exp (t * (X ω - p))) P ∧
      mgf (fun ω => X ω - p) P t ≤ Real.exp (p * t ^ 2) := by
  have hXI := init_bernoulli_integrable P X hX hv
  have hpn : 0 ≤ p := by
    rw [← hp]
    exact integral_nonneg (fun ω => by rcases hv ω with h | h <;> simp [h])
  have heq : (fun ω => Real.exp (t * (X ω - p))) =
      fun ω => Real.exp (-t * p) * (1 + X ω * (Real.exp t - 1)) := by
    funext ω
    rcases hv ω with h | h
    · simp [h]
    · simp only [h, one_mul]
      have harg : t * (1 - p) = -t * p + t := by ring
      rw [harg, Real.exp_add]
      congr 1
      ring
  have hInt : Integrable (fun ω => Real.exp (t * (X ω - p))) P := by
    rw [heq]
    exact ((integrable_const (1 : ℝ)).add (hXI.mul_const _)).const_mul _
  refine ⟨hInt, ?_⟩
  have hmgf : mgf (fun ω => X ω - p) P t =
      Real.exp (-t * p) * (1 + p * (Real.exp t - 1)) := by
    unfold mgf
    rw [heq, integral_const_mul, integral_add (integrable_const _) (hXI.mul_const _),
      integral_const, integral_mul_const, hp]
    simp
  rw [hmgf]
  have htaylor := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le ht)).2
  calc
    _ ≤ Real.exp (-t * p) * Real.exp (p * (Real.exp t - 1)) := by
      gcongr
      simpa [add_comm] using Real.add_one_le_exp (p * (Real.exp t - 1))
    _ = Real.exp (p * (Real.exp t - 1 - t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left htaylor hpn

private theorem init_bernoulli_sum_mgf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hv : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hi : iIndepFun X P) (p : ℝ) (hp : ∀ i, ∫ ω, X i ω ∂P = p)
    (t : ℝ) (ht : |t| ≤ 1) :
    Integrable (fun ω => Real.exp (t * ∑ i, (X i ω - p))) P ∧
      mgf (fun ω => ∑ i, (X i ω - p)) P t ≤ Real.exp ((n : ℝ) * p * t ^ 2) := by
  classical
  let Y := fun i ω => X i ω - p
  have hY : ∀ i, Measurable (Y i) := fun i => (hX i).sub_const p
  have hYi : iIndepFun Y P := hi.comp (fun _ x => x - p) (fun _ => measurable_id.sub_const p)
  have hm i := init_bernoulli_mgf P (X i) (hX i) (hv i) p (hp i) t ht
  have hI := hYi.integrable_exp_mul_sum hY (s := Finset.univ) (fun i _ => (hm i).1)
  refine ⟨by simpa only [Finset.sum_apply] using hI, ?_⟩
  have hsumEq : (fun ω => ∑ i, (X i ω - p)) = ∑ i, Y i := by
    funext ω
    simp [Y]
  rw [hsumEq, hYi.mgf_sum hY]
  calc
    _ ≤ ∏ i : Fin n, Real.exp (p * t ^ 2) := by
      apply Finset.prod_le_prod
      · intro i _
        exact integral_nonneg (fun _ => (Real.exp_pos _).le)
      · intro i _
        exact (hm i).2
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

private theorem init_bernoulli_average_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hv : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hi : iIndepFun X P) (p : ℝ) (hp : ∀ i, ∫ ω, X i ω ∂P = p)
    (δ κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    P.real {ω | |(∑ i, X i ω) / n - p| > (p + δ) * κ} ≤
      2 * Real.exp (-((n : ℝ) * δ * κ ^ 2)) := by
  let Z := fun ω => ∑ i, (X i ω - p)
  let ε := (n : ℝ) * (p + δ) * κ
  obtain ⟨hIp, hMp⟩ := init_bernoulli_sum_mgf P X hX hv hi p hp κ (by simpa [abs_of_pos hκ] using hκ1)
  obtain ⟨hIn, hMn⟩ := init_bernoulli_sum_mgf P X hX hv hi p hp (-κ) (by simpa [abs_of_pos hκ] using hκ1)
  have hpos := measure_ge_le_exp_mul_mgf (μ := P) (X := Z) ε (t := κ)
    hκ.le hIp
  have hneg := measure_le_le_exp_mul_mgf (μ := P) (X := Z) (-ε) (t := -κ)
    (neg_nonpos.mpr hκ.le) hIn
  have hpos' : P.real {ω | ε ≤ Z ω} ≤ Real.exp (-((n : ℝ) * δ * κ ^ 2)) := by
    apply hpos.trans
    calc
      _ ≤ Real.exp (-κ * ε) * Real.exp ((n : ℝ) * p * κ ^ 2) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [ε]; ring
  have hneg' : P.real {ω | Z ω ≤ -ε} ≤ Real.exp (-((n : ℝ) * δ * κ ^ 2)) := by
    apply hneg.trans
    calc
      _ ≤ Real.exp (-(-κ) * (-ε)) * Real.exp ((n : ℝ) * p * (-κ) ^ 2) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [ε]; ring
  have hsub : {ω | |(∑ i, X i ω) / n - p| > (p + δ) * κ} ⊆
      {ω | ε ≤ Z ω} ∪ {ω | Z ω ≤ -ε} := by
    intro ω hω
    change (p + δ) * κ < |(∑ i, X i ω) / n - p| at hω
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hZ : Z ω = ∑ i, X i ω - (n : ℝ) * p := by
      simp [Z, Finset.sum_sub_distrib, mul_comm]
    have hfrac : (∑ i, X i ω) / n - p = Z ω / n := by
      rw [hZ]
      field_simp
    rw [hfrac, abs_div, abs_of_pos hnR] at hω
    have hω' := (lt_div_iff₀ hnR).mp hω
    change ε ≤ Z ω ∨ Z ω ≤ -ε
    rcases le_total 0 (Z ω) with hz | hz
    · left
      rw [abs_of_nonneg hz] at hω'
      dsimp [ε]
      linarith only [hω']
    · right
      rw [abs_of_nonpos hz] at hω'
      dsimp [ε]
      linarith only [hω']
  calc
    _ ≤ P.real ({ω | ε ≤ Z ω} ∪ {ω | Z ω ≤ -ε}) := measureReal_mono hsub
    _ ≤ P.real {ω | ε ≤ Z ω} + P.real {ω | Z ω ≤ -ε} := measureReal_union_le _ _
    _ ≤ _ := by linarith

end BilateralProfitRegular
end BundlePart003


section BundlePart004



namespace BilateralProfitRegular

open MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

private abbrev InitUniforms := Option ℕ × (ℕ × ℕ) × ℕ → unitInterval

private noncomputable def probeBit (p : ℝ) (u : unitInterval) : ℝ :=
  if (u : ℝ) < p then 1 else 0

private theorem measurable_probeBit (p : ℝ) : Measurable (probeBit p) :=
  measurable_const.piecewise (measurableSet_lt measurable_subtype_coe measurable_const) measurable_const

private theorem integral_probeBit {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ∫ u : unitInterval, probeBit p u ∂volume = p := by
  let v : unitInterval := ⟨p, hp⟩
  have he : probeBit p = (Set.Iio v).indicator (fun _ => (1 : ℝ)) := by
    funext u
    rfl
  rw [he]
  have hi := integral_indicator_one (μ := (volume : Measure unitInterval))
    (s := Set.Iio v) measurableSet_Iio
  exact hi.trans (by rw [measureReal_def, unitInterval.volume_Iio, ENNReal.toReal_ofReal hp.1])

private theorem freq_measurable (K : ℕ) (prob : ℝ × ℝ → ℝ) (s : Option ℕ)
    (n : ℕ) (e : ℕ × ℕ) : Measurable (fun U : InitUniforms => freq K prob U s n e) :=
  (Finset.measurable_sum _ fun m _ =>
    (measurable_probeBit _).comp (measurable_pi_apply (s, e, m))).div_const _

private theorem freq_range (K : ℕ) (prob : ℝ × ℝ → ℝ) (U : InitUniforms) (s : Option ℕ)
    (n : ℕ) (e : ℕ × ℕ) : 0 ≤ freq K prob U s n e ∧ freq K prob U s n e ≤ 1 := by
  have hsum : ∀ m : ℕ, 0 ≤ probeBit (prob (gpt K e)) (U (s, e, m)) ∧
      probeBit (prob (gpt K e)) (U (s, e, m)) ≤ 1 := by
    intro m
    unfold probeBit
    split <;> norm_num
  change (0 ≤ (∑ m ∈ Finset.range n, probeBit _ (U (s, e, m))) / n) ∧
    ((∑ m ∈ Finset.range n, probeBit _ (U (s, e, m))) / n ≤ 1)
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun m _ => (hsum m).1) (Nat.cast_nonneg _)
  · by_cases hn : n = 0
    · subst n
      simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      apply (div_le_one hn').2
      calc
        _ ≤ ∑ _m ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun m _ => (hsum m).2
        _ = _ := by simp

private theorem freq_tail (K : ℕ) (prob : ℝ × ℝ → ℝ) (s : Option ℕ) {n : ℕ} (hn : 0 < n)
    (e : ℕ × ℕ) (hp : prob (gpt K e) ∈ Set.Icc (0 : ℝ) 1)
    (δ κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    initCoinLaw.real {U | (prob (gpt K e) + δ) * κ <
        |freq K prob U s n e - prob (gpt K e)|} ≤
      2 * Real.exp (-((n : ℝ) * δ * κ ^ 2)) := by
  let p := prob (gpt K e)
  let J := Option ℕ × (ℕ × ℕ) × ℕ
  let emb : Fin n → J := fun m => (s, e, (m : ℕ))
  let X : Fin n → InitUniforms → ℝ := fun m U => probeBit p (U (emb m))
  have hemb : Function.Injective emb := by
    intro m k he
    exact Fin.ext (congrArg (fun r : J => r.2.2) he)
  have hX (m : Fin n) : Measurable (X m) :=
    (measurable_probeBit p).comp (measurable_pi_apply (emb m))
  have hv (m : Fin n) (U : InitUniforms) : X m U = 0 ∨ X m U = 1 := by
    change probeBit p (U (emb m)) = 0 ∨ probeBit p (U (emb m)) = 1
    unfold probeBit
    split <;> simp
  have hiAll : iIndepFun (fun i : J => fun U : InitUniforms => probeBit p (U i)) initCoinLaw :=
    iIndepFun_infinitePi (P := fun _ : J => (volume : Measure unitInterval))
      (fun _ => measurable_probeBit p)
  have hi : iIndepFun X initCoinLaw := hiAll.precomp hemb
  have hpInt (m : Fin n) : ∫ U, X m U ∂initCoinLaw = p := by
    have hmap := Measure.infinitePi_map_eval (fun _ : J => (volume : Measure unitInterval)) (emb m)
    change Measure.map (fun U : InitUniforms => U (emb m)) initCoinLaw = volume at hmap
    have hint := integral_map (μ := initCoinLaw)
      (measurable_pi_apply (emb m)).aemeasurable (measurable_probeBit p).aestronglyMeasurable
    rw [hmap] at hint
    exact hint.symm.trans (integral_probeBit hp)
  have : IsProbabilityMeasure initCoinLaw := by unfold initCoinLaw; infer_instance
  have ht := init_bernoulli_average_tail initCoinLaw hn X hX hv hi p hpInt δ κ hκ hκ1
  have hfreq (U : InitUniforms) : freq K prob U s n e = (∑ m, X m U) / n := by
    unfold freq
    congr 1
    change (∑ m ∈ Finset.range n, probeBit p (U (s, e, m))) =
      ∑ m : Fin n, probeBit p (U (s, e, (m : ℕ)))
    exact (Fin.sum_univ_eq_sum_range (fun m => probeBit p (U (s, e, m))) n).symm
  simpa only [hfreq] using ht

/-- Accuracy for all possible stage scales, including the scale selected from the observations. -/
private def InitProbeStageGood (K : ℕ) (prob : ℝ × ℝ → ℝ) (s : ℕ → Option ℕ)
    (N : ℕ → ℕ) (κ : ℝ) (U : InitUniforms) : Prop :=
  ∀ h < K, ∀ i ≤ K, ∀ j ≤ K,
    |freq K prob U (s h) (N h) (i, j) - prob (gpt K (i, j))| ≤
      (prob (gpt K (i, j)) + scale h) * κ

private abbrev InitProbeGood (T K : ℕ) (prob : ℝ × ℝ → ℝ) (U : InitUniforms) : Prop :=
  InitProbeStageGood K prob some (mhrRounds T) (1 / 128) U ∧
  InitProbeStageGood K prob (fun _ => none) (fun h => step2Rounds T (scale h)) (1 / 262144) U

private theorem initCoinLaw_isProbabilityMeasure : IsProbabilityMeasure initCoinLaw := by
  unfold initCoinLaw
  infer_instance

set_option linter.unusedVariables false in
private theorem init_probe_stage_failure {T K : ℕ} (hK : 2 ≤ K) (hKT : K ≤ T)
    (prob : ℝ × ℝ → ℝ) (hp : ∀ x, prob x ∈ Set.Icc (0 : ℝ) 1)
    (s : ℕ → Option ℕ) (N : ℕ → ℕ) (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hN : ∀ h < K, 4 * Real.log (2 * (T : ℝ)) ≤ (N h : ℝ) * scale h * κ ^ 2) :
    initCoinLaw {U | ¬ InitProbeStageGood K prob s N κ U} ≤
      ENNReal.ofReal (1 / (2 * (T : ℝ))) := by
  let _ := initCoinLaw_isProbabilityMeasure
  let J := Fin K × Fin (K + 1) × Fin (K + 1)
  let F (v : J) : Set InitUniforms := {U |
    (prob (gpt K (v.2.1, v.2.2)) + scale v.1) * κ <
      |freq K prob U (s v.1) (N v.1) (v.2.1, v.2.2) - prob (gpt K (v.2.1, v.2.2))|}
  have hT' : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hlog : 0 < Real.log (2 * (T : ℝ)) := by
    apply Real.log_pos
    have : (2 : ℝ) ≤ T := by exact_mod_cast hK.trans hKT
    linarith
  have hNpos (h : Fin K) : 0 < N h := by
    by_contra! hz
    have hz' : N h = 0 := Nat.eq_zero_of_le_zero hz
    have hle := hN h h.isLt
    simp [hz'] at hle
    linarith
  have htail (v : J) : initCoinLaw.real (F v) ≤ 2 * Real.exp (-4 * Real.log (2 * (T : ℝ))) := by
    refine (freq_tail K prob (s v.1) (hNpos v.1) (v.2.1, v.2.2) (hp _)
      (scale v.1) κ hκ hκ1).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    exact (by linarith only [hN v.1 v.1.isLt])
  have hF_eq : {U | ¬ InitProbeStageGood K prob s N κ U} = ⋃ v, F v := by
    ext U
    simp only [Set.mem_ofPred_eq, InitProbeStageGood, not_forall, not_le, Set.mem_iUnion, F]
    constructor
    · rintro ⟨h, hh, i, hi, j, hj, hfail⟩
      exact ⟨(⟨h, hh⟩, ⟨i, Nat.lt_succ_of_le hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩), hfail⟩
    · rintro ⟨⟨h, i, j⟩, hfail⟩
      exact ⟨h, h.isLt, i, Nat.le_of_lt_succ i.isLt, j, Nat.le_of_lt_succ j.isLt, hfail⟩
  have hEsum : initCoinLaw.real (⋃ v, F v) ≤
      (K : ℝ) * ((K : ℝ) + 1) ^ 2 * (2 * Real.exp (-4 * Real.log (2 * (T : ℝ)))) := by
    refine (measureReal_iUnion_fintype_le _).trans ((Finset.sum_le_sum fun v _ => htail v).trans_eq ?_)
    simp only [J, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hK' : (K : ℝ) ≤ T := by exact_mod_cast hKT
  have hK2 : (K : ℝ) + 1 ≤ 2 * (T : ℝ) := by
    exact_mod_cast (show K + 1 ≤ 2 * T by omega)
  have he : Real.exp (-4 * Real.log (2 * (T : ℝ))) = ((2 * (T : ℝ)) ^ 4)⁻¹ := by
    rw [neg_mul, Real.exp_neg]
    congr 1
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hcard : (K : ℝ) * ((K : ℝ) + 1) ^ 2 ≤ (T : ℝ) * (2 * (T : ℝ)) ^ 2 := by
    gcongr
  have hreal : initCoinLaw.real (⋃ v, F v) ≤ 1 / (2 * (T : ℝ)) := by
    calc
      _ ≤ _ := hEsum
      _ ≤ (T : ℝ) * (2 * (T : ℝ)) ^ 2 * (2 * Real.exp (-4 * Real.log (2 * (T : ℝ)))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by rw [he]; field_simp
  rw [hF_eq]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).1
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact hreal

private theorem init_probe_failure {T K : ℕ} (hK : 2 ≤ K) (hKT : K ≤ T)
    (prob : ℝ × ℝ → ℝ) (hp : ∀ x, prob x ∈ Set.Icc (0 : ℝ) 1) :
    initCoinLaw {U | ¬ InitProbeGood T K prob U} ≤ ENNReal.ofReal (1 / (T : ℝ)) := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hs (h : ℕ) : 0 < scale h := by unfold scale; positivity
  have h₁ : ∀ h < K, 4 * Real.log (2 * (T : ℝ)) ≤
      (mhrRounds T h : ℝ) * scale h * (1 / 128) ^ 2 := by
    intro h _
    have hc := (div_le_iff₀ (hs h)).1 (Nat.le_ceil ((2 : ℝ)^16 * Real.log (2 * T) / scale h))
    change (2 : ℝ)^16 * Real.log (2 * T) ≤ (mhrRounds T h : ℝ) * scale h at hc
    norm_num at hc ⊢
    linarith only [hc]
  have h₂ : ∀ h < K, 4 * Real.log (2 * (T : ℝ)) ≤
      (step2Rounds T (scale h) : ℝ) * scale h * (1 / 262144) ^ 2 := by
    intro h _
    have hc := (div_le_iff₀ (hs h)).1 (Nat.le_ceil ((2 : ℝ)^38 * Real.log (2 * T) / scale h))
    change (2 : ℝ)^38 * Real.log (2 * T) ≤ (step2Rounds T (scale h) : ℝ) * scale h at hc
    norm_num at hc ⊢
    linarith only [hc]
  let A := {U | ¬ InitProbeStageGood K prob some (mhrRounds T) (1 / 128) U}
  let B := {U | ¬ InitProbeStageGood K prob (fun _ => none) (fun h => step2Rounds T (scale h))
    (1 / 262144) U}
  have he : {U | ¬ InitProbeGood T K prob U} = A ∪ B := by
    ext U
    exact not_and_or
  rw [he]
  refine (measure_union_le A B).trans ?_
  calc
    _ ≤ ENNReal.ofReal (1 / (2 * (T : ℝ))) + ENNReal.ofReal (1 / (2 * (T : ℝ))) :=
      add_le_add (init_probe_stage_failure hK hKT prob hp _ _ _ (by norm_num) (by norm_num) h₁)
        (init_probe_stage_failure hK hKT prob hp _ _ _ (by norm_num) (by norm_num) h₂)
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; field_simp; ring

end BilateralProfitRegular
end BundlePart004


section BundlePart005


namespace BilateralProfitRegular

private theorem ratio_nonneg_le {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ A * B / max A (max B C) ∧ A * B / max A (max B C) ≤ min A B := by
  let D := max A (max B C)
  have hAD : A ≤ D := le_max_left _ _
  have hBD : B ≤ D := (le_max_left B C).trans (le_max_right _ _)
  have hD : 0 ≤ D := hC.trans ((le_max_right B C).trans (le_max_right _ _))
  refine ⟨div_nonneg (mul_nonneg hA hB) hD, ?_⟩
  change A * B / D ≤ min A B
  by_cases hz : D = 0
  · simp [hz, le_min hA hB]
  · have hp : 0 < D := lt_of_le_of_ne hD (Ne.symm hz)
    apply le_min
    · exact (div_le_iff₀ hp).2 (mul_le_mul_of_nonneg_left hBD hA)
    · exact (div_le_iff₀ hp).2 (by nlinarith [mul_le_mul_of_nonneg_left hAD hB])

private theorem ratio_mem_unit {A B C : ℝ} (hA : A ∈ Set.Icc (0 : ℝ) 1) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    A * B / max A (max B C) ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h0, hu⟩ := ratio_nonneg_le hA.1 hB hC
  exact ⟨h0, hu.trans ((min_le_left _ _).trans hA.2)⟩

/-- The three-frequency reconstruction magnifies the relative-plus-additive tolerance by
at most a factor of eight. This applies to both stages of the regular initializer. -/
private theorem regular_ratio_error {a b c p A B C δ κ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (hac : a ≤ c) (hbc : b ≤ c) (hpc : p ≤ c) (hid : a * b = p * c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 128)
    (hea : |A - a| ≤ (a + δ) * κ) (heb : |B - b| ≤ (b + δ) * κ)
    (hec : |C - c| ≤ (c + δ) * κ) :
    |A * B / max A (max B C) - p| ≤ 8 * κ * (p + δ) := by
  let D := max A (max B C)
  have hCD : C ≤ D := (le_max_right B C).trans (le_max_right _ _)
  have hbounds := ratio_nonneg_le hA hB hC
  have hDerr : |D - c| ≤ (c + δ) * κ := by
    rw [abs_sub_le_iff] at hea heb hec ⊢
    constructor
    · apply sub_le_iff_le_add.mpr
      exact max_le
        (by nlinarith [mul_le_mul_of_nonneg_right hac hκ.le])
        (max_le (by nlinarith [mul_le_mul_of_nonneg_right hbc hκ.le]) (by linarith))
    · linarith
  by_cases hsmall : c < 4 * κ * δ
  · have hAu : A ≤ c + (c + δ) * κ := by
      have he := (abs_sub_le_iff.mp hea).1
      nlinarith [mul_le_mul_of_nonneg_right hac hκ.le]
    have hAu' : A ≤ 8 * κ * δ := by
      have h1 := mul_le_mul_of_nonneg_right hsmall.le hκ.le
      have h2 := mul_nonneg (show 0 ≤ κ * δ by positivity) (show 0 ≤ 3 - 4 * κ by linarith)
      nlinarith only [hAu, hsmall, h1, h2]
    have hr := hbounds.2.trans ((min_le_left _ _).trans hAu')
    have hpos : 0 ≤ κ * p := mul_nonneg hκ.le hp
    rw [abs_sub_le_iff]
    constructor <;> nlinarith only [hr, hbounds.1, hpc, hsmall, hp, hpos, hκ, hδ]
  · have hδc : 4 * κ * δ ≤ c := le_of_not_gt hsmall
    have hcp : 0 < c := (show 0 < 4 * κ * δ by positivity).trans_le hδc
    have hκq : κ ≤ 1 / 4 := by linarith
    have hDlow : c / 2 ≤ D := by
      have he := (abs_sub_le_iff.mp hDerr).2
      nlinarith only [he, hδc, mul_le_mul_of_nonneg_right hκq hc]
    have hDp : 0 < D := (half_pos hcp).trans_le hDlow
    have heq : A * B - p * D =
        b * (A - a) + a * (B - b) + (A - a) * (B - b) - p * (D - c) := by
      nlinarith only [hid]
    have hnum : |A * B - p * D| ≤
        b * ((a + δ) * κ) + a * ((b + δ) * κ) +
          ((a + δ) * κ) * ((b + δ) * κ) + p * ((c + δ) * κ) := by
      calc
        _ = |b * (A - a) + a * (B - b) + (A - a) * (B - b) - p * (D - c)| :=
          congrArg abs heq
        _ ≤ |b * (A - a) + a * (B - b) + (A - a) * (B - b)| +
            |p * (D - c)| := abs_sub _ _
        _ ≤ (|b * (A - a) + a * (B - b)| + |(A - a) * (B - b)|) +
            |p * (D - c)| := by gcongr; exact abs_add_le _ _
        _ ≤ ((|b * (A - a)| + |a * (B - b)|) + |(A - a) * (B - b)|) +
            |p * (D - c)| := by gcongr; exact abs_add_le _ _
        _ = b * |A - a| + a * |B - b| + |A - a| * |B - b| + p * |D - c| := by
          simp [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg hp]
        _ ≤ _ := by gcongr
    have hlinear : b * (a + δ) + a * (b + δ) + p * (c + δ) ≤
        3 * c * (p + δ) := by
      nlinarith only [hid, mul_le_mul_of_nonneg_right hac hδ.le,
        mul_le_mul_of_nonneg_right hbc hδ.le, mul_le_mul_of_nonneg_right hpc hδ.le]
    have hcross : κ * (a + δ) * (b + δ) ≤ c * (p + δ) := by
      have hsum : p * c + a * δ + b * δ ≤ p * c + c * δ + c * δ := by
        gcongr
      have hbound : κ * (p * c + c * δ + c * δ) + (c / 4) * δ ≤ c * (p + δ) := by
        have hpc' : 0 ≤ p * c := by positivity
        have hcδ : 0 ≤ c * δ := by positivity
        nlinarith only [hcδ, mul_le_mul_of_nonneg_right (show κ ≤ 1 by linarith) hpc',
          mul_le_mul_of_nonneg_right hκq hcδ]
      calc
        _ = κ * (p * c + a * δ + b * δ) + (κ * δ) * δ := by rw [← hid]; ring
        _ ≤ κ * (p * c + c * δ + c * δ) + (c / 4) * δ := by
          refine add_le_add (mul_le_mul_of_nonneg_left hsum hκ.le) ?_
          exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
        _ ≤ _ := hbound
    have hnum' : |A * B - p * D| ≤ 4 * κ * c * (p + δ) := by
      calc
        _ ≤ _ := hnum
        _ = κ * (b * (a + δ) + a * (b + δ) + p * (c + δ)) +
            κ * (κ * (a + δ) * (b + δ)) := by ring
        _ ≤ κ * (3 * c * (p + δ)) + κ * (c * (p + δ)) :=
          add_le_add (mul_le_mul_of_nonneg_left hlinear hκ.le)
            (mul_le_mul_of_nonneg_left hcross hκ.le)
        _ = _ := by ring
    change |A * B / D - p| ≤ _
    have hdiv : A * B / D - p = (A * B - p * D) / D := by field_simp
    rw [hdiv, abs_div, abs_of_pos hDp]
    apply (div_le_iff₀ hDp).2
    have hhalf := mul_le_mul_of_nonneg_left hDlow (show 0 ≤ 8 * κ * (p + δ) by positivity)
    nlinarith only [hnum', hhalf]

end BilateralProfitRegular
end BundlePart005


section BundlePart006





namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

private theorem gpt_coord_mem {K i : ℕ} (hK : 0 < K) (hi : i ≤ K) :
    (i : ℝ) / K ∈ Set.Icc (0 : ℝ) 1 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  exact ⟨div_nonneg (Nat.cast_nonneg _) hK'.le, (div_le_one hK').2 (by exact_mod_cast hi)⟩

private theorem gpt_tri {K i j : ℕ} (hK : 0 < K) (hij : i ≤ j) (hjK : j ≤ K) :
    gpt K (i, j) ∈ triT := by
  obtain ⟨hi0, _⟩ := gpt_coord_mem hK (hij.trans hjK)
  obtain ⟨_, hj1⟩ := gpt_coord_mem hK hjK
  exact ⟨hi0, div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg _), hj1⟩

private theorem gpt_profit_nonneg {K i j : ℕ} (hK : 0 < K) (hij : i ≤ j) (hjK : j ≤ K)
    (E : Environment) (hE : OnUnit E) :
    0 ≤ mu E (gpt K (i, j)) := by
  rw [mu_formula]
  exact mul_nonneg (sub_nonneg.mpr (gpt_tri hK hij hjK).2.1) ((onUnit_facts E hE).1 _).1

private theorem gpt_width {K i j : ℕ} (hK : 0 < K) (hij : i ≤ j) (hjK : j ≤ K) :
    ((j : ℝ) - i) / K ∈ Set.Icc (0 : ℝ) 1 := by
  rw [sub_div]
  obtain ⟨hi, hij', hj⟩ := gpt_tri hK hij hjK
  change (0 : ℝ) ≤ (i : ℝ) / K at hi
  change (j : ℝ) / K ≤ 1 at hj
  refine ⟨sub_nonneg.mpr hij', ?_⟩
  linarith

private theorem phat_mul_width (E : Environment) (K i j : ℕ) :
    mu E (gpt K (i, j)) = ((j : ℝ) - i) / K * P E (gpt K (i, j)) := by
  rw [mu_formula, sub_div]
  rfl

private theorem gpt_profit_error {p q d δ w : ℝ} (hd : d ∈ Set.Icc (0 : ℝ) 1)
    (hδ : 0 ≤ δ) (hw : 0 ≤ w) (he : |q - p| ≤ w * (p + δ)) :
    |d * q - d * p| ≤ w * (d * p + δ) := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hd.1]
  calc
    _ ≤ d * (w * (p + δ)) := mul_le_mul_of_nonneg_left he hd.1
    _ = w * (d * p + d * δ) := by ring
    _ ≤ _ := by gcongr; exact mul_le_of_le_one_left hδ hd.2

private theorem recon_bounds (E : Environment) (hE : OnUnit E) {K : ℕ} (hK : 0 < K)
    {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 128)
    (F : ℕ × ℕ → ℝ)
    (hF : ∀ e ∈ sampleSet K, F e ∈ Set.Icc (0 : ℝ) 1 ∧
      |F e - P E (gpt K e)| ≤ (P E (gpt K e) + δ) * κ)
    {i j : ℕ} (hij : i < j) (hjK : j ≤ K) :
    recon K F i j ∈ Set.Icc (0 : ℝ) 1 ∧
      |recon K F i j - P E (gpt K (i, j))| ≤ 8 * κ * (P E (gpt K (i, j)) + δ) := by
  let k := sepMid (K + 1) 0 K i j
  obtain ⟨hik, hkj, hikS, hkjS, hkkS⟩ := sepMid_spec hij hjK
  have hi := gpt_coord_mem hK (hij.le.trans hjK)
  have hk := gpt_coord_mem hK (hkj.le.trans hjK)
  have hj := gpt_coord_mem hK hjK
  have hik' : (i : ℝ) / K ≤ (k : ℝ) / K := (gpt_tri hK hik (hkj.le.trans hjK)).2.1
  have hkj' : (k : ℝ) / K ≤ (j : ℝ) / K := (gpt_tri hK hkj.le hjK).2.1
  obtain ⟨_, _, hP, _, _, _, _, _, _, _, _, _, _, _, hfactor, _⟩ :=
    BilateralProfitMHR.positive_density_profit_facts E hE
  obtain ⟨hid, hac, hbc, hpc⟩ := hfactor _ hi _ hk _ hj hik' hkj'
  have ⟨hA, heA⟩ := hF _ hikS
  have ⟨hB, heB⟩ := hF _ hkjS
  have ⟨hC, heC⟩ := hF _ hkkS
  refine ⟨ratio_mem_unit hA hB.1 hC.1, ?_⟩
  exact regular_ratio_error (hP _).1 (hP _).1 (hP _).1 (hP _).1 hac hbc hpc hid
    hA.1 hB.1 hC.1 hδ hκ hκ1 heA heB heC

private theorem P_gpt_zero_left (E : Environment) (hE : OnUnit E) {K j : ℕ} (hK : 0 < K) (hj : j ≤ K) :
    P E (gpt K (0, j)) = 0 := by
  rw [P_factor E hE ⟨gpt_coord_mem hK (Nat.zero_le K), gpt_coord_mem hK hj⟩]
  simp [gpt, Environment.cdfS, hE.1]

private theorem P_gpt_zero_right (E : Environment) (hE : OnUnit E) {K i : ℕ} (hK : 0 < K) (hi : i ≤ K) :
    P E (gpt K (i, K)) = 0 := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hf := E.fB_integral
  rw [hE.2.2.2] at hf
  rw [P_factor E hE ⟨gpt_coord_mem hK hi, gpt_coord_mem hK le_rfl⟩]
  simp [gpt, Environment.cdfB, hf, hk]

private theorem mhrEst_boundary (E : Environment) (hE : OnUnit E) {K i j : ℕ}
    (hK : 0 < K) (hij : i ≤ j) (hjK : j ≤ K)
    (hno : ¬ (1 ≤ i ∧ i < j ∧ j ≤ K - 1)) :
    mu E (gpt K (i, j)) = 0 := by
  rw [phat_mul_width]
  have h : i = 0 ∨ i = j ∨ j = K := by omega
  rcases h with rfl | h | rfl
  · rw [P_gpt_zero_left E hE hK hjK, mul_zero]
  · simp [h]
  · rw [P_gpt_zero_right E hE hK hij, mul_zero]

private theorem mhrEst_error (E : Environment) (hE : OnUnit E) (T K h : ℕ) (hK : 0 < K)
    (hh : h < K) (U : InitUniforms) (hgood : InitProbeGood T K (P E) U)
    (i j : ℕ) (hij : i ≤ j) (hjK : j ≤ K) :
    |mhrEst T K (P E) U h (i, j) - mu E (gpt K (i, j))| ≤
      (mu E (gpt K (i, j)) + scale h) / 16 := by
  have hδ : 0 < scale h := by unfold scale; positivity
  by_cases hyes : 1 ≤ i ∧ i < j ∧ j ≤ K - 1
  · let F := freq K (P E) U (some h) (mhrRounds T h)
    have hF (e : ℕ × ℕ) (he : e ∈ sampleSet K) :
        F e ∈ Set.Icc (0 : ℝ) 1 ∧
          |F e - P E (gpt K e)| ≤ (P E (gpt K e) + scale h) * (1 / 128) := by
      obtain ⟨hle, hmax⟩ := sampleSet_bounds he
      exact ⟨freq_range K (P E) U (some h) (mhrRounds T h) e,
        hgood.1 h hh e.1 (hle.trans hmax) e.2 hmax⟩
    have hR := (recon_bounds E hE hK hδ (by norm_num) le_rfl F hF hyes.2.1 hjK).2
    have herr := gpt_profit_error (gpt_width hK hij hjK) hδ.le (by norm_num : 0 ≤ 8 * (1 / 128 : ℝ)) hR
    rw [phat_mul_width]
    simp only [mhrEst, if_pos hyes]
    convert herr using 1
    ring
  · rw [mhrEst_boundary E hE hK hij hjK hyes]
    simp only [mhrEst, if_neg hyes, sub_zero, abs_zero, zero_add]
    positivity

private theorem step2_phat_bounds (E : Environment) (hE : OnUnit E) (T K h : ℕ) (hK : 0 < K)
    (hh : h < K) (U : InitUniforms) (hgood : InitProbeGood T K (P E) U)
    (i j : ℕ) (hij : i ≤ j) (hjK : j ≤ K) :
    phat T K (scale h) (P E) U (i, j) ∈ Set.Icc (0 : ℝ) 1 ∧
      |phat T K (scale h) (P E) U (i, j) - P E (gpt K (i, j))| ≤
        (P E (gpt K (i, j)) + scale h) / 32768 := by
  have hδ : 0 < scale h := by unfold scale; positivity
  let F := freq K (P E) U none (step2Rounds T (scale h))
  have hF (e : ℕ × ℕ) (he : e ∈ sampleSet K) :
      F e ∈ Set.Icc (0 : ℝ) 1 ∧
        |F e - P E (gpt K e)| ≤ (P E (gpt K e) + scale h) * (1 / 262144) := by
    obtain ⟨hle, hmax⟩ := sampleSet_bounds he
    exact ⟨freq_range K (P E) U none (step2Rounds T (scale h)) e,
      hgood.2 h hh e.1 (hle.trans hmax) e.2 hmax⟩
  by_cases hi : 1 ≤ i ∧ i < j ∧ j ≤ K - 1
  · have hh := recon_bounds E hE hK hδ (by norm_num) (by norm_num) F hF hi.2.1 hjK
    rw [phat, if_pos hi]
    exact ⟨hh.1, hh.2.trans_eq (by ring)⟩
  rw [phat, if_neg hi]
  by_cases hd : i = j ∧ 1 ≤ i ∧ i ≤ K - 1
  · rw [if_pos hd]
    have hd' := hd.2.2
    have he := hd.1
    subst j
    obtain ⟨hunit, herr⟩ := hF (i, i) (sampleSet_diagonal (by omega))
    refine ⟨hunit, ?_⟩
    linarith [show 0 ≤ P E (gpt K (i, i)) from ((onUnit_facts E hE).1 _).1]
  · rw [if_neg hd]
    have hz : i = 0 ∨ j = K := by omega
    have hP0 : P E (gpt K (i, j)) = 0 := by
      rcases hz with rfl | rfl
      · exact P_gpt_zero_left E hE hK hjK
      · exact P_gpt_zero_right E hE hK hij
    rw [hP0]
    exact ⟨by norm_num, by simp; positivity⟩

private theorem step2_muhat_error (E : Environment) (hE : OnUnit E) (T K h : ℕ) (hK : 0 < K)
    (hh : h < K) (U : InitUniforms) (hgood : InitProbeGood T K (P E) U)
    (i j : ℕ) (hij : i ≤ j) (hjK : j ≤ K) :
    |muhat T K (scale h) (P E) U (i, j) - mu E (gpt K (i, j))| ≤
      (mu E (gpt K (i, j)) + scale h) / 32768 := by
  have hδ : 0 < scale h := by unfold scale; positivity
  have hP := (step2_phat_bounds E hE T K h hK hh U hgood i j hij hjK).2
  have hP' : _ ≤ (1 / 32768 : ℝ) * (P E (gpt K (i, j)) + scale h) :=
    hP.trans_eq (by ring)
  have herr := gpt_profit_error (gpt_width hK hij hjK) hδ.le (by norm_num : 0 ≤ (1 / 32768 : ℝ)) hP'
  rw [phat_mul_width]
  unfold muhat
  convert herr using 1
  ring

end BilateralProfitRegular
end BundlePart006


section BundlePart007


namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

private theorem hasDerivAt_tanh (t : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh t ^ 2) t := by
  have hd := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  have he : Real.tanh = Real.sinh / Real.cosh := funext Real.tanh_eq_sinh_div_cosh
  rw [he]
  simpa only [← pow_two, Real.cosh_sq_sub_sinh_sq] using hd

private theorem tanh_lipschitz : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hasDerivAt_tanh t).differentiableAt)
  intro t
  rw [(hasDerivAt_tanh t).deriv]
  change ‖(1 / Real.cosh t ^ 2 : ℝ)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (pow_pos (Real.cosh_pos t) _)).mpr
  nlinarith only [Real.one_le_cosh t, sq_nonneg (Real.cosh t - 1)]

private theorem sech_sq_add_tanh_sq (t : ℝ) :
    (2 / (Real.exp t + Real.exp (-t))) ^ 2 + Real.tanh t ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  -- The exponential denominator is twice the hyperbolic cosine.
  have hc : Real.exp t + Real.exp (-t) = 2 * Real.cosh t := by rw [Real.cosh_eq]; ring
  rw [hc]
  have ht := (Real.cosh_pos t).ne'
  field_simp
  nlinarith only [Real.cosh_sq_sub_sinh_sq t]

private theorem auxProfit_sech (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) :
    auxProfit E lam x =
      mu E x * (2 / (Real.exp (Real.log (lam / balance E x)) +
        Real.exp (-Real.log (lam / balance E x)))) ^ 2 := by
  obtain ⟨hs, hb⟩ := intT_cdf_pos E hE hx
  have hl := balance_pos E hE hx
  have hsq := balance_sq E hE hx
  let t := Real.log (lam / balance E x)
  have he : Real.exp t + Real.exp (-t) = lam / balance E x + balance E x / lam := by
    rw [Real.exp_neg, show Real.exp t = lam / balance E x from Real.exp_log (div_pos hlam hl),
      inv_div]
  have hdivide :
      balance E x ^ 2 / E.cdfS x.1 = (1 - E.cdfB x.2)⁻¹ := by
    rw [hsq]
    field_simp [hs.ne']
  have hinv :
      lam / E.cdfS x.1 + lam⁻¹ / (1 - E.cdfB x.2) =
        balance E x / E.cdfS x.1 * (Real.exp t + Real.exp (-t)) := by
    rw [he, mul_add]
    congr 1
    · field_simp
    · calc
        lam⁻¹ / (1 - E.cdfB x.2) = (balance E x ^ 2 / E.cdfS x.1) / lam := by
          rw [hdivide]
          ring
        _ = balance E x / E.cdfS x.1 * (balance E x / lam) := by ring
  have hnorm : (balance E x / E.cdfS x.1) ^ 2 = (E.cdfS x.1 * (1 - E.cdfB x.2))⁻¹ := by
    calc
      (balance E x / E.cdfS x.1) ^ 2 =
          (balance E x ^ 2 / E.cdfS x.1) / E.cdfS x.1 := by ring
      _ = _ := by rw [hdivide, mul_inv]; ring
  change auxProfit E lam x = mu E x * (2 / (Real.exp t + Real.exp (-t))) ^ 2
  rw [auxProfit, hinv, mul_pow, hnorm, mu_formula, P_factor E hE (intT_subset_unitSq hx),
    inv_mul_eq_div, div_div_eq_mul_div, div_pow]
  ring

private theorem auxProfit_tanh_gap (E : Environment) (hE : OnUnit E) {lam : ℝ}
    (hlam : 0 < lam) {x : ℝ × ℝ} (hx : x ∈ intT) :
    mu E x - auxProfit E lam x = mu E x * Real.tanh (Real.log (lam / balance E x)) ^ 2 := by
  rw [auxProfit_sech E hE hlam hx]
  have he := sech_sq_add_tanh_sq (Real.log (lam / balance E x))
  nlinarith only [congrArg (fun t => mu E x * t) he]

private theorem auxProfit_values (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) :
    0 ≤ mu E x - auxProfit E lam x ∧
    mu E x - auxProfit E lam x ≤ mu E x * Real.log (lam / balance E x) ^ 2 ∧
    0 < auxProfit E lam x ∧ auxProfit E lam x ≤ mu E x ∧
    auxProfit E (balance E x) x = mu E x := by
  have hmu := ((onUnit_facts E hE).2.2.1 x (intT_subset_unitSq hx)).mpr hx
  have he := auxProfit_tanh_gap E hE hlam hx
  have hg : 0 ≤ mu E x - auxProfit E lam x := he.symm ▸ mul_nonneg hmu.le (sq_nonneg _)
  refine ⟨hg, ?_, auxProfit_pos E hE hlam hx, sub_nonneg.mp hg, ?_⟩
  · rw [he]
    let t := Real.log (lam / balance E x)
    have hd : |Real.tanh t| ≤ |t| := by
      simpa [Real.dist_eq] using tanh_lipschitz.dist_le_mul t 0
    apply mul_le_mul_of_nonneg_left _ hmu.le
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (Real.tanh t)) hd 2
  · have hb := balance_pos E hE hx
    have ht := auxProfit_tanh_gap E hE hb hx
    rw [div_self hb.ne', Real.log_one, Real.tanh_zero] at ht
    linarith

private theorem auxProfit_perturbation (E : Environment) (hE : OnUnit E) {lam : ℝ} (hlam : 0 < lam)
    {x : ℝ × ℝ} (hx : x ∈ intT) (θ : ℝ) :
    muStar E - auxProfit E (lam * Real.exp θ) x ≤
      2 * (muStar E - auxProfit E lam x) + 2 * muStar E * θ ^ 2 := by
  let t := Real.log (lam / balance E x)
  have hb := balance_pos E hE hx
  have hmu := ((onUnit_facts E hE).2.2.1 x (intT_subset_unitSq hx)).mpr hx
  have hmuStar := mu_le_muStar E hE (intT_subset_unitSq hx)
  have he : Real.log ((lam * Real.exp θ) / balance E x) = t + θ := by
    rw [mul_div_right_comm, Real.log_mul (div_pos hlam hb).ne' (Real.exp_pos _).ne', Real.log_exp]
  have hgap := auxProfit_tanh_gap E hE (mul_pos hlam (Real.exp_pos θ)) hx
  rw [he] at hgap
  have hbase := auxProfit_tanh_gap E hE hlam hx
  change mu E x - auxProfit E lam x = mu E x * Real.tanh t ^ 2 at hbase
  have hdiff : |Real.tanh (t + θ) - Real.tanh t| ≤ |θ| := by
    simpa [Real.dist_eq] using tanh_lipschitz.dist_le_mul (t + θ) t
  have hsq : (Real.tanh (t + θ) - Real.tanh t)^2 ≤ θ^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  have hsq' : Real.tanh (t + θ) ^ 2 ≤ 2 * Real.tanh t ^ 2 + 2 * θ ^ 2 := by
    nlinarith only [hsq, sq_nonneg (Real.tanh (t + θ) - 2 * Real.tanh t)]
  have hquad := mul_le_mul_of_nonneg_left hsq' hmu.le
  have hscale := mul_le_mul_of_nonneg_right hmuStar (sq_nonneg θ)
  linarith only [hgap, hbase, hmuStar, hquad, hscale]

/-- High auxiliary profit bounds the logarithmic displacement of the balance. -/
private theorem auxProfit_implies_balance_bound (E : Environment) (hE : OnUnit E) {lam : ℝ}
    (hlam : 0 < lam) {x : ℝ × ℝ} (hx : x ∈ intT) {d : ℝ} (hd : 0 ≤ d) (hd₁ : d < 1)
    (hr : (1 - d ^ 2) * muStar E ≤ auxProfit E lam x) :
    |Real.log (balance E x / lam)| ≤ Real.artanh d := by
  let t := Real.log (lam / balance E x)
  have hmu := ((onUnit_facts E hE).2.2.1 x (intT_subset_unitSq hx)).mpr hx
  have hmuStar := mu_le_muStar E hE (intT_subset_unitSq hx)
  have hd₂ : 0 ≤ 1 - d ^ 2 := by
    have hh := pow_le_pow_left₀ hd hd₁.le 2
    linarith only [hh]
  have hbase : mu E x - auxProfit E lam x = mu E x * Real.tanh t ^ 2 :=
    auxProfit_tanh_gap E hE hlam hx
  have hbound : Real.tanh t ^ 2 ≤ d ^ 2 := by
    apply le_of_mul_le_mul_left _ hmu
    linarith only [hbase, hr, mul_le_mul_of_nonneg_left hmuStar hd₂]
  rw [← sq_abs (Real.tanh t)] at hbound
  obtain ⟨htl, htr⟩ := abs_le.mp (le_of_pow_le_pow_left₀ (by decide) hd hbound)
  have htu : t ≤ Real.artanh d := by
    rw [← Real.artanh_tanh t]
    exact Real.artanh_le_artanh (Real.neg_one_lt_tanh t) hd₁ htr
  have htl' : -t ≤ Real.artanh d := by
    have hneg : Real.tanh (-t) ≤ d := by rw [Real.tanh_neg]; linarith only [htl]
    rw [← Real.artanh_tanh (-t)]
    exact Real.artanh_le_artanh (Real.neg_one_lt_tanh _) hd₁ hneg
  rw [← inv_div, Real.log_inv]
  exact abs_le.mpr ⟨by linarith only [htu], htl'⟩

/-- The offset interval used to form the regular candidates has a universal numerical bound. -/
private theorem regular_offset_halfwidth :
    0 < Real.artanh (1 / Real.sqrt 2000) ∧ Real.artanh (1 / Real.sqrt 2000) ≤ 1 / 40 := by
  let d := 1 / Real.sqrt 2000
  have hroot : 41 ≤ Real.sqrt 2000 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hpos : 0 < d := by dsimp [d]; positivity
  have hdu : d ≤ 1 / 41 := one_div_le_one_div_of_le (by norm_num) hroot
  have hdlt : d < 1 := by linarith only [hdu]
  change 0 < Real.artanh d ∧ Real.artanh d ≤ 1 / 40
  refine ⟨Real.artanh_pos ⟨hpos, hdlt⟩, ?_⟩
  have h1 : 0 < 1 - d := sub_pos.mpr hdlt
  have harg : 0 < (1 + d) / (1 - d) := div_pos (by linarith only [hpos]) h1
  rw [Real.artanh_eq_half_log ⟨by linarith only [hpos], hdlt.le⟩]
  have hlog := Real.log_le_sub_one_of_pos harg
  have hquot : (1 + d) / (1 - d) - 1 ≤ 1 / 20 := by
    apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ h1).mpr
    linarith only [hdu]
  linarith only [hlog, hquot]

end BilateralProfitRegular
end BundlePart007


section BundlePart008


namespace BilateralProfitRegular

open Set MeasureTheory MechanismDesign.BilateralTrade
open scoped Topology

/-- A single reciprocal-convexity argument for an increasing CDF and a decreasing tail.
The sign `d` is `1` for the CDF and `-1` for the tail. Absolute continuity of the primitive
allows pointwise virtual-price monotonicity to be used with its almost-everywhere derivative. -/
private theorem reciprocal_convex_of_virtual
    (G f : ℝ → ℝ) (d : ℝ) (hd : d ^ 2 = 1)
    (hG : ∀ x ∈ Ioo 0 1, 0 < G x) (hf : ∀ x ∈ Ioo 0 1, 0 < f x)
    (ha : AbsolutelyContinuousOnInterval G 0 1)
    (hderiv : ∀ᵐ x ∂volume, x ∈ Ioo 0 1 → HasDerivAt G (d * f x) x)
    (hmono : MonotoneOn (fun x => x + d * G x / f x) (Ioo 0 1)) :
    ConvexOn ℝ (Ioo 0 1) (fun x => 1 / G x) := by
  let V (x : ℝ) := x + d * G x / f x
  have hV : MonotoneOn V (Ioo 0 1) := hmono
  have htangent (x : ℝ) (hx : x ∈ Ioo 0 1) (y : ℝ) (hy : y ∈ Ioo 0 1) :
      1 / G x - d * f x / (G x)^2 * (y - x) ≤ 1 / G y := by
    let L (t : ℝ) := d * (V x - t)
    let W (t : ℝ) := G t * L t
    have haL : AbsolutelyContinuousOnInterval L 0 1 := by
      have hdiff : ContDiff ℝ 1 L := by unfold L; fun_prop
      exact hdiff.contDiffOn.absolutelyContinuousOnInterval
    have haW : AbsolutelyContinuousOnInterval W 0 1 := ha.fun_mul haL
    have hL (t : ℝ) : HasDerivAt L (-d) t := by
      simpa only [L, id_eq, mul_neg, mul_one] using
        (((hasDerivAt_id t).const_sub (V x)).const_mul d)
    have he : ∀ᵐ t ∂volume, t ∈ Ioo 0 1 → deriv W t = f t * (V x - V t) := by
      filter_upwards [hderiv] with t ht htI
      have hw := ((ht htI).mul (hL t)).deriv
      change deriv W t = _ at hw
      rw [hw]
      have hf' := (hf t htI).ne'
      have hterm : f t * (d * G t / f t) = d * G t := by field_simp
      calc
        d * f t * L t + G t * (-d) =
            d^2 * (f t * (V x - t)) - d * G t := by unfold L; ring
        _ = f t * (V x - V t) := by
          rw [hd, one_mul, show V t = t + d * G t / f t from rfl]
          rw [show f t * (V x - (t + d * G t / f t)) =
            f t * (V x - t) - f t * (d * G t / f t) from by ring, hterm]
    have hint {a b : ℝ} (ha' : a ∈ Ioo 0 1) (hb' : b ∈ Ioo 0 1) (hab : a ≤ b) :
        ∫ t in a..b, deriv W t = W b - W a := by
      apply (haW.mono _).integral_deriv_eq_sub
      rw [uIcc_of_le hab, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc ha'.1.le hb'.2.le
    have hW : W y ≤ W x := by
      rcases le_total y x with hyx | hxy
      · have hn : 0 ≤ ∫ t in y..x, deriv W t := by
          apply intervalIntegral.integral_nonneg_of_ae_restrict hyx
          rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
          filter_upwards [he] with t ht htI
          have ht' : t ∈ Ioo 0 1 := ⟨hy.1.trans_le htI.1, htI.2.trans_lt hx.2⟩
          change 0 ≤ deriv W t
          rw [ht ht']
          exact mul_nonneg (hf t ht').le (sub_nonneg.mpr (hV ht' hx htI.2))
        rw [hint hy hx hyx] at hn
        exact sub_nonneg.mp hn
      · have hn : 0 ≤ ∫ t in x..y, -deriv W t := by
          apply intervalIntegral.integral_nonneg_of_ae_restrict hxy
          rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
          filter_upwards [he] with t ht htI
          have ht' : t ∈ Ioo 0 1 := ⟨hx.1.trans_le htI.1, htI.2.trans_lt hy.2⟩
          change 0 ≤ -deriv W t
          rw [ht ht']
          exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hf t ht').le
            (sub_nonpos.mpr (hV hx ht' htI.1)))
        rw [intervalIntegral.integral_neg, hint hx hy hxy] at hn
        linarith only [hn]
    have hfactor (t : ℝ) : L t = G x / f x - d * (t - x) := by
      unfold L V
      calc
        d * (x + d * G x / f x - t) = d^2 * (G x / f x) - d * (t - x) := by ring
        _ = _ := by rw [hd, one_mul]
    have hx' := hG x hx
    have hy' := hG y hy
    have hf' := hf x hx
    have hscaled := mul_le_mul_of_nonneg_right hW hf'.le
    change G y * L y * f x ≤ G x * L x * f x at hscaled
    rw [hfactor, hfactor, sub_self, mul_zero, sub_zero] at hscaled
    have hh : G x / f x * f x = G x := div_mul_cancel₀ _ hf'.ne'
    calc
      1 / G x - d * f x / G x ^ 2 * (y - x) =
          (G x - d * (y - x) * f x) / G x ^ 2 := by
        field_simp [hx'.ne']
      _ ≤ 1 / G y := by
        apply (div_le_div_iff₀ (pow_pos hx' _) hy').mpr
        calc
          (G x - d * (y - x) * f x) * G y = G y * (G x / f x - d * (y - x)) * f x := by
            field_simp [hf'.ne']
          _ ≤ G x * (G x / f x) * f x := hscaled
          _ = 1 * G x ^ 2 := by rw [mul_assoc, hh]; ring
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x hx y hy a b ha' hb' hab
  let z := a * x + b * y
  have hz : z ∈ Ioo 0 1 := (convex_Ioo (0 : ℝ) 1) hx hy ha' hb' hab
  have hzx := mul_le_mul_of_nonneg_left (htangent z hz x hx) ha'
  have hzy := mul_le_mul_of_nonneg_left (htangent z hz y hy) hb'
  change 1 / G z ≤ a * (1 / G x) + b * (1 / G y)
  calc
    1 / G z =
        a * (1 / G z - d * f z / G z ^ 2 * (x - z)) +
          b * (1 / G z - d * f z / G z ^ 2 * (y - z)) := by
      have he : a * (x - z) + b * (y - z) = 0 := by
        calc
          a * (x - z) + b * (y - z) = (a * x + b * y) - (a + b) * z := by ring
          _ = 0 := by rw [hab, one_mul]; exact sub_self z
      linear_combination -(1 / G z) * hab + d * f z / G z ^ 2 * he
    _ ≤ _ := add_le_add hzx hzy

private theorem cdfS_reciprocal_convex (E : Environment) (hE : RegularUnit E) :
    ConvexOn ℝ (Ioo 0 1) (fun p => 1 / E.cdfS p) := by
  have hf : IntervalIntegrable E.fS volume 0 1 := by
    simpa only [hE.1.1, hE.1.2.1] using E.fS_intervalIntegrable
  have hc : E.cdfS = fun x => ∫ t in 0..x, E.fS t := by
    funext x
    rw [Environment.cdfS, hE.1.1]
  have ha : AbsolutelyContinuousOnInterval E.cdfS 0 1 := by
    rw [hc]
    exact hf.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  refine reciprocal_convex_of_virtual E.cdfS E.fS 1 (by norm_num)
    (fun x hx => cdfS_pos E hE.1 ⟨hx.1, hx.2.le⟩) ?_ ha ?_ ?_
  · intro x hx
    exact E.fS_pos x (by rw [hE.1.1, hE.1.2.1]; exact Ioo_subset_Icc_self hx)
  · rw [hc]
    filter_upwards [hf.ae_hasDerivAt_integral] with x hx hx'
    simpa only [one_mul] using
      hx (by rw [uIcc_of_le zero_le_one]; exact Ioo_subset_Icc_self hx') 0 left_mem_uIcc
  · have hm := hE.2.1
    rw [hE.1.1, hE.1.2.1] at hm
    intro x hx y hy hxy
    simp only [one_mul]
    exact hm (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hxy

private theorem tailB_reciprocal_convex (E : Environment) (hE : RegularUnit E) :
    ConvexOn ℝ (Ioo 0 1) (fun q => 1 / (1 - E.cdfB q)) := by
  have hf : IntervalIntegrable E.fB volume 0 1 := by
    simpa only [hE.1.2.2.1, hE.1.2.2.2] using E.fB_intervalIntegrable
  have hc : E.cdfB = fun x => ∫ t in 0..x, E.fB t := by
    funext x
    rw [Environment.cdfB, hE.1.2.2.1]
  have ha : AbsolutelyContinuousOnInterval E.cdfB 0 1 := by
    rw [hc]
    exact hf.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 1 :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ))).contDiffOn.absolutelyContinuousOnInterval
  refine reciprocal_convex_of_virtual (fun q => 1 - E.cdfB q) E.fB (-1) (by norm_num)
    (fun x hx => tailB_pos E hE.1 ⟨hx.1.le, hx.2⟩) ?_ (hconst.sub ha) ?_ ?_
  · intro x hx
    exact E.fB_pos x (by rw [hE.1.2.2.1, hE.1.2.2.2]; exact Ioo_subset_Icc_self hx)
  · rw [hc]
    filter_upwards [hf.ae_hasDerivAt_integral] with x hx hx'
    have hd := hx (by rw [uIcc_of_le zero_le_one]; exact Ioo_subset_Icc_self hx') 0 left_mem_uIcc
    simpa only [neg_mul, one_mul] using hd.const_sub 1
  · have hm := hE.2.2
    rw [hE.1.2.2.1, hE.1.2.2.2] at hm
    intro x hx y hy hxy
    simp only [neg_mul, one_mul, neg_div, ← sub_eq_add_neg]
    exact hm (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hxy

end BilateralProfitRegular
end BundlePart008


section BundlePart009



namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade

private theorem pos_weighted_add {a b s t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hs : 0 < s) (ht : 0 < t) :
    0 < a * s + b * t := by
  by_cases h : a = 0
  · have hb' : 0 < b := by linarith only [h, hab]
    simpa [h] using mul_pos hb' ht
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm h)) hs)
      (mul_nonneg hb ht.le)

private theorem convex_intT : Convex ℝ intT := by
  intro x hx y hy a b ha hb hab
  refine ⟨pos_weighted_add ha hb hab hx.1 hy.1, ?_, ?_⟩
  · have h := pos_weighted_add ha hb hab (sub_pos.mpr hx.2.1) (sub_pos.mpr hy.2.1)
    change a * x.1 + b * y.1 < a * x.2 + b * y.2
    linarith only [h]
  · have h := pos_weighted_add ha hb hab (sub_pos.mpr hx.2.2) (sub_pos.mpr hy.2.2)
    change a * x.2 + b * y.2 < 1
    linarith only [h, hab]

private theorem weighted_sq_div_le {a b s t X Y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hs : 0 < s) (ht : 0 < t) :
    (a * X + b * Y) ^ 2 / (a * s + b * t) ≤ a * (X ^ 2 / s) + b * (Y ^ 2 / t) := by
  apply (div_le_iff₀ (pos_weighted_add ha hb hab hs ht)).mpr
  apply le_of_mul_le_mul_right _ (mul_pos hs ht)
  have he :
      (a * (X^2 / s) + b * (Y^2 / t)) * (a * s + b * t) * (s * t) -
        (a * X + b * Y)^2 * (s * t) = a * b * (t * X - s * Y)^2 := by
    field_simp [hs.ne', ht.ne']
    ring
  linarith only [he, mul_nonneg (mul_nonneg ha hb) (sq_nonneg (t * X - s * Y))]

private theorem auxProfit_reciprocal_convex (E : Environment) (hE : RegularUnit E) {lam : ℝ}
    (hlam : 0 < lam) : ConvexOn ℝ intT (fun x => 1 / auxProfit E lam x) := by
  let u (x : ℝ × ℝ) := lam / E.cdfS x.1 + lam⁻¹ / (1 - E.cdfB x.2)
  let g (x : ℝ × ℝ) := 4 * (x.2 - x.1)
  have hu {x : ℝ × ℝ} (hx : x ∈ intT) : 0 < u x :=
    add_pos (div_pos hlam (intT_cdf_pos E hE.1 hx).1)
      (div_pos (inv_pos.mpr hlam) (intT_cdf_pos E hE.1 hx).2)
  refine ⟨convex_intT, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hz : z ∈ intT := convex_intT hx hy ha hb hab
  have hx₁ : x.1 ∈ Ioo 0 1 := ⟨hx.1, hx.2.1.trans hx.2.2⟩
  have hy₁ : y.1 ∈ Ioo 0 1 := ⟨hy.1, hy.2.1.trans hy.2.2⟩
  have hx₂ : x.2 ∈ Ioo 0 1 := ⟨hx.1.trans hx.2.1, hx.2.2⟩
  have hy₂ : y.2 ∈ Ioo 0 1 := ⟨hy.1.trans hy.2.1, hy.2.2⟩
  have hCs := (cdfS_reciprocal_convex E hE).2 hx₁ hy₁ ha hb hab
  have hCb := (tailB_reciprocal_convex E hE).2 hx₂ hy₂ ha hb hab
  change 1 / E.cdfS z.1 ≤ a * (1 / E.cdfS x.1) + b * (1 / E.cdfS y.1) at hCs
  change 1 / (1 - E.cdfB z.2) ≤
    a * (1 / (1 - E.cdfB x.2)) + b * (1 / (1 - E.cdfB y.2)) at hCb
  have huc : u z ≤ a * u x + b * u y := by
    have hS := mul_le_mul_of_nonneg_left hCs hlam.le
    have hB := mul_le_mul_of_nonneg_left hCb (inv_nonneg.mpr hlam.le)
    dsimp only [u]
    simp only [div_eq_mul_inv, one_mul] at hS hB ⊢
    linarith only [hS, hB]
  have gpos {x : ℝ × ℝ} (hx : x ∈ intT) : 0 < g x :=
    mul_pos (by norm_num) (sub_pos.mpr hx.2.1)
  have hg : g z = a * g x + b * g y := by
    change 4 * ((a * x.2 + b * y.2) - (a * x.1 + b * y.1)) = _
    unfold g
    ring
  have he (w : ℝ × ℝ) : 1 / auxProfit E lam w = u w ^ 2 / g w := by
    simp only [auxProfit, one_div, inv_div, u, g]
  change 1 / auxProfit E lam z ≤ a * (1 / auxProfit E lam x) + b * (1 / auxProfit E lam y)
  simp only [he]
  calc
    u z ^ 2 / g z ≤ (a * u x + b * u y) ^ 2 / g z :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (hu hz).le huc 2) (gpos hz).le
    _ ≤ _ := by rw [hg]; exact weighted_sq_div_le ha hb hab (gpos hx) (gpos hy)

private theorem lemma_6_2 (E : Environment) (hE : RegularUnit E) (lam : ℝ) (hlam : 0 < lam) :
    ConvexOn ℝ intT (fun x => 1 / auxProfit E lam x) ∧
    ∀ x ∈ intT,
      auxProfit E lam x =
          mu E x * (2 / (Real.exp (Real.log (lam / balance E x)) +
            Real.exp (-Real.log (lam / balance E x)))) ^ 2 ∧
        0 ≤ mu E x - auxProfit E lam x ∧
        mu E x - auxProfit E lam x ≤ mu E x * Real.log (lam / balance E x) ^ 2 ∧
        0 < auxProfit E lam x ∧ auxProfit E lam x ≤ mu E x ∧
        auxProfit E (balance E x) x = mu E x ∧
        ∀ θ : ℝ, muStar E - auxProfit E (lam * Real.exp θ) x ≤
          2 * (muStar E - auxProfit E lam x) + 2 * muStar E * θ ^ 2 := by
  refine ⟨auxProfit_reciprocal_convex E hE hlam, ?_⟩
  intro x hx
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := auxProfit_values E hE.1 hlam hx
  exact ⟨auxProfit_sech E hE.1 hlam hx, h₁, h₂, h₃, h₄, h₅,
    auxProfit_perturbation E hE.1 hlam hx⟩

/-- A common lower bound on auxiliary profit persists over the convex hull. -/
private theorem auxProfit_lower_convexHull (E : Environment) (hE : RegularUnit E) {lam : ℝ}
    (hlam : 0 < lam) {S : Set (ℝ × ℝ)} (hS : S ⊆ intT) {r : ℝ} (hr : 0 < r)
    (h : ∀ x ∈ S, r ≤ auxProfit E lam x) :
    ∀ x ∈ convexHull ℝ S, x ∈ intT ∧ r ≤ auxProfit E lam x := by
  have hs : S ⊆ {x ∈ intT | 1 / auxProfit E lam x ≤ 1 / r} := by
    intro x hx
    exact ⟨hS hx, one_div_le_one_div_of_le hr (h x hx)⟩
  have hsub := convexHull_min hs ((auxProfit_reciprocal_convex E hE hlam).convex_le (1 / r))
  intro x hx
  obtain ⟨hxi, hxv⟩ := hsub hx
  exact ⟨hxi, le_of_one_div_le_one_div (auxProfit_pos E hE.1 hlam hxi) hxv⟩

end BilateralProfitRegular
end BundlePart009


section BundlePart010


namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade

private theorem lemma_6_3 (E : Environment) (hE : RegularUnit E) (lam : ℝ) (hlam : 0 < lam)
    (x z : ℝ × ℝ) (hx : x ∈ intT) (hz : z ∈ intT)
    (hrx : 99 / 100 * muStar E ≤ auxProfit E lam x)
    (hrz : 99 / 100 * muStar E ≤ auxProfit E lam z) :
    (x.1, z.2) ∈ triT ∧ (z.1, x.2) ∈ triT ∧
    muStar E - mu E (x.1, z.2) ≤
      4 * (muStar E - auxProfit E lam x + (muStar E - auxProfit E lam z)) ∧
    muStar E - mu E (z.1, x.2) ≤
      4 * (muStar E - auxProfit E lam x + (muStar E - auxProfit E lam z)) ∧
    ∀ a ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ)),
      ∀ b ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ)), P E a ≤ 3 * P E b := by
  let M := muStar E
  have hM : 0 < M := (onUnit_facts E hE.1).2.2.2.1.1
  let A (t : ℝ × ℝ) := lam / E.cdfS t.1
  let B (t : ℝ × ℝ) := lam⁻¹ / (1 - E.cdfB t.2)
  let H (t : ℝ × ℝ) := (A t + B t) / 2
  let D (t : ℝ × ℝ) := (A t - B t) / 2
  let Δ (t : ℝ × ℝ) := M - auxProfit E lam t
  have hA {t : ℝ × ℝ} (ht : t ∈ intT) : 0 < A t :=
    div_pos hlam (intT_cdf_pos E hE.1 ht).1
  have hB {t : ℝ × ℝ} (ht : t ∈ intT) : 0 < B t :=
    div_pos (inv_pos.mpr hlam) (intT_cdf_pos E hE.1 ht).2
  have hH {t : ℝ × ℝ} (ht : t ∈ intT) : 0 < H t :=
    div_pos (add_pos (hA ht) (hB ht)) (by norm_num)
  have hmem {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      (s.1, t.2) ∈ BilateralProfitMHR.unitSq :=
    ⟨(intT_subset_unitSq hs).1, (intT_subset_unitSq ht).2⟩
  have hP {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      P E (s.1,t.2) * (A s * B t) = 1 := by
    rw [P_factor E hE.1 (hmem hs ht)]
    dsimp [A, B]
    have hs' := (intT_cdf_pos E hE.1 hs).1.ne'
    have ht' := (intT_cdf_pos E hE.1 ht).2.ne'
    field_simp [hlam.ne']
  have hPpos {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      0 < P E (s.1,t.2) := by
    rw [P_factor E hE.1 (hmem hs ht)]
    exact mul_pos (intT_cdf_pos E hE.1 hs).1 (intT_cdf_pos E hE.1 ht).2
  have hspread {t : ℝ × ℝ} (ht : t ∈ intT) :
      auxProfit E lam t * H t ^ 2 = t.2 - t.1 := by
    change (4 * (t.2 - t.1) / (A t + B t) ^ 2) * ((A t + B t) / 2) ^ 2 = _
    have hp := (add_pos (hA ht) (hB ht)).ne'
    field_simp
    ring
  have hdev {t : ℝ × ℝ} (ht : t ∈ intT) : M * D t ^ 2 ≤ Δ t * H t ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right (mu_le_muStar E hE.1 (intT_subset_unitSq ht))
      (mul_pos (hA ht) (hB ht)).le
    rw [mu_formula, mul_assoc, hP ht ht, mul_one] at hh
    have he : A t * B t = H t ^ 2 - D t ^ 2 := by unfold H D; ring
    rw [he, ← hspread ht] at hh
    dsimp [Δ]
    linarith only [hh]
  have hΔ {t : ℝ × ℝ} (ht : t ∈ intT) : 0 ≤ Δ t :=
    nonneg_of_mul_nonneg_left
      ((mul_nonneg hM.le (sq_nonneg _)).trans (hdev ht)) (pow_pos (hH ht) _)
  have hbds {t : ℝ × ℝ} (ht : t ∈ intT) (hr : 99 / 100 * M ≤ auxProfit E lam t) :
      9 / 10 * H t ≤ A t ∧ A t ≤ 11 / 10 * H t ∧
      9 / 10 * H t ≤ B t ∧ B t ≤ 11 / 10 * H t := by
    have hd : Δ t ≤ M / 100 := by dsimp [Δ]; linarith
    have hs := (hdev ht).trans (mul_le_mul_of_nonneg_right hd (sq_nonneg (H t)))
    have hh : D t ^ 2 ≤ (H t / 10) ^ 2 := by
      apply le_of_mul_le_mul_left _ hM
      nlinarith only [hs]
    have habs : |D t| ≤ H t / 10 := by
      rw [← sq_abs (D t)] at hh
      exact le_of_pow_le_pow_left₀ (by decide) (by linarith only [hH ht]) hh
    obtain ⟨hl, hu⟩ := abs_le.mp habs
    unfold D H at hl hu
    unfold H
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  let G (s t : ℝ × ℝ) := M - mu E (s.1,t.2)
  have hG {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) : 0 ≤ G s t :=
    sub_nonneg.mpr (mu_le_muStar E hE.1 (hmem hs ht))
  have hG_eq {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT) :
      G s t * (A s * B t) = M * (A s * B t) - (t.2 - s.1) := by
    change (M - mu E (s.1,t.2)) * _ = _
    rw [sub_mul, mu_formula, mul_assoc, hP hs ht, mul_one]
  let S := G x z * (A x * B z) + G z x * (A z * B x)
  have hS0 : 0 ≤ S := add_nonneg (mul_nonneg (hG hx hz) (mul_pos (hA hx) (hB hz)).le)
    (mul_nonneg (hG hz hx) (mul_pos (hA hz) (hB hx)).le)
  have hS :
      S = Δ x * H x ^ 2 + Δ z * H z ^ 2 - M * (H x - H z) ^ 2 - 2 * M * D x * D z := by
    unfold S
    rw [hG_eq hx hz, hG_eq hz hx]
    have he : (z.2 - x.1) + (x.2 - z.1) = (x.2 - x.1) + (z.2 - z.1) := by ring
    rw [sub_add_sub_comm, he, ← hspread hx, ← hspread hz]
    unfold Δ D H
    ring
  have hcross : -(2 * M * D x * D z) ≤ M * D x ^ 2 + M * D z ^ 2 := by
    nlinarith only [mul_nonneg hM.le (sq_nonneg (D x + D z))]
  let m := max (H x) (H z)
  have hm : 0 < m := (hH hx).trans_le (le_max_left _ _)
  have hm₁ : H x ≤ m := le_max_left _ _
  have hm₂ : H z ≤ m := le_max_right _ _
  have hΔm : Δ x + Δ z ≤ M / 50 := by dsimp [Δ]; linarith only [hrx, hrz]
  have hSle : S ≤ 2 * (Δ x + Δ z) * m ^ 2 - M * (H x - H z) ^ 2 := by
    have hh₁ : H x ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (hH hx).le hm₁ 2
    have hh₂ : H z ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (hH hz).le hm₂ 2
    rw [hS]
    linarith only [hcross, hdev hx, hdev hz, mul_le_mul_of_nonneg_left hh₁ (hΔ hx),
      mul_le_mul_of_nonneg_left hh₂ (hΔ hz)]
  have hdiff : |H x - H z| ≤ m / 5 := by
    have hb := mul_le_mul_of_nonneg_right hΔm (sq_nonneg m)
    have ht : (H x - H z)^2 ≤ (m / 5)^2 := by
      apply le_of_mul_le_mul_left _ hM
      nlinarith only [hS0, hSle, hb]
    rw [← sq_abs (H x - H z)] at ht
    exact le_of_pow_le_pow_left₀ (by decide) (by linarith only [hm]) ht
  obtain ⟨hmd₁, hmd₂⟩ := abs_le.mp hdiff
  have hmin₁ : 4 / 5 * m ≤ H x := by
    dsimp [m] at hmd₁ ⊢
    rcases le_total (H x) (H z) with h | h
    · rw [max_eq_right h] at hmd₁ ⊢
      linarith only [hmd₁]
    · rw [max_eq_left h]
      linarith only [hH hx]
  have hmin₂ : 4 / 5 * m ≤ H z := by
    dsimp [m] at hmd₂ ⊢
    rcases le_total (H x) (H z) with h | h
    · rw [max_eq_right h]
      linarith only [hH hz]
    · rw [max_eq_left h] at hmd₂ ⊢
      linarith only [hmd₂]
  have hprod : 4 / 5 * m ^ 2 ≤ H x * H z := by
    by_cases h : H x ≤ H z
    · have he : m = H z := max_eq_right h
      calc
        (4 / 5) * m ^ 2 = (4 / 5 * m) * H z := by rw [he]; ring
        _ ≤ H x * H z := mul_le_mul_of_nonneg_right hmin₁ (hH hz).le
    · have he : m = H x := max_eq_left (le_of_not_ge h)
      calc
        (4 / 5) * m ^ 2 = H x * (4 / 5 * m) := by rw [he]; ring
        _ ≤ H x * H z := mul_le_mul_of_nonneg_left hmin₂ (hH hx).le
  obtain ⟨hax₁, hax₂, hbx₁, hbx₂⟩ := hbds hx hrx
  obtain ⟨haz₁, haz₂, hbz₁, hbz₂⟩ := hbds hz hrz
  have hab₁ : 16 / 25 * m ^ 2 ≤ A x * B z := by
    have he := mul_le_mul hax₁ hbz₁ (by linarith only [hH hz]) (hA hx).le
    nlinarith only [he, hprod]
  have hab₂ : 16 / 25 * m ^ 2 ≤ A z * B x := by
    have he := mul_le_mul haz₁ hbx₁ (by linarith only [hH hx]) (hA hz).le
    nlinarith only [he, hprod]
  have hGle {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT)
      (hab : 16 / 25 * m ^ 2 ≤ A s * B t) (hg : G s t * (A s * B t) ≤ S) :
      G s t ≤ 4 * (Δ x + Δ z) := by
    have hlow := mul_le_mul_of_nonneg_left hab (hG hs ht)
    have hpos : 0 < m ^ 2 := pow_pos hm _
    have hd := add_nonneg (hΔ hx) (hΔ hz)
    apply le_of_mul_le_mul_right _ hpos
    nlinarith only [hlow, hg, hSle, mul_nonneg hM.le (sq_nonneg (H x - H z)),
      mul_nonneg hd hpos.le]
  have hG₁ := hGle hx hz hab₁
    (le_add_of_nonneg_right (mul_nonneg (hG hz hx) (mul_pos (hA hz) (hB hx)).le))
  have hG₂ := hGle hz hx hab₂
    (le_add_of_nonneg_left (mul_nonneg (hG hx hz) (mul_pos (hA hx) (hB hz)).le))
  have htri {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT)
      (hg : G s t ≤ 4 * (Δ x + Δ z)) : (s.1, t.2) ∈ triT := by
    have hp : 0 < mu E (s.1,t.2) := by dsimp [G] at hg; linarith only [hM, hg, hΔm]
    exact ⟨hs.1.le, le_of_lt ((onUnit_facts E hE.1).2.2.1 _ (hmem hs ht) |>.mp hp).2.1,
      ht.2.2.le⟩
  refine ⟨htri hx hz hG₁, htri hz hx hG₂, hG₁, hG₂, ?_⟩
  have hProb {s t : ℝ × ℝ} (hs : s ∈ intT) (ht : t ∈ intT)
      (ha₁ : 9 / 10 * H s ≤ A s) (ha₂ : A s ≤ 11 / 10 * H s)
      (hb₁ : 9 / 10 * H t ≤ B t) (hb₂ : B t ≤ 11 / 10 * H t)
      (hm_s : 4 / 5 * m ≤ H s) (hm_t : 4 / 5 * m ≤ H t)
      (hs_m : H s ≤ m) (ht_m : H t ≤ m) :
      1 / ((11 / 10 * m) ^ 2) ≤ P E (s.1,t.2) ∧
        P E (s.1,t.2) ≤ 1 / ((18 / 25 * m) ^ 2) := by
    have hloA : 18 / 25 * m ≤ A s := by linarith only [ha₁, hm_s]
    have hloB : 18 / 25 * m ≤ B t := by linarith only [hb₁, hm_t]
    have hhiA : A s ≤ 11 / 10 * m := by linarith only [ha₂, hs_m]
    have hhiB : B t ≤ 11 / 10 * m := by linarith only [hb₂, ht_m]
    have he := hP hs ht
    have hv := (hPpos hs ht).le
    constructor
    · have hbound := mul_le_mul hhiA hhiB (hB ht).le (by linarith only [hm])
      apply (div_le_iff₀ (pow_pos (by linarith only [hm] : 0 < 11 / 10 * m) _)).mpr
      simpa only [sq, mul_comm (P E (s.1,t.2))] using
        he.symm.le.trans (mul_le_mul_of_nonneg_left hbound hv)
    · have hbound := mul_le_mul hloA hloB (by linarith only [hm]) (hA hs).le
      apply (le_div_iff₀ (pow_pos (by linarith only [hm] : 0 < 18 / 25 * m) _)).mpr
      simpa only [sq] using
        (mul_le_mul_of_nonneg_left hbound hv).trans he.le
  have hPall (a : ℝ × ℝ) (ha : a ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ))) :
      1 / ((11 / 10 * m) ^ 2) ≤ P E a ∧ P E a ≤ 1 / ((18 / 25 * m) ^ 2) := by
    simp only [mem_insert_iff, mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hProb hx hx hax₁ hax₂ hbx₁ hbx₂ hmin₁ hmin₁ hm₁ hm₁
    · exact hProb hz hz haz₁ haz₂ hbz₁ hbz₂ hmin₂ hmin₂ hm₂ hm₂
    · exact hProb hx hz hax₁ hax₂ hbz₁ hbz₂ hmin₁ hmin₂ hm₁ hm₂
    · exact hProb hz hx haz₁ haz₂ hbx₁ hbx₂ hmin₂ hmin₁ hm₂ hm₁
  intro a ha b hb
  apply (hPall a ha).2.trans
  apply le_trans _ (mul_le_mul_of_nonneg_left (hPall b hb).1 (by norm_num))
  rw [mul_one_div]
  apply (div_le_div_iff₀ (pow_pos (by linarith only [hm] : 0 < 18 / 25 * m) _)
    (pow_pos (by linarith only [hm] : 0 < 11 / 10 * m) _)).mpr
  nlinarith only [sq_nonneg m]

end BilateralProfitRegular
end BundlePart010


section BundlePart011




namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade

/-- The deterministic grid and additional-sampling guarantees used in steps 3–7. -/
private structure InitCandidatesData (E : Environment) (T K : ℕ) (δ : ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) where
  regular : RegularUnit E
  K_pos : 0 < K
  δ_large : (2 : ℝ)^16 / (K : ℝ) ≤ δ
  δ_le_opt : δ ≤ muStar E
  opt_lt : muStar E < 6 * δ
  best : ℕ × ℕ
  best_mem : best ∈ actList K
  best_max : ∀ e ∈ actList K, mu E (gpt K e) ≤ mu E (gpt K best)
  best_approx : muStar E - 2 / (K : ℝ) ≤ mu E (gpt K best)
  best_scale : (23 / 17) * δ ≤ mu E (gpt K best)
  estimates : ∀ e ∈ actList K,
    0 ≤ phat T K δ (P E) U e ∧ phat T K δ (P E) U e ≤ 1 ∧
      |phat T K δ (P E) U e - P E (gpt K e)| ≤ (P E (gpt K e) + δ) / 32768

private def InitRetained (E : Environment) (T K : ℕ) (δ : ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) (e : ℕ × ℕ) : Prop :=
  e ∈ actList K ∧
    (1 - (2 : ℝ)^(-13 : ℤ)) * muhatStar T K δ (P E) U ≤ muhat T K δ (P E) U e

private theorem mem_actList_iff {K : ℕ} {e : ℕ × ℕ} :
    e ∈ actList K ↔ e.1 ≤ e.2 ∧ e.2 ≤ K := by
  rcases e with ⟨i,j⟩
  simp only [actList, List.mem_filter, decide_eq_true_eq]
  change ((i,j) ∈ List.range (K + 1) ×ˢ List.range (K + 1) ∧ i ≤ j) ↔ i ≤ j ∧ j ≤ K
  simp only [List.mem_product, List.mem_range, Nat.lt_succ_iff]
  omega

private theorem gpt_spread (K : ℕ) (e : ℕ × ℕ) :
    (gpt K e).2 - (gpt K e).1 = ((e.2 : ℝ) - e.1) / K := by
  simp only [gpt, sub_div]

private theorem gpt_mem_tri {K : ℕ} {e : ℕ × ℕ} (hK : 0 < K) (he : e ∈ actList K) :
    gpt K e ∈ triT := by
  obtain ⟨h₁, h₂⟩ := mem_actList_iff.mp he
  have hK' : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  exact ⟨div_nonneg (Nat.cast_nonneg _) hK'.le,
    div_le_div_of_nonneg_right (Nat.cast_le.mpr h₁) hK'.le,
    (div_le_iff₀ hK').mpr (by simpa using (Nat.cast_le.mpr h₂ : (e.2 : ℝ) ≤ K))⟩

private theorem triT_subset_unitSq : triT ⊆ BilateralProfitMHR.unitSq := by
  intro x hx
  exact ⟨⟨hx.1, hx.2.1.trans hx.2.2⟩, ⟨hx.1.trans hx.2.1, hx.2.2⟩⟩

private theorem gpt_spread_mem {K : ℕ} {e : ℕ × ℕ} (hK : 0 < K) (he : e ∈ actList K) :
    0 ≤ (gpt K e).2 - (gpt K e).1 ∧ (gpt K e).2 - (gpt K e).1 ≤ 1 := by
  have h := gpt_mem_tri hK he
  exact ⟨sub_nonneg.mpr h.2.1, by linarith only [h.1, h.2.2]⟩

private theorem fold_max_bounds {α : Type} (v : α → ℝ) (l : List α) (s : ℝ) :
    s ≤ l.foldl (fun a e => max a (v e)) s ∧
    (∀ e ∈ l, v e ≤ l.foldl (fun a e => max a (v e)) s) ∧
    ∀ r, s ≤ r → (∀ e ∈ l, v e ≤ r) → l.foldl (fun a e => max a (v e)) s ≤ r := by
  induction l generalizing s with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    obtain ⟨hle, hem, hge⟩ := ih (max s (v e))
    refine ⟨(le_max_left _ _).trans hle, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact (le_max_right _ _).trans hle
      · exact hem e' he'
    · intro r hs he
      exact hge r (max_le hs (he e (by simp))) (fun e' he' => he e' (by simp [he']))

section

variable {E : Environment} {T K : ℕ} {δ : ℝ}
  {U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval}

local notation "ph" => phat T K δ (P E) U
local notation "mh" => muhat T K δ (P E) U
local notation "mhS" => muhatStar T K δ (P E) U
local notation "ret" => InitRetained E T K δ U

private theorem InitCandidatesData.δ_pos (D : InitCandidatesData E T K δ U) : 0 < δ :=
  (div_pos (by norm_num) (Nat.cast_pos.mpr D.K_pos)).trans_le D.δ_large

private theorem InitCandidatesData.best_le_opt (D : InitCandidatesData E T K δ U) :
    mu E (gpt K D.best) ≤ muStar E :=
  mu_le_muStar E D.regular.1 (triT_subset_unitSq (gpt_mem_tri D.K_pos D.best_mem))

private theorem InitCandidatesData.δ_le_best (D : InitCandidatesData E T K δ U) :
    δ ≤ mu E (gpt K D.best) := by
  linarith only [D.δ_pos, D.best_scale]

private theorem InitCandidatesData.mu_le_P (D : InitCandidatesData E T K δ U)
    {e : ℕ × ℕ} (he : e ∈ actList K) : mu E (gpt K e) ≤ P E (gpt K e) := by
  rw [mu_formula]
  exact mul_le_of_le_one_left ((onUnit_facts E D.regular.1).1 _).1
    (gpt_spread_mem D.K_pos he).2

private theorem InitCandidatesData.mu_error (D : InitCandidatesData E T K δ U)
    {e : ℕ × ℕ} (he : e ∈ actList K) :
    |mh e - mu E (gpt K e)| ≤ mu E (gpt K D.best) / 16384 := by
  have hs := gpt_spread_mem D.K_pos he
  rw [muhat, ← gpt_spread, mu_formula E (gpt K e), ← mul_sub, abs_mul, abs_of_nonneg hs.1]
  apply (mul_le_mul_of_nonneg_left (D.estimates e he).2.2 hs.1).trans
  have hd := mul_le_of_le_one_left D.δ_pos.le hs.2
  have h := D.best_max e he
  rw [mu_formula E (gpt K e)] at h
  linarith only [hd, h, D.δ_le_best]

private theorem InitCandidatesData.muhatStar_bounds (D : InitCandidatesData E T K δ U) :
    (1 - 1 / 16384) * mu E (gpt K D.best) ≤ mhS ∧
    mhS ≤ (1 + 1 / 16384) * mu E (gpt K D.best) := by
  change _ ≤ (actList K).foldl (fun a e => max a (mh e)) 0 ∧
    (actList K).foldl (fun a e => max a (mh e)) 0 ≤ _
  have hf := fold_max_bounds mh (actList K) 0
  constructor
  · have hlo := (abs_le.mp (D.mu_error D.best_mem)).1
    apply le_trans _ (hf.2.1 _ D.best_mem)
    linarith only [hlo]
  · apply hf.2.2
    · linarith only [D.δ_pos, D.δ_le_best]
    · intro e he
      linarith only [(abs_le.mp (D.mu_error he)).2, D.best_max e he]

private theorem InitCandidatesData.best_retained (D : InitCandidatesData E T K δ U) :
    ret D.best := by
  refine ⟨D.best_mem, ?_⟩
  have he := (abs_le.mp (D.mu_error D.best_mem)).1
  have hu := D.muhatStar_bounds.2
  norm_num at *
  linarith only [he, hu, D.δ_pos, D.δ_le_best]

private theorem InitCandidatesData.retained_high_best (D : InitCandidatesData E T K δ U)
    {e : ℕ × ℕ} (he : ret e) :
    (1 - 1 / 4096 : ℝ) * mu E (gpt K D.best) ≤ mu E (gpt K e) := by
  have hr := he.2
  have he' := (abs_le.mp (D.mu_error he.1)).2
  have hlo := D.muhatStar_bounds.1
  norm_num at *
  linarith only [hr, he', hlo, D.δ_pos, D.δ_le_best]

private theorem InitCandidatesData.opt_approx_best (D : InitCandidatesData E T K δ U) :
    (1 - 1 / 32768 : ℝ) * muStar E ≤ mu E (gpt K D.best) := by
  have hh : (2 : ℝ)^16 / (K : ℝ) ≤ muStar E := D.δ_large.trans D.δ_le_opt
  have hscale : (2 : ℝ)^16 / (K : ℝ) = 32768 * (2 / (K : ℝ)) := by ring
  rw [hscale] at hh
  linarith only [hh, D.best_approx]

private theorem InitCandidatesData.retained_high (D : InitCandidatesData E T K δ U)
    {e : ℕ × ℕ} (he : ret e) :
    (1 - 3 / 10000 : ℝ) * muStar E ≤ mu E (gpt K e) := by
  have hM := (onUnit_facts E D.regular.1).2.2.2.1.1
  linarith only [D.retained_high_best he, D.opt_approx_best, hM]

private theorem InitCandidatesData.retained_interior (D : InitCandidatesData E T K δ U)
    {e : ℕ × ℕ} (he : ret e) : gpt K e ∈ intT := by
  have hpos := (mul_pos (by norm_num : (0 : ℝ) < 1 - 3/10000)
    (onUnit_facts E D.regular.1).2.2.2.1.1).trans_le (D.retained_high he)
  exact ((onUnit_facts E D.regular.1).2.2.1 _ (triT_subset_unitSq (gpt_mem_tri D.K_pos he.1))).mp hpos

private theorem InitCandidatesData.relative_error (D : InitCandidatesData E T K δ U)
    {e : ℕ × ℕ} (he : e ∈ actList K) (heδ : δ ≤ P E (gpt K e)) :
    (1 - 1 / 16384 : ℝ) * P E (gpt K e) ≤ ph e ∧
      ph e ≤ (1 + 1 / 16384 : ℝ) * P E (gpt K e) := by
  have hh := abs_le.mp (D.estimates e he).2.2
  exact ⟨by linarith only [hh.1, heδ], by linarith only [hh.2, heδ]⟩

private theorem InitCandidatesData.log_error (D : InitCandidatesData E T K δ U)
    {e : ℕ × ℕ} (he : e ∈ actList K) (heδ : δ ≤ P E (gpt K e)) :
    0 < ph e ∧ |Real.log (ph e) - Real.log (P E (gpt K e))| ≤ 1 / 1000 := by
  have hp := D.δ_pos.trans_le heδ
  obtain ⟨hl, hu⟩ := D.relative_error he heδ
  have hph := (mul_pos (by norm_num : (0 : ℝ) < 1 - 1/16384) hp).trans_le hl
  let r := ph e / P E (gpt K e)
  have hrpos := div_pos hph hp
  have hrlo : 1 - 1 / 16384 ≤ r := (le_div_iff₀ hp).mpr hl
  have hrhi : r ≤ 1 + 1 / 16384 := (div_le_iff₀ hp).mpr hu
  have hlogu := Real.log_le_sub_one_of_pos hrpos
  have hlogl := Real.log_le_sub_one_of_pos (inv_pos.mpr hrpos)
  have hri : r⁻¹ ≤ 1 + 1 / 1000 := by
    rw [← one_div]
    apply (div_le_iff₀ hrpos).mpr
    linarith only [hrlo]
  rw [Real.log_inv] at hlogl
  refine ⟨hph, ?_⟩
  have h : Real.log r = Real.log (ph e) - Real.log (P E (gpt K e)) := Real.log_div hph.ne' hp.ne'
  rw [← h]
  exact abs_le.mpr ⟨by linarith only [hlogl, hri], by linarith only [hlogu, hrhi]⟩

end

end BilateralProfitRegular
end BundlePart011


section BundlePart012




namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade

private theorem gridK_ge_two {η : ℝ} (hη : 0 < η) (hη₁ : η < 1) : 2 ≤ gridK η := by
  have hu : 1 < 1 / η := (lt_div_iff₀ hη).2 (by simpa)
  have h := Nat.le_ceil (1 / η)
  change 1 / η ≤ (gridK η : ℝ) at h
  exact_mod_cast hu.trans_le h

private theorem scale_pos (h : ℕ) : 0 < scale h := by unfold scale; positivity

private theorem scale_le_one (h : ℕ) : scale h ≤ 1 := by
  unfold scale
  exact pow_le_one₀ (by norm_num) (by norm_num)

private theorem scale_eq_inv_pow (h : ℕ) : scale h = ((2 : ℝ) ^ h)⁻¹ := by
  rw [scale, one_div, inv_pow]

private theorem scale_succ (h : ℕ) : scale h = 2 * scale (h + 1) := by
  unfold scale
  rw [pow_succ]
  ring

private theorem scale_ge_grid_inv {K h : ℕ} (hp : 2 ^ h ≤ K) : 1 / (K : ℝ) ≤ scale h := by
  have h' : (2 : ℝ) ^ h ≤ K := by exact_mod_cast hp
  rw [scale_eq_inv_pow, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) h'

private theorem mhrScale_some_spec {T K h : ℕ} {prob : ℝ × ℝ → ℝ} {U : InitUniforms}
    (hf : mhrScale T K prob U = some h) :
    mhrTriggers T K prob U h ∧ ∀ j < h, ¬ mhrTriggers T K prob U j := by
  classical
  unfold mhrScale at hf
  obtain ⟨htr, i, hi, hi', hprev⟩ := List.find?_eq_some_iff_getElem.mp hf
  rw [List.getElem_range] at hi'
  subst i
  refine ⟨of_decide_eq_true htr, ?_⟩
  intro j hj
  have hh := hprev j hj
  simpa only [List.getElem_range, Bool.not_eq_true', decide_eq_false_iff_not] using hh

private theorem mhrScale_none_spec {T K : ℕ} {prob : ℝ × ℝ → ℝ} {U : InitUniforms}
    (hf : mhrScale T K prob U = none) {h : ℕ} (hK : h ≤ K) :
    ¬ mhrTriggers T K prob U h := by
  unfold mhrScale at hf
  have he := List.find?_eq_none.mp hf h (List.mem_range.mpr (Nat.lt_succ_of_le hK))
  simpa only [decide_eq_true_eq] using he

private theorem integrable_grid_profit (D : Measure (ℝ × ℝ)) [IsFiniteMeasure D]
    (a : ℝ × ℝ) : Integrable (fun v => BilateralProfit.profit v a) D := by
  have hs : MeasurableSet {v | BilateralProfit.Trades v a} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_const measurable_snd)
  have hM : Measurable fun v => BilateralProfit.tradeBit v a :=
    measurable_const.piecewise hs measurable_const
  have hi : Integrable (fun v => BilateralProfit.tradeBit v a) D := by
    apply (integrable_const (1 : ℝ)).mono' hM.aestronglyMeasurable
    exact ae_of_all _ (fun v => by unfold BilateralProfit.tradeBit; split_ifs <;> norm_num)
  exact hi.const_mul _

private theorem integral_profit_eq (D : Measure (ℝ × ℝ)) (a : ℝ × ℝ) :
    (∫ v, BilateralProfit.profit v a ∂D) = BilateralProfit.muP D a := by
  have hs : MeasurableSet {v | BilateralProfit.Trades v a} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_const measurable_snd)
  have hb : (∫ v, BilateralProfit.tradeBit v a ∂D) = BilateralProfit.Ptrade D a := by
    simpa only [BilateralProfit.Ptrade, BilateralProfit.tradeBit, Set.indicator,
      Set.mem_ofPred_eq, measureReal_def, Pi.one_apply] using
      (integral_indicator_one (μ := D) hs :
        (∫ v, {v | BilateralProfit.Trades v a}.indicator (fun _ => (1 : ℝ)) v ∂D) = _)
  unfold BilateralProfit.profit BilateralProfit.muP
  rw [integral_const_mul, hb]

/-- The grid has a maximizer and its value is within two grid spacings of the optimum. -/
private theorem exists_regular_grid_best (K : ℕ) (hK : 0 < K) (E : Environment) (hE : OnUnit E) :
    ∃ best ∈ actList K,
      (∀ e ∈ actList K, mu E (gpt K e) ≤ mu E (gpt K best)) ∧
      muStar E - 2 / (K : ℝ) ≤ mu E (gpt K best) := by
  classical
  have hnonempty : (actList K).toFinset.Nonempty :=
    ⟨(0, 0), List.mem_toFinset.mpr (mem_actList_iff.mpr (by simp))⟩
  obtain ⟨best, hbest, hbmax⟩ := Finset.exists_max_image (actList K).toFinset
    (fun e => mu E (gpt K e)) hnonempty
  have hmax (e : ℕ × ℕ) (he : e ∈ actList K) : mu E (gpt K e) ≤ mu E (gpt K best) :=
    hbmax e (List.mem_toFinset.mpr he)
  refine ⟨best, List.mem_toFinset.mp hbest, hmax, ?_⟩
  obtain ⟨a, ha, hStar⟩ := (onUnit_facts E hE).2.2.2.2.2
  obtain ⟨e, he, _⟩ :=
    BilateralProfit.lemma_A_6 K (by omega) a.1 a.2 ha.1.le ha.2.1.le ha.2.2.le
  let v : ℕ × ℕ := (e.1.1, e.1.2)
  have hv : v ∈ actList K := mem_actList_iff.mpr ⟨e.2, Nat.le_of_lt_succ e.1.2.isLt⟩
  have heq : BilateralProfit.pt K e.1 = gpt K v := rfl
  rw [heq] at he
  have := (BilateralProfitMHR.positive_density_profit_facts E hE).1
  have hi := integral_mono (integrable_grid_profit E.prior a)
    ((integrable_grid_profit E.prior (gpt K v)).add (integrable_const (2 / (K : ℝ))))
      (fun w => he w.1 w.2)
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_grid_profit E.prior (gpt K v)) (integrable_const _),
    integral_profit_eq, integral_profit_eq, integral_const] at hi
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hi
  change mu E a ≤ mu E (gpt K v) + 2 / (K : ℝ) at hi
  rw [hStar] at hi
  linarith only [hi, hmax v hv]

private theorem nontrigger_profit_bound {E : Environment} (hE : OnUnit E) {T K h : ℕ}
    {U : InitUniforms} (hgood : InitProbeGood T K (P E) U) (hp : 2 ^ h ≤ K)
    (hnt : ¬ mhrTriggers T K (P E) U h) {e : ℕ × ℕ} (he : e ∈ actList K) :
    mu E (gpt K e) < (5 / 3) * scale h := by
  have hh := Nat.lt_two_pow_self.trans_le hp
  have hK : 0 < K := (Nat.zero_le h).trans_lt hh
  have herr := abs_le.mp (mhrEst_error E hE T K h hK hh U hgood e.1 e.2
    (mem_actList_iff.mp he).1 (mem_actList_iff.mp he).2)
  have hlt : mhrEst T K (P E) U h e < 3 * scale h / 2 :=
    lt_of_not_ge (fun h => hnt ⟨hp, e, he, h⟩)
  linarith only [herr.1, hlt]

private theorem mhrScale_no_trigger_bound {E : Environment} (hE : OnUnit E) {T K : ℕ}
    (hK : 0 < K) {U : InitUniforms} (hgood : InitProbeGood T K (P E) U)
    (hn : mhrScale T K (P E) U = none) :
    muStar E < 6 / (K : ℝ) := by
  let h := Nat.log 2 K
  have hp : 2 ^ h ≤ K := Nat.pow_log_le_self 2 hK.ne'
  have hlt : h < K := Nat.lt_two_pow_self.trans_le hp
  have hnt := mhrScale_none_spec hn hlt.le
  obtain ⟨e, he, _, hap⟩ := exists_regular_grid_best K hK E hE
  have hle := nontrigger_profit_bound hE hgood hp hnt he
  have hpow : (K : ℝ) < 2 * (2 : ℝ) ^ h := by
    have hn := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) K
    rw [Nat.succ_eq_add_one, pow_succ, mul_comm] at hn
    exact_mod_cast hn
  have hδ : scale h < 2 / (K : ℝ) := by
    rw [scale_eq_inv_pow]
    apply (lt_div_iff₀ (Nat.cast_pos.mpr hK)).2
    simpa only [div_eq_mul_inv, mul_comm] using (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) ^ h)).2 hpow
  have hk : 0 < (K : ℝ)⁻¹ := by positivity
  simp only [div_eq_mul_inv] at hδ hap ⊢
  linarith only [hle, hδ, hap, hk]

private theorem mhrScale_trigger_bounds {E : Environment} (hE : OnUnit E) {T K h : ℕ}
    {U : InitUniforms} (hgood : InitProbeGood T K (P E) U)
    (hs : mhrScale T K (P E) U = some h) {best : ℕ × ℕ} (hb : best ∈ actList K)
    (hmax : ∀ e ∈ actList K, mu E (gpt K e) ≤ mu E (gpt K best))
    (hap : muStar E - 2 / (K : ℝ) ≤ mu E (gpt K best)) :
    h < K ∧ scale h ≤ muStar E ∧ muStar E < 6 * scale h ∧
      (23 / 17) * scale h ≤ mu E (gpt K best) := by
  obtain ⟨⟨hp, e, he, htrigger⟩, hprev⟩ := mhrScale_some_spec hs
  have hh := Nat.lt_two_pow_self.trans_le hp
  have hK : 0 < K := (Nat.zero_le h).trans_lt hh
  have hidx := mem_actList_iff.mp he
  have hmargin := (abs_le.mp (mhrEst_error E hE T K h hK hh U hgood
    e.1 e.2 hidx.1 hidx.2)).2
  have hsk : (23 / 17) * scale h ≤ mu E (gpt K best) := by
    linarith only [hmargin, htrigger, hmax e he]
  have hδ := scale_pos h
  have hbest := mu_le_muStar E hE (triT_subset_unitSq (gpt_mem_tri hK hb))
  refine ⟨hh, by linarith only [hδ, hsk, hbest], ?_, hsk⟩
  cases h with
  | zero =>
    have hμ := (onUnit_facts E hE).2.2.2.1.2
    simp only [scale, pow_zero]
    linarith only [hμ]
  | succ j =>
    have hp' : 2 ^ j ≤ K := (Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ j)).trans hp
    have hn := nontrigger_profit_bound hE hgood hp' (hprev j (Nat.lt_succ_self j)) hb
    have hinv := scale_ge_grid_inv hp
    have hscale := scale_succ j
    simp only [div_eq_mul_inv, one_mul] at hinv hap
    linarith only [hδ, hinv, hn, hscale, hap]

end BilateralProfitRegular
end BundlePart012


section BundlePart013


namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

private theorem ceil_rounds_bound {T : ℕ} (hT : 2 ≤ T) (h : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (↑⌈a * Real.log (2 * (T : ℝ)) / scale h⌉₊ : ℝ) ≤
      (a + 1) * Real.log (2 * (T : ℝ)) * (2 : ℝ) ^ h := by
  have hL := init_log_ge_one hT
  have hL0 : 0 ≤ Real.log (2 * (T : ℝ)) := by linarith
  have hp : (1 : ℝ) ≤ (2 : ℝ)^h := one_le_pow₀ (by norm_num)
  have hc := (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg ha hL0) (scale_pos h).le)).le
  rw [scale_eq_inv_pow, div_inv_eq_mul] at hc ⊢
  have hm := mul_le_mul hL hp (by norm_num : (0 : ℝ) ≤ 1) hL0
  nlinarith only [hc, hm]

private theorem sum_pow_two (n : ℕ) :
    (∑ h ∈ Finset.range n, (2 : ℝ)^h) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

private theorem testedScales_subset {T K h : ℕ} {prob : ℝ × ℝ → ℝ} {U : InitUniforms}
    (hs : mhrScale T K prob U = some h) :
    (testedScales T K prob U).toFinset ⊆ Finset.range (h + 1) := by
  intro j hj
  have hj' := List.mem_toFinset.mp hj
  unfold testedScales at hj'
  have hj'' := of_decide_eq_true (List.mem_filter.mp hj').2
  have hjh : j ≤ h := hj''.2 h (by simp [hs])
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hjh)

private theorem mhr_rounds_sum_bound {T K h : ℕ} (hT : 2 ≤ T) {prob : ℝ × ℝ → ℝ}
    {U : InitUniforms} (hs : mhrScale T K prob U = some h) :
    (∑ j ∈ (testedScales T K prob U).toFinset, (mhrRounds T j : ℝ)) ≤
      131074 * Real.log (2 * (T : ℝ)) * (2 : ℝ)^h := by
  have hR (j : ℕ) : (mhrRounds T j : ℝ) ≤ 65537 * Real.log (2 * (T : ℝ)) * (2 : ℝ)^j := by
    have he := ceil_rounds_bound hT j (a := (2 : ℝ)^16) (by positivity)
    simpa only [mhrRounds, show (2 : ℝ)^16 + 1 = 65537 by norm_num] using he
  calc
    _ ≤ ∑ j ∈ Finset.range (h + 1), (mhrRounds T j : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (testedScales_subset hs) (fun _ _ _ => by positivity)
    _ ≤ ∑ j ∈ Finset.range (h + 1), 65537 * Real.log (2 * (T : ℝ)) * (2 : ℝ)^j :=
      Finset.sum_le_sum (fun j _ => hR j)
    _ = 65537 * Real.log (2 * (T : ℝ)) * (2 ^ (h + 1) - 1) := by
      rw [← Finset.mul_sum, sum_pow_two]
    _ ≤ _ := by
      rw [pow_succ]
      have hL := init_log_ge_one hT
      nlinarith only [hL]

private theorem initRegret_trigger_bound (E : Environment) (hE : OnUnit E) {T h : ℕ} {η : ℝ}
    (hK : 2 ≤ gridK η) (hKT : gridK η ≤ T) {U : InitUniforms}
    (hs : mhrScale T (gridK η) (P E) U = some h)
    (hlarge : (2 : ℝ)^16 / (gridK η : ℝ) ≤ scale h)
    (hStar : muStar E ≤ 6 * scale h) :
    initRegret E T η U ≤ (2 : ℝ)^48 * (gridK η : ℝ) * Real.log (T : ℝ)^2 := by
  let K := gridK η
  let L := Real.log (2 * (T : ℝ))
  let gaps := ∑ e ∈ sampleSet K, (muStar E - mu E (gpt K e))
  let rounds1 := ∑ j ∈ (testedScales T K (P E) U).toFinset, (mhrRounds T j : ℝ)
  let rounds2 := (step2Rounds T (scale h) : ℝ)
  have hT : 2 ≤ T := hK.trans hKT
  have hL := init_log_ge_one hT
  have hδ := scale_pos h
  have hKpos : 0 < K := by omega
  have hK' : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hrounds1 := mhr_rounds_sum_bound hT hs
  have hrounds2 : rounds2 ≤ 274877906945 * L * (2 : ℝ)^h := by
    have he := ceil_rounds_bound hT h (a := (2 : ℝ)^38) (by positivity)
    simpa only [rounds2, step2Rounds, L, show (2 : ℝ)^38 + 1 = 274877906945 by norm_num] using he
  have htotal : rounds1 + rounds2 ≤ (2 : ℝ)^39 * L * (2 : ℝ)^h := by
    change rounds1 ≤ 131074 * L * (2 : ℝ)^h at hrounds1
    have hL' : 0 ≤ L := by exact (show 1 ≤ L from hL).trans' (by norm_num)
    have hm := mul_nonneg hL' (show 0 ≤ (2 : ℝ)^h by positivity)
    linarith only [hrounds1, hrounds2, hm]
  have hgap (e : ℕ × ℕ) (he : e ∈ sampleSet K) :
      0 ≤ muStar E - mu E (gpt K e) ∧ muStar E - mu E (gpt K e) ≤ muStar E := by
    obtain ⟨hle, hmax⟩ := sampleSet_bounds he
    have he' : e ∈ actList K := mem_actList_iff.mpr ⟨hle, hmax⟩
    exact ⟨sub_nonneg.mpr (mu_le_muStar E hE (triT_subset_unitSq (gpt_mem_tri hKpos he'))),
      sub_le_self _ (gpt_profit_nonneg hKpos hle hmax E hE)⟩
  have hgaps : 0 ≤ gaps := Finset.sum_nonneg (fun e he => (hgap e he).1)
  have hScard := sampleSet_real_card_le hK hKT
  have hgapUpper : gaps ≤ 36 * K * L * scale h := by
    calc
      _ ≤ ∑ _e ∈ sampleSet K, muStar E := Finset.sum_le_sum (fun e he => (hgap e he).2)
      _ = ((sampleSet K).card : ℝ) * muStar E := by simp
      _ ≤ (6 * K * L) * (6 * scale h) := by
        exact mul_le_mul hScard hStar ((onUnit_facts E hE).2.2.2.1.1.le) (by
          have : 0 ≤ L := zero_le_one.trans hL
          positivity)
      _ = _ := by ring
  have hinit : initRegret E T η U = (rounds1 + rounds2) * gaps := by
    unfold initRegret
    dsimp only
    simp only [hs, if_neg (not_lt_of_ge hlarge), add_mul]
    change (∑ j ∈ (testedScales T K (P E) U).toFinset, (mhrRounds T j : ℝ) * gaps) +
      rounds2 * gaps = rounds1 * gaps + rounds2 * gaps
    rw [Finset.sum_mul]
  have hrealT : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hposT : (0 : ℝ) < T := by linarith
  have hlogT : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by linarith)
  have hlog2 : L ≤ 2 * Real.log (T : ℝ) := by
    dsimp [L]
    rw [Real.log_mul (by norm_num) hposT.ne']
    linarith only [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hrealT]
  have hnorm : (2 : ℝ) ^ h * scale h = 1 := by
    rw [scale_eq_inv_pow, mul_inv_cancel₀ (by positivity)]
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  calc
    _ = (rounds1 + rounds2) * gaps := hinit
    _ ≤ ((2 : ℝ)^39 * L * (2 : ℝ)^h) * (36 * K * L * scale h) := by
      exact mul_le_mul htotal hgapUpper hgaps (by positivity)
    _ = (36 * (2 : ℝ)^39) * K * L ^ 2 := by
      calc
        _ = (36 * (2 : ℝ)^39) * K * L ^ 2 * ((2 : ℝ)^h * scale h) := by ring
        _ = _ := by rw [hnorm, mul_one]
    _ ≤ (36 * (2 : ℝ)^39) * K * (2 * Real.log (T : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by
      change _ ≤ (2 : ℝ)^48 * (K : ℝ) * Real.log (T : ℝ)^2
      have hm := mul_nonneg hK'.le (sq_nonneg (Real.log (T : ℝ)))
      norm_num
      nlinarith only [hm]

end BilateralProfitRegular
end BundlePart013


section BundlePart014


namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade

section

variable {E : Environment} {T K : ℕ} {δ : ℝ}
  {U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval}

local notation "ph" => phat T K δ (P E) U
local notation "mh" => muhat T K δ (P E) U
local notation "mhS" => muhatStar T K δ (P E) U
local notation "ret" => InitRetained E T K δ U

private theorem InitCandidatesData.cross_mem (D : InitCandidatesData E T K δ U)
    {e w : ℕ × ℕ} (hw : ret w) (hc : (gpt K e).1 ≤ (gpt K w).2) :
    (e.1, w.2) ∈ actList K := by
  have hK : 0 < (K : ℝ) := Nat.cast_pos.mpr D.K_pos
  refine mem_actList_iff.mpr ⟨?_, (mem_actList_iff.mp hw.1).2⟩
  exact Nat.cast_le.mp ((div_le_div_iff_of_pos_right hK).mp hc)

private theorem InitCandidatesData.empirical_balance_error (D : InitCandidatesData E T K δ U)
    {e w : ℕ × ℕ} (he : ret e) (hw : ret w)
    (h₁ : (e.1, w.2) ∈ actList K) (h₂ : (w.1, e.2) ∈ actList K)
    (hp₁ : δ ≤ P E (gpt K (e.1, w.2))) (hp₂ : δ ≤ P E (gpt K (w.1, e.2))) :
    |1 / 2 * Real.log (ph (e.1, w.2) / ph (w.1, e.2)) -
      Real.log (balance E (gpt K e) / balance E (gpt K w))| ≤ 1 / 1000 := by
  obtain ⟨hph₁, hl₁⟩ := D.log_error h₁ hp₁
  obtain ⟨hph₂, hl₂⟩ := D.log_error h₂ hp₂
  have hprob₁ := D.δ_pos.trans_le hp₁
  have hprob₂ := D.δ_pos.trans_le hp₂
  have heq := eq_47 E D.regular (gpt K e) (gpt K w)
    (D.retained_interior he) (D.retained_interior hw)
  change Real.log (balance E (gpt K e) / balance E (gpt K w)) =
    1 / 2 * Real.log (P E (gpt K (e.1,w.2)) / P E (gpt K (w.1,e.2))) at heq
  rw [heq, Real.log_div hph₁.ne' hph₂.ne', Real.log_div hprob₁.ne' hprob₂.ne']
  obtain ⟨hl₁, hu₁⟩ := abs_le.mp hl₁
  obtain ⟨hl₂, hu₂⟩ := abs_le.mp hl₂
  exact abs_le.mpr ⟨by linarith only [hl₁, hu₂], by linarith only [hu₁, hl₂]⟩

private theorem InitCandidatesData.pass_implies_close (D : InitCandidatesData E T K δ U)
    {e w : ℕ × ℕ} (he : ret e) (hw : ret w) (h : passes T K δ (P E) U e w) :
    |Real.log (balance E (gpt K e) / balance E (gpt K w))| ≤ 11 / 1000 := by
  obtain ⟨hc₁, hc₂, hh₁, hh₂, hlog⟩ := h
  have hc₁' : (e.1,w.2) ∈ actList K := mem_actList_iff.mpr ⟨hc₁, (mem_actList_iff.mp hw.1).2⟩
  have hc₂' : (w.1,e.2) ∈ actList K := mem_actList_iff.mpr ⟨hc₂, (mem_actList_iff.mp he.1).2⟩
  have hhigh {c : ℕ × ℕ} (hc : c ∈ actList K) (hh : 99 / 100 * mhS ≤ mh c) :
      δ ≤ P E (gpt K c) := by
    apply le_trans _ (D.mu_le_P hc)
    have herror := (abs_le.mp (D.mu_error hc)).2
    have hmhS := D.muhatStar_bounds.1
    linarith only [D.δ_pos, D.best_scale, herror, hmhS, hh]
  have hh := D.empirical_balance_error he hw hc₁' hc₂' (hhigh hc₁' hh₁) (hhigh hc₂' hh₂)
  obtain ⟨hl, hu⟩ := abs_le.mp hh
  obtain ⟨hla, hua⟩ := abs_le.mp hlog
  exact abs_le.mpr ⟨by linarith only [hla, hu], by linarith only [hua, hl]⟩

private theorem InitCandidatesData.close_implies_pass (D : InitCandidatesData E T K δ U)
    {e w : ℕ × ℕ} (he : ret e) (hw : ret w)
    (hclose : |Real.log (balance E (gpt K e) / balance E (gpt K w))| ≤ 1 / 200) :
    passes T K δ (P E) U e w := by
  have heI := D.retained_interior he
  have hwI := D.retained_interior hw
  let lam := balance E (gpt K w)
  have hlam : 0 < lam := balance_pos E D.regular.1 hwI
  have hwr : auxProfit E lam (gpt K w) = mu E (gpt K w) :=
    (auxProfit_values E D.regular.1 hlam hwI).2.2.2.2
  have habs : |Real.log (lam / balance E (gpt K e))| ≤ 1 / 200 := by
    rw [← inv_div, Real.log_inv, abs_neg]
    exact hclose
  have hsq : Real.log (lam / balance E (gpt K e)) ^ 2 ≤ (1 / 200 : ℝ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hM := (onUnit_facts E D.regular.1).2.2.2.1.1
  have hmu := mu_le_muStar E D.regular.1 (intT_subset_unitSq heI)
  have hmupos := ((onUnit_facts E D.regular.1).2.2.1 _ (intT_subset_unitSq heI)).mpr heI
  have hgap := (auxProfit_values E D.regular.1 hlam heI).2.1
  have hgap' := hgap.trans <| (mul_le_mul_of_nonneg_left hsq hmupos.le).trans
    (mul_le_mul_of_nonneg_right hmu (sq_nonneg (1 / 200 : ℝ)))
  have her : (1 - 13 / 40000 : ℝ) * muStar E ≤ auxProfit E lam (gpt K e) := by
    linarith only [D.retained_high he, hgap']
  have hwr' : (1 - 3 / 10000 : ℝ) * muStar E ≤ auxProfit E lam (gpt K w) :=
    hwr.symm ▸ D.retained_high hw
  obtain ⟨ht₁, ht₂, hc₁, hc₂, _⟩ := lemma_6_3 E D.regular lam hlam (gpt K e) (gpt K w)
    heI hwI (by linarith only [her, hM]) (by linarith only [hwr', hM])
  have h₁ := D.cross_mem hw ht₁.2.1
  have h₂ := D.cross_mem he ht₂.2.1
  have htrue {c : ℕ × ℕ} (hc : muStar E - mu E (gpt K c) ≤
      4 * (muStar E - auxProfit E lam (gpt K e) + (muStar E - auxProfit E lam (gpt K w)))) :
      (1 - 1 / 400 : ℝ) * muStar E ≤ mu E (gpt K c) := by
    linarith only [hc, her, hwr']
  have hp₁ : (1 - 1 / 400 : ℝ) * muStar E ≤ mu E (gpt K (e.1, w.2)) := htrue hc₁
  have hp₂ : (1 - 1 / 400 : ℝ) * muStar E ≤ mu E (gpt K (w.1, e.2)) := htrue hc₂
  have hh {c : ℕ × ℕ} (hc : c ∈ actList K)
      (hg : (1 - 1 / 400 : ℝ) * muStar E ≤ mu E (gpt K c)) :
      δ ≤ P E (gpt K c) ∧ 99 / 100 * mhS ≤ mh c := by
    have hμ := D.mu_le_P hc
    have hErr := (abs_le.mp (D.mu_error hc)).1
    have hStar := D.muhatStar_bounds.2
    exact ⟨by linarith only [hg, hμ, D.best_le_opt, D.best_scale, D.δ_pos],
      by linarith only [hg, hErr, hStar, D.best_le_opt, hM]⟩
  obtain ⟨hpr₁, hmh₁⟩ := hh h₁ hp₁
  obtain ⟨hpr₂, hmh₂⟩ := hh h₂ hp₂
  refine ⟨(mem_actList_iff.mp h₁).1, (mem_actList_iff.mp h₂).1, hmh₁, hmh₂, ?_⟩
  have hErr := D.empirical_balance_error he hw h₁ h₂ hpr₁ hpr₂
  obtain ⟨hl, hu⟩ := abs_le.mp hErr
  obtain ⟨htl, htu⟩ := abs_le.mp hclose
  exact abs_le.mpr ⟨by linarith only [hl, htl], by linarith only [hu, htu]⟩

/-- Log-balances of retained grid prices lie in the interval of width `log K`. -/
private theorem InitCandidatesData.root_log_bound (D : InitCandidatesData E T K δ U)
    {e : ℕ × ℕ} (he : ret e) :
    |Real.log (balance E (gpt K e))| ≤ 1 / 2 * Real.log (K : ℝ) := by
  let x := gpt K e
  have hx : x ∈ intT := D.retained_interior he
  have hK : 0 < (K : ℝ) := Nat.cast_pos.mpr D.K_pos
  have haux := D.δ_large.trans D.δ_le_opt
  have htmp : (2 : ℝ)^16 / (K : ℝ) = 65536 * (1 / (K : ℝ)) := by ring
  rw [htmp] at haux
  have honeK : 0 < 1 / (K : ℝ) := one_div_pos.mpr hK
  have hm : 1 / (K : ℝ) ≤ mu E x := by
    dsimp [x]
    linarith only [D.retained_high he, haux, honeK]
  have hprob := hm.trans (D.mu_le_P he.1)
  obtain ⟨hs, hb⟩ := intT_cdf_pos E D.regular.1 hx
  have hStrict : 0 < balance E x := balance_pos E D.regular.1 hx
  have hs_le : E.cdfS x.1 ≤ 1 := by
    have hh := (BilateralProfitMHR.positive_density_profit_facts E D.regular.1).2.2.2.2.1
      (intT_subset_unitSq hx).1 (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (intT_subset_unitSq hx).1.2
    have heq : E.cdfS 1 = 1 := by
      simpa only [Environment.cdfS, D.regular.1.2.1] using E.fS_integral
    rwa [heq] at hh
  have hb_le : 1 - E.cdfB x.2 ≤ 1 := by
    have hh := (BilateralProfitMHR.positive_density_profit_facts E D.regular.1).2.2.2.2.2.1
      (show (0 : ℝ) ∈ Icc 0 1 by norm_num) (intT_subset_unitSq hx).2 (intT_subset_unitSq hx).2.1
    have heq : E.cdfB 0 = 0 := by simp [Environment.cdfB, D.regular.1.2.2.1]
    rw [heq] at hh
    linarith only [hh]
  change 1 / (K : ℝ) ≤ P E x at hprob
  rw [P_factor E D.regular.1 (intT_subset_unitSq hx)] at hprob
  have hsl := hprob.trans (mul_le_of_le_one_right hs.le hb_le)
  have hbl := hprob.trans (mul_le_of_le_one_left hb.le hs_le)
  have hlo : 1 / (K : ℝ) ≤ E.cdfS x.1 / (1 - E.cdfB x.2) := by
    apply (le_div_iff₀ hb).mpr
    exact (mul_le_of_le_one_right honeK.le hb_le).trans hsl
  have hhi : E.cdfS x.1 / (1 - E.cdfB x.2) ≤ K := by
    apply (div_le_iff₀ hb).mpr
    have hh := mul_le_mul_of_nonneg_left hbl hK.le
    rw [mul_one_div, div_self hK.ne'] at hh
    exact hs_le.trans hh
  have hlogl := Real.log_le_log honeK hlo
  have hlogu := Real.log_le_log (div_pos hs hb) hhi
  rw [← balance_sq E D.regular.1 hx, Real.log_pow] at hlogl hlogu
  rw [one_div, Real.log_inv] at hlogl
  norm_num at hlogl hlogu
  change |Real.log (balance E x)| ≤ 1 / 2 * Real.log (K : ℝ)
  exact abs_le.mpr ⟨by linarith only [hlogl], by linarith only [hlogu]⟩

end

end BilateralProfitRegular
end BundlePart014


section BundlePart015


namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade

private abbrev InitIndex := ℕ × ℕ
private abbrev InitGroup := InitIndex × List InitIndex

section

variable {E : Environment} {T K : ℕ} {δ : ℝ}
  {U : Option ℕ × InitIndex × ℕ → unitInterval}

local notation "ret" => InitRetained E T K δ U
local notation "passGroup" => passes T K δ (P E) U
local notation "addGroup" => addToGroups T K δ (P E) U
local notation "logBal" => (fun e => Real.log (balance E (gpt K e)))

/-- Every group contains its root and retains exactly eligible members. New roots are
separated in log balance even when the process chooses the earliest compatible root. -/
private structure InitGroupsCertified (gs : List InitGroup) : Prop where
  root_mem : ∀ g ∈ gs, g.1 ∈ g.2
  members : ∀ g ∈ gs, ∀ x ∈ g.2, ret x ∧ (x = g.1 ∨ passGroup x g.1)
  separated : gs.Pairwise (fun g h => 1 / 200 < |logBal h.1 - logBal g.1|)

private theorem root_origin (x : InitIndex) (gs : List InitGroup) :
    ∀ g ∈ addGroup x gs, g.1 = x ∨ ∃ h ∈ gs, g.1 = h.1 := by
  induction gs with
  | nil => simp [addToGroups]
  | cons h hs ih =>
    by_cases hp : passGroup x h.1
    · intro g hg
      simp only [addToGroups, if_pos hp, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact Or.inr ⟨h, by simp, rfl⟩
      · exact Or.inr ⟨g, by simp [hg], rfl⟩
    · intro g hg
      simp only [addToGroups, if_neg hp, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact Or.inr ⟨g, by simp, rfl⟩
      · exact (ih g hg).imp_right (fun ⟨r, hr, he⟩ => ⟨r, by simp [hr], he⟩)

private theorem add_mem_iff (x y : InitIndex) (gs : List InitGroup) :
    y ∈ (addGroup x gs).flatMap Prod.snd ↔ y = x ∨ y ∈ gs.flatMap Prod.snd := by
  induction gs with
  | nil => simp [addToGroups]
  | cons g l ih =>
    by_cases h : passGroup x g.1
    · simp only [addToGroups, if_pos h, List.flatMap_cons, List.append_assoc, List.mem_append,
        List.mem_singleton]
      tauto
    · simp only [addToGroups, if_neg h, List.flatMap_cons, List.mem_append, ih]
      tauto

private theorem add_certified (D : InitCandidatesData E T K δ U)
    (x : InitIndex) (hx : ret x) (gs : List InitGroup)
    (hgs : InitGroupsCertified (E := E) (T := T) (K := K) (δ := δ) (U := U) gs) :
    InitGroupsCertified (E := E) (T := T) (K := K) (δ := δ) (U := U) (addGroup x gs) := by
  induction gs with
  | nil =>
    simp only [addToGroups]
    refine ⟨?_, ?_, by simp⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst g
      simp
    · intro g hg e he
      simp only [List.mem_singleton] at hg
      subst g
      simp only [List.mem_singleton] at he
      subst e
      exact ⟨hx, Or.inl rfl⟩
  | cons g l ih =>
    obtain ⟨hroot, hmembers, hsep⟩ := hgs
    have ht : InitGroupsCertified (E := E) (T := T) (K := K) (δ := δ) (U := U) l :=
      ⟨fun h hh => hroot h (by simp [hh]), fun h hh => hmembers h (by simp [hh]),
        (List.pairwise_cons.mp hsep).2⟩
    by_cases hp : passGroup x g.1
    · rw [addToGroups, if_pos hp]
      refine ⟨?_, ?_, ?_⟩
      · intro h hh
        rcases List.mem_cons.mp hh with rfl | hh'
        · exact List.mem_append_left _ (hroot _ (by simp))
        · exact ht.root_mem h hh'
      · intro h hh e he
        rcases List.mem_cons.mp hh with rfl | hh'
        · rcases List.mem_append.mp he with he' | he'
          · exact hmembers g (by simp) e he'
          · have : e = x := List.mem_singleton.mp he'
            subst e
            exact ⟨hx, Or.inr hp⟩
        · exact ht.members h hh' e he
      · exact List.pairwise_cons.mpr ⟨(List.pairwise_cons.mp hsep).1, ht.separated⟩
    · rw [addToGroups, if_neg hp]
      have htail := ih ht
      refine ⟨?_, ?_, ?_⟩
      · intro h hh
        rcases List.mem_cons.mp hh with rfl | hh'
        · exact hroot h (by simp)
        · exact htail.root_mem h hh'
      · intro h hh e he
        rcases List.mem_cons.mp hh with rfl | hh'
        · exact hmembers h (by simp) e he
        · exact htail.members h hh' e he
      · apply List.pairwise_cons.mpr
        refine ⟨?_, htail.separated⟩
        intro h hh
        rcases root_origin (E := E) (T := T) (K := K) (δ := δ) (U := U) x l h hh with he | ⟨k, hk, he⟩
        · rw [he]
          apply lt_of_not_ge
          intro hc
          have hg := (hmembers g (by simp) g.1 (hroot g (by simp))).1
          have hposx := balance_pos E D.regular.1 (D.retained_interior hx)
          have hposg := balance_pos E D.regular.1 (D.retained_interior hg)
          apply hp (D.close_implies_pass hx hg _)
          rw [Real.log_div hposx.ne' hposg.ne']
          exact hc
        · rw [he]
          exact (List.pairwise_cons.mp hsep).1 k hk

private theorem fold_certified (D : InitCandidatesData E T K δ U)
    (xs : List InitIndex) (hxs : ∀ x ∈ xs, ret x) (gs : List InitGroup)
    (hgs : InitGroupsCertified (E := E) (T := T) (K := K) (δ := δ) (U := U) gs) :
    InitGroupsCertified (E := E) (T := T) (K := K) (δ := δ) (U := U)
      (xs.foldl (fun s x => addGroup x s) gs) := by
  induction xs generalizing gs with
  | nil => exact hgs
  | cons x xs ih =>
    exact ih (fun y hy => hxs y (by simp [hy])) _
      (add_certified D x (hxs x (by simp)) gs hgs)

private theorem fold_members (xs : List InitIndex) (y : InitIndex) (gs : List InitGroup) :
    y ∈ (xs.foldl (fun s x => addGroup x s) gs).flatMap Prod.snd ↔
      y ∈ xs ∨ y ∈ gs.flatMap Prod.snd := by
  induction xs generalizing gs with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, add_mem_iff, List.mem_cons]
    tauto

private theorem InitCandidatesData.groups_certified (D : InitCandidatesData E T K δ U)
    {ord : List InitIndex} (hord : IsOrder K ord) :
    InitGroupsCertified (E := E) (T := T) (K := K) (δ := δ) (U := U)
      (groups T K δ ord (P E) U) := by
  unfold groups
  apply fold_certified D
  · intro x hx
    obtain ⟨h₁, h₂⟩ := List.mem_filter.mp hx
    exact ⟨mem_actList_iff.mpr ((hord.2 x).mp h₁), of_decide_eq_true h₂⟩
  · exact ⟨by simp, by simp, by simp⟩

private theorem retained_mem_group {ord : List InitIndex} (hord : IsOrder K ord)
    {e : InitIndex} (he : ret e) : ∃ g ∈ groups T K δ ord (P E) U, e ∈ g.2 := by
  apply List.mem_flatMap.mp
  unfold groups
  rw [fold_members]
  exact Or.inl (List.mem_filter.mpr ⟨(hord.2 e).mpr (mem_actList_iff.mp he.1),
    decide_eq_true he.2⟩)

private theorem InitGroupsCertified.root_retained {gs : List InitGroup}
    (h : InitGroupsCertified (E := E) (T := T) (K := K) (δ := δ) (U := U) gs)
    {g : InitGroup} (hg : g ∈ gs) : ret g.1 :=
  (h.members g hg g.1 (h.root_mem g hg)).1

private theorem InitCandidatesData.group_log_bound (D : InitCandidatesData E T K δ U)
    {gs : List InitGroup}
    (h : InitGroupsCertified (E := E) (T := T) (K := K) (δ := δ) (U := U) gs)
    {g : InitGroup} (hg : g ∈ gs) {x : InitIndex} (hx : x ∈ g.2) :
    |Real.log (balance E (gpt K x) / balance E (gpt K g.1))| ≤ 11 / 1000 := by
  obtain ⟨hr, he | hp⟩ := h.members g hg x hx
  · subst x
    rw [div_self (balance_pos E D.regular.1 (D.retained_interior hr)).ne', Real.log_one, abs_zero]
    norm_num
  · exact D.pass_implies_close hr (h.root_retained hg) hp

end

end BilateralProfitRegular
end BundlePart015


section BundlePart016



namespace BilateralProfitRegular

open Set

private theorem offsetRange_pos : 0 < offsetRange := regular_offset_halfwidth.1

private theorem offsetRange_le : offsetRange ≤ 1 / 40 := regular_offset_halfwidth.2

private theorem numIntervals_pos {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    0 < numIntervals η δ :=
  Nat.ceil_pos.mpr (div_pos (mul_pos (by norm_num) offsetRange_pos)
    (mul_pos (by norm_num) (Real.sqrt_pos.2 (div_pos hη hδ))))

private theorem mesh_step_pos {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    0 < 2 * offsetRange / (numIntervals η δ : ℝ) :=
  div_pos (mul_pos (by norm_num) offsetRange_pos) (Nat.cast_pos.mpr (numIntervals_pos hη hδ))

private theorem mesh_step_upper {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    2 * offsetRange / (numIntervals η δ : ℝ) ≤ 1 / 2 * Real.sqrt (η / δ) := by
  have hp : 0 < 1 / 2 * Real.sqrt (η / δ) :=
    mul_pos (by norm_num) (Real.sqrt_pos.2 (div_pos hη hδ))
  have hm : 0 < (numIntervals η δ : ℝ) := Nat.cast_pos.mpr (numIntervals_pos hη hδ)
  have h : 2 * offsetRange / (1 / 2 * Real.sqrt (η / δ)) ≤ (numIntervals η δ : ℝ) :=
    Nat.le_ceil _
  have hh := (div_le_iff₀ hp).mp h
  exact (div_le_iff₀ hm).mpr (by simpa only [mul_comm (numIntervals η δ : ℝ)] using hh)

private theorem offsets_eq_map (η δ : ℝ) :
    offsets η δ = (List.range (numIntervals η δ + 1)).map fun k : ℕ =>
      -offsetRange + (k : ℝ) * (2 * offsetRange / numIntervals η δ) := by
  unfold offsets
  change (((List.range (numIntervals η δ + 1)).flatMap fun k : ℕ => [(k : ℝ)]).map fun k =>
    -offsetRange + k * (2 * offsetRange / numIntervals η δ)) = _
  rw [← List.map_eq_flatMap, List.map_map]
  rfl

private theorem offset_abs_le {η δ θ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hθ : θ ∈ offsets η δ) : |θ| ≤ offsetRange := by
  rw [offsets_eq_map] at hθ
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hθ
  have hk' : k ≤ numIntervals η δ := Nat.lt_succ_iff.mp (List.mem_range.mp hk)
  have hm : 0 < (numIntervals η δ : ℝ) := Nat.cast_pos.mpr (numIntervals_pos hη hδ)
  have he : (numIntervals η δ : ℝ) * (2 * offsetRange / numIntervals η δ) =
      2 * offsetRange := by
    rw [mul_comm, div_mul_cancel₀ _ hm.ne']
  have hu := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk')
    (mesh_step_pos hη hδ).le
  have hl := mul_nonneg (Nat.cast_nonneg k) (mesh_step_pos hη hδ).le
  rw [he] at hu
  exact abs_le.mpr ⟨by linarith only [hl], by linarith only [hu]⟩

private theorem exists_close_offset {η δ t : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (ht : |t| ≤ offsetRange) :
    ∃ θ ∈ offsets η δ, |θ - t| ≤ 1 / 4 * Real.sqrt (η / δ) := by
  let m := numIntervals η δ
  let s := 2 * offsetRange / (m : ℝ)
  have hs : 0 < s := mesh_step_pos hη hδ
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr (numIntervals_pos hη hδ)
  have hsm : s * (m : ℝ) = 2 * offsetRange := div_mul_cancel₀ _ hm.ne'
  let a := (t + offsetRange) / s
  have ha : 0 ≤ a := div_nonneg (by linarith only [(abs_le.mp ht).1]) hs.le
  have ha' : a ≤ (m : ℝ) := (div_le_iff₀ hs).mpr (by linarith only [hsm, (abs_le.mp ht).2])
  have has : a * s = t + offsetRange := div_mul_cancel₀ _ hs.ne'
  let k := ⌊a + 1 / 2⌋₊
  have hk : k < m + 1 := by
    apply (Nat.floor_lt (by linarith only [ha] : 0 ≤ a + 1 / 2)).mpr
    push_cast
    linarith only [ha']
  have hlo := Nat.lt_floor_add_one (a + 1 / 2)
  have hhi := Nat.floor_le (by linarith only [ha] : 0 ≤ a + 1 / 2)
  have habs : |(k : ℝ) - a| ≤ 1 / 2 := by
    exact abs_le.mpr ⟨by change -(1 / 2) ≤ (k : ℝ) - a; linarith only [hlo],
      by change (k : ℝ) - a ≤ 1 / 2; linarith only [hhi]⟩
  refine ⟨-offsetRange + (k : ℝ) * s, by rw [offsets_eq_map]; exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩, ?_⟩
  rw [show -offsetRange + (k : ℝ) * s - t = ((k : ℝ) - a) * s by nlinarith only [has],
    abs_mul, abs_of_nonneg hs.le]
  have hh := mul_le_mul_of_nonneg_right habs hs.le
  have hstep := mesh_step_upper hη hδ
  change s ≤ 1 / 2 * Real.sqrt (η / δ) at hstep
  linarith only [hh, hstep]

private theorem offsets_count {η δ : ℝ} (hη : 0 < η) (hηδ : η ≤ δ) :
    ((offsets η δ).length : ℝ) ≤ 3 * Real.sqrt (δ / η) := by
  have hδ := hη.trans_le hηδ
  let s := Real.sqrt (η / δ)
  let t := Real.sqrt (δ / η)
  have hs : 0 < s := Real.sqrt_pos.2 (div_pos hη hδ)
  have ht : 1 ≤ t := (Real.le_sqrt (by norm_num) (div_nonneg hδ.le hη.le)).mpr (by
    rw [one_pow]
    exact (le_div_iff₀ hη).mpr (by simpa using hηδ))
  have he : s⁻¹ = t := by
    unfold s t
    rw [← Real.sqrt_inv, inv_div]
  have hq : 2 * offsetRange / (1 / 2 * s) = 4 * offsetRange * t := by
    rw [← he]
    field_simp
    ring
  have hp : 0 ≤ 2 * offsetRange / (1 / 2 * s) := div_nonneg (mul_nonneg (by norm_num) offsetRange_pos.le)
    (mul_nonneg (by norm_num) hs.le)
  have hn := Nat.ceil_lt_add_one hp
  change (numIntervals η δ : ℝ) < 2 * offsetRange / (1 / 2 * s) + 1 at hn
  rw [hq] at hn
  have hb := mul_le_mul_of_nonneg_right offsetRange_le (show 0 ≤ t by linarith only [ht])
  simp only [offsets_eq_map, List.length_map, List.length_range, Nat.cast_add, Nat.cast_one]
  change (numIntervals η δ : ℝ) + 1 ≤ 3 * t
  linarith only [hn, hb, ht]

end BilateralProfitRegular
end BundlePart016


section BundlePart017



namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade

/-- The candidate associated with one group and one offset in Algorithm 7. -/
private noncomputable def initGroupCandidate (E : Environment) (T K : ℕ) (δ : ℝ)
    (U : Option ℕ × InitIndex × ℕ → unitInterval) (g : InitGroup) (θ : ℝ) : Candidate :=
  { region := convexHull ℝ {y | ∃ e ∈ g.2, y = gpt K e}
    root := gpt K g.1
    offset := θ
    est := phat T K δ (P E) U g.1 }

private theorem mem_initCandidates_iff (E : Environment) (T : ℕ) (η δ : ℝ) (ord : List InitIndex)
    (U : Option ℕ × InitIndex × ℕ → unitInterval) (c : Candidate) :
    c ∈ candidates T η δ ord (P E) U ↔
      ∃ g ∈ groups T (gridK η) δ ord (P E) U, ∃ θ ∈ offsets η δ,
        c = initGroupCandidate E T (gridK η) δ U g θ := by
  unfold candidates
  rw [List.mem_flatMap]
  simp only [List.mem_map, initGroupCandidate, eq_comm]

private theorem initGroupCandidate_mem {E : Environment} {T K : ℕ} {δ : ℝ}
    {U : Option ℕ × InitIndex × ℕ → unitInterval} {g : InitGroup} {θ : ℝ} {e : InitIndex}
    (he : e ∈ g.2) : gpt K e ∈ (initGroupCandidate E T K δ U g θ).region :=
  subset_convexHull ℝ _ ⟨e, he, rfl⟩

private theorem initGroupCandidate_compact (E : Environment) (T K : ℕ) (δ : ℝ)
    (U : Option ℕ × InitIndex × ℕ → unitInterval) (g : InitGroup) (θ : ℝ) :
    IsCompact (initGroupCandidate E T K δ U g θ).region := by
  apply Set.Finite.isCompact_convexHull
  have he : {y | ∃ e ∈ g.2, y = gpt K e} = gpt K '' {e | e ∈ g.2} := by
    ext x
    simp only [mem_ofPred_eq, mem_image]
    exact exists_congr fun y => and_congr_right fun _ => eq_comm
  rw [he]
  exact (List.finite_toSet g.2).image _

private theorem log_initCandidate_param {E : Environment} {w x : ℝ × ℝ} {θ u : ℝ}
    (hw : 0 < balance E w) (hx : 0 < balance E x) :
    Real.log ((Real.exp θ * balance E w * Real.exp u) / balance E x) =
      θ + u + Real.log (balance E w / balance E x) := by
  have he : Real.exp θ * balance E w * Real.exp u / balance E x =
    (Real.exp θ * Real.exp u) * (balance E w / balance E x) := by ring
  rw [he, Real.log_mul (mul_pos (Real.exp_pos θ) (Real.exp_pos u)).ne' (div_pos hw hx).ne',
    Real.log_mul (Real.exp_pos θ).ne' (Real.exp_pos u).ne', Real.log_exp, Real.log_exp]

section

variable {E : Environment} {T K : ℕ} {δ : ℝ}
  {U : Option ℕ × InitIndex × ℕ → unitInterval}

private theorem InitCandidatesData.hull_high (D : InitCandidatesData E T K δ U)
    {gs : List InitGroup} (hgs : InitGroupsCertified (E := E) (T := T) (K := K) (δ := δ) (U := U) gs)
    {g : InitGroup} (hg : g ∈ gs) {θ : ℝ} :
    ∀ x ∈ (initGroupCandidate E T K δ U g θ).region, x ∈ intT ∧
      (1 - 1 / 2000 : ℝ) * muStar E ≤ auxProfit E (balance E (gpt K g.1)) x := by
  have hw := D.retained_interior (hgs.root_retained hg)
  have hwpos := balance_pos E D.regular.1 hw
  have hM := (onUnit_facts E D.regular.1).2.2.2.1.1
  refine auxProfit_lower_convexHull E D.regular hwpos ?_
    (mul_pos (by norm_num) hM) ?_
  · rintro _ ⟨e, he, rfl⟩
    exact D.retained_interior (hgs.members g hg e he).1
  · rintro _ ⟨e, he, rfl⟩
    have hr := (hgs.members g hg e he).1
    have heI := D.retained_interior hr
    have hb := D.group_log_bound hgs hg he
    have hLog : |Real.log (balance E (gpt K g.1) / balance E (gpt K e))| ≤ 11 / 1000 := by
      rw [← inv_div, Real.log_inv, abs_neg]
      exact hb
    have hSq : Real.log (balance E (gpt K g.1) / balance E (gpt K e))^2 ≤ (11 / 1000 : ℝ)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hLog 2
    have hp := ((onUnit_facts E D.regular.1).2.2.1 _ (intT_subset_unitSq heI)).mpr heI
    have hu := mu_le_muStar E D.regular.1 (intT_subset_unitSq heI)
    have hd := (auxProfit_values E D.regular.1 hwpos heI).2.1
    have ht := hd.trans ((mul_le_mul_of_nonneg_left hSq hp.le).trans
      (mul_le_mul_of_nonneg_right hu (sq_nonneg _)))
    nlinarith only [D.retained_high hr, ht, hM]

private theorem InitCandidatesData.candidate_valid (D : InitCandidatesData E T K δ U)
    {gs : List InitGroup} (hgs : InitGroupsCertified (E := E) (T := T) (K := K) (δ := δ) (U := U) gs)
    {g : InitGroup} (hg : g ∈ gs) {θ : ℝ} (hθ : |θ| ≤ offsetRange) :
    (initGroupCandidate E T K δ U g θ).Valid E δ := by
  let c := initGroupCandidate E T K δ U g θ
  let w := gpt K g.1
  let lam := balance E w
  have hroot : w ∈ c.region := initGroupCandidate_mem (hgs.root_mem g hg)
  have hr := hgs.root_retained hg
  have hw := D.retained_interior hr
  have hlam := balance_pos E D.regular.1 hw
  have hM := (onUnit_facts E D.regular.1).2.2.2.1.1
  have hHull := D.hull_high hgs hg (θ := θ)
  have hμ {x : ℝ × ℝ} (hx : x ∈ c.region) :
      (1 - 1 / 2000 : ℝ) * muStar E ≤ mu E x :=
    (hHull x hx).2.trans ((auxProfit_values E D.regular.1 hlam (hHull x hx).1).2.2.2.1)
  have hd := D.best_scale.trans D.best_le_opt
  have hPw : δ ≤ P E w := by
    have hh := (D.retained_high hr).trans (D.mu_le_P hr.1)
    exact le_trans (by linarith only [hd, D.δ_pos] : δ ≤ (1 - 3 / 10000) * muStar E) hh
  have hRel := D.relative_error hr.1 hPw
  have hPw' : (1 - 3 / 10000 : ℝ) * muStar E ≤ P E w :=
    (D.retained_high hr).trans (D.mu_le_P hr.1)
  have hEst : δ ≤ c.est := by
    change δ ≤ phat T K δ (P E) U g.1
    linarith only [hRel.1, hd, hPw', D.δ_pos]
  have hcross {x z : ℝ × ℝ} (hx : x ∈ c.region) (hz : z ∈ c.region) :=
    lemma_6_3 E D.regular lam hlam x z (hHull x hx).1 (hHull z hz).1
      (by linarith only [(hHull x hx).2, hM]) (by linarith only [(hHull z hz).2, hM])
  have hPx {x : ℝ × ℝ} (hx : x ∈ c.region) : P E w ≤ 3 * P E x ∧ P E x ≤ 3 * P E w := by
    have hh := (hcross hx hroot).2.2.2.2
    exact ⟨hh w (by simp) x (by simp), hh x (by simp) w (by simp)⟩
  have hCrossProb {x z : ℝ × ℝ} (hx : x ∈ c.region) (hz : z ∈ c.region)
      {e : ℝ × ℝ} (he : e ∈ ({x,z,(x.1,z.2),(z.1,x.2)} : Set (ℝ × ℝ))) :
      c.est / 10 ≤ P E e ∧ P E e ≤ 10 * c.est := by
    have hh := (hcross hx hz).2.2.2.2
    have hl := hh x (by simp) e he
    have hu := hh e he x (by simp)
    obtain ⟨hxl, hxu⟩ := hPx hx
    have he0 := ((onUnit_facts E D.regular.1).1 e).1
    change phat T K δ (P E) U g.1 / 10 ≤ P E e ∧
      P E e ≤ 10 * phat T K δ (P E) U g.1
    exact ⟨by linarith only [hRel.2, hl, hxl, he0],
      by linarith only [hRel.1, hu, hxu, D.δ_pos, hPw]⟩
  refine ⟨fun x hx => (hHull x hx).1, initGroupCandidate_compact E T K δ U g θ,
    convex_convexHull ℝ _, hroot, ?_, ?_, hEst, (D.estimates g.1 hr.1).2.1, ?_⟩
  · intro u hu x hx
    have hxI := (hHull x hx).1
    have hb := balance_pos E D.regular.1 hxI
    have hbal := auxProfit_implies_balance_bound E D.regular.1 hlam hxI
      (d := 1 / Real.sqrt 2000) (by positivity)
      (by
        apply (div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2000))).mpr
        have hh : (1:ℝ) < Real.sqrt 2000 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
        simpa using hh)
      (by
        have he : (1 / Real.sqrt 2000)^2 = (1 / 2000 : ℝ) := by
          rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
        rw [he]
        exact (hHull x hx).2)
    have hbal' : |Real.log (balance E w / balance E x)| ≤ offsetRange := by
      rw [← inv_div, Real.log_inv, abs_neg]
      exact hbal
    have hcpos : 0 < c.param E * Real.exp u :=
      mul_pos (mul_pos (Real.exp_pos θ) hlam) (Real.exp_pos u)
    have hlog : |Real.log (c.param E * Real.exp u / balance E x)| ≤ 51 / 1000 := by
      change |Real.log (Real.exp θ * balance E w * Real.exp u / balance E x)| ≤ _
      rw [log_initCandidate_param hlam hb]
      let v := Real.log (balance E w / balance E x)
      change |θ + u + v| ≤ _
      have hh := abs_add_le (θ+u) v
      have htu := abs_add_le θ u
      change |v| ≤ offsetRange at hbal'
      linarith only [hh, htu, hθ, hu, hbal', offsetRange_le]
    have hs : Real.log (c.param E * Real.exp u / balance E x)^2 ≤ (51 / 1000 : ℝ)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hlog 2
    have hp := ((onUnit_facts E D.regular.1).2.2.1 _ (intT_subset_unitSq hxI)).mpr hxI
    have hm := mu_le_muStar E D.regular.1 (intT_subset_unitSq hxI)
    have hg' := (auxProfit_values E D.regular.1 hcpos hxI).2.1
    have hd' := hg'.trans ((mul_le_mul_of_nonneg_left hs hp.le).trans
      (mul_le_mul_of_nonneg_right hm (sq_nonneg _)))
    linarith only [hd', hμ hx, hM]
  · intro x hx z hz
    exact ⟨(hcross hx hz).1, (hcross hx hz).2.1, fun e he => hCrossProb hx hz he⟩
  · intro x hx
    have hs := sub_pos.mpr (hHull x hx).1.2.1
    apply (div_le_iff₀ hs).mpr
    have hδx : δ ≤ mu E x := by linarith only [hμ hx, hd, D.δ_pos]
    rw [mu_formula] at hδx
    have hPc := (hCrossProb hx hx (e := x) (by simp)).2
    rw [mul_comm (10 * c.est)]
    exact hδx.trans (mul_le_mul_of_nonneg_left hPc hs.le)

end

end BilateralProfitRegular
end BundlePart017


section BundlePart018


namespace BilateralProfitRegular

open Set MechanismDesign.BilateralTrade

private theorem gridK_pos_of_eta {η : ℝ} (hη : 0 < η) : 0 < gridK η :=
  Nat.ceil_pos.mpr (one_div_pos.mpr hη)

private theorem one_div_gridK_le_eta {η : ℝ} (hη : 0 < η) : 1 / (gridK η : ℝ) ≤ η := by
  have hK : 0 < (gridK η : ℝ) := Nat.cast_pos.mpr (gridK_pos_of_eta hη)
  have h := (div_le_iff₀ hη).mp (Nat.le_ceil (1 / η))
  exact (div_le_iff₀ hK).mpr (by rwa [mul_comm])

private theorem eta_lt_large_delta {η δ : ℝ} (hη : 0 < η) (hη₁ : η < 1)
    (hδ : (2:ℝ)^16 / (gridK η : ℝ) ≤ δ) : η < δ := by
  have hK : 0 < (gridK η : ℝ) := Nat.cast_pos.mpr (gridK_pos_of_eta hη)
  have h := Nat.ceil_lt_add_one (one_div_nonneg.mpr hη.le)
  change (gridK η : ℝ) < 1 / η + 1 at h
  have hmul := mul_lt_mul_of_pos_right h hη
  rw [add_mul, one_div_mul_cancel hη.ne', one_mul] at hmul
  apply lt_of_lt_of_le ((lt_div_iff₀ hK).mpr (by nlinarith only [hmul, hη₁] : η * (gridK η : ℝ) < 2))
  exact (div_le_div_of_nonneg_right (by norm_num) hK.le).trans hδ

private theorem InitCandidatesData.nearOpt_candidate {E : Environment} {T : ℕ} {η δ : ℝ}
    {U : Option ℕ × InitIndex × ℕ → unitInterval}
    (D : InitCandidatesData E T (gridK η) δ U) (hη : 0 < η)
    {ord : List InitIndex} (hord : IsOrder (gridK η) ord) :
    ∃ c ∈ candidates T η δ ord (P E) U, c.NearOpt E η δ := by
  let K := gridK η
  let x := gpt K D.best
  have hx := D.retained_interior D.best_retained
  have hbx := balance_pos E D.regular.1 hx
  let gs := groups T K δ ord (P E) U
  have hgs : InitGroupsCertified (E := E) (T := T) (K := K) (δ := δ) (U := U) gs :=
    D.groups_certified hord
  obtain ⟨g, hg, hmem⟩ := retained_mem_group hord D.best_retained
  let w := gpt K g.1
  have hw := D.retained_interior (hgs.root_retained hg)
  have hbw := balance_pos E D.regular.1 hw
  let t := Real.log (balance E x / balance E w)
  have ht : |t| ≤ offsetRange := by
    have hh := D.hull_high hgs hg (θ := 0) x (initGroupCandidate_mem hmem)
    have he : (1 / Real.sqrt 2000)^2 = (1 / 2000 : ℝ) := by
      rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
    have hD : 1 / Real.sqrt 2000 < 1 := by
      apply (div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2000))).mpr
      have hh' : (1:ℝ) < Real.sqrt 2000 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
      simpa using hh'
    apply auxProfit_implies_balance_bound E D.regular.1 hbw hx (by positivity) hD
    rw [he]
    exact hh.2
  obtain ⟨θ, hθ, hclose⟩ := exists_close_offset hη D.δ_pos ht
  let c := initGroupCandidate E T K δ U g θ
  refine ⟨c, (mem_initCandidates_iff E T η δ ord U c).mpr ⟨g, hg, θ, hθ, rfl⟩, ?_⟩
  intro u hu
  refine ⟨x, initGroupCandidate_mem hmem, ?_⟩
  let s := Real.sqrt (η / δ)
  have hs : 0 < s := Real.sqrt_pos.2 (div_pos hη D.δ_pos)
  have hz : Real.log (c.param E * Real.exp u / balance E x) = (θ - t) + u := by
    change Real.log (Real.exp θ * balance E w * Real.exp u / balance E x) = _
    rw [log_initCandidate_param hbw hbx, ← inv_div, Real.log_inv]
    change θ + u + -t = _
    ring
  have hsq : Real.log (c.param E * Real.exp u / balance E x)^2 ≤
      (251 / 1000 : ℝ)^2 * (η / δ) := by
    have hfinal : |Real.log (c.param E * Real.exp u / balance E x)| ≤ (251 / 1000) * s := by
      rw [hz]
      have htri := abs_add_le (θ - t) u
      change |u| ≤ 1 / 1000 * s at hu
      change |θ - t| ≤ 1 / 4 * s at hclose
      linarith only [htri, hu, hclose]
    have hh := pow_le_pow_left₀ (abs_nonneg _) hfinal 2
    rw [sq_abs, mul_pow, show s^2 = η / δ from Real.sq_sqrt (div_nonneg hη.le D.δ_pos.le)] at hh
    exact hh
  have hp := ((onUnit_facts E D.regular.1).2.2.1 _ (intT_subset_unitSq hx)).mpr hx
  have hpos : 0 < c.param E * Real.exp u :=
    mul_pos (mul_pos (Real.exp_pos θ) hbw) (Real.exp_pos u)
  have hr := (auxProfit_values E D.regular.1 hpos hx).2.1
  have hb0 : 0 ≤ (251 / 1000 : ℝ)^2 * (η / δ) :=
    mul_nonneg (sq_nonneg _) (div_nonneg hη.le D.δ_pos.le)
  have hμ := D.best_le_opt.trans D.opt_lt.le
  have hgap : mu E x - auxProfit E (c.param E * Real.exp u) x ≤ η := by
    apply hr.trans ((mul_le_mul_of_nonneg_left hsq hp.le).trans
      ((mul_le_mul_of_nonneg_right hμ hb0).trans _))
    have hh : 6 * δ * ((251 / 1000 : ℝ)^2 * (η / δ)) = 6 * (251 / 1000 : ℝ)^2 * η := by
      field_simp [D.δ_pos.ne']
    rw [hh]
    linarith only [hη]
  change muStar E - 3 * η ≤ auxProfit E (c.param E * Real.exp u) x
  have happrox := D.best_approx
  change muStar E - 2 / (K : ℝ) ≤ mu E x at happrox
  have hCoeff : 2 / (K : ℝ) ≤ 2 * η := by
    have hh := one_div_gridK_le_eta hη
    calc
      2 / (K : ℝ) = 2 * (1 / (K : ℝ)) := by ring
      _ ≤ 2 * η := mul_le_mul_of_nonneg_left hh (by norm_num)
  linarith only [hgap, happrox, hCoeff]

end BilateralProfitRegular
end BundlePart018


section BundlePart019



namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

private theorem packed_length_le (s : List ℝ) (a b : ℝ) (hab : a ≤ b)
    (hb : ∀ x ∈ s, a + 1 / 200 ≤ x ∧ x ≤ b)
    (hs : s.Pairwise (fun x y => 1 / 200 ≤ y - x)) :
    (s.length : ℝ) ≤ 200 * (b - a) := by
  induction s generalizing a with
  | nil => simp; linarith only [hab]
  | cons x xs ih =>
    obtain ⟨hx, hy⟩ := hb x (by simp)
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    refine le_trans ?_ (show 200 * (b - x) + 1 ≤ 200 * (b - a) by linarith only [hx])
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    have hh := ih x hy (fun y h =>
      ⟨by linarith only [hhead y h], (hb y (by simp [h])).2⟩) htail
    linarith only [hh]

private theorem InitCandidatesData.groups_count {E : Environment} {T K : ℕ} {δ : ℝ}
    {U : Option ℕ × InitIndex × ℕ → unitInterval}
    (D : InitCandidatesData E T K δ U) {ord : List InitIndex} (hord : IsOrder K ord) :
    ((groups T K δ ord (P E) U).length : ℝ) ≤ 1 + 200 * Real.log (K : ℝ) := by
  classical
  let gs := groups T K δ ord (P E) U
  let v (g : InitGroup) := Real.log (balance E (gpt K g.1))
  let us := gs.map v
  let vs := us.mergeSort (· ≤ ·)
  have hs := D.groups_certified hord
  have hsep : us.Pairwise (fun a b => 1 / 200 < |b - a|) := by
    rw [List.pairwise_map]
    exact hs.separated
  have hp : vs.Perm us := List.mergeSort_perm _ _
  have hsepV := hsep.perm hp.symm (fun {a b} h => by simpa only [abs_sub_comm] using h)
  have hsorted : vs.Pairwise (· ≤ ·) := (List.sortedLE_mergeSort (l := us)).pairwise
  have hv : vs.Pairwise (fun a b => 1 / 200 ≤ b - a) :=
    (hsepV.and hsorted).imp (fun h => by
      have hn := sub_nonneg.mpr h.2
      have hh := h.1
      rw [abs_of_nonneg hn] at hh
      exact hh.le)
  let half := 1 / 2 * Real.log (K : ℝ)
  have hh : ∀ x ∈ vs, -half ≤ x ∧ x ≤ half := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (hp.mem_iff.mp hx)
    exact abs_le.mp (D.root_log_bound (hs.root_retained hg))
  have hlog : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast D.K_pos)
  have hb : -half - 1 / 200 ≤ half := by dsimp [half]; linarith only [hlog]
  have H := packed_length_le vs (-half - 1 / 200) half hb
    (fun x hx => ⟨by linarith only [(hh x hx).1], (hh x hx).2⟩) hv
  rw [hp.length_eq, show us.length = gs.length from List.length_map v] at H
  dsimp [half] at H
  exact (show (gs.length : ℝ) ≤ 1 + 200 * Real.log (K : ℝ) from by linarith only [H])

private theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (n : ℕ)
    (h : ∀ x, (f x).length = n) : (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, h, ih, Nat.succ_mul]
    omega

private theorem InitCandidatesData.candidates_count {E : Environment} {T : ℕ} {η δ : ℝ}
    {U : Option ℕ × InitIndex × ℕ → unitInterval}
    (D : InitCandidatesData E T (gridK η) δ U) (hη : 0 < η) (hηδ : η ≤ δ)
    (hKT : gridK η ≤ T) {ord : List InitIndex} (hord : IsOrder (gridK η) ord) :
    ((candidates T η δ ord (P E) U).length : ℝ) ≤ 1000 * Real.sqrt (δ / η) * Real.log (2 * T) := by
  let gs := groups T (gridK η) δ ord (P E) U
  let os := offsets η δ
  have hf : (candidates T η δ ord (P E) U).length = gs.length * os.length := by
    unfold candidates
    apply length_flatMap_const
    intro g
    exact List.length_map _
  have hKT' : (gridK η : ℝ) ≤ T := Nat.cast_le.mpr hKT
  have hK : 0 < (gridK η : ℝ) := Nat.cast_pos.mpr D.K_pos
  have hT : (1 : ℝ) ≤ T := by exact_mod_cast D.K_pos.trans_le hKT
  have hlog := Real.log_le_log hK (by linarith only [hKT', hT] : (gridK η : ℝ) ≤ 2 * T)
  have hlow : 1 / 2 ≤ Real.log (2 * T) := by
    have hp : 0 < 2 * (T : ℝ) := by linarith only [hT]
    have hi : (2 * (T : ℝ))⁻¹ ≤ (1 / 2 : ℝ) := by
      rw [← one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hT])
    linarith only [Real.one_sub_inv_le_log_of_pos hp, hi]
  have hgroups : (gs.length : ℝ) ≤ 1000 / 3 * Real.log (2 * T) := by
    have hh := D.groups_count hord
    change (gs.length : ℝ) ≤ 1 + 200 * Real.log (gridK η : ℝ) at hh
    linarith only [hh, hlog, hlow]
  have hm := mul_le_mul hgroups (offsets_count hη hηδ) (Nat.cast_nonneg _)
    (by linarith only [hlow] : 0 ≤ 1000 / 3 * Real.log (2 * T))
  rw [hf, Nat.cast_mul]
  exact hm.trans_eq (by ring)

end BilateralProfitRegular
end BundlePart019


section BundlePart020



namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

/-- Deterministic guarantees for steps 3–7 of Algorithm 7 on the estimation event. -/
private theorem InitCandidatesData.guarantees {E : Environment} {T : ℕ} {η δ : ℝ}
    {U : Option ℕ × InitIndex × ℕ → unitInterval}
    (D : InitCandidatesData E T (gridK η) δ U)
    (hη : 0 < η) (hη₁ : η < 1) (hKT : gridK η ≤ T)
    {ord : List InitIndex} (hord : IsOrder (gridK η) ord) :
    InitGuarantee E η δ (candidates T η δ ord (P E) U) ∧
    ((candidates T η δ ord (P E) U).length : ℝ) ≤
      1000 * Real.sqrt (δ / η) * Real.log (2 * T) := by
  have hηδ := eta_lt_large_delta hη hη₁ D.δ_large
  refine ⟨⟨hηδ, D.δ_le_opt, D.opt_lt, ?_, D.nearOpt_candidate hη hord⟩,
    D.candidates_count hη hηδ.le hKT hord⟩
  intro c hc
  obtain ⟨g, hg, θ, hθ, rfl⟩ := (mem_initCandidates_iff E T η δ ord U c).mp hc
  exact D.candidate_valid (D.groups_certified hord) hg (offset_abs_le hη D.δ_pos hθ)

private theorem initCandidates_guarantees (E : Environment) (hE : RegularUnit E) (T : ℕ)
    (η δ : ℝ) (hη : 0 < η) (hη₁ : η < 1) (hKT : gridK η ≤ T)
    (ord : List InitIndex) (hord : IsOrder (gridK η) ord)
    (U : Option ℕ × InitIndex × ℕ → unitInterval)
    (hδMin : (2 : ℝ)^16 / (gridK η : ℝ) ≤ δ) (hδopt : δ ≤ muStar E)
    (hoptδ : muStar E < 6 * δ) (emax : InitIndex) (hemax : emax ∈ actList (gridK η))
    (hmax : ∀ e ∈ actList (gridK η), mu E (gpt (gridK η) e) ≤ mu E (gpt (gridK η) emax))
    (happrox : muStar E - 2 / (gridK η : ℝ) ≤ mu E (gpt (gridK η) emax))
    (hscale : (23 / 17) * δ ≤ mu E (gpt (gridK η) emax))
    (hest : ∀ e ∈ actList (gridK η),
      0 ≤ phat T (gridK η) δ (P E) U e ∧ phat T (gridK η) δ (P E) U e ≤ 1 ∧
      |phat T (gridK η) δ (P E) U e - P E (gpt (gridK η) e)| ≤
        (P E (gpt (gridK η) e) + δ) / 32768) :
    InitGuarantee E η δ (candidates T η δ ord (P E) U) ∧
    ((candidates T η δ ord (P E) U).length : ℝ) ≤
      1000 * Real.sqrt (δ / η) * Real.log (2 * T) :=
  InitCandidatesData.guarantees
    ⟨hE, gridK_pos_of_eta hη, hδMin, hδopt, hoptδ, emax, hemax, hmax, happrox, hscale, hest⟩
    hη hη₁ hKT hord

end BilateralProfitRegular
end BundlePart020


section BundlePart021



namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade

/-- The deterministic initializer guarantees on the joint probing event. -/
private theorem init_guarantees_on_probe {T : ℕ} {η : ℝ}
    (hη : 0 < η) (hη₁ : η < 1) (hKT : gridK η ≤ T)
    (E : Environment) (hE : RegularUnit E) (ord : List (ℕ × ℕ))
    (hord : IsOrder (gridK η) ord) (U : InitUniforms)
    (hgood : InitProbeGood T (gridK η) (P E) U) :
    match initRegular T η ord (P E) U with
    | none => muStar E ≤ (2 : ℝ)^48 / gridK η
    | some (δ, cs) =>
      InitGuarantee E η δ cs ∧
      (cs.length : ℝ) ≤ (2 : ℝ)^48 * Real.sqrt (δ / η) * Real.log (2 * T) ∧
      initRegret E T η U ≤ (2 : ℝ)^48 * gridK η * Real.log (T : ℝ)^2 := by
  let K := gridK η
  have hK := gridK_ge_two hη hη₁
  have hKpos : 0 < K := by omega
  have hK' : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hT := hK.trans hKT
  unfold initRegular
  change (match (match mhrScale T K (P E) U with
      | none => none
      | some h => if scale h < (2 : ℝ)^16 / K then none
        else some (scale h, candidates T η (scale h) ord (P E) U)) with
    | none => _
    | some (δ, cs) => _) 
  cases hs : mhrScale T K (P E) U with
  | none =>
    have h := mhrScale_no_trigger_bound hE.1 hKpos hgood hs
    change muStar E ≤ (2 : ℝ)^48 / (K : ℝ)
    exact h.le.trans (div_le_div_of_nonneg_right (by norm_num) hK'.le)
  | some h =>
    obtain ⟨best, hbest, hmax, hap⟩ := exists_regular_grid_best K hKpos E hE.1
    obtain ⟨hh, hδopt, hoptδ, hbestδ⟩ := mhrScale_trigger_bounds hE.1 hgood hs hbest hmax hap
    by_cases hsmall : scale h < (2 : ℝ)^16 / (K : ℝ)
    · simp only [if_pos hsmall]
      calc
        muStar E ≤ 6 * scale h := hoptδ.le
        _ ≤ 6 * ((2 : ℝ)^16 / (K : ℝ)) := mul_le_mul_of_nonneg_left hsmall.le (by norm_num)
        _ = (6 * (2 : ℝ)^16) / (K : ℝ) := by ring
        _ ≤ (2 : ℝ)^48 / (K : ℝ) := div_le_div_of_nonneg_right (by norm_num) hK'.le
    · have hlarge := le_of_not_gt hsmall
      simp only [if_neg hsmall]
      let D : InitCandidatesData E T K (scale h) U :=
        ⟨hE, hKpos, hlarge, hδopt, hoptδ, best, hbest, hmax, hap, hbestδ, fun e he => by
          obtain ⟨hij, hjK⟩ := mem_actList_iff.mp he
          obtain ⟨hu, he'⟩ := step2_phat_bounds E hE.1 T K h hKpos hh U hgood e.1 e.2 hij hjK
          exact ⟨hu.1, hu.2, he'⟩⟩
      obtain ⟨hinit, hcount⟩ := D.guarantees hη hη₁ hKT hord
      have hL : 0 ≤ Real.log (2 * (T : ℝ)) := zero_le_one.trans (init_log_ge_one hT)
      refine ⟨hinit, hcount.trans ?_, initRegret_trigger_bound E hE.1 hK hKT hs hlarge hoptδ.le⟩
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by norm_num : (1000 : ℝ) ≤ (2 : ℝ)^48)
        (Real.sqrt_nonneg _)) hL

private theorem lemma_6_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℕ) (η : ℝ), 0 < η → η < 1 → gridK η ≤ T →
      ∀ (E : Environment), RegularUnit E →
      ∀ ord : List (ℕ × ℕ), IsOrder (gridK η) ord →
        initCoinLaw {U |
          ¬ (match initRegular T η ord (P E) U with
            | none => muStar E ≤ C / gridK η
            | some (δ, cs) =>
                InitGuarantee E η δ cs ∧
                (cs.length : ℝ) ≤ C * Real.sqrt (δ / η) * Real.log (2 * T) ∧
                initRegret E T η U ≤ C * gridK η * Real.log T ^ 2)} ≤
          ENNReal.ofReal (1 / T) := by
  refine ⟨(2 : ℝ)^48, by positivity, ?_⟩
  intro T η hη hη₁ hKT E hE ord hord
  have hK := gridK_ge_two hη hη₁
  refine (measure_mono (t := {U | ¬ InitProbeGood T (gridK η) (P E) U}) ?_).trans ?_
  · intro U hbad hgood
    exact hbad (init_guarantees_on_probe hη hη₁ hKT E hE ord hord U hgood)
  · exact init_probe_failure hK hKT (P E) (onUnit_facts E hE.1).1


end BilateralProfitRegular
end BundlePart021

open BilateralProfitRegular
open MeasureTheory MechanismDesign.BilateralTrade

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℕ) (η : ℝ), 0 < η → η < 1 → gridK η ≤ T →
      ∀ (E : Environment), RegularUnit E →
      ∀ ord : List (ℕ × ℕ), IsOrder (gridK η) ord →
        initCoinLaw {U |
          ¬ (match initRegular T η ord (P E) U with
            | none => muStar E ≤ C / gridK η
            | some (δ, cs) =>
                InitGuarantee E η δ cs ∧
                (cs.length : ℝ) ≤ C * Real.sqrt (δ / η) * Real.log (2 * T) ∧
                initRegret E T η U ≤ C * gridK η * Real.log T ^ 2)} ≤
          ENNReal.ofReal (1 / T) := by
  exact BilateralProfitRegular.lemma_6_4
