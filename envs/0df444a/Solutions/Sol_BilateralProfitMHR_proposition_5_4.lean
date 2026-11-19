-- Prove2me | solution 1 for BilateralProfitMHR.proposition_5_4
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T11:53:21.139979+00:00
-- url     : https://prove2.me/submissions/d88be41b-5749-45a6-93b3-1741cbab9ba6

import Mathlib
import Definitions.Def_BilateralProfitMHR_InitializeMHR
import Theorems.Thm_BilateralProfitMHR_positive_density_profit_facts

noncomputable section
namespace BilateralProfitMHR
open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade Set
open scoped ENNReal
private lemma ptrade_nonneg (D : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : 0 ≤ Ptrade D a :=
  ENNReal.toReal_nonneg

private lemma ptrade_le_one (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D] (a : ℝ × ℝ) :
    Ptrade D a ≤ 1 := by
  unfold Ptrade
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr prob_le_one

private lemma mu_nonneg {D : Measure (ℝ × ℝ)} {a : ℝ × ℝ} (ha : a.1 ≤ a.2) :
    0 ≤ muP D a := mul_nonneg (sub_nonneg.mpr ha) (ptrade_nonneg D a)

private lemma mu_le_ptrade {D : Measure (ℝ × ℝ)} {a : ℝ × ℝ} (ha : a ∈ unitSq) :
    muP D a ≤ Ptrade D a := by
  unfold muP
  apply mul_le_of_le_one_left (ptrade_nonneg D a)
  rcases ha with ⟨ha, hb⟩
  linarith [ha.1, hb.2]

private lemma mu_le_one {D : Measure (ℝ × ℝ)} [IsProbabilityMeasure D] {a : ℝ × ℝ}
    (ha : a ∈ unitSq) : muP D a ≤ 1 :=
  (mu_le_ptrade ha).trans (ptrade_le_one D a)

private lemma abs_mu_le_one {D : Measure (ℝ × ℝ)} [IsProbabilityMeasure D] {a : ℝ × ℝ}
    (ha : a ∈ unitSq) : |muP D a| ≤ 1 := by
  apply abs_le.mpr
  refine ⟨?_, mu_le_ptrade ha |>.trans (ptrade_le_one D a)⟩
  have hg : -1 ≤ a.2 - a.1 := by linarith [ha.1.2,ha.2.1]
  have hp := ptrade_nonneg D a
  have hP := ptrade_le_one D a
  have hm := mul_le_mul_of_nonneg_right hg hp
  unfold muP
  nlinarith

private lemma prior_isProbabilityMeasure (E : Environment) (hE : UnitSupport E) : IsProbabilityMeasure E.prior := by
  obtain ⟨hprob, hmP, hPbounds, hPfactor, hFS, hFB, hμcont, hLcont, hμpos, hμstar, hμle, hatt, hbounds, hzero, hPprod, hgap⟩ := positive_density_profit_facts E hE
  exact hprob
private lemma ptrade_factorization (E : Environment) (hE : UnitSupport E) {a : ℝ × ℝ}
    (ha : a ∈ unitSq) : Ptrade E.prior a = E.cdfS a.1 * (1 - E.cdfB a.2) := by
  obtain ⟨hprob, hmP, hPbounds, hPfactor, hFS, hFB, hμcont, hLcont, hμpos, hμstar, hμle, hatt, hbounds, hzero, hPprod, hgap⟩ := positive_density_profit_facts E hE
  exact hPfactor a ha
private lemma ptrade_product (E : Environment) (hE : UnitSupport E) {x z y : ℝ}
    (hx : x ∈ Icc 0 1) (hz : z ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    Ptrade E.prior (x,z) * Ptrade E.prior (z,y) = Ptrade E.prior (x,y) * Ptrade E.prior (z,z) := by
  rw [ptrade_factorization E hE (a := (x,z)) ⟨hx,hz⟩,
    ptrade_factorization E hE (a := (z,y)) ⟨hz,hy⟩,
    ptrade_factorization E hE (a := (x,y)) ⟨hx,hy⟩,
    ptrade_factorization E hE (a := (z,z)) ⟨hz,hz⟩]
  ring
private lemma ptrade_le_center (E : Environment) (hE : UnitSupport E) {x z y : ℝ}
    (hx : x ∈ Icc 0 1) (hz : z ∈ Icc 0 1) (hy : y ∈ Icc 0 1) (hxz : x ≤ z) (hzy : z ≤ y) :
    Ptrade E.prior (x,z) ≤ Ptrade E.prior (z,z) ∧ Ptrade E.prior (z,y) ≤ Ptrade E.prior (z,z) ∧
      Ptrade E.prior (x,y) ≤ Ptrade E.prior (z,z) := by
  obtain ⟨hprob, hmP, hPbounds, hPfactor, hFS, hFB, hμcont, hLcont, hμpos, hμstar, hμle, hatt, hbounds, hzero, hPprod, hgap⟩ := positive_density_profit_facts E hE
  exact (hPprod x hx z hz y hy hxz hzy).2
private lemma mu_zero_left (E : Environment) (hE : UnitSupport E) {x : ℝ} (hx : x ∈ Icc 0 1) : muP E.prior (0,x) = 0 := by
  obtain ⟨hprob, hmP, hPbounds, hPfactor, hFS, hFB, hμcont, hLcont, hμpos, hμstar, hμle, hatt, hbounds, hzero, hPprod, hgap⟩ := positive_density_profit_facts E hE
  exact (hzero x hx).1
private lemma mu_zero_right (E : Environment) (hE : UnitSupport E) {x : ℝ} (hx : x ∈ Icc 0 1) : muP E.prior (x,1) = 0 := by
  obtain ⟨hprob, hmP, hPbounds, hPfactor, hFS, hFB, hμcont, hLcont, hμpos, hμstar, hμle, hatt, hbounds, hzero, hPprod, hgap⟩ := positive_density_profit_facts E hE
  exact (hzero x hx).2.1
private lemma mu_zero_diag (D : Measure (ℝ × ℝ)) (x : ℝ) : muP D (x,x) = 0 := by simp [muP]
end BilateralProfitMHR


set_option autoImplicit false

namespace BilateralProfitMHR

private theorem init_ratio_nonneg_le {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) :
    0 ≤ A * B / max (max A B) C ∧ A * B / max (max A B) C ≤ min A B := by
  let D := max (max A B) C
  have hAD : A ≤ D := (le_max_left A B).trans (le_max_left _ C)
  have hBD : B ≤ D := (le_max_right A B).trans (le_max_left _ C)
  have hD : 0 ≤ D := hC.trans (le_max_right _ C)
  refine ⟨div_nonneg (mul_nonneg hA hB) hD, ?_⟩
  change A * B / D ≤ min A B
  by_cases hz : D = 0
  · simp [hz, le_min hA hB]
  · have hp : 0 < D := lt_of_le_of_ne hD (Ne.symm hz)
    apply le_min
    · apply (div_le_iff₀ hp).2
      nlinarith [mul_le_mul_of_nonneg_left hBD hA]
    · apply (div_le_iff₀ hp).2
      nlinarith [mul_le_mul_of_nonneg_left hAD hB]


private theorem init_ratio_error {a b c p A B C δ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (hac : a ≤ c) (hbc : b ≤ c) (hpc : p ≤ c) (hid : a * b = p * c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hea : |A - a| ≤ (a + δ) / 128)
    (heb : |B - b| ≤ (b + δ) / 128)
    (hec : |C - c| ≤ (c + δ) / 128) :
    |A * B / max (max A B) C - p| ≤ (p + δ) / 16 := by
  let D := max (max A B) C
  have hD : 0 ≤ D := hC.trans (le_max_right _ _)
  have hbounds := init_ratio_nonneg_le hA hB hC
  have hDerr : |D - c| ≤ (c + δ) / 128 := by
    rw [abs_sub_le_iff] at hea heb hec ⊢
    constructor
    · apply sub_le_iff_le_add.mpr
      apply max_le
      · exact max_le (by linarith) (by linarith)
      · linarith
    · have hCD : C ≤ D := le_max_right _ _
      linarith
  by_cases hsmall : c < δ / 32
  · have hAu : A ≤ c + (c + δ) / 128 := by
      have := (abs_sub_le_iff.mp hea).1
      linarith
    have hr := hbounds.2.trans (min_le_left _ _)
    rw [abs_sub_le_iff]
    constructor <;> nlinarith [hbounds.1]
  · have hδc : δ ≤ 32 * c := by linarith
    have hcp : 0 < c := by linarith
    have hDp : 0 < D := by
      have := (abs_sub_le_iff.mp hDerr).2
      linarith
    have hDlow : c / 2 ≤ D := by
      have := (abs_sub_le_iff.mp hDerr).2
      linarith
    have heq : A * B - p * D =
        b * (A - a) + a * (B - b) + (A - a) * (B - b) - p * (D - c) := by
      nlinarith [hid]
    have hnum : |A * B - p * D| ≤
        b * ((a + δ) / 128) + a * ((b + δ) / 128) +
          ((a + δ) / 128) * ((b + δ) / 128) + p * ((c + δ) / 128) := by
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
      nlinarith [mul_le_mul_of_nonneg_left hac hδ.le,
        mul_le_mul_of_nonneg_left hbc hδ.le,
        mul_le_mul_of_nonneg_left hpc hδ.le]
    have hcross : (a + δ) * (b + δ) ≤ 34 * c * (p + δ) := by
      nlinarith [mul_le_mul_of_nonneg_left hac hδ.le,
        mul_le_mul_of_nonneg_left hbc hδ.le,
        mul_le_mul_of_nonneg_left hδc hδ.le, mul_nonneg hc hp]
    have hnum' : |A * B - p * D| ≤ c * (p + δ) / 32 := by
      nlinarith [mul_nonneg hc (show 0 ≤ p + δ by linarith)]
    change |A * B / D - p| ≤ _
    have hdiv : A * B / D - p = (A * B - p * D) / D := by
      field_simp
      <;> ring
    rw [hdiv, abs_div, abs_of_pos hDp]
    apply (div_le_iff₀ hDp).2
    nlinarith [mul_le_mul_of_nonneg_right hDlow (show 0 ≤ p + δ by linarith)]

private theorem init_profit_error {P Q d δ : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (h : |Q - P| ≤ (P + δ) / 16) (hδ : 0 ≤ δ) :
    |d * Q - d * P| ≤ (d * P + δ) / 16 := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hd]
  have hm := mul_le_mul_of_nonneg_left h hd
  have hδd := mul_le_mul_of_nonneg_right hd1 hδ
  nlinarith

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

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade

private theorem init_nat_div_mem_Icc {K i : ℕ} (hK : 0 < K) (hi : i ≤ K) :
    (i : ℝ) / K ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨by positivity, (div_le_one (by positivity : (0 : ℝ) < K)).2 ?_⟩
  exact_mod_cast hi

private theorem init_measurable_tradeBit (a : ℝ × ℝ) : Measurable fun v => tradeBit v a := by
  unfold tradeBit Trades
  exact Measurable.ite ((measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_const measurable_snd)) measurable_const measurable_const

private theorem init_measurable_Pbar (K T h i j : ℕ) :
    Measurable fun ω : Samples K T => Pbar K T h ω i j := by
  classical
  unfold Pbar
  split_ifs with hh
  · apply Measurable.div_const
    apply Finset.measurable_sum
    intro r _
    exact (init_measurable_tradeBit _).comp (measurable_pi_apply _)
  · exact measurable_const

private theorem init_Pbar_nonneg (K T h : ℕ) (ω : Samples K T) (i j : ℕ) :
    0 ≤ Pbar K T h ω i j := by
  classical
  unfold Pbar
  split_ifs
  · apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro r _
    unfold tradeBit
    split_ifs <;> norm_num
  · exact le_rfl

private theorem init_measurable_muHat (K T h : ℕ) (e : Act K) :
    Measurable fun ω : Samples K T => muHat K T h ω e := by
  classical
  unfold muHat
  split_ifs
  · exact measurable_const.mul (((init_measurable_Pbar _ _ _ _ _).mul
      (init_measurable_Pbar _ _ _ _ _)).div
      (((init_measurable_Pbar _ _ _ _ _).max (init_measurable_Pbar _ _ _ _ _)).max
        (init_measurable_Pbar _ _ _ _ _)))
  · exact measurable_const


private theorem init_reconstruction_error {K T h : ℕ} (hK : 0 < K) (E : Environment)
    (hE : UnitSupport E) (ω : Samples K T)
    (hfreq : ∀ z ∈ Spairs K,
      |Pbar K T h ω z.1 z.2 - Ptrade E.prior ((z.1 : ℝ) / K, (z.2 : ℝ) / K)| ≤
        (Ptrade E.prior ((z.1 : ℝ) / K, (z.2 : ℝ) / K) + delta h) / 128) :
    ∀ e : Act K, |muHat K T h ω e - muP E.prior (pt K e.1)| ≤
      (muP E.prior (pt K e.1) + delta h) / 16 := by
  intro e
  let i : ℕ := e.1.1
  let j : ℕ := e.1.2
  have hij : i ≤ j := e.2
  have hiK : i ≤ K := Nat.lt_succ_iff.mp e.1.1.isLt
  have hjK : j ≤ K := Nat.lt_succ_iff.mp e.1.2.isLt
  have hiR := init_nat_div_mem_Icc hK hiK
  have hjR := init_nat_div_mem_Icc hK hjK
  by_cases hint : 1 ≤ i ∧ i < j ∧ j < K
  · let k := sepMid K i j
    obtain ⟨hik, hkj, hsik, hskj, hskk⟩ := sepMid_spec hint.2.1 hjK
    have hkK : k ≤ K := hkj.le.trans hjK
    have hkR := init_nat_div_mem_Icc hK hkK
    have hikR : (i : ℝ) / K ≤ (k : ℝ) / K := by gcongr
    have hkjR : (k : ℝ) / K ≤ (j : ℝ) / K := by gcongr
    have hprod := ptrade_product E hE hiR hkR hjR
    obtain ⟨h1, h2, h3⟩ := ptrade_le_center E hE hiR hkR hjR hikR hkjR
    have herr := init_ratio_error
      (ptrade_nonneg E.prior _) (ptrade_nonneg E.prior _)
      (ptrade_nonneg E.prior _) (ptrade_nonneg E.prior _)
      h1 h2 h3 hprod
      (init_Pbar_nonneg K T h ω i k) (init_Pbar_nonneg K T h ω k j)
      (init_Pbar_nonneg K T h ω k k) (init_delta_pos h)
      (hfreq (i, k) hsik) (hfreq (k, j) hskj) (hfreq (k, k) hskk)
    have hwidth0 : 0 ≤ ((j : ℝ) - i) / K := by
      apply div_nonneg _ (Nat.cast_nonneg _)
      exact sub_nonneg.mpr (by exact_mod_cast hij)
    have hwidth1 : ((j : ℝ) - i) / K ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < K)).2
      have : (j : ℝ) ≤ K := by exact_mod_cast hjK
      linarith [Nat.cast_nonneg (α := ℝ) i]
    have hout := init_profit_error hwidth0 hwidth1 herr (init_delta_pos h).le
    change |muHat K T h ω e - ((j : ℝ) / K - (i : ℝ) / K) *
      Ptrade E.prior ((i : ℝ) / K, (j : ℝ) / K)| ≤ _
    have hm : muHat K T h ω e = ((j : ℝ) - i) / K *
        (Pbar K T h ω i k * Pbar K T h ω k j /
          max (max (Pbar K T h ω i k) (Pbar K T h ω k j)) (Pbar K T h ω k k)) := by
      exact if_pos hint
    rw [hm, ← sub_div]
    simpa only [muP, pt, Prod.fst, Prod.snd, i, j, ← sub_div] using hout
  · have hmu : muP E.prior (pt K e.1) = 0 := by
      have hcases : i = 0 ∨ i = j ∨ j = K := by omega
      rcases hcases with hi | hij | hj
      · change muP E.prior ((i : ℝ) / K, (j : ℝ) / K) = 0
        rw [hi, Nat.cast_zero, zero_div]
        exact mu_zero_left E hE hjR
      · change muP E.prior ((i : ℝ) / K, (j : ℝ) / K) = 0
        rw [hij]
        exact mu_zero_diag _ _
      · change muP E.prior ((i : ℝ) / K, (j : ℝ) / K) = 0
        rw [hj, div_self (by positivity : (K : ℝ) ≠ 0)]
        exact mu_zero_right E hE hiR
    have hhat : muHat K T h ω e = 0 := if_neg hint
    rw [hhat, hmu]
    have := init_delta_pos h
    simp only [sub_self, abs_zero, zero_add]
    positivity

end BilateralProfitMHR


set_option autoImplicit false

namespace BilateralProfitMHR

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
    (δ : ℝ) (hδ : 0 < δ) :
    P.real {ω | |(∑ i, X i ω) / n - p| > (p + δ) / 128} ≤
      2 * Real.exp (-((n : ℝ) * δ) / 16384) := by
  let Z := fun ω => ∑ i, (X i ω - p)
  let ε := (n : ℝ) * (p + δ) / 128
  obtain ⟨hIp, hMp⟩ := init_bernoulli_sum_mgf P X hX hv hi p hp (1 / 128) (by norm_num)
  obtain ⟨hIn, hMn⟩ := init_bernoulli_sum_mgf P X hX hv hi p hp (-1 / 128) (by norm_num)
  have hpos := measure_ge_le_exp_mul_mgf (μ := P) (X := Z) ε (t := 1 / 128)
    (by norm_num) hIp
  have hneg := measure_le_le_exp_mul_mgf (μ := P) (X := Z) (-ε) (t := -1 / 128)
    (by norm_num) hIn
  have hpos' : P.real {ω | ε ≤ Z ω} ≤ Real.exp (-((n : ℝ) * δ) / 16384) := by
    apply hpos.trans
    calc
      _ ≤ Real.exp (-(1 / 128) * ε) * Real.exp ((n : ℝ) * p * (1 / 128) ^ 2) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [ε]; ring
  have hneg' : P.real {ω | Z ω ≤ -ε} ≤ Real.exp (-((n : ℝ) * δ) / 16384) := by
    apply hneg.trans
    calc
      _ ≤ Real.exp (-(-1 / 128) * (-ε)) * Real.exp ((n : ℝ) * p * (-1 / 128) ^ 2) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [ε]; ring
  have hsub : {ω | |(∑ i, X i ω) / n - p| > (p + δ) / 128} ⊆
      {ω | ε ≤ Z ω} ∪ {ω | Z ω ≤ -ε} := by
    intro ω hω
    change (p + δ) / 128 < |(∑ i, X i ω) / n - p| at hω
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
      nlinarith
    · right
      rw [abs_of_nonpos hz] at hω'
      dsimp [ε]
      nlinarith
  calc
    _ ≤ P.real ({ω | ε ≤ Z ω} ∪ {ω | Z ω ≤ -ε}) := measureReal_mono hsub
    _ ≤ P.real {ω | ε ≤ Z ω} + P.real {ω | Z ω ≤ -ε} := measureReal_union_le _ _
    _ ≤ _ := by linarith

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
open MeasureTheory BilateralProfit
private theorem init_integrable_tradeBit (D : Measure (ℝ × ℝ)) [IsFiniteMeasure D] (a : ℝ × ℝ) :
    Integrable (fun v => tradeBit v a) D := by
  apply (integrable_const (1 : ℝ)).mono' (init_measurable_tradeBit a).aestronglyMeasurable
  exact ae_of_all _ (fun v => by unfold tradeBit; split_ifs <;> norm_num)

private theorem init_integral_tradeBit (D : Measure (ℝ × ℝ)) (a : ℝ × ℝ) :
    (∫ v, tradeBit v a ∂D) = Ptrade D a := by
  have hs : MeasurableSet {v | Trades v a} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_const measurable_snd)
  simpa only [Ptrade, tradeBit, Set.indicator, Set.mem_setOf_eq, measureReal_def, Pi.one_apply] using
    (integral_indicator_one (μ := D) hs : (∫ v, {v | Trades v a}.indicator (fun _ => (1 : ℝ)) v ∂D) = _)

private theorem init_integrable_profit (D : Measure (ℝ × ℝ)) [IsFiniteMeasure D] (a : ℝ × ℝ) :
    Integrable (fun v => profit v a) D :=
  (init_integrable_tradeBit D a).const_mul _

private theorem init_integral_profit (D : Measure (ℝ × ℝ)) (a : ℝ × ℝ) :
    (∫ v, profit v a ∂D) = muP D a := by
  unfold profit muP
  rw [integral_const_mul, init_integral_tradeBit]


end BilateralProfitMHR


set_option autoImplicit false

namespace BilateralProfitMHR

open MeasureTheory ProbabilityTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem init_Pbar_tail {K T : ℕ} (hK : 2 ≤ K) (hKT : K ≤ T) (E : Environment) (hE : UnitSupport E)
    (h : Fin (numScales K)) (i j : Fin (K + 1)) :
    (initLaw K T E.prior).real {ω |
      |Pbar K T h ω i j - Ptrade E.prior ((i : ℝ) / K, (j : ℝ) / K)| >
        (Ptrade E.prior ((i : ℝ) / K, (j : ℝ) / K) + delta h) / 128} ≤
      2 * Real.exp (-4 * Real.log (2 * T)) := by
  classical
  letI := prior_isProbabilityMeasure E hE
  letI : IsProbabilityMeasure (initLaw K T E.prior) := by unfold initLaw; infer_instance
  let a : ℝ × ℝ := ((i : ℝ) / K, (j : ℝ) / K)
  let emb : Fin (nSamp T h) → SampleIdx K T := fun r => ⟨h, (i, j), r⟩
  let X := fun r (ω : Samples K T) => tradeBit (ω (emb r)) a
  have hemb : Function.Injective emb := by
    intro r s he
    simpa [emb] using he
  have hX : ∀ r, Measurable (X r) := fun r =>
    (init_measurable_tradeBit a).comp (measurable_pi_apply (emb r))
  have hv : ∀ r ω, X r ω = 0 ∨ X r ω = 1 := by
    intro r ω
    unfold X tradeBit
    split_ifs <;> simp
  have hiAll : iIndepFun (fun z : SampleIdx K T => fun ω : Samples K T => ω z)
      (initLaw K T E.prior) := iIndepFun_pi (fun _ => aemeasurable_id)
  have hi : iIndepFun X (initLaw K T E.prior) :=
    (hiAll.precomp hemb).comp (fun _ v => tradeBit v a) (fun _ => init_measurable_tradeBit a)
  have hp r : ∫ ω, X r ω ∂(initLaw K T E.prior) = Ptrade E.prior a := by
    have hmap := (measurePreserving_eval (fun _ : SampleIdx K T => E.prior) (emb r)).map_eq
    change Measure.map (fun ω : Samples K T => ω (emb r)) (initLaw K T E.prior) = E.prior at hmap
    have hint := integral_map (μ := initLaw K T E.prior)
      (measurable_pi_apply (emb r)).aemeasurable (init_measurable_tradeBit a).aestronglyMeasurable
    rw [hmap] at hint
    exact hint.symm.trans (init_integral_tradeBit E.prior a)
  have hL := init_log_ge_one (hK.trans hKT)
  have hδ := init_delta_pos h
  have hn : 0 < nSamp T h := by
    unfold nSamp
    apply Nat.ceil_pos.mpr
    positivity
  have ht := init_bernoulli_average_tail (initLaw K T E.prior) hn X hX hv hi
    (Ptrade E.prior a) hp (delta h) hδ
  have hbar (ω : Samples K T) : Pbar K T h ω i j =
      (∑ r, X r ω) / nSamp T h := by
    unfold Pbar
    rw [dif_pos ⟨h.isLt, i.isLt, j.isLt⟩]
  simp_rw [hbar]
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hc := Nat.le_ceil ((2 : ℝ) ^ 16 * Real.log (2 * T) / delta h)
  change (2 : ℝ) ^ 16 * Real.log (2 * T) / delta h ≤ (nSamp T h : ℝ) at hc
  have hc' := (div_le_iff₀ hδ).mp hc
  norm_num only [show (2 : ℝ) ^ 16 = 65536 by norm_num] at hc'
  linarith

private noncomputable def initFrequencyGood (K T : ℕ) (D : Measure (ℝ × ℝ)) : Set (Samples K T) :=
  {ω | ∀ h : Fin (numScales K), ∀ i j : Fin (K + 1),
    |Pbar K T h ω i j - Ptrade D ((i : ℝ) / K, (j : ℝ) / K)| ≤
      (Ptrade D ((i : ℝ) / K, (j : ℝ) / K) + delta h) / 128}

private theorem init_frequency_good_measurable (K T : ℕ) (D : Measure (ℝ × ℝ)) :
    MeasurableSet (initFrequencyGood K T D) := by
  simp only [initFrequencyGood, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro h
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le (((init_measurable_Pbar _ _ _ _ _).sub_const _).abs) measurable_const

private theorem init_frequency_failure_bound {K T : ℕ} (hK : 2 ≤ K) (hKT : K ≤ T)
    (E : Environment) (hE : UnitSupport E) :
    (initLaw K T E.prior).real (initFrequencyGood K T E.prior)ᶜ ≤ 1 / (T : ℝ) := by
  classical
  letI := prior_isProbabilityMeasure E hE
  letI : IsProbabilityMeasure (initLaw K T E.prior) := by unfold initLaw; infer_instance
  let F := fun z : Fin (numScales K) × Fin (K + 1) × Fin (K + 1) =>
    {ω : Samples K T |
      |Pbar K T z.1 ω z.2.1 z.2.2 - Ptrade E.prior ((z.2.1 : ℝ) / K, (z.2.2 : ℝ) / K)| >
        (Ptrade E.prior ((z.2.1 : ℝ) / K, (z.2.2 : ℝ) / K) + delta z.1) / 128}
  have heq : (initFrequencyGood K T E.prior)ᶜ = ⋃ z, F z := by
    ext ω
    simp only [initFrequencyGood, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall,
      not_le, Set.mem_iUnion, F]
    constructor
    · rintro ⟨h, i, j, he⟩
      exact ⟨(h, i, j), he⟩
    · rintro ⟨⟨h, i, j⟩, he⟩
      exact ⟨h, i, j, he⟩
  have hsum : (initLaw K T E.prior).real (initFrequencyGood K T E.prior)ᶜ ≤
      (numScales K : ℝ) * (K + 1 : ℝ) ^ 2 * (2 * Real.exp (-4 * Real.log (2 * T))) := by
    rw [heq]
    apply (measureReal_iUnion_fintype_le _).trans
    apply (Finset.sum_le_sum (fun z _ => init_Pbar_tail hK hKT E hE z.1 z.2.1 z.2.2)).trans_eq
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  have hT : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hsc : (numScales K : ℝ) ≤ T := by
    exact_mod_cast (init_numScales_le (by omega : 0 < K)).trans hKT
  have hKreal : (K : ℝ) + 1 ≤ 2 * T := by exact_mod_cast (by omega : K + 1 ≤ 2 * T)
  have hexp : Real.exp (-4 * Real.log (2 * T)) = ((2 * (T : ℝ)) ^ 4)⁻¹ := by
    rw [neg_mul, Real.exp_neg]
    congr 1
    calc
      _ = Real.exp (Real.log (2 * (T : ℝ))) ^ 4 := by
        simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (Real.log (2 * (T : ℝ))) 4
      _ = _ := by rw [Real.exp_log (by positivity)]
  rw [hexp] at hsum
  apply hsum.trans
  have hcard : (numScales K : ℝ) * (K + 1 : ℝ) ^ 2 ≤ 4 * (T : ℝ) ^ 3 := by
    have hsq : (K + 1 : ℝ) ^ 2 ≤ (2 * (T : ℝ)) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) K]
    nlinarith [mul_le_mul hsc hsq (by positivity : (0 : ℝ) ≤ (K + 1 : ℝ) ^ 2) hT.le]
  calc
    _ ≤ 4 * (T : ℝ) ^ 3 * (2 * ((2 * (T : ℝ)) ^ 4)⁻¹) := by gcongr
    _ ≤ 1 / (T : ℝ) := by
      field_simp
      nlinarith

private theorem init_frequency_good_probability {K T : ℕ} (hK : 2 ≤ K) (hKT : K ≤ T)
    (E : Environment) (hE : UnitSupport E) :
    1 - (T : ℝ≥0∞)⁻¹ ≤ initLaw K T E.prior (initFrequencyGood K T E.prior) := by
  letI := prior_isProbabilityMeasure E hE
  letI : IsProbabilityMeasure (initLaw K T E.prior) := by unfold initLaw; infer_instance
  have hb := init_frequency_failure_bound hK hKT E hE
  have hm := init_frequency_good_measurable K T E.prior
  have he : (initLaw K T E.prior) (initFrequencyGood K T E.prior)ᶜ ≤ (T : ℝ≥0∞)⁻¹ := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast (show T ≠ 0 by omega)))).mp
    simpa [measureReal_def, ENNReal.toReal_inv] using hb
  rw [measure_compl hm (measure_ne_top _ _)] at he
  simp only [measure_univ] at he
  exact tsub_le_iff_right.mpr ((tsub_le_iff_right.mp he).trans_eq (add_comm _ _))

end BilateralProfitMHR


set_option autoImplicit false

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem init_frequency_good_accuracy {K T : ℕ} (hK : 0 < K) (E : Environment)
    (hE : UnitSupport E) {ω : Samples K T} (hω : ω ∈ initFrequencyGood K T E.prior) :
    ∀ h ∈ testedScales K T ω, ∀ e : Act K,
      |muHat K T h ω e - muP E.prior (pt K e.1)| ≤
        (muP E.prior (pt K e.1) + delta h) / 16 := by
  intro h hh
  apply init_reconstruction_error hK E hE ω
  intro z hz
  obtain ⟨hij, hjK⟩ := Spairs_bounds hz
  have hiK := hij.trans hjK
  exact hω ⟨h, init_tested_lt hh⟩ ⟨z.1, by omega⟩ ⟨z.2, by omega⟩

private theorem prop54_main (T K : ℕ) (hK : 2 ≤ K) (hKT : K ≤ T) (E : Environment)
    (hE : UnitSupport E) :
    ∃ G : Set (Samples K T), MeasurableSet G ∧ 1 - (T : ℝ≥0∞)⁻¹ ≤ initLaw K T E.prior G ∧
      ∀ ω ∈ G, ∀ h ∈ testedScales K T ω, ∀ e : Act K,
        |muHat K T h ω e - muP E.prior (pt K e.1)| ≤ (muP E.prior (pt K e.1) + delta h) / 16 := by
  refine ⟨initFrequencyGood K T E.prior, init_frequency_good_measurable K T E.prior,
    init_frequency_good_probability hK hKT E hE, ?_⟩
  intro ω hω
  exact init_frequency_good_accuracy (by omega) E hE hω

end BilateralProfitMHR
open BilateralProfitMHR MeasureTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal

theorem solution (T K : ℕ) (hK : 2 ≤ K) (hKT : K ≤ T) (E : Environment)
    (hE : UnitSupport E) :
    ∃ G : Set (Samples K T), MeasurableSet G ∧ 1 - (T : ℝ≥0∞)⁻¹ ≤ initLaw K T E.prior G ∧
      ∀ ω ∈ G, ∀ h ∈ testedScales K T ω, ∀ e : Act K,
        |muHat K T h ω e - muP E.prior (pt K e.1)| ≤ (muP E.prior (pt K e.1) + delta h) / 16 :=
  BilateralProfitMHR.prop54_main T K hK hKT E hE

