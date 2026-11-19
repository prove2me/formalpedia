-- Prove2me | solution 1 for BilateralProfitMHR.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T11:56:14.226335+00:00
-- url     : https://prove2.me/submissions/d9aeaa5b-e6c4-463d-a08c-07bba2afdc4c

import Mathlib
import Definitions.Def_BilateralProfitMHR_InitializeMHR
import Theorems.Thm_BilateralProfitMHR_positive_density_profit_facts
import Theorems.Thm_BilateralProfitMHR_proposition_3_2
import Theorems.Thm_BilateralProfit_lemma_A_6
import Theorems.Thm_BilateralProfitMHR_proposition_5_4

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

private lemma intT_subset_unitSq : intT ⊆ unitSq := by
  intro a ha
  exact ⟨⟨ha.1.le, (ha.2.1.trans ha.2.2).le⟩, ⟨(ha.1.trans ha.2.1).le, ha.2.2.le⟩⟩
private lemma mu_le_muStar (E : Environment) (hE : UnitSupport E) {a : ℝ × ℝ} (ha : a ∈ unitSq) : muP E.prior a ≤ muStar E.prior := by
  obtain ⟨hprob, hmP, hPbounds, hPfactor, hFS, hFB, hμcont, hLcont, hμpos, hμstar, hμle, hatt, hbounds, hzero, hPprod, hgap⟩ := positive_density_profit_facts E hE
  exact hμle a ha
private lemma muStar_pos (E : Environment) (hE : UnitSupport E) : 0 < muStar E.prior := by
  obtain ⟨hprob, hmP, hPbounds, hPfactor, hFS, hFB, hμcont, hLcont, hμpos, hμstar, hμle, hatt, hbounds, hzero, hPprod, hgap⟩ := positive_density_profit_facts E hE
  exact hμstar.1
private lemma muStar_le_one (E : Environment) (hE : UnitSupport E) : muStar E.prior ≤ 1 := by
  obtain ⟨hprob, hmP, hPbounds, hPfactor, hFS, hFB, hμcont, hLcont, hμpos, hμstar, hμle, hatt, hbounds, hzero, hPprod, hgap⟩ := positive_density_profit_facts E hE
  exact hμstar.2
private lemma exists_muStar (E : Environment) (hE : UnitSupport E) : ∃ a ∈ intT, muP E.prior a = muStar E.prior := by
  obtain ⟨hprob, hmP, hPbounds, hPfactor, hFS, hFB, hμcont, hLcont, hμpos, hμstar, hμle, hatt, hbounds, hzero, hPprod, hgap⟩ := positive_density_profit_facts E hE
  exact hatt
private lemma continuousOn_mu (E : Environment) (hE : UnitSupport E) : ContinuousOn (muP E.prior) unitSq := by
  obtain ⟨hprob, hmP, hPbounds, hPfactor, hFS, hFB, hμcont, hLcont, hμpos, hμstar, hμle, hatt, hbounds, hzero, hPprod, hgap⟩ := positive_density_profit_facts E hE
  exact hμcont
private lemma mu_pos (E : Environment) (hE : UnitSupport E) {a : ℝ × ℝ} (ha : a ∈ intT) : 0 < muP E.prior a := by
  obtain ⟨hprob, hmP, hPbounds, hPfactor, hFS, hFB, hμcont, hLcont, hμpos, hμstar, hμle, hatt, hbounds, hzero, hPprod, hgap⟩ := positive_density_profit_facts E hE
  exact (hμpos a (intT_subset_unitSq ha)).mpr ha
private lemma profit_superlevel_convex (E : Environment) (hE : UnitSupport E) (hM : IsMHR E)
    {c : ℝ} (hc : 0 < c) : Convex ℝ {a ∈ intT | c ≤ muP E.prior a} := by
  have h := (BilateralProfitMHR.proposition_3_2 E hE hM).2.convex_le (-Real.log c)
  convert! h using 1
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨ha,hcμ⟩
    refine ⟨ha, ?_⟩
    change -Real.log (muP E.prior a) ≤ -Real.log c
    exact neg_le_neg ((Real.log_le_log_iff hc (mu_pos E hE ha)).mpr hcμ)
  · rintro ⟨ha,hL⟩
    refine ⟨ha, ?_⟩
    change -Real.log (muP E.prior a) ≤ -Real.log c at hL
    exact (Real.log_le_log_iff hc (mu_pos E hE ha)).mp (neg_le_neg_iff.mp hL)
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

namespace BilateralProfitMHR
open MeasureTheory BilateralProfit
private theorem init_nat_div_mem_Icc {K i : ℕ} (hK : 0 < K) (hi : i ≤ K) :
    (i : ℝ) / K ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨by positivity, (div_le_one (by positivity : (0 : ℝ) < K)).2 ?_⟩
  exact_mod_cast hi

private theorem init_measurable_tradeBit (a : ℝ × ℝ) : Measurable fun v => tradeBit v a := by
  unfold tradeBit Trades
  exact Measurable.ite ((measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_const measurable_snd)) measurable_const measurable_const


end BilateralProfitMHR


set_option autoImplicit false

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade

private theorem init_grid_max_exists (K : ℕ) (D : Measure (ℝ × ℝ)) :
    ∃ e : Act K, IsGridMax K D e := by
  classical
  let e0 : Act K := ⟨(0, 0), le_rfl⟩
  obtain ⟨e, _, he⟩ := Finset.exists_max_image Finset.univ
    (fun e : Act K => muP D (pt K e.1)) (Finset.univ_nonempty (α := Act K))
  exact ⟨e, fun e' => he e' (Finset.mem_univ _)⟩

private theorem init_trigger_grid_bounds {K T h : ℕ} {D : Measure (ℝ × ℝ)}
    {ω : Samples K T} (hf : firstTrigger K T ω = some h) (eStar : Act K)
    (heStar : IsGridMax K D eStar) (hunit : muP D (pt K eStar.1) ≤ 1)
    (hAcc : ∀ j ∈ testedScales K T ω, ∀ e : Act K,
      |muHat K T j ω e - muP D (pt K e.1)| ≤ (muP D (pt K e.1) + delta j) / 16) :
    delta h ≤ muP D (pt K eStar.1) ∧ muP D (pt K eStar.1) < 4 * delta h := by
  obtain ⟨hh, ⟨e, he⟩, hprev⟩ := init_firstTrigger_spec hf
  have hAc := hAcc h (init_trigger_mem_tested hf) e
  have heM := heStar e
  have hδ := init_delta_pos h
  constructor
  · have hupper := (abs_sub_le_iff.mp hAc).1
    linarith
  · cases h with
    | zero => simpa [delta] using (show muP D (pt K eStar.1) < 4 by linarith)
    | succ j =>
      have hj : j < j + 1 := Nat.lt_succ_self _
      have hnt : muHat K T j ω eStar < 3 * delta j / 2 := by
        by_contra hn
        exact hprev j hj ⟨eStar, le_of_not_gt hn⟩
      have hjAcc := hAcc j (init_preceding_mem_tested hf hj) eStar
      have hlower := (abs_sub_le_iff.mp hjAcc).2
      have hδj := init_delta_pos j
      rw [init_delta_succ]
      linarith

private theorem init_grid_high_selected {K T h : ℕ} {D : Measure (ℝ × ℝ)} {ω : Samples K T}
    (hAcc : ∀ e : Act K,
      |muHat K T h ω e - muP D (pt K e.1)| ≤ (muP D (pt K e.1) + delta h) / 16)
    (e : Act K) (he : delta h ≤ muP D (pt K e.1)) :
    3 * delta h / 4 ≤ muHat K T h ω e := by
  have ha := (abs_sub_le_iff.mp (hAcc e)).2
  have hd := init_delta_pos h
  linarith

private theorem init_selected_grid_safe {K T h : ℕ} {D : Measure (ℝ × ℝ)} {ω : Samples K T}
    (hAcc : ∀ e : Act K,
      |muHat K T h ω e - muP D (pt K e.1)| ≤ (muP D (pt K e.1) + delta h) / 16)
    (e : Act K) (he : 3 * delta h / 4 ≤ muHat K T h ω e) :
    delta h / 2 ≤ muP D (pt K e.1) := by
  have ha := (abs_sub_le_iff.mp (hAcc e)).1
  have hd := init_delta_pos h
  linarith

private theorem init_no_trigger_grid_bound {K T : ℕ} (hK : 0 < K) {D : Measure (ℝ × ℝ)}
    {ω : Samples K T} (hf : firstTrigger K T ω = none) (eStar : Act K)
    (hAcc : ∀ j ∈ testedScales K T ω, ∀ e : Act K,
      |muHat K T j ω e - muP D (pt K e.1)| ≤ (muP D (pt K e.1) + delta j) / 16) :
    muP D (pt K eStar.1) < 4 / K := by
  let h := Nat.log 2 K
  have hh : h < numScales K := by unfold h numScales; omega
  have hnt : muHat K T h ω eStar < 3 * delta h / 2 := by
    by_contra hn
    exact init_firstTrigger_none.mp hf h hh ⟨eStar, le_of_not_gt hn⟩
  have ha := (abs_sub_le_iff.mp (hAcc h (init_none_mem_tested hf hh) eStar)).2
  have hd := init_delta_pos h
  have hml : muP D (pt K eStar.1) < 2 * delta h := by linarith
  have hlast := init_last_delta_lt hK
  dsimp [h] at hml
  calc
    _ < 2 * delta (Nat.log 2 K) := hml
    _ < 2 * (2 / (K : ℝ)) := by linarith
    _ = 4 / K := by ring

private theorem init_trigger_star_bounds {K T h : ℕ} (hK : 0 < K) {D : Measure (ℝ × ℝ)}
    {ω : Samples K T} (hf : firstTrigger K T ω = some h) (eStar : Act K)
    (heStar : IsGridMax K D eStar) (hunit : muP D (pt K eStar.1) ≤ 1)
    (hgridLower : muP D (pt K eStar.1) ≤ muStar D)
    (hgridUpper : muStar D ≤ muP D (pt K eStar.1) + 2 / K)
    (hAcc : ∀ j ∈ testedScales K T ω, ∀ e : Act K,
      |muHat K T j ω e - muP D (pt K e.1)| ≤ (muP D (pt K e.1) + delta j) / 16) :
    delta h ≤ muStar D ∧ muStar D < 6 * delta h := by
  obtain ⟨h1, h2⟩ := init_trigger_grid_bounds hf eStar heStar hunit hAcc
  have hδK := init_delta_ge_inv hK (init_firstTrigger_spec hf).1
  constructor
  · exact h1.trans hgridLower
  · have hround : 2 / (K : ℝ) ≤ 2 * delta h := by
      calc
        _ = 2 * (1 / (K : ℝ)) := by ring
        _ ≤ _ := by linarith
    linarith

private theorem init_region_safe {K T h : ℕ} (hK : 0 < K) {D : Measure (ℝ × ℝ)}
    (ω : Samples K T)
    (hAcc : ∀ e : Act K,
      |muHat K T h ω e - muP D (pt K e.1)| ≤ (muP D (pt K e.1) + delta h) / 16)
    (hc : Convex ℝ {x | x ∈ intT ∧ delta h / 2 ≤ muP D x}) :
    ∀ x ∈ region K T h ω, delta h / 2 ≤ muP D x ∧ muP D x ≤ Ptrade D x := by
  have hs : region K T h ω ⊆ {x | x ∈ intT ∧ delta h / 2 ≤ muP D x} := by
    apply convexHull_min _ hc
    rintro _ ⟨e, he, rfl⟩
    exact ⟨init_selected_mem_intT hK ω e he, init_selected_grid_safe hAcc e he⟩
  intro x hx
  exact ⟨(hs hx).2, mu_le_ptrade (intT_subset_unitSq (hs hx).1)⟩

private theorem init_region_contains_gridMax {K T h : ℕ} {D : Measure (ℝ × ℝ)}
    {ω : Samples K T} (hf : firstTrigger K T ω = some h) (eStar : Act K)
    (heStar : IsGridMax K D eStar) (hunit : muP D (pt K eStar.1) ≤ 1)
    (hAcc : ∀ j ∈ testedScales K T ω, ∀ e : Act K,
      |muHat K T j ω e - muP D (pt K e.1)| ≤ (muP D (pt K e.1) + delta j) / 16) :
    ∀ e : Act K, IsGridMax K D e → pt K e.1 ∈ region K T h ω := by
  have hδM := (init_trigger_grid_bounds hf eStar heStar hunit hAcc).1
  intro e he
  apply subset_convexHull
  apply Set.mem_image_of_mem
  apply init_grid_high_selected (hAcc h (init_trigger_mem_tested hf))
  exact hδM.trans (he eStar)

private theorem init_region_attains {K T h : ℕ} (hK : 0 < K) (E : Environment)
    (hE : UnitSupport E) (ω : Samples K T) (ht : Triggers K T h ω) :
    ∃ x ∈ region K T h ω, ∀ y ∈ region K T h ω, muP E.prior y ≤ muP E.prior x := by
  obtain ⟨hne, hcompact, _, hsub⟩ := init_region_geometry hK ω ht
  exact hcompact.exists_isMaxOn hne
    ((continuousOn_mu E hE).mono (hsub.trans intT_subset_unitSq))

end BilateralProfitMHR


set_option autoImplicit false

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade

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


private theorem init_grid_approx {K : ℕ} (hK : 1 ≤ K) (E : Environment) (hE : UnitSupport E)
    (eStar : Act K) (heStar : IsGridMax K E.prior eStar) :
    muStar E.prior ≤ muP E.prior (pt K eStar.1) + 2 / K := by
  letI := prior_isProbabilityMeasure E hE
  obtain ⟨a, ha, hmax⟩ := exists_muStar E hE
  obtain ⟨e, he, _⟩ := BilateralProfit.lemma_A_6 K hK a.1 a.2 ha.1.le ha.2.1.le ha.2.2.le
  have hi := integral_mono (init_integrable_profit E.prior a)
    ((init_integrable_profit E.prior (pt K e.1)).add (integrable_const (2 / (K : ℝ))))
    (fun v => he v.1 v.2)
  simp only [Pi.add_apply] at hi
  rw [integral_add (init_integrable_profit E.prior (pt K e.1)) (integrable_const _),
    init_integral_profit, init_integral_profit, integral_const] at hi
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hi
  rw [hmax] at hi
  linarith [heStar e]

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


set_option autoImplicit false

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem init_all_output_geometry {K T : ℕ} (hK : 0 < K)
    (ω : Samples K T) (h : ℕ) (R : Set (ℝ × ℝ)) (ho : initOut K T ω = some (h, R)) :
    R.Nonempty ∧ IsCompact R ∧ Convex ℝ R ∧ R ⊆ intT := by
  obtain ⟨hf, rfl⟩ := initOut_some ho
  exact init_region_geometry hK ω (init_firstTrigger_spec hf).2.1

private theorem init_good_results {K T : ℕ} (hK : 2 ≤ K) (hKT : K ≤ T)
    (E : Environment) (hE : UnitSupport E) (hM : IsMHR E)
    {ω : Samples K T} (hAcc : ∀ j ∈ testedScales K T ω, ∀ e : Act K,
      |muHat K T j ω e - muP E.prior (pt K e.1)| ≤ (muP E.prior (pt K e.1) + delta j) / 16) :
    (initOut K T ω = none → muStar E.prior < 6 / K) ∧
    ∀ (h : ℕ) (R : Set (ℝ × ℝ)), initOut K T ω = some (h, R) →
      (delta h ≤ muStar E.prior ∧ muStar E.prior < 6 * delta h) ∧
      (∀ x ∈ R, delta h / 2 ≤ muP E.prior x ∧ muP E.prior x ≤ Ptrade E.prior x) ∧
      (∀ e : Act K, IsGridMax K E.prior e → pt K e.1 ∈ R) ∧
      (∃ x ∈ R, (∀ y ∈ R, muP E.prior y ≤ muP E.prior x) ∧
        muStar E.prior - 2 / K ≤ muP E.prior x) := by
  letI := prior_isProbabilityMeasure E hE
  obtain ⟨eStar, heStar⟩ := init_grid_max_exists K E.prior
  have hKpos : 0 < K := by omega
  have hpt : pt K eStar.1 ∈ unitSq :=
    ⟨init_nat_div_mem_Icc hKpos (Nat.lt_succ_iff.mp eStar.1.1.isLt),
      init_nat_div_mem_Icc hKpos (Nat.lt_succ_iff.mp eStar.1.2.isLt)⟩
  have hunit := mu_le_one (D := E.prior) hpt
  have hgridLower := mu_le_muStar E hE hpt
  have hgridUpper := init_grid_approx (by omega : 1 ≤ K) E hE eStar heStar
  constructor
  · intro ho
    have hf := initOut_none.mp ho
    have hsmall := init_no_trigger_grid_bound hKpos hf eStar hAcc
    calc
      _ ≤ muP E.prior (pt K eStar.1) + 2 / K := hgridUpper
      _ < 4 / (K : ℝ) + 2 / K := by linarith
      _ = 6 / K := by ring
  · intro h R ho
    obtain ⟨hf, rfl⟩ := initOut_some ho
    have htrigger := (init_firstTrigger_spec hf).2.1
    have hbounds := init_trigger_star_bounds hKpos hf eStar heStar hunit
      hgridLower hgridUpper hAcc
    have hδ := init_delta_pos h
    have hsafe := init_region_safe hKpos ω (hAcc h (init_trigger_mem_tested hf))
      (profit_superlevel_convex E hE hM (by positivity : 0 < delta h / 2))
    have hgrid := init_region_contains_gridMax hf eStar heStar hunit hAcc
    obtain ⟨x, hx, hmax⟩ := init_region_attains hKpos E hE ω htrigger
    refine ⟨hbounds, hsafe, hgrid, x, hx, hmax, ?_⟩
    have hptmax := hmax (pt K eStar.1) (hgrid eStar heStar)
    linarith

end BilateralProfitMHR


set_option autoImplicit false

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem init_probe_unitSq {K : ℕ} (hK : 0 < K) {z : ℕ × ℕ} (hz : z ∈ Spairs K) :
    ((z.1 : ℝ) / K, (z.2 : ℝ) / K) ∈ unitSq := by
  obtain ⟨hij, hjK⟩ := Spairs_bounds hz
  exact ⟨init_nat_div_mem_Icc hK (hij.trans hjK), init_nat_div_mem_Icc hK hjK⟩

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

private noncomputable def initTotalRegret (K T : ℕ) (D : Measure (ℝ × ℝ)) (ω : Samples K T) : ℝ :=
  filterRegret K T D ω + if initOut K T ω = none then
    ((T - initRounds K T ω : ℕ) : ℝ) * muStar D else 0

private theorem init_totalRegret_le_horizon {K T : ℕ} (hK : 0 < K) (E : Environment)
    (hE : UnitSupport E) (ω : Samples K T) (hr : initRounds K T ω ≤ T) :
    initTotalRegret K T E.prior ω ≤ (T : ℝ) := by
  have hreg := init_filterRegret_le_rounds hK E ω
  have hstar := muStar_le_one E hE
  have hstar0 := (muStar_pos E hE).le
  have hrr : (initRounds K T ω : ℝ) ≤ T := by exact_mod_cast hr
  unfold initTotalRegret
  split_ifs
  · rw [Nat.cast_sub hr]
    nlinarith
  · simp only [add_zero]
    nlinarith

private theorem init_totalRegret_no_trigger {K T : ℕ} (hK : 0 < K) (E : Environment)
    {ω : Samples K T} (hr : initRounds K T ω ≤ T) (ho : initOut K T ω = none) :
    initTotalRegret K T E.prior ω ≤ (T : ℝ) * muStar E.prior := by
  have hreg := init_filterRegret_le_rounds hK E ω
  unfold initTotalRegret
  rw [if_pos ho, Nat.cast_sub hr]
  nlinarith

private theorem init_lintegral_good_event {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → ℝ) (G : Set Ω) (hm : MeasurableSet G)
    {T : ℕ} (hT : T ≠ 0) {B : ℝ} (hgood : ∀ ω ∈ G, f ω ≤ B)
    (hall : ∀ ω, f ω ≤ T) (hbad : P Gᶜ ≤ (T : ℝ≥0∞)⁻¹) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) ≤ ENNReal.ofReal B + 1 := by
  rw [← lintegral_add_compl (fun ω => ENNReal.ofReal (f ω)) hm]
  have hg : (∫⁻ ω in G, ENNReal.ofReal (f ω) ∂P) ≤ ENNReal.ofReal B := by
    calc
      _ ≤ ∫⁻ _ω in G, ENNReal.ofReal B ∂P := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hm] with ω hω
        exact ENNReal.ofReal_le_ofReal (hgood ω hω)
      _ = ENNReal.ofReal B * P G := by simp
      _ ≤ _ := mul_le_of_le_one_right (by positivity) prob_le_one
  have hb : (∫⁻ ω in Gᶜ, ENNReal.ofReal (f ω) ∂P) ≤ 1 := by
    calc
      _ ≤ ∫⁻ _ω in Gᶜ, (T : ℝ≥0∞) ∂P := by
        apply lintegral_mono
        intro ω
        simpa using ENNReal.ofReal_le_ofReal (hall ω)
      _ = (T : ℝ≥0∞) * P Gᶜ := by simp
      _ ≤ (T : ℝ≥0∞) * (T : ℝ≥0∞)⁻¹ := by gcongr
      _ = 1 := ENNReal.mul_inv_cancel (by exact_mod_cast hT) (by finiteness)
  exact add_le_add hg hb

private theorem init_filterRegret_le_total {K T : ℕ} (E : Environment) (hE : UnitSupport E)
    (ω : Samples K T) : filterRegret K T E.prior ω ≤ initTotalRegret K T E.prior ω := by
  unfold initTotalRegret
  split_ifs
  · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (T - initRounds K T ω)) (muStar_pos E hE).le]
  · simp

private theorem init_log_twoT_le_two_log {T : ℕ} (hT : 2 ≤ T) :
    Real.log (2 * T) ≤ 2 * Real.log T := by
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hTr
  rw [Real.log_mul (by norm_num) (by positivity)]
  linarith

private theorem init_sqrt_log_ge_half {T : ℕ} (hT : 2 ≤ T) :
    (1 / 2 : ℝ) ≤ Real.sqrt T * Real.log T := by
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hTr
  have hlog : (1 / 2 : ℝ) ≤ Real.log T := by linarith [Real.log_two_gt_d9]
  have hsqrt : 1 ≤ Real.sqrt (T : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith)
  nlinarith

private theorem init_trigger_rate {T : ℕ} (hK : 2 ≤ Kpar (1 / 1048576) T) :
    4718664 * (Kpar (1 / 1048576) T : ℝ) * Real.log (2 * T) ^ 2 ≤
      100000000 * Real.sqrt T * Real.log T := by
  have hT := init_Kpar_T_ge_two (c0 := 1 / 1048576) (by norm_num) (by norm_num) hK
  have hu := init_Kpar_real_upper (c0 := 1 / 1048576) (by norm_num) hT
  have hL := init_log_ge_one hT
  have hlog := init_log_twoT_le_two_log hT
  have hmul := (le_div_iff₀ (by linarith : 0 < Real.log (2 * T))).mp hu
  have hmulL := mul_le_mul_of_nonneg_right hmul (show 0 ≤ Real.log (2 * T) by linarith)
  have hlogS := mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg (T : ℝ))
  have hSL := init_sqrt_log_ge_half hT
  nlinarith

private theorem init_no_trigger_rate {T : ℕ} (hK : 2 ≤ Kpar (1 / 1048576) T) :
    6 * (T : ℝ) / Kpar (1 / 1048576) T ≤
      100000000 * Real.sqrt T * Real.log T := by
  have hT := init_Kpar_T_ge_two (c0 := 1 / 1048576) (by norm_num) (by norm_num) hK
  have hL := init_log_ge_one hT
  have hlog := init_log_twoT_le_two_log hT
  have hl := init_Kpar_real_lower hK
  have hKr : (0 : ℝ) < Kpar (1 / 1048576) T := by exact_mod_cast (by omega : 0 < Kpar (1 / 1048576) T)
  have hmul := (div_le_iff₀ (by linarith : 0 < Real.log (2 * T))).mp hl
  have hmulS := mul_le_mul_of_nonneg_left hmul (Real.sqrt_nonneg (T : ℝ))
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) T)
  have hSL := init_sqrt_log_ge_half hT
  calc
    _ ≤ 12582912 * Real.sqrt T * Real.log (2 * T) := by
      apply (div_le_iff₀ hKr).2
      nlinarith
    _ ≤ 25165824 * Real.sqrt T * Real.log T := by nlinarith [mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg (T : ℝ))]
    _ ≤ _ := by nlinarith

end BilateralProfitMHR


set_option autoImplicit false

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem init_totalRegret_good_rate {T : ℕ} (hK : 2 ≤ Kpar (1 / 1048576) T)
    (E : Environment) (hE : UnitSupport E) (hM : IsMHR E)
    {ω : Samples (Kpar (1 / 1048576) T) T}
    (hAcc : ∀ j ∈ testedScales (Kpar (1 / 1048576) T) T ω, ∀ e : Act (Kpar (1 / 1048576) T),
      |muHat (Kpar (1 / 1048576) T) T j ω e - muP E.prior (pt (Kpar (1 / 1048576) T) e.1)| ≤
        (muP E.prior (pt (Kpar (1 / 1048576) T) e.1) + delta j) / 16) :
    initTotalRegret (Kpar (1 / 1048576) T) T E.prior ω ≤
      100000000 * Real.sqrt T * Real.log T := by
  let K := Kpar (1 / 1048576) T
  have hT := init_Kpar_T_ge_two (c0 := 1 / 1048576) (by norm_num) (by norm_num) hK
  have hKT := init_Kpar_le_T (c0 := 1 / 1048576) (by norm_num) (by norm_num) hT
  have hgood := init_good_results hK hKT E hE hM hAcc
  have hr := init_Kpar_rounds hK ω
  cases ho : initOut K T ω with
  | none =>
    have hstar := hgood.1 ho
    have htot := init_totalRegret_no_trigger (by omega : 0 < K) E hr ho
    apply htot.trans
    calc
      _ ≤ (T : ℝ) * (6 / K) := by gcongr
      _ = 6 * (T : ℝ) / K := by ring
      _ ≤ _ := init_no_trigger_rate hK
  | some z =>
    rcases z with ⟨h, R⟩
    have hstar := (hgood.2 h R ho).1.2.le
    have hf := (initOut_some ho).1
    have hreg := init_filterRegret_trigger_bound hK hKT E hf hstar
    unfold initTotalRegret
    rw [if_neg (by rw [ho]; simp), add_zero]
    exact hreg.trans (init_trigger_rate hK)

private theorem init_expected_regret_bounds {T : ℕ} (hK : 2 ≤ Kpar (1 / 1048576) T)
    (E : Environment) (hE : UnitSupport E) (hM : IsMHR E) :
    (∫⁻ ω, ENNReal.ofReal (filterRegret (Kpar (1 / 1048576) T) T E.prior ω)
        ∂(initLaw (Kpar (1 / 1048576) T) T E.prior)) ≤
      ENNReal.ofReal (100000002 * Real.sqrt T * Real.log T) ∧
    (∫⁻ ω, ENNReal.ofReal (initTotalRegret (Kpar (1 / 1048576) T) T E.prior ω)
        ∂(initLaw (Kpar (1 / 1048576) T) T E.prior)) ≤
      ENNReal.ofReal (100000002 * Real.sqrt T * Real.log T) := by
  letI := prior_isProbabilityMeasure E hE
  let K := Kpar (1 / 1048576) T
  letI : IsProbabilityMeasure (initLaw K T E.prior) := by unfold initLaw; infer_instance
  have hT := init_Kpar_T_ge_two (c0 := 1 / 1048576) (by norm_num) (by norm_num) hK
  have hKT := init_Kpar_le_T (c0 := 1 / 1048576) (by norm_num) (by norm_num) hT
  obtain ⟨G, hm, hprob, hacc⟩ := BilateralProfitMHR.proposition_5_4 T K hK hKT E hE
  have hb : initLaw K T E.prior Gᶜ ≤ (T : ℝ≥0∞)⁻¹ := by
    rw [measure_compl hm (measure_ne_top _ _)]
    simp only [measure_univ]
    exact tsub_le_iff_right.mpr ((tsub_le_iff_right.mp hprob).trans_eq (add_comm _ _))
  have hall := fun ω => init_totalRegret_le_horizon (by omega : 0 < K) E hE ω (init_Kpar_rounds hK ω)
  have hgood := fun ω hω => init_totalRegret_good_rate hK E hE hM (ω := ω) (hacc ω hω)
  have hint := init_lintegral_good_event (initLaw K T E.prior) (initTotalRegret K T E.prior)
    G hm (by omega : T ≠ 0) hgood hall hb
  have hSL := init_sqrt_log_ge_half hT
  have hB : 0 ≤ 100000000 * Real.sqrt T * Real.log T := by nlinarith
  have hrate : 100000000 * Real.sqrt T * Real.log T + 1 ≤
      100000002 * Real.sqrt T * Real.log T := by nlinarith
  have hfinal : (∫⁻ ω, ENNReal.ofReal (initTotalRegret K T E.prior ω)
      ∂(initLaw K T E.prior)) ≤ ENNReal.ofReal (100000002 * Real.sqrt T * Real.log T) := by
    apply hint.trans
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hB (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hrate
  refine ⟨?_, hfinal⟩
  apply le_trans (lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (init_filterRegret_le_total E hE ω))) hfinal

end BilateralProfitMHR

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal


private theorem lemma53_main :
    (∀ T K : ℕ, 2 ≤ K → K ≤ T →
      (∀ (ω : Samples K T) (h : ℕ) (R : Set (ℝ × ℝ)), initOut K T ω = some (h, R) →
          R.Nonempty ∧ IsCompact R ∧ Convex ℝ R ∧ R ⊆ intT) ∧
      ∀ E : Environment, UnitSupport E → IsMHR E →
        ∃ G : Set (Samples K T), MeasurableSet G ∧ 1 - (T : ℝ≥0∞)⁻¹ ≤ initLaw K T E.prior G ∧
          ∀ ω ∈ G,
            (initOut K T ω = none → muStar E.prior < 6 / K) ∧
            ∀ (h : ℕ) (R : Set (ℝ × ℝ)), initOut K T ω = some (h, R) →
              (delta h ≤ muStar E.prior ∧ muStar E.prior < 6 * delta h) ∧
              (∀ x ∈ R, delta h / 2 ≤ muP E.prior x ∧ muP E.prior x ≤ Ptrade E.prior x) ∧
              (∀ e : Act K, IsGridMax K E.prior e → pt K e.1 ∈ R) ∧
              (∃ x ∈ R, (∀ y ∈ R, muP E.prior y ≤ muP E.prior x) ∧
                muStar E.prior - 2 / K ≤ muP E.prior x)) ∧
    (∃ c0 C : ℝ, 0 < c0 ∧ c0 ≤ 1 / 2 ∧ ∀ T : ℕ, 2 ≤ Kpar c0 T →
      (∀ ω : Samples (Kpar c0 T) T, initRounds (Kpar c0 T) T ω ≤ T) ∧
      ∀ E : Environment, UnitSupport E → IsMHR E →
        ∫⁻ ω, ENNReal.ofReal (filterRegret (Kpar c0 T) T E.prior ω)
            ∂(initLaw (Kpar c0 T) T E.prior) ≤
          ENNReal.ofReal (C * Real.sqrt T * Real.log T) ∧
        ∫⁻ ω, ENNReal.ofReal (filterRegret (Kpar c0 T) T E.prior ω +
              if initOut (Kpar c0 T) T ω = none then
                ((T - initRounds (Kpar c0 T) T ω : ℕ) : ℝ) * muStar E.prior
              else 0)
            ∂(initLaw (Kpar c0 T) T E.prior) ≤
          ENNReal.ofReal (C * Real.sqrt T * Real.log T)) := by
  constructor
  · intro T K hK hKT
    refine ⟨?_, ?_⟩
    · intro ω h R ho
      exact init_all_output_geometry (by omega) ω h R ho
    · intro E hE hM
      obtain ⟨G, hm, hprob, hacc⟩ := BilateralProfitMHR.proposition_5_4 T K hK hKT E hE
      refine ⟨G, hm, hprob, ?_⟩
      intro ω hω
      exact init_good_results hK hKT E hE hM (hacc ω hω)
  · refine ⟨1 / 1048576, 100000002, by norm_num, by norm_num, ?_⟩
    intro T hK
    refine ⟨init_Kpar_rounds hK, ?_⟩
    intro E hE hM
    simpa only [initTotalRegret] using init_expected_regret_bounds hK E hE hM


end BilateralProfitMHR
open BilateralProfitMHR MeasureTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal
theorem solution :
    (∀ T K : ℕ, 2 ≤ K → K ≤ T →
      (∀ (ω : Samples K T) (h : ℕ) (R : Set (ℝ × ℝ)), initOut K T ω = some (h, R) →
          R.Nonempty ∧ IsCompact R ∧ Convex ℝ R ∧ R ⊆ intT) ∧
      ∀ E : Environment, UnitSupport E → IsMHR E →
        ∃ G : Set (Samples K T), MeasurableSet G ∧ 1 - (T : ℝ≥0∞)⁻¹ ≤ initLaw K T E.prior G ∧
          ∀ ω ∈ G,
            (initOut K T ω = none → muStar E.prior < 6 / K) ∧
            ∀ (h : ℕ) (R : Set (ℝ × ℝ)), initOut K T ω = some (h, R) →
              (delta h ≤ muStar E.prior ∧ muStar E.prior < 6 * delta h) ∧
              (∀ x ∈ R, delta h / 2 ≤ muP E.prior x ∧ muP E.prior x ≤ Ptrade E.prior x) ∧
              (∀ e : Act K, IsGridMax K E.prior e → pt K e.1 ∈ R) ∧
              (∃ x ∈ R, (∀ y ∈ R, muP E.prior y ≤ muP E.prior x) ∧
                muStar E.prior - 2 / K ≤ muP E.prior x)) ∧
    (∃ c0 C : ℝ, 0 < c0 ∧ c0 ≤ 1 / 2 ∧ ∀ T : ℕ, 2 ≤ Kpar c0 T →
      (∀ ω : Samples (Kpar c0 T) T, initRounds (Kpar c0 T) T ω ≤ T) ∧
      ∀ E : Environment, UnitSupport E → IsMHR E →
        ∫⁻ ω, ENNReal.ofReal (filterRegret (Kpar c0 T) T E.prior ω)
            ∂(initLaw (Kpar c0 T) T E.prior) ≤
          ENNReal.ofReal (C * Real.sqrt T * Real.log T) ∧
        ∫⁻ ω, ENNReal.ofReal (filterRegret (Kpar c0 T) T E.prior ω +
              if initOut (Kpar c0 T) T ω = none then
                ((T - initRounds (Kpar c0 T) T ω : ℕ) : ℝ) * muStar E.prior
              else 0)
            ∂(initLaw (Kpar c0 T) T E.prior) ≤
          ENNReal.ofReal (C * Real.sqrt T * Real.log T)) := BilateralProfitMHR.lemma53_main

