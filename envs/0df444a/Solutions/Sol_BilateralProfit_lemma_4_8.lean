-- Prove2me | solution 1 for BilateralProfit.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T14:47:09.323827+00:00
-- url     : https://prove2.me/submissions/a9d3f7db-c311-4079-9f62-1227962b44ef

import Mathlib
import Definitions.Def_BilateralProfit_SellerTree
import Theorems.Thm_BilateralProfit_eq_17
import Definitions.Def_BilateralProfit_QueryRoutine
import Theorems.Thm_BilateralProfit_claim_4_10

namespace BilateralProfit.SellerFacts

open MeasureTheory

theorem descend_bounds (n lo len i : ℕ) (hi : lo ≤ i ∧ i < lo + len) :
    ∀ I ∈ descend n lo len i,
      I.1 ≤ i ∧ i < I.1 + I.2 ∧ lo ≤ I.1 ∧ I.1 + I.2 ≤ lo + len := by
  induction n generalizing lo len with
  | zero =>
      intro I hI
      simp only [descend, List.mem_singleton] at hI
      subst I
      exact ⟨hi.1, hi.2, le_rfl, le_rfl⟩
  | succ n ih =>
      intro I hI
      simp only [descend] at hI
      split_ifs at hI with hlen hside
      · simp only [List.mem_singleton] at hI
        subst I
        exact ⟨hi.1, hi.2, le_rfl, le_rfl⟩
      · rcases List.mem_cons.mp hI with hI | hI
        · subst I
          exact ⟨hi.1, hi.2, le_rfl, le_rfl⟩
        · obtain ⟨h1, h2, h3, h4⟩ := ih lo (len / 2) ⟨hi.1, hside⟩ I hI
          exact ⟨h1, h2, h3, by omega⟩
      · rcases List.mem_cons.mp hI with hI | hI
        · subst I
          exact ⟨hi.1, hi.2, le_rfl, le_rfl⟩
        · have hchild : lo + len / 2 ≤ i ∧ i < lo + len / 2 + (len - len / 2) := by omega
          obtain ⟨h1, h2, h3, h4⟩ := ih (lo + len / 2) (len - len / 2) hchild I hI
          exact ⟨h1, h2, by omega, by omega⟩

theorem path_bounds {K i : ℕ} (hi : i ≤ K) {I : ℕ × ℕ} (hI : I ∈ sellerPath K i) :
    I.1 ≤ i ∧ i < I.1 + I.2 ∧ I.1 + I.2 ≤ K + 1 := by
  obtain ⟨h1, h2, _, h4⟩ := descend_bounds (K + 1) 0 (K + 1) i (by omega) I hI
  exact ⟨h1, h2, by simpa using h4⟩

theorem descend_nonempty (n lo len i : ℕ) : descend n lo len i ≠ [] := by
  cases n with
  | zero => simp [descend]
  | succ n =>
      simp only [descend]
      split_ifs <;> simp

theorem descend_last (n lo len i : ℕ) (hi : lo ≤ i ∧ i < lo + len)
    (hfuel : len ≤ n + 1) : (descend n lo len i).getLast? = some (i, 1) := by
  induction n generalizing lo len with
  | zero =>
      have hlen : len = 1 := by omega
      have hlo : lo = i := by omega
      subst len lo
      simp [descend]
  | succ n ih =>
      simp only [descend]
      split_ifs with hlen hside
      · have hlen' : len = 1 := by omega
        have hlo : lo = i := by omega
        subst len lo
        simp
      · rw [List.getLast?_cons]
        rw [ih lo (len / 2) ⟨hi.1, hside⟩ (by omega)]
        rfl
      · rw [List.getLast?_cons]
        rw [ih (lo + len / 2) (len - len / 2) (by omega) (by omega)]
        rfl

theorem sellerPath_last {K i : ℕ} (hi : i ≤ K) :
    (sellerPath K i).getLast? = some (i, 1) :=
  descend_last (K + 1) 0 (K + 1) i (by omega) (by omega)

theorem scan_mem {S : Set ℕ} (l : List ℕ) (f : ℕ → ℝ) (b : ℕ)
    (hb : b ∈ S) (hl : ∀ i ∈ l, i ∈ S) :
    l.foldl (fun b i => if f b < f i then i else b) b ∈ S := by
  induction l generalizing b with
  | nil => exact hb
  | cons i l ih =>
      simp only [List.foldl_cons]
      split_ifs with h
      · exact ih i (hl i (by simp)) (fun j hj => hl j (by simp [hj]))
      · exact ih b hb (fun j hj => hl j (by simp [hj]))

theorem scan_ge_initial (l : List ℕ) (f : ℕ → ℝ) (b : ℕ) :
    f b ≤ f (l.foldl (fun b i => if f b < f i then i else b) b) := by
  induction l generalizing b with
  | nil => exact le_rfl
  | cons i l ih =>
      simp only [List.foldl_cons]
      split_ifs with h
      · exact h.le.trans (ih i)
      · exact ih b

theorem scan_ge_member (l : List ℕ) (f : ℕ → ℝ) (b i : ℕ) (hi : i ∈ l) :
    f i ≤ f (l.foldl (fun b i => if f b < f i then i else b) b) := by
  induction l generalizing b with
  | nil => simp at hi
  | cons j l ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hi with rfl | hi
      · split_ifs with h
        · exact scan_ge_initial l f i
        · exact (le_of_not_gt h).trans (scan_ge_initial l f b)
      · split_ifs <;> exact ih _ hi

theorem scan_le (l : List ℕ) (f : ℕ → ℝ) (b q : ℕ) (hb : b ≤ q)
    (hl : ∀ i ∈ l, q < i → f i ≤ f b) :
    l.foldl (fun b i => if f b < f i then i else b) b ≤ q := by
  induction l generalizing b with
  | nil => exact hb
  | cons i l ih =>
      simp only [List.foldl_cons]
      split_ifs with h
      · have hi : i ≤ q := by
          by_contra hnot
          exact (not_lt_of_ge (hl i (by simp) (lt_of_not_ge hnot))) h
        apply ih i hi
        intro j hj hjq
        exact (hl j (by simp [hj]) hjq).trans h.le
      · exact ih b hb (fun j hj hjq => hl j (by simp [hj]) hjq)

theorem range_head (lo len : ℕ) (hlen : 0 < len) : (List.range' lo len).headD 0 = lo := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen)
  simp [List.range'_succ]

theorem rep_mem {K : ℕ} (ρ : Grid K × Act K → ℝ) (lo len s : ℕ) (hlen : 0 < len) :
    lo ≤ rep ρ lo len s ∧ rep ρ lo len s < lo + len := by
  unfold rep argmaxFirst
  rw [range_head lo len hlen]
  apply scan_mem (S := {i | lo ≤ i ∧ i < lo + len})
  · exact ⟨le_rfl, by omega⟩
  · intro i hi
    obtain ⟨j, hj, hij⟩ := List.mem_range'.mp hi
    simp only [one_mul] at hij
    exact ⟨by omega, by omega⟩

theorem rep_max {K : ℕ} (ρ : Grid K × Act K → ℝ) (lo len s i : ℕ)
    (hi : lo ≤ i ∧ i < lo + len) :
    ((s : ℝ) / K - (i : ℝ) / K) * P0 ρ ((i : ℝ) / K, (s : ℝ) / K) ≤
      ((s : ℝ) / K - (rep ρ lo len s : ℝ) / K) *
        P0 ρ ((rep ρ lo len s : ℝ) / K, (s : ℝ) / K) := by
  unfold rep argmaxFirst
  apply scan_ge_member _ _ _ i
  apply List.mem_range'.mpr
  exact ⟨i - lo, by omega, by omega⟩

theorem blockStart_le {K : ℕ} (ρ : Grid K × Act K → ℝ) (ε : ℝ) (lo len j : ℕ) :
    blockStart ρ ε lo len j ≤ j := by
  induction j with
  | zero => simp [blockStart]
  | succ j ih =>
      simp only [blockStart]
      split_ifs <;> omega

theorem nuMeas_finite (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (nuMeas μ) := by
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    constructor
    simp [Measure.restrict_apply, Real.volume_Icc]
  unfold nuMeas
  infer_instance

theorem block_mass {K : ℕ} (ρ : Grid K × Act K → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (lo len j : ℕ) :
    (nuMeas (margLaw ρ) (Set.Ioc ((lo : ℝ) / K) (((lo + len - 1 : ℕ) : ℝ) / K) ×ˢ
      Set.Ico ((blockStart ρ ε lo len j : ℝ) / K) ((j : ℝ) / K))).toReal ≤ ε := by
  cases j with
  | zero => simpa [blockStart] using hε
  | succ j =>
      simp only [blockStart]
      split_ifs with h
      · exact h
      · simpa using hε

theorem profit_seller_beyond (v : ℝ × ℝ) (l r d : ℝ) (hlr : l ≤ r) (hdr : d ≤ r) :
    profit v (r, d) ≤ profit v (l, d) := by
  classical
  by_cases hr : Trades v (r, d)
  · by_cases hl : Trades v (l, d)
    · simp only [profit, tradeBit, if_pos hr, if_pos hl, mul_one]
      linarith
    · simp only [profit, tradeBit, if_pos hr, if_neg hl, mul_one, mul_zero]
      linarith
  · have hl : ¬Trades v (l, d) := by
      intro hl
      exact hr ⟨hl.1.trans hlr, hl.2⟩
    simp [profit, tradeBit, hr, hl]

theorem valProfitPt_seller_beyond {K : ℕ} (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (l r d : ℝ) (hlr : l ≤ r) (hdr : d ≤ r) :
    valProfitPt ρ (r, d) ≤ valProfitPt ρ (l, d) := by
  unfold valProfitPt
  exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
    (profit_seller_beyond _ _ _ _ hlr hdr) (hρ.1 y))

theorem spread_P0_eq {K : ℕ} (ρ : Grid K × Act K → ℝ) (p q : ℝ) :
    (q - p) * P0 ρ (p, q) = valProfitPt ρ (p, q) := by
  unfold P0 valProfitPt profit
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem rep_feasible {K : ℕ} (_hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (lo len s q : ℕ) (hlen : 0 < len) (hlo : lo ≤ q) (hs : s ≤ q) :
    rep ρ lo len s ≤ q := by
  unfold rep argmaxFirst
  rw [range_head lo len hlen]
  apply scan_le _ _ lo q hlo
  intro i _ hi
  rw [spread_P0_eq, spread_P0_eq]
  apply valProfitPt_seller_beyond ρ hρ
  · exact div_le_div_of_nonneg_right (by exact_mod_cast (show lo ≤ i by omega))
      (Nat.cast_nonneg K)
  · exact div_le_div_of_nonneg_right (by exact_mod_cast (show s ≤ i by omega))
      (Nat.cast_nonneg K)

theorem Ptrade_antitone_buyer (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (p : ℝ) :
    Antitone (fun q : ℝ => Ptrade μ (p, q)) := by
  intro q q' hq
  apply ENNReal.toReal_mono (by finiteness)
  apply measure_mono
  intro v hv
  exact ⟨hv.1, hq.trans hv.2⟩

theorem Ptrade_seller_split (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (l r q : ℝ) (hlr : l ≤ r) :
    Ptrade μ (r, q) - Ptrade μ (l, q) = μ.real (Set.Ioc l r ×ˢ Set.Ici q) := by
  change μ.real (Set.Iic r ×ˢ Set.Ici q) - μ.real (Set.Iic l ×ˢ Set.Ici q) = _
  have hset : Set.Iic r ×ˢ Set.Ici q =
      (Set.Iic l ×ˢ Set.Ici q) ∪ (Set.Ioc l r ×ˢ Set.Ici q) := by
    ext v
    simp only [Set.mem_prod, Set.mem_Iic, Set.mem_Ici, Set.mem_union, Set.mem_Ioc]
    constructor
    · rintro ⟨hv, hb⟩
      by_cases h : v.1 ≤ l
      · exact Or.inl ⟨h, hb⟩
      · exact Or.inr ⟨⟨lt_of_not_ge h, hv⟩, hb⟩
    · rintro (⟨hv, hb⟩ | ⟨⟨_, hv⟩, hb⟩)
      · exact ⟨hv.trans hlr, hb⟩
      · exact ⟨hv, hb⟩
  rw [hset, measureReal_union]
  · ring
  · apply Set.disjoint_left.mpr
    intro v hv hw
    exact (not_lt_of_ge hv.1) hw.1.1
  · exact measurableSet_Ioc.prod measurableSet_Ici

theorem Ptrade_difference_monotone (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (p r : ℝ) :
    Monotone (fun q : ℝ => Ptrade μ (p, q) - Ptrade μ (r, q)) ∨
      Antitone (fun q : ℝ => Ptrade μ (p, q) - Ptrade μ (r, q)) := by
  by_cases h : r ≤ p
  · right
    intro q q' hq
    dsimp only
    rw [Ptrade_seller_split μ r p q' h, Ptrade_seller_split μ r p q h]
    apply ENNReal.toReal_mono (by finiteness)
    exact measure_mono (fun v hv => ⟨hv.1, hq.trans hv.2⟩)
  · left
    have hpr : p ≤ r := le_of_not_ge h
    intro q q' hq
    have h1 := Ptrade_seller_split μ p r q hpr
    have h2 := Ptrade_seller_split μ p r q' hpr
    have hle : μ.real (Set.Ioc p r ×ˢ Set.Ici q') ≤
        μ.real (Set.Ioc p r ×ˢ Set.Ici q) := by
      apply ENNReal.toReal_mono (by finiteness)
      exact measure_mono (fun v hv => ⟨hv.1, hq.trans hv.2⟩)
    linarith

end BilateralProfit.SellerFacts

namespace BilateralProfit.TradeFacts

open MeasureTheory

variable {K : ℕ}

theorem coord_mem (hK : 0 < K) (i : Fin (K + 1)) :
    (i : ℝ) / K ∈ Set.Icc (0 : ℝ) 1 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hi : (i : ℕ) ≤ K := by omega
  constructor
  · positivity
  · apply (div_le_one hKr).mpr
    exact_mod_cast hi

theorem pt_mem (hK : 0 < K) (x : Grid K) :
    pt K x ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
  ⟨coord_mem hK x.1, coord_mem hK x.2⟩

theorem spread_mem (hK : 0 < K) (a : Act K) :
    (pt K a.1).2 - (pt K a.1).1 ∈ Set.Icc (0 : ℝ) 1 := by
  have hleft := coord_mem hK a.1.1
  have hright := coord_mem hK a.1.2
  have horder : ((a.1.1 : ℕ) : ℝ) ≤ ((a.1.2 : ℕ) : ℝ) := by exact_mod_cast a.2
  have hdiv := div_le_div_of_nonneg_right horder (by positivity : (0 : ℝ) ≤ K)
  change ((a.1.2 : ℕ) : ℝ) / K - ((a.1.1 : ℕ) : ℝ) / K ∈ Set.Icc 0 1
  exact ⟨sub_nonneg.mpr hdiv, by linarith [hleft.1, hright.2]⟩

theorem tradeBit_nonneg (v a : ℝ × ℝ) : 0 ≤ tradeBit v a := by
  unfold tradeBit
  split_ifs <;> norm_num

theorem tradeBit_le_one (v a : ℝ × ℝ) : tradeBit v a ≤ 1 := by
  unfold tradeBit
  split_ifs <;> norm_num

theorem measurableSet_trades (a : ℝ × ℝ) : MeasurableSet {v | Trades v a} := by
  change MeasurableSet (Set.Iic a.1 ×ˢ Set.Ici a.2)
  exact measurableSet_Iic.prod measurableSet_Ici

theorem Ptrade_nonneg (μ : Measure (ℝ × ℝ)) (a : ℝ × ℝ) : 0 ≤ Ptrade μ a :=
  ENNReal.toReal_nonneg

theorem Ptrade_le_one (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (a : ℝ × ℝ) :
    Ptrade μ a ≤ 1 := by
  change μ.real {v | Trades v a} ≤ 1
  exact measureReal_le_one

theorem P0_nonneg (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : ℝ × ℝ) :
    0 ≤ P0 ρ a := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hρ.1 x) (tradeBit_nonneg _ _))

theorem P0_le_one (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (a : ℝ × ℝ) :
    P0 ρ a ≤ 1 := by
  calc
    P0 ρ a ≤ ∑ x, ρ x := Finset.sum_le_sum (fun x _ => by
      simpa using mul_le_mul_of_nonneg_left (tradeBit_le_one (pt K x.1) a) (hρ.1 x))
    _ = 1 := hρ.2

theorem valProfitPt_eq_spread_mul_P0 (ρ : Grid K × Act K → ℝ) (a : ℝ × ℝ) :
    valProfitPt ρ a = (a.2 - a.1) * P0 ρ a := by
  unfold valProfitPt profit P0
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem margLaw_apply (ρ : Grid K × Act K → ℝ) (s : Set (ℝ × ℝ)) :
    margLaw ρ s = ∑ x, ENNReal.ofReal (ρ x) * Measure.dirac (pt K x.1) s := by
  classical
  simp [margLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]

theorem margLaw_univ (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    margLaw ρ Set.univ = 1 := by
  rw [margLaw_apply]
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hρ.1 x), hρ.2]
  exact ENNReal.ofReal_one

theorem margLaw_isValLaw (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    IsValLaw (margLaw ρ) := by
  refine ⟨⟨margLaw_univ ρ hρ⟩, ?_⟩
  rw [margLaw_apply]
  apply Finset.sum_eq_zero
  intro x _
  have hx : pt K x.1 ∉ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ :=
    fun h => h (pt_mem hK x.1)
  rw [Measure.dirac_apply, Set.indicator_of_notMem hx, mul_zero]

theorem Ptrade_margLaw_eq_P0 (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : ℝ × ℝ) : Ptrade (margLaw ρ) a = P0 ρ a := by
  classical
  unfold Ptrade
  rw [margLaw_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro x _
    by_cases h : Trades (pt K x.1) a
    · simp [tradeBit, h, ENNReal.toReal_ofReal (hρ.1 x)]
    · simp [tradeBit, h]
  · intro x _
    finiteness

theorem muP_margLaw_eq_valProfitPt (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : ℝ × ℝ) : muP (margLaw ρ) a = valProfitPt ρ a := by
  rw [muP, Ptrade_margLaw_eq_P0 ρ hρ, valProfitPt_eq_spread_mul_P0]

theorem valProfit_nonneg (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : Act K) : 0 ≤ valProfit ρ a := by
  rw [valProfit, valProfitPt_eq_spread_mul_P0]
  exact mul_nonneg (spread_mem hK a).1 (P0_nonneg ρ hρ _)

theorem valProfit_le_one (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : Act K) : valProfit ρ a ≤ 1 := by
  rw [valProfit, valProfitPt_eq_spread_mul_P0]
  have hs := spread_mem hK a
  have hp0 := P0_nonneg ρ hρ (pt K a.1)
  have hp1 := P0_le_one ρ hρ (pt K a.1)
  calc
    _ ≤ 1 * P0 ρ (pt K a.1) := mul_le_mul_of_nonneg_right hs.2 hp0
    _ ≤ 1 := by simpa using hp1

theorem valProfit_le_optVal (ρ : Grid K × Act K → ℝ) (a : Act K) :
    valProfit ρ a ≤ optVal ρ :=
  le_ciSup (Finite.bddAbove_range (valProfit ρ)) a

theorem optVal_nonneg (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    0 ≤ optVal ρ :=
  (valProfit_nonneg hK ρ hρ default).trans (valProfit_le_optVal ρ default)

theorem optVal_le_one (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) :
    optVal ρ ≤ 1 :=
  ciSup_le (valProfit_le_one hK ρ hρ)

theorem gapStar_nonneg (ρ : Grid K × Act K → ℝ) (a : Act K) :
    0 ≤ gapStar ρ a :=
  sub_nonneg.mpr (valProfit_le_optVal ρ a)

theorem gapStar_le_one (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (a : Act K) : gapStar ρ a ≤ 1 := by
  change optVal ρ - valProfit ρ a ≤ 1
  linarith [optVal_le_one hK ρ hρ, valProfit_nonneg hK ρ hρ a]

end BilateralProfit.TradeFacts

namespace BilateralProfit.SellerFacts

open MeasureTheory

theorem nat_coord_mem {K : ℕ} (hK : 0 < K) (i : ℕ) (hi : i ≤ K) :
    (i : ℝ) / K ∈ Set.Icc (0 : ℝ) 1 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  exact ⟨by positivity, (div_le_one hKr).mpr (by exact_mod_cast hi)⟩

theorem node_variation {K : ℕ} (hK : 0 < K) (ρ : Grid K × Act K → ℝ)
    (hρ : IsDist ρ) (ε : ℝ) (hε : 0 ≤ ε) (lo len p r q : ℕ)
    (hp : lo ≤ p ∧ p < lo + len) (hr : lo ≤ r ∧ r < lo + len)
    (hnode : lo + len ≤ K + 1) (hq : q ≤ K) (hpr : p ≤ r) :
    |(valProfitPt ρ ((r : ℝ) / K, (q : ℝ) / K) -
        valProfitPt ρ ((p : ℝ) / K, (q : ℝ) / K)) -
      (valProfitPt ρ ((r : ℝ) / K, (blockStart ρ ε lo len q : ℝ) / K) -
        valProfitPt ρ ((p : ℝ) / K, (blockStart ρ ε lo len q : ℝ) / K))| ≤ ε := by
  have hμ := TradeFacts.margLaw_isValLaw hK ρ hρ
  letI : IsProbabilityMeasure (margLaw ρ) := hμ.1
  letI : IsFiniteMeasure (nuMeas (margLaw ρ)) := nuMeas_finite (margLaw ρ)
  have hs := blockStart_le ρ ε lo len q
  have hbound := (eq_17 (margLaw ρ) hμ).1
    ((p : ℝ) / K) ((r : ℝ) / K) ((blockStart ρ ε lo len q : ℝ) / K) ((q : ℝ) / K)
    (nat_coord_mem hK p (by omega)) (nat_coord_mem hK r (by omega))
    (nat_coord_mem hK _ (by omega)) (nat_coord_mem hK q hq)
    (div_le_div_of_nonneg_right (by exact_mod_cast hpr) (Nat.cast_nonneg K))
    (div_le_div_of_nonneg_right (by exact_mod_cast hs) (Nat.cast_nonneg K))
  simp only [TradeFacts.muP_margLaw_eq_valProfitPt ρ hρ] at hbound
  apply hbound.trans
  apply (ENNReal.toReal_mono (by finiteness) (measure_mono ?_)).trans
    (block_mass ρ ε hε lo len q)
  intro v hv
  refine ⟨⟨?_, ?_⟩, hv.2⟩
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast hp.1) (Nat.cast_nonneg K)).trans_lt hv.1.1
  · exact hv.1.2.trans (div_le_div_of_nonneg_right
      (by exact_mod_cast (show r ≤ lo + len - 1 by omega)) (Nat.cast_nonneg K))

theorem rep_approx {K : ℕ} (hK : 0 < K) (ρ : Grid K × Act K → ℝ)
    (hρ : IsDist ρ) (ε : ℝ) (hε : 0 ≤ ε) (lo len p q : ℕ)
    (hp : lo ≤ p ∧ p < lo + len) (hnode : lo + len ≤ K + 1) (hq : q ≤ K) :
    valProfitPt ρ ((p : ℝ) / K, (q : ℝ) / K) ≤
      valProfitPt ρ ((rep ρ lo len (blockStart ρ ε lo len q) : ℝ) / K, (q : ℝ) / K) + ε := by
  let s := blockStart ρ ε lo len q
  let r := rep ρ lo len s
  have hr : lo ≤ r ∧ r < lo + len := rep_mem ρ lo len s (by omega)
  have hmax := rep_max ρ lo len s p hp
  rw [spread_P0_eq, spread_P0_eq] at hmax
  by_cases hpr : p ≤ r
  · have hvar := node_variation hK ρ hρ ε hε lo len p r q hp hr hnode hq hpr
    have habs := (abs_le.mp hvar).1
    change valProfitPt ρ ((p : ℝ) / K, (q : ℝ) / K) ≤
      valProfitPt ρ ((r : ℝ) / K, (q : ℝ) / K) + ε
    dsimp only [s] at hmax
    linarith
  · have hvar := node_variation hK ρ hρ ε hε lo len r p q hr hp hnode hq (le_of_not_ge hpr)
    have habs := (abs_le.mp hvar).2
    change valProfitPt ρ ((p : ℝ) / K, (q : ℝ) / K) ≤
      valProfitPt ρ ((r : ℝ) / K, (q : ℝ) / K) + ε
    dsimp only [s] at hmax
    linarith

theorem path_representative {K : ℕ} (hK : 0 < K) (ρ : Grid K × Act K → ℝ)
    (hρ : IsDist ρ) (ε : ℝ) (hε : 0 ≤ ε) (a : Act K) (ha : gapStar ρ a ≤ ε)
    (I : ℕ × ℕ) (hI : I ∈ sellerPath K a.1.1) :
    repAt ρ ε I a.1.2 ≤ (a.1.2 : ℕ) ∧
      gapStarPt ρ ((repAt ρ ε I a.1.2 : ℝ) / K, ((a.1.2 : ℕ) : ℝ) / K) ≤ 2 * ε := by
  have hpath := path_bounds (i := (a.1.1 : ℕ)) (by omega) hI
  have hlen : 0 < I.2 := by omega
  refine ⟨?_, ?_⟩
  · exact rep_feasible hK ρ hρ I.1 I.2 _ _ hlen
      (hpath.1.trans (by exact_mod_cast a.2)) (blockStart_le ρ ε I.1 I.2 _)
  · have happ := rep_approx hK ρ hρ ε hε I.1 I.2 a.1.1 a.1.2
      ⟨hpath.1, hpath.2.1⟩ hpath.2.2 (by omega)
    change optVal ρ - valProfitPt ρ _ ≤ 2 * ε
    change optVal ρ - valProfitPt ρ (((a.1.1 : ℕ) : ℝ) / K, ((a.1.2 : ℕ) : ℝ) / K) ≤ ε at ha
    change valProfitPt ρ (((a.1.1 : ℕ) : ℝ) / K, ((a.1.2 : ℕ) : ℝ) / K) ≤
      valProfitPt ρ ((repAt ρ ε I a.1.2 : ℝ) / K, ((a.1.2 : ℕ) : ℝ) / K) + ε at happ
    linarith

end BilateralProfit.SellerFacts

open MeasureTheory BilateralProfit

theorem BilateralProfit.cert_claim_4_9 (K : ℕ) (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (ε : ℝ)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (a : Act K) (ha : gapStar ρ a ≤ ε) :
    (∀ I ∈ sellerPath K a.1.1, repAt ρ ε I a.1.2 ≤ (a.1.2 : ℕ) ∧
      gapStarPt ρ ((repAt ρ ε I a.1.2 : ℝ) / K, ((a.1.2 : ℕ) : ℝ) / K) ≤ 2 * ε) ∧
    ∀ μ : Measure (ℝ × ℝ), IsValLaw μ →
      (∀ (m : ℕ) (hm : m + 1 < (sellerPath K a.1.1).length),
        MonotoneOn
            (fun q : ℕ => Ptrade μ ((repAt ρ ε ((sellerPath K a.1.1)[m + 1]'hm) a.1.2 : ℝ) / K,
                (q : ℝ) / K) -
              Ptrade μ ((repAt ρ ε ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)) a.1.2 : ℝ) / K,
                (q : ℝ) / K))
            {q : ℕ | q ≤ K ∧
              blockStart ρ ε ((sellerPath K a.1.1)[m + 1]'hm).1
                ((sellerPath K a.1.1)[m + 1]'hm).2 q =
              blockStart ρ ε ((sellerPath K a.1.1)[m + 1]'hm).1
                ((sellerPath K a.1.1)[m + 1]'hm).2 a.1.2 ∧
              blockStart ρ ε ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).1
                ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).2 q =
              blockStart ρ ε ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).1
                ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).2 a.1.2} ∨
        AntitoneOn
            (fun q : ℕ => Ptrade μ ((repAt ρ ε ((sellerPath K a.1.1)[m + 1]'hm) a.1.2 : ℝ) / K,
                (q : ℝ) / K) -
              Ptrade μ ((repAt ρ ε ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)) a.1.2 : ℝ) / K,
                (q : ℝ) / K))
            {q : ℕ | q ≤ K ∧
              blockStart ρ ε ((sellerPath K a.1.1)[m + 1]'hm).1
                ((sellerPath K a.1.1)[m + 1]'hm).2 q =
              blockStart ρ ε ((sellerPath K a.1.1)[m + 1]'hm).1
                ((sellerPath K a.1.1)[m + 1]'hm).2 a.1.2 ∧
              blockStart ρ ε ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).1
                ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).2 q =
              blockStart ρ ε ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).1
                ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)).2 a.1.2}) ∧
      (MonotoneOn (fun q : ℕ => Ptrade μ ((repAt ρ ε (0, K + 1) a.1.2 : ℝ) / K, (q : ℝ) / K))
          {q : ℕ | q ≤ K ∧ blockStart ρ ε 0 (K + 1) q = blockStart ρ ε 0 (K + 1) a.1.2} ∨
        AntitoneOn (fun q : ℕ => Ptrade μ ((repAt ρ ε (0, K + 1) a.1.2 : ℝ) / K, (q : ℝ) / K))
          {q : ℕ | q ≤ K ∧ blockStart ρ ε 0 (K + 1) q = blockStart ρ ε 0 (K + 1) a.1.2})  := by
  classical
  refine ⟨?_, ?_⟩
  · intro I hI
    exact SellerFacts.path_representative hK ρ hρ ε hε.le a ha I hI
  · intro μ hμ
    letI : IsProbabilityMeasure μ := hμ.1
    refine ⟨?_, ?_⟩
    · intro m hm
      rcases SellerFacts.Ptrade_difference_monotone μ
        ((repAt ρ ε ((sellerPath K a.1.1)[m + 1]'hm) a.1.2 : ℝ) / K)
        ((repAt ρ ε ((sellerPath K a.1.1)[m]'(Nat.lt_of_succ_lt hm)) a.1.2 : ℝ) / K)
        with hmono | hanti
      · left
        intro q _ q' _ hqq
        exact hmono (div_le_div_of_nonneg_right (by exact_mod_cast hqq) (Nat.cast_nonneg K))
      · right
        intro q _ q' _ hqq
        exact hanti (div_le_div_of_nonneg_right (by exact_mod_cast hqq) (Nat.cast_nonneg K))
    · right
      intro q _ q' _ hqq
      exact SellerFacts.Ptrade_antitone_buyer μ _
        (div_le_div_of_nonneg_right (by exact_mod_cast hqq) (Nat.cast_nonneg K))

namespace BilateralProfit.Estimation

open MeasureTheory

variable {K : ℕ}

abbrev Node := ℕ × ℕ

def left (I : Node) : Node := (I.1, I.2 / 2)

def right (I : Node) : Node := (I.1 + I.2 / 2, I.2 - I.2 / 2)

/-- The nodes of the finite seller tree, in preorder. -/
def nodes : ℕ → Node → List Node
  | 0, I => [I]
  | n + 1, I =>
      if I.2 ≤ 1 then [I]
      else I :: (nodes n (left I) ++ nodes n (right I))

/-- The directed parent-to-child edges of the finite seller tree. -/
def edges : ℕ → Node → List (Node × Node)
  | 0, _ => []
  | n + 1, I =>
      if I.2 ≤ 1 then []
      else (I, left I) :: (I, right I) ::
        (edges n (left I) ++ edges n (right I))

lemma halves_pos (I : Node) (hI : 1 < I.2) :
    0 < (left I).2 ∧ 0 < (right I).2 := by
  dsimp [left, right]
  omega

lemma halves_le_pow (I : Node) (d : ℕ) (hI : I.2 ≤ 2 ^ (d + 1)) :
    (left I).2 ≤ 2 ^ d ∧ (right I).2 ≤ 2 ^ d := by
  dsimp [left, right]
  rw [pow_succ] at hI
  omega

lemma nodes_length_le (n : ℕ) (I : Node) (hI : 0 < I.2) :
    (nodes n I).length ≤ 2 * I.2 - 1 := by
  induction n generalizing I with
  | zero => simp only [nodes, List.length_singleton]; omega
  | succ n ih =>
      simp only [nodes]
      split_ifs with h
      · simp only [List.length_singleton]; omega
      · have hp := halves_pos I (by omega)
        have hl := ih (left I) hp.1
        have hr := ih (right I) hp.2
        simp only [List.length_cons, List.length_append]
        dsimp [left, right]
        dsimp [left, right] at hl hr
        omega

lemma descend_stable (d n m lo len i : ℕ) (hlen : len ≤ 2 ^ d) :
    descend (d + n) lo len i = descend (d + m) lo len i := by
  induction d generalizing lo len i with
  | zero =>
      have hlen' : len ≤ 1 := by simpa using hlen
      cases n <;> cases m <;> simp [descend, hlen']
  | succ d ih =>
      rw [Nat.succ_add, Nat.succ_add]
      simp only [descend]
      split_ifs with hsmall hbranch
      · rfl
      · have hhalves := halves_le_pow (lo, len) d hlen
        simpa [left] using congrArg (List.cons (lo, len))
          (ih lo (len / 2) i hhalves.1)
      · have hhalves := halves_le_pow (lo, len) d hlen
        simpa [right] using congrArg (List.cons (lo, len))
          (ih (lo + len / 2) (len - len / 2) i hhalves.2)

lemma nodes_stable (d n m : ℕ) (I : Node) (hI : I.2 ≤ 2 ^ d) :
    nodes (d + n) I = nodes (d + m) I := by
  induction d generalizing I with
  | zero =>
      have hI' : I.2 ≤ 1 := by simpa using hI
      cases n <;> cases m <;> simp [nodes, hI']
  | succ d ih =>
      rw [Nat.succ_add, Nat.succ_add]
      simp only [nodes]
      split_ifs with hsmall
      · rfl
      · have hhalves := halves_le_pow I d hI
        rw [ih (left I) hhalves.1, ih (right I) hhalves.2]

lemma edges_stable (d n m : ℕ) (I : Node) (hI : I.2 ≤ 2 ^ d) :
    edges (d + n) I = edges (d + m) I := by
  induction d generalizing I with
  | zero =>
      have hI' : I.2 ≤ 1 := by simpa using hI
      cases n <;> cases m <;> simp [edges, hI']
  | succ d ih =>
      rw [Nat.succ_add, Nat.succ_add]
      simp only [edges]
      split_ifs with hsmall
      · rfl
      · have hhalves := halves_le_pow I d hI
        rw [ih (left I) hhalves.1, ih (right I) hhalves.2]

/-- Additive mass over all tree nodes is bounded by depth times the root mass.
The child mass inequality allows gaps between consecutive grid coordinates. -/
lemma sum_nodes_le (d : ℕ) (I : Node) (w : Node → ℝ)
    (hw0 : ∀ J, 0 ≤ w J)
    (hw : ∀ J, 1 < J.2 → w (left J) + w (right J) ≤ w J)
    (hI : I.2 ≤ 2 ^ d) :
    ((nodes d I).map w).sum ≤ ((d : ℝ) + 1) * w I := by
  induction d generalizing I with
  | zero => simp [nodes]
  | succ d ih =>
      simp only [nodes]
      split_ifs with hsmall
      · simp only [List.map_singleton, List.sum_singleton]
        have := hw0 I
        have : (1 : ℝ) ≤ (↑(d + 1) : ℝ) + 1 := by
          have : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
          push_cast
          linarith
        nlinarith
      · have hhalves := halves_le_pow I d hI
        have hl := ih (left I) hhalves.1
        have hr := ih (right I) hhalves.2
        have hp := hw I (by omega)
        simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
        have hd : 0 ≤ (d : ℝ) + 1 := by positivity
        have hm := mul_le_mul_of_nonneg_left hp hd
        push_cast
        nlinarith

/-- The total parent weight over directed edges pays each internal node twice. -/
lemma sum_edges_parent_le (n : ℕ) (I : Node) (w : Node → ℝ)
    (hw : ∀ J, 0 ≤ w J) :
    ((edges n I).map (fun e => w e.1)).sum ≤
      2 * ((nodes n I).map w).sum := by
  induction n generalizing I with
  | zero => simp [edges, nodes, hw I]
  | succ n ih =>
      simp only [edges, nodes]
      split_ifs with hsmall
      · simp [hw I]
      · have hl := ih (left I)
        have hr := ih (right I)
        simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
        linarith

lemma blockStart_monotone (ρ : Grid K × Act K → ℝ) (ε : ℝ) (lo len : ℕ) :
    Monotone (blockStart ρ ε lo len) := by
  apply monotone_nat_of_le_succ
  intro j
  simp only [blockStart]
  split_ifs
  · exact le_rfl
  · exact (SellerFacts.blockStart_le ρ ε lo len j).trans (Nat.le_succ j)

lemma blockStart_idem (ρ : Grid K × Act K → ℝ) (ε : ℝ) (lo len j : ℕ) :
    blockStart ρ ε lo len (blockStart ρ ε lo len j) = blockStart ρ ε lo len j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      by_cases h : (nuMeas (margLaw ρ) (Set.Ioc ((lo : ℝ) / K)
          (((lo + len - 1 : ℕ) : ℝ) / K) ×ˢ
          Set.Ico ((blockStart ρ ε lo len j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K))).toReal ≤ ε
      · have heq : blockStart ρ ε lo len (j + 1) = blockStart ρ ε lo len j := by
          simpa only [blockStart, if_pos h]
        rw [heq]
        exact ih
      · have heq : blockStart ρ ε lo len (j + 1) = j + 1 := by
          simpa only [blockStart, if_neg h]
        rw [heq]
        exact heq

lemma blockStart_between (ρ : Grid K × Act K → ℝ) (ε : ℝ) (lo len y t : ℕ)
    (ht : blockStart ρ ε lo len y ≤ t) (hty : t ≤ y) :
    blockStart ρ ε lo len t = blockStart ρ ε lo len y := by
  apply le_antisymm ((blockStart_monotone ρ ε lo len) hty)
  simpa only [blockStart_idem] using (blockStart_monotone ρ ε lo len) ht

/-- The block boundaries among buyer coordinates through `j`. -/
noncomputable def startsThrough (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) (j : ℕ) :
    Finset ℕ := (Finset.range (j + 1)).filter (fun q => blockStart ρ ε I.1 I.2 q = q)

lemma startsThrough_zero (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) :
    startsThrough ρ ε I 0 = {0} := by
  ext q
  simp only [startsThrough, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · intro h; omega
  · rintro rfl; exact ⟨by omega, rfl⟩

lemma startsThrough_succ (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) (j : ℕ) :
    startsThrough ρ ε I (j + 1) =
      if blockStart ρ ε I.1 I.2 (j + 1) = j + 1 then
        insert (j + 1) (startsThrough ρ ε I j) else startsThrough ρ ε I j := by
  classical
  unfold startsThrough
  rw [Finset.range_add_one, Finset.filter_insert]

lemma not_mem_startsThrough_succ (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) (j : ℕ) :
    j + 1 ∉ startsThrough ρ ε I j := by
  simp [startsThrough]

lemma start_mem (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) (j : ℕ) :
    blockStart ρ ε I.1 I.2 j ∈ startsThrough ρ ε I j := by
  simp only [startsThrough, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (SellerFacts.blockStart_le ρ ε I.1 I.2 j),
    blockStart_idem ρ ε I.1 I.2 j⟩

lemma intersection_start (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I J : Node) (y : ℕ) :
    let t := max (blockStart ρ ε I.1 I.2 y) (blockStart ρ ε J.1 J.2 y)
    t ≤ y ∧ blockStart ρ ε I.1 I.2 t = blockStart ρ ε I.1 I.2 y ∧
      blockStart ρ ε J.1 J.2 t = blockStart ρ ε J.1 J.2 y ∧
      (t ∈ startsThrough ρ ε I y ∨ t ∈ startsThrough ρ ε J y) := by
  dsimp only
  have hi := SellerFacts.blockStart_le ρ ε I.1 I.2 y
  have hj := SellerFacts.blockStart_le ρ ε J.1 J.2 y
  have ht : max (blockStart ρ ε I.1 I.2 y) (blockStart ρ ε J.1 J.2 y) ≤ y := max_le hi hj
  have hI := blockStart_between ρ ε I.1 I.2 y _ (le_max_left _ _) ht
  have hJ := blockStart_between ρ ε J.1 J.2 y _ (le_max_right _ _) ht
  refine ⟨ht, hI, hJ, ?_⟩
  by_cases h : blockStart ρ ε I.1 I.2 y ≤ blockStart ρ ε J.1 J.2 y
  · right
    simp only [startsThrough, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le ht, hJ.trans (max_eq_right h).symm⟩
  · left
    simp only [startsThrough, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le ht, hI.trans (max_eq_left (le_of_not_ge h)).symm⟩

lemma rectangle_mass_add (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (S : Set ℝ) (hS : MeasurableSet S) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    μ.real (S ×ˢ Set.Ico a c) =
      μ.real (S ×ˢ Set.Ico a b) + μ.real (S ×ˢ Set.Ico b c) := by
  rw [← Set.Ico_union_Ico_eq_Ico hab hbc, Set.prod_union]
  apply measureReal_union
  · apply Set.disjoint_left.mpr
    intro z hz hz'
    exact (not_lt_of_ge hz'.2.1) hz.2.2
  · exact hS.prod measurableSet_Ico
  all_goals finiteness

lemma block_count_potential (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (ε : ℝ)
    (I : Node) (j : ℕ) [IsFiniteMeasure (nuMeas (margLaw ρ))] :
    ((startsThrough ρ ε I j).card : ℝ) * ε ≤ ε +
      (nuMeas (margLaw ρ)).real
        (Set.Ioc ((I.1 : ℝ) / K) (((I.1 + I.2 - 1 : ℕ) : ℝ) / K) ×ˢ
          Set.Ico 0 ((blockStart ρ ε I.1 I.2 j : ℝ) / K)) := by
  classical
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  let S := Set.Ioc ((I.1 : ℝ) / K) (((I.1 + I.2 - 1 : ℕ) : ℝ) / K)
  let μ := nuMeas (margLaw ρ)
  change ((startsThrough ρ ε I j).card : ℝ) * ε ≤
    ε + μ.real (S ×ˢ Set.Ico 0 ((blockStart ρ ε I.1 I.2 j : ℝ) / K))
  induction j with
  | zero => simp [startsThrough_zero, blockStart]
  | succ j ih =>
      let s := blockStart ρ ε I.1 I.2 j
      by_cases h : μ.real (S ×ˢ Set.Ico ((s : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) ≤ ε
      · have hnext : blockStart ρ ε I.1 I.2 (j + 1) = s := by
          change (nuMeas (margLaw ρ) (Set.Ioc ((I.1 : ℝ) / K)
            (((I.1 + I.2 - 1 : ℕ) : ℝ) / K) ×ˢ
            Set.Ico ((blockStart ρ ε I.1 I.2 j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K))).toReal ≤ ε at h
          simp only [blockStart, if_pos h]
          rfl
        have hneq : blockStart ρ ε I.1 I.2 (j + 1) ≠ j + 1 := by
          rw [hnext]
          have := SellerFacts.blockStart_le ρ ε I.1 I.2 j
          dsimp [s]
          omega
        rw [startsThrough_succ, if_neg hneq, hnext]
        exact ih
      · have hnext : blockStart ρ ε I.1 I.2 (j + 1) = j + 1 := by
          change ¬(nuMeas (margLaw ρ) (Set.Ioc ((I.1 : ℝ) / K)
            (((I.1 + I.2 - 1 : ℕ) : ℝ) / K) ×ˢ
            Set.Ico ((blockStart ρ ε I.1 I.2 j : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K))).toReal ≤ ε at h
          simp only [blockStart, if_neg h]
        rw [startsThrough_succ, if_pos hnext, Finset.card_insert_of_notMem
          (not_mem_startsThrough_succ ρ ε I j), hnext]
        have hs0 : (0 : ℝ) ≤ (s : ℝ) / K := div_nonneg (Nat.cast_nonneg _) hKr.le
        have hsj : (s : ℝ) / K ≤ ((j + 1 : ℕ) : ℝ) / K := by
          apply div_le_div_of_nonneg_right _ hKr.le
          exact_mod_cast (SellerFacts.blockStart_le ρ ε I.1 I.2 j).trans (Nat.le_succ j)
        rw [rectangle_mass_add μ S measurableSet_Ioc 0 _ _ hs0 hsj]
        push_cast
        have hsplit : ε < μ.real (S ×ˢ Set.Ico ((s : ℝ) / K) (((j + 1 : ℕ) : ℝ) / K)) :=
          lt_of_not_ge h
        push_cast at hsplit
        change ((startsThrough ρ ε I j).card : ℝ) * ε ≤
          ε + μ.real (S ×ˢ Set.Ico 0 ((s : ℝ) / K)) at ih
        linarith

lemma block_count_le (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (ε : ℝ) (hε : 0 < ε)
    (I : Node) (j : ℕ) [IsFiniteMeasure (nuMeas (margLaw ρ))] :
    ((startsThrough ρ ε I j).card : ℝ) ≤ 1 +
      (nuMeas (margLaw ρ)).real
        (Set.Ioc ((I.1 : ℝ) / K) (((I.1 + I.2 - 1 : ℕ) : ℝ) / K) ×ˢ Set.univ) / ε := by
  have h := block_count_potential hK ρ ε I j
  have hmass : (nuMeas (margLaw ρ)).real
        (Set.Ioc ((I.1 : ℝ) / K) (((I.1 + I.2 - 1 : ℕ) : ℝ) / K) ×ˢ
          Set.Ico 0 ((blockStart ρ ε I.1 I.2 j : ℝ) / K)) ≤
      (nuMeas (margLaw ρ)).real
        (Set.Ioc ((I.1 : ℝ) / K) (((I.1 + I.2 - 1 : ℕ) : ℝ) / K) ×ˢ Set.univ) := by
    apply ENNReal.toReal_mono (by finiteness)
    exact measure_mono (fun z hz => ⟨hz.1, Set.mem_univ _⟩)
  have hr := (le_div_iff₀ hε).mpr (h.trans (add_le_add (le_refl ε) hmass))
  calc
    _ ≤ _ := hr
    _ = _ := by rw [add_div, div_self hε.ne']

def strip (K : ℕ) (I : Node) : Set ℝ :=
  Set.Ioc ((I.1 : ℝ) / K) (((I.1 + I.2 - 1 : ℕ) : ℝ) / K)

def hull (K : ℕ) (I : Node) : Set ℝ :=
  Set.Icc ((I.1 : ℝ) / K) (((I.1 + I.2 - 1 : ℕ) : ℝ) / K)

lemma child_endpoints (I : Node) (hI : 1 < I.2) :
    I.1 ≤ (left I).1 ∧ (left I).1 + (left I).2 - 1 < (right I).1 ∧
      (right I).1 + (right I).2 - 1 = I.1 + I.2 - 1 := by
  dsimp [left, right]
  omega

lemma strip_children (K : ℕ) (I : Node) (hI : 1 < I.2) :
    strip K (left I) ⊆ strip K I ∧ strip K (right I) ⊆ strip K I ∧
      Disjoint (strip K (left I)) (strip K (right I)) := by
  have hp := halves_pos I hI
  have he := child_endpoints I hI
  have hcoord : ∀ a b : ℕ, a ≤ b → (a : ℝ) / K ≤ (b : ℝ) / K := by
    intro a b hab
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (Nat.cast_nonneg K)
  have hlmax : (left I).1 + (left I).2 - 1 ≤ I.1 + I.2 - 1 := by
    dsimp [left]; omega
  have hrmin : I.1 ≤ (right I).1 := by dsimp [right]; omega
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(hcoord _ _ he.1).trans_lt hx.1, hx.2.trans (hcoord _ _ hlmax)⟩
  · intro x hx
    exact ⟨(hcoord _ _ hrmin).trans_lt hx.1, by simpa [strip, he.2.2] using hx.2⟩
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hle := hcoord _ _ he.2.1.le
    exact (not_lt_of_ge (hx.2.trans hle)) hy.1

lemma hull_children (hK : 0 < K) (I : Node) (hI : 1 < I.2) :
    hull K (left I) ⊆ hull K I ∧ hull K (right I) ⊆ hull K I ∧
      Disjoint (hull K (left I)) (hull K (right I)) := by
  have hp := halves_pos I hI
  have he := child_endpoints I hI
  have hcoord : ∀ a b : ℕ, a ≤ b → (a : ℝ) / K ≤ (b : ℝ) / K := by
    intro a b hab
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (Nat.cast_nonneg K)
  have hlmax : (left I).1 + (left I).2 - 1 ≤ I.1 + I.2 - 1 := by
    dsimp [left]; omega
  have hrmin : I.1 ≤ (right I).1 := by dsimp [right]; omega
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(hcoord _ _ he.1).trans hx.1, hx.2.trans (hcoord _ _ hlmax)⟩
  · intro x hx
    exact ⟨(hcoord _ _ hrmin).trans hx.1, by simpa [hull, he.2.2] using hx.2⟩
  · apply Set.disjoint_left.mpr
    intro x hx hy
    have hlt : (((left I).1 + (left I).2 - 1 : ℕ) : ℝ) / K < ((right I).1 : ℝ) / K :=
      div_lt_div_of_pos_right (by exact_mod_cast he.2.1) (Nat.cast_pos.mpr hK)
    exact (not_lt_of_ge hy.1) (hx.2.trans_lt hlt)

lemma interval_mass_children (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (S : Node → Set ℝ) (hS : ∀ I, MeasurableSet (S I)) (I : Node)
    (hsub : S (left I) ⊆ S I ∧ S (right I) ⊆ S I ∧
      Disjoint (S (left I)) (S (right I))) :
    μ.real (S (left I) ×ˢ Set.univ) + μ.real (S (right I) ×ˢ Set.univ) ≤
      μ.real (S I ×ˢ Set.univ) := by
  rw [← measureReal_union]
  · apply ENNReal.toReal_mono (by finiteness)
    apply measure_mono
    rintro z (hz | hz)
    · exact ⟨hsub.1 hz.1, hz.2⟩
    · exact ⟨hsub.2.1 hz.1, hz.2⟩
  · apply Set.disjoint_left.mpr
    intro z hz hz'
    exact Set.disjoint_left.mp hsub.2.2 hz.1 hz'.1
  · exact (hS _).prod MeasurableSet.univ
  all_goals finiteness

lemma strip_mass_children (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (K : ℕ) (I : Node) (hI : 1 < I.2) :
    μ.real (strip K (left I) ×ˢ Set.univ) + μ.real (strip K (right I) ×ˢ Set.univ) ≤
      μ.real (strip K I ×ˢ Set.univ) :=
  interval_mass_children μ (strip K) (fun _ => measurableSet_Ioc) I (strip_children K I hI)

lemma hull_mass_children (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hK : 0 < K) (I : Node) (hI : 1 < I.2) :
    μ.real (hull K (left I) ×ˢ Set.univ) + μ.real (hull K (right I) ×ˢ Set.univ) ≤
      μ.real (hull K I ×ˢ Set.univ) :=
  interval_mass_children μ (hull K) (fun _ => measurableSet_Icc) I (hull_children hK I hI)

lemma sum_node_strip_mass_le (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (K d : ℕ) (I : Node) (hI : I.2 ≤ 2 ^ d) :
    ((nodes d I).map (fun J => μ.real (strip K J ×ˢ Set.univ))).sum ≤
      ((d : ℝ) + 1) * μ.real (strip K I ×ˢ Set.univ) :=
  sum_nodes_le d I _ (fun _ => ENNReal.toReal_nonneg)
    (fun J hJ => strip_mass_children μ K J hJ) hI

lemma sum_node_hull_mass_le (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hK : 0 < K) (d : ℕ) (I : Node) (hI : I.2 ≤ 2 ^ d) :
    ((nodes d I).map (fun J => μ.real (hull K J ×ˢ Set.univ))).sum ≤
      ((d : ℝ) + 1) * μ.real (hull K I ×ˢ Set.univ) :=
  sum_nodes_le d I _ (fun _ => ENNReal.toReal_nonneg)
    (fun J hJ => hull_mass_children μ hK J hJ) hI

lemma root_add_sum_edges_child (n : ℕ) (I : Node) (w : Node → ℝ) :
    w I + ((edges n I).map (fun e => w e.2)).sum = ((nodes n I).map w).sum := by
  induction n generalizing I with
  | zero => simp [edges, nodes]
  | succ n ih =>
      simp only [edges, nodes]
      split_ifs with hsmall
      · simp
      · have hl := ih (left I)
        have hr := ih (right I)
        simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
        linarith

lemma root_add_sum_edges_le_three_nodes (n : ℕ) (I : Node) (w : Node → ℝ)
    (hw : ∀ J, 0 ≤ w J) :
    w I + ((edges n I).map (fun e => w e.1 + w e.2)).sum ≤
      3 * ((nodes n I).map w).sum := by
  have hp := sum_edges_parent_le n I w hw
  have hc := root_add_sum_edges_child n I w
  rw [List.sum_map_add]
  linarith

lemma sum_block_counts_le (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (ε : ℝ) (hε : 0 < ε)
    [IsFiniteMeasure (nuMeas (margLaw ρ))] (is : List Node) :
    (is.map (fun I => ((startsThrough ρ ε I K).card : ℝ))).sum ≤
      (is.length : ℝ) + (is.map (fun I => (nuMeas (margLaw ρ)).real
        (strip K I ×ˢ Set.univ))).sum / ε := by
  induction is with
  | nil => simp
  | cons I is ih =>
      have hI := block_count_le hK ρ ε hε I K
      change ((startsThrough ρ ε I K).card : ℝ) ≤
        1 + (nuMeas (margLaw ρ)).real (strip K I ×ˢ Set.univ) / ε at hI
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [add_div]
      linarith

lemma sum_tree_block_counts_le (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (ε : ℝ) (hε : 0 < ε)
    [IsFiniteMeasure (nuMeas (margLaw ρ))] (d : ℕ) (I : Node) (hpos : 0 < I.2)
    (hI : I.2 ≤ 2 ^ d) :
    ((nodes d I).map (fun J => ((startsThrough ρ ε J K).card : ℝ))).sum ≤
      2 * I.2 + (((d : ℝ) + 1) * (nuMeas (margLaw ρ)).real
        (strip K I ×ˢ Set.univ)) / ε := by
  have h := sum_block_counts_le hK ρ ε hε (nodes d I)
  have hlen : ((nodes d I).length : ℝ) ≤ 2 * I.2 := by
    exact_mod_cast (nodes_length_le d I hpos).trans (Nat.sub_le _ _)
  have hm := sum_node_strip_mass_le (nuMeas (margLaw ρ)) K d I hI
  exact h.trans (add_le_add hlen (div_le_div_of_nonneg_right hm hε.le))

inductive Piece where
  | root : Node → ℕ → Piece
  | edge : Node → Node → ℕ → Piece
  deriving DecidableEq

noncomputable def rootPieces (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) : List Piece :=
  (startsThrough ρ ε I K).toList.map (Piece.root I)

noncomputable def edgePieces (ρ : Grid K × Act K → ℝ) (ε : ℝ) (e : Node × Node) : List Piece :=
  ((startsThrough ρ ε e.1 K) ∪ (startsThrough ρ ε e.2 K)).toList.map (Piece.edge e.1 e.2)

noncomputable def pieces (ρ : Grid K × Act K → ℝ) (ε : ℝ) (d : ℕ) (I : Node) : List Piece :=
  rootPieces ρ ε I ++ (edges d I).flatMap (edgePieces ρ ε)

lemma rootPieces_length (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) :
    (rootPieces ρ ε I).length = (startsThrough ρ ε I K).card := by
  simp [rootPieces]

lemma edgePieces_length_le (ρ : Grid K × Act K → ℝ) (ε : ℝ) (e : Node × Node) :
    (edgePieces ρ ε e).length ≤
      (startsThrough ρ ε e.1 K).card + (startsThrough ρ ε e.2 K).card := by
  simpa [edgePieces] using Finset.card_union_le (startsThrough ρ ε e.1 K) (startsThrough ρ ε e.2 K)

lemma flatMap_edgePieces_length_le (ρ : Grid K × Act K → ℝ) (ε : ℝ) (es : List (Node × Node)) :
    ((es.flatMap (edgePieces ρ ε)).length : ℝ) ≤
      (es.map (fun e => ((startsThrough ρ ε e.1 K).card : ℝ) +
        ((startsThrough ρ ε e.2 K).card : ℝ))).sum := by
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.flatMap_cons, List.length_append, Nat.cast_add, List.map_cons, List.sum_cons]
      have he : ((edgePieces ρ ε e).length : ℝ) ≤
          ((startsThrough ρ ε e.1 K).card : ℝ) + ((startsThrough ρ ε e.2 K).card : ℝ) := by
        exact_mod_cast edgePieces_length_le ρ ε e
      exact add_le_add he ih

lemma pieces_length_le (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (ε : ℝ) (hε : 0 < ε)
    [IsFiniteMeasure (nuMeas (margLaw ρ))] (d : ℕ) (I : Node) (hpos : 0 < I.2)
    (hI : I.2 ≤ 2 ^ d) :
    ((pieces ρ ε d I).length : ℝ) ≤
      3 * (2 * I.2 + (((d : ℝ) + 1) * (nuMeas (margLaw ρ)).real
        (strip K I ×ˢ Set.univ)) / ε) := by
  have h := root_add_sum_edges_le_three_nodes d I
    (fun J => ((startsThrough ρ ε J K).card : ℝ)) (fun _ => Nat.cast_nonneg _)
  have hb := sum_tree_block_counts_le hK ρ ε hε d I hpos hI
  have he := flatMap_edgePieces_length_le ρ ε (edges d I)
  simp only [pieces, List.length_append, Nat.cast_add, rootPieces_length]
  linarith

noncomputable def cell (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I J : Node) (s : ℕ) : Finset ℕ :=
  (Finset.range (K + 1)).filter (fun q =>
    blockStart ρ ε I.1 I.2 q = blockStart ρ ε I.1 I.2 s ∧
    blockStart ρ ε J.1 J.2 q = blockStart ρ ε J.1 J.2 s)

noncomputable def cellEnd (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I J : Node) (s : ℕ) : ℕ :=
  (cell ρ ε I J s).sup id

lemma cell_mem (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I J : Node) (s q : ℕ) :
    q ∈ cell ρ ε I J s ↔ q ≤ K ∧
      blockStart ρ ε I.1 I.2 q = blockStart ρ ε I.1 I.2 s ∧
      blockStart ρ ε J.1 J.2 q = blockStart ρ ε J.1 J.2 s := by
  simp only [cell, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

lemma self_mem_cell (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I J : Node) (s : ℕ) (hs : s ≤ K) :
    s ∈ cell ρ ε I J s := (cell_mem ρ ε I J s s).mpr ⟨hs, rfl, rfl⟩

lemma cellEnd_mem (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I J : Node) (s : ℕ) (hs : s ≤ K) :
    cellEnd ρ ε I J s ∈ cell ρ ε I J s := by
  have hne : (cell ρ ε I J s).Nonempty := ⟨s, self_mem_cell ρ ε I J s hs⟩
  have h := Finset.sup_mem_of_nonempty (f := id) hne
  rcases h with ⟨x, hx, heq⟩
  change x = cellEnd ρ ε I J s at heq
  rw [← heq]
  exact hx

lemma mem_cell_le_end (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I J : Node) (s q : ℕ)
    (hq : q ∈ cell ρ ε I J s) : q ≤ cellEnd ρ ε I J s := Finset.le_sup (f := id) hq

lemma cell_ordConnected (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I J : Node) (s x y z : ℕ)
    (hx : x ∈ cell ρ ε I J s) (hz : z ∈ cell ρ ε I J s) (hxy : x ≤ y) (hyz : y ≤ z) :
    y ∈ cell ρ ε I J s := by
  rw [cell_mem] at hx hz ⊢
  refine ⟨hyz.trans hz.1, ?_, ?_⟩
  · have h1 := blockStart_monotone ρ ε I.1 I.2 hxy
    have h2 := blockStart_monotone ρ ε I.1 I.2 hyz
    rw [hx.2.1] at h1
    rw [hz.2.1] at h2
    exact le_antisymm h2 h1
  · have h1 := blockStart_monotone ρ ε J.1 J.2 hxy
    have h2 := blockStart_monotone ρ ε J.1 J.2 hyz
    rw [hx.2.2] at h1
    rw [hz.2.2] at h2
    exact le_antisymm h2 h1

lemma boundary_max (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I J : Node) (s : ℕ)
    (hs : s ∈ startsThrough ρ ε I K ∪ startsThrough ρ ε J K) :
    s ≤ K ∧ max (blockStart ρ ε I.1 I.2 s) (blockStart ρ ε J.1 J.2 s) = s := by
  rcases Finset.mem_union.mp hs with hs | hs
  · have h := Finset.mem_filter.mp hs
    exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp h.1),
      by rw [h.2, max_eq_left (SellerFacts.blockStart_le ρ ε J.1 J.2 s)]⟩
  · have h := Finset.mem_filter.mp hs
    exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp h.1),
      by rw [h.2, max_eq_right (SellerFacts.blockStart_le ρ ε I.1 I.2 s)]⟩

lemma boundary_le_cell (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I J : Node) (s q : ℕ)
    (hs : s ∈ startsThrough ρ ε I K ∪ startsThrough ρ ε J K)
    (hq : q ∈ cell ρ ε I J s) : s ≤ q := by
  have h := (cell_mem ρ ε I J s q).mp hq
  have hm := (boundary_max ρ ε I J s hs).2
  rw [← h.2.1, ← h.2.2] at hm
  rw [← hm]
  exact max_le (SellerFacts.blockStart_le ρ ε I.1 I.2 q)
    (SellerFacts.blockStart_le ρ ε J.1 J.2 q)

lemma cellEnd_lt_boundary (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I J : Node) (s t : ℕ)
    (hs : s ∈ startsThrough ρ ε I K ∪ startsThrough ρ ε J K)
    (ht : t ∈ startsThrough ρ ε I K ∪ startsThrough ρ ε J K) (hst : s < t) :
    cellEnd ρ ε I J s < t := by
  by_contra h
  have hsm := boundary_max ρ ε I J s hs
  have htm := boundary_max ρ ε I J t ht
  have hm := cell_ordConnected ρ ε I J s s t (cellEnd ρ ε I J s)
    (self_mem_cell ρ ε I J s hsm.1) (cellEnd_mem ρ ε I J s hsm.1) hst.le (by omega)
  have hcell := (cell_mem ρ ε I J s t).mp hm
  rw [hcell.2.1, hcell.2.2, hsm.2] at htm
  omega

def buyerInterval (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I J : Node) (s : ℕ) : Set ℝ :=
  Set.Icc ((s : ℝ) / K) ((cellEnd ρ ε I J s : ℝ) / K)

lemma buyerInterval_disjoint (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (ε : ℝ)
    (I J : Node) (s t : ℕ)
    (hs : s ∈ startsThrough ρ ε I K ∪ startsThrough ρ ε J K)
    (ht : t ∈ startsThrough ρ ε I K ∪ startsThrough ρ ε J K) (hst : s ≠ t) :
    Disjoint (buyerInterval ρ ε I J s) (buyerInterval ρ ε I J t) := by
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  rcases lt_or_gt_of_ne hst with h | h
  · have he := cellEnd_lt_boundary ρ ε I J s t hs ht h
    have hreal : (cellEnd ρ ε I J s : ℝ) / K < (t : ℝ) / K :=
      div_lt_div_of_pos_right (by exact_mod_cast he) hKr
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hy.1) (hx.2.trans_lt hreal)
  · have he := cellEnd_lt_boundary ρ ε I J t s ht hs h
    have hreal : (cellEnd ρ ε I J t : ℝ) / K < (s : ℝ) / K :=
      div_lt_div_of_pos_right (by exact_mod_cast he) hKr
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.1) (hy.2.trans_lt hreal)

lemma cell_coord_mem_buyerInterval (ρ : Grid K × Act K → ℝ) (ε : ℝ)
    (I J : Node) (s q : ℕ)
    (hs : s ∈ startsThrough ρ ε I K ∪ startsThrough ρ ε J K)
    (hq : q ∈ cell ρ ε I J s) : (q : ℝ) / K ∈ buyerInterval ρ ε I J s := by
  constructor
  · exact div_le_div_of_nonneg_right (by exact_mod_cast boundary_le_cell ρ ε I J s q hs hq)
      (Nat.cast_nonneg K)
  · exact div_le_div_of_nonneg_right (by exact_mod_cast mem_cell_le_end ρ ε I J s q hq)
      (Nat.cast_nonneg K)

lemma startsThrough_subset_range (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) :
    startsThrough ρ ε I K ⊆ Finset.range (K + 1) := Finset.filter_subset _ _

lemma rootPieces_length_le_grid (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) :
    (rootPieces ρ ε I).length ≤ K + 1 := by
  rw [rootPieces_length]
  simpa using Finset.card_le_card (startsThrough_subset_range ρ ε I)

lemma edgePieces_length_le_grid (ρ : Grid K × Act K → ℝ) (ε : ℝ) (e : Node × Node) :
    (edgePieces ρ ε e).length ≤ K + 1 := by
  have hsub : startsThrough ρ ε e.1 K ∪ startsThrough ρ ε e.2 K ⊆ Finset.range (K + 1) :=
    Finset.union_subset (startsThrough_subset_range ρ ε e.1) (startsThrough_subset_range ρ ε e.2)
  simpa [edgePieces] using Finset.card_le_card hsub

lemma flatMap_edgePieces_length_le_grid (ρ : Grid K × Act K → ℝ) (ε : ℝ)
    (es : List (Node × Node)) : (es.flatMap (edgePieces ρ ε)).length ≤ es.length * (K + 1) := by
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
      have he := edgePieces_length_le_grid ρ ε e
      omega

lemma edges_length_add_one (n : ℕ) (I : Node) : (edges n I).length + 1 = (nodes n I).length := by
  induction n generalizing I with
  | zero => simp [edges, nodes]
  | succ n ih =>
      simp only [edges, nodes]
      split_ifs with h
      · simp
      · have hl := ih (left I)
        have hr := ih (right I)
        simp only [List.length_cons, List.length_append]
        omega

lemma pieces_length_le_grid (ρ : Grid K × Act K → ℝ) (ε : ℝ) (d : ℕ) (I : Node) :
    (pieces ρ ε d I).length ≤ (nodes d I).length * (K + 1) := by
  have hr := rootPieces_length_le_grid ρ ε I
  have he := flatMap_edgePieces_length_le_grid ρ ε (edges d I)
  rw [pieces, List.length_append, ← edges_length_add_one, Nat.succ_mul]
  omega

lemma root_pieces_quadratic (ρ : Grid K × Act K → ℝ) (ε : ℝ) (d : ℕ) :
    (pieces ρ ε d (0, K + 1)).length ≤ 2 * (K + 1) ^ 2 := by
  have hg := pieces_length_le_grid ρ ε d (0, K + 1)
  have hn := nodes_length_le d (0, K + 1) (by simp)
  have hn' : (nodes d (0, K + 1)).length ≤ 2 * (K + 1) := hn.trans (Nat.sub_le _ _)
  have hm := Nat.mul_le_mul_right (K + 1) hn'
  nlinarith

def depth (K : ℕ) : ℕ := Nat.log2 (K + 1) + 1

lemma root_le_pow_depth (K : ℕ) : K + 1 ≤ 2 ^ depth K := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (K + 1)
  rw [← Nat.log2_eq_log_two] at h
  exact h.le


end BilateralProfit.Estimation

namespace BilateralProfit

open MeasureTheory

/-- A scalar query is either half an action observation or half the difference
of two fresh action observations. -/
inductive QuerySpec (A : Type) where
  | one : A → QuerySpec A
  | sub : A → A → QuerySpec A

namespace QuerySpec

variable {A : Type}

def Legal (p : A → Prop) : QuerySpec A → Prop
  | .one a => p a
  | .sub a b => p a ∧ p b

noncomputable def law (obs : A → Measure ℝ) : QuerySpec A → Measure ℝ
  | .one a => (obs a).map (fun r => r / 2)
  | .sub a b => ((obs a).prod (obs b)).map (fun z => (z.1 - z.2) / 2)

end QuerySpec

namespace QTree

variable {H A Out Out' : Type}

lemma allQueries_mono_pred (R : QTree H Out) {p q : H → Prop}
    (hR : R.AllQueries p) (hpq : ∀ h, p h → q h) : R.AllQueries q := by
  induction R with
  | done o => trivial
  | query h k ih => exact ⟨hpq h hR.1, fun r => ih r (hR.2 r)⟩

lemma prob_mono_output [DecidableEq H] (obs : H → ℕ → Measure ℝ) (R : QTree H Out)
    {E F : Out → Prop} (hEF : ∀ o, E o → F o) (cnt : H → ℕ) :
    R.prob obs E cnt ≤ R.prob obs F cnt := by
  induction R generalizing cnt with
  | done o =>
      classical
      simp only [prob]
      split_ifs with hE hF <;> simp_all
  | query q k ih => exact lintegral_mono (fun r => ih r _)

def mapOutput (f : Out → Out') : QTree H Out → QTree H Out'
  | .done o => .done (f o)
  | .query q k => .query q (fun r => mapOutput f (k r))

lemma allQueries_mapOutput (f : Out → Out') (R : QTree H Out)
    (p : H → Prop) (hR : R.AllQueries p) : (mapOutput f R).AllQueries p := by
  induction R with
  | done o => trivial
  | query q k ih => exact ⟨hR.1, fun r => ih r (hR.2 r)⟩

lemma queriesAtMost_mapOutput (f : Out → Out') (R : QTree H Out)
    {n : ℕ} (hR : R.QueriesAtMost n) : (mapOutput f R).QueriesAtMost n := by
  induction R generalizing n with
  | done o => trivial
  | query q k ih =>
      cases n with
      | zero => exact False.elim hR
      | succ n => exact fun r => ih r (hR r)

lemma prob_mapOutput [DecidableEq H] (f : Out → Out') (R : QTree H Out)
    (obs : H → ℕ → Measure ℝ) (E : Out' → Prop) (cnt : H → ℕ) :
    (mapOutput f R).prob obs E cnt = R.prob obs (fun o => E (f o)) cnt := by
  induction R generalizing cnt with
  | done o => rfl
  | query q k ih => exact lintegral_congr (fun r => ih r _)

/-- Implement every scalar query with one or two fresh action queries. -/
noncomputable def substitute (spec : H → QuerySpec A) : QTree H Out → QTree A Out
  | .done o => .done o
  | .query q k =>
      match spec q with
      | .one a => .query a (fun r => substitute spec (k (r / 2)))
      | .sub a b => .query a (fun r => .query b
          (fun s => substitute spec (k ((r - s) / 2))))

lemma allQueries_substitute (spec : H → QuerySpec A) (R : QTree H Out)
    (p : A → Prop) (hR : R.AllQueries (fun q => (spec q).Legal p)) :
    (substitute spec R).AllQueries p := by
  induction R with
  | done o => trivial
  | query q k ih =>
      cases h : spec q with
      | one a =>
          change (spec q).Legal p ∧ _ at hR
          rw [h] at hR
          simp only [substitute, h, AllQueries]
          exact ⟨hR.1, fun r => ih _ (hR.2 _)⟩
      | sub a b =>
          change (spec q).Legal p ∧ _ at hR
          rw [h] at hR
          simp only [substitute, h, AllQueries]
          exact ⟨hR.1.1, fun r => ⟨hR.1.2, fun s => ih _ (hR.2 _)⟩⟩

lemma queriesAtMost_substitute (spec : H → QuerySpec A) (R : QTree H Out)
    {n : ℕ} (hR : R.QueriesAtMost n) : (substitute spec R).QueriesAtMost (2 * n) := by
  induction R generalizing n with
  | done o => trivial
  | query q k ih =>
      cases n with
      | zero => exact False.elim hR
      | succ n =>
          cases h : spec q with
          | one a =>
              simp only [substitute, h, Nat.mul_succ, QueriesAtMost]
              intro r
              have hr := ih (r / 2) (hR (r / 2))
              have hmono : ∀ (S : QTree A Out) (m : ℕ), S.QueriesAtMost m →
                  S.QueriesAtMost (m + 1) := by
                intro S m hS
                induction S generalizing m with
                | done o => trivial
                | query a k ihS =>
                    cases m with
                    | zero => exact False.elim hS
                    | succ m => exact fun x => ihS x m (hS x)
              exact hmono _ _ hr
          | sub a b =>
              simp only [substitute, h, Nat.mul_succ, QueriesAtMost]
              exact fun r s => ih _ (hR _)

/-- Lower integrals suffice for substitution even when the continuation is not
measurable. Each replacement can only increase the lower probability. -/
lemma prob_substitute_lower [DecidableEq H] [DecidableEq A]
    (spec : H → QuerySpec A) (R : QTree H Out) (obs : A → Measure ℝ)
    (hobs : ∀ a, IsProbabilityMeasure (obs a)) (E : Out → Prop)
    (cntH : H → ℕ) (cntA : A → ℕ) :
    R.prob (fun q _ => (spec q).law obs) E cntH ≤
      (substitute spec R).prob (fun a _ => obs a) E cntA := by
  induction R generalizing cntH cntA with
  | done o => exact le_rfl
  | query q k ih =>
      cases h : spec q with
      | one a =>
          simp only [prob, substitute, h, QuerySpec.law]
          calc
            _ ≤ ∫⁻ r, (substitute spec (k r)).prob (fun a _ => obs a) E
                (Function.update cntA a (cntA a + 1)) ∂(obs a).map (fun r => r / 2) :=
              lintegral_mono (fun r => ih r _ _)
            _ ≤ _ := lintegral_map_le _ _
      | sub a b =>
          letI := hobs a
          letI := hobs b
          simp only [prob, substitute, h, QuerySpec.law]
          calc
            _ ≤ ∫⁻ r, (substitute spec (k r)).prob (fun a _ => obs a) E
                (Function.update (Function.update cntA a (cntA a + 1)) b
                  ((Function.update cntA a (cntA a + 1)) b + 1))
                ∂((obs a).prod (obs b)).map (fun z => (z.1 - z.2) / 2) :=
              lintegral_mono (fun r => ih r _ _)
            _ ≤ ∫⁻ z, (substitute spec (k ((z.1 - z.2) / 2))).prob
                (fun a _ => obs a) E
                (Function.update (Function.update cntA a (cntA a + 1)) b
                  ((Function.update cntA a (cntA a + 1)) b + 1)) ∂(obs a).prod (obs b) :=
              lintegral_map_le _ _
            _ ≤ _ := lintegral_prod_le _

end QTree

end BilateralProfit

namespace BilateralProfit.ObservationFacts

open MeasureTheory

theorem integrable_id_of_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (c : ℝ) (hs : ν (Set.Icc c (c + 2))ᶜ = 0) : Integrable (fun r : ℝ => r) ν := by
  apply Integrable.of_bound (by fun_prop) (|c| + 2)
  have hs' : ∀ᵐ r ∂ν, r ∈ Set.Icc c (c + 2) := ae_iff.mpr hs
  filter_upwards [hs'] with r hr
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le c, hr.1]
  · linarith [le_abs_self c, hr.2]

theorem mean_mem_support (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (c : ℝ) (hs : ν (Set.Icc c (c + 2))ᶜ = 0) :
    (∫ r : ℝ, r ∂ν) ∈ Set.Icc c (c + 2) := by
  have hi := integrable_id_of_support ν c hs
  have hs' : ∀ᵐ r ∂ν, r ∈ Set.Icc c (c + 2) := ae_iff.mpr hs
  constructor
  · have h := integral_mono_ae (integrable_const c) hi
      (hs'.mono fun _ hr => hr.1)
    simpa using h
  · have h := integral_mono_ae hi (integrable_const (c + 2))
      (hs'.mono fun _ hr => hr.2)
    simpa using h

theorem offset_bounds {A : Type} [Nonempty A] (obs : A → Measure ℝ)
    (hobs : ∀ a, IsProbabilityMeasure (obs a)) (c : ℝ)
    (hs : ∀ a, obs a (Set.Icc c (c + 2))ᶜ = 0)
    (hm : ∀ a, (∫ r : ℝ, r ∂obs a) ∈ Set.Icc (0 : ℝ) 1) :
    -2 ≤ c ∧ c ≤ 1 := by
  obtain ⟨a⟩ := ‹Nonempty A›
  letI := hobs a
  have hb := mean_mem_support (obs a) c (hs a)
  have ha := hm a
  constructor <;> linarith [hb.1, hb.2, ha.1, ha.2]

theorem law_probability {A : Type} (obs : A → Measure ℝ)
    (hobs : ∀ a, IsProbabilityMeasure (obs a)) (q : QuerySpec A) :
    IsProbabilityMeasure (q.law obs) := by
  cases q with
  | one a =>
      letI := hobs a
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  | sub a b =>
      letI := hobs a
      letI := hobs b
      exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem law_support {A : Type} (obs : A → Measure ℝ)
    (hobs : ∀ a, IsProbabilityMeasure (obs a)) (c : ℝ)
    (hc : -2 ≤ c ∧ c ≤ 1)
    (hs : ∀ a, obs a (Set.Icc c (c + 2))ᶜ = 0) (q : QuerySpec A) :
    q.law obs (Set.Icc (-1 : ℝ) 3)ᶜ = 0 := by
  apply ae_iff.mp
  cases q with
  | one a =>
      apply (ae_map_iff (by fun_prop) measurableSet_Icc).mpr
      have ha : ∀ᵐ r ∂obs a, r ∈ Set.Icc c (c + 2) := ae_iff.mpr (hs a)
      filter_upwards [ha] with r hr
      constructor <;> linarith [hr.1, hr.2, hc.1, hc.2]
  | sub a b =>
      letI := hobs a
      letI := hobs b
      apply (ae_map_iff (by fun_prop) measurableSet_Icc).mpr
      have ha : ∀ᵐ r ∂obs a, r ∈ Set.Icc c (c + 2) := ae_iff.mpr (hs a)
      have hb : ∀ᵐ r ∂obs b, r ∈ Set.Icc c (c + 2) := ae_iff.mpr (hs b)
      have haf : ∀ᵐ z ∂(obs a).prod (obs b), z.1 ∈ Set.Icc c (c + 2) :=
        (measurePreserving_fst (μ := obs a) (ν := obs b)).quasiMeasurePreserving.ae ha
      have hbs : ∀ᵐ z ∂(obs a).prod (obs b), z.2 ∈ Set.Icc c (c + 2) :=
        (measurePreserving_snd (μ := obs a) (ν := obs b)).quasiMeasurePreserving.ae hb
      filter_upwards [haf, hbs] with z hz1 hz2
      constructor <;> linarith [hz1.1, hz1.2, hz2.1, hz2.2]

theorem law_one_mean {A : Type} (obs : A → Measure ℝ)
    (hobs : ∀ a, IsProbabilityMeasure (obs a)) (a : A) :
    (∫ r : ℝ, r ∂(QuerySpec.one a).law obs) = (∫ r : ℝ, r ∂obs a) / 2 := by
  rw [QuerySpec.law, integral_map (by fun_prop) (by fun_prop), integral_div]

theorem law_sub_mean {A : Type} (obs : A → Measure ℝ)
    (hobs : ∀ a, IsProbabilityMeasure (obs a)) (c : ℝ)
    (hs : ∀ a, obs a (Set.Icc c (c + 2))ᶜ = 0) (a b : A) :
    (∫ r : ℝ, r ∂(QuerySpec.sub a b).law obs) =
      ((∫ r : ℝ, r ∂obs a) - (∫ r : ℝ, r ∂obs b)) / 2 := by
  letI := hobs a
  letI := hobs b
  have ha := integrable_id_of_support (obs a) c (hs a)
  have hb := integrable_id_of_support (obs b) c (hs b)
  rw [QuerySpec.law, integral_map (by fun_prop) (by fun_prop), integral_div,
    integral_sub (ha.comp_fst (obs b)) (hb.comp_snd (obs a))]
  rw [integral_fun_fst (μ := obs a) (ν := obs b) (fun r : ℝ => r),
    integral_fun_snd (μ := obs a) (ν := obs b) (fun r : ℝ => r)]
  simp only [probReal_univ, one_smul]

end BilateralProfit.ObservationFacts

namespace BilateralProfit.Estimation

open MeasureTheory

variable {K : ℕ}

def Piece.parent : Piece → Node
  | .root I _ => I
  | .edge I _ _ => I

def Piece.child : Piece → Node
  | .root I _ => I
  | .edge _ J _ => J

def Piece.start : Piece → ℕ
  | .root _ s => s
  | .edge _ _ s => s

def gridAction (r : ℕ) (q : Fin (K + 1)) : Act K :=
  if h : r ≤ (q : ℕ) then
    ⟨(⟨r, lt_of_le_of_lt h q.isLt⟩, q), by exact_mod_cast h⟩ else default

lemma gridAction_pt (r : ℕ) (q : Fin (K + 1)) (hr : r ≤ (q : ℕ)) :
    pt K (gridAction r q).1 = ((r : ℝ) / K, (q : ℝ) / K) := by
  simp [gridAction, hr, pt]

noncomputable def safeAt (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) (s : ℕ)
    (q : Fin (K + 1)) : Prop :=
  repAt ρ ε I s ≤ (q : ℕ) ∧ gapStar ρ (gridAction (repAt ρ ε I s) q) ≤ 2 * ε

noncomputable def pieceDom (ρ : Grid K × Act K → ℝ) (ε : ℝ) (p : Piece) :
    Finset (Fin (K + 1)) := by
  classical
  exact Finset.univ.filter (fun q => (q : ℕ) ∈ cell ρ ε p.parent p.child p.start ∧
    safeAt ρ ε p.parent p.start q ∧ safeAt ρ ε p.child p.start q)

noncomputable def pieceSpec (ρ : Grid K × Act K → ℝ) (ε : ℝ)
    (p : Piece) (q : Fin (K + 1)) : QuerySpec (Act K) :=
  match p with
  | .root I s => .one (gridAction (repAt ρ ε I s) q)
  | .edge I J s => .sub (gridAction (repAt ρ ε J s) q)
      (gridAction (repAt ρ ε I s) q)

noncomputable def pieceValue (ρ : Grid K × Act K → ℝ) (ε : ℝ)
    (μ : Measure (ℝ × ℝ)) (p : Piece) (q : Fin (K + 1)) : ℝ :=
  match p with
  | .root I s => Ptrade μ ((repAt ρ ε I s : ℝ) / K, (q : ℝ) / K) / 2
  | .edge I J s => (Ptrade μ ((repAt ρ ε J s : ℝ) / K, (q : ℝ) / K) -
      Ptrade μ ((repAt ρ ε I s : ℝ) / K, (q : ℝ) / K)) / 2

lemma pieceSpec_legal (ρ : Grid K × Act K → ℝ) (ε : ℝ)
    (p : Piece) (q : Fin (K + 1)) (hq : q ∈ pieceDom ρ ε p) :
    (pieceSpec ρ ε p q).Legal (fun a => gapStar ρ a ≤ 2 * ε) := by
  classical
  have h := (Finset.mem_filter.mp hq).2
  cases p with
  | root I s => exact h.2.1.2
  | edge I J s => exact ⟨h.2.2.2, h.2.1.2⟩

lemma local_representative_good (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (ε : ℝ) (hε : 0 ≤ ε) (a : Act K) (ha : gapStar ρ a ≤ ε)
    (I : Node) (hp : I.1 ≤ (a.1.1 : ℕ) ∧ (a.1.1 : ℕ) < I.1 + I.2)
    (hnode : I.1 + I.2 ≤ K + 1) : safeAt ρ ε I a.1.2 a.1.2 := by
  have hfeas : repAt ρ ε I a.1.2 ≤ (a.1.2 : ℕ) :=
    SellerFacts.rep_feasible hK ρ hρ I.1 I.2 _ _ (by omega)
      (hp.1.trans (by exact_mod_cast a.2)) (SellerFacts.blockStart_le ρ ε I.1 I.2 _)
  refine ⟨hfeas, ?_⟩
  have happ := SellerFacts.rep_approx hK ρ hρ ε hε I.1 I.2 a.1.1 a.1.2 hp hnode (by omega)
  unfold gapStar gapStarPt
  rw [gridAction_pt _ _ hfeas]
  change optVal ρ - valProfitPt ρ (pt K a.1) ≤ ε at ha
  change valProfitPt ρ (pt K a.1) ≤
    valProfitPt ρ ((repAt ρ ε I a.1.2 : ℝ) / K, (a.1.2 : ℝ) / K) + ε at happ
  linarith

lemma repAt_eq_of_block_eq (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) (q s : ℕ)
    (h : blockStart ρ ε I.1 I.2 q = blockStart ρ ε I.1 I.2 s) :
    repAt ρ ε I q = repAt ρ ε I s := by simp only [repAt, h]

lemma target_mem_pieceDom (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (ε : ℝ) (hε : 0 ≤ ε) (a : Act K) (ha : gapStar ρ a ≤ ε)
    (p : Piece)
    (hp : p.parent.1 ≤ (a.1.1 : ℕ) ∧ (a.1.1 : ℕ) < p.parent.1 + p.parent.2)
    (hc : p.child.1 ≤ (a.1.1 : ℕ) ∧ (a.1.1 : ℕ) < p.child.1 + p.child.2)
    (hpb : p.parent.1 + p.parent.2 ≤ K + 1) (hcb : p.child.1 + p.child.2 ≤ K + 1)
    (hcell : (a.1.2 : ℕ) ∈ cell ρ ε p.parent p.child p.start) :
    a.1.2 ∈ pieceDom ρ ε p := by
  classical
  have h := (cell_mem ρ ε p.parent p.child p.start a.1.2).mp hcell
  have hpg := local_representative_good hK ρ hρ ε hε a ha p.parent hp hpb
  have hcg := local_representative_good hK ρ hρ ε hε a ha p.child hc hcb
  have hpr := repAt_eq_of_block_eq ρ ε p.parent a.1.2 p.start h.2.1
  have hcr := repAt_eq_of_block_eq ρ ε p.child a.1.2 p.start h.2.2
  rw [safeAt, hpr] at hpg
  rw [safeAt, hcr] at hcg
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcell, hpg, hcg⟩

lemma pieceValue_mem (ρ : Grid K × Act K → ℝ) (ε : ℝ)
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (p : Piece) (q : Fin (K + 1)) :
    pieceValue ρ ε μ p q ∈ Set.Icc (-1 : ℝ) 1 := by
  cases p with
  | root I s =>
      have h0 := TradeFacts.Ptrade_nonneg μ ((repAt ρ ε I s : ℝ) / K, (q : ℝ) / K)
      have h1 := TradeFacts.Ptrade_le_one μ ((repAt ρ ε I s : ℝ) / K, (q : ℝ) / K)
      dsimp [pieceValue]
      constructor <;> linarith
  | edge I J s =>
      have h0 := TradeFacts.Ptrade_nonneg μ ((repAt ρ ε I s : ℝ) / K, (q : ℝ) / K)
      have h1 := TradeFacts.Ptrade_le_one μ ((repAt ρ ε I s : ℝ) / K, (q : ℝ) / K)
      have h0' := TradeFacts.Ptrade_nonneg μ ((repAt ρ ε J s : ℝ) / K, (q : ℝ) / K)
      have h1' := TradeFacts.Ptrade_le_one μ ((repAt ρ ε J s : ℝ) / K, (q : ℝ) / K)
      dsimp [pieceValue]
      constructor <;> linarith

lemma pieceValue_monotone (ρ : Grid K × Act K → ℝ) (ε : ℝ)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (p : Piece) :
    Monotone (pieceValue ρ ε μ p) ∨ Antitone (pieceValue ρ ε μ p) := by
  cases p with
  | root I s =>
      right
      intro q q' hq
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact SellerFacts.Ptrade_antitone_buyer μ _
        (div_le_div_of_nonneg_right (by exact_mod_cast hq) (Nat.cast_nonneg K))
  | edge I J s =>
      rcases SellerFacts.Ptrade_difference_monotone μ ((repAt ρ ε J s : ℝ) / K)
        ((repAt ρ ε I s : ℝ) / K) with h | h
      · left
        intro q q' hq
        exact div_le_div_of_nonneg_right
          (h (div_le_div_of_nonneg_right (by exact_mod_cast hq) (Nat.cast_nonneg K))) (by norm_num)
      · right
        intro q q' hq
        exact div_le_div_of_nonneg_right
          (h (div_le_div_of_nonneg_right (by exact_mod_cast hq) (Nat.cast_nonneg K))) (by norm_num)

lemma pieceLaw_mean (ρ : Grid K × Act K → ℝ) (ε : ℝ)
    (μ : Measure (ℝ × ℝ)) (c : ℝ) (obs : Act K → Measure ℝ)
    (hobs : ∀ a, IsProbabilityMeasure (obs a))
    (hs : ∀ a, obs a (Set.Icc c (c + 2))ᶜ = 0)
    (hm : ∀ a, ∫ r, r ∂obs a = Ptrade μ (pt K a.1))
    (p : Piece) (q : Fin (K + 1)) (hq : q ∈ pieceDom ρ ε p) :
    (∫ r, r ∂(pieceSpec ρ ε p q).law obs) = pieceValue ρ ε μ p q := by
  classical
  have h := (Finset.mem_filter.mp hq).2
  cases p with
  | root I s =>
      change _ = Ptrade μ ((repAt ρ ε I s : ℝ) / K, (q : ℝ) / K) / 2
      rw [pieceSpec, ObservationFacts.law_one_mean obs hobs, hm]
      rw [gridAction_pt (repAt ρ ε I s) q (by exact h.2.1.1)]
  | edge I J s =>
      change _ = (Ptrade μ ((repAt ρ ε J s : ℝ) / K, (q : ℝ) / K) -
        Ptrade μ ((repAt ρ ε I s : ℝ) / K, (q : ℝ) / K)) / 2
      rw [pieceSpec, ObservationFacts.law_sub_mean obs hobs c hs, hm, hm]
      rw [gridAction_pt (repAt ρ ε I s) q (by exact h.2.1.1),
        gridAction_pt (repAt ρ ε J s) q (by exact h.2.2.1)]

end BilateralProfit.Estimation

namespace BilateralProfit.Estimation

open MeasureTheory Set

theorem survival_variation_eq_endpoints {Y : Type*} [LinearOrder Y]
    (g : Y → ℝ) (s : Set Y) (a b : Y)
    (ha : a ∈ s) (hb : b ∈ s) (hs : ∀ y ∈ s, a ≤ y ∧ y ≤ b)
    (hg : MonotoneOn g s ∨ AntitoneOn g s) :
    eVariationOn g s = ENNReal.ofReal |g b - g a| := by
  have hab : a ≤ b := (hs b hb).1
  rcases hg with hg | hg
  · have hset : s ∩ Icc a b = s := inter_eq_left.mpr hs
    rw [← hset, hg.eVariationOn_eq ha hb, abs_of_nonneg (sub_nonneg.mpr (hg ha hb hab))]
  · have hmono : MonotoneOn (g ∘ OrderDual.ofDual)
        (OrderDual.ofDual ⁻¹' s) := by
      intro x hx y hy hxy
      exact hg hy hx hxy
    have hv := hmono.eVariationOn_eq (a := OrderDual.toDual b)
      (b := OrderDual.toDual a) hb ha
    have hset : OrderDual.ofDual ⁻¹' s ∩
        Icc (OrderDual.toDual b) (OrderDual.toDual a) = OrderDual.ofDual ⁻¹' s := by
      apply inter_eq_left.mpr
      intro y hy
      exact ⟨(hs y hy).2, (hs y hy).1⟩
    rw [hset, eVariationOn.comp_ofDual] at hv
    rw [hv, abs_of_nonpos (sub_nonpos.mpr (hg ha hb hab))]
    congr 1
    simp only [Function.comp_apply, OrderDual.ofDual_toDual]
    ring

theorem finite_survival_variation_eq {Y : Type*} [LinearOrder Y]
    (g : Y → ℝ) (s : Finset Y) (hs : s.Nonempty)
    (hg : MonotoneOn g (s : Set Y) ∨ AntitoneOn g (s : Set Y)) :
    (eVariationOn g (s : Set Y)).toReal = |g (s.max' hs) - g (s.min' hs)| := by
  rw [survival_variation_eq_endpoints g (s : Set Y) (s.min' hs) (s.max' hs)
    (Finset.min'_mem s hs) (Finset.max'_mem s hs)
    (fun y hy => ⟨Finset.min'_le s y hy, Finset.le_max' s y hy⟩) hg]
  exact ENNReal.toReal_ofReal (abs_nonneg _)

theorem buyer_strip_split (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (S : Set ℝ) (hS : MeasurableSet S) (a b : ℝ) (hab : a ≤ b) :
    μ.real (S ×ˢ Ici a) = μ.real (S ×ˢ Ici b) + μ.real (S ×ˢ Ico a b) := by
  have hset : S ×ˢ Ici a = (S ×ˢ Ici b) ∪ (S ×ˢ Ico a b) := by
    ext v
    simp only [mem_prod, mem_Ici, mem_union, mem_Ico]
    constructor
    · rintro ⟨hv, hb⟩
      by_cases h : b ≤ v.2
      · exact Or.inl ⟨hv, h⟩
      · exact Or.inr ⟨hv, hb, lt_of_not_ge h⟩
    · rintro (⟨hv, hb⟩ | ⟨hv, hb, _⟩)
      · exact ⟨hv, hab.trans hb⟩
      · exact ⟨hv, hb⟩
  rw [hset]
  apply measureReal_union
  · apply disjoint_left.mpr
    intro v hv hw
    exact (not_lt_of_ge hv.2) hw.2.2
  · exact hS.prod measurableSet_Ico
  · finiteness
  · finiteness

theorem trade_difference_oscillation_le (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (u v l r a b c d : ℝ) (hu : u ∈ Icc l r) (hv : v ∈ Icc l r)
    (ha : a ∈ Icc c d) (hb : b ∈ Icc c d) (hab : a ≤ b) :
    |(Ptrade μ (u, b) - Ptrade μ (v, b)) / 2 -
      (Ptrade μ (u, a) - Ptrade μ (v, a)) / 2| ≤ μ.real (Icc l r ×ˢ Icc c d) := by
  by_cases huv : u ≤ v
  · have h1 := SellerFacts.Ptrade_seller_split μ u v a huv
    have h2 := SellerFacts.Ptrade_seller_split μ u v b huv
    have h3 := buyer_strip_split μ (Ioc u v) measurableSet_Ioc a b hab
    have heq : (Ptrade μ (u, b) - Ptrade μ (v, b)) / 2 -
        (Ptrade μ (u, a) - Ptrade μ (v, a)) / 2 = μ.real (Ioc u v ×ˢ Ico a b) / 2 := by
      linarith
    rw [heq, abs_of_nonneg (by positivity)]
    have hmass : μ.real (Ioc u v ×ˢ Ico a b) ≤ μ.real (Icc l r ×ˢ Icc c d) := by
      apply measureReal_mono ?_ (by finiteness)
      intro z hz
      exact ⟨⟨hu.1.trans hz.1.1.le, hz.1.2.trans hv.2⟩,
        ⟨ha.1.trans hz.2.1, hz.2.2.le.trans hb.2⟩⟩
    linarith [measureReal_nonneg (μ := μ) (s := Ioc u v ×ˢ Ico a b)]
  · have hvu := le_of_not_ge huv
    have h1 := SellerFacts.Ptrade_seller_split μ v u a hvu
    have h2 := SellerFacts.Ptrade_seller_split μ v u b hvu
    have h3 := buyer_strip_split μ (Ioc v u) measurableSet_Ioc a b hab
    have heq : (Ptrade μ (u, b) - Ptrade μ (v, b)) / 2 -
        (Ptrade μ (u, a) - Ptrade μ (v, a)) / 2 = -(μ.real (Ioc v u ×ˢ Ico a b) / 2) := by
      linarith
    rw [heq, abs_neg, abs_of_nonneg (by positivity)]
    have hmass : μ.real (Ioc v u ×ˢ Ico a b) ≤ μ.real (Icc l r ×ˢ Icc c d) := by
      apply measureReal_mono ?_ (by finiteness)
      intro z hz
      exact ⟨⟨hv.1.trans hz.1.1.le, hz.1.2.trans hu.2⟩,
        ⟨ha.1.trans hz.2.1, hz.2.2.le.trans hb.2⟩⟩
    linarith [measureReal_nonneg (μ := μ) (s := Ioc v u ×ˢ Ico a b)]

theorem trade_oscillation_le (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (u a b c d : ℝ) (ha : a ∈ Icc c d) (hb : b ∈ Icc c d) (hab : a ≤ b) :
    |Ptrade μ (u, b) / 2 - Ptrade μ (u, a) / 2| ≤ μ.real (univ ×ˢ Icc c d) := by
  have hsplit := buyer_strip_split μ (Iic u) measurableSet_Iic a b hab
  change Ptrade μ (u, a) = Ptrade μ (u, b) + μ.real (Iic u ×ˢ Ico a b) at hsplit
  have heq : Ptrade μ (u, b) / 2 - Ptrade μ (u, a) / 2 =
      -(μ.real (Iic u ×ˢ Ico a b) / 2) := by linarith
  rw [heq, abs_neg, abs_of_nonneg (by positivity)]
  have hmass : μ.real (Iic u ×ˢ Ico a b) ≤ μ.real (univ ×ˢ Icc c d) := by
    apply measureReal_mono ?_ (by finiteness)
    intro z hz
    exact ⟨mem_univ _, ⟨ha.1.trans hz.2.1, hz.2.2.le.trans hb.2⟩⟩
  linarith [measureReal_nonneg (μ := μ) (s := Iic u ×ˢ Ico a b)]

theorem trade_difference_variation_le {K : ℕ} (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (_hK : 0 < K) (dom : Finset (Fin (K + 1))) (u v l r b₀ b₁ : ℝ)
    (hu : u ∈ Icc l r) (hv : v ∈ Icc l r)
    (hdom : ∀ y ∈ dom, (y : ℝ) / K ∈ Icc b₀ b₁) :
    (eVariationOn (fun y : Fin (K + 1) =>
      (Ptrade μ (u, (y : ℝ) / K) - Ptrade μ (v, (y : ℝ) / K)) / 2)
      (dom : Set (Fin (K + 1)))).toReal ≤ μ.real (Icc l r ×ˢ Icc b₀ b₁) := by
  by_cases hs : dom.Nonempty
  · have hmono : MonotoneOn (fun y : Fin (K + 1) =>
        (Ptrade μ (u, (y : ℝ) / K) - Ptrade μ (v, (y : ℝ) / K)) / 2) ↑dom ∨
        AntitoneOn (fun y : Fin (K + 1) =>
        (Ptrade μ (u, (y : ℝ) / K) - Ptrade μ (v, (y : ℝ) / K)) / 2) ↑dom := by
      rcases SellerFacts.Ptrade_difference_monotone μ u v with hm | hm
      · left
        intro y _ z _ hyz
        exact div_le_div_of_nonneg_right (hm
          (div_le_div_of_nonneg_right (by exact_mod_cast hyz) (Nat.cast_nonneg K))) (by norm_num)
      · right
        intro y _ z _ hyz
        exact div_le_div_of_nonneg_right (hm
          (div_le_div_of_nonneg_right (by exact_mod_cast hyz) (Nat.cast_nonneg K))) (by norm_num)
    rw [finite_survival_variation_eq _ dom hs hmono]
    apply trade_difference_oscillation_le μ u v l r _ _ b₀ b₁ hu hv
      (hdom _ (Finset.min'_mem _ _)) (hdom _ (Finset.max'_mem _ _))
    exact div_le_div_of_nonneg_right (by exact_mod_cast (Finset.min'_le dom _ (Finset.max'_mem dom hs)))
      (Nat.cast_nonneg K)
  · have hemp := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hemp, measureReal_nonneg]

theorem trade_variation_le {K : ℕ} (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (_hK : 0 < K) (dom : Finset (Fin (K + 1))) (u b₀ b₁ : ℝ)
    (hdom : ∀ y ∈ dom, (y : ℝ) / K ∈ Icc b₀ b₁) :
    (eVariationOn (fun y : Fin (K + 1) => Ptrade μ (u, (y : ℝ) / K) / 2)
      (dom : Set (Fin (K + 1)))).toReal ≤ μ.real (univ ×ˢ Icc b₀ b₁) := by
  by_cases hs : dom.Nonempty
  · have hmono : AntitoneOn (fun y : Fin (K + 1) => Ptrade μ (u, (y : ℝ) / K) / 2) ↑dom := by
      intro y _ z _ hyz
      exact div_le_div_of_nonneg_right (SellerFacts.Ptrade_antitone_buyer μ u
        (div_le_div_of_nonneg_right (by exact_mod_cast hyz) (Nat.cast_nonneg K))) (by norm_num)
    rw [finite_survival_variation_eq _ dom hs (Or.inr hmono)]
    apply trade_oscillation_le μ u _ _ b₀ b₁
      (hdom _ (Finset.min'_mem _ _)) (hdom _ (Finset.max'_mem _ _))
    exact div_le_div_of_nonneg_right (by exact_mod_cast (Finset.min'_le dom _ (Finset.max'_mem dom hs)))
      (Nat.cast_nonneg K)
  · have hemp := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hemp, measureReal_nonneg]

theorem sum_rectangle_mass_le {ι : Type*} [Fintype ι]
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (S : Set ℝ) (hS : MeasurableSet S)
    (b₀ b₁ : ι → ℝ) (hdisj : Pairwise (fun i j => Disjoint (Icc (b₀ i) (b₁ i)) (Icc (b₀ j) (b₁ j)))) :
    ∑ i, μ.real (S ×ˢ Icc (b₀ i) (b₁ i)) ≤ μ.real (S ×ˢ (univ : Set ℝ)) := by
  have hprod : Pairwise (fun i j =>
      Disjoint (S ×ˢ Icc (b₀ i) (b₁ i)) (S ×ˢ Icc (b₀ j) (b₁ j))) := by
    intro i j hij
    apply disjoint_left.mpr
    intro z hzi hzj
    exact disjoint_left.mp (hdisj hij) hzi.2 hzj.2
  rw [← measureReal_iUnion_fintype hprod (fun i => hS.prod measurableSet_Icc)
    (fun _ => by finiteness)]
  apply measureReal_mono ?_ (by finiteness)
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  exact ⟨hi.1, mem_univ _⟩

theorem sum_trade_difference_variation_le {K : ℕ} {ι : Type*} [Fintype ι]
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] (hK : 0 < K)
    (dom : ι → Finset (Fin (K + 1))) (u v : ι → ℝ) (l r : ℝ) (b₀ b₁ : ι → ℝ)
    (hu : ∀ i, u i ∈ Icc l r) (hv : ∀ i, v i ∈ Icc l r)
    (hdom : ∀ i, ∀ y ∈ dom i, (y : ℝ) / K ∈ Icc (b₀ i) (b₁ i))
    (hdisj : Pairwise (fun i j => Disjoint (Icc (b₀ i) (b₁ i)) (Icc (b₀ j) (b₁ j)))) :
    ∑ i, (eVariationOn (fun y : Fin (K + 1) =>
      (Ptrade μ (u i, (y : ℝ) / K) - Ptrade μ (v i, (y : ℝ) / K)) / 2)
      (dom i : Set (Fin (K + 1)))).toReal ≤ μ.real (Icc l r ×ˢ (univ : Set ℝ)) := by
  calc
    _ ≤ ∑ i, μ.real (Icc l r ×ˢ Icc (b₀ i) (b₁ i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact trade_difference_variation_le μ hK (dom i) (u i) (v i) l r (b₀ i) (b₁ i)
        (hu i) (hv i) (hdom i)
    _ ≤ _ := sum_rectangle_mass_le μ (Icc l r) measurableSet_Icc b₀ b₁ hdisj

theorem sum_trade_variation_le {K : ℕ} {ι : Type*} [Fintype ι]
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (hK : 0 < K)
    (dom : ι → Finset (Fin (K + 1))) (u : ι → ℝ) (b₀ b₁ : ι → ℝ)
    (hdom : ∀ i, ∀ y ∈ dom i, (y : ℝ) / K ∈ Icc (b₀ i) (b₁ i))
    (hdisj : Pairwise (fun i j => Disjoint (Icc (b₀ i) (b₁ i)) (Icc (b₀ j) (b₁ j)))) :
    ∑ i, (eVariationOn (fun y : Fin (K + 1) => Ptrade μ (u i, (y : ℝ) / K) / 2)
      (dom i : Set (Fin (K + 1)))).toReal ≤ 1 := by
  calc
    _ ≤ ∑ i, μ.real ((univ : Set ℝ) ×ˢ Icc (b₀ i) (b₁ i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact trade_variation_le μ hK (dom i) (u i) (b₀ i) (b₁ i) (hdom i)
    _ ≤ μ.real ((univ : Set ℝ) ×ˢ (univ : Set ℝ)) :=
      sum_rectangle_mass_le μ univ MeasurableSet.univ b₀ b₁ hdisj
    _ = 1 := by simp

end BilateralProfit.Estimation

namespace BilateralProfit.Estimation

open MeasureTheory Set

variable {K : ℕ}

lemma repAt_mem_hull (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) (s : ℕ)
    (hI : 0 < I.2) : (repAt ρ ε I s : ℝ) / K ∈ hull K I := by
  have hr := SellerFacts.rep_mem ρ I.1 I.2 (blockStart ρ ε I.1 I.2 s) hI
  refine ⟨?_, ?_⟩
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hr.1) (Nat.cast_nonneg K)
  · exact div_le_div_of_nonneg_right
      (by exact_mod_cast (show repAt ρ ε I s ≤ I.1 + I.2 - 1 by exact Nat.le_sub_one_of_lt hr.2))
      (Nat.cast_nonneg K)

lemma edges_valid (hK : 0 < K) (n : ℕ) (I : Node) (hI : 0 < I.2) :
    ∀ e ∈ edges n I, 0 < e.1.2 ∧ 0 < e.2.2 ∧ hull K e.2 ⊆ hull K e.1 := by
  induction n generalizing I with
  | zero => simp [edges]
  | succ n ih =>
      intro e he
      simp only [edges] at he
      split_ifs at he with hsmall
      · simp at he
      · have hh := halves_pos I (by omega)
        have hsub := hull_children hK I (by omega)
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨hI, hh.1, hsub.1⟩
        · rcases List.mem_cons.mp he with rfl | he
          · exact ⟨hI, hh.2, hsub.2.1⟩
          · rcases List.mem_append.mp he with he | he
            · exact ih (left I) hh.1 e he
            · exact ih (right I) hh.2 e he

lemma pieceDom_mem_cell (ρ : Grid K × Act K → ℝ) (ε : ℝ) (p : Piece)
    (q : Fin (K + 1)) (hq : q ∈ pieceDom ρ ε p) :
    (q : ℕ) ∈ cell ρ ε p.parent p.child p.start := by
  classical
  exact (Finset.mem_filter.mp hq).2.1

lemma rootPieces_variation_le (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) :
    ((rootPieces ρ ε I).map (fun p =>
      (eVariationOn (pieceValue ρ ε μ p) (pieceDom ρ ε p : Set (Fin (K + 1)))).toReal)).sum ≤ 1 := by
  classical
  let S := startsThrough ρ ε I K
  have h := sum_trade_variation_le (ι := {s // s ∈ S}) μ hK
    (fun s => pieceDom ρ ε (.root I s))
    (fun s => (repAt ρ ε I s : ℝ) / K)
    (fun s => (s : ℕ) / (K : ℝ))
    (fun s => (cellEnd ρ ε I I s : ℝ) / K) ?_ ?_
  · change (∑ s : S, (eVariationOn (pieceValue ρ ε μ (.root I s))
        (pieceDom ρ ε (.root I s) : Set (Fin (K + 1)))).toReal) ≤ 1 at h
    rw [Finset.sum_coe_sort S (fun s => (eVariationOn (pieceValue ρ ε μ (.root I s))
      (pieceDom ρ ε (.root I s) : Set (Fin (K + 1)))).toReal)] at h
    simpa [rootPieces, List.map_map, Function.comp_def, S] using h
  · intro s q hq
    apply cell_coord_mem_buyerInterval ρ ε I I s q
      (Finset.mem_union.mpr (Or.inl s.property))
    exact pieceDom_mem_cell ρ ε (.root I s) q hq
  · intro s t hst
    apply buyerInterval_disjoint hK ρ ε I I s t
      (Finset.mem_union.mpr (Or.inl s.property)) (Finset.mem_union.mpr (Or.inl t.property))
    intro heq
    exact hst (Subtype.ext heq)

lemma edgePieces_variation_le (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I J : Node)
    (hI : 0 < I.2) (hJ : 0 < J.2) (hsub : hull K J ⊆ hull K I) :
    ((edgePieces ρ ε (I, J)).map (fun p =>
      (eVariationOn (pieceValue ρ ε μ p) (pieceDom ρ ε p : Set (Fin (K + 1)))).toReal)).sum ≤
      μ.real (hull K I ×ˢ (univ : Set ℝ)) := by
  classical
  let S := startsThrough ρ ε I K ∪ startsThrough ρ ε J K
  have h := sum_trade_difference_variation_le (ι := {s // s ∈ S}) μ hK
    (fun s => pieceDom ρ ε (.edge I J s))
    (fun s => (repAt ρ ε J s : ℝ) / K) (fun s => (repAt ρ ε I s : ℝ) / K)
    ((I.1 : ℝ) / K) (((I.1 + I.2 - 1 : ℕ) : ℝ) / K)
    (fun s => (s : ℕ) / (K : ℝ)) (fun s => (cellEnd ρ ε I J s : ℝ) / K)
    (fun s => hsub (repAt_mem_hull ρ ε J s hJ))
    (fun s => repAt_mem_hull ρ ε I s hI) ?_ ?_
  · change (∑ s : S, (eVariationOn (pieceValue ρ ε μ (.edge I J s))
        (pieceDom ρ ε (.edge I J s) : Set (Fin (K + 1)))).toReal) ≤ _ at h
    rw [Finset.sum_coe_sort S (fun s => (eVariationOn (pieceValue ρ ε μ (.edge I J s))
      (pieceDom ρ ε (.edge I J s) : Set (Fin (K + 1)))).toReal)] at h
    simpa [edgePieces, List.map_map, Function.comp_def, S, hull] using h
  · intro s q hq
    apply cell_coord_mem_buyerInterval ρ ε I J s q s.property
    exact pieceDom_mem_cell ρ ε (.edge I J s) q hq
  · intro s t hst
    apply buyerInterval_disjoint hK ρ ε I J s t s.property t.property
    intro heq
    exact hst (Subtype.ext heq)

lemma flatMap_variation_sum_le {α : Type*} (es : List α) (f : α → List Piece)
    (w : α → ℝ) (v : Piece → ℝ)
    (h : ∀ e ∈ es, ((f e).map v).sum ≤ w e) :
    ((es.flatMap f).map v).sum ≤ (es.map w).sum := by
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      exact add_le_add (h e (by simp)) (ih (fun e he => h e (by simp [he])))

lemma pieces_variation_le (μ : Measure (ℝ × ℝ)) (hμ : IsValLaw μ)
    (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (ε : ℝ) (d : ℕ)
    (hd : K + 1 ≤ 2 ^ d) :
    ((pieces ρ ε d (0, K + 1)).map (fun p =>
      (eVariationOn (pieceValue ρ ε μ p) (pieceDom ρ ε p : Set (Fin (K + 1)))).toReal)).sum ≤
      1 + 2 * ((d : ℝ) + 1) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hroot := rootPieces_variation_le μ hK ρ ε (0, K + 1)
  have he := flatMap_variation_sum_le (edges d (0, K + 1)) (edgePieces ρ ε)
    (fun e => μ.real (hull K e.1 ×ˢ (univ : Set ℝ)))
    (fun p => (eVariationOn (pieceValue ρ ε μ p) (pieceDom ρ ε p : Set (Fin (K + 1)))).toReal) ?_
  · have hparents := sum_edges_parent_le d (0, K + 1)
      (fun I => μ.real (hull K I ×ˢ (univ : Set ℝ))) (fun _ => ENNReal.toReal_nonneg)
    have hnodes := sum_node_hull_mass_le μ hK d (0, K + 1) hd
    have hmass : μ.real (hull K (0, K + 1) ×ˢ (univ : Set ℝ)) ≤ 1 := measureReal_le_one
    have hnodebound : ((nodes d (0, K + 1)).map
        (fun I => μ.real (hull K I ×ˢ (univ : Set ℝ)))).sum ≤ (d : ℝ) + 1 := by
      have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
      exact hnodes.trans (by nlinarith)
    simp only [pieces, List.map_append, List.sum_append]
    linarith
  · intro e he
    obtain ⟨hI, hJ, hsub⟩ := edges_valid hK d (0, K + 1) (by omega) e he
    exact edgePieces_variation_le μ hK ρ ε e.1 e.2 hI hJ hsub

end BilateralProfit.Estimation

namespace BilateralProfit.TradeFacts

open MeasureTheory

theorem nuMeas_univ (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] :
    nuMeas μ Set.univ = 3 := by
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    constructor
    simp [Measure.restrict_apply, Real.volume_Icc]
  have hvolume : (volume.restrict (Set.Icc (0 : ℝ) 1)) Set.univ = 1 := by
    simp [Measure.restrict_apply, Real.volume_Icc]
  have hfst : (μ.map Prod.fst) Set.univ = 1 := by
    rw [Measure.map_apply measurable_fst MeasurableSet.univ]
    simp
  have hsnd : (μ.map Prod.snd) Set.univ = 1 := by
    rw [Measure.map_apply measurable_snd MeasurableSet.univ]
    simp
  have hfirst : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (μ.map Prod.snd)) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, hvolume, hsnd, mul_one]
  have hsecond : ((μ.map Prod.fst).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, hfst, hvolume, mul_one]
  norm_num [nuMeas, hfirst, hsecond]

theorem nuMeas_margLaw_univ {K : ℕ} (hK : 0 < K) (ρ : Grid K × Act K → ℝ)
    (hρ : IsDist ρ) : nuMeas (margLaw ρ) Set.univ = 3 := by
  letI : IsProbabilityMeasure (margLaw ρ) := (margLaw_isValLaw hK ρ hρ).1
  exact nuMeas_univ _

end BilateralProfit.TradeFacts

namespace BilateralProfit.Estimation

/-- The directed edges on the route to seller coordinate `p`, with depth fuel `n`. -/
def routeEdges : ℕ → Node → ℕ → List (Node × Node)
  | 0, _, _ => []
  | n + 1, I, p =>
      if I.2 ≤ 1 then []
      else if p < I.1 + I.2 / 2 then
        (I, left I) :: routeEdges n (left I) p
      else (I, right I) :: routeEdges n (right I) p

lemma route_mem_edges (n : ℕ) (I : Node) (p : ℕ) {e : Node × Node}
    (he : e ∈ routeEdges n I p) : e ∈ edges n I := by
  induction n generalizing I with
  | zero => simp [routeEdges] at he
  | succ n ih =>
      simp only [routeEdges] at he
      simp only [edges]
      split_ifs at he ⊢ with hsmall hside
      · simp at he
      · rcases List.mem_cons.mp he with rfl | he
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_left _ (ih (left I) he)))
      · rcases List.mem_cons.mp he with rfl | he
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_right _ (ih (right I) he)))

lemma route_length_le (n : ℕ) (I : Node) (p : ℕ) :
    (routeEdges n I p).length ≤ n := by
  induction n generalizing I with
  | zero => simp [routeEdges]
  | succ n ih =>
      simp only [routeEdges]
      split_ifs with hsmall hside
      · simp
      · simpa only [List.length_cons] using Nat.succ_le_succ (ih (left I))
      · simpa only [List.length_cons] using Nat.succ_le_succ (ih (right I))

lemma route_bounds (n : ℕ) (I : Node) (p : ℕ)
    (hp : I.1 ≤ p ∧ p < I.1 + I.2) {e : Node × Node}
    (he : e ∈ routeEdges n I p) :
    I.1 ≤ e.1.1 ∧ e.1.1 ≤ p ∧ p < e.1.1 + e.1.2 ∧ e.1.1 + e.1.2 ≤ I.1 + I.2 ∧
      I.1 ≤ e.2.1 ∧ e.2.1 ≤ p ∧ p < e.2.1 + e.2.2 ∧ e.2.1 + e.2.2 ≤ I.1 + I.2 := by
  induction n generalizing I with
  | zero => simp [routeEdges] at he
  | succ n ih =>
      simp only [routeEdges] at he
      split_ifs at he with hsmall hside
      · simp at he
      · have hpchild : (left I).1 ≤ p ∧ p < (left I).1 + (left I).2 := by
          dsimp [left]; exact ⟨hp.1, hside⟩
        rcases List.mem_cons.mp he with rfl | he
        · dsimp [left] at hpchild ⊢
          omega
        · obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := ih (left I) hpchild he
          dsimp [left] at h1 h4 h5 h8
          exact ⟨by omega,h2,h3,by omega,by omega,h6,h7,by omega⟩
      · have hpchild : (right I).1 ≤ p ∧ p < (right I).1 + (right I).2 := by
          dsimp [right]; omega
        rcases List.mem_cons.mp he with rfl | he
        · dsimp [right] at hpchild ⊢
          omega
        · obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := ih (right I) hpchild he
          dsimp [right] at h1 h4 h5 h8
          exact ⟨by omega,h2,h3,by omega,by omega,h6,h7,by omega⟩

lemma route_telescope (n : ℕ) (I : Node) (p : ℕ) (f : Node → ℝ)
    (hp : I.1 ≤ p ∧ p < I.1 + I.2) (hlen : I.2 ≤ 2 ^ n) :
    f I + ((routeEdges n I p).map (fun e => f e.2 - f e.1)).sum = f (p, 1) := by
  induction n generalizing I with
  | zero =>
      have hlen1 : I.2 = 1 := by simp only [pow_zero] at hlen; omega
      have hlo : I.1 = p := by omega
      have hI : I = (p, 1) := Prod.ext hlo hlen1
      simp [routeEdges, hI]
  | succ n ih =>
      simp only [routeEdges]
      split_ifs with hsmall hside
      · have hlen1 : I.2 = 1 := by omega
        have hlo : I.1 = p := by omega
        have hI : I = (p, 1) := Prod.ext hlo hlen1
        simp [hI]
      · have hpchild : (left I).1 ≤ p ∧ p < (left I).1 + (left I).2 := by
          dsimp [left]; exact ⟨hp.1, hside⟩
        have hc := ih (left I) hpchild (halves_le_pow I n hlen).1
        simp only [List.map_cons, List.sum_cons]
        linarith
      · have hpchild : (right I).1 ≤ p ∧ p < (right I).1 + (right I).2 := by
          dsimp [right]; omega
        have hc := ih (right I) hpchild (halves_le_pow I n hlen).2
        simp only [List.map_cons, List.sum_cons]
        linarith

lemma list_sum_error {α : Type} (es : List α) (f g : α → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (herror : ∀ e ∈ es, |f e - g e| ≤ δ) :
    |(es.map f).sum - (es.map g).sum| ≤ (es.length : ℝ) * δ := by
  induction es with
  | nil => simp
  | cons e es ih =>
      have he := herror e (by simp)
      have hs := ih (fun a ha => herror a (by simp [ha]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        _ = |(f e - g e) + ((es.map f).sum - (es.map g).sum)| := by congr 1; ring
        _ ≤ |f e - g e| + |(es.map f).sum - (es.map g).sum| := abs_add_le _ _
        _ ≤ _ := by nlinarith

/-- Uniform accuracy of each telescoping term gives uniform accuracy of the reconstruction. -/
lemma route_reconstruction_error (n : ℕ) (I : Node) (p : ℕ) (f : Node → ℝ)
    (hp : I.1 ≤ p ∧ p < I.1 + I.2) (hlen : I.2 ≤ 2 ^ n)
    (rootEst : ℝ) (edgeEst : Node × Node → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hroot : |rootEst - f I| ≤ δ)
    (hedge : ∀ e ∈ routeEdges n I p, |edgeEst e - (f e.2 - f e.1)| ≤ δ) :
    |rootEst + ((routeEdges n I p).map edgeEst).sum - f (p, 1)| ≤
      ((n : ℝ) + 1) * δ := by
  have htel := route_telescope n I p f hp hlen
  have herr := list_sum_error (routeEdges n I p) edgeEst (fun e => f e.2 - f e.1) δ hδ hedge
  have hcount : ((routeEdges n I p).length : ℝ) ≤ n := by exact_mod_cast route_length_le n I p
  calc
    _ = |(rootEst - f I) + (((routeEdges n I p).map edgeEst).sum -
        ((routeEdges n I p).map (fun e => f e.2 - f e.1)).sum)| := by
      congr 1
      linarith
    _ ≤ |rootEst - f I| + |((routeEdges n I p).map edgeEst).sum -
        ((routeEdges n I p).map (fun e => f e.2 - f e.1)).sum| := abs_add_le _ _
    _ ≤ _ := by nlinarith

end BilateralProfit.Estimation

namespace BilateralProfit.Estimation

open MeasureTheory

variable {K : ℕ}

noncomputable def rootPieceAt (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) (q : ℕ) : Piece :=
  .root I (blockStart ρ ε I.1 I.2 q)

noncomputable def edgePieceAt (ρ : Grid K × Act K → ℝ) (ε : ℝ) (e : Node × Node) (q : ℕ) : Piece :=
  .edge e.1 e.2 (max (blockStart ρ ε e.1.1 e.1.2 q) (blockStart ρ ε e.2.1 e.2.2 q))

lemma start_mem_full (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node) (q : ℕ) (hq : q ≤ K) :
    blockStart ρ ε I.1 I.2 q ∈ startsThrough ρ ε I K := by
  simp only [startsThrough, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le ((SellerFacts.blockStart_le ρ ε I.1 I.2 q).trans hq),
    blockStart_idem ρ ε I.1 I.2 q⟩

lemma rootPieceAt_mem (ρ : Grid K × Act K → ℝ) (ε : ℝ) (d : ℕ) (I : Node)
    (q : ℕ) (hq : q ≤ K) : rootPieceAt ρ ε I q ∈ pieces ρ ε d I := by
  apply List.mem_append_left
  simp only [rootPieces, rootPieceAt, List.mem_map, Finset.mem_toList]
  exact ⟨_, start_mem_full ρ ε I q hq, rfl⟩

lemma edgePieceAt_mem (ρ : Grid K × Act K → ℝ) (ε : ℝ) (d : ℕ) (I : Node)
    (e : Node × Node) (he : e ∈ edges d I) (q : ℕ) (hq : q ≤ K) :
    edgePieceAt ρ ε e q ∈ pieces ρ ε d I := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨e, he, ?_⟩
  simp only [edgePieces, edgePieceAt, List.mem_map, Finset.mem_toList]
  refine ⟨_, ?_, rfl⟩
  rcases le_total (blockStart ρ ε e.1.1 e.1.2 q) (blockStart ρ ε e.2.1 e.2.2 q) with h | h
  · rw [max_eq_right h]
    exact Finset.mem_union_right _ (start_mem_full ρ ε e.2 q hq)
  · rw [max_eq_left h]
    exact Finset.mem_union_left _ (start_mem_full ρ ε e.1 q hq)

lemma rootPieceAt_cell (ρ : Grid K × Act K → ℝ) (ε : ℝ) (I : Node)
    (q : ℕ) (hq : q ≤ K) :
    q ∈ cell ρ ε (rootPieceAt ρ ε I q).parent (rootPieceAt ρ ε I q).child
      (rootPieceAt ρ ε I q).start := by
  apply (cell_mem ρ ε I I _ q).mpr
  exact ⟨hq, (blockStart_idem ρ ε I.1 I.2 q).symm, (blockStart_idem ρ ε I.1 I.2 q).symm⟩

lemma edgePieceAt_cell (ρ : Grid K × Act K → ℝ) (ε : ℝ) (e : Node × Node)
    (q : ℕ) (hq : q ≤ K) :
    q ∈ cell ρ ε (edgePieceAt ρ ε e q).parent (edgePieceAt ρ ε e q).child
      (edgePieceAt ρ ε e q).start := by
  have h := intersection_start ρ ε e.1 e.2 q
  exact (cell_mem ρ ε e.1 e.2 _ q).mpr ⟨hq, h.2.1.symm, h.2.2.1.symm⟩

lemma repAt_singleton (ρ : Grid K × Act K → ℝ) (ε : ℝ) (p q : ℕ) :
    repAt ρ ε (p, 1) q = p := by
  have h := SellerFacts.rep_mem ρ p 1 (blockStart ρ ε p 1 q) (by omega)
  change p ≤ repAt ρ ε (p, 1) q ∧ repAt ρ ε (p, 1) q < p + 1 at h
  omega

lemma rootPieceAt_value (ρ : Grid K × Act K → ℝ) (ε : ℝ) (μ : Measure (ℝ × ℝ))
    (I : Node) (q : Fin (K + 1)) :
    pieceValue ρ ε μ (rootPieceAt ρ ε I q) q =
      Ptrade μ ((repAt ρ ε I q : ℝ) / K, (q : ℝ) / K) / 2 := by
  simp only [rootPieceAt, pieceValue, repAt, blockStart_idem]

lemma edgePieceAt_value (ρ : Grid K × Act K → ℝ) (ε : ℝ) (μ : Measure (ℝ × ℝ))
    (e : Node × Node) (q : Fin (K + 1)) :
    pieceValue ρ ε μ (edgePieceAt ρ ε e q) q =
      (Ptrade μ ((repAt ρ ε e.2 q : ℝ) / K, (q : ℝ) / K) -
        Ptrade μ ((repAt ρ ε e.1 q : ℝ) / K, (q : ℝ) / K)) / 2 := by
  have h := intersection_start ρ ε e.1 e.2 q
  simp only [edgePieceAt, pieceValue]
  rw [repAt_eq_of_block_eq ρ ε e.1 _ q h.2.1,
    repAt_eq_of_block_eq ρ ε e.2 _ q h.2.2.1]

noncomputable def selectedEstimate (L : List Piece)
    (est : Fin L.length → Fin (K + 1) → ℝ) (p : Piece) (q : Fin (K + 1)) : ℝ :=
  if h : p ∈ L then est ⟨L.idxOf p, List.idxOf_lt_length_of_mem h⟩ q else 0

lemma selectedEstimate_error (ρ : Grid K × Act K → ℝ) (ε : ℝ) (μ : Measure (ℝ × ℝ))
    (L : List Piece) (est : Fin L.length → Fin (K + 1) → ℝ) (δ : ℝ)
    (hest : ∀ i : Fin L.length, ∀ q ∈ pieceDom ρ ε L[i],
      |est i q - pieceValue ρ ε μ L[i] q| ≤ δ)
    (p : Piece) (hp : p ∈ L) (q : Fin (K + 1)) (hq : q ∈ pieceDom ρ ε p) :
    |selectedEstimate L est p q - pieceValue ρ ε μ p q| ≤ δ := by
  classical
  rw [selectedEstimate, dif_pos hp]
  have heq : L[L.idxOf p]'(List.idxOf_lt_length_of_mem hp) = p := List.getElem_idxOf _
  have hi := hest ⟨L.idxOf p, List.idxOf_lt_length_of_mem hp⟩ q
  simpa only [Fin.getElem_fin, heq] using hi (by simpa only [Fin.getElem_fin, heq] using hq)

noncomputable def reconstruct (ρ : Grid K × Act K → ℝ) (ε : ℝ) (d : ℕ)
    (est : Fin (pieces ρ ε d (0, K + 1)).length → Fin (K + 1) → ℝ) (a : Act K) : ℝ :=
  ((pt K a.1).2 - (pt K a.1).1) * (2 *
    (selectedEstimate (pieces ρ ε d (0, K + 1)) est (rootPieceAt ρ ε (0, K + 1) a.1.2) a.1.2 +
      ((routeEdges d (0, K + 1) a.1.1).map (fun e =>
        selectedEstimate (pieces ρ ε d (0, K + 1)) est (edgePieceAt ρ ε e a.1.2) a.1.2)).sum))

lemma reconstruct_error (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (ε : ℝ) (hε : 0 ≤ ε) (μ : Measure (ℝ × ℝ)) (d : ℕ) (hd : K + 1 ≤ 2 ^ d)
    (est : Fin (pieces ρ ε d (0, K + 1)).length → Fin (K + 1) → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hest : ∀ i : Fin (pieces ρ ε d (0, K + 1)).length,
      ∀ q ∈ pieceDom ρ ε (pieces ρ ε d (0, K + 1))[i],
        |est i q - pieceValue ρ ε μ (pieces ρ ε d (0, K + 1))[i] q| ≤ δ)
    (a : Act K) (ha : gapStar ρ a ≤ ε) :
    |reconstruct ρ ε d est a - muP μ (pt K a.1)| ≤ 2 * ((d : ℝ) + 1) * δ := by
  classical
  let I : Node := (0, K + 1)
  let L := pieces ρ ε d I
  let f := fun J : Node => Ptrade μ ((repAt ρ ε J a.1.2 : ℝ) / K, (a.1.2 : ℝ) / K) / 2
  let rootEst := selectedEstimate L est (rootPieceAt ρ ε I a.1.2) a.1.2
  let edgeEst := fun e => selectedEstimate L est (edgePieceAt ρ ε e a.1.2) a.1.2
  have hp : I.1 ≤ (a.1.1 : ℕ) ∧ (a.1.1 : ℕ) < I.1 + I.2 := by dsimp [I]; omega
  have hq : (a.1.2 : ℕ) ≤ K := by omega
  have hroot : |rootEst - f I| ≤ δ := by
    have hdom := target_mem_pieceDom hK ρ hρ ε hε a ha (rootPieceAt ρ ε I a.1.2)
      hp hp (by simp [I, rootPieceAt, Piece.parent]) (by simp [I, rootPieceAt, Piece.child])
      (rootPieceAt_cell ρ ε I a.1.2 hq)
    have hh := selectedEstimate_error ρ ε μ L est δ hest (rootPieceAt ρ ε I a.1.2)
      (rootPieceAt_mem ρ ε d I a.1.2 hq) a.1.2 hdom
    simpa only [rootEst, f, rootPieceAt_value] using hh
  have hedge : ∀ e ∈ routeEdges d I a.1.1, |edgeEst e - (f e.2 - f e.1)| ≤ δ := by
    intro e he
    obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := route_bounds d I a.1.1 hp he
    simp only [I, zero_add] at h4 h8
    have hdom := target_mem_pieceDom hK ρ hρ ε hε a ha (edgePieceAt ρ ε e a.1.2)
      ⟨h2,h3⟩ ⟨h6,h7⟩ h4 h8 (edgePieceAt_cell ρ ε e a.1.2 hq)
    have hh := selectedEstimate_error ρ ε μ L est δ hest (edgePieceAt ρ ε e a.1.2)
      (edgePieceAt_mem ρ ε d I e (route_mem_edges d I a.1.1 he) a.1.2 hq) a.1.2 hdom
    rw [edgePieceAt_value] at hh
    convert hh using 1 <;> dsimp [edgeEst, f] <;> ring
  have herr := route_reconstruction_error d I a.1.1 f hp hd rootEst edgeEst δ hδ hroot hedge
  have hleaf : f ((a.1.1 : ℕ), 1) = Ptrade μ (pt K a.1) / 2 := by
    simp only [f, repAt_singleton, pt]
  rw [hleaf] at herr
  have hspread := TradeFacts.spread_mem hK a
  have heq : reconstruct ρ ε d est a - muP μ (pt K a.1) =
      ((pt K a.1).2 - (pt K a.1).1) *
        (2 * (rootEst + ((routeEdges d I a.1.1).map edgeEst).sum - Ptrade μ (pt K a.1) / 2)) := by
    dsimp [reconstruct, muP, rootEst, edgeEst, L, I]
    ring
  rw [heq, abs_mul, abs_of_nonneg hspread.1, abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 1 * (2 * (((d : ℝ) + 1) * δ)) :=
      mul_le_mul hspread.2 (mul_le_mul_of_nonneg_left herr (by norm_num))
        (by positivity) (by norm_num)
    _ = _ := by ring

theorem reconstruct_accuracy (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (ε : ℝ) (hε : 0 < ε) (μ : Measure (ℝ × ℝ)) (d : ℕ) (hd : K + 1 ≤ 2 ^ d)
    (est : Fin (pieces ρ ε d (0, K + 1)).length → Fin (K + 1) → ℝ)
    (hest : ∀ i : Fin (pieces ρ ε d (0, K + 1)).length,
      ∀ q ∈ pieceDom ρ ε (pieces ρ ε d (0, K + 1))[i],
        |est i q - pieceValue ρ ε μ (pieces ρ ε d (0, K + 1))[i] q| ≤
          ε / (8 * ((d : ℝ) + 1))) :
    ∀ a, gapStar ρ a ≤ ε → |reconstruct ρ ε d est a - muP μ (pt K a.1)| ≤ ε / 4 := by
  intro a ha
  have h := reconstruct_error hK ρ hρ ε hε.le μ d hd est
    (ε / (8 * ((d : ℝ) + 1))) (by positivity) hest a ha
  have hdpos : 0 < (d : ℝ) + 1 := by positivity
  have heq : 2 * ((d : ℝ) + 1) * (ε / (8 * ((d : ℝ) + 1))) = ε / 4 := by
    field_simp [hdpos.ne']
    ring
  exact heq ▸ h

end BilateralProfit.Estimation

namespace BilateralProfit.Estimation

private theorem budget_log2_depth (Y : ℕ) (hY : 0 < Y) :
    (Nat.log2 Y : ℝ) + 2 ≤ 4 * Real.log (2 * Y) := by
  have hYr : (0 : ℝ) < Y := by exact_mod_cast hY
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hn := Real.log2_le_logb Y
  rw [Real.logb] at hn
  have hn' := (le_div_iff₀ hlog2pos).mp hn
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hYr.ne']
  have hn0 : (0 : ℝ) ≤ Nat.log2 Y := by positivity
  nlinarith

/-- The concrete family bounds and Claim 4.10's query bound imply the query
complexity in localized estimation, including the factor two for difference
queries. -/
theorem estimation_budget (C : ℝ) (hC : 0 ≤ C) (K : ℕ) (hK : 2 ≤ K)
    (ε : ℝ) (hε : 0 < ε) (G N : ℕ)
    (hGlinear : (G : ℝ) ≤ 6 * ((K : ℝ) + 1) + 9 * ((Nat.log2 (K + 1) : ℝ) + 2) / ε)
    (hGquad : (G : ℝ) ≤ 6 * ((K : ℝ) + 1) ^ 2)
    (hN : (N : ℝ) ≤
      C * Real.log (2 * (G : ℝ) * ((K : ℝ) + 1) / (1 / 10)) /
        (ε / (8 * ((Nat.log2 (K + 1) : ℝ) + 2))) ^ 2 *
          ((G : ℝ) + (1 + 2 * ((Nat.log2 (K + 1) : ℝ) + 2)) /
            (ε / (8 * ((Nat.log2 (K + 1) : ℝ) + 2))) * Real.log (2 * ((K : ℝ) + 1)))) :
    2 * (N : ℝ) ≤ (10 ^ 12 : ℝ) * C * Real.log K ^ 3 *
      ((K : ℝ) / ε ^ 2 + Real.log K ^ 3 / ε ^ 3) := by
  let L := Real.log (K : ℝ)
  let D := (Nat.log2 (K + 1) : ℝ) + 2
  let A := Real.log (2 * (G : ℝ) * ((K : ℝ) + 1) / (1 / 10))
  let B := Real.log (2 * ((K : ℝ) + 1))
  let α := ε / (8 * D)
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hK1pos : (0 : ℝ) < (K : ℝ) + 1 := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlog2L : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hKr
  have hL : (1 / 2 : ℝ) ≤ L := hlog2.trans hlog2L
  have hL0 : 0 ≤ L := by linarith
  have hD1 : 1 ≤ D := by
    dsimp [D]
    have hn0 : 0 ≤ (Nat.log2 (K + 1) : ℝ) := Nat.cast_nonneg _
    linarith
  have hDpos : 0 < D := by linarith
  have hα : 0 < α := by dsimp [α]; positivity
  have hlogK1 : Real.log ((K : ℝ) + 1) ≤ 2 * L := by
    have h := Real.log_le_log hK1pos (show (K : ℝ) + 1 ≤ 2 * K by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hKpos.ne'] at h
    dsimp [L] at hlog2L ⊢
    linarith
  have hB : B ≤ 3 * L := by
    dsimp [B]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hK1pos.ne']
    linarith
  have hB0 : 0 ≤ B := Real.log_nonneg (by nlinarith)
  have hD : D ≤ 12 * L := by
    have h := budget_log2_depth (K + 1) (by omega)
    simp only [Nat.cast_add, Nat.cast_one] at h
    change D ≤ 4 * B at h
    linarith
  have hDsq : D ^ 2 ≤ 144 * L ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 12 * L - D by linarith)
      (show 0 ≤ 12 * L + D by linarith)]
  have hLcube : L ≤ 4 * L ^ 3 := by
    have hs : 0 ≤ 4 * L ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg hL0 hs]
  by_cases hGzero : G = 0
  · have hNzero : (N : ℝ) ≤ 0 := by simpa [hGzero] using hN
    have hRHS : 0 ≤ (10 ^ 12 : ℝ) * C * Real.log K ^ 3 *
        ((K : ℝ) / ε ^ 2 + Real.log K ^ 3 / ε ^ 3) := by
      change 0 ≤ (10 ^ 12 : ℝ) * C * L ^ 3 * ((K : ℝ) / ε ^ 2 + L ^ 3 / ε ^ 3)
      positivity
    linarith
  · have hGpos : (0 : ℝ) < G := by exact_mod_cast (Nat.pos_of_ne_zero hGzero)
    have hA : A ≤ 256 * L := by
      have harg : 2 * (G : ℝ) * ((K : ℝ) + 1) / (1 / 10) ≤
          120 * ((K : ℝ) + 1) ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hGquad hK1pos.le]
      have hlog120 : Real.log (120 : ℝ) ≤ 119 := by
        have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 120 by norm_num)
        norm_num at hh
        exact hh
      calc
        A ≤ Real.log (120 * ((K : ℝ) + 1) ^ 3) :=
          Real.log_le_log (by positivity) harg
        _ = Real.log 120 + 3 * Real.log ((K : ℝ) + 1) := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          norm_num
        _ ≤ 256 * L := by linarith
    have hnum : 9 * D + 72 * D ^ 2 * L ≤ 10800 * L ^ 3 := by
      have hmul := mul_le_mul_of_nonneg_right hDsq hL0
      nlinarith
    have hinner : (G : ℝ) + (1 + 2 * D) / α * B ≤
        12 * K + 10800 * L ^ 3 / ε := by
      have hprod : (1 + 2 * D) * B ≤ (3 * D) * (3 * L) :=
        mul_le_mul (by linarith) hB hB0 (by positivity)
      have hterm : (1 + 2 * D) / α * B ≤ 72 * D ^ 2 * L / ε := by
        calc
          _ = (8 * D / ε) * ((1 + 2 * D) * B) := by dsimp [α]; field_simp [hε.ne', hDpos.ne']
          _ ≤ (8 * D / ε) * ((3 * D) * (3 * L)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
          _ = _ := by ring
      calc
        _ ≤ (6 * ((K : ℝ) + 1) + 9 * D / ε) + 72 * D ^ 2 * L / ε :=
          add_le_add hGlinear hterm
        _ = 6 * ((K : ℝ) + 1) + (9 * D + 72 * D ^ 2 * L) / ε := by ring
        _ ≤ _ := add_le_add (by linarith)
          (div_le_div_of_nonneg_right hnum hε.le)
    have hout : C * A / α ^ 2 ≤ 2359296 * C * L ^ 3 / ε ^ 2 := by
      have hp : A * D ^ 2 ≤ (256 * L) * (144 * L ^ 2) :=
        mul_le_mul hA hDsq (sq_nonneg D) (by positivity)
      calc
        _ = (64 * C / ε ^ 2) * (A * D ^ 2) := by
          dsimp [α]
          field_simp [hε.ne', hDpos.ne']
          ring
        _ ≤ (64 * C / ε ^ 2) * ((256 * L) * (144 * L ^ 2)) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        _ = _ := by ring
    have hinner0 : 0 ≤ (G : ℝ) + (1 + 2 * D) / α * B := by positivity
    change (N : ℝ) ≤ C * A / α ^ 2 * ((G : ℝ) + (1 + 2 * D) / α * B) at hN
    have hNfinal : (N : ℝ) ≤ (2359296 * C * L ^ 3 / ε ^ 2) *
        (12 * K + 10800 * L ^ 3 / ε) := by
      exact hN.trans ((mul_le_mul_of_nonneg_right hout hinner0).trans
        (mul_le_mul_of_nonneg_left hinner (by positivity)))
    change 2 * (N : ℝ) ≤ (10 ^ 12 : ℝ) * C * L ^ 3 * ((K : ℝ) / ε ^ 2 + L ^ 3 / ε ^ 3)
    calc
      _ ≤ 2 * ((2359296 * C * L ^ 3 / ε ^ 2) * (12 * K + 10800 * L ^ 3 / ε)) := by linarith
      _ = 56623104 * (C * L ^ 3 * K / ε ^ 2) +
          50960793600 * (C * L ^ 6 / ε ^ 3) := by ring
      _ ≤ (10 ^ 12 : ℝ) * (C * L ^ 3 * K / ε ^ 2) +
          (10 ^ 12 : ℝ) * (C * L ^ 6 / ε ^ 3) := by
        exact add_le_add (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
          (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
      _ = _ := by ring

end BilateralProfit.Estimation

namespace BilateralProfit.Estimation

open MeasureTheory

variable {K : ℕ}

lemma sum_fin_get_eq_sum_map {A : Type} (l : List A) (f : A → ℝ) :
    (∑ i : Fin l.length, f l[(i : ℕ)]) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map l f)

lemma family_count_bounds (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ)
    (ε : ℝ) (hε : 0 < ε) :
    ((pieces ρ ε (depth K) (0, K + 1)).length : ℝ) ≤
        6 * (K + 1) + 9 * ((depth K : ℝ) + 1) / ε ∧
      (pieces ρ ε (depth K) (0, K + 1)).length ≤ 2 * (K + 1) ^ 2 := by
  have hμ := TradeFacts.margLaw_isValLaw hK ρ hρ
  letI : IsProbabilityMeasure (margLaw ρ) := hμ.1
  letI : IsFiniteMeasure (nuMeas (margLaw ρ)) := SellerFacts.nuMeas_finite (margLaw ρ)
  have hν := TradeFacts.nuMeas_margLaw_univ hK ρ hρ
  have hmass : (nuMeas (margLaw ρ)).real (strip K (0, K + 1) ×ˢ Set.univ) ≤ 3 := by
    have hle := ENNReal.toReal_mono (by finiteness : nuMeas (margLaw ρ) Set.univ ≠ ⊤)
      (measure_mono (Set.subset_univ (strip K (0, K + 1) ×ˢ Set.univ)))
    simpa only [hν, ENNReal.toReal_ofNat, Measure.real] using hle
  have hG := pieces_length_le hK ρ ε hε (depth K) (0, K + 1) (by simp) (root_le_pow_depth K)
  refine ⟨?_, root_pieces_quadratic ρ ε (depth K)⟩
  have hd : 0 ≤ (depth K : ℝ) + 1 := by positivity
  have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hd) hε.le
  dsimp only [Prod.snd] at hG
  push_cast at hG
  calc
    _ ≤ 3 * (2 * (K + 1) + (((depth K : ℝ) + 1) * 3) / ε) :=
      hG.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hm) (by norm_num))
    _ = _ := by ring

lemma family_variation_bound (μ : Measure (ℝ × ℝ)) (hμ : IsValLaw μ)
    (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (ε : ℝ) :
    ∑ i : Fin (pieces ρ ε (depth K) (0, K + 1)).length,
      (eVariationOn (pieceValue ρ ε μ (pieces ρ ε (depth K) (0, K + 1))[i])
        ↑(pieceDom ρ ε (pieces ρ ε (depth K) (0, K + 1))[i])).toReal ≤
      1 + 2 * ((depth K : ℝ) + 1) := by
  change (∑ i : Fin (pieces ρ ε (depth K) (0, K + 1)).length,
    (fun p => (eVariationOn (pieceValue ρ ε μ p) ↑(pieceDom ρ ε p)).toReal)
      (pieces ρ ε (depth K) (0, K + 1))[(i : ℕ)]) ≤ _
  rw [sum_fin_get_eq_sum_map (pieces ρ ε (depth K) (0, K + 1))
    (fun p => (eVariationOn (pieceValue ρ ε μ p) ↑(pieceDom ρ ε p)).toReal)]
  exact pieces_variation_le μ hμ hK ρ ε (depth K) (root_le_pow_depth K)

lemma pieces_length_pos (ρ : Grid K × Act K → ℝ) (ε : ℝ) (d : ℕ) :
    0 < (pieces ρ ε d (0, K + 1)).length := by
  have h : Piece.root (0, K + 1) 0 ∈ pieces ρ ε d (0, K + 1) := by
    apply List.mem_append_left
    simp [rootPieces, startsThrough, blockStart]
  exact List.length_pos_of_mem h

/-- The complete localized estimator before the elementary logarithmic budget
simplification. `N` counts the half-scaled monotone-family queries; their
implementation uses at most `2*N` pricing queries on every path. -/
theorem localized_estimation_raw :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ, 2 ≤ K → ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ (R : QTree (Act K) (Act K → ℝ)) (N : ℕ),
          (N : ℝ) ≤ C * Real.log
            (20 * (pieces ρ ε (depth K) (0, K + 1)).length * (K + 1)) /
            (ε / (8 * ((depth K : ℝ) + 1))) ^ 2 *
            ((pieces ρ ε (depth K) (0, K + 1)).length +
              (1 + 2 * ((depth K : ℝ) + 1)) / (ε / (8 * ((depth K : ℝ) + 1))) *
                Real.log (2 * (K + 1))) ∧
          R.QueriesAtMost (2 * N) ∧ R.AllQueries (fun a => gapStar ρ a ≤ 2 * ε) ∧
          ∀ μ : Measure (ℝ × ℝ), IsValLaw μ →
            ∀ (c : ℝ) (obs : Act K → Measure ℝ), (∀ a, IsProbabilityMeasure (obs a)) →
              (∀ a, obs a (Set.Icc c (c + 2))ᶜ = 0) →
              (∀ a, ∫ r, r ∂(obs a) = Ptrade μ (pt K a.1)) →
              ENNReal.ofReal (9 / 10) ≤
                R.prob (fun a _ => obs a)
                  (fun est => ∀ a, gapStar ρ a ≤ ε → |est a - muP μ (pt K a.1)| ≤ ε / 4)
                  (fun _ => 0) := by
  classical
  obtain ⟨C, hC⟩ := claim_4_10
  refine ⟨|C|, abs_nonneg C, ?_⟩
  intro K hK ρ hρ ε hε hε1
  have hK0 : 0 < K := by omega
  let ps := pieces ρ ε (depth K) (0, K + 1)
  let ι := Fin ps.length
  let Y := Fin (K + 1)
  let dom : ι → Finset Y := fun i => pieceDom ρ ε ps[i]
  let D : ℝ := (depth K : ℝ) + 1
  let W : ℝ := 1 + 2 * D
  let α : ℝ := ε / (8 * D)
  have hD : 1 ≤ D := by dsimp [D]; linarith [Nat.cast_nonneg (α := ℝ) (depth K)]
  have hDpos : 0 < D := by linarith
  have hα : 0 < α := by dsimp [α]; positivity
  have hα1 : α < 1 := by
    dsimp [α]
    apply (div_lt_one (by positivity : 0 < 8 * D)).mpr
    linarith
  have hW : 0 ≤ W := by dsimp [W]; positivity
  obtain ⟨H, N, hN, hcap, hlegal, hprob⟩ :=
    hC ι Y dom W α (1 / 10) hW hα hα1 (by norm_num) (by norm_num)
  let spec : ι × Y → QuerySpec (Act K) := fun q => pieceSpec ρ ε ps[q.1] q.2
  let out : (ι → Y → ℝ) → Act K → ℝ := reconstruct ρ ε (depth K)
  let R := QTree.mapOutput out (QTree.substitute spec H)
  have hG : (1 : ℝ) ≤ ps.length := by
    exact_mod_cast pieces_length_pos ρ ε (depth K)
  have hY : (1 : ℝ) ≤ K + 1 := by linarith [Nat.cast_nonneg (α := ℝ) K]
  have hlog : 0 ≤ Real.log (20 * (ps.length : ℝ) * (K + 1)) := by
    apply Real.log_nonneg
    nlinarith
  have hlogY : 0 ≤ Real.log (2 * ((K : ℝ) + 1)) := by
    apply Real.log_nonneg
    linarith
  have hN' : (N : ℝ) ≤ |C| * Real.log (20 * (ps.length : ℝ) * (K + 1)) / α ^ 2 *
      ((ps.length : ℝ) + W / α * Real.log (2 * ((K : ℝ) + 1))) := by
    have hc : C * Real.log (20 * (ps.length : ℝ) * (K + 1)) / α ^ 2 *
        ((ps.length : ℝ) + W / α * Real.log (2 * ((K : ℝ) + 1))) ≤
        |C| * Real.log (20 * (ps.length : ℝ) * (K + 1)) / α ^ 2 *
          ((ps.length : ℝ) + W / α * Real.log (2 * ((K : ℝ) + 1))) := by
      gcongr
      exact le_abs_self C
    apply le_trans _ hc
    have hn0 : (N : ℝ) ≤ C * Real.log (2 * (ps.length : ℝ) * (K + 1) / (1 / 10)) / α ^ 2 *
        ((ps.length : ℝ) + W / α * Real.log (2 * ((K : ℝ) + 1))) := by
      simpa only [ι, Y, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hN
    have hr : 2 * (ps.length : ℝ) * (K + 1) / (1 / 10) = 20 * (ps.length : ℝ) * (K + 1) := by ring
    rw [hr] at hn0
    exact hn0
  refine ⟨R, N, ?_, ?_, ?_, ?_⟩
  · simpa only [R, ps, α, W, D, Nat.cast_add, Nat.cast_one] using hN'
  · exact QTree.queriesAtMost_mapOutput out _ (QTree.queriesAtMost_substitute spec H hcap)
  · apply QTree.allQueries_mapOutput out
    apply QTree.allQueries_substitute spec H
    exact QTree.allQueries_mono_pred H hlegal (fun q hq => pieceSpec_legal ρ ε ps[q.1] q.2 hq)
  · intro μ hμ c obs hobs hs hm
    letI : IsProbabilityMeasure μ := hμ.1
    let g : ι → Y → ℝ := fun i q => pieceValue ρ ε μ ps[i] q
    let highObs : ι × Y → ℕ → Measure ℝ := fun q _ => (spec q).law obs
    have hmono : ∀ i, MonotoneOn (g i) ↑(dom i) ∨ AntitoneOn (g i) ↑(dom i) := by
      intro i
      rcases pieceValue_monotone ρ ε μ ps[i] with h | h
      · exact Or.inl (h.monotoneOn _)
      · exact Or.inr (h.antitoneOn _)
    have hvar : ∑ i, (eVariationOn (g i) ↑(dom i)).toReal ≤ W :=
      family_variation_bound μ hμ hK0 ρ ε
    have hc : -2 ≤ c ∧ c ≤ 1 := ObservationFacts.offset_bounds obs hobs c hs (by
      intro a
      rw [hm a]
      exact ⟨TradeFacts.Ptrade_nonneg μ _, TradeFacts.Ptrade_le_one μ _⟩)
    have hh := hprob g (fun i y _ => pieceValue_mem ρ ε μ ps[i] y) hmono hvar (-1) highObs
      (fun i y _ _ => ObservationFacts.law_probability obs hobs (spec (i, y)))
      (fun i y _ _ => by simpa only [highObs, show (-1 : ℝ) + 4 = 3 by norm_num] using
        ObservationFacts.law_support obs hobs c hc hs (spec (i, y)))
      (fun i y hy _ => pieceLaw_mean ρ ε μ c obs hobs hs hm ps[i] y hy)
    have haccurate : ∀ est : ι → Y → ℝ,
        (∀ i, ∀ y ∈ dom i, |est i y - g i y| ≤ α) →
        ∀ a, gapStar ρ a ≤ ε → |out est a - muP μ (pt K a.1)| ≤ ε / 4 := by
      intro est hest
      exact reconstruct_accuracy hK0 ρ hρ ε hε μ (depth K) (root_le_pow_depth K) est hest
    change ENNReal.ofReal (9 / 10) ≤ (QTree.mapOutput out (QTree.substitute spec H)).prob
      (fun a _ => obs a) _ (fun _ => 0)
    rw [QTree.prob_mapOutput]
    calc
      _ ≤ H.prob highObs (fun est => ∀ i, ∀ y ∈ dom i, |est i y - g i y| ≤ α) (fun _ => 0) := by
        convert hh using 1 <;> norm_num
      _ ≤ H.prob highObs (fun est => ∀ a, gapStar ρ a ≤ ε →
          |out est a - muP μ (pt K a.1)| ≤ ε / 4) (fun _ => 0) :=
        QTree.prob_mono_output highObs H haccurate _
      _ ≤ _ := QTree.prob_substitute_lower spec H obs hobs _ _ _

end BilateralProfit.Estimation

namespace BilateralProfit

open MeasureTheory

/-- Lemma 4.8 with Remark 4.12, for the selected range `K ≥ 2`. -/
theorem cert_lemma_4_8 :
    ∃ C : ℝ, ∀ K : ℕ, 2 ≤ K → ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ (R : QTree (Act K) (Act K → ℝ)) (N : ℕ),
          (N : ℝ) ≤ C * Real.log K ^ 3 * ((K : ℝ) / ε ^ 2 + Real.log K ^ 3 / ε ^ 3) ∧
          R.QueriesAtMost N ∧ R.AllQueries (fun a => gapStar ρ a ≤ 2 * ε) ∧
          ∀ μ : Measure (ℝ × ℝ), IsValLaw μ →
            ∀ (c : ℝ) (obs : Act K → Measure ℝ), (∀ a, IsProbabilityMeasure (obs a)) →
              (∀ a, obs a (Set.Icc c (c + 2))ᶜ = 0) →
              (∀ a, ∫ r, r ∂(obs a) = Ptrade μ (pt K a.1)) →
              ENNReal.ofReal (9 / 10) ≤
                R.prob (fun a _ => obs a)
                  (fun est => ∀ a, gapStar ρ a ≤ ε → |est a - muP μ (pt K a.1)| ≤ ε / 4)
                  (fun _ => 0) := by
  obtain ⟨C, hC, hraw⟩ := Estimation.localized_estimation_raw
  refine ⟨10 ^ 12 * C, ?_⟩
  intro K hK ρ hρ ε hε hε1
  obtain ⟨R, N, hN, hcap, hlegal, hprob⟩ := hraw K hK ρ hρ ε hε hε1
  have hg := Estimation.family_count_bounds (by omega : 0 < K) ρ hρ ε hε
  let G := (Estimation.pieces ρ ε (Estimation.depth K) (0, K + 1)).length
  have hD : ((Estimation.depth K : ℝ) + 1) = (Nat.log2 (K + 1) : ℝ) + 2 := by
    simp only [Estimation.depth, Nat.cast_add, Nat.cast_one]
    ring
  have hlinear : (G : ℝ) ≤ 6 * ((K : ℝ) + 1) +
      9 * ((Nat.log2 (K + 1) : ℝ) + 2) / ε := by
    simpa only [G, Nat.cast_add, Nat.cast_one, hD] using hg.1
  have hquad : (G : ℝ) ≤ 6 * ((K : ℝ) + 1) ^ 2 := by
    have hquad' : (G : ℝ) ≤ 2 * ((K : ℝ) + 1) ^ 2 := by exact_mod_cast hg.2
    nlinarith [sq_nonneg ((K : ℝ) + 1)]
  have hratio : 2 * (G : ℝ) * ((K : ℝ) + 1) / (1 / 10) =
      20 * (G : ℝ) * ((K : ℝ) + 1) := by ring
  have hb := Estimation.estimation_budget C hC K hK ε hε G N hlinear hquad (by
    simpa only [G, hratio, hD, Nat.cast_add, Nat.cast_one] using hN)
  refine ⟨R, 2 * N, ?_, hcap, hlegal, hprob⟩
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hb

end BilateralProfit

open BilateralProfit

open MeasureTheory

/-- **Lemma 4.8** with **Remark 4.12**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript,
sha256 e91e8127…), p.24 (PDF 26) and p.28 (PDF 30); corrected: `K ≥ 2`.

There is a constant `C` such that for every `K ≥ 2`, every distribution `ρ` on `G_K × 𝒜` and every
precision `ε ∈ (0, 1]` there is a routine, depending only on `K, ρ, ε`, that
1. makes at most `C log³K (K/ε² + log³K/ε³)` pricing queries on every run,
2. queries only actions `a ∈ 𝒜` with `Δ_ρ(a⋆, a) ≤ 2ε`, and
3. for every unknown valuation law `P` on `[0,1]²`, when each query at `a` returns an independent
   observation with mean `P(a)` (the trade probability) and values in a fixed interval of length
   `2` (Remark 4.12; the trade bit is the case `[0, 2]`), estimates `E_P[Profit(Ṽ, a)]` to
   precision `ε/4` simultaneously for all `a ∈ 𝒜` with `Δ_ρ(a⋆, a) ≤ ε`, with probability at
   least `9/10`.

**Formalization Note.** The routine is a `QTree` over actions; its output is a vector of
estimates. Observations at the same action are i.i.d. with law `obs a`. `C` is chosen before
`K, ρ, ε`; the routine before `P`, the interval `[c, c + 2]` and the observation laws.
`E_P[Profit(Ṽ, a)] = (q − p) P(a)` (`muP`). `log` is natural. -/
theorem solution :
    ∃ C : ℝ, ∀ K : ℕ, 2 ≤ K → ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ (R : QTree (Act K) (Act K → ℝ)) (N : ℕ),
          (N : ℝ) ≤ C * Real.log K ^ 3 * ((K : ℝ) / ε ^ 2 + Real.log K ^ 3 / ε ^ 3) ∧
          R.QueriesAtMost N ∧ R.AllQueries (fun a => gapStar ρ a ≤ 2 * ε) ∧
          ∀ μ : Measure (ℝ × ℝ), IsValLaw μ →
            ∀ (c : ℝ) (obs : Act K → Measure ℝ), (∀ a, IsProbabilityMeasure (obs a)) →
              (∀ a, obs a (Set.Icc c (c + 2))ᶜ = 0) →
              (∀ a, ∫ r, r ∂(obs a) = Ptrade μ (pt K a.1)) →
              ENNReal.ofReal (9 / 10) ≤
                R.prob (fun a _ => obs a)
                  (fun est => ∀ a, gapStar ρ a ≤ ε → |est a - muP μ (pt K a.1)| ≤ ε / 4)
                  (fun _ => 0) := by exact BilateralProfit.cert_lemma_4_8
