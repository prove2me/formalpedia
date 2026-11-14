-- Prove2me | solution 1 for BilateralProfit.claim_4_9
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T14:25:03.281331+00:00
-- url     : https://prove2.me/submissions/6f94f2c0-f97e-4c0f-95af-83f07d5a1188

import Mathlib
import Definitions.Def_BilateralProfit_SellerTree
import Theorems.Thm_BilateralProfit_eq_17

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

theorem solution (K : ℕ) (hK : 0 < K) (ρ : Grid K × Act K → ℝ) (hρ : IsDist ρ) (ε : ℝ)
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
