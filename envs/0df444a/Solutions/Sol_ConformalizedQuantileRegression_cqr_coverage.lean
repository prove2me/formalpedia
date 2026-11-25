-- Prove2me | solution 1 for ConformalizedQuantileRegression.cqr_coverage
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T07:06:29.027393+00:00
-- url     : https://prove2.me/submissions/ff7f0685-a22e-4ab7-987a-0389e242fcce

import Mathlib
import Definitions.Def_ConformalizedQuantileRegression_Basic

open MeasureTheory ProbabilityTheory
namespace ConformalizedQuantileRegression

lemma qe_orderStat_eq {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    orderStat Finset.univ z k = (z ∘ Tuple.sort z) ⟨k - 1, by omega⟩ := by
  classical
  set σ := Tuple.sort z
  set w : Fin n → ℝ := z ∘ σ
  have hmono : Monotone w := Tuple.monotone_sort z
  have hL : (Finset.univ.val.map z).sort (· ≤ ·) = List.ofFn w := by
    have hp : List.Perm ((Finset.univ.val.map z).sort (· ≤ ·)) (List.ofFn w) := by
      rw [← Multiset.coe_eq_coe, Multiset.sort_eq, Fin.univ_val_map]
      exact Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm z).symm
    exact hp.eq_of_pairwise' (Multiset.pairwise_sort _ _) hmono.sortedLE_ofFn.pairwise
  simp only [orderStat, hL]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [show k - 1 < n by omega]

lemma qe_empQuantile_eq_orderStat {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    empQuantile Finset.univ z α = (orderStat Finset.univ z ⌈α * n⌉₊ : EReal) := by
  classical
  set σ := Tuple.sort z
  set w : Fin n → ℝ := z ∘ σ
  have hmono : Monotone w := Tuple.monotone_sort z
  have hL : (Finset.univ.val.map z).sort (· ≤ ·) = List.ofFn w := by
    have hp : List.Perm ((Finset.univ.val.map z).sort (· ≤ ·)) (List.ofFn w) := by
      rw [← Multiset.coe_eq_coe, Multiset.sort_eq, Fin.univ_val_map]
      exact Multiset.coe_eq_coe.mpr (σ.ofFn_comp_perm z).symm
    exact hp.eq_of_pairwise' (Multiset.pairwise_sort _ _) hmono.sortedLE_ofFn.pairwise
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hαn : 0 < α * n := mul_pos hα0 hnpos
  set k := ⌈α * n⌉₊
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hαn).ne'
  have hkn : k ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hup : (k : ℝ) < α * n + 1 := Nat.ceil_lt_add_one hαn.le
  have hge : α * n ≤ k := Nat.le_ceil _
  set m : Fin n := ⟨k - 1, by omega⟩
  have hq : orderStat Finset.univ z k = w m := by
    simp only [orderStat, hL]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [m, show k - 1 < n by omega]
  have hcnt : ∀ y, (Finset.univ.filter fun i => z i ≤ y).card
      = (Finset.univ.filter fun j => w j ≤ y).card := by
    intro y
    rw [Finset.card_filter, Finset.card_filter]
    exact (Equiv.sum_comp σ (fun i => if z i ≤ y then 1 else 0)).symm
  have hcdf : ∀ y, empCDF Finset.univ z y =
      ((Finset.univ.filter fun j => w j ≤ y).card : ℝ) / n := by
    intro y
    unfold empCDF
    rw [hcnt, Finset.card_univ, Fintype.card_fin]
  rw [hq]
  unfold empQuantile
  apply le_antisymm
  · refine iInf₂_le (w m) ?_
    rw [hcdf, le_div_iff₀ hnpos]
    have h1 : k ≤ (Finset.univ.filter fun j => w j ≤ w m).card := by
      calc k = (Finset.Iic m).card := by simp [m]; omega
        _ ≤ _ := Finset.card_le_card (fun j hj => by
              simp only [Finset.mem_Iic] at hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact hmono hj)
    have h2 : (k : ℝ) ≤ ((Finset.univ.filter fun j => w j ≤ w m).card : ℝ) := by
      exact_mod_cast h1
    linarith
  · refine le_iInf₂ fun y hy => ?_
    rw [EReal.coe_le_coe_iff]
    by_contra hlt
    push_neg at hlt
    rw [hcdf, le_div_iff₀ hnpos] at hy
    have h1 : (Finset.univ.filter fun j => w j ≤ y).card ≤ k - 1 := by
      calc _ ≤ (Finset.Iio m).card := Finset.card_le_card (fun j hj => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              simp only [Finset.mem_Iio]
              by_contra hc
              push_neg at hc
              have := hmono hc
              linarith)
        _ = k - 1 := by simp [m]
    have h2 : ((Finset.univ.filter fun j => w j ≤ y).card : ℝ) ≤ (k : ℝ) - 1 := by
      rw [← Nat.cast_one, ← Nat.cast_sub hk1]
      exact_mod_cast h1
    linarith

lemma qe_le_orderStat_iff {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k ≤ n) (i0 : Fin n) :
    z i0 ≤ orderStat Finset.univ z k ↔
      (Finset.univ.filter fun j => z j < z i0).card < k := by
  classical
  set σ := Tuple.sort z
  set w : Fin n → ℝ := z ∘ σ
  have hmono : Monotone w := Tuple.monotone_sort z
  have hq : orderStat Finset.univ z k = w ⟨k - 1, by omega⟩ :=
    qe_orderStat_eq hn z k hk1 hkn
  set m : Fin n := ⟨k - 1, by omega⟩
  constructor
  · intro h
    rw [hq] at h
    have him : ∀ j, z j < z i0 → σ.symm j < m := by
      intro j hj
      have : w (σ.symm j) < w m := by
        simp only [w, Function.comp_apply, Equiv.apply_symm_apply]
        exact lt_of_lt_of_le hj h
      exact lt_of_not_ge fun hge => (not_le_of_gt this) (hmono hge)
    have : (Finset.univ.filter fun j => z j < z i0) ⊆ Finset.image σ (Finset.Iio m) := by
      intro j hj
      simp only [Finset.mem_filter] at hj
      simp only [Finset.mem_image, Finset.mem_Iio]
      exact ⟨σ.symm j, him j hj.2, by simp⟩
    have hcard := Finset.card_le_card this
    have : (Finset.image σ (Finset.Iio m)).card = k - 1 := by
      rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iio]
      try simp [m]
    omega
  · intro h
    rw [hq]
    by_contra hgt
    push_neg at hgt
    have : Finset.image σ (Finset.Iic m) ⊆ Finset.univ.filter fun j => z j < z i0 := by
      intro j hj
      simp only [Finset.mem_image, Finset.mem_Iic] at hj
      obtain ⟨t, ht, rfl⟩ := hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_lt (hmono ht) hgt
    have hcard := Finset.card_le_card this
    have : (Finset.image σ (Finset.Iic m)).card = k := by
      rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iic]
      simp [m]; omega
    omega

lemma qe_count_le {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    k ≤ (Finset.univ.filter fun j => z j ≤ orderStat Finset.univ z k).card := by
  classical
  set σ := Tuple.sort z
  set w : Fin n → ℝ := z ∘ σ
  have hmono : Monotone w := Tuple.monotone_sort z
  have hq : orderStat Finset.univ z k = w ⟨k - 1, by omega⟩ :=
    qe_orderStat_eq hn z k hk1 hkn
  set m : Fin n := ⟨k - 1, by omega⟩
  have : Finset.image σ (Finset.Iic m) ⊆
      Finset.univ.filter fun j => z j ≤ orderStat Finset.univ z k := by
    intro j hj
    simp only [Finset.mem_image, Finset.mem_Iic] at hj
    obtain ⟨t, ht, rfl⟩ := hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hq]
    exact hmono ht
  have hcard := Finset.card_le_card this
  have : (Finset.image σ (Finset.Iic m)).card = k := by
    rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iic]
    simp [m]; omega
  omega

lemma qe_count_eq_of_injective {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k ≤ n) (hinj : Function.Injective z) :
    (Finset.univ.filter fun j => z j ≤ orderStat Finset.univ z k).card = k := by
  classical
  set σ := Tuple.sort z
  set w : Fin n → ℝ := z ∘ σ
  have hmono : Monotone w := Tuple.monotone_sort z
  have hstrict : StrictMono w := by
    intro i j hij
    refine lt_of_le_of_ne (hmono hij.le) ?_
    intro heq
    have : σ i = σ j := hinj (by simpa [w] using heq)
    exact hij.ne (σ.injective this)
  have hq : orderStat Finset.univ z k = w ⟨k - 1, by omega⟩ :=
    qe_orderStat_eq hn z k hk1 hkn
  set m : Fin n := ⟨k - 1, by omega⟩
  apply le_antisymm ?_ (qe_count_le hn z k hk1 hkn)
  have : Finset.univ.filter (fun j => z j ≤ orderStat Finset.univ z k) ⊆
      Finset.image σ (Finset.Iic m) := by
    intro j hj
    simp only [Finset.mem_filter, hq] at hj
    simp only [Finset.mem_image, Finset.mem_Iic]
    refine ⟨σ.symm j, ?_, by simp⟩
    have : w (σ.symm j) ≤ w m := by
      simp only [w, Function.comp_apply, Equiv.apply_symm_apply]
      exact hj.2
    exact le_of_not_gt fun hgt => (not_le_of_gt (hstrict hgt)) this
  have hcard := Finset.card_le_card this
  have : (Finset.image σ (Finset.Iic m)).card = k := by
    rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iic]
    simp [m]; omega
  omega

lemma qe_event_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Z : Fin n → Ω → ℝ) (hZm : ∀ i, Measurable (Z i)) (i : Fin n) (k : ℕ) :
    MeasurableSet {ω | (Finset.univ.filter fun j => Z j ω < Z i ω).card < k} := by
  classical
  have hcard : Measurable fun ω => (Finset.univ.filter fun j => Z j ω < Z i ω).card := by
    simp_rw [Finset.card_filter]
    refine Finset.measurable_sum _ fun j _ => ?_
    exact Measurable.ite (measurableSet_lt (hZm j) (hZm i)) measurable_const measurable_const
  change MeasurableSet
      ((fun ω => (Finset.univ.filter fun j => Z j ω < Z i ω).card) ⁻¹' Set.Iio k)
  exact MeasurableSet.preimage measurableSet_Iio hcard

theorem quantile_exchangeability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → ℝ) (hZ : IsExchangeable P Z)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal α ≤
        P {ω | (Z ⟨n - 1, by omega⟩ ω : EReal) ≤ empQuantile Finset.univ (fun i => Z i ω) α} ∧
    ((∀ᵐ ω ∂P, Function.Injective (fun i => Z i ω)) →
      P {ω | (Z ⟨n - 1, by omega⟩ ω : EReal) ≤ empQuantile Finset.univ (fun i => Z i ω) α} ≤
        ENNReal.ofReal (α + 1 / (n : ℝ))) := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hαn : 0 < α * n := mul_pos hα0 hnpos
  set k := ⌈α * n⌉₊
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hαn).ne'
  have hkn : k ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hge : (α : ℝ) * n ≤ k := Nat.le_ceil _
  have hup : (k : ℝ) < α * n + 1 := Nat.ceil_lt_add_one hαn.le
  set last : Fin n := ⟨n - 1, by omega⟩
  have hrew : ∀ ω,
      ((Z last ω : EReal) ≤ empQuantile Finset.univ (fun i => Z i ω) α) ↔
        (Finset.univ.filter fun j => Z j ω < Z last ω).card < k := by
    intro ω
    rw [qe_empQuantile_eq_orderStat hn (fun i => Z i ω) α hα0 hα1, EReal.coe_le_coe_iff]
    exact qe_le_orderStat_iff hn (fun i => Z i ω) k hk1 hkn last
  have hset : {ω | (Z last ω : EReal) ≤ empQuantile Finset.univ (fun i => Z i ω) α} =
      {ω | (Finset.univ.filter fun j => Z j ω < Z last ω).card < k} := by
    ext ω; exact hrew ω
  rw [hset]
  let E : Fin n → Set Ω :=
    fun i => {ω | (Finset.univ.filter fun j => Z j ω < Z i ω).card < k}
  have hEmeas : ∀ i, MeasurableSet (E i) := fun i =>
    qe_event_measurable Z hZ.1 i k
  let F : (Fin n → ℝ) → Prop :=
    fun v => (Finset.univ.filter fun j => v j < v last).card < k
  have hF : MeasurableSet {v : Fin n → ℝ | F v} :=
    qe_event_measurable (Ω := Fin n → ℝ)
      (fun (i : Fin n) (v : Fin n → ℝ) => v i)
      (fun i => measurable_pi_apply i) last k
  have hmapZ : Measurable fun ω i => Z i ω := measurable_pi_lambda _ fun i => hZ.1 i
  have hEq : ∀ i, P (E i) = P (E last) := by
    intro i
    let σ : Equiv.Perm (Fin n) := Equiv.swap i last
    have hmaps : Measure.map (fun ω j => Z (σ j) ω) P = Measure.map (fun ω j => Z j ω) P :=
      hZ.2 σ
    have hml : Measurable fun ω j => Z (σ j) ω := measurable_pi_lambda _ fun j => hZ.1 (σ j)
    have h1 : P (E last) = Measure.map (fun ω j => Z j ω) P {v | F v} := by
      rw [Measure.map_apply hmapZ hF]; rfl
    have h2 : P (E i) = Measure.map (fun ω j => Z (σ j) ω) P {v | F v} := by
      rw [Measure.map_apply hml hF]
      congr 1
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, E, F]
      have hσlast : σ last = i := Equiv.swap_apply_right i last
      have hswap : (Finset.univ.filter fun j => Z (σ j) ω < Z (σ last) ω).card =
          (Finset.univ.filter fun j => Z j ω < Z i ω).card := by
        rw [hσlast, Finset.card_filter, Finset.card_filter]
        exact Equiv.sum_comp σ fun j => if Z j ω < Z i ω then 1 else 0
      simp [hswap]
    rw [h1, h2, hmaps]
  have hcount_ge : ∀ ω,
      k ≤ (Finset.univ.filter fun i =>
        (Finset.univ.filter fun j => Z j ω < Z i ω).card < k).card := by
    intro ω
    have h := qe_count_le hn (fun i => Z i ω) k hk1 hkn
    have hset' :
        (Finset.univ.filter fun i =>
          (Finset.univ.filter fun j => Z j ω < Z i ω).card < k) =
        (Finset.univ.filter fun i =>
          (fun j => Z j ω) i ≤ orderStat Finset.univ (fun j => Z j ω) k) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (qe_le_orderStat_iff hn (fun j => Z j ω) k hk1 hkn i).symm
    simpa [hset'] using h
  have hinterg :
      ∫⁻ ω, ((Finset.univ.filter fun i =>
        (Finset.univ.filter fun j => Z j ω < Z i ω).card < k).card : ENNReal) ∂P =
        ∑ i : Fin n, P (E i) := by
    have heq : (fun ω =>
        ((Finset.univ.filter fun i =>
          (Finset.univ.filter fun j => Z j ω < Z i ω).card < k).card : ENNReal)) =
        fun ω => ∑ i : Fin n, Set.indicator (E i) (fun _ => (1 : ENNReal)) ω := by
      funext ω
      have hc :
          ((Finset.univ.filter fun i =>
            (Finset.univ.filter fun j => Z j ω < Z i ω).card < k).card : ENNReal) =
          ∑ i : Fin n, if (Finset.univ.filter fun j => Z j ω < Z i ω).card < k then (1 : ENNReal) else 0 := by
        simp only [Finset.card_filter, Nat.cast_sum]
        congr 1
        ext i
        split_ifs <;> simp
      rw [hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Set.indicator, E]
    rw [heq, lintegral_finsetSum _ (fun i _ =>
      Measurable.indicator measurable_const (hEmeas i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_indicator_const (hEmeas i) 1, one_mul]
  have hsum' : ∑ i : Fin n, P (E i) = (n : ENNReal) * P (E last) := by
    rw [Finset.sum_congr rfl (fun i _ => hEq i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  -- lower bound
  have hlower : ENNReal.ofReal α ≤ P (E last) := by
    have hge_int : (k : ENNReal) * P Set.univ ≤ ∑ i : Fin n, P (E i) := by
      rw [← hinterg]
      have hc : ∫⁻ _ω, (k : ENNReal) ∂P = (k : ENNReal) * P Set.univ := lintegral_const _
      rw [← hc]
      exact lintegral_mono fun ω => Nat.cast_le.mpr (hcount_ge ω)
    rw [measure_univ, mul_one, hsum'] at hge_int
    have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
    have hdiv : (k : ENNReal) / n ≤ P (E last) :=
      (ENNReal.div_le_iff_le_mul (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top n))).mpr
        (by rwa [mul_comm] at hge_int)
    have hkdiv : ENNReal.ofReal (k / n : ℝ) = (k : ENNReal) / n := by
      rw [ENNReal.ofReal_div_of_pos hnpos]
      simp
    have hαle : (α : ℝ) ≤ k / n := (le_div_iff₀ hnpos).mpr hge
    calc ENNReal.ofReal α
        ≤ ENNReal.ofReal (k / n : ℝ) := ENNReal.ofReal_le_ofReal hαle
      _ = (k : ENNReal) / n := hkdiv
      _ ≤ P (E last) := hdiv
  refine ⟨hlower, ?_⟩
  intro hinj
  have hcount_eq : ∀ᵐ ω ∂P,
      (Finset.univ.filter fun i =>
        (Finset.univ.filter fun j => Z j ω < Z i ω).card < k).card = k := by
    filter_upwards [hinj] with ω hω
    have h := qe_count_eq_of_injective hn (fun i => Z i ω) k hk1 hkn hω
    have hset' :
        (Finset.univ.filter fun i =>
          (Finset.univ.filter fun j => Z j ω < Z i ω).card < k) =
        (Finset.univ.filter fun i =>
          (fun j => Z j ω) i ≤ orderStat Finset.univ (fun j => Z j ω) k) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (qe_le_orderStat_iff hn (fun j => Z j ω) k hk1 hkn i).symm
    simpa [hset'] using h
  have heq_int : ∑ i : Fin n, P (E i) = (k : ENNReal) := by
    rw [← hinterg]
    have hc : ∫⁻ _ω, (k : ENNReal) ∂P = (k : ENNReal) := by
      simp [lintegral_const, measure_univ]
    rw [← hc]
    refine lintegral_congr_ae ?_
    filter_upwards [hcount_eq] with ω hω
    exact congrArg Nat.cast hω
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
  have hPeq : P (E last) = (k : ENNReal) / n := by
    have hmul : (n : ENNReal) * P (E last) = (k : ENNReal) := by
      rwa [hsum'] at heq_int
    exact (ENNReal.eq_div_iff hn0 (ENNReal.natCast_ne_top n)).mpr hmul
  have hknR : (k : ℝ) / n ≤ α + 1 / n := by
    have : (k : ℝ) ≤ α * n + 1 := le_of_lt hup
    calc (k : ℝ) / n ≤ (α * n + 1) / n := (div_le_div_iff_of_pos_right hnpos).mpr this
      _ = α + 1 / n := by field_simp
  have hkdiv : (k : ENNReal) / n = ENNReal.ofReal (k / n : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos hnpos]
    simp
  rw [hPeq, hkdiv]
  exact ENNReal.ofReal_le_ofReal hknR

lemma qe_inflated_quantile_iff {n : ℕ} (hn : 0 < n) (z : Fin (n + 1) → ℝ) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    (z (Fin.last n) : EReal) ≤ empQuantile (Finset.univ.map Fin.castSuccEmb) z ((1 + 1 / (n : ℝ)) * α) ↔
      (z (Fin.last n) : EReal) ≤ empQuantile Finset.univ z α := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ y : ℝ, y < z (Fin.last n) →
      ((1 + 1 / (n : ℝ)) * α ≤ empCDF (Finset.univ.map Fin.castSuccEmb) z y ↔
        α ≤ empCDF Finset.univ z y) := by
    intro y hy
    have h1 : (Finset.univ.filter fun i => z i ≤ y).card =
        ((Finset.univ.map Fin.castSuccEmb).filter fun i => z i ≤ y).card := by
      rw [Fin.univ_castSuccEmb, Finset.filter_cons, if_neg (not_le.mpr hy)]
    simp only [empCDF, h1, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    set c : ℝ := (((Finset.univ.map Fin.castSuccEmb).filter fun i => z i ≤ y).card : ℝ)
    have e : (1 + 1 / (n : ℝ)) * α * n = α * (n + 1) := by field_simp
    push_cast
    rw [le_div_iff₀ hnpos, e, le_div_iff₀ (by positivity)]
  simp only [empQuantile, le_iInf₂_iff]
  constructor
  · intro h y hy
    by_contra hlt
    have hlt' : y < z (Fin.last n) := by exact_mod_cast not_le.mp hlt
    exact hlt (h y ((key y hlt').2 hy))
  · intro h y hy
    by_contra hlt
    have hlt' : y < z (Fin.last n) := by exact_mod_cast not_le.mp hlt
    exact hlt (h y ((key y hlt').1 hy))

theorem quantile_inflation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) (Z : Fin (n + 1) → Ω → ℝ)
    (hZ : IsExchangeable P Z) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal α ≤
        P {ω | (Z (Fin.last n) ω : EReal) ≤
          empQuantile (Finset.univ.map Fin.castSuccEmb) (fun i => Z i ω) ((1 + 1 / (n : ℝ)) * α)} ∧
    ((∀ᵐ ω ∂P, Function.Injective (fun i => Z i ω)) →
      P {ω | (Z (Fin.last n) ω : EReal) ≤
          empQuantile (Finset.univ.map Fin.castSuccEmb) (fun i => Z i ω) ((1 + 1 / (n : ℝ)) * α)} ≤
        ENNReal.ofReal (α + 1 / ((n : ℝ) + 1))) := by
  have hidx : (⟨(n + 1) - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
    ext; simp
  have hset :
      {ω | (Z (Fin.last n) ω : EReal) ≤
          empQuantile (Finset.univ.map Fin.castSuccEmb) (fun i => Z i ω)
            ((1 + 1 / (n : ℝ)) * α)} =
      {ω | (Z ⟨(n + 1) - 1, by omega⟩ ω : EReal) ≤
          empQuantile Finset.univ (fun i => Z i ω) α} := by
    ext ω
    rw [hidx]
    exact qe_inflated_quantile_iff hn (fun i => Z i ω) α hα0 hα1
  rw [hset]
  simpa [hidx] using
    (quantile_exchangeability (n := n + 1) P (Nat.succ_pos n) Z hZ α hα0 hα1)


lemma cov_interval_iff_score {p n : ℕ} {I₁ : Finset (Fin n)} (A : QRAlgorithm p I₁)
    (I₂ : Finset (Fin n)) (α : ℝ) (d : Fin n → Sample p) (z : Sample p) :
    z.2 ∈ cqrInterval A I₂ α d z.1 ↔
      (conformityScore (fitQR A d).1 (fitQR A d).2 z : EReal) ≤ cqrCorrection A I₂ α d := by
  simp only [cqrInterval, Set.mem_setOf_eq, conformityScore]
  generalize cqrCorrection A I₂ α d = Q
  induction Q using EReal.rec with
  | bot => simp
  | top => simp
  | coe q =>
    rw [← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff,
      EReal.coe_le_coe_iff, max_le_iff]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith

lemma cov_empQuantile_reindex {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']
    (s : Finset ι) (s' : Finset ι') (e : ↥s ≃ ↥s')
    (z : ι → ℝ) (z' : ι' → ℝ) (hz : ∀ i : s, z i = z' (e i)) (β : ℝ) :
    empQuantile s z β = empQuantile s' z' β := by
  have hcard' : s.card = s'.card := by
    rw [← Fintype.card_coe s, ← Fintype.card_coe s']
    exact Fintype.card_congr e
  have hcdf : ∀ y, empCDF s z y = empCDF s' z' y := by
    intro y
    have hc :
        (s.filter fun i => z i ≤ y).card = (s'.filter fun i => z' i ≤ y).card := by
      have h1 : (s.filter fun i => z i ≤ y).card =
          ∑ i : ↥s, if z i ≤ y then (1 : ℕ) else 0 := by
        rw [Finset.card_filter, ← Finset.sum_attach]
        rfl
      have h2 : (s'.filter fun i => z' i ≤ y).card =
          ∑ i : ↥s', if z' i ≤ y then (1 : ℕ) else 0 := by
        rw [Finset.card_filter, ← Finset.sum_attach]
        rfl
      rw [h1, h2, ← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hz]
    unfold empCDF
    rw [hc, hcard']
  simp only [empQuantile, hcdf]

lemma cov_score_measurable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (Z : Fin (n + 1) → Ω → Sample p) (hZm : ∀ i, Measurable (Z i))
    (I₁ : Finset (Fin n)) (A : QRAlgorithm p I₁) (hA : IsMeasurableAlgorithm A)
    (j : Fin (n + 1)) :
    Measurable fun ω =>
      conformityScore (fitQR A (fun i => Z i.castSucc ω)).1
        (fitQR A (fun i => Z i.castSucc ω)).2 (Z j ω) := by
  have hdata : Measurable fun ω => (fun i : ↥I₁ => Z i.1.castSucc ω) :=
    measurable_pi_lambda _ fun i => hZm _
  have hx : Measurable fun ω => (Z j ω).1 := measurable_fst.comp (hZm j)
  have hy : Measurable fun ω => (Z j ω).2 := measurable_snd.comp (hZm j)
  have hqlo : Measurable fun ω => (fitQR A (fun i => Z i.castSucc ω)).1 (Z j ω).1 := by
    have : Measurable fun ω =>
        (A (fun i : ↥I₁ => Z i.1.castSucc ω)).1 (Z j ω).1 :=
      hA.1.comp (hdata.prodMk hx)
    simpa [fitQR] using this
  have hqhi : Measurable fun ω => (fitQR A (fun i => Z i.castSucc ω)).2 (Z j ω).1 := by
    have : Measurable fun ω =>
        (A (fun i : ↥I₁ => Z i.1.castSucc ω)).2 (Z j ω).1 :=
      hA.2.comp (hdata.prodMk hx)
    simpa [fitQR] using this
  simp only [conformityScore]
  exact (hqlo.sub hy).max (hy.sub hqhi)

theorem cqr_coverage {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p n : ℕ} (Z : Fin (n + 1) → Ω → Sample p) (hZ : IsExchangeable P Z)
    (I₁ I₂ : Finset (Fin n)) (hdisj : Disjoint I₁ I₂) (hsplit : I₁ ∪ I₂ = Finset.univ)
    (hI₂ : I₂.Nonempty) (A : QRAlgorithm p I₁) (hA : IsMeasurableAlgorithm A)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (1 - α) ≤
        P {ω | (Z (Fin.last n) ω).2 ∈
          cqrInterval A I₂ α (fun i => Z i.castSucc ω) (Z (Fin.last n) ω).1} ∧
    ((∀ᵐ ω ∂P, Set.InjOn
        (fun j => conformityScore (fitQR A (fun i => Z i.castSucc ω)).1
          (fitQR A (fun i => Z i.castSucc ω)).2 (Z j ω))
        (↑(I₂.map Fin.castSuccEmb ∪ {Fin.last n}) : Set (Fin (n + 1)))) →
      P {ω | (Z (Fin.last n) ω).2 ∈
          cqrInterval A I₂ α (fun i => Z i.castSucc ω) (Z (Fin.last n) ω).1} ≤
        ENNReal.ofReal (1 - α + 1 / ((I₂.card : ℝ) + 1))) := by
  classical
  set m := I₂.card
  have hm : 0 < m := Finset.card_pos.mpr hI₂
  let e : Fin m ≃ ↥I₂ := (Fintype.equivFinOfCardEq (Fintype.card_coe I₂)).symm
  let φ : Fin (m + 1) → Fin (n + 1) := fun i =>
    if h : (i : ℕ) < m then (e ⟨i, h⟩).1.castSucc else Fin.last n
  have hφ_cast : ∀ k : Fin m, φ k.castSucc = (e k).1.castSucc := by
    intro k
    simp [φ, Fin.coe_castSucc, k.is_lt]
  have hφ_last : φ (Fin.last m) = Fin.last n := by
    simp [φ, Fin.val_last, lt_irrefl]
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    by_cases ha : (a : ℕ) < m
    · by_cases hb : (b : ℕ) < m
      · have ha' : φ a = (e ⟨a, ha⟩).1.castSucc := by simp [φ, ha]
        have hb' : φ b = (e ⟨b, hb⟩).1.castSucc := by simp [φ, hb]
        rw [ha', hb'] at hab
        have : (e ⟨a, ha⟩).1 = (e ⟨b, hb⟩).1 := Fin.castSucc_injective _ hab
        have heq : (⟨a, ha⟩ : Fin m) = ⟨b, hb⟩ :=
          e.injective (Subtype.ext this)
        exact Fin.ext (congrArg (fun k : Fin m => (k : ℕ)) heq)
      · have : φ b = Fin.last n := by simp [φ, hb]
        have : φ a = (e ⟨a, ha⟩).1.castSucc := by simp [φ, ha]
        rw [this, ‹φ b = _›] at hab
        exact (Fin.castSucc_ne_last _ hab).elim
    · have ha' : φ a = Fin.last n := by simp [φ, ha]
      by_cases hb : (b : ℕ) < m
      · have : φ b = (e ⟨b, hb⟩).1.castSucc := by simp [φ, hb]
        rw [ha', this] at hab
        exact (Fin.castSucc_ne_last _ hab.symm).elim
      · have haeq : a = Fin.last m :=
          Fin.ext ((Nat.eq_of_le_of_lt_succ (le_of_not_gt ha) a.isLt).trans (Eq.symm (Fin.val_last m)))
        have hbeq : b = Fin.last m :=
          Fin.ext ((Nat.eq_of_le_of_lt_succ (le_of_not_gt hb) b.isLt).trans (Eq.symm (Fin.val_last m)))
        exact haeq.trans hbeq.symm
  -- Fix the last identification if Fin.last_le_iff is wrong; compile will tell us.
  let ι : Fin (m + 1) ↪ Fin (n + 1) := ⟨φ, hφ_inj⟩
  have hrange : Set.range φ = ↑(I₂.map Fin.castSuccEmb ∪ {Fin.last n}) := by
    ext j
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hi : (i : ℕ) < m
      · simp [φ, hi]
      · simp [φ, hi]
    · intro hj
      simp only [Finset.coe_union, Finset.coe_map, Finset.coe_singleton, Set.mem_union,
        Set.mem_image, Set.mem_singleton_iff] at hj
      rcases hj with ⟨i, hi, rfl⟩ | rfl
      · refine ⟨(e.symm ⟨i, hi⟩).castSucc, ?_⟩
        simp [hφ_cast, e.apply_symm_apply]
      · exact ⟨Fin.last m, hφ_last⟩
  let W : Fin (m + 1) → Ω → ℝ := fun i ω =>
    conformityScore (fitQR A (fun t => Z t.castSucc ω)).1
      (fitQR A (fun t => Z t.castSucc ω)).2 (Z (φ i) ω)
  have hWmeas : ∀ i, Measurable (W i) := fun i =>
    cov_score_measurable Z hZ.1 I₁ A hA (φ i)
  have hfit_perm : ∀ (π : Equiv.Perm (Fin (n + 1)))
      (hπ : ∀ i ∈ I₁, π i.castSucc = i.castSucc) (ω : Ω),
      fitQR A (fun t => Z (π t.castSucc) ω) = fitQR A (fun t => Z t.castSucc ω) := by
    intro π hπ ω
    simp only [fitQR]
    congr 1
    funext i
    exact congrArg (fun j => Z j ω) (hπ i.1 i.2)
  have hWex : IsExchangeable P W := by
    refine ⟨hWmeas, ?_⟩
    intro τ
    let π : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.viaEmbedding τ ι
    have hπ_img : ∀ i, π (φ i) = φ (τ i) := fun i =>
      Equiv.Perm.viaEmbedding_apply τ ι i
    have hπ_fix : ∀ t ∈ I₁, π t.castSucc = t.castSucc := by
      intro t ht
      change τ.viaEmbedding ι t.castSucc = t.castSucc
      refine Equiv.Perm.viaEmbedding_apply_of_notMem (e := τ) (ι := ι) (x := t.castSucc) ?_
      intro hmem
      obtain ⟨i, hi⟩ := hmem
      have : t.castSucc ∈ I₂.map Fin.castSuccEmb ∪ {Fin.last n} := by
        have himg : φ i ∈ (↑(I₂.map Fin.castSuccEmb ∪ {Fin.last n}) : Set (Fin (n + 1))) := by
          rw [← hrange]; exact ⟨i, rfl⟩
        have hφ : φ i = t.castSucc := hi
        simpa [hφ] using himg
      rw [Finset.mem_union, Finset.mem_singleton] at this
      rcases this with hmap | hlast
      · obtain ⟨x, hx, hxe⟩ := Finset.mem_map.mp hmap
        have : t = x := by
          apply Fin.castSucc_injective n
          change t.castSucc = (x.castSucc : Fin (n + 1))
          exact hxe.symm.trans (by simp [Fin.castSuccEmb, Fin.castSucc])
        subst this
        exact (Finset.disjoint_left.mp hdisj) ht hx
      · exact (Fin.castSucc_ne_last t hlast).elim
    -- W(τ i) ω = score at φ(τ i) with original fit = score at π(φ i) = W^{Z∘π} i
    have hWτ : ∀ ω i, W (τ i) ω =
        conformityScore (fitQR A (fun t => Z (π t.castSucc) ω)).1
          (fitQR A (fun t => Z (π t.castSucc) ω)).2 (Z (π (φ i)) ω) := by
      intro ω i
      dsimp only [W]
      rw [hfit_perm π hπ_fix ω, hπ_img]
    have hmapZ : Measure.map (fun ω j => Z (π j) ω) P =
        Measure.map (fun ω j => Z j ω) P := hZ.2 π
    -- rewrite both sides as pushforwards of the data vector
    have hmapW : Measure.map (fun ω i => W i ω) P =
        (Measure.map (fun ω j => Z j ω) P).map
          (fun v i => conformityScore (fitQR A (fun t => v t.castSucc)).1
            (fitQR A (fun t => v t.castSucc)).2 (v (φ i))) := by
      rw [Measure.map_map]
      · rfl
      · exact measurable_pi_lambda _ fun i =>
          cov_score_measurable (Ω := Fin (n + 1) → Sample p)
            (fun (j : Fin (n + 1)) (v : Fin (n + 1) → Sample p) => v j)
            (fun j => measurable_pi_apply j) I₁ A hA (φ i)
      · exact measurable_pi_lambda _ fun j => hZ.1 j
    have hWhat :
        Measurable fun v : Fin (n + 1) → Sample p =>
          (fun i : Fin (m + 1) =>
            conformityScore (fitQR A (fun t => v t.castSucc)).1
              (fitQR A (fun t => v t.castSucc)).2 (v (φ i))) :=
      measurable_pi_lambda _ fun i =>
        cov_score_measurable (Ω := Fin (n + 1) → Sample p)
          (fun (j : Fin (n + 1)) (v : Fin (n + 1) → Sample p) => v j)
          (fun j => measurable_pi_apply j) I₁ A hA (φ i)
    have hmapWτ : Measure.map (fun ω i => W (τ i) ω) P =
        (Measure.map (fun ω j => Z (π j) ω) P).map
          (fun v i => conformityScore (fitQR A (fun t => v t.castSucc)).1
            (fitQR A (fun t => v t.castSucc)).2 (v (φ i))) := by
      rw [Measure.map_map]
      · refine Measure.map_congr (Filter.Eventually.of_forall fun ω => funext fun i => ?_)
        exact (hWτ ω i)
      · exact hWhat
      · exact measurable_pi_lambda _ fun j => hZ.1 (π j)
    rw [hmapWτ, hmapZ, ← hmapW]

  -- Event rewrite and apply inflation.
  have hα'0 : 0 < 1 - α := sub_pos.mpr hα1
  have hα'1 : (1 : ℝ) - α < 1 := by linarith
  have hset : {ω | (Z (Fin.last n) ω).2 ∈
        cqrInterval A I₂ α (fun i => Z i.castSucc ω) (Z (Fin.last n) ω).1} =
      {ω | (W (Fin.last m) ω : EReal) ≤
        empQuantile (Finset.univ.map Fin.castSuccEmb) (fun i => W i ω)
          ((1 + 1 / (m : ℝ)) * (1 - α))} := by
    ext ω
    constructor
    · intro h
      have hiff := cov_interval_iff_score A I₂ α (fun i => Z i.castSucc ω) (Z (Fin.last n) ω)
      have hs : (conformityScore (fitQR A (fun i => Z i.castSucc ω)).1
          (fitQR A (fun i => Z i.castSucc ω)).2 (Z (Fin.last n) ω) : EReal) ≤
          cqrCorrection A I₂ α (fun i => Z i.castSucc ω) := hiff.mp h
      -- identify last score and quantile
      have hWl : W (Fin.last m) ω =
          conformityScore (fitQR A (fun i => Z i.castSucc ω)).1
            (fitQR A (fun i => Z i.castSucc ω)).2 (Z (Fin.last n) ω) := by
        simp [W, hφ_last]
      have hq : cqrCorrection A I₂ α (fun i => Z i.castSucc ω) =
          empQuantile (Finset.univ.map Fin.castSuccEmb) (fun i => W i ω)
            ((1 + 1 / (m : ℝ)) * (1 - α)) := by
        unfold cqrCorrection
        have hlevel : (1 - α) * (1 + 1 / (m : ℝ)) = (1 + 1 / (m : ℝ)) * (1 - α) := by ring
        rw [hlevel]
        -- reindex I₂ to univ.map castSuccEmb
        let s : Finset (Fin (m + 1)) := Finset.univ.map Fin.castSuccEmb
        let es : Fin m ≃ ↥s :=
          { toFun := fun k => ⟨k.castSucc, by simp [s]⟩
            invFun := fun k => ⟨k.1, by
              have := k.2
              simp only [s, Finset.mem_map, Finset.mem_univ, true_and] at this
              rcases this with ⟨a, ha⟩
              have : k.1 = a.castSucc := ha.symm
              have : (k.1 : ℕ) < m := by rw [this]; exact a.is_lt
              exact this⟩
            left_inv := fun k => by ext; simp
            right_inv := fun k => by
              ext
              have := k.2
              simp only [s, Finset.mem_map, Finset.mem_univ, true_and] at this
              rcases this with ⟨a, ha⟩
              have hk : k.1 = a.castSucc := ha.symm
              simp [hk] }
        let e2 : ↥s ≃ ↥I₂ := es.symm.trans e
        refine cov_empQuantile_reindex I₂ s e2.symm
          (fun i => conformityScore (fitQR A (fun t => Z t.castSucc ω)).1
            (fitQR A (fun t => Z t.castSucc ω)).2 (Z i.castSucc ω))
          (fun i => W i ω) ?_ _
        intro i
        -- i : ↥I₂, e2.symm i is in s, should be (e.symm i).castSucc
        change conformityScore _ _ (Z i.1.castSucc ω) = W (e2.symm i) ω
        have : e2.symm i = es (e.symm i) := by
          simp [e2]
        rw [this]
        simp [W, hφ_cast, es]
      simpa [hWl, hq] using hs
    · intro h
      have hiff := cov_interval_iff_score A I₂ α (fun i => Z i.castSucc ω) (Z (Fin.last n) ω)
      apply hiff.mpr
      have hWl : W (Fin.last m) ω =
          conformityScore (fitQR A (fun i => Z i.castSucc ω)).1
            (fitQR A (fun i => Z i.castSucc ω)).2 (Z (Fin.last n) ω) := by
        simp [W, hφ_last]
      have hq : cqrCorrection A I₂ α (fun i => Z i.castSucc ω) =
          empQuantile (Finset.univ.map Fin.castSuccEmb) (fun i => W i ω)
            ((1 + 1 / (m : ℝ)) * (1 - α)) := by
        unfold cqrCorrection
        have hlevel : (1 - α) * (1 + 1 / (m : ℝ)) = (1 + 1 / (m : ℝ)) * (1 - α) := by ring
        rw [hlevel]
        let s : Finset (Fin (m + 1)) := Finset.univ.map Fin.castSuccEmb
        let es : Fin m ≃ ↥s :=
          { toFun := fun k => ⟨k.castSucc, by simp [s]⟩
            invFun := fun k => ⟨k.1, by
              have := k.2
              simp only [s, Finset.mem_map, Finset.mem_univ, true_and] at this
              rcases this with ⟨a, ha⟩
              have : k.1 = a.castSucc := ha.symm
              have : (k.1 : ℕ) < m := by rw [this]; exact a.is_lt
              exact this⟩
            left_inv := fun k => by ext; simp
            right_inv := fun k => by
              ext
              have := k.2
              simp only [s, Finset.mem_map, Finset.mem_univ, true_and] at this
              rcases this with ⟨a, ha⟩
              have hk : k.1 = a.castSucc := ha.symm
              simp [hk] }
        let e2 : ↥s ≃ ↥I₂ := es.symm.trans e
        refine cov_empQuantile_reindex I₂ s e2.symm
          (fun i => conformityScore (fitQR A (fun t => Z t.castSucc ω)).1
            (fitQR A (fun t => Z t.castSucc ω)).2 (Z i.castSucc ω))
          (fun i => W i ω) ?_ _
        intro i
        have : e2.symm i = es (e.symm i) := by simp [e2]
        rw [this]
        simp [W, hφ_cast, es]
      simpa [hWl, hq] using h
  rw [hset]
  have hinf :=
    quantile_inflation (n := m) P hm W hWex (1 - α) hα'0 hα'1
  refine ⟨hinf.1, ?_⟩
  intro hinj
  have hinjW : ∀ᵐ ω ∂P, Function.Injective fun i => W i ω := by
    filter_upwards [hinj] with ω hω
    intro a b hab
    have ha_mem : φ a ∈ (↑(I₂.map Fin.castSuccEmb ∪ {Fin.last n}) : Set _) := by
      have : φ a ∈ Set.range φ := ⟨a, rfl⟩
      rwa [hrange] at this
    have hb_mem : φ b ∈ (↑(I₂.map Fin.castSuccEmb ∪ {Fin.last n}) : Set _) := by
      have : φ b ∈ Set.range φ := ⟨b, rfl⟩
      rwa [hrange] at this
    exact hφ_inj (hω ha_mem hb_mem hab)
  have : (m : ℝ) = (I₂.card : ℝ) := rfl
  simpa [this] using hinf.2 hinjW

end ConformalizedQuantileRegression

open ConformalizedQuantileRegression in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {p n : ℕ} (Z : Fin (n + 1) → Ω → Sample p) (hZ : IsExchangeable P Z)
    (I₁ I₂ : Finset (Fin n)) (hdisj : Disjoint I₁ I₂) (hsplit : I₁ ∪ I₂ = Finset.univ)
    (hI₂ : I₂.Nonempty) (A : QRAlgorithm p I₁) (hA : IsMeasurableAlgorithm A)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (1 - α) ≤
        P {ω | (Z (Fin.last n) ω).2 ∈
          cqrInterval A I₂ α (fun i => Z i.castSucc ω) (Z (Fin.last n) ω).1} ∧
    ((∀ᵐ ω ∂P, Set.InjOn
        (fun j => conformityScore (fitQR A (fun i => Z i.castSucc ω)).1
          (fitQR A (fun i => Z i.castSucc ω)).2 (Z j ω))
        (↑(I₂.map Fin.castSuccEmb ∪ {Fin.last n}) : Set (Fin (n + 1)))) →
      P {ω | (Z (Fin.last n) ω).2 ∈
          cqrInterval A I₂ α (fun i => Z i.castSucc ω) (Z (Fin.last n) ω).1} ≤
        ENNReal.ofReal (1 - α + 1 / ((I₂.card : ℝ) + 1))) :=
  ConformalizedQuantileRegression.cqr_coverage P Z hZ I₁ I₂ hdisj hsplit hI₂ A hA α hα0 hα1
