-- Prove2me | solution 1 for ConformalizedQuantileRegression.quantile_exchangeability
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T06:50:43.802299+00:00
-- url     : https://prove2.me/submissions/8c1c2162-8d5d-4221-b8e8-309964baae37

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

end ConformalizedQuantileRegression

open ConformalizedQuantileRegression in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → ℝ) (hZ : IsExchangeable P Z)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal α ≤
        P {ω | (Z ⟨n - 1, by omega⟩ ω : EReal) ≤ empQuantile Finset.univ (fun i => Z i ω) α} ∧
    ((∀ᵐ ω ∂P, Function.Injective (fun i => Z i ω)) →
      P {ω | (Z ⟨n - 1, by omega⟩ ω : EReal) ≤ empQuantile Finset.univ (fun i => Z i ω) α} ≤
        ENNReal.ofReal (α + 1 / (n : ℝ))) :=
  ConformalizedQuantileRegression.quantile_exchangeability P hn Z hZ α hα0 hα1
