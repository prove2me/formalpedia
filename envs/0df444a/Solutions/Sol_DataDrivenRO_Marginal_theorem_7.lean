-- Prove2me | solution 1 for DataDrivenRO.Marginal.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T18:19:20.164995+00:00
-- url     : https://prove2.me/submissions/ea1a3874-5b9f-47c1-bea0-608fd540d8a2

import Mathlib
import Definitions.Def_DataDrivenRO_Marginal_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace P0ce6640c

open Classical

/-- `{y | ofReal α ≤ P{Z ≤ y}}` written through the cdf of the law of `Z`. -/
theorem vle_set_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) (α : ℝ) :
    {y : ℝ | ENNReal.ofReal α ≤ P {ω | Z ω ≤ y}} = {y | α ≤ cdf (P.map Z) y} := by
  have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  ext y
  simp only [mem_ofPred_eq]
  have h1 : P {ω | Z ω ≤ y} = ENNReal.ofReal (cdf (P.map Z) y) := by
    rw [ofReal_cdf, Measure.map_apply hZ measurableSet_Iic]; rfl
  rw [h1, ENNReal.ofReal_le_ofReal_iff (cdf_nonneg _ _)]

theorem vle_bdd (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu0 : 0 < u) :
    BddBelow {x | u ≤ cdf μ x} := by
  have h := (tendsto_cdf_atBot μ).eventually (gt_mem_nhds hu0)
  rw [Filter.eventually_atBot] at h
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx => ?_⟩
  by_contra hlt
  exact absurd (hx0 x (le_of_lt (not_le.mp hlt))) (not_lt.mpr hx)

theorem vset_bdd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) {α : ℝ} (hα0 : 0 < α) :
    BddBelow {y : ℝ | ENNReal.ofReal α ≤ P {ω | Z ω ≤ y}} := by
  have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  rw [vle_set_eq P Z hZ α]
  exact vle_bdd _ hα0

theorem vle_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) {α : ℝ} (hα0 : 0 < α) (t : ℝ)
    (ht : ENNReal.ofReal α ≤ P {ω | Z ω ≤ t}) :
    MultistageStochastic.valueAtRisk P Z α ≤ t :=
  csInf_le (vset_bdd P Z hZ hα0) ht

/-- The strict lower tail below the VaR has mass at most the level. -/
theorem lt_var_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) {a : ℝ} (ha0 : 0 < a) :
    P {ω | Z ω < MultistageStochastic.valueAtRisk P Z a} ≤ ENNReal.ofReal a := by
  set V := MultistageStochastic.valueAtRisk P Z a with hV
  have hlt : ∀ y, y < V → P {ω | Z ω ≤ y} ≤ ENNReal.ofReal a := by
    intro y hy
    by_contra h
    push Not at h
    have : V ≤ y := vle_le P Z hZ ha0 y h.le
    linarith
  have hU : {ω | Z ω < V} = ⋃ n : ℕ, {ω | Z ω ≤ V - 1 / ((n : ℝ) + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone (fun n : ℕ => {ω | Z ω ≤ V - 1 / ((n : ℝ) + 1)}) := by
    intro m n hmn ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    linarith
  rw [hU, hmono.measure_iUnion]
  refine iSup_le fun n => hlt _ ?_
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem count_set_eq {N : ℕ} (s : ℕ) (A : Set ℝ) :
    {x : Fin N → ℝ | s ≤ (Finset.univ.filter fun k => x k ∈ A).card} =
      ⋃ B ∈ (Finset.univ.filter fun B : Finset (Fin N) => s ≤ B.card),
        Set.pi univ (fun k => if k ∈ B then A else Aᶜ) := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_pi,
    mem_univ, forall_const, exists_prop]
  constructor
  · intro h
    refine ⟨_, h, fun k => ?_⟩
    by_cases hk : x k ∈ A
    · simp [hk]
    · simp [hk]
  · rintro ⟨B, hB, hx⟩
    have : (Finset.univ.filter fun k => x k ∈ A) = B := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hx k
      by_cases hk : k ∈ B
      · simp only [hk, if_true] at this
        simp [hk, this]
      · simp only [hk, if_false] at this
        simpa [hk] using this
    rw [this]; exact hB

theorem count_set_meas {N : ℕ} (s : ℕ) (A : Set ℝ) (hA : MeasurableSet A) :
    MeasurableSet {x : Fin N → ℝ | s ≤ (Finset.univ.filter fun k => x k ∈ A).card} := by
  rw [count_set_eq]
  exact Finset.measurableSet_biUnion _
    (fun B _ => MeasurableSet.univ_pi (fun k => by split_ifs; exacts [hA, hA.compl]))

theorem pi_count_eq {N : ℕ} (s : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : Set ℝ)
    (hA : MeasurableSet A) :
    (Measure.pi fun _ : Fin N => μ) {x | s ≤ (Finset.univ.filter fun k => x k ∈ A).card} =
      ∑ m ∈ Finset.range (N + 1),
        (N.choose m) • (if s ≤ m then μ A ^ m * μ Aᶜ ^ (N - m) else 0) := by
  rw [count_set_eq, measure_biUnion_finset]
  · have h1 : ∀ B : Finset (Fin N), (Measure.pi fun _ : Fin N => μ)
        (Set.pi univ (fun k => if k ∈ B then A else Aᶜ)) = μ A ^ B.card * μ Aᶜ ^ (N - B.card) := by
      intro B
      rw [Measure.pi_pi]
      have e : (fun k => μ (if k ∈ B then A else Aᶜ)) = fun k => if k ∈ B then μ A else μ Aᶜ :=
        funext fun k => by split_ifs <;> rfl
      rw [e, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
      have hc1 : (Finset.univ.filter fun k => k ∈ B) = B := by ext; simp
      have hc2 : (Finset.univ.filter fun k => k ∉ B) = Bᶜ := by ext; simp
      rw [hc1, hc2, Finset.card_compl, Fintype.card_fin]
    rw [Finset.sum_congr rfl (fun B _ => h1 B), Finset.sum_filter, ← Finset.powerset_univ]
    have := Finset.sum_powerset_apply_card
      (fun m => if s ≤ m then μ A ^ m * μ Aᶜ ^ (N - m) else 0) (x := (Finset.univ : Finset (Fin N)))
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact this
  · intro B _ B' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    apply hne
    simp only [Set.mem_pi, mem_univ, forall_const] at hx hx'
    ext k
    have h1 := hx k
    have h2 := hx' k
    by_cases hk : k ∈ B <;> by_cases hk' : k ∈ B' <;> simp_all
  · intro B _
    exact MeasurableSet.univ_pi (fun k => by split_ifs; exacts [hA, hA.compl])

theorem F_mono (N s : ℕ) {q p : ℝ} (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp1 : p ≤ 1) :
    ∑ m ∈ Finset.range (N + 1), (N.choose m) •
        (if s ≤ m then ENNReal.ofReal q ^ m * ENNReal.ofReal (1 - q) ^ (N - m) else 0)
      ≤ ∑ m ∈ Finset.range (N + 1), (N.choose m) •
        (if s ≤ m then ENNReal.ofReal p ^ m * ENNReal.ofReal (1 - p) ^ (N - m) else 0) := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  haveI : IsProbabilityMeasure ν := ⟨by simp [ν, Real.volume_Icc]⟩
  have hν : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ν (Iic t) = ENNReal.ofReal t ∧ ν (Iic t)ᶜ = ENNReal.ofReal (1 - t) := by
    intro t h0 h1
    have e : ν (Iic t) = ENNReal.ofReal t := by
      simp only [ν, Measure.restrict_apply measurableSet_Iic]
      have : Iic t ∩ Icc 0 1 = Icc 0 t := by
        ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
        constructor
        · rintro ⟨a, b, c⟩; exact ⟨b, a⟩
        · rintro ⟨a, b⟩; exact ⟨b, a, by linarith⟩
      rw [this, Real.volume_Icc, sub_zero]
    refine ⟨e, ?_⟩
    rw [prob_compl_eq_one_sub measurableSet_Iic, e, ENNReal.ofReal_sub _ h0, ENNReal.ofReal_one]
  obtain ⟨hq1, hq2⟩ := hν q hq0 (by linarith)
  obtain ⟨hp1', hp2⟩ := hν p (by linarith) hp1
  rw [← hq1, ← hq2, ← hp1', ← hp2, ← pi_count_eq s ν _ measurableSet_Iic,
    ← pi_count_eq s ν _ measurableSet_Iic]
  apply measure_mono
  intro x hx
  simp only [mem_ofPred_eq] at hx ⊢
  refine le_trans hx (Finset.card_le_card ?_)
  intro k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_Iic]
  intro h; linarith

theorem pi_count_le {N : ℕ} (s : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (A : Set ℝ)
    (hA : MeasurableSet A) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hμ : μ A ≤ ENNReal.ofReal p) :
    (Measure.pi fun _ : Fin N => μ) {x | s ≤ (Finset.univ.filter fun k => x k ∈ A).card} ≤
      ENNReal.ofReal (∑ j ∈ Finset.Icc s N, (N.choose j : ℝ) * (1 - p) ^ (N - j) * p ^ j) := by
  set q := (μ A).toReal with hqdef
  have hq : μ A = ENNReal.ofReal q := (ENNReal.ofReal_toReal (measure_ne_top μ A)).symm
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  have hqp : q ≤ p := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ
    rwa [ENNReal.toReal_ofReal hp0] at this
  have hAc : μ Aᶜ = ENNReal.ofReal (1 - q) := by
    rw [prob_compl_eq_one_sub hA, hq, ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one]
  rw [pi_count_eq s μ A hA, hAc, hq]
  refine le_trans (F_mono N s hq0 hqp hp1) (le_of_eq ?_)
  have hfil : (Finset.range (N + 1)).filter (fun m => s ≤ m) = Finset.Icc s N := by
    ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
  have hp' : 0 ≤ 1 - p := by linarith
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (mul_nonneg (by positivity)
    (pow_nonneg hp' _)) (pow_nonneg hp0 _))]
  calc _ = ∑ m ∈ Finset.range (N + 1), if s ≤ m then
          (N.choose m) • (ENNReal.ofReal p ^ m * ENNReal.ofReal (1 - p) ^ (N - m)) else 0 := by
        apply Finset.sum_congr rfl; intro m _; split_ifs <;> simp
    _ = ∑ m ∈ Finset.Icc s N,
          (N.choose m) • (ENNReal.ofReal p ^ m * ENNReal.ofReal (1 - p) ^ (N - m)) := by
        rw [← Finset.sum_filter, hfil]
    _ = _ := by
        apply Finset.sum_congr rfl; intro j _
        rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) (pow_nonneg hp' _)),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hp', ENNReal.ofReal_pow hp0,
          ENNReal.ofReal_natCast, nsmul_eq_mul]
        ring

theorem count_lt_of_sorted {N : ℕ} (f : Fin N → ℝ) (j : Fin N) (c : ℝ)
    (h : (f ∘ Tuple.sort f) j < c) :
    j.val + 1 ≤ (Finset.univ.filter fun k => f k ∈ Iio c).card := by
  have hmono : Monotone (f ∘ Tuple.sort f) := Tuple.monotone_sort f
  calc j.val + 1 = (Finset.Iic j).card := (Fin.card_Iic j).symm
    _ ≤ _ := by
      apply Finset.card_le_card_of_injOn (Tuple.sort f)
      · intro m hm
        simp only [Finset.coe_Iic, mem_Iic, Finset.coe_filter, Finset.mem_univ, true_and,
          mem_ofPred_eq, Finset.mem_Iic, Finset.mem_filter] at hm ⊢
        exact lt_of_le_of_lt (hmono hm) h
      · exact (Tuple.sort f).injective.injOn

theorem count_gt_of_sorted {N : ℕ} (f : Fin N → ℝ) (j : Fin N) (c : ℝ)
    (h : c < (f ∘ Tuple.sort f) j) :
    N - j.val ≤ (Finset.univ.filter fun k => f k ∈ Ioi c).card := by
  have hmono : Monotone (f ∘ Tuple.sort f) := Tuple.monotone_sort f
  calc N - j.val = (Finset.Ici j).card := (Fin.card_Ici j).symm
    _ ≤ _ := by
      apply Finset.card_le_card_of_injOn (Tuple.sort f)
      · intro m hm
        simp only [Finset.coe_Ici, mem_Ici, Finset.coe_filter, Finset.mem_univ, true_and,
          mem_ofPred_eq, Finset.mem_Ici, Finset.mem_filter] at hm ⊢
        exact lt_of_lt_of_le h (hmono hm)
      · exact (Tuple.sort f).injective.injOn

open DataDrivenRO.Marginal

theorem sIndex_spec {d N : ℕ} (ε α : ℝ) (hα0 : 0 < α) (hd : 0 < d) :
    ∑ j ∈ Finset.Icc (sIndex N d ε α) N,
        (N.choose j : ℝ) * (ε / d) ^ (N - j) * (1 - ε / d) ^ j ≤ α / (2 * d) ∧
      sIndex N d ε α ≤ N + 1 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hex : ∃ k : ℕ, ∑ j ∈ Finset.Icc k N,
      (N.choose j : ℝ) * (ε / d) ^ (N - j) * (1 - ε / d) ^ j ≤ α / (2 * d) := by
    refine ⟨N + 1, ?_⟩
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  unfold sIndex
  rw [dif_pos hex]
  refine ⟨Nat.find_spec hex, Nat.find_min' hex ?_⟩
  rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
  positivity

theorem Q_count_le {d N : ℕ} (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (Q : Measure (Fin N → Fin d → ℝ)) (hQ : IsMarginalSampleLaw Pstar Q) (i : Fin d)
    (s : ℕ) (A : Set ℝ) (hA : MeasurableSet A) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hPA : Pstar {u | u i ∈ A} ≤ ENNReal.ofReal p) :
    Q {S | s ≤ (Finset.univ.filter fun k => S k i ∈ A).card} ≤
      ENNReal.ofReal (∑ j ∈ Finset.Icc s N, (N.choose j : ℝ) * (1 - p) ^ (N - j) * p ^ j) := by
  have hf : Measurable (fun (S : Fin N → Fin d → ℝ) (k : Fin N) => S k i) :=
    measurable_pi_lambda _ (fun k => (measurable_pi_apply i).comp (measurable_pi_apply k))
  have h1 : Q {S | s ≤ (Finset.univ.filter fun k => S k i ∈ A).card} =
      (Q.map (fun (S : Fin N → Fin d → ℝ) (k : Fin N) => S k i))
        {x : Fin N → ℝ | s ≤ (Finset.univ.filter fun k => x k ∈ A).card} := by
    rw [Measure.map_apply hf (count_set_meas s A hA)]; rfl
  rw [h1, hQ.2 i]
  haveI : IsProbabilityMeasure (Pstar.map fun u => u i) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
  apply pi_count_le s _ A hA hp0 hp1
  rw [Measure.map_apply (measurable_pi_apply i) hA]; exact hPA

theorem meas_dot {d : ℕ} (w : Fin d → ℝ) : Measurable (fun u : Fin d → ℝ => u ⬝ᵥ w) :=
  (Continuous.dotProduct continuous_id continuous_const).measurable

theorem test_up {d N : ℕ} (hd : 0 < d) (ε α : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hα0 : 0 < α) (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (Q : Measure (Fin N → Fin d → ℝ)) (hQ : IsMarginalSampleLaw Pstar Q) (lo hi : Fin d → ℝ)
    (hsupp : Pstar (box lo hi)ᶜ = 0) (hs : N + 1 - sIndex N d ε α < sIndex N d ε α) (i : Fin d) :
    Q {S | uhat S lo hi i (sIndex N d ε α) < VaR Pstar (ε / d) (Pi.single i 1)}
      ≤ ENNReal.ofReal (α / (2 * d)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hεd0 : 0 < ε / d := div_pos hε0 hdpos
  have hεd1 : ε / d < 1 := by
    rw [div_lt_one hdpos]; have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨hsum, hsle⟩ := sIndex_spec (N := N) ε α hα0 hd
  set s := sIndex N d ε α with hsdef
  set V := VaR Pstar (ε / d) (Pi.single i 1) with hV
  have hZ := meas_dot (Pi.single i (1 : ℝ))
  by_cases hsN : N < s
  · have hVle : V ≤ hi i := by
      apply vle_le Pstar _ hZ (α := 1 - ε / d) (by linarith) (hi i)
      have hmeas : MeasurableSet {u : Fin d → ℝ | u ⬝ᵥ Pi.single i 1 ≤ hi i} :=
        measurableSet_le hZ measurable_const
      have : Pstar {u : Fin d → ℝ | u ⬝ᵥ Pi.single i 1 ≤ hi i} = 1 := by
        rw [← prob_compl_eq_zero_iff hmeas]
        refine measure_mono_null (fun u hu => ?_) hsupp
        simp only [mem_compl_iff, mem_ofPred_eq, dotProduct_single, mul_one, box] at hu ⊢
        intro h; exact hu (h i).2
      rw [this]; exact ENNReal.ofReal_le_one.mpr (by linarith)
    have : {S : Fin N → Fin d → ℝ | uhat S lo hi i s < V} = ∅ := by
      ext S
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      unfold uhat
      rw [dif_neg (by omega), dif_pos hsN]
      exact hVle
    rw [this, measure_empty]; exact bot_le
  · have hs0 : s ≠ 0 := by omega
    have hsub : {S : Fin N → Fin d → ℝ | uhat S lo hi i s < V} ⊆
        {S | s ≤ (Finset.univ.filter fun k => S k i ∈ Iio V).card} := by
      intro S hS
      simp only [mem_ofPred_eq] at hS ⊢
      unfold uhat at hS
      rw [dif_neg hs0, dif_neg hsN] at hS
      have := count_lt_of_sorted (fun k => S k i) ⟨s - 1, by omega⟩ V hS
      simp only at this
      omega
    have hPA : Pstar {u : Fin d → ℝ | u i ∈ Iio V} ≤ ENNReal.ofReal (1 - ε / d) := by
      have e : {u : Fin d → ℝ | u i ∈ Iio V} =
          {u | (fun u : Fin d → ℝ => u ⬝ᵥ Pi.single i 1) u <
            MultistageStochastic.valueAtRisk Pstar (fun u => u ⬝ᵥ Pi.single i 1) (1 - ε / d)} := by
        ext u; simp [dotProduct_single, hV, VaR]
      rw [e]; exact lt_var_le Pstar _ hZ (by linarith)
    refine le_trans (measure_mono hsub) (le_trans (Q_count_le Pstar Q hQ i s (Iio V)
      measurableSet_Iio (by linarith) (by linarith) hPA) ?_)
    apply ENNReal.ofReal_le_ofReal
    simp only [sub_sub_cancel]
    exact hsum

theorem test_lo {d N : ℕ} (hd : 0 < d) (ε α : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hα0 : 0 < α) (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (Q : Measure (Fin N → Fin d → ℝ)) (hQ : IsMarginalSampleLaw Pstar Q) (lo hi : Fin d → ℝ)
    (hsupp : Pstar (box lo hi)ᶜ = 0) (hs : N + 1 - sIndex N d ε α < sIndex N d ε α) (i : Fin d) :
    Q {S | -uhat S lo hi i (N + 1 - sIndex N d ε α) < VaR Pstar (ε / d) (Pi.single i (-1))}
      ≤ ENNReal.ofReal (α / (2 * d)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hεd0 : 0 < ε / d := div_pos hε0 hdpos
  have hεd1 : ε / d < 1 := by
    rw [div_lt_one hdpos]; have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨hsum, hsle⟩ := sIndex_spec (N := N) ε α hα0 hd
  set s := sIndex N d ε α with hsdef
  set W := VaR Pstar (ε / d) (Pi.single i (-1)) with hW
  have hZ := meas_dot (Pi.single i (-1 : ℝ))
  by_cases hr : N + 1 - s = 0
  · have hWle : W ≤ -lo i := by
      apply vle_le Pstar _ hZ (α := 1 - ε / d) (by linarith) (-lo i)
      have hmeas : MeasurableSet {u : Fin d → ℝ | u ⬝ᵥ Pi.single i (-1) ≤ -lo i} :=
        measurableSet_le hZ measurable_const
      have : Pstar {u : Fin d → ℝ | u ⬝ᵥ Pi.single i (-1) ≤ -lo i} = 1 := by
        rw [← prob_compl_eq_zero_iff hmeas]
        refine measure_mono_null (fun u hu => ?_) hsupp
        simp only [mem_compl_iff, mem_ofPred_eq, dotProduct_single, mul_neg, mul_one,
          neg_le_neg_iff, box] at hu ⊢
        intro h; exact hu (h i).1
      rw [this]; exact ENNReal.ofReal_le_one.mpr (by linarith)
    have : {S : Fin N → Fin d → ℝ | -uhat S lo hi i (N + 1 - s) < W} = ∅ := by
      ext S
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      unfold uhat
      rw [dif_pos hr]
      exact hWle
    rw [this, measure_empty]; exact bot_le
  · have hrN : ¬ N < N + 1 - s := by omega
    have hsub : {S : Fin N → Fin d → ℝ | -uhat S lo hi i (N + 1 - s) < W} ⊆
        {S | s ≤ (Finset.univ.filter fun k => S k i ∈ Ioi (-W)).card} := by
      intro S hS
      simp only [mem_ofPred_eq] at hS ⊢
      unfold uhat at hS
      rw [dif_neg hr, dif_neg hrN] at hS
      have := count_gt_of_sorted (fun k => S k i) ⟨N + 1 - s - 1, by omega⟩ (-W)
        (by unfold orderStat at hS; linarith)
      simp only at this
      omega
    have hPA : Pstar {u : Fin d → ℝ | u i ∈ Ioi (-W)} ≤ ENNReal.ofReal (1 - ε / d) := by
      have e : {u : Fin d → ℝ | u i ∈ Ioi (-W)} =
          {u | (fun u : Fin d → ℝ => u ⬝ᵥ Pi.single i (-1)) u <
            MultistageStochastic.valueAtRisk Pstar (fun u => u ⬝ᵥ Pi.single i (-1)) (1 - ε / d)} := by
        ext u
        show -W < u i ↔ u ⬝ᵥ Pi.single i (-1) < W
        rw [dotProduct_single]; constructor <;> intro h <;> linarith
      rw [e]; exact lt_var_le Pstar _ hZ (by linarith)
    refine le_trans (measure_mono hsub) (le_trans (Q_count_le Pstar Q hQ i s (Ioi (-W))
      measurableSet_Ioi (by linarith) (by linarith) hPA) ?_)
    apply ENNReal.ofReal_le_ofReal
    simp only [sub_sub_cancel]
    exact hsum

theorem vle_nonempty (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu1 : u < 1) :
    ({x | u ≤ cdf μ x} : Set ℝ).Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds hu1)).exists
  exact ⟨x, hx.le⟩

theorem vle_attain (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu1 : u < 1) :
    u ≤ cdf μ (sInf {x | u ≤ cdf μ x}) := by
  have hcont : ContinuousWithinAt (cdf μ) (Ici (sInf {x | u ≤ cdf μ x}))
      (sInf {x | u ≤ cdf μ x}) := (cdf μ).right_continuous _
  have ht : Tendsto (cdf μ) (𝓝[>] (sInf {x | u ≤ cdf μ x}))
      (𝓝 (cdf μ (sInf {x | u ≤ cdf μ x}))) := hcont.mono Ioi_subset_Ici_self
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt (vle_nonempty μ hu1) hx
  exact le_trans hs (monotone_cdf μ hsx.le)

/-- The VaR level set is attained: `α ≤ P.real {Z ≤ valueAtRisk P Z α}` for `α < 1`. -/
theorem vle_attain_real {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) {α : ℝ} (hα1 : α < 1) :
    α ≤ P.real {ω | Z ω ≤ MultistageStochastic.valueAtRisk P Z α} := by
  have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  unfold MultistageStochastic.valueAtRisk
  rw [vle_set_eq P Z hZ α]
  have h := vle_attain (P.map Z) hα1
  have h1 : P {ω | Z ω ≤ sInf {x | α ≤ cdf (P.map Z) x}}
      = ENNReal.ofReal (cdf (P.map Z) (sInf {x | α ≤ cdf (P.map Z) x})) := by
    rw [ofReal_cdf, Measure.map_apply hZ measurableSet_Iic]; rfl
  rw [measureReal_def, h1, ENNReal.toReal_ofReal (cdf_nonneg _ _)]
  exact h

theorem vle_le_real {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) {α : ℝ} (hα0 : 0 < α) (t : ℝ)
    (ht : α ≤ P.real {ω | Z ω ≤ t}) :
    MultistageStochastic.valueAtRisk P Z α ≤ t := by
  have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  unfold MultistageStochastic.valueAtRisk
  rw [vle_set_eq P Z hZ α]
  refine csInf_le (vle_bdd (P.map Z) hα0) ?_
  have h1 : P {ω | Z ω ≤ t} = ENNReal.ofReal (cdf (P.map Z) t) := by
    rw [ofReal_cdf, Measure.map_apply hZ measurableSet_Iic]; rfl
  rw [measureReal_def, h1, ENNReal.toReal_ofReal (cdf_nonneg _ _)] at ht
  exact ht

theorem var_le_sum_coord' {d : ℕ} (hd : 0 < d) (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : Fin d → ℝ) :
    VaR P ε v ≤ ∑ i, VaR P (ε / d) (Pi.single i (v i)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hdge : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hεd0 : 0 < ε / d := div_pos hε0 hdpos
  have hεd1 : ε / d < 1 := by
    rw [div_lt_one hdpos]; linarith
  set Zi : Fin d → (Fin d → ℝ) → ℝ := fun i u => u ⬝ᵥ Pi.single i (v i) with hZi
  have hZim : ∀ i, Measurable (Zi i) := fun i =>
    (Continuous.dotProduct continuous_id continuous_const).measurable
  have hZm : Measurable (fun u : Fin d → ℝ => u ⬝ᵥ v) :=
    (Continuous.dotProduct continuous_id continuous_const).measurable
  set t : Fin d → ℝ := fun i => VaR P (ε / d) (Pi.single i (v i)) with ht
  have hA : ∀ i, 1 - ε / d ≤ P.real {u | Zi i u ≤ t i} := fun i =>
    vle_attain_real P (Zi i) (hZim i) (by linarith)
  have hsum : ∀ u : Fin d → ℝ, u ⬝ᵥ v = ∑ i, Zi i u := by
    intro u
    simp only [hZi, dotProduct_single]
    rfl
  -- complement bound
  have hsub : {u : Fin d → ℝ | u ⬝ᵥ v ≤ ∑ i, t i}ᶜ ⊆ ⋃ i, {u | Zi i u ≤ t i}ᶜ := by
    intro u hu
    simp only [mem_compl_iff, mem_ofPred_eq, mem_iUnion] at hu ⊢
    by_contra hcon
    push Not at hcon
    apply hu
    rw [hsum u]
    exact Finset.sum_le_sum fun i _ => hcon i
  have hmB : MeasurableSet {u : Fin d → ℝ | u ⬝ᵥ v ≤ ∑ i, t i} :=
    measurableSet_le hZm measurable_const
  have hmA : ∀ i, MeasurableSet {u : Fin d → ℝ | Zi i u ≤ t i} := fun i =>
    measurableSet_le (hZim i) measurable_const
  have hcB : P.real {u : Fin d → ℝ | u ⬝ᵥ v ≤ ∑ i, t i}ᶜ ≤ ε := by
    calc P.real {u : Fin d → ℝ | u ⬝ᵥ v ≤ ∑ i, t i}ᶜ
        ≤ P.real (⋃ i, {u | Zi i u ≤ t i}ᶜ) := measureReal_mono hsub
      _ ≤ ∑ i, P.real {u | Zi i u ≤ t i}ᶜ := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : Fin d, ε / d := by
          apply Finset.sum_le_sum
          intro i _
          rw [probReal_compl_eq_one_sub (hmA i)]
          linarith [hA i]
      _ = ε := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hB : 1 - ε ≤ P.real {u : Fin d → ℝ | u ⬝ᵥ v ≤ ∑ i, t i} := by
    rw [probReal_compl_eq_one_sub hmB] at hcB
    linarith
  exact vle_le_real P (fun u => u ⬝ᵥ v) hZm (by linarith) _ hB

open Pointwise in
theorem var_pos_homog' {d : ℕ} (P : Measure (Fin d → ℝ)) (δ : ℝ)
    (c : ℝ) (hc : 0 < c) (w : Fin d → ℝ) :
    VaR P δ (c • w) = c * VaR P δ w := by
  unfold VaR MultistageStochastic.valueAtRisk
  have hset : {y : ℝ | ENNReal.ofReal (1 - δ) ≤ P {ω | ω ⬝ᵥ (c • w) ≤ y}}
      = c • {y : ℝ | ENNReal.ofReal (1 - δ) ≤ P {ω | ω ⬝ᵥ w ≤ y}} := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
    simp only [Set.mem_ofPred_eq, smul_eq_mul]
    have : {ω : Fin d → ℝ | ω ⬝ᵥ (c • w) ≤ y} = {ω | ω ⬝ᵥ w ≤ c⁻¹ * y} := by
      ext ω
      simp only [Set.mem_ofPred_eq, dotProduct_smul, smul_eq_mul]
      rw [le_inv_mul_iff₀ hc]
    rw [this]
  rw [hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]

theorem box_support {d : ℕ} (a b : Fin d → ℝ) (hab : ∀ i, a i ≤ b i) (v : Fin d → ℝ) :
    sSup ((fun p : Fin d → ℝ => ∑ j, p j * v j) '' {u | ∀ i, a i ≤ u i ∧ u i ≤ b i}) =
      ∑ i, max (v i * a i) (v i * b i) := by
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun i => if 0 ≤ v i then b i else a i, ?_, ?_⟩
    · intro i
      have := hab i
      show a i ≤ (if 0 ≤ v i then b i else a i) ∧ (if 0 ≤ v i then b i else a i) ≤ b i
      split_ifs <;> constructor <;> linarith
    · simp only
      apply Finset.sum_congr rfl
      intro i _
      have := hab i
      split_ifs with h
      · rw [max_eq_right (by nlinarith)]; ring
      · rw [max_eq_left (by nlinarith)]; ring
  · rintro x ⟨u, hu, rfl⟩
    simp only
    apply Finset.sum_le_sum
    intro i _
    obtain ⟨h1, h2⟩ := hu i
    rcases le_or_gt 0 (v i) with h | h
    · exact le_trans (by nlinarith) (le_max_right _ _)
    · exact le_trans (by nlinarith) (le_max_left _ _)

theorem uhat_mono {d N : ℕ} (S : Fin N → Fin d → ℝ) (lo hi : Fin d → ℝ) (hlohi : lo ≤ hi)
    (i : Fin d) (a b : ℕ) (hab : a < b) (hsum : a + b = N + 1 ∨ (a = 0 ∧ N + 1 ≤ b)) :
    uhat S lo hi i a ≤ uhat S lo hi i b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hb : N < b := by omega
    simp [uhat, hb, show b ≠ 0 by omega]
    exact hlohi i
  · have hb : ¬ N < b := by omega
    have ha' : ¬ N < a := by omega
    simp only [uhat, dif_neg (show a ≠ 0 by omega), dif_neg (show b ≠ 0 by omega), dif_neg hb,
      dif_neg ha']
    apply Tuple.monotone_sort
    show a - 1 ≤ b - 1
    omega

theorem uhat_le' {d N : ℕ} (ε α : ℝ) (lo hi : Fin d → ℝ) (hlohi : lo ≤ hi)
    (hs : N + 1 - sIndex N d ε α < sIndex N d ε α) (S : Fin N → Fin d → ℝ) (i : Fin d) :
    uhat S lo hi i (N + 1 - sIndex N d ε α) ≤ uhat S lo hi i (sIndex N d ε α) :=
  uhat_mono S lo hi hlohi i _ _ hs (by omega)

theorem support_formula {d N : ℕ} (ε α : ℝ) (lo hi : Fin d → ℝ) (hlohi : lo ≤ hi)
    (hs : N + 1 - sIndex N d ε α < sIndex N d ε α) (S : Fin N → Fin d → ℝ) (v : Fin d → ℝ) :
    RobustMDP.Shared.supportFunction (UM S lo hi ε α) v =
      ∑ i, max (v i * uhat S lo hi i (N + 1 - sIndex N d ε α))
        (v i * uhat S lo hi i (sIndex N d ε α)) := by
  unfold RobustMDP.Shared.supportFunction UM
  exact box_support _ _ (uhat_le' ε α lo hi hlohi hs S) v

theorem var_zero_le {d : ℕ} (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P] {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) : VaR P δ 0 ≤ 0 := by
  apply vle_le P _ (meas_dot 0) (by linarith) 0
  have : {u : Fin d → ℝ | u ⬝ᵥ (0 : Fin d → ℝ) ≤ 0} = univ := by ext u; simp
  rw [this, measure_univ]; exact ENNReal.ofReal_le_one.mpr (by linarith)

theorem good_of_tests {d N : ℕ} (hd : 0 < d) (ε α : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar] (lo hi : Fin d → ℝ)
    (hlohi : lo ≤ hi) (hs : N + 1 - sIndex N d ε α < sIndex N d ε α) (S : Fin N → Fin d → ℝ)
    (hS : ∀ i, VaR Pstar (ε / d) (Pi.single i 1) ≤ uhat S lo hi i (sIndex N d ε α) ∧
      VaR Pstar (ε / d) (Pi.single i (-1)) ≤ -uhat S lo hi i (N + 1 - sIndex N d ε α))
    (v : Fin d → ℝ) :
    VaR Pstar ε v ≤ RobustMDP.Shared.supportFunction (UM S lo hi ε α) v := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hεd1 : ε / d < 1 := by
    rw [div_lt_one hdpos]; have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [support_formula ε α lo hi hlohi hs S v]
  refine le_trans (var_le_sum_coord' hd Pstar ε hε0 hε1 v) (Finset.sum_le_sum fun i _ => ?_)
  obtain ⟨h1, h2⟩ := hS i
  rcases lt_trichotomy (v i) 0 with hv | hv | hv
  · have e : Pi.single i (v i) = (-v i) • (Pi.single i (-1) : Fin d → ℝ) := by
      ext j; rcases eq_or_ne j i with rfl | h <;> simp [*]
    rw [e, var_pos_homog' Pstar _ _ (by linarith)]
    refine le_trans ?_ (le_max_left _ _)
    nlinarith
  · have e : Pi.single i (v i) = (0 : Fin d → ℝ) := by rw [hv]; exact Pi.single_zero i
    rw [e, hv]; simp only [zero_mul, max_self]
    exact var_zero_le Pstar (div_pos hε0 hdpos) hεd1
  · have e : Pi.single i (v i) = (v i) • (Pi.single i 1 : Fin d → ℝ) := by
      ext j; rcases eq_or_ne j i with rfl | h <;> simp [*]
    rw [e, var_pos_homog' Pstar _ _ hv]
    refine le_trans ?_ (le_max_right _ _)
    nlinarith

end P0ce6640c

open MeasureTheory DataDrivenRO.Marginal in
theorem solution {d N : ℕ} (hd : 0 < d) (ε α : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hα0 : 0 < α) (hα1 : α < 1)
    (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (Q : Measure (Fin N → Fin d → ℝ)) (hQ : IsMarginalSampleLaw Pstar Q) (lo hi : Fin d → ℝ)
    (hlohi : lo ≤ hi) (hsupp : Pstar (box lo hi)ᶜ = 0)
    (hs : N + 1 - sIndex N d ε α < sIndex N d ε α) :
    ENNReal.ofReal (1 - α) ≤
        Q {S | ∀ v, VaR Pstar ε v ≤ RobustMDP.Shared.supportFunction (UM S lo hi ε α) v} ∧
      (∀ (S : Fin N → Fin d → ℝ) (v : Fin d → ℝ),
        RobustMDP.Shared.supportFunction (UM S lo hi ε α) v =
          ∑ i, max (v i * uhat S lo hi i (N + 1 - sIndex N d ε α))
            (v i * uhat S lo hi i (sIndex N d ε α))) ∧
      (∀ S : Fin N → Fin d → ℝ,
        (UM S lo hi ε α).Nonempty ∧ Convex ℝ (UM S lo hi ε α) ∧
          IsCompact (UM S lo hi ε α)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨?_, fun S v => P0ce6640c.support_formula ε α lo hi hlohi hs S v, fun S => ?_⟩
  · haveI := hQ.1
    set G := {S : Fin N → Fin d → ℝ |
      ∀ v, VaR Pstar ε v ≤ RobustMDP.Shared.supportFunction (UM S lo hi ε α) v} with hG
    set Bad := ⋃ i : Fin d,
      ({S : Fin N → Fin d → ℝ | uhat S lo hi i (sIndex N d ε α) < VaR Pstar (ε / d) (Pi.single i 1)} ∪
        {S | -uhat S lo hi i (N + 1 - sIndex N d ε α) < VaR Pstar (ε / d) (Pi.single i (-1))})
      with hBad
    have hsub : Gᶜ ⊆ Bad := by
      intro S hS
      by_contra hB
      apply hS
      intro v
      apply P0ce6640c.good_of_tests hd ε α hε0 hε1 Pstar lo hi hlohi hs S _ v
      intro i
      simp only [hBad, Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, not_exists, not_or,
        not_lt] at hB
      exact hB i
    have hBadle : Q Bad ≤ ENNReal.ofReal α := by
      calc Q Bad ≤ ∑ i : Fin d, Q ({S : Fin N → Fin d → ℝ |
              uhat S lo hi i (sIndex N d ε α) < VaR Pstar (ε / d) (Pi.single i 1)} ∪
            {S | -uhat S lo hi i (N + 1 - sIndex N d ε α) < VaR Pstar (ε / d) (Pi.single i (-1))}) :=
            measure_iUnion_fintype_le _ _
        _ ≤ ∑ _i : Fin d, (ENNReal.ofReal (α / (2 * d)) + ENNReal.ofReal (α / (2 * d))) := by
            apply Finset.sum_le_sum
            intro i _
            exact le_trans (measure_union_le _ _) (add_le_add
              (P0ce6640c.test_up hd ε α hε0 hε1 hα0 Pstar Q hQ lo hi hsupp hs i)
              (P0ce6640c.test_lo hd ε α hε0 hε1 hα0 Pstar Q hQ lo hi hsupp hs i))
        _ = ENNReal.ofReal α := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            congr 1
            field_simp
            ring
    have h1 : (1 : ENNReal) ≤ Q G + ENNReal.ofReal α := by
      calc (1 : ENNReal) = Q univ := measure_univ.symm
        _ ≤ Q G + Q Gᶜ := by
            rw [← Set.union_compl_self G]; exact measure_union_le _ _
        _ ≤ Q G + ENNReal.ofReal α := add_le_add le_rfl (le_trans (measure_mono hsub) hBadle)
    rw [ENNReal.ofReal_sub _ hα0.le, ENNReal.ofReal_one]
    exact tsub_le_iff_right.mpr h1
  · have hUM : UM S lo hi ε α = Set.pi univ (fun i =>
        Icc (uhat S lo hi i (N + 1 - sIndex N d ε α)) (uhat S lo hi i (sIndex N d ε α))) := by
      ext u
      simp only [UM, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    rw [hUM]
    refine ⟨⟨fun i => uhat S lo hi i (N + 1 - sIndex N d ε α), fun i _ =>
      ⟨le_rfl, P0ce6640c.uhat_le' ε α lo hi hlohi hs S i⟩⟩, ?_, ?_⟩
    · exact convex_pi (fun i _ => convex_Icc _ _)
    · exact isCompact_univ_pi (fun i => isCompact_Icc)
