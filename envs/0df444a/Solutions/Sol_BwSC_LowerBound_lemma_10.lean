-- Prove2me | solution 1 for BwSC.LowerBound.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T03:23:00.040933+00:00
-- url     : https://prove2.me/submissions/f3479793-71a0-4c7c-b042-6c8a7ce4aeb7

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound.L10Aux

lemma iSup_update {K : ℕ} (k : Fin K) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    (⨆ i, Function.update (0 : Fin K → ℝ) k Δ i) = Δ := by
  haveI : Nonempty (Fin K) := ⟨k⟩
  apply le_antisymm
  · apply ciSup_le
    intro i
    by_cases hi : i = k
    · subst hi; simp
    · simp [Function.update_of_ne hi, hΔ]
  · have := le_ciSup (Set.finite_range (Function.update (0 : Fin K → ℝ) k Δ)).bddAbove k
    simpa using this

/-- On "`k` not chosen in `[lo, hi]`" (with `hi ≤ T`), the pseudo-regret under `Δ·e_k`
is at least `Δ · #{rounds in [max lo 1, hi]}`. -/
lemma regret_window {K T : ℕ} (k : Fin K) (Δ : ℝ) (hΔ : 0 ≤ Δ) (h : BanditHistory K T)
    (lo hi : ℕ) (hhi : hi ≤ T) (hE : notChosen h k lo hi) :
    Δ * ((hi - (lo - 1) : ℕ) : ℝ) ≤ regretOf (Function.update (0 : Fin K → ℝ) k Δ) h := by
  set μ := Function.update (0 : Fin K → ℝ) k Δ with hμ
  have hsup : (⨆ i, μ i) = Δ := iSup_update k Δ hΔ
  unfold regretOf
  rw [hsup]
  -- rewrite the pseudo-regret as a sum over `range T`
  set g : ℕ → ℝ := fun i => if hi' : i < T then Δ - μ (h ⟨i, hi'⟩).1 else 0 with hg
  have hsum : (T : ℝ) * Δ - ∑ t, μ (h t).1 = ∑ i ∈ Finset.range T, g i := by
    rw [← Fin.sum_univ_eq_sum_range g T]
    simp only [hg, Fin.is_lt, dif_pos]
    rw [Finset.sum_sub_distrib]
    simp
  rw [hsum]
  have hg0 : ∀ i, 0 ≤ g i := by
    intro i
    simp only [hg]
    split_ifs with hi'
    · have : μ (h ⟨i, hi'⟩).1 ≤ Δ := by
        rw [← hsup]; exact le_ciSup (Set.finite_range μ).bddAbove _
      linarith
    · exact le_rfl
  have hsub : Finset.Ico (lo - 1) hi ⊆ Finset.range T := by
    intro i hi'; simp only [Finset.mem_Ico, Finset.mem_range] at hi' ⊢; omega
  have hval : ∀ i ∈ Finset.Ico (lo - 1) hi, g i = Δ := by
    intro i hi'
    simp only [Finset.mem_Ico] at hi'
    have hiT : i < T := by omega
    simp only [hg, dif_pos hiT]
    have hne : (h ⟨i, hiT⟩).1 ≠ k := by
      intro hk
      apply hE (i + 1) (by omega) (by omega)
      simp [act, actA, actions, hk, hiT]
    rw [hμ, Function.update_of_ne hne]
    simp
  calc Δ * ((hi - (lo - 1) : ℕ) : ℝ) = ∑ i ∈ Finset.Ico (lo - 1) hi, g i := by
        rw [Finset.sum_congr rfl hval, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]; ring
    _ ≤ ∑ i ∈ Finset.range T, g i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hg0 i)

lemma armPullCount_eq {K T : ℕ} (i : Fin K) (h : BanditHistory K T) :
    (armPullCount i h : ℝ) = ∑ t : Fin T, if (h t).1 = i then (1 : ℝ) else 0 := by
  classical
  simp only [armPullCount, Finset.sum_boole]
  congr 1
  congr 1
  ext t; simp

lemma regretOf_eq {K T : ℕ} (μ : Fin K → ℝ) (h : BanditHistory K T) :
    regretOf μ h = ∑ i, ((⨆ j, μ j) - μ i) * (armPullCount i h : ℝ) := by
  classical
  simp_rw [armPullCount_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  unfold regretOf
  rw [Finset.sum_sub_distrib]
  simp

lemma measurable_armPullCount {K T : ℕ} (i : Fin K) :
    Measurable (fun h : BanditHistory K T => (armPullCount i h : ℝ)) := by
  have : (fun h : BanditHistory K T => (armPullCount i h : ℝ)) =
      (fun a : Fin T → Fin K => (({t | a t = i}.toFinset.card : ℕ) : ℝ)) ∘ actions := by
    funext h; rfl
  rw [this]
  exact (measurable_of_finite _).comp measurable_actions

lemma integrable_armPullCount {K T : ℕ} (i : Fin K) (P : Measure (BanditHistory K T))
    [IsFiniteMeasure P] : Integrable (fun h => (armPullCount i h : ℝ)) P := by
  refine Integrable.of_bound (C := T) (measurable_armPullCount i).aestronglyMeasurable
    (ae_of_all _ (fun h => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have : armPullCount i h ≤ T := by
    unfold armPullCount
    exact (Finset.card_le_univ _).trans (by simp)
  exact_mod_cast this

lemma integrable_regretOf {K T : ℕ} (μ : Fin K → ℝ) (P : Measure (BanditHistory K T))
    [IsFiniteMeasure P] : Integrable (regretOf μ) P := by
  have : (regretOf μ : BanditHistory K T → ℝ) =
      fun h => ∑ i, ((⨆ j, μ j) - μ i) * (armPullCount i h : ℝ) := by
    funext h; exact regretOf_eq μ h
  rw [this]
  exact integrable_finsetSum _ (fun i _ => (integrable_armPullCount i P).const_mul _)

lemma regretOf_nonneg {K T : ℕ} (μ : Fin K → ℝ) (h : BanditHistory K T) : 0 ≤ regretOf μ h := by
  rw [regretOf_eq]
  refine Finset.sum_nonneg (fun i _ => mul_nonneg ?_ (Nat.cast_nonneg _))
  exact sub_nonneg.mpr (le_ciSup (Set.finite_range μ).bddAbove i)


lemma measurableSet_of_actions {K T : ℕ} (E : Set (BanditHistory K T))
    (hE : ∀ h h', actions h = actions h' → h ∈ E → h' ∈ E) : MeasurableSet E := by
  have : E = actions ⁻¹' (actions '' E) := by
    ext h; constructor
    · intro hh; exact ⟨h, hh, rfl⟩
    · rintro ⟨h', hh', e⟩; exact hE h' h e hh'
  rw [this]; exact measurable_actions (Set.toFinite _).measurableSet

lemma act_congr {K T : ℕ} {h h' : BanditHistory K T} (e : actions h = actions h') :
    act h = act h' := by
  funext t; simp [act, e]

lemma measurableSet_E2 (S K T j : ℕ) (k : Fin K) : MeasurableSet (E2 S K T j k) := by
  apply measurableSet_of_actions
  intro h h' e hh
  simp only [E2, notChosen, Set.mem_setOf_eq] at hh ⊢
  rw [← act_congr e]; exact hh

/-- From a pointwise bound on an event to the product form. -/
lemma setIntegral_ge {K T : ℕ} (μ : Fin K → ℝ) (P : Measure (BanditHistory K T))
    [IsFiniteMeasure P] (E : Set (BanditHistory K T)) (hE : MeasurableSet E) (c : ℝ)
    (hpt : ∀ h ∈ E, c ≤ regretOf μ h) :
    c * (P E).toReal ≤ ∫ h in E, regretOf μ h ∂P := by
  have h1 : ∫ h in E, c ∂P = c * (P E).toReal := by
    rw [setIntegral_const]; simp [Measure.real, mul_comm]
  rw [← h1]
  exact setIntegral_mono_on (integrableOn_const (by simp)) (integrable_regretOf μ P).integrableOn hE hpt

/-- The core inequality of Lemma 10 for `j ≥ 2`, with `A = y^a`, `B = y^{(1-u)a}`. -/
lemma key_real (K A B n tj tj1 : ℝ) (hK : 0 < K) (hB : 0 < B) (hAB : 2 * B ≤ A) (hn : 0 < n)
    (htj : K * (A * B) - 1 < tj) (htj1 : tj1 ≤ K * B ^ 2) (htj1pos : 0 < tj1) :
    K / (4 * n) * A ≤ 1 / (2 * n) * Real.sqrt (K / tj1) * (tj - tj1 + 1) := by
  have hs : 1 / B ≤ Real.sqrt (K / tj1) := by
    rw [show 1 / B = Real.sqrt (1 / B ^ 2) by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_sq hB.le]]
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ (by positivity) htj1pos]; nlinarith
  have hcnt : K * (A * B) - K * B ^ 2 ≤ tj - tj1 + 1 := by linarith
  have hcnt0 : 0 ≤ K * (A * B) - K * B ^ 2 := by nlinarith
  have h1 : 1 / (2 * n) * (1 / B) * (K * (A * B) - K * B ^ 2) ≤
      1 / (2 * n) * Real.sqrt (K / tj1) * (tj - tj1 + 1) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hcnt hcnt0
    positivity
  have h2 : 1 / (2 * n) * (1 / B) * (K * (A * B) - K * B ^ 2) = K * (A - B) / (2 * n) := by
    field_simp
  rw [h2] at h1
  have h3 : K / (4 * n) * A ≤ K * (A - B) / (2 * n) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hK.le hn.le) (sub_nonneg.mpr hAB)]
  linarith

lemma rpow_grid (K T e : ℝ) (hK : 0 < K) (hT : 0 < T) :
    K ^ (1 - e) * T ^ e = K * (T / K) ^ e := by
  rw [Real.div_rpow hT.le hK.le, Real.rpow_sub hK, Real.rpow_one]
  have : 0 < K ^ e := by positivity
  field_simp

lemma aExp_ge_half (n : ℕ) : 1 / 2 ≤ aExp n ∧ aExp n ≤ 1 := by
  set t := (2 : ℝ) ^ (-(n : ℝ)) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht]; apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num); simp
  have : aExp n = 1 / (2 - t) := rfl
  rw [this]
  constructor
  · rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
  · rw [div_le_one (by linarith)]; linarith

end BwSC.LowerBound.L10Aux

namespace BwSC.LowerBound.L10Aux

lemma cast_sub_ge (m p : ℕ) : (m : ℝ) - p ≤ ((m - p : ℕ) : ℝ) := by
  rcases le_total p m with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]; simp; exact_mod_cast h

/-- Standing assumption in the form `2^(q+2) ≤ log₂(T/K)`. -/
lemma standing_L {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T)
    (hstand : (qIdx S K : ℝ) + 2 ≤ Real.logb 2 (Real.logb 2 ((T : ℝ) / K))) :
    (2 : ℝ) ^ ((qIdx S K : ℝ) + 2) ≤ Real.logb 2 ((T : ℝ) / K) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have h2 : (2 : ℝ) ≤ (T : ℝ) / K := by
    rw [le_div_iff₀ hK0]; exact_mod_cast (by omega : 2 * K ≤ T)
  have hL : 1 ≤ Real.logb 2 ((T : ℝ) / K) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
    simpa using h2
  exact (Real.le_logb_iff_rpow_le (by norm_num) (by linarith)).mp hstand

/-- `y^(a u) ≥ 2` from `a ≥ 1/2`, `u ≥ 2^{-m}` and `log₂ y ≥ 2^{m+1}`. -/
lemma pow_ge_two (y a u m : ℝ) (hy : 0 < y) (ha : 1 / 2 ≤ a) (hu : (2 : ℝ) ^ (-m) ≤ u)
    (hL : (2 : ℝ) ^ (m + 1) ≤ Real.logb 2 y) : 2 ≤ y ^ (a * u) := by
  have hyL : y = (2 : ℝ) ^ (Real.logb 2 y) := (Real.rpow_logb (by norm_num) (by norm_num) hy).symm
  rw [hyL, ← Real.rpow_mul (by norm_num)]
  conv_lhs => rw [show (2 : ℝ) = 2 ^ (1 : ℝ) by norm_num]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hpm : (2 : ℝ) ^ (-m) * 2 ^ (m + 1) = 2 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  have h0 : 0 < (2 : ℝ) ^ (-m) := by positivity
  have h1 : 0 ≤ Real.logb 2 y := le_trans (by positivity) hL
  calc (1 : ℝ) = 1 / 2 * ((2 : ℝ) ^ (-m) * 2 ^ (m + 1)) := by rw [hpm]; norm_num
    _ ≤ a * (u * Real.logb 2 y) := by
        apply mul_le_mul ha (mul_le_mul hu hL (by positivity) (by linarith)) (by positivity)
          (by linarith)
    _ = Real.logb 2 y * (a * u) := by ring

end BwSC.LowerBound.L10Aux

open BwSC.LowerBound BwSC.LowerBound.L10Aux in
theorem solution {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π)
    (hstand : (qIdx S K : ℝ) + 2 ≤ Real.logb 2 (Real.logb 2 ((T : ℝ) / K)))
    (j : ℕ) (hj : j ∈ Finset.Icc 1 (qIdx S K + 2)) (k : Fin K) :
    Rbad2 S K T *
        ((banditMeasure (gaussianBandit (envAlt2 S K T j k)) π T) (E2 S K T j k)).toReal ≤
      ∫ h in E2 S K T j k, regretOf (envAlt2 S K T j k) h
        ∂(banditMeasure (gaussianBandit (envAlt2 S K T j k)) π T) := by
  apply setIntegral_ge _ _ _ (measurableSet_E2 _ _ _ _ _)
  intro h hE
  simp only [E2, Set.mem_setOf_eq] at hE
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  -- notation
  set q := qIdx S K with hqdef
  set n : ℝ := (q : ℝ) + 2 with hn
  set a := aExp (q + 1) with hadef
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  set y : ℝ := (T : ℝ) / K with hydef
  have hy1 : 1 ≤ y := by rw [hydef, le_div_iff₀ hK0, one_mul]; exact_mod_cast (by omega : K ≤ T)
  have hy0 : 0 < y := by linarith
  have hTy : (T : ℝ) = K * y := by rw [hydef]; field_simp
  have hn2 : 2 ≤ n := by
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    rw [hn]; linarith
  obtain ⟨ha1, ha2⟩ := aExp_ge_half (q + 1)
  rw [← hadef] at ha1 ha2
  have hL := standing_L hK hT hstand
  rw [← hqdef, ← hydef] at hL
  set u : ℝ := (2 : ℝ) ^ (1 - (j : ℝ)) with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    linarith
  have hulow : (2 : ℝ) ^ (-((q : ℝ) + 1)) ≤ u := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (j : ℝ) ≤ q + 2 := by exact_mod_cast hj2
    linarith
  have hayu : 2 ≤ y ^ (a * u) := pow_ge_two y a u ((q : ℝ) + 1) hy0 ha1 hulow
    (by rw [show (q : ℝ) + 1 + 1 = (q : ℝ) + 2 by ring]; exact hL)
  -- the exponent (2 - u) a is at most 1
  have he1 : (2 - u) * a ≤ 1 := by
    have : a = 1 / (2 - (2 : ℝ) ^ (-(((q + 1 : ℕ) : ℝ)))) := rfl
    have hc : (2 : ℝ) ^ (-(((q + 1 : ℕ) : ℝ))) = (2 : ℝ) ^ (-((q : ℝ) + 1)) := by push_cast; ring_nf
    rw [hc] at this
    have hpos : 0 < 2 - (2 : ℝ) ^ (-((q : ℝ) + 1)) := by
      have : (2 : ℝ) ^ (-((q : ℝ) + 1)) ≤ 1 := by
        apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        have : (0 : ℝ) ≤ q := by positivity
        linarith
      linarith
    rw [this, mul_one_div, div_le_one hpos]; linarith
  -- the right end of the window
  have hhi_eq : (t2 S K T j : ℝ) = ⌊K * y ^ ((2 - u) * a)⌋₊ := by
    unfold t2; rw [if_neg (by omega), rpow_grid _ _ _ hK0 hT0]
  have hxT : K * y ^ ((2 - u) * a) ≤ T := by
    rw [hTy]
    apply mul_le_mul_of_nonneg_left _ hK0.le
    calc y ^ ((2 - u) * a) ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 he1
      _ = y := Real.rpow_one y
  have hhiT : t2 S K T j ≤ T := by
    have h1 : t2 S K T j = ⌊K * y ^ ((2 - u) * a)⌋₊ := by exact_mod_cast hhi_eq
    rw [h1]
    exact (Nat.floor_le_floor hxT).trans_eq (Nat.floor_natCast T)
  have hhi_gt : K * y ^ ((2 - u) * a) - 1 < (t2 S K T j : ℝ) := by
    rw [hhi_eq]; exact Nat.sub_one_lt_floor _
  -- Rbad2 in this notation
  have hR : Rbad2 S K T = K / (4 * n) * y ^ a := rfl
  rw [hR]
  by_cases hj1' : j = 1
  · -- first window: `Δ = 1`, `k` not chosen in `[1, t₁]`
    subst hj1'
    have hΔ : Δ2 S K T 1 = 1 := by simp [Δ2]
    have hw := regret_window k (Δ2 S K T 1) (by rw [hΔ]; norm_num) h _ _ hhiT hE
    have hlo : t2 S K T (1 - 1) = 0 := by simp [t2]
    rw [hlo, hΔ, one_mul] at hw
    simp only [zero_tsub, Nat.sub_zero] at hw
    have hu1' : u = 1 := by rw [hu]; norm_num
    rw [hu1'] at hhi_gt
    have hya : 1 ≤ y ^ a := Real.one_le_rpow hy1 (by linarith)
    have : K / (4 * n) * y ^ a ≤ K * y ^ ((2 - 1) * a) - 1 := by
      rw [show (2 - 1 : ℝ) * a = a by ring]
      have : K / (4 * n) ≤ K / 8 := div_le_div_of_nonneg_left hK0.le (by norm_num) (by linarith)
      nlinarith
    exact this.trans (hhi_gt.le.trans hw)
  · -- later windows
    have hj2' : 2 ≤ j := by omega
    have hu2 : u ≤ 1 / 2 := by
      rw [hu, show (1 / 2 : ℝ) = 2 ^ (-1 : ℝ) by norm_num]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (2 : ℝ) ≤ j := by exact_mod_cast hj2'
      linarith
    set B := y ^ ((1 - u) * a) with hB
    set A := y ^ a with hA
    have hB0 : 0 < B := by positivity
    have hAB : 2 * B ≤ A := by
      have : A = y ^ (a * u) * B := by
        rw [hA, hB, ← Real.rpow_add hy0]; ring_nf
      rw [this]; nlinarith
    have hAB' : y ^ ((2 - u) * a) = A * B := by
      rw [hA, hB, ← Real.rpow_add hy0]; ring_nf
    -- the left end of the window
    have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hlo_eq : (t2 S K T (j - 1) : ℝ) = ⌊K * B ^ 2⌋₊ := by
      unfold t2; rw [if_neg (by omega), rpow_grid _ _ _ hK0 hT0, hcast]
      congr 3
      rw [hB, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
      congr 1
      have : (2 : ℝ) ^ (1 - ((j : ℝ) - 1)) = 2 * u := by
        rw [hu, show 1 - ((j : ℝ) - 1) = 1 + (1 - (j : ℝ)) by ring, Real.rpow_add (by norm_num)]
        norm_num
      rw [this]; push_cast; ring
    have hKB : K ≤ K * B ^ 2 := by
      have : 1 ≤ B := Real.one_le_rpow hy1 (by nlinarith)
      have h1 : 1 ≤ B ^ 2 := one_le_pow₀ this
      nlinarith [mul_le_mul_of_nonneg_left h1 hK0.le]
    have hlo_pos : (0 : ℝ) < (t2 S K T (j - 1) : ℝ) := by
      rw [hlo_eq]; exact_mod_cast Nat.floor_pos.mpr (by linarith)
    have hlo_le : (t2 S K T (j - 1) : ℝ) ≤ K * B ^ 2 := by
      rw [hlo_eq]; exact Nat.floor_le (by positivity)
    have hΔ : Δ2 S K T j = 1 / (2 * n) * Real.sqrt ((K : ℝ) / (t2 S K T (j - 1) : ℝ)) := by
      unfold Δ2; rw [if_neg hj1']
    have hΔ0 : 0 ≤ Δ2 S K T j := by rw [hΔ]; positivity
    have hw := regret_window k (Δ2 S K T j) hΔ0 h _ _ hhiT hE
    have hlo1 : 1 ≤ t2 S K T (j - 1) := by exact_mod_cast hlo_pos
    have hcnt : (t2 S K T j : ℝ) - (t2 S K T (j - 1) : ℝ) + 1 ≤
        ((t2 S K T j - (t2 S K T (j - 1) - 1) : ℕ) : ℝ) := by
      have := cast_sub_ge (t2 S K T j) (t2 S K T (j - 1) - 1)
      rw [Nat.cast_sub hlo1] at this
      push_cast at this; linarith
    have hkey := key_real K A B n _ _ hK0 hB0 hAB (by linarith) (by rw [← hAB']; exact hhi_gt)
      hlo_le hlo_pos
    rw [← hΔ] at hkey
    calc K / (4 * n) * A ≤ Δ2 S K T j * ((t2 S K T j : ℝ) - (t2 S K T (j - 1) : ℝ) + 1) := hkey
      _ ≤ Δ2 S K T j * ((t2 S K T j - (t2 S K T (j - 1) - 1) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hcnt hΔ0
      _ ≤ _ := hw
