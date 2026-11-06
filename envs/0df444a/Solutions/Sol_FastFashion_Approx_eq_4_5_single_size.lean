-- Prove2me | solution 1 for FastFashion.Approx.eq_4_5_single_size
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:28:53.956287+00:00
-- url     : https://prove2.me/submissions/769ee3d9-dbea-46d2-a03e-e5604f773e66

import Mathlib
import Definitions.Def_FastFashion_Structure_Model
import Definitions.Def_FastFashion_Approx_Tangents

open MeasureTheory ProbabilityTheory

namespace FFEq45

/-- Poisson weights `e^{-x} x^j / j!` -/
noncomputable def term (j : ℕ) (x : ℝ) : ℝ := Real.exp (-x) * x ^ j / (j.factorial : ℝ)

lemma continuous_term (j : ℕ) : Continuous (term j) := by
  unfold term; fun_prop

lemma hasDerivAt_term_succ (j : ℕ) (x : ℝ) :
    HasDerivAt (term (j + 1)) (-(term (j + 1) x) + term j x) x := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x :=
    ((hasDerivAt_neg x).exp).congr_deriv (by ring)
  have h2 : HasDerivAt (fun x : ℝ => x ^ (j + 1)) (((j + 1 : ℕ) : ℝ) * x ^ j) x := by
    simpa using hasDerivAt_pow (j + 1) x
  have h3 := (h1.mul h2).div_const (((j + 1).factorial : ℕ) : ℝ)
  have hf : term (j + 1) = fun x => (Real.exp (-x) * x ^ (j + 1)) / (((j + 1).factorial : ℕ) : ℝ) := by
    funext y; rfl
  rw [hf]
  refine h3.congr_deriv ?_
  unfold term
  rw [Nat.factorial_succ]
  push_cast
  have : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma hasDerivAt_term_zero (x : ℝ) : HasDerivAt (term 0) (-(term 0 x)) x := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x :=
    ((hasDerivAt_neg x).exp).congr_deriv (by ring)
  have hf : term 0 = fun x => Real.exp (-x) := by
    funext y; simp [term]
  rw [hf]
  exact h1

lemma hasDerivAt_sum (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x => ∑ j ∈ Finset.range (k + 1), term j x) (-(term k x)) x := by
  induction k with
  | zero => simpa using hasDerivAt_term_zero x
  | succ k ih =>
    have := ih.add (hasDerivAt_term_succ k x)
    have hfun : (fun x => ∑ j ∈ Finset.range (k + 1 + 1), term j x) =
        fun x => ∑ j ∈ Finset.range (k + 1), term j x + term (k + 1) x := by
      funext y; rw [Finset.sum_range_succ]
    rw [hfun]
    exact this.congr_deriv (by ring)

/-- `γ(k+1, x) / k! = 1 - ∑_{j ≤ k} e^{-x} x^j / j!` -/
lemma lowerGamma_succ_div (k : ℕ) (x : ℝ) :
    FastFashion.Approx.lowerGamma (k + 1) x / (k.factorial : ℝ) =
      1 - ∑ j ∈ Finset.range (k + 1), term j x := by
  have hI : ∫ v in (0:ℝ)..x, term k v =
      (-(∑ j ∈ Finset.range (k + 1), term j x)) - (-(∑ j ∈ Finset.range (k + 1), term j 0)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => ((hasDerivAt_sum k y).neg).congr_deriv (neg_neg _))
      ((continuous_term k).intervalIntegrable _ _)
  have h0 : ∑ j ∈ Finset.range (k + 1), term j 0 = 1 := by
    rw [Finset.sum_range_succ']
    simp [term]
  unfold FastFashion.Approx.lowerGamma
  rw [Nat.add_sub_cancel, ← intervalIntegral.integral_div]
  have : (fun v : ℝ => v ^ k * Real.exp (-v) / (k.factorial : ℝ)) = term k := by
    funext v; unfold term; ring
  rw [this, hI, h0]
  ring

/-- `∫_0^T e^{-λt}(λt)^j/j! dt = γ(j+1, λT)/(λ j!)` -/
lemma integral_term_scaled (j : ℕ) (l T : ℝ) (hl : 0 < l) :
    ∫ t in (0:ℝ)..T, term j (l * t) =
      FastFashion.Approx.lowerGamma (j + 1) (l * T) / (l * (j.factorial : ℝ)) := by
  rw [intervalIntegral.integral_comp_mul_left (fun v => term j v) hl.ne', mul_zero]
  unfold FastFashion.Approx.lowerGamma
  rw [Nat.add_sub_cancel, smul_eq_mul]
  have : (fun v : ℝ => v ^ j * Real.exp (-v)) = fun v => (j.factorial : ℝ) * term j v := by
    funext v; unfold term
    have : (j.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [this, intervalIntegral.integral_const_mul]
  have : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp



open FastFashion.Structure

/-- the truncation map `x ↦ x ∧ T` from `WithTop ℝ` to `ℝ` -/
noncomputable def trunc (T : ℝ) : WithTop ℝ → ℝ
  | ⊤ => T
  | (t : ℝ) => min t T

lemma stopMin_eq {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (T : ℝ) (ω : Ω) :
    stopMin N A q T ω = trunc T (tauMin N A q ω) := by
  unfold stopMin trunc
  rfl

lemma trunc_mono (T : ℝ) {x y : WithTop ℝ} (h : x ≤ y) : trunc T x ≤ trunc T y := by
  induction y using WithTop.recTopCoe with
  | top =>
    induction x using WithTop.recTopCoe with
    | top => exact le_rfl
    | coe a => exact min_le_right _ _
  | coe b =>
    induction x using WithTop.recTopCoe with
    | top => exact absurd h (by simp)
    | coe a =>
      have : a ≤ b := WithTop.coe_le_coe.mp h
      exact min_le_min_right _ this

lemma trunc_nonneg {T : ℝ} (hT : 0 ≤ T) {x : WithTop ℝ} (h : 0 ≤ x) : 0 ≤ trunc T x := by
  induction x using WithTop.recTopCoe with
  | top => exact hT
  | coe a =>
    have : (0:ℝ) ≤ a := by exact_mod_cast h
    exact le_min this hT

lemma trunc_le {T : ℝ} (x : WithTop ℝ) : trunc T x ≤ T := by
  induction x using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe a => exact min_le_right _ _

lemma stockoutTime_nonneg {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (s : S) (q : S → ℕ) (ω : Ω) :
    0 ≤ stockoutTime N s q ω := by
  classical
  unfold stockoutTime
  split_ifs with h
  · have : (0:ℝ) ≤ sInf {t : ℝ | 0 ≤ t ∧ N s t ω = q s} :=
      Real.sInf_nonneg (fun x hx => hx.1)
    exact_mod_cast this
  · exact le_top

lemma tauMin_nonneg {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (ω : Ω) :
    0 ≤ tauMin N A q ω := by
  unfold tauMin
  exact Finset.le_inf (fun s _ => stockoutTime_nonneg N s q ω)

/-- right-continuity of an `ℕ`-valued path: locally constant on the right -/
lemma rc_const {f : ℝ → ℕ} {t : ℝ} (h : ContinuousWithinAt f (Set.Ici t) t) :
    ∃ δ > 0, ∀ u, t ≤ u → u < t + δ → f u = f t := by
  have h1 : ∀ᶠ u in nhdsWithin t (Set.Ici t), f u = f t := by
    have := h.eventually (isOpen_discrete {f t} |>.mem_nhds rfl)
    exact this
  rcases (mem_nhdsGE_iff_exists_Ico_subset.mp h1) with ⟨u, hu, hsub⟩
  refine ⟨u - t, by linarith [hu.out], fun v hv1 hv2 => hsub ⟨hv1, by linarith⟩⟩

variable {S Ω : Type*} [MeasurableSpace Ω] {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} {P : Measure Ω}

/-- the path hits every level below a reached value -/
lemma hit (hN : IsPoissonFamily lam N P) (s : S) (ω : Ω) (k : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hk : k ≤ N s c ω) : ∃ u, 0 ≤ u ∧ u ≤ c ∧ N s u ω = k := by
  set B : Set ℝ := {t | 0 ≤ t ∧ k ≤ N s t ω} with hB
  have hBne : B.Nonempty := ⟨c, hc, hk⟩
  have hBbdd : BddBelow B := ⟨0, fun x hx => hx.1⟩
  set ts := sInf B with hts
  have h0 : 0 ≤ ts := le_csInf hBne (fun x hx => hx.1)
  have hc' : ts ≤ c := csInf_le hBbdd ⟨hc, hk⟩
  have hge : k ≤ N s ts ω := by
    by_contra hlt
    push Not at hlt
    obtain ⟨δ, hδ, hconst⟩ := rc_const (hN.rightContinuous s ω ts h0)
    obtain ⟨b, hbB, hb⟩ := exists_lt_of_csInf_lt hBne (show sInf B < ts + δ by linarith)
    have hbts : ts ≤ b := csInf_le hBbdd hbB
    have := hconst b hbts hb
    have := hbB.2
    omega
  refine ⟨ts, h0, hc', le_antisymm ?_ hge⟩
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h, hN.zero]; exact Nat.zero_le _
  · obtain ⟨u, hu, hj⟩ := hN.unitJumps s ω ts h
    set m := max u 0
    have hm : m < ts := max_lt hu h
    set v := (m + ts) / 2
    have hv1 : u < v := by
      have := le_max_left u 0; simp only [v]; linarith
    have hv2 : v < ts := by simp only [v]; linarith
    have hv0 : 0 ≤ v := by
      have := le_max_right u 0; simp only [v]; linarith
    have hvB : v ∉ B := fun hvB => by
      have := csInf_le hBbdd hvB
      linarith
    have hNv : N s v ω < k := by
      by_contra hh; push Not at hh; exact hvB ⟨hv0, hh⟩
    have := hj v hv1 hv2
    omega

lemma stockout_le_iff (hN : IsPoissonFamily lam N P) (s : S) (q : S → ℕ) (ω : Ω) (c : ℝ)
    (hc : 0 ≤ c) : stockoutTime N s q ω ≤ (c : WithTop ℝ) ↔ q s ≤ N s c ω := by
  classical
  set A : Set ℝ := {t : ℝ | 0 ≤ t ∧ N s t ω = q s} with hA
  have hAbdd : BddBelow A := ⟨0, fun x hx => hx.1⟩
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨δ, hδ, hconst⟩ := rc_const (hN.rightContinuous s ω c hc)
    unfold stockoutTime at h
    by_cases hne : A.Nonempty
    · rw [if_pos hne] at h
      have h' : sInf A ≤ c := by exact_mod_cast h
      have hlow : c + δ ≤ sInf A := by
        refine le_csInf hne (fun t ht => ?_)
        by_contra htlt
        push Not at htlt
        rcases le_or_gt t c with htc | htc
        · have := hN.mono s ω ht.1 htc
          have := ht.2
          omega
        · have := hconst t htc.le htlt
          have := ht.2
          omega
      linarith
    · rw [if_neg hne] at h
      exact absurd h (by simp)
  · intro h
    obtain ⟨u, hu0, huc, hu⟩ := hit hN s ω (q s) c hc h
    have hne : A.Nonempty := ⟨u, hu0, hu⟩
    unfold stockoutTime
    rw [if_pos hne]
    have : sInf A ≤ c := (csInf_le hAbdd ⟨hu0, hu⟩).trans huc
    exact_mod_cast this

lemma lt_trunc_iff {T c : ℝ} (hc : c < T) (x : WithTop ℝ) :
    c < trunc T x ↔ ¬ x ≤ (c : WithTop ℝ) := by
  induction x using WithTop.recTopCoe with
  | top => simp [trunc, hc]
  | coe a =>
    simp only [trunc, WithTop.coe_le_coe, not_le, lt_min_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩

lemma measurable_stopMin_single (hN : IsPoissonFamily lam N P) (s : S) (q : S → ℕ) (T : ℝ)
    (hT : 0 < T) : Measurable (fun ω => stopMin N {s} q T ω) := by
  classical
  refine measurable_of_Ioi (fun c => ?_)
  have hfe : ∀ ω, stopMin N {s} q T ω = trunc T (stockoutTime N s q ω) := by
    intro ω; rw [stopMin_eq]; simp [tauMin]
  rcases lt_or_ge c 0 with hc0 | hc0
  · convert MeasurableSet.univ
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
    rw [hfe]
    exact lt_of_lt_of_le hc0 (trunc_nonneg hT.le (stockoutTime_nonneg N s q ω))
  rcases lt_or_ge c T with hcT | hcT
  · have : (fun ω => stopMin N {s} q T ω) ⁻¹' Set.Ioi c = {ω | N s c ω < q s} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_ofPred_eq]
      rw [hfe, lt_trunc_iff hcT, stockout_le_iff hN s q ω c hc0, not_le]
    rw [this]
    exact measurableSet_lt (hN.measurable s c hc0) measurable_const
  · convert MeasurableSet.empty
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_lt]
    exact (hfe ω ▸ trunc_le _).trans hcT


section Prob
open FastFashion.Structure
variable {S Ω : Type*} [MeasurableSpace Ω] {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} {P : Measure Ω}

lemma law_lt [IsProbabilityMeasure P] (hN : IsPoissonFamily lam N P) (s : S) (t : ℝ) (ht : 0 ≤ t)
    (hl : 0 ≤ lam s) (m : ℕ) :
    P.real {ω | N s t ω < m} = ∑ j ∈ Finset.range m, term j (lam s * t) := by
  have hmap : P.map (N s t) = poissonMeasure (lam s * t).toNNReal := by
    have := hN.incrementLaw s 0 t le_rfl ht
    simp only [hN.zero, Nat.sub_zero, sub_zero] at this
    exact this
  have hmeas := hN.measurable s t ht
  have hset : {ω | N s t ω < m} = N s t ⁻¹' (↑(Finset.range m) : Set ℕ) := by
    ext ω; simp
  rw [hset, ← map_measureReal_apply hmeas (Finset.measurableSet _), hmap,
    ← sum_measureReal_singleton]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [poissonMeasure_real_singleton, Real.coe_toNNReal _ (mul_nonneg hl ht)]
  rfl

end Prob

end FFEq45

open FFEq45 FastFashion.Approx FastFashion.Structure in
theorem solution {S Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ)
    (hN : FastFashion.Structure.IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (T : ℝ) (hT : 0 < T)
    (s : S) (q : S → ℕ) :
    FastFashion.Structure.hA N P T {s} q =
        (1 / lam s) * ∑ k ∈ Finset.Icc 1 (q s), (P {ω | k ≤ N s T ω}).toReal ∧
      FastFashion.Structure.hA N P T {s} q =
        ∑ k ∈ Finset.Icc 1 (q s),
          lowerGamma k (lam s * T) / (lam s * (Nat.factorial (k - 1) : ℝ)) := by
  classical
  have hl := hlam s
  have hfe : ∀ ω, stopMin N {s} q T ω = trunc T (stockoutTime N s q ω) := by
    intro ω; rw [stopMin_eq]; simp [tauMin]
  have hint : Integrable (fun ω => stopMin N {s} q T ω) P := by
    refine Integrable.of_bound (measurable_stopMin_single hN s q T hT).aestronglyMeasurable T
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [stopMin_eq, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [trunc_nonneg hT.le (tauMin_nonneg N {s} q ω)], trunc_le _⟩
  have hnn : 0 ≤ᵐ[P] (fun ω => stopMin N {s} q T ω) :=
    Filter.Eventually.of_forall (fun ω => by
      simp only [Pi.zero_apply]; rw [stopMin_eq]; exact trunc_nonneg hT.le (tauMin_nonneg N {s} q ω))
  have hmain : hA N P T {s} q = ∑ j ∈ Finset.range (q s),
      lowerGamma (j + 1) (lam s * T) / (lam s * (j.factorial : ℝ)) := by
    unfold hA
    rw [hint.integral_eq_integral_meas_lt hnn]
    have h1 : Set.EqOn (fun t => P.real {ω | t < stopMin N {s} q T ω})
        ((Set.Iio T).indicator (fun t => ∑ j ∈ Finset.range (q s), term j (lam s * t)))
        (Set.Ioi 0) := by
      intro t ht
      have ht0 : (0:ℝ) ≤ t := le_of_lt ht
      by_cases htT : t < T
      · simp only
        rw [Set.indicator_of_mem (show t ∈ Set.Iio T from htT), ← law_lt hN s t ht0 hl.le]
        congr 1; ext ω
        simp only [Set.mem_ofPred_eq]
        rw [hfe, lt_trunc_iff htT, stockout_le_iff hN s q ω t ht0, not_le]
      · simp only
        rw [Set.indicator_of_notMem (show t ∉ Set.Iio T from htT)]
        have : {ω | t < stopMin N {s} q T ω} = ∅ := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
          push Not at htT
          exact (hfe ω ▸ trunc_le _).trans htT
        rw [this, measureReal_empty]
    rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio]
    rw [show Set.Iio T ∩ Set.Ioi 0 = Set.Ioo 0 T by ext; simp [and_comm],
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT.le]
    rw [intervalIntegral.integral_finsetSum (fun j _ =>
      (show Continuous (fun x => term j (lam s * x)) from
        (continuous_term j).comp (continuous_const_mul _)).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact integral_term_scaled j (lam s) T hl
  have hshift : ∀ (g : ℕ → ℝ), ∑ k ∈ Finset.Icc 1 (q s), g k = ∑ j ∈ Finset.range (q s), g (j + 1) := by
    intro g
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl (fun j _ => by rw [add_comm])
  refine ⟨?_, ?_⟩
  · rw [hmain, hshift, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hP : (P {ω | j + 1 ≤ N s T ω}).toReal = lowerGamma (j + 1) (lam s * T) / (j.factorial : ℝ) := by
      rw [← measureReal_def]
      have hc : {ω | j + 1 ≤ N s T ω} = {ω | N s T ω < j + 1}ᶜ := by
        ext ω; simp
      rw [hc, probReal_compl_eq_one_sub (measurableSet_lt (hN.measurable s T hT.le) measurable_const),
        law_lt hN s T hT.le hl.le, lowerGamma_succ_div]
    rw [hP]
    have : (j.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · rw [hmain, hshift]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Nat.add_sub_cancel]
