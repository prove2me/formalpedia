-- Prove2me | solution 1 for ChebotarevDensity.dirichlet_density
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T13:34:35.154369+00:00
-- url     : https://prove2.me/submissions/d3740977-c426-44de-8088-f40f838bbfad

import Definitions.Def_ChebotarevDensity_Defs

open Polynomial NumberField
open ChebotarevDensity

/-! Dirichlet density of primes in an arithmetic progression, via the real-variable
von Mangoldt estimate of `Mathlib.NumberTheory.LSeries.PrimesInAP`. -/

section aux

open Complex ArithmeticFunction.vonMangoldt Filter Topology LSeries

variable {q : ℕ}

private lemma bound_H [NeZero q] (A : ZMod q) (hA : IsUnit A) :
    ∃ B : ℝ, ∀ x ∈ Set.Ioc (1:ℝ) 2,
      |∑' n, residueClass A n / (n:ℝ)^x - (q.totient:ℝ)⁻¹/(x-1)| ≤ B := by
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, residueClass A n / (n : ℝ) ^ x =
        (LFunctionResidueClassAux A x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
    simp_rw [← LFunctionResidueClassAux_real hA hx,
      eqOn_LFunctionResidueClassAux hA <| Set.mem_ofPred.mpr (ofReal_re x ▸ hx), sub_add_cancel,
      LSeries, LSeries.term]
    refine tsum_congr fun n ↦ ?_
    split_ifs with hn
    · simp only [hn, residueClass_apply_zero, ofReal_zero, zero_div]
    · rfl
  have : ContinuousOn (fun x : ℝ ↦ (LFunctionResidueClassAux A x).re) (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t := Set.univ) (continuousOn_LFunctionResidueClassAux A)
      (fun ⦃x⦄ a ↦ trivial) |>.comp continuous_ofReal.continuousOn fun x hx ↦ by
        simpa only [Set.mem_ofPred_eq, ofReal_re] using hx.1
  obtain ⟨B, hB⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc this
  refine ⟨B, fun x hx ↦ ?_⟩
  rw [H hx.1, add_sub_cancel_right]
  simpa using hB x (Set.mem_Icc_of_Ioc hx)

private lemma bound_P [NeZero q] (A : ZMod q) (hA : IsUnit A) :
    ∃ K : ℝ, ∀ x ∈ Set.Ioc (1:ℝ) 2,
      |∑' n : ℕ, (if n.Prime then residueClass A n else 0) / (n:ℝ)^x
        - (q.totient:ℝ)⁻¹/(x-1)| ≤ K := by
  obtain ⟨B, hB⟩ := bound_H A hA
  set N₁ : ℝ := ∑' n : ℕ, (if n.Prime then 0 else residueClass A n) / (n:ℝ) with hN₁
  refine ⟨B + N₁, fun x hx ↦ ?_⟩
  have hsH : Summable fun n : ℕ ↦ residueClass A n / (n : ℝ) ^ x :=
    summable_real_of_abscissaOfAbsConv_lt <|
      (abscissaOfAbsConv_residueClass_le_one A).trans_lt <| mod_cast hx.1
  have hpos (n : ℕ) : 0 ≤ residueClass A n / (n : ℝ) ^ x :=
    div_nonneg (residueClass_nonneg A n) (by positivity)
  have hP0 (n : ℕ) : 0 ≤ (if n.Prime then residueClass A n else 0) / (n:ℝ)^x := by
    split_ifs
    · exact hpos n
    · simp
  have hN0 (n : ℕ) : 0 ≤ (if n.Prime then 0 else residueClass A n) / (n:ℝ)^x := by
    split_ifs
    · simp
    · exact hpos n
  have hPle (n : ℕ) : (if n.Prime then residueClass A n else 0) / (n:ℝ)^x
      ≤ residueClass A n / (n : ℝ) ^ x := by
    split_ifs
    · exact le_rfl
    · simpa using hpos n
  have hNle (n : ℕ) : (if n.Prime then 0 else residueClass A n) / (n:ℝ)^x
      ≤ residueClass A n / (n : ℝ) ^ x := by
    split_ifs
    · simpa using hpos n
    · exact le_rfl
  have hsP := Summable.of_nonneg_of_le hP0 hPle hsH
  have hsN := Summable.of_nonneg_of_le hN0 hNle hsH
  have hsum : ∑' n : ℕ, (if n.Prime then residueClass A n else 0) / (n:ℝ)^x
      + ∑' n : ℕ, (if n.Prime then 0 else residueClass A n) / (n:ℝ)^x
      = ∑' n, residueClass A n / (n : ℝ) ^ x := by
    rw [← hsP.tsum_add hsN]
    refine tsum_congr fun n ↦ ?_
    split_ifs <;> simp
  have hN_nonneg : 0 ≤ ∑' n : ℕ, (if n.Prime then 0 else residueClass A n) / (n:ℝ)^x :=
    tsum_nonneg hN0
  have hN_le : ∑' n : ℕ, (if n.Prime then 0 else residueClass A n) / (n:ℝ)^x ≤ N₁ := by
    refine hsN.tsum_le_tsum (fun n ↦ ?_) (summable_residueClass_non_primes_div A)
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · refine div_le_div_of_nonneg_left ?_ (mod_cast hn) ?_
      · split_ifs
        · exact le_rfl
        · exact residueClass_nonneg A n
      · conv_lhs => rw [← Real.rpow_one n]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_cast) hx.1.le
  have h1 := hB x hx
  rw [← hsum] at h1
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

private lemma summable_Pterm (A : ZMod q) {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ ↦ (if n.Prime then residueClass A n else 0) / (n:ℝ)^x := by
  have hsH : Summable fun n : ℕ ↦ residueClass A n / (n : ℝ) ^ x :=
    summable_real_of_abscissaOfAbsConv_lt <|
      (abscissaOfAbsConv_residueClass_le_one A).trans_lt <| mod_cast hx
  refine Summable.of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) hsH
  · split_ifs
    · exact div_nonneg (residueClass_nonneg A n) (by positivity)
    · simp
  · split_ifs
    · exact le_rfl
    · rw [zero_div]; exact div_nonneg (residueClass_nonneg A n) (by positivity)

private lemma Pterm_eq (A : ZMod q) (x : ℝ) :
    ∑' n : ℕ, (if n.Prime then residueClass A n else 0) / (n:ℝ)^x
      = ∑' p : {p : ℕ // p.Prime ∧ (p : ZMod q) = A}, Real.log p * (p:ℝ)^(-x) := by
  have hsub : Function.support (fun n : ℕ ↦ (if n.Prime then residueClass A n else 0) / (n:ℝ)^x)
      ⊆ {p : ℕ | p.Prime ∧ (p : ZMod q) = A} := by
    intro n hn
    by_contra h
    apply hn
    simp only [Set.mem_ofPred_eq, not_and] at h
    by_cases hp : n.Prime
    · have : residueClass A n = 0 := by
        simp [residueClass, Set.indicator, h hp]
      simp [hp, this]
    · simp [hp]
  rw [← tsum_subtype_eq_of_support_subset hsub]
  refine tsum_congr fun ⟨p, hp, hpa⟩ ↦ ?_
  have : residueClass A p = Real.log p := by
    simp [residueClass, Set.indicator, hpa, ArithmeticFunction.vonMangoldt_apply_prime hp]
  simp only [hp, if_true, this]
  rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

private lemma summable_log_rpow (A : ZMod q) {x : ℝ} (hx : 1 < x) :
    Summable fun p : {p : ℕ // p.Prime ∧ (p : ZMod q) = A} ↦ Real.log p * (p:ℝ)^(-x) := by
  have hsum := ((summable_Pterm A hx).subtype
    {p : ℕ | p.Prime ∧ (p : ZMod q) = A})
  refine hsum.congr fun ⟨p, hp, hpa⟩ ↦ ?_
  have : residueClass A p = Real.log p := by
    simp [residueClass, Set.indicator, hpa, ArithmeticFunction.vonMangoldt_apply_prime hp]
  simp only [Function.comp, hp, if_true, this]
  rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

private lemma summable_rpow_T (A : ZMod q) {x : ℝ} (hx : 1 < x) :
    Summable fun p : {p : ℕ // p.Prime ∧ (p : ZMod q) = A} ↦ (p:ℝ)^(-x) :=
  (Real.summable_nat_rpow.2 (by linarith : -x < -1)).subtype
      {p : ℕ | p.Prime ∧ (p : ZMod q) = A}

private lemma hasDerivAt_F (A : ZMod q) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y : ℝ ↦ ∑' p : {p : ℕ // p.Prime ∧ (p : ZMod q) = A}, (p:ℝ)^(-y))
      (-∑' n : ℕ, (if n.Prime then residueClass A n else 0) / (n:ℝ)^x) x := by
  rw [Pterm_eq, ← tsum_neg]
  set x₀ : ℝ := (1 + x) / 2 with hx₀
  have hx₀1 : 1 < x₀ := by rw [hx₀]; linarith
  have hx₀x : x₀ < x := by rw [hx₀]; linarith
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun (p : {p : ℕ // p.Prime ∧ (p : ZMod q) = A}) (y : ℝ) ↦ (p:ℝ)^(-y))
    (g' := fun (p : {p : ℕ // p.Prime ∧ (p : ZMod q) = A}) (y : ℝ) ↦ -(Real.log p * (p:ℝ)^(-y)))
    (u := fun p : {p : ℕ // p.Prime ∧ (p : ZMod q) = A} ↦ Real.log p * (p:ℝ)^(-x₀))
    (t := Set.Ioi x₀) (summable_log_rpow A hx₀1) isOpen_Ioi
    isPreconnected_Ioi ?_ ?_ (Set.mem_Ioi.2 hx₀x) (summable_rpow_T A hx) (Set.mem_Ioi.2 hx₀x)
  · intro ⟨p, hp, _⟩ y _
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
    have := ((Real.hasStrictDerivAt_const_rpow hp0 (-y)).hasDerivAt.comp y (hasDerivAt_neg y))
    refine HasDerivAt.congr_deriv this ?_
    show _ = -(Real.log p * (p:ℝ)^(-y))
    ring
  · intro ⟨p, hp, _⟩ y hy
    have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ hlog
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith [Set.mem_Ioi.1 hy])

private lemma F_bound [NeZero q] (A : ZMod q) (hA : IsUnit A) :
    ∃ M : ℝ, ∀ x ∈ Set.Ioc (1:ℝ) 2,
      |(∑' p : {p : ℕ // p.Prime ∧ (p : ZMod q) = A}, (p:ℝ)^(-x))
        - (q.totient:ℝ)⁻¹ * Real.log (1/(x-1))| ≤ M := by
  obtain ⟨K, hK⟩ := bound_P A hA
  set c : ℝ := (q.totient:ℝ)⁻¹ with hc
  set F : ℝ → ℝ := fun y ↦ ∑' p : {p : ℕ // p.Prime ∧ (p : ZMod q) = A}, (p:ℝ)^(-y) with hF
  set P : ℝ → ℝ := fun x ↦ ∑' n : ℕ, (if n.Prime then residueClass A n else 0) / (n:ℝ)^x
    with hP
  set Φ : ℝ → ℝ := fun y ↦ F y + c * Real.log (y - 1) with hΦ
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 2 ⟨one_lt_two, le_rfl⟩)
  have hder : ∀ x ∈ Set.Ioc (1:ℝ) 2, HasDerivWithinAt Φ (-P x + c / (x - 1)) (Set.Ioc 1 2) x := by
    intro x hx
    have h1 := hasDerivAt_F A hx.1
    have hne : x - 1 ≠ 0 := (sub_pos.2 hx.1).ne'
    have h2 : HasDerivAt (fun y : ℝ ↦ Real.log (y - 1)) (1 / (x - 1)) x := by
      simpa using ((hasDerivAt_id x).sub_const 1).log hne
    have := h1.add (h2.const_mul c)
    refine this.hasDerivWithinAt.congr_deriv ?_
    rw [mul_one_div]
  have hbd : ∀ x ∈ Set.Ioc (1:ℝ) 2, ‖-P x + c / (x - 1)‖ ≤ K := by
    intro x hx
    have := hK x hx
    rw [Real.norm_eq_abs, ← abs_neg]
    convert this using 2
    ring
  refine ⟨K + |Φ 2|, fun x hx ↦ ?_⟩
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_Ioc 1 2)
    (⟨one_lt_two, le_rfl⟩ : (2:ℝ) ∈ Set.Ioc (1:ℝ) 2) hx
  have habs : ‖x - 2‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hx.1, hx.2]
  have h3 : |Φ x - Φ 2| ≤ K := by
    rw [← Real.norm_eq_abs]
    exact hmv.trans (by nlinarith [norm_nonneg (x - 2)])
  have h4 : Φ x = F x - c * Real.log (1 / (x - 1)) := by
    simp only [hΦ, one_div, Real.log_inv]; ring
  rw [← h4]
  have := abs_sub_abs_le_abs_sub (Φ x) (Φ 2)
  linarith


private lemma tendsto_of_bound (F : ℝ → ℝ) (c M : ℝ)
    (h : ∀ x ∈ Set.Ioc (1:ℝ) 2, |F x - c * Real.log (1/(x-1))| ≤ M) :
    Tendsto (fun s : ℝ ↦ F s / Real.log (1/(s-1))) (𝓝[>] 1) (𝓝 c) := by
  have h0 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ ↦ s - 1) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_id.sub continuous_const).tendsto' 1 _ rfl
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs using sub_pos.2 (Set.mem_Ioi.1 hs)
  have hL : Tendsto (fun s : ℝ ↦ Real.log (1/(s-1))) (𝓝[>] 1) atTop := by
    simp only [one_div]
    exact Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp h0)
  have hM : Tendsto (fun s : ℝ ↦ M / Real.log (1/(s-1))) (𝓝[>] 1) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 1, s ∈ Set.Ioc (1:ℝ) 2 :=
    Ioc_mem_nhdsGT one_lt_two
  have hpos := hL.eventually_gt_atTop 0
  have hz : Tendsto (fun s : ℝ ↦ (F s - c * Real.log (1/(s-1))) / Real.log (1/(s-1)))
      (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hM
    filter_upwards [hev, hpos] with s hs hp
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp]
    exact div_le_div_of_nonneg_right (h s hs) hp.le
  have := hz.const_add c
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [hpos] with s hp
  field_simp
  ring

private lemma tsum_congr_T (a : ℤ) (m : ℕ) (s : ℝ) :
    ∑' p : {p : ℕ // p.Prime ∧ p ∈ {p : ℕ | (p : ℤ) ≡ a [ZMOD m]}}, ((p : ℕ) : ℝ) ^ (-s)
      = ∑' p : {p : ℕ // p.Prime ∧ (p : ZMod m) = (a : ZMod m)}, ((p : ℕ) : ℝ) ^ (-s) := by
  refine (Equiv.subtypeEquivRight (fun p : ℕ ↦ ?_)).tsum_eq
    (fun p : {p : ℕ // p.Prime ∧ (p : ZMod m) = (a : ZMod m)} ↦ ((p : ℕ) : ℝ) ^ (-s))
  simp only [Set.mem_ofPred_eq]
  rw [← ZMod.intCast_eq_intCast_iff]
  simp

end aux

theorem solution (m : ℕ) (hm : 0 < m) (a : ℤ) (ha : Int.gcd a m = 1) :
    HasDirichletDensity {p : ℕ | (p : ℤ) ≡ a [ZMOD m]} (1 / (Nat.totient m : ℝ)) := by
  have : NeZero m := ⟨hm.ne'⟩
  have hU : IsUnit (a : ZMod m) :=
    (ZMod.coe_int_isUnit_iff_isCoprime a m).2 (Int.isCoprime_iff_gcd_eq_one.2 (by rwa [Int.gcd_comm]))
  obtain ⟨M, hM⟩ := F_bound (a : ZMod m) hU
  have key := tendsto_of_bound _ _ M hM
  unfold HasDirichletDensity
  simp_rw [tsum_congr_T]
  simpa [one_div] using key
