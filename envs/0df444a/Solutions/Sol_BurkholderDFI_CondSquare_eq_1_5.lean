-- Prove2me | solution 1 for BurkholderDFI.CondSquare.eq_1_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:55:22.231749+00:00
-- url     : https://prove2.me/submissions/6e117f6b-edba-4d0e-b9bb-5bedbf8785dd

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal


namespace BurkholderDFI.CondSquare

open BurkholderDFI.SquareFnLp

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℕ mΩ}
  {g : ℕ → Ω → ℝ}

/-- `((x ^ (1/p)) ^ p = x`. -/
lemma rpow_one_div_rpow (x : ℝ≥0∞) {p : ℝ} (hp : p ≠ 0) : (x ^ (1 / p)) ^ p = x := by
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp, ENNReal.rpow_one]

/-- Hölder step: from `l * m ≤ a` and `a ≤ b^(1/p) m^(1/q)` deduce `l^p m ≤ b`. -/
lemma holder_step {p q : ℝ} (hpq : p.HolderConjugate q) {l : ℝ} (hl : 0 < l)
    {a b m : ℝ≥0∞} (hm : m ≠ ⊤) (h1 : ENNReal.ofReal l * m ≤ a)
    (h2 : a ≤ b ^ (1 / p) * m ^ (1 / q)) :
    ENNReal.ofReal (l ^ p) * m ≤ b := by
  rcases eq_or_ne m 0 with hm0 | hm0
  · simp [hm0]
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hpq' : 1 / q * p = p - 1 := by
    have h := hpq.inv_add_inv_eq_one
    field_simp
    field_simp at h
    linarith
  have h3 : (ENNReal.ofReal l * m) ^ p ≤ (b ^ (1 / p) * m ^ (1 / q)) ^ p :=
    ENNReal.rpow_le_rpow (h1.trans h2) hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    rpow_one_div_rpow _ hp0.ne', ← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_nonneg hl.le hp0.le,
    hpq'] at h3
  have hsplit : m ^ p = m * m ^ (p - 1) := by
    conv_lhs => rw [show p = 1 + (p - 1) by ring]
    rw [ENNReal.rpow_add _ _ hm0 hm, ENNReal.rpow_one]
  rw [hsplit, ← mul_assoc] at h3
  have hp1 : 0 ≤ p - 1 := by linarith [hpq.lt]
  refine (ENNReal.mul_le_mul_iff_left ?_ (ENNReal.rpow_ne_top_of_nonneg hp1 hm)).1 h3
  intro h0
  rw [ENNReal.rpow_eq_zero_iff] at h0
  rcases h0 with ⟨h, _⟩ | ⟨h, _⟩
  · exact hm0 h
  · exact hm h

/-- Doob's inequality in `L^p` form at a fixed time, for a nonnegative submartingale. -/
lemma doob_fixed [IsProbabilityMeasure P] (hg : Submartingale g ℱ P) (hnn : 0 ≤ g)
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) (n : ℕ) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < maxFnN g n ω}
      ≤ ∫⁻ ω, ENNReal.ofReal (g n ω) ^ p ∂P := by
  set ε : ℝ≥0 := Real.toNNReal l with hε
  have hεl : (ε : ℝ) = l := Real.coe_toNNReal _ hl.le
  have hεl' : (ε : ℝ≥0∞) = ENNReal.ofReal l := rfl
  set A := {ω | (ε : ℝ) ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => g k ω} with hA
  have hsub : {ω | ENNReal.ofReal l < maxFnN g n ω} ⊆ A := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, maxFnN, lt_iSup_iff] at hω
    obtain ⟨k, hk, hlt⟩ := hω
    have hk' : k ∈ Finset.range (n + 1) := by
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_range]; omega
    have hnn' : 0 ≤ g k ω := hnn k ω
    have hlt' : l < g k ω := by
      have := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
      rwa [abs_of_nonneg hnn'] at this
    simp only [hA, Set.mem_ofPred_eq, hεl]
    exact hlt'.le.trans (Finset.le_sup' (fun k => g k ω) hk')
  have hmax := maximal_ineq hg hnn (ε := ε) n
  rw [← hA, ofReal_integral_eq_lintegral_ofReal (hg.integrable n).integrableOn
    (Eventually.of_forall fun ω => hnn n ω), hεl'] at hmax
  have hb : ∫⁻ ω in A, ENNReal.ofReal (g n ω) ^ p ∂P ≤ ∫⁻ ω, ENNReal.ofReal (g n ω) ^ p ∂P :=
    setLIntegral_le_lintegral _ _
  refine le_trans ?_ hb
  have hmono : P {ω | ENNReal.ofReal l < maxFnN g n ω} ≤ P A := measure_mono hsub
  refine le_trans (mul_le_mul' le_rfl hmono) ?_
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · subst hp1
    simpa using hmax
  · have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp1
    have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (g n ω)) (P.restrict A) :=
      ((hg.stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl).ennreal_ofReal.aemeasurable
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (P.restrict A) hpq hmeas
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul,
      Measure.restrict_apply_univ] at hH
    exact holder_step hpq hl (measure_ne_top P A) hmax hH

/-- The maximal set is the increasing union of the finite-time maximal sets. -/
lemma measure_maxFn_eq_iSup (P : Measure Ω) (g : ℕ → Ω → ℝ) (l : ℝ) :
    P {ω | ENNReal.ofReal l < maxFn g ω} = ⨆ n, P {ω | ENNReal.ofReal l < maxFnN g n ω} := by
  have hU : {ω | ENNReal.ofReal l < maxFn g ω} = ⋃ n, {ω | ENNReal.ofReal l < maxFnN g n ω} := by
    ext ω; simp [maxFn, lt_iSup_iff]
  rw [hU]
  refine Monotone.measure_iUnion fun n m hnm ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine lt_of_lt_of_le hω ?_
  simp only [maxFnN]
  exact biSup_mono fun k hk => by
    simp only [Finset.mem_Icc] at hk ⊢; omega

/-- (1.5) for a nonnegative submartingale `g` (nonnegative everywhere). -/
lemma eq_1_5_nonneg [IsProbabilityMeasure P] (hg : Submartingale g ℱ P) (hnn : 0 ≤ g)
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < maxFn g ω} ≤ pNorm P p g ^ p := by
  rw [measure_maxFn_eq_iSup, ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : {ω | ENNReal.ofReal l < maxFnN g 0 ω} = ∅ := by
      ext ω; simp [maxFnN]
    rw [this, measure_empty, mul_zero]; exact zero_le
  refine (doob_fixed hg hnn p hp l hl n).trans ?_
  have hp0 : 0 ≤ p := by linarith
  have h1 : ∫⁻ ω, ENNReal.ofReal (g n ω) ^ p ∂P
      = lpNormE P p (fun ω => ENNReal.ofReal |g n ω|) ^ p := by
    simp only [lpNormE]
    rw [rpow_one_div_rpow _ (by linarith)]
    congr 1
    funext ω
    rw [abs_of_nonneg (hnn n ω)]
  rw [h1]
  refine ENNReal.rpow_le_rpow ?_ hp0
  exact le_iSup₂ (f := fun n (_ : n ∈ Set.Ici (1 : ℕ)) =>
    lpNormE P p (fun ω => ENNReal.ofReal |g n ω|)) n hn

/-- (1.5). -/
theorem eq_1_5_core [IsProbabilityMeasure P] {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < maxFn f ω} ≤ pNorm P p f ^ p := by
  rcases hf with hf | ⟨hf, hnn⟩
  · -- martingale case: `|f|` is a nonnegative submartingale
    have hsub : Submartingale (f⁺ + (-f)⁺) ℱ P :=
      hf.submartingale.pos.add hf.neg.submartingale.pos
    have heq : (f⁺ + (-f)⁺) = fun n ω => |f n ω| := by
      funext n ω
      simp only [Pi.add_apply, Pi.posPart_apply, Pi.neg_apply]
      rw [posPart_neg, posPart_add_negPart]
    rw [heq] at hsub
    have hnn : (0 : ℕ → Ω → ℝ) ≤ fun n ω => |f n ω| := fun n ω => abs_nonneg _
    have h := eq_1_5_nonneg hsub hnn p hp l hl
    have e1 : maxFn (fun n ω => |f n ω|) = maxFn f := by
      funext ω; simp [maxFn, maxFnN, abs_abs]
    have e2 : pNorm P p (fun n ω => |f n ω|) = pNorm P p f := by
      simp [pNorm, abs_abs]
    rwa [e1, e2] at h
  · -- nonnegative submartingale case: `f⁺` is a nonnegative submartingale a.e. equal to `f`
    have hsub : Submartingale (f⁺) ℱ P := hf.pos
    have hnn' : (0 : ℕ → Ω → ℝ) ≤ f⁺ := fun n ω => by
      simp only [Pi.posPart_apply, Pi.zero_apply]
      exact posPart_nonneg _
    have h := eq_1_5_nonneg hsub hnn' p hp l hl
    have hae : ∀ᵐ ω ∂P, ∀ n, 1 ≤ n → |(f⁺) n ω| = |f n ω| := by
      rw [ae_all_iff]
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · filter_upwards [hnn n hn] with ω hω
        intro _
        simp only [Pi.posPart_apply]
        rw [posPart_eq_self.2 hω]
    have e1 : P {ω | ENNReal.ofReal l < maxFn (f⁺) ω} = P {ω | ENNReal.ofReal l < maxFn f ω} := by
      refine measure_congr ?_
      filter_upwards [hae] with ω hω
      have : maxFn (f⁺) ω = maxFn f ω := by
        simp only [maxFn, maxFnN]
        refine iSup_congr fun n => iSup_congr fun k => iSup_congr fun hk => ?_
        simp only [Finset.mem_Icc] at hk
        rw [hω k hk.1]
      change (ENNReal.ofReal l < maxFn (f⁺) ω) = (ENNReal.ofReal l < maxFn f ω)
      rw [this]
    have e2 : pNorm P p (f⁺) = pNorm P p f := by
      simp only [pNorm]
      refine iSup_congr fun n => iSup_congr fun hn => ?_
      simp only [lpNormE]
      congr 1
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with ω hω
      rw [hω n hn]
    rwa [e1, e2] at h

end BurkholderDFI.CondSquare

open BurkholderDFI.CondSquare


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < BurkholderDFI.SquareFnLp.maxFn f ω} ≤ BurkholderDFI.SquareFnLp.pNorm P p f ^ p := by
  exact eq_1_5_core hf p hp l hl
