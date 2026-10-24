-- Prove2me | solution 1 for CondPortOT.FiberDual.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T04:36:20.114551+00:00
-- url     : https://prove2.me/submissions/6026724e-1506-4865-81d7-e87e1ec9e4c2

import Mathlib
import Definitions.Def_CondPortOT_FiberDual_Setting
import Theorems.Thm_CondPortOT_FiberDual_reduction
import Theorems.Thm_CondPortOT_FiberDual_proposition_2_5
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality
open scoped Pointwise

namespace CondPortOTFDAux

open CondPortOT.FiberDual

lemma coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

lemma extIntegral_eq_integral {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (L : Y → ℝ) (hLi : Integrable L μ) :
    extIntegral μ (fun y => (L y : EReal)) = ((∫ y, L y ∂μ : ℝ) : EReal) := by
  have h1 : ∀ y, ((L y : EReal)).toENNReal = ENNReal.ofReal (L y) := fun y => by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have h2 : ∀ y, (-(L y : EReal)).toENNReal = ENNReal.ofReal (-L y) := fun y => by
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  unfold extIntegral
  simp only [h1, h2]
  have hp : ∫⁻ y, ENNReal.ofReal (L y) ∂μ ≠ ⊤ := hLi.lintegral_lt_top.ne
  have hn : ∫⁻ y, ENNReal.ofReal (-L y) ∂μ ≠ ⊤ := hLi.neg.lintegral_lt_top.ne
  rw [← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn, ← EReal.coe_sub,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hLi]

/-- The extended integral of a real function bounded above by `s + l c`. -/
lemma extIntegral_le {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (L c : Y → ℝ) (hL : Measurable L) (hc : Measurable c) (hc0 : ∀ y, 0 ≤ c y)
    (s l a : ℝ) (hl : 0 ≤ l) (ha : 0 ≤ a) (hb : ∀ y, L y ≤ s + l * c y)
    (hca : ∫⁻ y, ENNReal.ofReal (c y) ∂μ ≤ ENNReal.ofReal a) :
    extIntegral μ (fun y => (L y : EReal)) ≤ ((s + l * a : ℝ) : EReal) := by
  have hci : Integrable c μ := by
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hc0)]
    exact lt_of_le_of_lt hca ENNReal.ofReal_lt_top
  by_cases hneg : ∫⁻ y, ENNReal.ofReal (-L y) ∂μ = ⊤
  · have h2 : ∀ y, (-(L y : EReal)).toENNReal = ENNReal.ofReal (-L y) := fun y => by
      rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    unfold extIntegral
    simp only [h2, hneg, EReal.coe_ennreal_top, EReal.sub_top]
    exact bot_le
  · have hg : Integrable (fun y => |s| + l * c y) μ := (integrable_const _).add (hci.const_mul l)
    have hpos : Integrable (fun y => max (L y) 0) μ := by
      refine Integrable.mono' hg (hL.max measurable_const).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ ?_
      · have := hb y; have := le_abs_self s; linarith
      · have := hc0 y; positivity
    have hnegi : Integrable (fun y => max (-L y) 0) μ := by
      refine ⟨(hL.neg.max measurable_const).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (f := fun y => max (-L y) 0)
        (Filter.Eventually.of_forall fun y => le_max_right _ _)]
      have : ∀ y, ENNReal.ofReal (max (-L y) 0) = ENNReal.ofReal (-L y) := fun y => by
        rcases le_total 0 (-L y) with h | h
        · rw [max_eq_left h]
        · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
      simp_rw [this]; exact lt_top_iff_ne_top.2 hneg
    have hLi : Integrable L μ := by
      have : L = fun y => max (L y) 0 - max (-L y) 0 := by
        funext y; rcases le_total 0 (L y) with h | h
        · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
        · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
      rw [this]; exact hpos.sub hnegi
    rw [extIntegral_eq_integral μ L hLi, EReal.coe_le_coe_iff]
    have hint : ∫ y, L y ∂μ ≤ ∫ y, (s + l * c y) ∂μ :=
      integral_mono hLi ((integrable_const _).add (hci.const_mul l)) hb
    rw [integral_add (integrable_const _) (hci.const_mul l), integral_const, integral_const_mul]
      at hint
    have hc_le : ∫ y, c y ∂μ ≤ a := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hc0)
        hc.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal ha hca
    simp only [probReal_univ, one_smul] at hint
    nlinarith

/-- exit/entry cost of sample `i` when a share `p` of it lies in the fiber. -/
noncomputable def eC {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) (p : ℝ) (i : Fin N) : ℝ :=
  if i ∈ I then (1 - p) * d i else p * d i

lemma eC_nonneg {N : ℕ} (d : Fin N → ℝ) (hd : ∀ i, 0 ≤ d i) (I : Finset (Fin N)) (p : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (i : Fin N) : 0 ≤ eC d I p i := by
  unfold eC
  split_ifs
  · exact mul_nonneg (by linarith [hp.2]) (hd i)
  · exact mul_nonneg hp.1 (hd i)

lemma split_sum {N : ℕ} (I : Finset (Fin N)) {M : Type*} [AddCommMonoid M] (f g : Fin N → M) :
    ∑ i ∈ I, f i + ∑ i ∈ Iᶜ, g i = ∑ i, (if i ∈ I then f i else g i) := by
  rw [← Finset.sum_add_sum_compl I (fun i => if i ∈ I then f i else g i)]
  congr 1
  · exact Finset.sum_congr rfl fun i hi => by rw [if_pos hi]
  · exact Finset.sum_congr rfl fun i hi => by rw [if_neg (Finset.mem_compl.1 hi)]

/-- The cost constraint of the reduced problem, rewritten in real numbers. -/
lemma cost_real {Y : Type*} [MeasurableSpace Y] (DY : Y → Y → ℝ) {N : ℕ} (yh : Fin N → Y)
    (d : Fin N → ℝ) (hd : ∀ i, 0 ≤ d i) (I : Finset (Fin N)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (p : Fin N → ℝ) (μ : Fin N → Measure Y) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hcost : (∑ i ∈ I, (ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
                ENNReal.ofReal ((1 - p i) * d i)) +
            ∑ i ∈ Iᶜ, (ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
                ENNReal.ofReal (p i * d i))) ≤ ENNReal.ofReal (N * ρ)) :
    (∀ i, ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) =
        ENNReal.ofReal (p i * (∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i)).toReal)) ∧
      ∑ i, (p i * (∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i)).toReal + eC d I (p i) i) ≤ N * ρ := by
  set lint : Fin N → ENNReal := fun i => ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) with hlint
  rw [split_sum I (fun i => ENNReal.ofReal (p i) * lint i + ENNReal.ofReal ((1 - p i) * d i))
    (fun i => ENNReal.ofReal (p i) * lint i + ENNReal.ofReal (p i * d i))] at hcost
  have hcost' : ∑ i, (ENNReal.ofReal (p i) * lint i + ENNReal.ofReal (eC d I (p i) i)) ≤
      ENNReal.ofReal (N * ρ) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) hcost
    unfold eC; split_ifs <;> rfl
  have hfin : ∀ i, ENNReal.ofReal (p i) * lint i ≠ ⊤ := by
    intro i h
    have : ENNReal.ofReal (p i) * lint i ≤ ∑ i, (ENNReal.ofReal (p i) * lint i +
        ENNReal.ofReal (eC d I (p i) i)) :=
      le_trans le_self_add (Finset.single_le_sum (f := fun i => ENNReal.ofReal (p i) * lint i +
        ENNReal.ofReal (eC d I (p i) i)) (fun _ _ => zero_le) (Finset.mem_univ i))
    rw [h] at this
    exact ENNReal.ofReal_ne_top (top_le_iff.1 (le_trans this hcost'))
  have hprod : ∀ i, ENNReal.ofReal (p i) * lint i = ENNReal.ofReal (p i * (lint i).toReal) := by
    intro i
    rcases (hp i).1.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hne : lint i ≠ ⊤ := by
        intro htop; apply hfin i; rw [htop]
        exact ENNReal.mul_top (by simpa using hpos)
      rw [ENNReal.ofReal_mul (hp i).1, ENNReal.ofReal_toReal hne]
  refine ⟨hprod, ?_⟩
  simp_rw [hprod] at hcost'
  have hnn : ∀ i, 0 ≤ p i * (lint i).toReal + eC d I (p i) i := fun i =>
    add_nonneg (mul_nonneg (hp i).1 ENNReal.toReal_nonneg) (eC_nonneg d hd I _ (hp i) i)
  have : ∑ i, (ENNReal.ofReal (p i * (lint i).toReal) + ENNReal.ofReal (eC d I (p i) i)) =
      ENNReal.ofReal (∑ i, (p i * (lint i).toReal + eC d I (p i) i)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => hnn i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_add (mul_nonneg (hp i).1 ENNReal.toReal_nonneg)
      (eC_nonneg d hd I _ (hp i) i)]
  rw [this, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hcost'
  exact hcost'

/-- Weak duality for the reduced problem. -/
lemma weak {Y : Type*} [MeasurableSpace Y] (DY : Y → Y → ℝ) (hDYnn : ∀ y y', 0 ≤ DY y y')
    {N : ℕ} (hN : 0 < N) (yh : Fin N → Y) (hDYm : ∀ i, Measurable fun y => DY y (yh i))
    (d : Fin N → ℝ) (hd : ∀ i, 0 ≤ d i) (I : Finset (Fin N)) (ρ ε : ℝ) (hρ : 0 ≤ ρ)
    (hε : 0 < ε) (L : Y → ℝ) (hL : Measurable L)
    (p : Fin N → ℝ) (μ : Fin N → Measure Y) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hcost : (∑ i ∈ I, (ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
                ENNReal.ofReal ((1 - p i) * d i)) +
            ∑ i ∈ Iᶜ, (ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
                ENNReal.ofReal (p i * d i))) ≤ ENNReal.ofReal (N * ρ))
    (hmass : (N : ℝ) * ε ≤ ∑ i, p i)
    (v : DualPt N) (hv : InV d I ρ v)
    (hs : ∀ i, (⨆ y, ((L y - v.lam i * DY y (yh i) : ℝ) : EReal)) ≤ (v.s i : EReal)) :
    (((∑ i, p i)⁻¹ : ℝ) : EReal) *
        ∑ i, ((p i : ℝ) : EReal) * extIntegral (μ i) (fun y => (L y : EReal)) ≤
      ((v.phi + ((N : ℝ) * ε)⁻¹ * v.nuP - (N : ℝ)⁻¹ * v.nuM : ℝ) : EReal) := by
  obtain ⟨hlam, hnuP, hnuM, hvphi, hpsi, hI, hIc, hsum, hphil⟩ := hv
  obtain ⟨hprod, hcR⟩ := cost_real DY yh d hd I ρ hρ p μ hp hcost
  set a : Fin N → ℝ := fun i => (∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i)).toReal with ha
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set P := ∑ i, p i with hP
  have hPpos : 0 < P := lt_of_lt_of_le (mul_pos hNpos hε) hmass
  have hPN : P ≤ N := by
    calc P ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hp i).2
      _ = N := by simp
  -- per-sample bound on the objective
  have hterm : ∀ i, ((p i : ℝ) : EReal) * extIntegral (μ i) (fun y => (L y : EReal)) ≤
      ((p i * (v.s i + v.lam i * a i) : ℝ) : EReal) := by
    intro i
    rcases (hp i).1.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hb : ∀ y, L y ≤ v.s i + v.lam i * DY y (yh i) := by
        intro y
        have h := le_trans (le_iSup (fun y => ((L y - v.lam i * DY y (yh i) : ℝ) : EReal)) y)
          (hs i)
        rw [EReal.coe_le_coe_iff] at h
        linarith
      have hne : ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) ≠ ⊤ := by
        intro htop
        have h1 := hprod i
        rw [htop, ENNReal.mul_top (by simpa using hpos)] at h1
        exact ENNReal.ofReal_ne_top h1.symm
      have hca : ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) ≤ ENNReal.ofReal (a i) := by
        rw [ha]; simp only; rw [ENNReal.ofReal_toReal hne]
      have hle := extIntegral_le (μ i) L (fun y => DY y (yh i)) hL (hDYm i)
        (fun y => hDYnn _ _) (v.s i) (v.lam i) (a i) (hlam i) ENNReal.toReal_nonneg hb hca
      rw [EReal.coe_mul]
      exact mul_le_mul_of_nonneg_left hle (by exact_mod_cast hpos.le)
  have hsumE : ∑ i, ((p i : ℝ) : EReal) * extIntegral (μ i) (fun y => (L y : EReal)) ≤
      ((∑ i, p i * (v.s i + v.lam i * a i) : ℝ) : EReal) := by
    rw [coe_sum]
    exact Finset.sum_le_sum fun i _ => hterm i
  -- the real inequality
  have hreal : ∑ i, p i * (v.s i + v.lam i * a i) ≤ P * v.phi + v.nuP - v.nuM := by
    have hper : ∀ i, p i * (v.s i + v.lam i * a i) ≤
        p i * v.phi + v.psi i + v.vphi * (p i * a i + eC d I (p i) i) -
          (if i ∈ I then v.vphi * d i else 0) := by
      intro i
      have ha0 : 0 ≤ a i := ENNReal.toReal_nonneg
      have hp0 := (hp i).1
      have hp1 := (hp i).2
      have hψ := hpsi i
      have hl1 : v.lam i * (p i * a i) ≤ v.vphi * (p i * a i) :=
        mul_le_mul_of_nonneg_right (by linarith [hphil i]) (mul_nonneg hp0 ha0)
      have hpψ : p i * v.psi i ≤ v.psi i := by nlinarith
      unfold eC
      by_cases hi : i ∈ I
      · rw [if_pos hi, if_pos hi]
        have h1 := hI i hi
        have h2 : p i * v.s i ≤ p i * (v.phi - d i * v.vphi + v.psi i) :=
          mul_le_mul_of_nonneg_left (by linarith) hp0
        nlinarith
      · rw [if_neg hi, if_neg hi]
        have h1 := hIc i hi
        have h2 : p i * v.s i ≤ p i * (v.phi + d i * v.vphi + v.psi i) :=
          mul_le_mul_of_nonneg_left (by linarith) hp0
        nlinarith
    have hS := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hper i
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero] at hS
    have hfilt : (Finset.univ.filter fun i => i ∈ I) = I := by ext; simp
    rw [hfilt, ← Finset.mul_sum] at hS
    have hc2 : v.vphi * ∑ i, (p i * a i + eC d I (p i) i) ≤ v.vphi * (N * ρ) :=
      mul_le_mul_of_nonneg_left hcR hvphi
    nlinarith
  -- conclude
  have hinv : (0 : EReal) ≤ ((P⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.2 hPpos).le
  calc (((∑ i, p i)⁻¹ : ℝ) : EReal) *
        ∑ i, ((p i : ℝ) : EReal) * extIntegral (μ i) (fun y => (L y : EReal))
      ≤ ((P⁻¹ : ℝ) : EReal) * ((∑ i, p i * (v.s i + v.lam i * a i) : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_left hsumE hinv
    _ ≤ ((v.phi + ((N : ℝ) * ε)⁻¹ * v.nuP - (N : ℝ)⁻¹ * v.nuM : ℝ) : EReal) := by
        rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
        have h1 : P⁻¹ * (∑ i, p i * (v.s i + v.lam i * a i)) ≤
            P⁻¹ * (P * v.phi + v.nuP - v.nuM) :=
          mul_le_mul_of_nonneg_left hreal (inv_pos.2 hPpos).le
        have h2 : P⁻¹ * (P * v.phi + v.nuP - v.nuM) = v.phi + P⁻¹ * v.nuP - P⁻¹ * v.nuM := by
          field_simp
        have h3 : P⁻¹ * v.nuP ≤ ((N : ℝ) * ε)⁻¹ * v.nuP :=
          mul_le_mul_of_nonneg_right (inv_anti₀ (mul_pos hNpos hε) hmass) hnuP
        have h4 : (N : ℝ)⁻¹ * v.nuM ≤ P⁻¹ * v.nuM :=
          mul_le_mul_of_nonneg_right (inv_anti₀ hPpos hPN) hnuM
        linarith

/-! ### Strong duality -/

lemma slope_nonpos (k b : ℝ) (h : ∀ s : ℝ, 0 < s → k * s + b < 0) : k ≤ 0 := by
  by_contra hk
  push Not at hk
  have h1 := h ((|b| + 1) / k) (by positivity)
  have h2 : k * ((|b| + 1) / k) = |b| + 1 := by field_simp
  rw [h2] at h1
  linarith [neg_abs_le b]

lemma limit_nonpos (c k : ℝ) (h : ∀ s : ℝ, 0 < s → c + s * k < 0) : c ≤ 0 := by
  by_contra hc
  push Not at hc
  have hs : 0 < c / (|k| + 1) := by positivity
  have h1 := h (c / (|k| + 1)) hs
  have h2 : c / (|k| + 1) * |k| < c := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg k]
  have h3 : -(c / (|k| + 1) * |k|) ≤ c / (|k| + 1) * k := by
    nlinarith [mul_le_mul_of_nonneg_left (neg_abs_le k) hs.le]
  linarith

/-- Separation of a convex set of `(objective, constraint, constraint)` values from the
open orthant `{r > 0, u₁ < 0, u₂ < 0}`. -/
lemma sep3 (A : Set (ℝ × ℝ × ℝ)) (hA : Convex ℝ A)
    (hno : ∀ z ∈ A, ¬ (0 < z.1 ∧ z.2.1 < 0 ∧ z.2.2 < 0)) :
    ∃ α β1 β2 : ℝ, 0 ≤ α ∧ 0 ≤ β1 ∧ 0 ≤ β2 ∧ (α ≠ 0 ∨ β1 ≠ 0 ∨ β2 ≠ 0) ∧
      ∀ z ∈ A, α * z.1 ≤ β1 * z.2.1 + β2 * z.2.2 := by
  rcases A.eq_empty_or_nonempty with hAe | ⟨a0, ha0⟩
  · exact ⟨1, 0, 0, zero_le_one, le_rfl, le_rfl, Or.inl one_ne_zero, by simp [hAe]⟩
  set O : Set (ℝ × ℝ × ℝ) := Set.Iio 0 ×ˢ (Set.Ioi 0 ×ˢ Set.Ioi 0) with hO
  have hOc : Convex ℝ O := (convex_Iio 0).prod ((convex_Ioi 0).prod (convex_Ioi 0))
  have hOo : IsOpen O := isOpen_Iio.prod (isOpen_Ioi.prod isOpen_Ioi)
  have hK : Convex ℝ (A + O) := hA.add hOc
  have hKo : IsOpen (A + O) := hOo.add_left
  have h0 : (0 : ℝ × ℝ × ℝ) ∉ A + O := by
    intro hm
    obtain ⟨a, ha, o, ho, hao⟩ := Set.mem_add.1 hm
    have e1 : a.1 + o.1 = 0 := by rw [← Prod.fst_add, hao]; rfl
    have e2 : a.2.1 + o.2.1 = 0 := by
      have := congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) hao; simpa using this
    have e3 : a.2.2 + o.2.2 = 0 := by
      have := congrArg (fun z : ℝ × ℝ × ℝ => z.2.2) hao; simpa using this
    have ho1 : o.1 < 0 := ho.1
    have ho2 : 0 < o.2.1 := ho.2.1
    have ho3 : 0 < o.2.2 := ho.2.2
    exact hno a ha ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hK hKo h0
  have hfz : f 0 = 0 := map_zero f
  have hf_apply : ∀ z : ℝ × ℝ × ℝ,
      f z = z.1 * f (1, 0, 0) + z.2.1 * f (0, 1, 0) + z.2.2 * f (0, 0, 1) := by
    intro z
    have : z = z.1 • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + z.2.1 • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) +
        z.2.2 • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  set A0 := f (1, 0, 0) with hA0
  set B1 := f (0, 1, 0) with hB1
  set B2 := f (0, 0, 1) with hB2
  have hmem : ∀ a ∈ A, ∀ s1 s2 s3 : ℝ, 0 < s1 → 0 < s2 → 0 < s3 →
      A0 * (a.1 - s1) + B1 * (a.2.1 + s2) + B2 * (a.2.2 + s3) < 0 := by
    intro a ha s1 s2 s3 h1 h2 h3
    have hk : a + ((-s1, s2, s3) : ℝ × ℝ × ℝ) ∈ A + O :=
      Set.add_mem_add ha ⟨by simp [h1], h2, h3⟩
    have := hf _ hk
    rw [hfz, hf_apply] at this
    have q1 : (a + ((-s1, s2, s3) : ℝ × ℝ × ℝ)).1 = a.1 - s1 := by
      rw [Prod.fst_add]; ring
    have q2 : (a + ((-s1, s2, s3) : ℝ × ℝ × ℝ)).2.1 = a.2.1 + s2 := by
      rw [Prod.snd_add, Prod.fst_add]
    have q3 : (a + ((-s1, s2, s3) : ℝ × ℝ × ℝ)).2.2 = a.2.2 + s3 := by
      rw [Prod.snd_add, Prod.snd_add]
    rw [q1, q2, q3] at this
    linarith
  have hA0n : 0 ≤ A0 := by
    have := slope_nonpos (-A0) (A0 * a0.1 + B1 * (a0.2.1 + 1) + B2 * (a0.2.2 + 1))
      (fun s hs => by have := hmem a0 ha0 s 1 1 hs one_pos one_pos; linarith)
    linarith
  have hB1n : B1 ≤ 0 :=
    slope_nonpos B1 (A0 * (a0.1 - 1) + B1 * a0.2.1 + B2 * (a0.2.2 + 1))
      (fun s hs => by have := hmem a0 ha0 1 s 1 one_pos hs one_pos; linarith)
  have hB2n : B2 ≤ 0 :=
    slope_nonpos B2 (A0 * (a0.1 - 1) + B1 * (a0.2.1 + 1) + B2 * a0.2.2)
      (fun s hs => by have := hmem a0 ha0 1 1 s one_pos one_pos hs; linarith)
  refine ⟨A0, -B1, -B2, hA0n, by linarith, by linarith, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    obtain ⟨h1, h2, h3⟩ := hall
    have := hmem a0 ha0 1 1 1 one_pos one_pos one_pos
    rw [h1, neg_eq_zero.1 h2, neg_eq_zero.1 h3] at this
    linarith
  · intro z hz
    have := limit_nonpos (A0 * z.1 + B1 * z.2.1 + B2 * z.2.2) (-A0 + B1 + B2)
      (fun s hs => by have := hmem z hz s s s hs hs hs; linarith)
    linarith

/-- indicator of `i ∈ T` as a real number. -/
noncomputable def ind {N : ℕ} (T : Finset (Fin N)) (i : Fin N) : ℝ := if i ∈ T then 1 else 0

lemma ind_mem {N : ℕ} (T : Finset (Fin N)) (i : Fin N) : ind T i ∈ Set.Icc (0 : ℝ) 1 := by
  unfold ind; split_ifs <;> simp

/-- objective of a pure point. -/
noncomputable def rP {Y : Type*} (L : Y → ℝ) (M : ℝ) {N : ℕ} (T : Finset (Fin N))
    (y : Fin N → Y) : ℝ :=
  ∑ i, ind T i * (L (y i) - M)

/-- cost slack of a pure point. -/
noncomputable def u1P {Y : Type*} (DY : Y → Y → ℝ) {N : ℕ} (yh : Fin N → Y) (d : Fin N → ℝ)
    (I : Finset (Fin N)) (ρ : ℝ) (T : Finset (Fin N)) (y : Fin N → Y) : ℝ :=
  ∑ i, (ind T i * DY (y i) (yh i) + eC d I (ind T i) i) - N * ρ

/-- mass slack of a pure point. -/
noncomputable def u2P {N : ℕ} (ε : ℝ) (T : Finset (Fin N)) : ℝ :=
  N * ε - ∑ i, ind T i

/-- The reduced primal value. -/
noncomputable def Rval {Y : Type*} [MeasurableSpace Y] (DY : Y → Y → ℝ) {N : ℕ}
    (yh : Fin N → Y) (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ ε : ℝ) (L : Y → ℝ) : EReal :=
  ⨆ (p : Fin N → ℝ) (μ : Fin N → Measure Y)
    (_ : (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, IsProbabilityMeasure (μ i)) ∧
      (∑ i ∈ I,
          (ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
            ENNReal.ofReal ((1 - p i) * d i)) +
        ∑ i ∈ Iᶜ,
          (ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
            ENNReal.ofReal (p i * d i))
        ≤ ENNReal.ofReal (N * ρ)) ∧
      (N : ℝ) * ε ≤ ∑ i, p i),
    (((∑ i, p i)⁻¹ : ℝ) : EReal) *
      ∑ i, ((p i : ℝ) : EReal) * extIntegral (μ i) (fun y => (L y : EReal))

/-- The dual value. -/
noncomputable def Dval {Y : Type*} (DY : Y → Y → ℝ) {N : ℕ}
    (yh : Fin N → Y) (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ ε : ℝ) (L : Y → ℝ) : EReal :=
  ⨅ (v : DualPt N) (_ : InV d I ρ v ∧
      ∀ i, (⨆ y, ((L y - v.lam i * DY y (yh i) : ℝ) : EReal)) ≤ (v.s i : EReal)),
    ((v.phi + ((N : ℝ) * ε)⁻¹ * v.nuP - (N : ℝ)⁻¹ * v.nuM : ℝ) : EReal)

/-- A finitely supported probability measure. -/
lemma finmix {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y] {ι : Type*}
    (t : Finset ι) (c : ι → ℝ) (hc0 : ∀ j ∈ t, 0 ≤ c j) (hc1 : ∑ j ∈ t, c j = 1)
    (z : ι → Y) (L : Y → ℝ) (g : Y → ℝ) (hg : ∀ y, 0 ≤ g y) :
    IsProbabilityMeasure (∑ j ∈ t, ENNReal.ofReal (c j) • Measure.dirac (z j)) ∧
    extIntegral (∑ j ∈ t, ENNReal.ofReal (c j) • Measure.dirac (z j))
        (fun y => (L y : EReal)) = ((∑ j ∈ t, c j * L (z j) : ℝ) : EReal) ∧
    ∫⁻ y, ENNReal.ofReal (g y) ∂(∑ j ∈ t, ENNReal.ofReal (c j) • Measure.dirac (z j)) =
      ENNReal.ofReal (∑ j ∈ t, c j * g (z j)) := by
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg hc0, hc1, ENNReal.ofReal_one]
  · have hLint : Integrable L (∑ j ∈ t, ENNReal.ofReal (c j) • Measure.dirac (z j)) := by
      refine integrable_finsetSum_measure.2 fun i _ => ?_
      exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
    rw [extIntegral_eq_integral _ L hLint, integral_finsetSum_measure fun i _ =>
      (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hc0 i hi), smul_eq_mul]
  · simp only [lintegral_finsetSum_measure, lintegral_smul_measure, lintegral_dirac,
      smul_eq_mul]
    rw [ENNReal.ofReal_sum_of_nonneg fun i hi => mul_nonneg (hc0 i hi) (hg _)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ENNReal.ofReal_mul (hc0 i hi)]

lemma eC_affine {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) (q : ℝ) (i : Fin N) :
    eC d I q i = eC d I 0 i + q * (eC d I 1 i - eC d I 0 i) := by
  unfold eC; split_ifs <;> ring

lemma eC_mix {N : ℕ} (d : Fin N → ℝ) (I : Finset (Fin N)) {ι : Type*} (t : Finset ι)
    (w : ι → ℝ) (hw1 : ∑ j ∈ t, w j = 1) (q : ι → ℝ) (i : Fin N) :
    ∑ j ∈ t, w j * eC d I (q j) i = eC d I (∑ j ∈ t, w j * q j) i := by
  rw [eC_affine d I (∑ j ∈ t, w j * q j) i]
  simp_rw [eC_affine d I (q _) i]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hw1]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  ring

/-- A convex combination of pure points that is strictly profitable, strictly within budget and
meets the mass requirement yields a feasible point of the reduced problem beating `M`. -/
lemma mix {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y] (DY : Y → Y → ℝ)
    (hDYnn : ∀ y y', 0 ≤ DY y y') {N : ℕ} (hN : 0 < N) (yh : Fin N → Y)
    (d : Fin N → ℝ) (hd : ∀ i, 0 ≤ d i) (I : Finset (Fin N)) (ρ ε : ℝ) (hρ : 0 ≤ ρ)
    (hε : 0 < ε) (L : Y → ℝ) (M : ℝ)
    {ι : Type*} (t : Finset ι) (w : ι → ℝ) (hw0 : ∀ j ∈ t, 0 ≤ w j) (hw1 : ∑ j ∈ t, w j = 1)
    (T : ι → Finset (Fin N)) (y : ι → Fin N → Y)
    (hr : 0 < ∑ j ∈ t, w j * rP L M (T j) (y j))
    (hu1 : ∑ j ∈ t, w j * u1P DY yh d I ρ (T j) (y j) < 0)
    (hu2 : ∑ j ∈ t, w j * u2P ε (T j) ≤ 0) :
    (M : EReal) < Rval DY yh d I ρ ε L := by
  classical
  set ω : ι → Fin N → ℝ := fun j i => w j * ind (T j) i with hω
  have hω0 : ∀ j ∈ t, ∀ i, 0 ≤ ω j i := fun j hj i => mul_nonneg (hw0 j hj) (ind_mem _ _).1
  set p : Fin N → ℝ := fun i => ∑ j ∈ t, ω j i with hp_def
  have hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    refine ⟨Finset.sum_nonneg fun j hj => hω0 j hj i, ?_⟩
    rw [← hw1]
    refine Finset.sum_le_sum fun j hj => ?_
    have := (ind_mem (T j) i).2
    have := hw0 j hj
    simp only [hω]
    nlinarith
  set Ls : Fin N → ℝ := fun i => ∑ j ∈ t, ω j i * L (y j i) with hLs
  set Ds : Fin N → ℝ := fun i => ∑ j ∈ t, ω j i * DY (y j i) (yh i) with hDs
  have hr' : ∑ j ∈ t, w j * rP L M (T j) (y j) = ∑ i, (Ls i - M * p i) := by
    simp only [rP, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hLs, hp_def, hω, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hu1' : ∑ j ∈ t, w j * u1P DY yh d I ρ (T j) (y j) =
      ∑ i, (Ds i + eC d I (p i) i) - N * ρ := by
    simp only [u1P, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mul_add, Finset.sum_add_distrib]
    rw [eC_mix d I t w hw1 (fun j => ind (T j) i) i]
    congr 1
    simp only [hDs, hω]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hu2' : ∑ j ∈ t, w j * u2P ε (T j) = N * ε - ∑ i, p i := by
    simp only [u2P, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  -- the measures
  have hNe : Nonempty Y := ⟨yh ⟨0, hN⟩⟩
  let μ : Fin N → Measure Y := fun i => if p i = 0 then Measure.dirac (yh i) else
    ∑ j ∈ t, ENNReal.ofReal (ω j i / p i) • Measure.dirac (y j i)
  have hper : ∀ i, IsProbabilityMeasure (μ i) ∧
      ((p i : ℝ) : EReal) * extIntegral (μ i) (fun y => (L y : EReal)) = ((Ls i : ℝ) : EReal) ∧
      ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) = ENNReal.ofReal (Ds i) := by
    intro i
    by_cases h0 : p i = 0
    · have hz : ∀ j ∈ t, ω j i = 0 := (Finset.sum_eq_zero_iff_of_nonneg
        fun j hj => hω0 j hj i).1 h0
      have hLs0 : Ls i = 0 := Finset.sum_eq_zero fun j hj => by rw [hz j hj, zero_mul]
      have hDs0 : Ds i = 0 := Finset.sum_eq_zero fun j hj => by rw [hz j hj, zero_mul]
      simp only [μ, if_pos h0, h0, hLs0, hDs0, EReal.coe_zero, zero_mul, ENNReal.ofReal_zero,
        and_true]
      first
        | exact inferInstance
        | exact ⟨inferInstance, trivial⟩
        | exact ⟨inferInstance, rfl, rfl⟩
    · have hpos : 0 < p i := lt_of_le_of_ne (hp i).1 (Ne.symm h0)
      have hc0 : ∀ j ∈ t, 0 ≤ ω j i / p i := fun j hj => div_nonneg (hω0 j hj i) hpos.le
      have hc1 : ∑ j ∈ t, ω j i / p i = 1 := by rw [← Finset.sum_div]; exact div_self h0
      obtain ⟨hprob, hext, hlint⟩ := finmix t (fun j => ω j i / p i) hc0 hc1 (fun j => y j i) L
        (fun y => DY y (yh i)) (fun y => hDYnn _ _)
      simp only [μ, if_neg h0]
      refine ⟨hprob, ?_, ?_⟩
      · rw [hext, ← EReal.coe_mul, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp
      · rw [hlint, ← ENNReal.ofReal_mul hpos.le, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hPpos : 0 < ∑ i, p i := by nlinarith [mul_pos hNpos hε]
  -- feasibility
  have hfeas : (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, IsProbabilityMeasure (μ i)) ∧
      (∑ i ∈ I,
          (ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
            ENNReal.ofReal ((1 - p i) * d i)) +
        ∑ i ∈ Iᶜ,
          (ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
            ENNReal.ofReal (p i * d i))
        ≤ ENNReal.ofReal (N * ρ)) ∧
      (N : ℝ) * ε ≤ ∑ i, p i := by
    refine ⟨hp, fun i => (hper i).1, ?_, by linarith⟩
    rw [split_sum I (fun i => ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
            ENNReal.ofReal ((1 - p i) * d i))
          (fun i => ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
            ENNReal.ofReal (p i * d i))]
    have hDs0 : ∀ i, 0 ≤ Ds i := fun i =>
      Finset.sum_nonneg fun j hj => mul_nonneg (hω0 j hj i) (hDYnn _ _)
    have : ∀ i, (if i ∈ I then ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
            ENNReal.ofReal ((1 - p i) * d i) else
          ENNReal.ofReal (p i) * ∫⁻ y, ENNReal.ofReal (DY y (yh i)) ∂(μ i) +
            ENNReal.ofReal (p i * d i)) = ENNReal.ofReal (Ds i + eC d I (p i) i) := by
      intro i
      rw [(hper i).2.2, ENNReal.ofReal_add (hDs0 i) (eC_nonneg d hd I _ (hp i) i)]
      unfold eC
      split_ifs <;> rfl
    simp_rw [this]
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ =>
      add_nonneg (hDs0 i) (eC_nonneg d hd I _ (hp i) i)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hobj : (((∑ i, p i)⁻¹ : ℝ) : EReal) *
      ∑ i, ((p i : ℝ) : EReal) * extIntegral (μ i) (fun y => (L y : EReal)) =
      (((∑ i, p i)⁻¹ * ∑ i, Ls i : ℝ) : EReal) := by
    simp_rw [fun i => (hper i).2.1]
    rw [← coe_sum, ← EReal.coe_mul]
  have hlt : M < (∑ i, p i)⁻¹ * ∑ i, Ls i := by
    rw [lt_inv_mul_iff₀ hPpos]
    have : ∑ i, (Ls i - M * p i) = ∑ i, Ls i - M * ∑ i, p i := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    linarith
  calc (M : EReal) < (((∑ i, p i)⁻¹ * ∑ i, Ls i : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 hlt
    _ = _ := hobj.symm
    _ ≤ Rval DY yh d I ρ ε L := by
      unfold Rval
      exact le_iSup_of_le p (le_iSup_of_le μ (le_iSup_of_le hfeas le_rfl))

lemma sum_ind_single {N : ℕ} (i : Fin N) (f : Fin N → ℝ) :
    ∑ k, ind {i} k * f k = f i := by
  simp [ind]

/-- Dual construction: Lagrange multipliers `φ, κ ≥ 0` for the pure points give a dual
feasible point of value `M`. -/
lemma dual_le {Y : Type*} (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (yh : Fin N → Y)
    (d : Fin N → ℝ) (I : Finset (Fin N)) (ρ ε : ℝ) (hε : 0 < ε) (L : Y → ℝ) (M φ κ : ℝ)
    (hφ : 0 ≤ φ) (hκ : 0 ≤ κ)
    (H : ∀ (T : Finset (Fin N)) (y : Fin N → Y),
      rP L M T y ≤ φ * u1P DY yh d I ρ T y + κ * u2P ε T) :
    Dval DY yh d I ρ ε L ≤ (M : EReal) := by
  classical
  have hNe : Nonempty Y := ⟨yh ⟨0, hN⟩⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- rearrangement of the multiplier inequality
  have hgen : ∀ (T : Finset (Fin N)) (y : Fin N → Y),
      rP L M T y - φ * u1P DY yh d I ρ T y - κ * u2P ε T =
        ∑ i, (ind T i * (L (y i) - M - φ * DY (y i) (yh i) + κ) - φ * eC d I (ind T i) i) +
          φ * (N * ρ) - κ * (N * ε) := by
    intro T y
    have e : ∀ i, ind T i * (L (y i) - M - φ * DY (y i) (yh i) + κ) - φ * eC d I (ind T i) i =
        ind T i * (L (y i) - M) - φ * (ind T i * DY (y i) (yh i) + eC d I (ind T i) i) +
          κ * ind T i := fun i => by ring
    simp_rw [e]
    simp only [rP, u1P, u2P, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  -- an upper bound for `L - φ DY(·, ŷᵢ)`
  have hB : ∀ i (y' : Y), L y' - φ * DY y' (yh i) ≤
      M + φ * (∑ k, eC d I (ind {i} k) k - N * ρ) + κ * (N * ε - 1) := by
    intro i y'
    have h := H {i} (fun _ => y')
    simp only [rP, u1P, u2P, Finset.sum_add_distrib, sum_ind_single] at h
    have h1 : ∑ k, ind {i} k = 1 := by
      have := sum_ind_single i (fun _ => (1 : ℝ)); simpa using this
    rw [h1] at h
    linarith
  set s : Fin N → ℝ := fun i => sSup (Set.range fun y' => L y' - φ * DY y' (yh i)) with hs_def
  have hbdd : ∀ i, BddAbove (Set.range fun y' => L y' - φ * DY y' (yh i)) := fun i =>
    ⟨_, by rintro _ ⟨y', rfl⟩; exact hB i y'⟩
  have hle : ∀ i y', L y' - φ * DY y' (yh i) ≤ s i := fun i y' => le_csSup (hbdd i) ⟨y', rfl⟩
  have happrox : ∀ η : ℝ, 0 < η → ∀ i, ∃ y', s i - η < L y' - φ * DY y' (yh i) := by
    intro η hη i
    obtain ⟨_, ⟨y', rfl⟩, h⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _)
      (by linarith : s i - η < s i)
    exact ⟨y', h⟩
  set ϕ := M - κ with hϕ
  set ψ : Fin N → ℝ := fun i =>
    max (s i - ϕ + (if i ∈ I then φ * d i else -(φ * d i))) 0 with hψ
  have key : ∑ i, ψ i ≤ κ * (N * ε) + φ * (∑ i ∈ I, d i - N * ρ) := by
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    set η := δ / (2 * N) with hη
    have hηpos : 0 < η := by positivity
    choose ys hys using happrox η hηpos
    set onv : Fin N → ℝ := fun i => L (ys i) - M - φ * DY (ys i) (yh i) + κ - φ * eC d I 1 i
    set offv : Fin N → ℝ := fun i => -(φ * eC d I 0 i)
    set T := Finset.univ.filter fun i => offv i ≤ onv i with hT
    have h := H T ys
    have hg := hgen T ys
    have hterm : ∀ i, ψ i - (if i ∈ I then φ * d i else 0) - η ≤
        ind T i * (L (ys i) - M - φ * DY (ys i) (yh i) + κ) - φ * eC d I (ind T i) i := by
      intro i
      have hy := hys i
      have hcase : ind T i * (L (ys i) - M - φ * DY (ys i) (yh i) + κ) - φ * eC d I (ind T i) i
          = max (onv i) (offv i) := by
        by_cases hiT : i ∈ T
        · have hc : offv i ≤ onv i := (Finset.mem_filter.1 hiT).2
          simp only [ind, if_pos hiT, one_mul, max_eq_left hc, onv]
        · have hc : ¬ offv i ≤ onv i := fun hc => hiT (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩)
          push Not at hc
          simp only [ind, if_neg hiT, zero_mul, zero_sub, max_eq_right hc.le, offv]
      rw [hcase]
      simp only [hψ, onv, offv, eC]
      by_cases hiI : i ∈ I
      · simp only [if_pos hiI]
        rw [sub_sub, sub_le_iff_le_add, max_le_iff]
        constructor
        · have := le_max_left (L (ys i) - M - φ * DY (ys i) (yh i) + κ - φ * ((1 - 1) * d i))
            (-(φ * ((1 - 0) * d i)))
          linarith
        · have := le_max_right (L (ys i) - M - φ * DY (ys i) (yh i) + κ - φ * ((1 - 1) * d i))
            (-(φ * ((1 - 0) * d i)))
          linarith
      · simp only [if_neg hiI]
        rw [sub_sub, sub_le_iff_le_add, max_le_iff]
        constructor
        · have := le_max_left (L (ys i) - M - φ * DY (ys i) (yh i) + κ - φ * (1 * d i))
            (-(φ * (0 * d i)))
          linarith
        · have := le_max_right (L (ys i) - M - φ * DY (ys i) (yh i) + κ - φ * (1 * d i))
            (-(φ * (0 * d i)))
          linarith
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    have hI' : ∑ i, (if i ∈ I then φ * d i else 0) = φ * ∑ i ∈ I, d i := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
    rw [hI'] at hsum
    have hNη : (N : ℝ) * η = δ / 2 := by rw [hη]; field_simp
    linarith
  -- the dual point
  let v : DualPt N := ⟨fun _ => φ, s, κ * (N * ε), 0, ϕ, φ, ψ⟩
  have hv : InV d I ρ v ∧
      ∀ i, (⨆ y, ((L y - v.lam i * DY y (yh i) : ℝ) : EReal)) ≤ (v.s i : EReal) := by
    refine ⟨⟨fun _ => hφ, by positivity, le_rfl, hφ, fun i => le_max_right _ _, ?_, ?_, ?_,
      fun i => by simp [v]⟩, ?_⟩
    · intro i hi
      have := le_max_left (s i - ϕ + (if i ∈ I then φ * d i else -(φ * d i))) 0
      rw [if_pos hi] at this
      simp only [v, hψ]
      rw [if_pos hi]
      linarith
    · intro i hi
      have := le_max_left (s i - ϕ + (if i ∈ I then φ * d i else -(φ * d i))) 0
      rw [if_neg hi] at this
      simp only [v, hψ]
      rw [if_neg hi]
      linarith
    · simp only [v]
      linarith
    · intro i
      exact iSup_le fun y => EReal.coe_le_coe_iff.2 (hle i y)
  unfold Dval
  refine iInf₂_le_of_le v hv (le_of_eq ?_)
  rw [EReal.coe_eq_coe_iff]
  simp only [v, hϕ]
  field_simp
  ring

lemma sum_ind_univ {N : ℕ} : ∑ i : Fin N, ind (Finset.univ : Finset (Fin N)) i = N := by
  simp [ind]

lemma sum_ind_lt {N : ℕ} (T : Finset (Fin N)) (hT : T ≠ Finset.univ) :
    ∑ i, ind T i ≤ (N : ℝ) - 1 := by
  have h1 : ∑ i, ind T i = (T.card : ℝ) := by
    simp only [ind]
    rw [Finset.sum_boole]
    congr 2
    ext i; simp
  have h2 : T.card < N := by
    have := Finset.card_lt_card (Finset.ssubset_univ_iff.2 hT)
    simpa using this
  rw [h1]
  have : ((T.card : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast h2
  linarith

/-- Strong duality for the reduced problem. -/
lemma strong {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y] (DY : Y → Y → ℝ)
    (hDYnn : ∀ y y', 0 ≤ DY y y') {N : ℕ} (hN : 0 < N) (yh : Fin N → Y)
    (hDY0 : ∀ i, DY (yh i) (yh i) = 0)
    (d : Fin N → ℝ) (hd : ∀ i, 0 ≤ d i) (I : Finset (Fin N)) (ρ ε : ℝ) (hρ : 0 ≤ ρ)
    (hε : 0 < ε) (L : Y → ℝ)
    (hfeas : ∃ p : Fin N → ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧ (N : ℝ) * ε ≤ ∑ i, p i ∧
      ∑ i, eC d I (p i) i < N * ρ) :
    Dval DY yh d I ρ ε L ≤ Rval DY yh d I ρ ε L := by
  classical
  have hNe : Nonempty Y := ⟨yh ⟨0, hN⟩⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← EReal.le_of_forall_lt_iff_le]
  intro M hM
  have hnoMix : ∀ {ι : Type} (t : Finset ι) (w : ι → ℝ), (∀ j ∈ t, 0 ≤ w j) →
      ∑ j ∈ t, w j = 1 → ∀ (T : ι → Finset (Fin N)) (y : ι → Fin N → Y),
      ¬ (0 < ∑ j ∈ t, w j * rP L M (T j) (y j) ∧
        ∑ j ∈ t, w j * u1P DY yh d I ρ (T j) (y j) < 0 ∧
        ∑ j ∈ t, w j * u2P ε (T j) ≤ 0) := by
    rintro ι t w hw0 hw1 T y ⟨h1, h2, h3⟩
    exact absurd hM (not_lt.2
      (mix DY hDYnn hN yh d hd I ρ ε hρ hε L M t w hw0 hw1 T y h1 h2 h3).le)
  have hu1yh : ∀ T, u1P DY yh d I ρ T yh = ∑ i, eC d I (ind T i) i - N * ρ := by
    intro T; simp [u1P, hDY0]
  obtain ⟨ps, hps, hmass, hcost⟩ := hfeas
  -- first separation
  set F : Finset (Fin N) × (Fin N → Y) → ℝ × ℝ × ℝ := fun Ty =>
    (rP L M Ty.1 Ty.2, u1P DY yh d I ρ Ty.1 Ty.2, u2P ε Ty.1) with hF
  have hno : ∀ z ∈ convexHull ℝ (Set.range F), ¬ (0 < z.1 ∧ z.2.1 < 0 ∧ z.2.2 < 0) := by
    intro z hz h
    rw [convexHull_eq] at hz
    obtain ⟨ι, t, w, zz, hw0, hw1, hzz, hcm⟩ := hz
    choose! Ty hTy using hzz
    have hz_eq : z = ∑ j ∈ t, w j • zz j := by
      rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]
    have c1 : z.1 = ∑ j ∈ t, w j * rP L M (Ty j).1 (Ty j).2 := by
      rw [hz_eq, Prod.fst_sum]
      exact Finset.sum_congr rfl fun j hj => by rw [Prod.smul_fst, smul_eq_mul, ← hTy j hj]
    have c2 : z.2.1 = ∑ j ∈ t, w j * u1P DY yh d I ρ (Ty j).1 (Ty j).2 := by
      rw [hz_eq, Prod.snd_sum, Prod.fst_sum]
      exact Finset.sum_congr rfl fun j hj => by
        rw [Prod.smul_snd, Prod.smul_fst, smul_eq_mul, ← hTy j hj]
    have c3 : z.2.2 = ∑ j ∈ t, w j * u2P ε (Ty j).1 := by
      rw [hz_eq, Prod.snd_sum, Prod.snd_sum]
      exact Finset.sum_congr rfl fun j hj => by
        rw [Prod.smul_snd, Prod.smul_snd, smul_eq_mul, ← hTy j hj]
    exact hnoMix t w hw0 hw1 (fun j => (Ty j).1) (fun j => (Ty j).2)
      ⟨c1 ▸ h.1, c2 ▸ h.2.1, (c3 ▸ h.2.2).le⟩
  obtain ⟨α, β1, β2, hα, hβ1, hβ2, hnz, hsep⟩ := sep3 _ (convex_convexHull ℝ _) hno
  have hpure : ∀ T y, α * rP L M T y ≤ β1 * u1P DY yh d I ρ T y + β2 * u2P ε T :=
    fun T y => hsep _ (subset_convexHull ℝ _ ⟨(T, y), rfl⟩)
  rcases hα.eq_or_lt with hα0 | hαpos
  · -- degenerate multiplier: forces `ε = 1`
    have hβ1z : β1 = 0 := by
      by_contra hne
      have hβ1pos : 0 < β1 := lt_of_le_of_ne hβ1 (Ne.symm hne)
      set c : Fin N → ℝ := fun i => β1 * (eC d I 1 i - eC d I 0 i) - β2 with hc
      set Ts := Finset.univ.filter fun i => c i < 0 with hTs
      have h := hpure Ts yh
      rw [← hα0, zero_mul, hu1yh] at h
      have hper : ∀ i, β1 * eC d I (ind Ts i) i - β2 * ind Ts i ≤
          β1 * eC d I (ps i) i - β2 * ps i := by
        intro i
        rw [eC_affine d I (ind Ts i) i, eC_affine d I (ps i) i]
        have hp0 := (hps i).1
        have hp1 := (hps i).2
        by_cases hi : i ∈ Ts
        · have hci : c i < 0 := (Finset.mem_filter.1 hi).2
          simp only [ind, if_pos hi]
          simp only [hc] at hci
          nlinarith
        · have hci : ¬ c i < 0 := fun hci => hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, hci⟩)
          push Not at hci
          simp only [ind, if_neg hi]
          simp only [hc] at hci
          nlinarith
      have hsumle := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hper i
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum] at hsumle
      unfold u2P at h
      nlinarith [mul_pos hβ1pos (sub_pos.2 hcost), mul_nonneg hβ2 (sub_nonneg.2 hmass)]
    have hβ2pos : 0 < β2 := by
      rcases hnz with h | h | h
      · exact absurd hα0.symm h
      · exact absurd hβ1z h
      · exact lt_of_le_of_ne hβ2 (Ne.symm h)
    have hε1 : ε = 1 := by
      have h := hpure Finset.univ yh
      rw [← hα0, hβ1z, zero_mul, zero_mul, zero_add] at h
      unfold u2P at h
      rw [sum_ind_univ] at h
      have hge : (N : ℝ) * 1 ≤ N * ε := by nlinarith
      have hge' : 1 ≤ ε := le_of_mul_le_mul_left hge hNpos
      have hsle : ∑ i, ps i ≤ N := by
        calc ∑ i, ps i ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hps i).2
          _ = N := by simp
      have hle' : ε ≤ 1 := by
        have : (N : ℝ) * ε ≤ N * 1 := by linarith
        exact le_of_mul_le_mul_left this hNpos
      linarith
    have hps1 : ∀ i, ps i = 1 := by
      have hsum : ∑ i, (1 - ps i) = 0 := by
        have hsle : ∑ i, (1 - ps i) ≤ 0 := by
          rw [Finset.sum_sub_distrib]; simp only [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
          rw [hε1, mul_one] at hmass; linarith
        exact le_antisymm hsle (Finset.sum_nonneg fun i _ => sub_nonneg.2 (hps i).2)
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.2 (hps i).2).1 hsum i
        (Finset.mem_univ _)
      linarith
    have hcost1 : ∑ i, eC d I (ind Finset.univ i) i < N * ρ := by
      have : ∀ i, ind (Finset.univ : Finset (Fin N)) i = ps i := fun i => by
        simp [ind, hps1 i]
      simp_rw [this]; exact hcost
    have hu2univ : u2P ε (Finset.univ : Finset (Fin N)) = 0 := by
      unfold u2P; rw [sum_ind_univ, hε1]; ring
    -- second separation, with all samples fully in the fiber
    set F' : (Fin N → Y) → ℝ × ℝ × ℝ := fun y =>
      (rP L M Finset.univ y, u1P DY yh d I ρ Finset.univ y, u1P DY yh d I ρ Finset.univ y)
      with hF'
    have hno' : ∀ z ∈ convexHull ℝ (Set.range F'), ¬ (0 < z.1 ∧ z.2.1 < 0 ∧ z.2.2 < 0) := by
      intro z hz h
      rw [convexHull_eq] at hz
      obtain ⟨ι, t, w, zz, hw0, hw1, hzz, hcm⟩ := hz
      choose! ys hys using hzz
      have hz_eq : z = ∑ j ∈ t, w j • zz j := by
        rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]
      have c1 : z.1 = ∑ j ∈ t, w j * rP L M Finset.univ (ys j) := by
        rw [hz_eq, Prod.fst_sum]
        exact Finset.sum_congr rfl fun j hj => by rw [Prod.smul_fst, smul_eq_mul, ← hys j hj]
      have c2 : z.2.1 = ∑ j ∈ t, w j * u1P DY yh d I ρ Finset.univ (ys j) := by
        rw [hz_eq, Prod.snd_sum, Prod.fst_sum]
        exact Finset.sum_congr rfl fun j hj => by
          rw [Prod.smul_snd, Prod.smul_fst, smul_eq_mul, ← hys j hj]
      refine hnoMix t w hw0 hw1 (fun _ => Finset.univ) ys ⟨c1 ▸ h.1, c2 ▸ h.2.1, ?_⟩
      simp only [hu2univ, mul_zero, Finset.sum_const_zero, le_refl]
    obtain ⟨α', β1', β2', hα', hβ1', hβ2', hnz', hsep'⟩ := sep3 _ (convex_convexHull ℝ _) hno'
    have hpure' : ∀ y, α' * rP L M Finset.univ y ≤
        (β1' + β2') * u1P DY yh d I ρ Finset.univ y := by
      intro y
      have := hsep' _ (subset_convexHull ℝ _ ⟨y, rfl⟩)
      simp only [hF'] at this
      linarith
    have hα'pos : 0 < α' := by
      rcases hα'.eq_or_lt with h0 | h
      · exfalso
        have h1 := hpure' yh
        rw [← h0, zero_mul, hu1yh] at h1
        have h2 : β1' + β2' ≤ 0 := by nlinarith
        have h3 : β1' = 0 := by linarith
        have h4 : β2' = 0 := by linarith
        rcases hnz' with h5 | h5 | h5
        · exact h5 h0.symm
        · exact h5 h3
        · exact h5 h4
      · exact h
    set φ := (β1' + β2') / α' with hφdef
    have hφ : 0 ≤ φ := by positivity
    have hU : ∀ y, rP L M Finset.univ y ≤ φ * u1P DY yh d I ρ Finset.univ y := by
      intro y
      have := hpure' y
      rw [hφdef, div_mul_eq_mul_div, le_div_iff₀ hα'pos]
      linarith
    -- uniform bound
    set G := φ * (∑ k, eC d I 1 k) - φ * (N * ρ) + ∑ k, |L (yh k) - M| with hG
    have hGb : ∀ i y', L y' - M - φ * DY y' (yh i) ≤ G := by
      intro i y'
      have h := hU (Function.update yh i y')
      simp only [rP, u1P, ind, Finset.mem_univ, if_true, one_mul] at h
      set g : Fin N → ℝ := fun k =>
        L (Function.update yh i y' k) - M - φ * DY (Function.update yh i y' k) (yh k) with hg
      have hsplit : ∑ k, (L (Function.update yh i y' k) - M) -
          φ * (∑ k, (DY (Function.update yh i y' k) (yh k) + eC d I 1 k) - N * ρ) =
          ∑ k, g k - φ * (∑ k, eC d I 1 k) + φ * (N * ρ) := by
        simp only [hg, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      have hgk : ∀ k ∈ Finset.univ.erase i, -|L (yh k) - M| ≤ g k := by
        intro k hk
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        simp only [hg, Function.update_of_ne hki, hDY0, mul_zero, sub_zero]
        exact neg_abs_le _
      have hgi : g i = L y' - M - φ * DY y' (yh i) := by
        simp only [hg, Function.update_self]
      have herase := Finset.add_sum_erase Finset.univ g (Finset.mem_univ i)
      have hlow := Finset.sum_le_sum hgk
      have habs : ∑ k ∈ Finset.univ.erase i, |L (yh k) - M| ≤ ∑ k, |L (yh k) - M| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => abs_nonneg _)
      rw [Finset.sum_neg_distrib] at hlow
      linarith
    set κ := (N : ℝ) * |G| + φ * (N * ρ) + 1 with hκdef
    have hκ : 0 ≤ κ := by positivity
    apply dual_le DY hN yh d I ρ ε hε L M φ κ hφ hκ
    intro T y
    by_cases hT : T = Finset.univ
    · subst hT; rw [hu2univ, mul_zero, add_zero]; exact hU y
    · have hu2 : 1 ≤ u2P ε T := by
        unfold u2P; rw [hε1, mul_one]; linarith [sum_ind_lt T hT]
      have hr : rP L M T y - φ * u1P DY yh d I ρ T y ≤ (N : ℝ) * |G| + φ * (N * ρ) := by
        have e : rP L M T y - φ * u1P DY yh d I ρ T y =
            ∑ i, (ind T i * (L (y i) - M - φ * DY (y i) (yh i)) - φ * eC d I (ind T i) i) +
              φ * (N * ρ) := by
          calc rP L M T y - φ * u1P DY yh d I ρ T y
              = ∑ i, ind T i * (L (y i) - M) -
                  φ * ∑ i, (ind T i * DY (y i) (yh i) + eC d I (ind T i) i) + φ * (N * ρ) := by
                unfold rP u1P; ring
            _ = ∑ i, (ind T i * (L (y i) - M) -
                  φ * (ind T i * DY (y i) (yh i) + eC d I (ind T i) i)) + φ * (N * ρ) := by
                rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            _ = _ := by
                congr 1
                exact Finset.sum_congr rfl fun i _ => by ring
        rw [e]
        have hper : ∀ i, ind T i * (L (y i) - M - φ * DY (y i) (yh i)) -
            φ * eC d I (ind T i) i ≤ |G| := by
          intro i
          have h1 := hGb i (y i)
          have h2 : 0 ≤ φ * eC d I (ind T i) i := mul_nonneg hφ (eC_nonneg d hd I _ (ind_mem T i) i)
          have h3 := ind_mem T i
          by_cases hiT : i ∈ T
          · simp only [ind, if_pos hiT] at h2 ⊢
            linarith [le_abs_self G]
          · simp only [ind, if_neg hiT] at h2 ⊢
            linarith [abs_nonneg G]
        have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hper i
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
        linarith
      have : κ ≤ κ * u2P ε T := le_mul_of_one_le_right hκ hu2
      linarith
  · -- regular multiplier
    apply dual_le DY hN yh d I ρ ε hε L M (β1 / α) (β2 / α) (by positivity) (by positivity)
    intro T y
    have := hpure T y
    have e : β1 / α * u1P DY yh d I ρ T y + β2 / α * u2P ε T =
        (β1 * u1P DY yh d I ρ T y + β2 * u2P ε T) / α := by
      field_simp
    rw [e, le_div_iff₀ hαpos]
    linarith

end CondPortOTFDAux

open CondPortOTFDAux in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (γ : ℝ) (hγ : 0 < γ) (hA : CondPortOT.BigRadius.Assumption24 DX DY x0 γ xh)
    (hH2 : CondPortOT.BigRadius.BoundaryRegular DX x0 γ xh)
    (ε : ℝ) (hε : 0 < ε) (ρ : ℝ) (hρ : CondPortOT.SingDual.rhoMin DX DY xh yh x0 γ ε < ENNReal.ofReal ρ)
    (L : Y → ℝ) (hL : Measurable L) :
    CondPortOT.SingDual.worstCaseGe DX DY xh yh x0 γ ρ ε L =
      ⨅ (v : CondPortOT.FiberDual.DualPt N) (_ : CondPortOT.FiberDual.InV (CondPortOT.BigRadius.bdDist DX x0 γ xh) (CondPortOT.BigRadius.I1 DX x0 γ xh) ρ v ∧
          ∀ i, (⨆ y, ((L y - v.lam i * DY y (yh i) : ℝ) : EReal)) ≤ (v.s i : EReal)),
        ((v.phi + ((N : ℝ) * ε)⁻¹ * v.nuP - (N : ℝ)⁻¹ * v.nuM : ℝ) : EReal) := by
  classical
  rw [CondPortOT.FiberDual.reduction DX DY hN xh yh x0 γ hγ hA hH2 ε hε ρ hρ L hL]
  have hDYnn := hA.nonnegY
  have hDXnn := hA.nonnegX
  have hDXself : ∀ x, DX x x = 0 := fun x => by
    have h := (hA.eq_zero_iff x x (yh ⟨0, hN⟩) (yh ⟨0, hN⟩)).2 rfl
    linarith [hDXnn x x, hDYnn (yh ⟨0, hN⟩) (yh ⟨0, hN⟩)]
  have hDYself : ∀ y, DY y y = 0 := fun y => by
    have h := (hA.eq_zero_iff (xh ⟨0, hN⟩) (xh ⟨0, hN⟩) y y).2 rfl
    linarith [hDXnn (xh ⟨0, hN⟩) (xh ⟨0, hN⟩), hDYnn y y]
  have hDYm : ∀ i, Measurable fun y => DY y (yh i) := fun i =>
    (hA.contY.comp (continuous_id.prodMk continuous_const)).measurable
  set d := CondPortOT.BigRadius.bdDist DX x0 γ xh with hd_def
  set I := CondPortOT.BigRadius.I1 DX x0 γ xh with hI_def
  have hd : ∀ i, 0 ≤ d i := fun i =>
    Real.sInf_nonneg (by rintro _ ⟨x, _, rfl⟩; exact hDXnn _ _)
  -- `ε ≤ 1`, otherwise `ρ_min = ∞`
  have hε1 : ε ≤ 1 := by
    by_contra h
    push Not at h
    have htop : CondPortOT.SingDual.rhoMin DX DY xh yh x0 γ ε = ⊤ := by
      unfold CondPortOT.SingDual.rhoMin
      refine iInf₂_eq_top.2 fun Q hQ => ?_
      exfalso
      obtain ⟨hQp, hQF⟩ := hQ
      have h1 : Q (CondPortOT.SingUninf.fiber DX x0 γ) ≤ 1 := prob_le_one
      have h2 : (1 : ENNReal) < ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 h
      exact absurd (lt_of_lt_of_le h2 (le_trans hQF h1)) (lt_irrefl _)
    rw [htop] at hρ
    exact not_top_lt hρ
  -- Proposition 2.5: `ρ_min` is the value of the LP (9)
  obtain ⟨⟨v, hvLeast, hrho⟩, -⟩ :=
    CondPortOT.FiberDual.proposition_2_5 DX DY hN xh yh x0 γ hγ.le hA ε hε.le hε1
  rw [hrho] at hρ
  have hvρ : v < ρ := (ENNReal.ofReal_lt_ofReal_iff'.1 hρ).1
  obtain ⟨υ, hυ, hυsum, hv_eq⟩ := hvLeast.1
  set κ := CondPortOT.SingUninf.kappa DX x0 γ xh with hκ_def
  have hκnn : ∀ i, 0 ≤ κ i := fun i =>
    Real.sInf_nonneg (by rintro _ ⟨x, _, rfl⟩; exact hDXnn _ _)
  have hκI : ∀ i ∈ I, κ i = 0 := by
    intro i hi
    have hmem : xh i ∈ CondPortOT.SingUninf.nbhd DX x0 γ := by
      simpa [hI_def, CondPortOT.BigRadius.I1] using hi
    refine le_antisymm ?_ (hκnn i)
    have hin : DX (xh i) (xh i) ∈ (fun x => DX x (xh i)) '' CondPortOT.SingUninf.nbhd DX x0 γ :=
      ⟨xh i, hmem, rfl⟩
    calc κ i ≤ DX (xh i) (xh i) :=
          csInf_le ⟨0, by rintro _ ⟨x, _, rfl⟩; exact hDXnn _ _⟩ hin
      _ = 0 := hDXself _
  have hκIc : ∀ i ∉ I, d i = κ i := fun i hi => hH2.enter_cost i hi
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hv0 : 0 ≤ v := by
    rw [hv_eq]
    exact mul_nonneg (inv_nonneg.2 hNpos.le)
      (Finset.sum_nonneg fun i _ => mul_nonneg (hκnn i) (hυ i).1)
  have hρ0 : 0 ≤ ρ := by linarith
  set ps : Fin N → ℝ := fun i => if i ∈ I then 1 else υ i with hps_def
  have hfeas : ∃ p : Fin N → ℝ, (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) ∧ (N : ℝ) * ε ≤ ∑ i, p i ∧
      ∑ i, eC d I (p i) i < N * ρ := by
    refine ⟨ps, fun i => ?_, ?_, ?_⟩
    · by_cases hi : i ∈ I
      · simp [ps, hi]
      · simp only [ps, if_neg hi]; exact hυ i
    · calc (N : ℝ) * ε ≤ ∑ i, υ i := hυsum
        _ ≤ ∑ i, ps i := Finset.sum_le_sum fun i _ => by
            by_cases hi : i ∈ I
            · simp only [ps, if_pos hi]; exact (hυ i).2
            · simp only [ps, if_neg hi]; exact le_rfl
    · have h1 : ∀ i, eC d I (ps i) i = κ i * υ i := by
        intro i
        unfold eC
        by_cases hi : i ∈ I
        · simp only [ps, if_pos hi, sub_self, zero_mul, hκI i hi]
        · simp only [ps, if_neg hi, hκIc i hi]; ring
      simp_rw [h1]
      have h2 : ∑ i, κ i * υ i = N * v := by rw [hv_eq]; field_simp
      rw [h2]
      exact mul_lt_mul_of_pos_left hvρ hNpos
  have hW : Rval DY yh d I ρ ε L ≤ Dval DY yh d I ρ ε L := by
    unfold Rval Dval
    refine iSup_le fun p => iSup_le fun μ => iSup_le fun hpm => le_iInf fun w => le_iInf
      fun hw => ?_
    exact weak DY hDYnn hN yh hDYm d hd I ρ ε hρ0 hε L hL p μ hpm.1 hpm.2.1 hpm.2.2.1
      hpm.2.2.2 w hw.1 hw.2
  have hS : Dval DY yh d I ρ ε L ≤ Rval DY yh d I ρ ε L :=
    strong DY hDYnn hN yh (fun i => hDYself _) d hd I ρ ε hρ0 hε L hfeas
  exact le_antisymm hW hS
