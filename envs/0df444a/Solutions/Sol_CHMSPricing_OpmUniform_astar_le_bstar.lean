-- Prove2me | solution 1 for CHMSPricing.OpmUniform.astar_le_bstar
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:30:11.265583+00:00
-- url     : https://prove2.me/submissions/c5ae9821-374b-44ce-9ea2-27900d06bd62

import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_Prophet

set_option autoImplicit false

namespace CHMSPricing.OpmUniform.P32e2c604

open MeasureTheory

lemma sum_range_getD (φ : ℝ → ℝ) (L : List ℝ) :
    ∑ i ∈ Finset.range L.length, φ (L.getD i 0) = (L.map φ).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← ih]
    simp [add_comm]

lemma topk_le {n k : ℕ} (hkn : k ≤ n) (x : Fin n → ℝ) (φ : ℝ → ℝ) (hφ : ∀ y, 0 ≤ φ y) :
    ∑ i : Fin k, φ (orderStat x i) ≤ ∑ j, φ (x j) := by
  set L := (Finset.univ.val.map x).sort (fun a b => b ≤ a) with hL
  have hlen : L.length = n := by
    rw [hL, Multiset.length_sort]; simp
  have h1 : ∀ i : ℕ, orderStat x i = L.getD i 0 := fun i => rfl
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun i => φ (L.getD i 0))]
  calc ∑ i ∈ Finset.range k, φ (L.getD i 0)
      ≤ ∑ i ∈ Finset.range L.length, φ (L.getD i 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi; simp at hi ⊢; omega
        · intro i _ _; exact hφ _
    _ = (L.map φ).sum := sum_range_getD φ L
    _ = ∑ j, φ (x j) := by
        have : ((L : Multiset ℝ).map φ).sum = (L.map φ).sum := by simp
        rw [← this, hL, Multiset.sort_eq]
        simp [Finset.sum_eq_multiset_sum]
        rfl

lemma ofReal_integral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (h : Ω → ℝ)
    (hnn : ∀ ω, 0 ≤ h ω) :
    ENNReal.ofReal (∫ ω, h ω ∂P) ≤ ∫⁻ ω, ENNReal.ofReal (h ω) ∂P := by
  by_cases hi : Integrable h P
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn)]
  · rw [integral_undef hi]; simp

lemma sum_lintegral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*}
    (s : Finset ι) (f : ι → Ω → ENNReal) :
    ∑ i ∈ s, ∫⁻ ω, f i ω ∂P ≤ ∫⁻ ω, ∑ i ∈ s, f i ω ∂P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp_rw [Finset.sum_insert ha]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

lemma sum_integral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m : ℕ}
    (h : Fin m → Ω → ℝ) (hnn : ∀ i ω, 0 ≤ h i ω) (G : Ω → ℝ) (hG : Integrable G P)
    (hGnn : ∀ ω, 0 ≤ G ω) (hle : ∀ ω, ∑ i, h i ω ≤ G ω) :
    ∑ i, ∫ ω, h i ω ∂P ≤ ∫ ω, G ω ∂P := by
  have hs : 0 ≤ ∑ i, ∫ ω, h i ω ∂P :=
    Finset.sum_nonneg fun i _ => integral_nonneg (hnn i)
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg hGnn),
    ofReal_integral_eq_lintegral_ofReal hG (Filter.Eventually.of_forall hGnn),
    ENNReal.ofReal_sum_of_nonneg fun i _ => integral_nonneg (hnn i)]
  calc ∑ i, ENNReal.ofReal (∫ ω, h i ω ∂P)
      ≤ ∑ i, ∫⁻ ω, ENNReal.ofReal (h i ω) ∂P :=
        Finset.sum_le_sum fun i _ => ofReal_integral_le (h i) (hnn i)
    _ ≤ ∫⁻ ω, ∑ i, ENNReal.ofReal (h i ω) ∂P := sum_lintegral_le _ _
    _ ≤ ∫⁻ ω, ENNReal.ofReal (G ω) ∂P := by
        apply lintegral_mono
        intro ω
        show ∑ i, ENNReal.ofReal (h i ω) ≤ ENNReal.ofReal (G ω)
        rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hnn i ω]
        exact ENNReal.ofReal_le_ofReal (hle ω)

lemma integrable_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (f : Ω → ℝ) (hf : Integrable f P) (c : ℝ) :
    Integrable (fun ω => max 0 (f ω - c)) P :=
  (integrable_const 0).sup (hf.sub (integrable_const c))

end CHMSPricing.OpmUniform.P32e2c604

open MeasureTheory ProbabilityTheory CHMSPricing.OpmUniform in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω)
    (hXint : ∀ i, Integrable (X i) P) (a b : ℝ)
    (ha : a = ∑ i : Fin k, ∫ ω, max 0 (orderStat (fun j => X j ω) i - a / k) ∂P)
    (hb : b = ∑ i, ∫ ω, max 0 (X i ω - b / k) ∂P) :
    a ≤ b := by
  by_contra hab
  push Not at hab
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  -- a ≤ g(a)
  have h1 : a ≤ ∑ i, ∫ ω, max 0 (X i ω - a / k) ∂P := by
    rw [← integral_finsetSum _ (fun i _ => P32e2c604.integrable_pos _ (hXint i) _)]
    conv_lhs => rw [ha]
    refine P32e2c604.sum_integral_le (fun i ω => max 0 (orderStat (fun j => X j ω) i - a / k))
      (fun _ _ => le_max_left _ _) _
      (integrable_finsetSum _ (fun i _ => P32e2c604.integrable_pos _ (hXint i) _))
      (fun ω => Finset.sum_nonneg fun _ _ => le_max_left _ _) ?_
    intro ω
    exact P32e2c604.topk_le hkn (fun j => X j ω) (fun y => max 0 (y - a / k)) (fun _ => le_max_left _ _)
  -- g(a) ≤ g(b)
  have h2 : ∑ i, ∫ ω, max 0 (X i ω - a / k) ∂P ≤ ∑ i, ∫ ω, max 0 (X i ω - b / k) ∂P := by
    apply Finset.sum_le_sum
    intro i _
    apply integral_mono (P32e2c604.integrable_pos _ (hXint i) _) (P32e2c604.integrable_pos _ (hXint i) _)
    intro ω
    have : b / k ≤ a / k := div_le_div_of_nonneg_right hab.le hkpos.le
    exact max_le_max le_rfl (by linarith)
  linarith
