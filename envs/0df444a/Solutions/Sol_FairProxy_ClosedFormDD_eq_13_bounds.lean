-- Prove2me | solution 1 for FairProxy.ClosedFormDD.eq_13_bounds
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T22:19:29.257404+00:00
-- url     : https://prove2.me/submissions/70e0f787-0a87-416d-8f92-4af99bc572d0

import Mathlib
import Definitions.Def_FairProxy_ClosedFormDD_Model

open FairProxy.ClosedFormDD

namespace Prove2FairProxySubmission

namespace FairProxy.ClosedFormDD.Lead34Eq13

open MeasureTheory

/-- The primary decision marginal `etaPri M ŷ` is measurable. -/
theorem measurable_etaPri {Z : Type*} [MeasurableSpace Z] (M : Marginals Z) (hM : M.Valid)
    (ŷ : Fin 2) : Measurable (etaPri M ŷ) :=
  Finset.measurable_sum _ fun y _ => hM.2.2.1 ŷ y

theorem etaPri_nonneg {Z : Type*} [MeasurableSpace Z] (M : Marginals Z) (hM : M.Valid)
    (ŷ : Fin 2) (z : Z) : 0 ≤ etaPri M ŷ z :=
  Finset.sum_nonneg fun y _ => hM.2.2.2.2.2.1 ŷ y z

theorem etaPri_le_one {Z : Type*} [MeasurableSpace Z] (M : Marginals Z) (hM : M.Valid)
    (ŷ : Fin 2) (z : Z) : etaPri M ŷ z ≤ 1 :=
  (Finset.single_le_sum (f := fun ŷ' => etaPri M ŷ' z) (fun ŷ' _ => etaPri_nonneg M hM ŷ' z)
    (Finset.mem_univ ŷ)).trans_eq (hM.2.2.2.2.2.2 z)

theorem measurable_wL {Z : Type*} [MeasurableSpace Z] (M : Marginals Z) (hM : M.Valid)
    (α : Cls) (ŷ : Fin 2) : Measurable (wL M α ŷ) := by
  show Measurable fun z => max 0 (1 + (M.etaAux α z - 1) / etaPri M ŷ z)
  exact measurable_const.max
    ((((hM.2.1 α).sub_const 1).fun_div (measurable_etaPri M hM ŷ)).const_add 1)

theorem measurable_wU {Z : Type*} [MeasurableSpace Z] (M : Marginals Z) (hM : M.Valid)
    (α : Cls) (ŷ : Fin 2) : Measurable (wU M α ŷ) := by
  show Measurable fun z => min 1 (M.etaAux α z / etaPri M ŷ z)
  exact measurable_const.min ((hM.2.1 α).fun_div (measurable_etaPri M hM ŷ))

/-- Fréchet bounds for one cell of a coupling at a fixed proxy value `z`: the mass
`A = ∑ y, π α ŷ y z` satisfies `0 ≤ A`, `A ≤ etaPri`, `A ≤ etaAux` and
`etaPri + etaAux - 1 ≤ A`. -/
theorem cell_bounds {Z : Type*} [MeasurableSpace Z] (M : Marginals Z) (hM : M.Valid)
    {π : Cls → Fin 2 → Fin 2 → Z → ℝ} (hπ : IsInPD M π) (α : Cls) (ŷ : Fin 2) (z : Z) :
    0 ≤ ∑ y, π α ŷ y z ∧ ∑ y, π α ŷ y z ≤ etaPri M ŷ z ∧ ∑ y, π α ŷ y z ≤ M.etaAux α z ∧
      etaPri M ŷ z + M.etaAux α z - 1 ≤ ∑ y, π α ŷ y z := by
  obtain ⟨hc1, hc2, hc3⟩ := hπ.2 z
  have h0 : ∀ α' ŷ' y, 0 ≤ π α' ŷ' y z := fun α' ŷ' y => (hc3 (ŷ', y) α').1
  -- row sums (over the decision) recover the auxiliary marginal
  have hrow : ∀ α', ∑ ŷ', ∑ y, π α' ŷ' y z = M.etaAux α' z := fun α' =>
    (Fintype.sum_prod_type' fun ŷ' y => π α' ŷ' y z).symm.trans (hc2 α')
  -- column sums (over the class) recover the primary marginal
  have hcol : ∀ ŷ', ∑ α', ∑ y, π α' ŷ' y z = etaPri M ŷ' z := fun ŷ' =>
    Finset.sum_comm.trans (Finset.sum_congr rfl fun y _ => hc1 (ŷ', y))
  have hsub : ∀ α', ∑ y, π α' ŷ y z ≤ ∑ ŷ', ∑ y, π α' ŷ' y z := fun α' =>
    Finset.single_le_sum (f := fun ŷ' => ∑ y, π α' ŷ' y z)
      (fun ŷ' _ => Finset.sum_nonneg fun y _ => h0 α' ŷ' y) (Finset.mem_univ ŷ)
  have hR : ∑ ŷ', ∑ y, π α ŷ' y z - ∑ y, π α ŷ y z ≤
      ∑ α', (∑ ŷ', ∑ y, π α' ŷ' y z - ∑ y, π α' ŷ y z) :=
    Finset.single_le_sum (f := fun α' => ∑ ŷ', ∑ y, π α' ŷ' y z - ∑ y, π α' ŷ y z)
      (fun α' _ => sub_nonneg.mpr (hsub α')) (Finset.mem_univ α)
  have e1 : ∑ α', (∑ ŷ', ∑ y, π α' ŷ' y z - ∑ y, π α' ŷ y z) =
      ∑ α', ∑ ŷ', ∑ y, π α' ŷ' y z - ∑ α', ∑ y, π α' ŷ y z :=
    Finset.sum_sub_distrib ..
  have e2 : ∑ α', ∑ ŷ', ∑ y, π α' ŷ' y z = 1 :=
    (Finset.sum_congr rfl fun α' _ => hrow α').trans (hM.2.2.2.2.1 z)
  refine ⟨Finset.sum_nonneg fun y _ => h0 α ŷ y, ?_, (hsub α).trans_eq (hrow α), ?_⟩
  · exact (Finset.single_le_sum (f := fun α' => ∑ y, π α' ŷ y z)
      (fun α' _ => Finset.sum_nonneg fun y _ => h0 α' ŷ y) (Finset.mem_univ α)).trans_eq (hcol ŷ)
  · have e3 := hcol ŷ
    have e4 := hrow α
    linarith

/-- Pointwise sandwich `0 ≤ wL·etaPri ≤ w·etaPri ≤ wU·etaPri ≤ 1` for a weight induced by a
coupling; every product vanishes on an empty decision cell. -/
theorem weight_bounds {Z : Type*} [MeasurableSpace Z] (M : Marginals Z) (hM : M.Valid)
    {π : Cls → Fin 2 → Fin 2 → Z → ℝ} (hπ : IsInPD M π) (w : Cls → Fin 2 → Z → ℝ)
    (hwπ : ∀ α ŷ z, 0 < etaPri M ŷ z → w α ŷ z = (∑ y, π α ŷ y z) / etaPri M ŷ z)
    (α : Cls) (ŷ : Fin 2) (z : Z) :
    0 ≤ wL M α ŷ z * etaPri M ŷ z ∧ wL M α ŷ z * etaPri M ŷ z ≤ w α ŷ z * etaPri M ŷ z ∧
      w α ŷ z * etaPri M ŷ z ≤ wU M α ŷ z * etaPri M ŷ z ∧ wU M α ŷ z * etaPri M ŷ z ≤ 1 := by
  obtain ⟨hA0, hAe, hAaux, hlow⟩ := cell_bounds M hM hπ α ŷ z
  rcases (etaPri_nonneg M hM ŷ z).lt_or_eq with he | he
  · have hw : w α ŷ z = (∑ y, π α ŷ y z) / etaPri M ŷ z := hwπ α ŷ z he
    have hLw : wL M α ŷ z ≤ w α ŷ z := by
      rw [hw]
      refine max_le (div_nonneg hA0 he.le) ?_
      rw [le_div_iff₀ he, add_mul, one_mul, div_mul_cancel₀ _ he.ne']
      linarith
    have hwU : w α ŷ z ≤ wU M α ŷ z := by
      rw [hw]
      exact le_min ((div_le_one he).mpr hAe) (div_le_div_of_nonneg_right hAaux he.le)
    refine ⟨mul_nonneg (le_max_left _ _) he.le, mul_le_mul_of_nonneg_right hLw he.le,
      mul_le_mul_of_nonneg_right hwU he.le, ?_⟩
    calc wU M α ŷ z * etaPri M ŷ z ≤ 1 * etaPri M ŷ z :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) he.le
      _ = etaPri M ŷ z := one_mul _
      _ ≤ 1 := etaPri_le_one M hM ŷ z
  · have hz : ∀ x : ℝ, x * etaPri M ŷ z = 0 := fun x => by rw [← he, mul_zero]
    rw [hz, hz, hz]
    exact ⟨le_rfl, le_rfl, le_rfl, zero_le_one⟩

/-- The integrand of `mu M α g` is integrable once `g α ŷ` is measurable and
`0 ≤ g α ŷ z * etaPri M ŷ z ≤ 1`. -/
theorem integrable_weighted {Z : Type*} [MeasurableSpace Z] (M : Marginals Z) (hM : M.Valid)
    (g : Cls → Fin 2 → Z → ℝ) (α : Cls) (hg : ∀ ŷ, Measurable (g α ŷ))
    (h0 : ∀ ŷ z, 0 ≤ g α ŷ z * etaPri M ŷ z) (h1 : ∀ ŷ z, g α ŷ z * etaPri M ŷ z ≤ 1) :
    Integrable (fun z => ∑ ŷ : Fin 2, g α ŷ z * ((ŷ : ℕ) : ℝ) * etaPri M ŷ z) M.PZ := by
  have hP : IsProbabilityMeasure M.PZ := hM.1
  have hmeas : Measurable fun z => ∑ ŷ : Fin 2, g α ŷ z * ((ŷ : ℕ) : ℝ) * etaPri M ŷ z :=
    Finset.measurable_sum _ fun ŷ _ => ((hg ŷ).mul_const _).fun_mul (measurable_etaPri M hM ŷ)
  have hbd : ∀ z, ‖∑ ŷ : Fin 2, g α ŷ z * ((ŷ : ℕ) : ℝ) * etaPri M ŷ z‖ ≤
      ∑ _ : Fin 2, (1 : ℝ) := by
    intro z
    have ht0 : ∀ ŷ : Fin 2, 0 ≤ g α ŷ z * ((ŷ : ℕ) : ℝ) * etaPri M ŷ z := fun ŷ => by
      rw [mul_right_comm (g α ŷ z)]
      exact mul_nonneg (h0 ŷ z) (Nat.cast_nonneg _)
    have ht1 : ∀ ŷ : Fin 2, g α ŷ z * ((ŷ : ℕ) : ℝ) * etaPri M ŷ z ≤ 1 := fun ŷ => by
      rw [mul_right_comm (g α ŷ z)]
      exact mul_le_one₀ (h1 ŷ z) (Nat.cast_nonneg _) (Nat.cast_le_one.mpr ŷ.is_le)
    have hS0 : 0 ≤ ∑ ŷ : Fin 2, g α ŷ z * ((ŷ : ℕ) : ℝ) * etaPri M ŷ z :=
      Finset.sum_nonneg fun ŷ _ => ht0 ŷ
    rw [Real.norm_eq_abs, abs_of_nonneg hS0]
    exact Finset.sum_le_sum fun ŷ _ => ht1 ŷ
  exact Integrable.of_bound hmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hbd)

/-- `mu M α` is monotone in the weight wherever the integrands are integrable and the weighted
primary marginals are ordered pointwise. -/
theorem mu_mono {Z : Type*} [MeasurableSpace Z] (M : Marginals Z) {α : Cls}
    (hα : 0 < probA M α) {f g : Cls → Fin 2 → Z → ℝ}
    (hf : Integrable (fun z => ∑ ŷ : Fin 2, f α ŷ z * ((ŷ : ℕ) : ℝ) * etaPri M ŷ z) M.PZ)
    (hg : Integrable (fun z => ∑ ŷ : Fin 2, g α ŷ z * ((ŷ : ℕ) : ℝ) * etaPri M ŷ z) M.PZ)
    (hfg : ∀ ŷ z, f α ŷ z * etaPri M ŷ z ≤ g α ŷ z * etaPri M ŷ z) :
    mu M α f ≤ mu M α g := by
  refine div_le_div_of_nonneg_right (integral_mono hf hg fun z => ?_) hα.le
  refine Finset.sum_le_sum fun ŷ _ => ?_
  rw [mul_right_comm (f α ŷ z), mul_right_comm (g α ŷ z)]
  exact mul_le_mul_of_nonneg_right (hfg ŷ z) (Nat.cast_nonneg _)

/-- For one class `α` with positive mass: `mu α wL ≤ mu α w ≤ mu α wU`. -/
theorem mu_sandwich {Z : Type*} [MeasurableSpace Z] (M : Marginals Z) (hM : M.Valid)
    (w : Cls → Fin 2 → Z → ℝ) (hw : w ∈ WPD M) (α : Cls) (hα : 0 < probA M α) :
    mu M α (wL M) ≤ mu M α w ∧ mu M α w ≤ mu M α (wU M) := by
  obtain ⟨hwm, π, hπ, hwπ⟩ := hw
  have hb := weight_bounds M hM hπ w hwπ α
  have iL := integrable_weighted M hM (wL M) α (measurable_wL M hM α) (fun ŷ z => (hb ŷ z).1)
    (fun ŷ z => ((hb ŷ z).2.1.trans (hb ŷ z).2.2.1).trans (hb ŷ z).2.2.2)
  have iw := integrable_weighted M hM w α (hwm α) (fun ŷ z => (hb ŷ z).1.trans (hb ŷ z).2.1)
    (fun ŷ z => (hb ŷ z).2.2.1.trans (hb ŷ z).2.2.2)
  have iU := integrable_weighted M hM (wU M) α (measurable_wU M hM α)
    (fun ŷ z => ((hb ŷ z).1.trans (hb ŷ z).2.1).trans (hb ŷ z).2.2.1) (fun ŷ z => (hb ŷ z).2.2.2)
  exact ⟨mu_mono M hα iL iw fun ŷ z => (hb ŷ z).2.1, mu_mono M hα iw iU fun ŷ z => (hb ŷ z).2.2.1⟩

end FairProxy.ClosedFormDD.Lead34Eq13

namespace FairProxy.ClosedFormDD

/-- The lower bound in the proof of Proposition 7, p. 15, after equation (13),
and its stated analogous upper bound. -/
theorem eq_13_bounds {Z : Type*} [MeasurableSpace Z]
    (M : Marginals Z) (hM : M.Valid)
    (ha : 0 < probA M .a) (hb : 0 < probA M .b)
    (w : Cls → Fin 2 → Z → ℝ) (hw : w ∈ WPD M) :
    mu M .a (wL M) - mu M .b (wU M) ≤ mu M .a w - mu M .b w ∧
      mu M .a w - mu M .b w ≤
        mu M .a (wU M) - mu M .b (wL M) := by
  obtain ⟨hLa, hUa⟩ := Lead34Eq13.mu_sandwich M hM w hw .a ha
  obtain ⟨hLb, hUb⟩ := Lead34Eq13.mu_sandwich M hM w hw .b hb
  exact ⟨sub_le_sub hLa hUb, sub_le_sub hUa hLb⟩

end FairProxy.ClosedFormDD

end Prove2FairProxySubmission

theorem solution {Z : Type*} [MeasurableSpace Z]
    (M : Marginals Z) (hM : M.Valid)
    (ha : 0 < probA M .a) (hb : 0 < probA M .b)
    (w : Cls → Fin 2 → Z → ℝ) (hw : w ∈ WPD M) :
    mu M .a (wL M) - mu M .b (wU M) ≤ mu M .a w - mu M .b w ∧
      mu M .a w - mu M .b w ≤
        mu M .a (wU M) - mu M .b (wL M) := by
  exact _root_.Prove2FairProxySubmission.FairProxy.ClosedFormDD.eq_13_bounds M hM ha hb w hw
