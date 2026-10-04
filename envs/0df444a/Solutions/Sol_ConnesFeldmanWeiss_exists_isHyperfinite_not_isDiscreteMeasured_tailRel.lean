-- Prove2me | solution 1 for ConnesFeldmanWeiss.exists_isHyperfinite_not_isDiscreteMeasured_tailRel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T23:34:35.183781+00:00
-- url     : https://prove2.me/submissions/f41373b7-45a0-4e86-9fd0-194e87261b77

import Definitions.Def_ConnesFeldmanWeiss
import Theorems.Thm_ConnesFeldmanWeiss_isHyperfinite_tailRel_of_isNonsingular
import Mathlib


section
section
/-!
# A hyperfinite tail relation that is not discrete measured

On `ℝ` with Lebesgue measure, let `T` be a Borel isomorphism of the Cantor set onto `ℝ` on the
Cantor set and the identity elsewhere. Then `T` is non-singular (it agrees with the identity almost
everywhere) and at most two-to-one, so Corollary 13 of Connes–Feldman–Weiss makes its tail relation
hyperfinite in the bundle's sense; but the null Cantor set saturates to all of `ℝ`, so the relation
is not discrete measured on all of `ℝ`.
-/

open MeasureTheory Set
open scoped Pointwise

namespace ConnesFeldmanWeiss.CantorNull

lemma volume_preCantorSet_le (n : ℕ) :
    volume (preCantorSet n) ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ n) := by
  induction n with
  | zero => simp [Real.volume_Icc]
  | succ n ih =>
    rw [preCantorSet_succ]
    have h1 : (fun x : ℝ => x / 3) '' preCantorSet n = (1 / 3 : ℝ) • preCantorSet n := by
      rw [← Set.image_smul]; congr 1; ext x; simp [smul_eq_mul]; ring
    have h2 : (fun x : ℝ => (2 + x) / 3) '' preCantorSet n
        = (2 / 3 : ℝ) +ᵥ (1 / 3 : ℝ) • preCantorSet n := by
      rw [← Set.image_smul, ← Set.image_vadd, Set.image_image]; congr 1; ext x
      simp [smul_eq_mul, vadd_eq_add]; ring
    have hA : volume ((fun x : ℝ => x / 3) '' preCantorSet n)
        = ENNReal.ofReal (1 / 3) * volume (preCantorSet n) := by
      rw [h1, Measure.addHaar_smul]; simp
    have hB : volume ((fun x : ℝ => (2 + x) / 3) '' preCantorSet n)
        = ENNReal.ofReal (1 / 3) * volume (preCantorSet n) := by
      rw [h2, measure_vadd, Measure.addHaar_smul]; simp
    calc volume ((fun x : ℝ => x / 3) '' preCantorSet n ∪
          (fun x : ℝ => (2 + x) / 3) '' preCantorSet n)
        ≤ volume ((fun x : ℝ => x / 3) '' preCantorSet n) +
          volume ((fun x : ℝ => (2 + x) / 3) '' preCantorSet n) := measure_union_le _ _
      _ = ENNReal.ofReal (2 / 3) * volume (preCantorSet n) := by
          rw [hA, hB, ← two_mul, ← mul_assoc]; congr 1
          rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
      _ ≤ ENNReal.ofReal (2 / 3) * ENNReal.ofReal ((2 / 3 : ℝ) ^ n) := by gcongr
      _ = ENNReal.ofReal ((2 / 3 : ℝ) ^ (n + 1)) := by
          rw [← ENNReal.ofReal_mul (by norm_num), pow_succ, mul_comm]

/-- The Cantor set is Lebesgue-null. -/
lemma volume_cantorSet : volume cantorSet = 0 := by
  have ht : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal ((2 / 3 : ℝ) ^ n)) Filter.atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  exact le_antisymm (ge_of_tendsto' ht fun n =>
    (measure_mono (Set.iInter_subset _ n)).trans (volume_preCantorSet_le n)) bot_le

/-- The Cantor set is uncountable. -/
lemma not_countable_cantorSet : ¬ Countable cantorSet := by
  intro h
  let f : (ℕ → Bool) → cantorSet := fun b =>
    ⟨Real.ofDigits (fun i ↦ cond (b i) (2 : Fin 3) 0), ofDigits_bool_to_fin_three_mem_cantorSet b⟩
  have hf : Function.Injective f := by
    intro b c hbc
    have := ofDigits_zero_two_sequence_unique (a := fun i ↦ cond (b i) (2 : Fin 3) 0)
      (b := fun i ↦ cond (c i) (2 : Fin 3) 0) (by intro n; cases b n <;> decide)
      (by intro n; cases c n <;> decide) (congrArg Subtype.val hbc)
    funext i
    have hi := congrFun this i
    cases hb : b i <;> cases hc : c i <;> simp_all
  have hU : Uncountable (ℕ → Bool) := by
    rw [uncountable_iff_forall_not_surjective]
    intro g hg
    obtain ⟨n, hn⟩ := hg (fun n => !(g n n))
    have := congrFun hn n
    cases hgn : g n n <;> simp_all
  exact not_injective_uncountable_countable f hf

instance : StandardBorelSpace cantorSet := isClosed_cantorSet.measurableSet.standardBorel

/-- A Borel isomorphism of the Cantor set onto `ℝ`. -/
noncomputable def e : cantorSet ≃ᵐ ℝ :=
  PolishSpace.measurableEquivOfNotCountable not_countable_cantorSet
    (fun _ => not_countable_cantorSet (Subtype.countable))

open Classical in
/-- `e` on the Cantor set, the identity elsewhere. -/
noncomputable def T (x : ℝ) : ℝ := if hx : x ∈ cantorSet then e ⟨x, hx⟩ else x

lemma measurable_T : Measurable T := by
  classical
  exact Measurable.dite (s := cantorSet) e.measurable measurable_subtype_coe
    isClosed_cantorSet.measurableSet

lemma T_ae_eq_id : ∀ᵐ x ∂volume, T x = x := by
  have : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ cantorSet := measure_eq_zero_iff_ae_notMem.1 volume_cantorSet
  filter_upwards [this] with x hx
  simp [T, hx]

lemma T_symm (y : ℝ) : T (e.symm y) = y := by
  simp [T, (e.symm y).2]

lemma preimage_T_singleton_subset (y : ℝ) : T ⁻¹' {y} ⊆ {y, (e.symm y : ℝ)} := by
  intro x hx
  simp only [mem_preimage, mem_singleton_iff] at hx
  by_cases h : x ∈ cantorSet
  · right
    simp only [T, h, dite_true] at hx
    have : (⟨x, h⟩ : cantorSet) = e.symm y := by rw [← hx, MeasurableEquiv.symm_apply_apply]
    simp [← this]
  · left
    simpa [T, h] using hx

lemma isNonsingular_T : IsNonsingular volume T := by
  refine ⟨measurable_T, fun A hA => ?_⟩
  have : T ⁻¹' A =ᵐ[volume] A := by
    filter_upwards [T_ae_eq_id] with x hx
    change (T x ∈ A) = (x ∈ A)
    rw [hx]
  rw [measure_congr this]

lemma not_isDiscreteMeasured_tailRel :
    ¬ IsDiscreteMeasured volume {p : ℝ × ℝ | ∃ n m : ℕ, T^[n] p.1 = T^[m] p.2} := by
  intro h
  have h0 := h.quasiInvariant cantorSet isClosed_cantorSet.measurableSet volume_cantorSet
  have huniv : saturation {p : ℝ × ℝ | ∃ n m : ℕ, T^[n] p.1 = T^[m] p.2} cantorSet = univ := by
    refine eq_univ_of_forall fun x => ⟨e.symm x, (e.symm x).2, 0, 1, ?_⟩
    simp [T_symm]
  rw [huniv, Real.volume_univ] at h0
  exact ENNReal.top_ne_zero h0

end ConnesFeldmanWeiss.CantorNull

namespace ConnesFeldmanWeiss

open CantorNull in
theorem exists_isHyperfinite_not_isDiscreteMeasured_tailRel :
    ∃ T : ℝ → ℝ, IsNonsingular MeasureTheory.volume T ∧ (∀ᵐ x ∂MeasureTheory.volume, T x = x) ∧
      (∀ y, (T ⁻¹' {y}).Finite) ∧
      IsHyperfinite MeasureTheory.volume {p : ℝ × ℝ | ∃ n m : ℕ, T^[n] p.1 = T^[m] p.2} ∧
      ¬ IsDiscreteMeasured MeasureTheory.volume {p : ℝ × ℝ | ∃ n m : ℕ, T^[n] p.1 = T^[m] p.2} :=
  ⟨CantorNull.T, isNonsingular_T, T_ae_eq_id,
    fun y => (Set.toFinite {y, (e.symm y : ℝ)}).subset (preimage_T_singleton_subset y),
    isHyperfinite_tailRel_of_isNonsingular volume CantorNull.T isNonsingular_T
      (Filter.Eventually.of_forall fun y =>
        ((Set.toFinite {y, (e.symm y : ℝ)}).subset (preimage_T_singleton_subset y)).countable),
    not_isDiscreteMeasured_tailRel⟩

end ConnesFeldmanWeiss

end
end

section
open ConnesFeldmanWeiss

theorem solution :
    ∃ T : ℝ → ℝ, IsNonsingular MeasureTheory.volume T ∧ (∀ᵐ x ∂MeasureTheory.volume, T x = x) ∧
      (∀ y, (T ⁻¹' {y}).Finite) ∧
      IsHyperfinite MeasureTheory.volume {p : ℝ × ℝ | ∃ n m : ℕ, T^[n] p.1 = T^[m] p.2} ∧
      ¬ IsDiscreteMeasured MeasureTheory.volume {p : ℝ × ℝ | ∃ n m : ℕ, T^[n] p.1 = T^[m] p.2} := by
  apply ConnesFeldmanWeiss.exists_isHyperfinite_not_isDiscreteMeasured_tailRel <;> assumption

end
