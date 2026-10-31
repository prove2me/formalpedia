-- Prove2me | solution 1 for FoundationsML.Regression.pseudo_dimension_regression_bound_v2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-30T21:49:08.920524+00:00
-- url     : https://prove2.me/submissions/fb01ef39-0818-4994-bef8-e4dba56c6c25

import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_FoundationsML_Regression_GeneralizationError
import Definitions.Def_FoundationsML_Regression_EmpiricalError
import Definitions.Def_FoundationsML_Regression_LossComposedFamily
import Definitions.Def_FoundationsML_Regression_PseudoDim

open MeasureTheory

set_option autoImplicit false

namespace Cex439d

open Cardinal Set

/-- A subset of `[0,1]` of positive outer measure whose every subset of smaller cardinality is
Lebesgue-null (take one of least cardinality). -/
theorem exists_minA : ∃ A : Set ℝ, A ⊆ Icc 0 1 ∧ volume A ≠ 0 ∧
    ∀ B ⊆ A, #B < #A → volume B = 0 := by
  let Q : Set Cardinal.{0} := {κ | ∃ A : Set ℝ, A ⊆ Icc 0 1 ∧ volume A ≠ 0 ∧ #A = κ}
  have hQ : Q.Nonempty := ⟨_, Icc 0 1, subset_rfl, by simp, rfl⟩
  obtain ⟨κ, ⟨A, hA1, hA2, rfl⟩, hmin⟩ := wellFounded_lt.has_min Q hQ
  refine ⟨A, hA1, hA2, fun B hB hlt => ?_⟩
  by_contra h
  exact hmin _ ⟨B, hB.trans hA1, h, rfl⟩ hlt

noncomputable def A : Set ℝ := Classical.choose exists_minA

theorem A_sub : A ⊆ Icc 0 1 := (Classical.choose_spec exists_minA).1
theorem A_pos : volume A ≠ 0 := (Classical.choose_spec exists_minA).2.1
theorem A_min : ∀ B ⊆ A, #B < #A → volume B = 0 := (Classical.choose_spec exists_minA).2.2

theorem A_fin : volume A ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (measure_mono A_sub)

theorem A_inf : ℵ₀ ≤ #A := by
  rw [Cardinal.aleph0_le_mk_iff, Set.infinite_coe_iff]
  intro hfin
  exact A_pos (hfin.measure_zero volume)

/-- The sample space: the initial well-order of cardinality `#A`. -/
abbrev X : Type := (#A).ord.ToType

theorem mk_X : #X = #A := Cardinal.mk_ord_toType _

noncomputable def e0 : X ≃ A := Classical.choice (Cardinal.eq.1 mk_X)

noncomputable def e (x : X) : ℝ := (e0 x : ℝ)

theorem e_range : range e = A := by
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    exact (e0 x).2
  · intro hr
    exact ⟨e0.symm ⟨r, hr⟩, by simp [e]⟩

theorem mk_Iio_lt' (z : X) : #(Iio z) < #A := by
  simpa using Cardinal.mk_Iio_lt (α := (#A).ord.ToType) z (by simp)

/-- The outer measure pulled back from Lebesgue outer measure along `e`. -/
noncomputable def ν : OuterMeasure X := OuterMeasure.comap e (volume : Measure ℝ).toOuterMeasure

theorem ν_apply (s : Set X) : ν s = volume (e '' s) := by
  simp [ν, OuterMeasure.comap_apply]

noncomputable instance instMS : MeasurableSpace X := ν.caratheodory

theorem meas_of_null {s : Set X} (hs : ν s = 0) : MeasurableSet s := by
  rw [OuterMeasure.isCaratheodory_iff_le]
  intro t
  have h1 : ν (t ∩ s) = 0 := le_antisymm (hs ▸ measure_mono inter_subset_right) bot_le
  rw [h1, zero_add]
  exact measure_mono diff_subset

theorem ν_Iio (z : X) : ν (Iio z) = 0 := by
  rw [ν_apply]
  apply A_min
  · rintro r ⟨x, _, rfl⟩; exact (e0 x).2
  · exact (Cardinal.mk_image_le).trans_lt (mk_Iio_lt' z)

theorem meas_Iio (z : X) : MeasurableSet (Iio z) := meas_of_null (ν_Iio z)

theorem exists_gt (z : X) : ∃ a : X, z < a := by
  by_contra h
  push_neg at h
  have hsub : (univ : Set X) ⊆ insert z (Iio z) := by
    intro x _
    rcases (h x).lt_or_eq with hx | hx
    · exact Or.inr hx
    · exact Or.inl hx
  have h1 : #(univ : Set X) ≤ #(Iio z) + 1 :=
    (Cardinal.mk_le_mk_of_subset hsub).trans (Cardinal.mk_insert_le)
  have h2 : #(Iio z) + 1 < #A :=
    Cardinal.add_lt_of_lt A_inf (mk_Iio_lt' z) (Cardinal.one_lt_aleph0.trans_le A_inf)
  rw [Cardinal.mk_univ, mk_X] at h1
  exact lt_irrefl _ (h1.trans_lt h2)

noncomputable instance : Nonempty X := by
  have hne : A.Nonempty := nonempty_of_measure_ne_zero A_pos
  exact ⟨e0.symm ⟨hne.some, hne.some_mem⟩⟩

noncomputable def P0 : Measure X := ν.toMeasure le_rfl

theorem P0_univ : P0 univ = volume A := by
  rw [P0, toMeasure_apply _ _ MeasurableSet.univ, ν_apply, image_univ, e_range]

theorem P0_Iio (z : X) : P0 (Iio z) = 0 := by
  rw [P0, toMeasure_apply _ _ (meas_Iio z), ν_Iio]

noncomputable def P : Measure X := (volume A)⁻¹ • P0

instance P_prob : IsProbabilityMeasure P := by
  constructor
  rw [P, Measure.smul_apply, P0_univ, smul_eq_mul, ENNReal.inv_mul_cancel A_pos A_fin]

theorem P_Iio (z : X) : P (Iio z) = 0 := by
  rw [P, Measure.smul_apply, P0_Iio, smul_zero]

/-- The labelled distribution: `x ∼ P`, label `0`. -/
noncomputable def D : Measure (X × ℝ) := P.map (fun x => (x, (0 : ℝ)))

theorem f_meas : Measurable (fun x : X => (x, (0 : ℝ))) := measurable_id.prodMk measurable_const

instance D_prob : IsProbabilityMeasure D := Measure.isProbabilityMeasure_map f_meas.aemeasurable

/-- Threshold hypotheses. -/
noncomputable def th (a : X) : X → ℝ := fun x => if a ≤ x then 1 else 0

def H : Set (X → ℝ) := range th

noncomputable def L : ℝ → ℝ → ℝ := fun t _ => min |t| 1

theorem th_meas (a : X) : Measurable (th a) := by
  have hs : MeasurableSet {x : X | a ≤ x} := by
    have : {x : X | a ≤ x} = (Iio a)ᶜ := by ext x; simp
    rw [this]; exact (meas_Iio a).compl
  exact Measurable.ite hs measurable_const measurable_const

theorem L_th (a : X) (x : X) (y : ℝ) : L (th a x) y = th a x := by
  by_cases h : a ≤ x <;> simp [L, th, h]

theorem th_antitone {a₁ a₂ : X} (h : a₁ ≤ a₂) (x : X) : th a₂ x ≤ th a₁ x := by
  by_cases h2 : a₂ ≤ x
  · have h1 : a₁ ≤ x := h.trans h2
    simp [th, h1, h2]
  · by_cases h1 : a₁ ≤ x <;> simp [th, h1, h2]

theorem genErr (a : X) : FoundationsML.Regression.GeneralizationError D L (th a) = 1 := by
  have hset : MeasurableSet {p : X × ℝ | a ≤ p.1} := by
    have : {p : X × ℝ | a ≤ p.1} = Prod.fst ⁻¹' (Iio a)ᶜ := by ext p; simp
    rw [this]; exact measurable_fst (meas_Iio a).compl
  have hae : ∀ᵐ p ∂D, a ≤ p.1 := by
    rw [D, ae_map_iff f_meas.aemeasurable hset]
    rw [ae_iff]
    have : {x : X | ¬ a ≤ x} = Iio a := by ext x; simp
    simp only [this]
    exact P_Iio a
  unfold FoundationsML.Regression.GeneralizationError
  rw [integral_congr_ae (g := fun _ => (1 : ℝ))]
  · simp
  · filter_upwards [hae] with p hp
    simp [L, th, hp]

theorem pdim_one :
    FoundationsML.Regression.PseudoDim (FoundationsML.Regression.LossComposedFamily L H) 1 := by
  refine ⟨?_, ?_⟩
  · let x0 : X := Classical.arbitrary X
    refine ⟨fun _ => (x0, 0), fun _ => (1 / 2 : ℝ), fun b => ?_⟩
    cases hb : b 0
    · obtain ⟨a, ha⟩ := exists_gt x0
      refine ⟨fun p => L (th a p.1) p.2, ⟨th a, ⟨a, rfl⟩, rfl⟩, fun i => ?_⟩
      rw [Fin.eq_zero i, hb]
      simp [L, th, not_le.2 ha]
    · refine ⟨fun p => L (th x0 p.1) p.2, ⟨th x0, ⟨x0, rfl⟩, rfl⟩, fun i => ?_⟩
      rw [Fin.eq_zero i, hb]
      simp [L, th]
      norm_num
  · intro m ⟨z, t, hsh⟩
    by_contra hlt
    have hm2 : 2 ≤ m := by omega
    let i0 : Fin m := ⟨0, by omega⟩
    let i1 : Fin m := ⟨1, by omega⟩
    have h01_ne : i0 ≠ i1 := by
      intro h; have := congrArg Fin.val h; dsimp [i0, i1] at this; omega
    obtain ⟨g1, ⟨_, ⟨a1, rfl⟩, rfl⟩, hg1⟩ := hsh (fun i => decide (i = i0))
    obtain ⟨g2, ⟨_, ⟨a2, rfl⟩, rfl⟩, hg2⟩ := hsh (fun i => decide (i = i1))
    have h10 : t i0 < th a1 (z i0).1 := by
      have := (hg1 i0).mp (by simp)
      simpa [L_th] using this
    have h11 : th a1 (z i1).1 ≤ t i1 := by
      have hfalse : ¬ (decide (i1 = i0) = true) := by simp [h01_ne.symm]
      have := mt (hg1 i1).mpr hfalse
      linarith [L_th a1 (z i1).1 (z i1).2]
    have h20 : th a2 (z i0).1 ≤ t i0 := by
      have hfalse : ¬ (decide (i0 = i1) = true) := by simp [h01_ne]
      have := mt (hg2 i0).mpr hfalse
      linarith [L_th a2 (z i0).1 (z i0).2]
    have h21 : t i1 < th a2 (z i1).1 := by
      have := (hg2 i1).mp (by simp)
      simpa [L_th] using this
    rcases le_total a1 a2 with hle | hle
    · have := th_antitone hle (z i1).1
      linarith
    · have := th_antitone hle (z i0).1
      linarith

theorem log_two_le : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem vc_term_small :
    Real.sqrt (2 * (1 : ℕ) * Real.log (Real.exp 1 * (64 : ℕ) / (1 : ℕ)) / (64 : ℕ)) < 1 / 2 := by
  rw [Real.sqrt_lt' (by norm_num)]
  push_cast
  have hexp : Real.exp 1 * 64 / 1 = Real.exp 1 * (2 : ℝ) ^ (6 : ℕ) := by ring
  rw [hexp, Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow]
  have h2 := log_two_le
  push_cast
  linarith

theorem delta_term_small :
    Real.sqrt (Real.log (1 / (9 / 10 : ℝ)) / (2 * (64 : ℕ))) < 1 / 4 := by
  rw [Real.sqrt_lt' (by norm_num)]
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (9 / 10) by norm_num)
  push_cast
  norm_num at h ⊢
  linarith

theorem event_empty :
    {S : Fin 64 → X × ℝ | ∀ h ∈ H,
      FoundationsML.Regression.GeneralizationError D L h ≤
        FoundationsML.Regression.EmpiricalError S L h +
          1 * Real.sqrt (2 * (1 : ℕ) * Real.log (Real.exp 1 * (64 : ℕ) / (1 : ℕ)) / (64 : ℕ)) +
          1 * Real.sqrt (Real.log (1 / (9 / 10 : ℝ)) / (2 * (64 : ℕ)))} = ∅ := by
  ext S
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall]
  let M : X := Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 64 => (S i).1)
  obtain ⟨a, ha⟩ := exists_gt M
  refine ⟨th a, ⟨a, rfl⟩, ?_⟩
  have hE : FoundationsML.Regression.EmpiricalError S L (th a) = 0 := by
    unfold FoundationsML.Regression.EmpiricalError
    have hsum : (∑ i : Fin 64, L (th a (S i).1) (S i).2) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hi : (S i).1 ≤ M := Finset.le_sup' (fun j : Fin 64 => (S j).1) (Finset.mem_univ i)
      have hna : ¬ a ≤ (S i).1 := not_le.2 (hi.trans_lt ha)
      simp [L, th, hna]
    rw [hsum, mul_zero]
  rw [genErr, hE]
  have := vc_term_small
  have := delta_term_small
  linarith

end Cex439d

open FoundationsML.Regression in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hL_meas : Measurable (Function.uncurry L))
    (H : Set (X → ℝ)) (hH_meas : ∀ h ∈ H, Measurable h)
    (d : ℕ) (hPdim : PseudoDim (LossComposedFamily L H) d)
    (m : ℕ) (hm : 0 < m) (hdm : d ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            M * Real.sqrt (2 * d * Real.log (Real.exp 1 * m / d) / m) +
            M * Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal) := by
  intro hall
  have h := hall (X := Cex439d.X) Cex439d.D Cex439d.L 1 one_pos
    (fun _ _ => le_min (abs_nonneg _) zero_le_one) (fun _ _ => min_le_right _ _)
    (by
      show Measurable (fun p : ℝ × ℝ => min |p.1| 1)
      exact (continuous_fst.abs.min continuous_const).measurable)
    Cex439d.H (by rintro _ ⟨a, rfl⟩; exact Cex439d.th_meas a)
    1 Cex439d.pdim_one 64 (by decide) (by decide) (9 / 10) (by norm_num) (by norm_num)
  rw [Cex439d.event_empty, measure_empty, ENNReal.toReal_zero] at h
  norm_num at h
