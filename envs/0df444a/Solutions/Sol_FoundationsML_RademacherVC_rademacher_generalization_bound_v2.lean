-- Prove2me | solution 1 for FoundationsML.RademacherVC.rademacher_generalization_bound_v2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-30T21:15:00.527567+00:00
-- url     : https://prove2.me/submissions/cb68b40a-ae87-453e-9afe-20f37b278029

import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_FoundationsML_RademacherVC_RademacherComplexity_v2

open MeasureTheory

set_option autoImplicit false

namespace Cex94e7

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

theorem e_inj : Function.Injective e := fun x y h => e0.injective (Subtype.ext h)

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

theorem meas_preimage {B : Set ℝ} (hB : MeasurableSet B) : MeasurableSet (e ⁻¹' B) := by
  rw [OuterMeasure.isCaratheodory_iff_le]
  intro t
  rw [ν_apply, ν_apply, ν_apply, Set.image_inter_preimage, Set.image_diff_preimage,
    measure_inter_add_diff _ hB]

theorem e_meas : Measurable e := fun _ hB => meas_preimage hB

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

/-- Threshold hypotheses. -/
noncomputable def th (a : X) : X → ℝ := fun x => if a ≤ x then 1 else 0

def G : Set (X → ℝ) := range th

theorem th_meas (a : X) : Measurable (th a) := by
  have hs : MeasurableSet {x : X | a ≤ x} := by
    have : {x : X | a ≤ x} = (Iio a)ᶜ := by ext x; simp
    rw [this]; exact (meas_Iio a).compl
  exact Measurable.ite hs measurable_const measurable_const

theorem int_th (a : X) : (∫ z, th a z ∂P) = 1 := by
  have hae : ∀ᵐ z ∂P, a ≤ z := by
    rw [ae_iff]
    have : {x : X | ¬ a ≤ x} = Iio a := by ext x; simp
    simp only [this]
    exact P_Iio a
  rw [integral_congr_ae (g := fun _ => (1 : ℝ))]
  · simp
  · filter_upwards [hae] with z hz
    simp [th, hz]

/-- Ranges of the Rademacher correlation over thresholds, by order type of the two points. -/
theorem range_lt {x y : X} (hxy : x < y) (s0 s1 : ℝ) :
    range (fun a => (1 / 2 : ℝ) * (s0 * th a x + s1 * th a y)) =
      {(1 / 2 : ℝ) * (s0 * 1 + s1 * 1), (1 / 2 : ℝ) * (s0 * 0 + s1 * 1),
        (1 / 2 : ℝ) * (s0 * 0 + s1 * 0)} := by
  obtain ⟨b, hb⟩ := exists_gt y
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    by_cases h0 : a ≤ x
    · simp [th, h0, h0.trans hxy.le]
    · by_cases h1 : a ≤ y
      · simp [th, h0, h1]
      · simp [th, h0, h1]
  · rintro (rfl | rfl | rfl)
    · exact ⟨x, by simp [th, hxy.le]⟩
    · exact ⟨y, by simp [th, not_le.2 hxy]⟩
    · exact ⟨b, by simp [th, not_le.2 hb, not_le.2 (hxy.trans hb)]⟩

theorem range_eq (x : X) (s0 s1 : ℝ) :
    range (fun a => (1 / 2 : ℝ) * (s0 * th a x + s1 * th a x)) =
      {(1 / 2 : ℝ) * (s0 * 1 + s1 * 1), (1 / 2 : ℝ) * (s0 * 0 + s1 * 0)} := by
  obtain ⟨b, hb⟩ := exists_gt x
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    by_cases h0 : a ≤ x
    · simp [th, h0]
    · simp [th, h0]
  · rintro (rfl | rfl)
    · exact ⟨x, by simp [th]⟩
    · exact ⟨b, by simp [th, not_le.2 hb]⟩

theorem sSup3 (p q r : ℝ) : sSup ({p, q, r} : Set ℝ) = max p (max q r) := by
  rw [csSup_insert (by simp [bddAbove_def]; exact ⟨max q r, by simp, by simp⟩) (by simp),
    csSup_pair]

theorem sSup2 (p q : ℝ) : sSup ({p, q} : Set ℝ) = max p q := by
  rw [csSup_pair]

def sg (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sg_true : sg true = 1 := rfl
@[simp] theorem sg_false : sg false = -1 := rfl

noncomputable def V (x y : X) (s0 s1 : ℝ) : ℝ :=
  sSup (range fun a => (1 / 2 : ℝ) * (s0 * th a x + s1 * th a y))

theorem erc_term (S : Fin 2 → X) (σ : Fin 2 → Bool) :
    sSup ((fun g : X → ℝ =>
      (1 / ((2 : ℕ) : ℝ)) * ∑ i : Fin 2, (if σ i then (1 : ℝ) else -1) * g (S i)) '' G) =
      V (S 0) (S 1) (sg (σ 0)) (sg (σ 1)) := by
  rw [G, ← Set.range_comp, V]
  refine congrArg (fun f => sSup (range f)) ?_
  funext a
  by_cases h0 : σ 0 = true <;> by_cases h1 : σ 1 = true <;>
    simp [h0, h1, Fin.sum_univ_two, sg] <;> ring

theorem erc_V (S : Fin 2 → X) :
    FoundationsML.RademacherVC.EmpiricalRademacherComplexity G S =
      (1 / 4) * (V (S 0) (S 1) 1 1 + V (S 0) (S 1) 1 (-1) +
        V (S 0) (S 1) (-1) 1 + V (S 0) (S 1) (-1) (-1)) := by
  unfold FoundationsML.RademacherVC.EmpiricalRademacherComplexity
  simp only [erc_term]
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, sg_true, sg_false]
  norm_num
  ring

theorem V_lt' {x y : X} (hxy : x < y) (s0 s1 : ℝ) :
    V x y s0 s1 = max ((1 / 2 : ℝ) * (s0 * 1 + s1 * 1))
      (max ((1 / 2 : ℝ) * (s0 * 0 + s1 * 1)) ((1 / 2 : ℝ) * (s0 * 0 + s1 * 0))) := by
  rw [V, range_lt hxy, sSup3]

theorem V_eq' (x : X) (s0 s1 : ℝ) :
    V x x s0 s1 = max ((1 / 2 : ℝ) * (s0 * 1 + s1 * 1)) ((1 / 2 : ℝ) * (s0 * 0 + s1 * 0)) := by
  rw [V, range_eq, sSup2]

theorem V_lt {x y : X} (hxy : x < y) :
    V x y 1 1 + V x y 1 (-1) + V x y (-1) 1 + V x y (-1) (-1) = 3 / 2 := by
  rw [V_lt' hxy, V_lt' hxy, V_lt' hxy, V_lt' hxy]
  norm_num

theorem V_eq (x : X) :
    V x x 1 1 + V x x 1 (-1) + V x x (-1) 1 + V x x (-1) (-1) = 1 := by
  rw [V_eq', V_eq', V_eq', V_eq']
  norm_num

theorem V_swap (x y : X) (s0 s1 : ℝ) : V x y s0 s1 = V y x s1 s0 := by
  simp only [V]
  congr 1
  funext a
  ring

theorem erc_eq (S : Fin 2 → X) :
    FoundationsML.RademacherVC.EmpiricalRademacherComplexity G S =
      if S 0 = S 1 then 1 / 4 else 3 / 8 := by
  rw [erc_V]
  split_ifs with h
  · rw [h, V_eq]; norm_num
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · rw [V_lt hlt]; norm_num
    · rw [V_swap (S 0) (S 1) 1 1, V_swap (S 0) (S 1) 1 (-1),
        V_swap (S 0) (S 1) (-1) 1, V_swap (S 0) (S 1) (-1) (-1)]
      have := V_lt hgt
      linarith

theorem erc_meas :
    Measurable (fun S : Fin 2 → X =>
      FoundationsML.RademacherVC.EmpiricalRademacherComplexity G S) := by
  simp only [erc_eq]
  have hs : MeasurableSet {S : Fin 2 → X | S 0 = S 1} := by
    have : {S : Fin 2 → X | S 0 = S 1} = {S | e (S 0) = e (S 1)} := by
      ext S; simp [e_inj.eq_iff]
    rw [this]
    exact measurableSet_eq_fun (e_meas.comp (measurable_pi_apply 0))
      (e_meas.comp (measurable_pi_apply 1))
  exact Measurable.ite hs measurable_const measurable_const

theorem rc_le :
    FoundationsML.RademacherVC.RademacherComplexity P G 2 ≤ 3 / 8 := by
  unfold FoundationsML.RademacherVC.RademacherComplexity
  have hb : ∀ S : Fin 2 → X,
      ‖FoundationsML.RademacherVC.EmpiricalRademacherComplexity G S‖ ≤ 3 / 8 := by
    intro S
    rw [erc_eq]
    split_ifs <;> norm_num [abs_of_pos]
  have := norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin 2 => P))
    (Filter.Eventually.of_forall hb)
  simp only [probReal_univ, mul_one] at this
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ this)

theorem sqrt_small : Real.sqrt (Real.log (1 / (9 / 10 : ℝ)) / (2 * (2 : ℕ))) < 1 / 4 := by
  rw [Real.sqrt_lt' (by norm_num)]
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (9 / 10) by norm_num)
  push_cast
  norm_num at h ⊢
  linarith

theorem event_empty :
    {S : Fin 2 → X | ∀ g ∈ G,
        (∫ z, g z ∂P) ≤
          (1 / ((2 : ℕ) : ℝ)) * ∑ i : Fin 2, g (S i) +
            2 * FoundationsML.RademacherVC.RademacherComplexity P G 2 +
            Real.sqrt (Real.log (1 / (9 / 10 : ℝ)) / (2 * (2 : ℕ)))} = ∅ := by
  ext S
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall]
  obtain ⟨a, ha⟩ := exists_gt (max (S 0) (S 1))
  refine ⟨th a, ⟨a, rfl⟩, ?_⟩
  have h0 : ¬ a ≤ S 0 := not_le.2 ((le_max_left _ _).trans_lt ha)
  have h1 : ¬ a ≤ S 1 := not_le.2 ((le_max_right _ _).trans_lt ha)
  have hE : (1 / ((2 : ℕ) : ℝ)) * ∑ i : Fin 2, th a (S i) = 0 := by
    simp [Fin.sum_univ_two, th, h0, h1, not_le.mp h0, not_le.mp h1]
  rw [int_th, hE]
  have := rc_le
  have := sqrt_small
  linarith

end Cex94e7

open FoundationsML.RademacherVC in
theorem solution : ¬ (∀ {Z : Type} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (G : Set (Z → ℝ)) (hGb : ∀ g ∈ G, ∀ z, g z ∈ Set.Icc (0 : ℝ) 1)
    (hGm : ∀ g ∈ G, Measurable g)
    (m : ℕ) (hm : 0 < m)
    (hGsup : Measurable (fun S : Fin m → Z => EmpiricalRademacherComplexity G S))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → Z | ∀ g ∈ G, (∫ z, g z ∂D) ≤
        (1 / (m : ℝ)) * ∑ i, g (S i) + 2 * RademacherComplexity D G m +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal ∧
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → Z | ∀ g ∈ G, (∫ z, g z ∂D) ≤
        (1 / (m : ℝ)) * ∑ i, g (S i) + 2 * EmpiricalRademacherComplexity G S +
          3 * Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal) := by
  intro hall
  have h := (hall (Z := Cex94e7.X) Cex94e7.P Cex94e7.G
    (by
      rintro _ ⟨a, rfl⟩ x
      simp only [Cex94e7.th]
      split_ifs <;> norm_num)
    (by rintro _ ⟨a, rfl⟩; exact Cex94e7.th_meas a)
    2 two_pos Cex94e7.erc_meas (9 / 10) (by norm_num) (by norm_num)).1
  rw [Cex94e7.event_empty, measure_empty, ENNReal.toReal_zero] at h
  norm_num at h
