-- Prove2me | solution 1 for FoundationsML.RademacherVC.vc_dimension_generalization_bound_v2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-30T21:22:42.660318+00:00
-- url     : https://prove2.me/submissions/80c218de-59b4-49f3-8c51-211bc393382d

import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_FoundationsML_RademacherVC_GeneralizationError
import Definitions.Def_FoundationsML_RademacherVC_EmpiricalError
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim

open MeasureTheory

set_option autoImplicit false

namespace Cex9002

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

/-- Boolean threshold hypotheses. -/
noncomputable def thB (a : X) : X → Bool := fun x => decide (a ≤ x)

def H : Set (X → Bool) := range thB

def c : X → Bool := fun _ => false

theorem c_meas : Measurable c := measurable_const

theorem thB_meas (a : X) : Measurable (thB a) := by
  have hs : MeasurableSet {x : X | a ≤ x} := by
    have : {x : X | a ≤ x} = (Iio a)ᶜ := by ext x; simp
    rw [this]; exact (meas_Iio a).compl
  have hite : thB a = fun x => if a ≤ x then true else false := by
    funext x; by_cases h : a ≤ x <;> simp [thB, h]
  rw [hite]
  exact Measurable.ite hs measurable_const measurable_const

theorem genErr (a : X) :
    FoundationsML.RademacherVC.GeneralizationError P c (thB a) = 1 := by
  unfold FoundationsML.RademacherVC.GeneralizationError
  have hset : {x : X | thB a x ≠ c x} = (Iio a)ᶜ := by
    ext x; simp [thB, c]
  rw [hset, measure_compl (meas_Iio a) (measure_ne_top _ _), P_Iio, measure_univ]
  simp

theorem card_sub_le {m : ℕ} (x : Fin m → X) :
    Nat.card {t : Fin m → Bool // ∃ h ∈ H, t = h ∘ x} ≤ 2 ^ m := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_subtype_le _).trans (by simp)

theorem growth_one : FoundationsML.RademacherVC.GrowthFunction H 1 = 2 ^ 1 := by
  classical
  unfold FoundationsML.RademacherVC.GrowthFunction
  apply le_antisymm
  · exact ciSup_le (fun x => card_sub_le x)
  · let x0 : X := Classical.arbitrary X
    let x : Fin 1 → X := fun _ => x0
    have hbdd : BddAbove (range fun x : Fin 1 → X =>
        Nat.card {t : Fin 1 → Bool // ∃ h ∈ H, t = h ∘ x}) :=
      ⟨2 ^ 1, by rintro _ ⟨y, rfl⟩; exact card_sub_le y⟩
    refine le_trans ?_ (le_ciSup hbdd x)
    have huniv : ∀ t : Fin 1 → Bool, ∃ h ∈ H, t = h ∘ x := by
      intro t
      cases ht : t 0
      · obtain ⟨b, hb⟩ := exists_gt x0
        refine ⟨thB b, ⟨b, rfl⟩, funext fun i => ?_⟩
        rw [Fin.eq_zero i, ht]
        simp [x, thB, not_le.2 hb]
      · refine ⟨thB x0, ⟨x0, rfl⟩, funext fun i => ?_⟩
        rw [Fin.eq_zero i, ht]
        simp [x, thB]
    rw [Nat.card_eq_fintype_card, Fintype.card_of_subtype Finset.univ (by simp [huniv])]
    simp

theorem card_sub_lt_of_two_le {m : ℕ} (hm : 2 ≤ m) (x : Fin m → X) :
    Nat.card {t : Fin m → Bool // ∃ h ∈ H, t = h ∘ x} ≤ 2 ^ m - 1 := by
  classical
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have h01_ne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    dsimp [i0, i1] at this
    omega
  have hex : ∃ t0 : Fin m → Bool, ¬ ∃ h ∈ H, t0 = h ∘ x := by
    by_cases hle : x i0 ≤ x i1
    · refine ⟨fun i => decide (i = i0), ?_⟩
      rintro ⟨_, ⟨a, rfl⟩, ht⟩
      have h0 := congrFun ht i0
      have h1 := congrFun ht i1
      have h0' : a ≤ x i0 := of_decide_eq_true (by simpa [Function.comp_apply, thB] using h0.symm)
      have h1' : ¬ a ≤ x i1 :=
        of_decide_eq_false (by simpa [Function.comp_apply, thB, h01_ne.symm] using h1.symm)
      exact h1' (h0'.trans hle)
    · have hle' : x i1 ≤ x i0 := le_of_not_ge hle
      refine ⟨fun i => decide (i = i1), ?_⟩
      rintro ⟨_, ⟨a, rfl⟩, ht⟩
      have h0 := congrFun ht i0
      have h1 := congrFun ht i1
      have h1' : a ≤ x i1 := of_decide_eq_true (by simpa [Function.comp_apply, thB] using h1.symm)
      have h0' : ¬ a ≤ x i0 :=
        of_decide_eq_false (by simpa [Function.comp_apply, thB, h01_ne] using h0.symm)
      exact h0' (h1'.trans hle')
  obtain ⟨t0, ht0⟩ := hex
  let s : Finset (Fin m → Bool) := Finset.univ.filter (fun t => ∃ h ∈ H, t = h ∘ x)
  rw [Nat.card_eq_fintype_card, Fintype.card_of_subtype s (by simp [s])]
  have hlt : s.card < (Finset.univ : Finset (Fin m → Bool)).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have : t0 ∈ s := heq ▸ Finset.mem_univ t0
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact ht0 this
  have hcard : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by simp
  rw [hcard] at hlt
  omega

theorem hasVCDim_H : FoundationsML.RademacherVC.HasVCDim H 1 := by
  refine ⟨growth_one, fun m hm => ?_⟩
  by_contra hlt
  have hm2 : 2 ≤ m := by omega
  have hle : FoundationsML.RademacherVC.GrowthFunction H m ≤ 2 ^ m - 1 := by
    unfold FoundationsML.RademacherVC.GrowthFunction
    exact ciSup_le (fun x => card_sub_lt_of_two_le hm2 x)
  rw [hm] at hle
  have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

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
    {S : Fin 64 → X | ∀ h ∈ H,
      FoundationsML.RademacherVC.GeneralizationError P c h ≤
        FoundationsML.RademacherVC.EmpiricalError S c h +
          Real.sqrt (2 * (1 : ℕ) * Real.log (Real.exp 1 * (64 : ℕ) / (1 : ℕ)) / (64 : ℕ)) +
          Real.sqrt (Real.log (1 / (9 / 10 : ℝ)) / (2 * (64 : ℕ)))} = ∅ := by
  ext S
  simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall]
  let M : X := Finset.univ.sup' Finset.univ_nonempty S
  obtain ⟨a, ha⟩ := exists_gt M
  refine ⟨thB a, ⟨a, rfl⟩, ?_⟩
  have hE : FoundationsML.RademacherVC.EmpiricalError S c (thB a) = 0 := by
    unfold FoundationsML.RademacherVC.EmpiricalError
    rw [div_eq_zero_iff]; left; norm_cast
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rw [Finset.mem_filter] at hi
    have hle : S i ≤ M := Finset.le_sup' S (Finset.mem_univ i)
    have hna : ¬ a ≤ S i := not_le.2 (hle.trans_lt ha)
    exact hi.2 (by simp [thB, c, hna])
  rw [genErr, hE]
  have := vc_term_small
  have := delta_term_small
  linarith

end Cex9002

open FoundationsML.RademacherVC in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Set (X → Bool)) (d : ℕ) (hH : HasVCDim H d) (hH_meas : ∀ h ∈ H, Measurable h)
    (c : X → Bool) (hc_meas : Measurable c)
    (m : ℕ) (hm0 : 0 < m) (hm : d ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤
        EmpiricalError S c h +
          Real.sqrt (2 * d * Real.log (Real.exp 1 * m / d) / m) +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal) := by
  intro hall
  have h := hall (X := Cex9002.X) Cex9002.P Cex9002.H 1 Cex9002.hasVCDim_H
    (by rintro _ ⟨a, rfl⟩; exact Cex9002.thB_meas a)
    Cex9002.c Cex9002.c_meas 64 (by decide) (by decide) (9 / 10) (by norm_num) (by norm_num)
  rw [Cex9002.event_empty, measure_empty, ENNReal.toReal_zero] at h
  norm_num at h
