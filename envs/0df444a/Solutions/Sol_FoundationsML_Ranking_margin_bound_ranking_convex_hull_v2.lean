-- Prove2me | solution 1 for FoundationsML.Ranking.margin_bound_ranking_convex_hull_v2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-30T21:44:04.217906+00:00
-- url     : https://prove2.me/submissions/62a1531b-099f-400b-9555-7c4f0b9c05b9

import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_FoundationsML_Ranking_GeneralizationError
import Definitions.Def_FoundationsML_Ranking_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Ranking_RademacherComplexity_v2
import Definitions.Def_FoundationsML_Ranking_ConvHull_v2

open MeasureTheory

set_option autoImplicit false

namespace Cex5233

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

theorem A_ne : A.Nonempty := nonempty_of_measure_ne_zero A_pos

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

instance instMSC : MeasurableSingletonClass X :=
  ⟨fun x => meas_of_null (by rw [ν_apply, image_singleton]; exact measure_singleton _)⟩

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

/-- The fixed first point of every pair. -/
noncomputable def p : X := e0.symm ⟨A_ne.some, A_ne.some_mem⟩

theorem P_p : P {p} = 0 := by
  obtain ⟨b, hb⟩ := exists_gt p
  exact measure_mono_null (singleton_subset_iff.2 hb) (P_Iio b)

/-- The pair distribution: `(p, x)` with `x ∼ P`. -/
noncomputable def D : Measure (X × X) := P.map (fun x => (p, x))

theorem j_meas : Measurable (fun x : X => (p, x)) := measurable_const.prodMk measurable_id

instance D_prob : IsProbabilityMeasure D := Measure.isProbabilityMeasure_map j_meas.aemeasurable

theorem D_fst : D.map Prod.fst = Measure.dirac p := by
  rw [D, Measure.map_map measurable_fst j_meas]
  change P.map (fun _ => p) = _
  rw [Measure.map_const, measure_univ, one_smul]

theorem D_snd : D.map Prod.snd = P := by
  rw [D, Measure.map_map measurable_snd j_meas]
  exact Measure.map_id

/-- The preference function: always `1`. -/
def fr : X × X → ℝ := fun _ => 1

/-- Lower-segment indicator: `1` strictly below `a`, `0` from `a` on. -/
noncomputable def th (a : X) : X → ℝ := fun x => if a ≤ x then 0 else 1

/-- Hypotheses: the lower-segment indicator, forced to `0` at `p`. -/
noncomputable def g (a : X) : X → ℝ := fun x => if x = p then 0 else th a x

def H : Set (X → ℝ) := range g

theorem g_mem_convHull (a : X) : g a ∈ FoundationsML.Ranking.ConvHull H :=
  ⟨1, fun _ => 1, fun _ => g a, le_rfl, fun _ => zero_le_one,
    fun _ => ⟨a, rfl⟩, by simp, by funext x; simp⟩

theorem th_meas (a : X) : Measurable (th a) := by
  have hs : MeasurableSet {x : X | a ≤ x} := by
    have : {x : X | a ≤ x} = (Iio a)ᶜ := by ext x; simp
    rw [this]; exact (meas_Iio a).compl
  exact Measurable.ite hs measurable_const measurable_const

theorem g_meas (a : X) : Measurable (g a) :=
  Measurable.ite (measurableSet_singleton p) measurable_const (th_meas a)

theorem g_p (a : X) : g a p = 0 := by simp [g]

theorem genErr (a : X) : FoundationsML.Ranking.GeneralizationError D fr (g a) = 1 := by
  have hset : MeasurableSet {q : X × X | fr q * (g a q.2 - g a q.1) ≤ 0} :=
    measurableSet_le (measurable_const.mul
      (((g_meas a).comp measurable_snd).sub ((g_meas a).comp measurable_fst))) measurable_const
  have hpre : (fun x : X => (p, x)) ⁻¹' {q : X × X | fr q * (g a q.2 - g a q.1) ≤ 0} =
      (Iio a \ {p})ᶜ := by
    ext x
    by_cases hx : x = p
    · subst hx; simp [fr, g_p]
    · by_cases ha : a ≤ x
      · simp [fr, g, th, hx, ha, g_p]
      · simp [fr, g, th, hx, ha, g_p, not_le.1 ha]
  have hnull : P (Iio a \ {p}) = 0 := measure_mono_null diff_subset (P_Iio a)
  unfold FoundationsML.Ranking.GeneralizationError
  rw [D, Measure.map_apply j_meas hset, hpre,
    measure_compl ((meas_Iio a).diff (measurableSet_singleton p)) (measure_ne_top _ _),
    hnull, measure_univ]
  simp

/-- Ranges of the Rademacher correlation over lower segments, by order type of the two points. -/
theorem range_lt {x y : X} (hxy : x < y) (s0 s1 : ℝ) :
    range (fun a => (1 / 2 : ℝ) * (s0 * th a x + s1 * th a y)) =
      {(1 / 2 : ℝ) * (s0 * 1 + s1 * 1), (1 / 2 : ℝ) * (s0 * 1 + s1 * 0),
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
    · exact ⟨b, by simp [th, not_le.2 hb, not_le.2 (hxy.trans hb)]⟩
    · exact ⟨y, by simp [th, not_le.2 hxy]⟩
    · exact ⟨x, by simp [th, hxy.le]⟩

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
    · exact ⟨b, by simp [th, not_le.2 hb]⟩
    · exact ⟨x, by simp [th]⟩

theorem range_one (y : X) (s1 : ℝ) :
    range (fun a => (1 / 2 : ℝ) * (s1 * th a y)) = {(1 / 2 : ℝ) * (s1 * 1), (1 / 2 : ℝ) * (s1 * 0)} := by
  obtain ⟨b, hb⟩ := exists_gt y
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    by_cases h0 : a ≤ y
    · simp [th, h0]
    · simp [th, h0]
  · rintro (rfl | rfl)
    · exact ⟨b, by simp [th, not_le.2 hb]⟩
    · exact ⟨y, by simp [th]⟩

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

noncomputable def W (x y : X) (s0 s1 : ℝ) : ℝ :=
  sSup (range fun a => (1 / 2 : ℝ) * (s0 * g a x + s1 * g a y))

theorem erc_term (S : Fin 2 → X) (σ : Fin 2 → Bool) :
    sSup ((fun h : X → ℝ =>
      (1 / ((2 : ℕ) : ℝ)) * ∑ i : Fin 2, (if σ i then (1 : ℝ) else -1) * h (S i)) '' H) =
      W (S 0) (S 1) (sg (σ 0)) (sg (σ 1)) := by
  rw [H, ← Set.range_comp, W]
  refine congrArg (fun f => sSup (range f)) ?_
  funext a
  by_cases h0 : σ 0 = true <;> by_cases h1 : σ 1 = true <;>
    simp [h0, h1, Fin.sum_univ_two, sg] <;> ring

/-- The four-sign average of `W`. -/
noncomputable def W4 (x y : X) : ℝ :=
  W x y 1 1 + W x y 1 (-1) + W x y (-1) 1 + W x y (-1) (-1)

theorem erc_W (S : Fin 2 → X) :
    FoundationsML.Ranking.EmpiricalRademacherComplexity H S = (1 / 4) * W4 (S 0) (S 1) := by
  unfold FoundationsML.Ranking.EmpiricalRademacherComplexity
  simp only [erc_term]
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, sg_true, sg_false, W4]
  norm_num
  ring

theorem V_lt' {x y : X} (hxy : x < y) (s0 s1 : ℝ) :
    V x y s0 s1 = max ((1 / 2 : ℝ) * (s0 * 1 + s1 * 1))
      (max ((1 / 2 : ℝ) * (s0 * 1 + s1 * 0)) ((1 / 2 : ℝ) * (s0 * 0 + s1 * 0))) := by
  rw [V, range_lt hxy, sSup3]

theorem V_eq' (x : X) (s0 s1 : ℝ) :
    V x x s0 s1 = max ((1 / 2 : ℝ) * (s0 * 1 + s1 * 1)) ((1 / 2 : ℝ) * (s0 * 0 + s1 * 0)) := by
  rw [V, range_eq, sSup2]

theorem W_np {x y : X} (hx : x ≠ p) (hy : y ≠ p) (s0 s1 : ℝ) : W x y s0 s1 = V x y s0 s1 := by
  simp only [W, V, g, hx, hy, if_false]

theorem W_swap (x y : X) (s0 s1 : ℝ) : W x y s0 s1 = W y x s1 s0 := by
  simp only [W]
  congr 1
  funext a
  ring

theorem W_p1 {y : X} (hy : y ≠ p) (s0 s1 : ℝ) :
    W p y s0 s1 = max ((1 / 2 : ℝ) * (s1 * 1)) ((1 / 2 : ℝ) * (s1 * 0)) := by
  have : (fun a => (1 / 2 : ℝ) * (s0 * g a p + s1 * g a y)) =
      (fun a => (1 / 2 : ℝ) * (s1 * th a y)) := by
    funext a; simp [g, hy]
  rw [W, this, range_one, sSup2]

theorem W_pp (s0 s1 : ℝ) : W p p s0 s1 = 0 := by
  have hz : (fun a => (1 / 2 : ℝ) * (s0 * g a p + s1 * g a p)) = (fun _ => (0 : ℝ)) := by
    funext a; simp [g_p]
  haveI : Nonempty X := ⟨p⟩
  rw [W, hz, Set.range_const, csSup_singleton]

theorem W4_lt {x y : X} (hxy : x < y) (hx : x ≠ p) (hy : y ≠ p) : W4 x y = 3 / 2 := by
  rw [W4, W_np hx hy, W_np hx hy, W_np hx hy, W_np hx hy, V_lt' hxy, V_lt' hxy, V_lt' hxy,
    V_lt' hxy]
  norm_num

theorem W4_np {x y : X} (hx : x ≠ p) (hy : y ≠ p) : W4 x y = if x = y then 1 else 3 / 2 := by
  split_ifs with h
  · subst h
    rw [W4, W_np hx hx, W_np hx hx, W_np hx hx, W_np hx hx, V_eq', V_eq', V_eq', V_eq']
    norm_num
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · exact W4_lt hlt hx hy
    · have := W4_lt hgt hy hx
      rw [W4, W_swap x y 1 1, W_swap x y 1 (-1), W_swap x y (-1) 1, W_swap x y (-1) (-1)]
      rw [W4] at this
      linarith

theorem W4_p1 {y : X} (hy : y ≠ p) : W4 p y = 1 := by
  rw [W4, W_p1 hy, W_p1 hy, W_p1 hy, W_p1 hy]
  norm_num

theorem W4_p2 {x : X} (hx : x ≠ p) : W4 x p = 1 := by
  rw [W4, W_swap x p 1 1, W_swap x p 1 (-1), W_swap x p (-1) 1, W_swap x p (-1) (-1),
    W_p1 hx, W_p1 hx, W_p1 hx, W_p1 hx]
  norm_num

theorem W4_pp : W4 p p = 0 := by
  rw [W4, W_pp, W_pp, W_pp, W_pp]
  norm_num

theorem erc_eq (S : Fin 2 → X) :
    FoundationsML.Ranking.EmpiricalRademacherComplexity H S =
      if S 0 = p then (if S 1 = p then 0 else 1 / 4)
      else if S 1 = p then 1 / 4 else if S 0 = S 1 then 1 / 4 else 3 / 8 := by
  rw [erc_W]
  by_cases h0 : S 0 = p
  · by_cases h1 : S 1 = p
    · rw [h0, h1, W4_pp]; simp
    · rw [h0, W4_p1 h1]; simp [h1]
  · by_cases h1 : S 1 = p
    · rw [h1, W4_p2 h0]; simp [h0]
    · rw [W4_np h0 h1]
      split_ifs <;> norm_num

theorem erc_meas :
    Measurable (fun S : Fin 2 → X => FoundationsML.Ranking.EmpiricalRademacherComplexity H S) := by
  simp only [erc_eq]
  have h0 : MeasurableSet {S : Fin 2 → X | S 0 = p} :=
    (measurableSet_singleton p).preimage (measurable_pi_apply 0)
  have h1 : MeasurableSet {S : Fin 2 → X | S 1 = p} :=
    (measurableSet_singleton p).preimage (measurable_pi_apply 1)
  have hs : MeasurableSet {S : Fin 2 → X | S 0 = S 1} := by
    have : {S : Fin 2 → X | S 0 = S 1} = {S | e (S 0) = e (S 1)} := by
      ext S; simp [e_inj.eq_iff]
    rw [this]
    have e_meas : Measurable e := by
      intro B hB
      rw [OuterMeasure.isCaratheodory_iff_le]
      intro t
      rw [ν_apply, ν_apply, ν_apply, Set.image_inter_preimage, Set.image_diff_preimage,
        measure_inter_add_diff _ hB]
    exact measurableSet_eq_fun (e_meas.comp (measurable_pi_apply 0))
      (e_meas.comp (measurable_pi_apply 1))
  exact Measurable.ite h0 (Measurable.ite h1 measurable_const measurable_const)
    (Measurable.ite h1 measurable_const (Measurable.ite hs measurable_const measurable_const))

theorem rc_fst : FoundationsML.Ranking.RademacherComplexity (Measure.map Prod.fst D) H 2 = 0 := by
  unfold FoundationsML.Ranking.RademacherComplexity
  rw [D_fst]
  have hp : ∀ᵐ x ∂(Measure.dirac p), x = p :=
    (ae_dirac_iff (p := fun x : X => x = p) (measurableSet_singleton p)).2 rfl
  have hall : ∀ᵐ S ∂(Measure.pi (fun _ : Fin 2 => Measure.dirac p)), ∀ i, S i = p := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 2 => Measure.dirac p) (i := i)).eventually
      (p := fun x : X => x = p) hp
  apply integral_eq_zero_of_ae
  filter_upwards [hall] with S hS
  simp [erc_eq, hS 0, hS 1]

theorem rc_snd : FoundationsML.Ranking.RademacherComplexity (Measure.map Prod.snd D) H 2 ≤ 3 / 8 := by
  unfold FoundationsML.Ranking.RademacherComplexity
  rw [D_snd]
  have hb : ∀ S : Fin 2 → X,
      ‖FoundationsML.Ranking.EmpiricalRademacherComplexity H S‖ ≤ 3 / 8 := by
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

theorem pairs_ae : ∀ᵐ q ∂D, q.1 = p ∧ q.2 ≠ p := by
  have hs : MeasurableSet {q : X × X | q.1 = p ∧ q.2 ≠ p} := by
    have : {q : X × X | q.1 = p ∧ q.2 ≠ p} = Prod.fst ⁻¹' {p} ∩ (Prod.snd ⁻¹' {p})ᶜ := by
      ext q; simp
    rw [this]
    exact ((measurableSet_singleton p).preimage measurable_fst).inter
      ((measurableSet_singleton p).preimage measurable_snd).compl
  rw [D, ae_map_iff j_meas.aemeasurable hs]
  have h := (measure_eq_zero_iff_ae_notMem).1 P_p
  filter_upwards [h] with x hx
  exact ⟨rfl, by simpa using hx⟩

/-- The first event misses every sample of pairs `(p, x)` with `x ≠ p`. -/
theorem not_mem_event (S : Fin 2 → X × X) (hS : ∀ i, (S i).1 = p ∧ (S i).2 ≠ p) :
    S ∉ {S : Fin 2 → X × X | ∀ h ∈ FoundationsML.Ranking.ConvHull H,
        FoundationsML.Ranking.GeneralizationError D fr h ≤
          FoundationsML.Ranking.EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2)
              (fun i => fr (S i)) h +
            (2 / 1) * (FoundationsML.Ranking.RademacherComplexity (Measure.map Prod.fst D) H 2 +
              FoundationsML.Ranking.RademacherComplexity (Measure.map Prod.snd D) H 2) +
            Real.sqrt (Real.log (1 / (9 / 10 : ℝ)) / (2 * (2 : ℕ)))} := by
  simp only [mem_setOf_eq, not_forall]
  obtain ⟨a, ha⟩ := exists_gt (max (S 0).2 (S 1).2)
  refine ⟨g a, g_mem_convHull a, ?_⟩
  have h0 : ¬ a ≤ (S 0).2 := not_le.2 ((le_max_left _ _).trans_lt ha)
  have h1 : ¬ a ≤ (S 1).2 := not_le.2 ((le_max_right _ _).trans_lt ha)
  have hE : FoundationsML.Ranking.EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2)
      (fun i => fr (S i)) (g a) = 0 := by
    simp [FoundationsML.Ranking.EmpiricalMarginLoss, FoundationsML.Ranking.MarginLossFunction,
      Fin.sum_univ_two, fr, g, th, h0, h1, (hS 0).1, (hS 1).1, (hS 0).2, (hS 1).2]
  rw [genErr, hE, rc_fst]
  have := rc_snd
  have := sqrt_small
  intro hle
  linarith

theorem event_null :
    Measure.pi (fun _ : Fin 2 => D) {S : Fin 2 → X × X | ∀ h ∈ FoundationsML.Ranking.ConvHull H,
        FoundationsML.Ranking.GeneralizationError D fr h ≤
          FoundationsML.Ranking.EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2)
              (fun i => fr (S i)) h +
            (2 / 1) * (FoundationsML.Ranking.RademacherComplexity (Measure.map Prod.fst D) H 2 +
              FoundationsML.Ranking.RademacherComplexity (Measure.map Prod.snd D) H 2) +
            Real.sqrt (Real.log (1 / (9 / 10 : ℝ)) / (2 * (2 : ℕ)))} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  have hall : ∀ᵐ S ∂(Measure.pi (fun _ : Fin 2 => D)), ∀ i, (S i).1 = p ∧ (S i).2 ≠ p := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 2 => D) (i := i)).eventually
      (p := fun q : X × X => q.1 = p ∧ q.2 ≠ p) pairs_ae
  filter_upwards [hall] with S hS
  exact not_mem_event S hS

end Cex5233

open FoundationsML.Ranking in
theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure (X × X)) [IsProbabilityMeasure D]
    (f : X × X → ℝ) (hf : ∀ p, f p = 1 ∨ f p = -1) (hf_meas : Measurable f)
    (H : Set (X → ℝ)) (hHb : ∃ a b : ℝ, ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b)
    (hHmeas : ∀ h ∈ H, Measurable h)
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (hm : 0 < m)
    (hHsup : Measurable (fun S : Fin m → X => EmpiricalRademacherComplexity H S))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × X | ∀ h ∈ ConvHull H,
        GeneralizationError D f h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun i => f (S i)) h +
            (2 / ρ) * (RademacherComplexity (Measure.map Prod.fst D) H m +
              RademacherComplexity (Measure.map Prod.snd D) H m) +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal ∧
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × X | ∀ h ∈ ConvHull H,
        GeneralizationError D f h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun i => f (S i)) h +
            (2 / ρ) * (EmpiricalRademacherComplexity H (fun i => (S i).1) +
              EmpiricalRademacherComplexity H (fun i => (S i).2)) +
            3 * Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal) := by
  intro hall
  have h := (hall (X := Cex5233.X) Cex5233.D Cex5233.fr (fun _ => Or.inl rfl) measurable_const
    Cex5233.H
    ⟨0, 1, by
      rintro _ ⟨a, rfl⟩ x
      simp only [Cex5233.g, Cex5233.th]
      split_ifs <;> norm_num⟩
    (by rintro _ ⟨a, rfl⟩; exact Cex5233.g_meas a)
    1 one_pos 2 two_pos Cex5233.erc_meas (9 / 10) (by norm_num) (by norm_num)).1
  rw [Cex5233.event_null, ENNReal.toReal_zero] at h
  norm_num at h
