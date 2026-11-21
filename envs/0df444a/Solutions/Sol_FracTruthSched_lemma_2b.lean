-- Prove2me | solution 1 for FracTruthSched.lemma_2b
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T14:33:30.826872+00:00
-- url     : https://prove2.me/submissions/3c34ffc2-7076-420b-83c0-e91ed67a7afc

import Mathlib
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_IsGraphInput
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_pairSliceDisutility
import Theorems.Thm_FracTruthSched_lemma_10
import Theorems.Thm_FracTruthSched_lemma_4

section
/-! Lower regularization in the second argument, for `versions` of Lemma 2(b) (q407). -/

set_option autoImplicit false

namespace FracTruthSched.Dev.Reg
open MeasureTheory Filter Topology

/-- Clamp to the closed orthant. -/
def cl (x : ℝ × ℝ) : ℝ × ℝ := (max x.1 0, max x.2 0)

/-- Hypotheses: monotone and 1-Lipschitz per coordinate in `x`, monotone in `y`, on the orthant. -/
structure RegHyp (F : ℝ × ℝ → ℝ × ℝ → ℝ) : Prop where
  lip : ∀ x x' y : ℝ × ℝ, 0 ≤ x.1 → 0 ≤ x.2 → x.1 ≤ x'.1 → x.2 ≤ x'.2 → 0 ≤ y.1 → 0 ≤ y.2 →
    F x y ≤ F x' y ∧ F x' y ≤ F x y + ((x'.1 - x.1) + (x'.2 - x.2))
  mono : ∀ x y y' : ℝ × ℝ, 0 ≤ x.1 → 0 ≤ x.2 → 0 ≤ y.1 → 0 ≤ y.2 → y.1 ≤ y'.1 → y.2 ≤ y'.2 →
    F x y ≤ F x y'

/-- The validity condition of a rational point `q` below `y`. -/
def Valid (q : ℚ × ℚ) (y : ℝ × ℝ) : Prop :=
  0 ≤ (q.1 : ℝ) ∧ 0 ≤ (q.2 : ℝ) ∧ (q.1 : ℝ) < y.1 ∧ (q.2 : ℝ) < y.2

noncomputable def term (F : ℝ × ℝ → ℝ × ℝ → ℝ) (x y : ℝ × ℝ) (q : ℚ × ℚ) : ℝ := by
  classical
  exact if Valid q y then F (cl x) ((q.1 : ℝ), (q.2 : ℝ)) else F (cl x) 0

noncomputable def reg (F : ℝ × ℝ → ℝ × ℝ → ℝ) (x y : ℝ × ℝ) : ℝ := ⨆ q, term F x y q

variable {F : ℝ × ℝ → ℝ × ℝ → ℝ}

lemma cl_nn (x : ℝ × ℝ) : 0 ≤ (cl x).1 ∧ 0 ≤ (cl x).2 := ⟨le_max_right _ _, le_max_right _ _⟩

lemma cl_of_nn (x : ℝ × ℝ) (h1 : 0 ≤ x.1) (h2 : 0 ≤ x.2) : cl x = x := by
  simp [cl, h1, h2]

lemma term_le (h : RegHyp F) (x y : ℝ × ℝ) (q : ℚ × ℚ) : term F x y q ≤ F (cl x) (cl y) := by
  classical
  unfold term
  split_ifs with hq
  · obtain ⟨a, b, c, d⟩ := hq
    exact h.mono _ _ _ (cl_nn x).1 (cl_nn x).2 a b (le_max_of_le_left c.le) (le_max_of_le_left d.le)
  · exact h.mono _ _ _ (cl_nn x).1 (cl_nn x).2 le_rfl le_rfl (cl_nn y).1 (cl_nn y).2

lemma bdd (h : RegHyp F) (x y : ℝ × ℝ) : BddAbove (Set.range (term F x y)) :=
  ⟨F (cl x) (cl y), by rintro _ ⟨q, rfl⟩; exact term_le h x y q⟩

lemma reg_le (h : RegHyp F) (x y : ℝ × ℝ) : reg F x y ≤ F (cl x) (cl y) :=
  ciSup_le fun q => term_le h x y q

lemma le_reg (h : RegHyp F) (x y : ℝ × ℝ) (q : ℚ × ℚ) : term F x y q ≤ reg F x y :=
  le_ciSup (bdd h x y) q

lemma base_le_reg (h : RegHyp F) (x y : ℝ × ℝ) : F (cl x) 0 ≤ reg F x y := by
  classical
  have := le_reg h x y (-1, -1)
  have hv : ¬ Valid ((-1, -1) : ℚ × ℚ) y := by
    intro hv; have := hv.1; norm_num at this
  simpa [term, hv] using this

lemma valid_le_reg (h : RegHyp F) (x y : ℝ × ℝ) (q : ℚ × ℚ) (hq : Valid q y) :
    F (cl x) ((q.1 : ℝ), (q.2 : ℝ)) ≤ reg F x y := by
  classical
  have := le_reg h x y q
  simpa [term, hq] using this

lemma reg_cl (x y : ℝ × ℝ) : reg F (cl x) y = reg F x y := by
  have : cl (cl x) = cl x := cl_of_nn _ (cl_nn x).1 (cl_nn x).2
  simp [reg, term, this]

/-- Monotone and Lipschitz in `x` along the orthant. -/
lemma reg_lip (h : RegHyp F) (x x' y : ℝ × ℝ) (h1 : 0 ≤ x.1) (h2 : 0 ≤ x.2) (h3 : x.1 ≤ x'.1)
    (h4 : x.2 ≤ x'.2) :
    reg F x y ≤ reg F x' y ∧ reg F x' y ≤ reg F x y + ((x'.1 - x.1) + (x'.2 - x.2)) := by
  classical
  have ex : cl x = x := cl_of_nn x h1 h2
  have ex' : cl x' = x' := cl_of_nn x' (h1.trans h3) (h2.trans h4)
  constructor
  · refine ciSup_mono (bdd h x' y) fun q => ?_
    unfold term
    rw [ex, ex']
    split_ifs with hq
    · exact (h.lip x x' ((q.1 : ℝ), (q.2 : ℝ)) h1 h2 h3 h4 hq.1 hq.2.1).1
    · exact (h.lip x x' 0 h1 h2 h3 h4 le_rfl le_rfl).1
  · refine ciSup_le fun q => ?_
    have hle := le_reg h x y q
    unfold term at hle ⊢
    rw [ex, ex'] at *
    split_ifs with hq
    · rw [if_pos hq] at hle
      have := (h.lip x x' ((q.1 : ℝ), (q.2 : ℝ)) h1 h2 h3 h4 hq.1 hq.2.1).2
      linarith
    · rw [if_neg hq] at hle
      have := (h.lip x x' 0 h1 h2 h3 h4 le_rfl le_rfl).2
      linarith

/-- A two-sided Lipschitz bound in `x` on the whole plane (through the clamp). -/
lemma clamp_lip (G : ℝ × ℝ → ℝ)
    (hG : ∀ x x' : ℝ × ℝ, 0 ≤ x.1 → 0 ≤ x.2 → x.1 ≤ x'.1 → x.2 ≤ x'.2 →
      G x ≤ G x' ∧ G x' ≤ G x + ((x'.1 - x.1) + (x'.2 - x.2))) :
    LipschitzWith 2 (fun x => G (cl x)) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  set m : ℝ × ℝ := (max (cl x).1 (cl x').1, max (cl x).2 (cl x').2)
  have hx := cl_nn x
  have hx' := cl_nn x'
  have a := hG (cl x) m hx.1 hx.2 (le_max_left _ _) (le_max_left _ _)
  have b := hG (cl x') m hx'.1 hx'.2 (le_max_right _ _) (le_max_right _ _)
  have d1 : |(cl x).1 - (cl x').1| ≤ dist x x' := by
    have : |(cl x).1 - (cl x').1| ≤ |x.1 - x'.1| := abs_max_sub_max_le_abs _ _ _
    have hd : dist x.1 x'.1 ≤ dist x x' := by rw [Prod.dist_eq]; exact le_max_left _ _
    rw [Real.dist_eq] at hd; exact this.trans hd
  have d2 : |(cl x).2 - (cl x').2| ≤ dist x x' := by
    have : |(cl x).2 - (cl x').2| ≤ |x.2 - x'.2| := abs_max_sub_max_le_abs _ _ _
    have hd : dist x.2 x'.2 ≤ dist x x' := by rw [Prod.dist_eq]; exact le_max_right _ _
    rw [Real.dist_eq] at hd; exact this.trans hd
  have e1 : m.1 - (cl x).1 ≤ |(cl x).1 - (cl x').1| := by
    simp only [m]; rcases le_total (cl x).1 (cl x').1 with h | h
    · rw [max_eq_right h, abs_sub_comm, abs_of_nonneg (by linarith)]
    · rw [max_eq_left h]; simp
  have e2 : m.2 - (cl x).2 ≤ |(cl x).2 - (cl x').2| := by
    simp only [m]; rcases le_total (cl x).2 (cl x').2 with h | h
    · rw [max_eq_right h, abs_sub_comm, abs_of_nonneg (by linarith)]
    · rw [max_eq_left h]; simp
  have e3 : m.1 - (cl x').1 ≤ |(cl x).1 - (cl x').1| := by
    simp only [m]; rcases le_total (cl x).1 (cl x').1 with h | h
    · rw [max_eq_right h]; simp
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]
  have e4 : m.2 - (cl x').2 ≤ |(cl x).2 - (cl x').2| := by
    simp only [m]; rcases le_total (cl x).2 (cl x').2 with h | h
    · rw [max_eq_right h]; simp
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]
  rw [Real.dist_eq, abs_le]
  push_cast
  constructor <;> linarith [a.1, a.2, b.1, b.2]

lemma reg_continuous (h : RegHyp F) (y : ℝ × ℝ) : Continuous (fun x => reg F x y) := by
  have : (fun x => reg F x y) = fun x => reg F (cl x) y := by
    funext x; rw [reg_cl]
  rw [this]
  refine (clamp_lip (fun x => reg F x y) fun x x' h1 h2 h3 h4 => reg_lip h x x' y h1 h2 h3 h4).continuous

lemma F_continuous (h : RegHyp F) (c : ℝ × ℝ) (hc1 : 0 ≤ c.1) (hc2 : 0 ≤ c.2) :
    Continuous (fun x => F (cl x) c) :=
  (clamp_lip (fun x => F x c) fun x x' h1 h2 h3 h4 => h.lip x x' c h1 h2 h3 h4 hc1 hc2).continuous

lemma reg_measurable (h : RegHyp F) :
    Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => reg F p.1 p.2) := by
  classical
  refine Measurable.iSup fun q => ?_
  have hs : MeasurableSet {p : (ℝ × ℝ) × (ℝ × ℝ) | Valid q p.2} := by
    simp only [Valid]
    refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      ((measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)).inter
        (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))))
  have m2 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => F (cl p.1) 0) :=
    (F_continuous h (0 : ℝ × ℝ) le_rfl le_rfl).measurable.comp measurable_fst
  by_cases hq : 0 ≤ (q.1 : ℝ) ∧ 0 ≤ (q.2 : ℝ)
  · have m1 : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => F (cl p.1) ((q.1 : ℝ), (q.2 : ℝ))) :=
      (F_continuous h ((q.1 : ℝ), (q.2 : ℝ)) hq.1 hq.2).measurable.comp measurable_fst
    show Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => term F p.1 p.2 q
    unfold term
    exact Measurable.ite hs m1 m2
  · have : (fun p : (ℝ × ℝ) × (ℝ × ℝ) => term F p.1 p.2 q) = fun p => F (cl p.1) 0 := by
      funext p; simp only [term]; rw [if_neg (fun hv => hq ⟨hv.1, hv.2.1⟩)]
    rw [this]; exact m2

/-- The regularization is the left limit along the diagonal. -/
lemma reg_tendsto (h : RegHyp F) (x y : ℝ × ℝ) (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2) (hy1 : 0 < y.1)
    (hy2 : 0 < y.2) :
    Tendsto (fun ε : ℝ => F x (y.1 - ε, y.2 - ε)) (𝓝[>] 0) (𝓝 (reg F x y)) := by
  classical
  have ex : cl x = x := cl_of_nn x hx1 hx2
  have hm : 0 < min y.1 y.2 := lt_min hy1 hy2
  -- values lie below `reg`
  have hle : ∀ ε, 0 < ε → F x (y.1 - ε, y.2 - ε) ≤ reg F x y ∨ ¬ (ε < min y.1 y.2) := by
    intro ε hε
    by_cases he : ε < min y.1 y.2
    · left
      have e1 : ε < y.1 := he.trans_le (min_le_left _ _)
      have e2 : ε < y.2 := he.trans_le (min_le_right _ _)
      obtain ⟨q1, hq1, hq1'⟩ := exists_rat_btwn (show y.1 - ε < y.1 by linarith)
      obtain ⟨q2, hq2, hq2'⟩ := exists_rat_btwn (show y.2 - ε < y.2 by linarith)
      have hv : Valid (q1, q2) y :=
        ⟨show (0:ℝ) ≤ (q1:ℝ) by linarith, show (0:ℝ) ≤ (q2:ℝ) by linarith, hq1', hq2'⟩
      have := valid_le_reg h x y (q1, q2) hv
      rw [ex] at this
      exact (h.mono x (y.1 - ε, y.2 - ε) ((q1 : ℝ), (q2 : ℝ)) hx1 hx2 (by simp; linarith)
        (by simp; linarith) hq1.le hq2.le).trans this
    · right; exact he
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨q, hq⟩ := exists_lt_of_lt_ciSup (show a < ⨆ q, term F x y q from ha)
    unfold term at hq
    rw [ex] at hq
    split_ifs at hq with hv
    · have g1 : 0 < y.1 - q.1 := by linarith [hv.2.2.1]
      have g2 : 0 < y.2 - q.2 := by linarith [hv.2.2.2]
      filter_upwards [Ioo_mem_nhdsGT (lt_min g1 g2)] with ε hε
      have := h.mono x ((q.1 : ℝ), (q.2 : ℝ)) (y.1 - ε, y.2 - ε) hx1 hx2 hv.1 hv.2.1
        (by simp; linarith [hε.2.trans_le (min_le_left _ _)])
        (by simp; linarith [hε.2.trans_le (min_le_right _ _)])
      exact hq.trans_le this
    · filter_upwards [Ioo_mem_nhdsGT hm] with ε hε
      have := h.mono x 0 (y.1 - ε, y.2 - ε) hx1 hx2 le_rfl le_rfl
        (by simp; linarith [hε.2.trans_le (min_le_left _ _)])
        (by simp; linarith [hε.2.trans_le (min_le_right _ _)])
      exact hq.trans_le this
  · intro a ha
    filter_upwards [Ioo_mem_nhdsGT hm] with ε hε
    rcases hle ε hε.1 with h' | h'
    · exact h'.trans_lt ha
    · exact absurd hε.2 h'

lemma reg_meas_y (h : RegHyp F) (x : ℝ × ℝ) : Measurable (fun y => reg F x y) :=
  (reg_measurable h).comp (measurable_const.prodMk measurable_id)

lemma shear_mp : MeasurePreserving (fun z : ℝ × ℝ => (z.2 + z.1, z.2)) volume volume := by
  have h1 := Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
  have h2 := measurePreserving_prod_add (volume : Measure ℝ) (volume : Measure ℝ)
  rw [Measure.volume_eq_prod]
  exact h1.comp (h2.comp h1)

/-- For fixed `x`, the regularization agrees with `F x` off a null set of the open quadrant. -/
lemma reg_null (h : RegHyp F) (x : ℝ × ℝ) (hx1 : 0 ≤ x.1) (hx2 : 0 ≤ x.2) :
    (volume : Measure (ℝ × ℝ)) {y | 0 < y.1 ∧ 0 < y.2 ∧ reg F x y ≠ F x y} = 0 := by
  classical
  have ex : cl x = x := cl_of_nn x hx1 hx2
  let regp : ℝ × ℝ → ℝ := fun y : ℝ × ℝ => ⨅ n : ℕ, reg F x (y.1 + 1 / ((n : ℝ) + 1), y.2 + 1 / ((n : ℝ) + 1))
  have hbddp : ∀ y : ℝ × ℝ, BddBelow (Set.range fun n : ℕ =>
      reg F x (y.1 + 1 / ((n : ℝ) + 1), y.2 + 1 / ((n : ℝ) + 1))) := by
    intro y; exact ⟨F (cl x) 0, by rintro _ ⟨n, rfl⟩; exact base_le_reg h x _⟩
  let E : Set (ℝ × ℝ) := {y | 0 < y.1 ∧ 0 < y.2 ∧ reg F x y < regp y}
  have hEm : MeasurableSet E := by
    refine (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd).inter (measurableSet_lt (reg_meas_y h x) ?_))
    exact Measurable.iInf fun n => (reg_meas_y h x).comp
      ((measurable_fst.add_const _).prodMk (measurable_snd.add_const _))
  have hsub : {y : ℝ × ℝ | 0 < y.1 ∧ 0 < y.2 ∧ reg F x y ≠ F x y} ⊆ E := by
    rintro y ⟨y1, y2, hne⟩
    refine ⟨y1, y2, ?_⟩
    have ey : cl y = y := cl_of_nn y y1.le y2.le
    have a : reg F x y ≤ F x y := by have := reg_le h x y; rwa [ex, ey] at this
    have b : F x y ≤ regp y := by
      refine le_ciInf fun n => ?_
      have hd : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨q1, hq1, hq1'⟩ := exists_rat_btwn (show y.1 < y.1 + 1 / ((n : ℝ) + 1) by linarith)
      obtain ⟨q2, hq2, hq2'⟩ := exists_rat_btwn (show y.2 < y.2 + 1 / ((n : ℝ) + 1) by linarith)
      have hv : Valid (q1, q2) (y.1 + 1 / ((n : ℝ) + 1), y.2 + 1 / ((n : ℝ) + 1)) :=
        ⟨show (0:ℝ) ≤ (q1:ℝ) by linarith, show (0:ℝ) ≤ (q2:ℝ) by linarith, hq1', hq2'⟩
      have := valid_le_reg h x _ (q1, q2) hv
      rw [ex] at this
      exact (h.mono x y ((q1 : ℝ), (q2 : ℝ)) hx1 hx2 y1.le y2.le hq1.le hq2.le).trans this
    exact lt_of_le_of_ne a hne |>.trans_le b
  refine measure_mono_null hsub ?_
  rw [← shear_mp.measure_preimage hEm.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.measure_prod_null (hEm.preimage shear_mp.measurable)]
  refine Filter.Eventually.of_forall fun c => ?_
  simp only [Pi.zero_apply]
  let hc : ℝ → ℝ := fun l => F x (cl (l + c, l))
  have hmono : Monotone hc := by
    intro l l' hl
    exact h.mono x _ _ hx1 hx2 (cl_nn _).1 (cl_nn _).2
      (max_le_max (by simp only; linarith) le_rfl) (max_le_max hl le_rfl)
  refine Set.Countable.measure_zero ((hmono.countable_not_continuousAt).mono ?_) _
  intro l hl hcont
  simp only [Set.mem_preimage, E, Set.mem_setOf_eq] at hl
  obtain ⟨p1, p2, hlt⟩ := hl
  set y : ℝ × ℝ := (l + c, l) with hy
  -- `reg F x y = hc l`
  have t1 := reg_tendsto h x y hx1 hx2 p1 p2
  have t2 : Tendsto (fun ε : ℝ => hc (l - ε)) (𝓝[>] 0) (𝓝 (hc l)) := by
    have : Tendsto (fun ε : ℝ => l - ε) (𝓝[>] 0) (𝓝 l) := by
      have h0 : Continuous (fun ε : ℝ => l - ε) := continuous_const.sub continuous_id
      have := (h0.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    exact hcont.tendsto.comp this
  have t3 : Tendsto (fun ε : ℝ => F x (y.1 - ε, y.2 - ε)) (𝓝[>] 0) (𝓝 (hc l)) := by
    refine t2.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min p1 p2)] with ε hε
    have e1 : ε < y.1 := hε.2.trans_le (min_le_left _ _)
    have e2 : ε < y.2 := hε.2.trans_le (min_le_right _ _)
    simp only [hc, y] at e1 e2 ⊢
    rw [cl_of_nn _ (by simp; linarith) (by simp; linarith)]
    congr 1; ext <;> simp; ring
  have heq : reg F x y = hc l := tendsto_nhds_unique t1 t3
  -- `regp y ≤ hc l`
  have t4 : Tendsto (fun n : ℕ => hc (l + 1 / ((n : ℝ) + 1))) atTop (𝓝 (hc l)) := by
    have h0 : Continuous (fun d : ℝ => l + d) := continuous_const.add continuous_id
    have := (h0.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simp only [add_zero] at this
    exact hcont.tendsto.comp this
  have hp : regp y ≤ hc l := by
    refine ge_of_tendsto' t4 fun n => ?_
    refine (ciInf_le (hbddp y) n).trans ?_
    refine (reg_le h x _).trans_eq ?_
    simp only [hc, y, ex]
    congr 2; ext <;> simp; ring
  linarith

/-- Off a null set of the open quadrant, the regularization agrees with `F` for every `x ≥ 0`. -/
theorem reg_ae (h : RegHyp F) :
    ∀ᵐ y ∂((volume : Measure (ℝ × ℝ)).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))),
      ∀ x : ℝ × ℝ, 0 ≤ x.1 → 0 ≤ x.2 → reg F x y = F x y := by
  have hI : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hq : ∀ q : ℚ × ℚ, ∀ᵐ y ∂((volume : Measure (ℝ × ℝ)).restrict
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))),
      0 ≤ (q.1 : ℝ) → 0 ≤ (q.2 : ℝ) → reg F ((q.1 : ℝ), (q.2 : ℝ)) y = F ((q.1 : ℝ), (q.2 : ℝ)) y := by
    intro q
    by_cases hq : 0 ≤ (q.1 : ℝ) ∧ 0 ≤ (q.2 : ℝ)
    · refine (ae_restrict_iff' hI).2 ?_
      refine measure_mono_null ?_ (reg_null h ((q.1 : ℝ), (q.2 : ℝ)) hq.1 hq.2)
      intro y hy
      have hy' : ¬ (y ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) → 0 ≤ (q.1 : ℝ) → 0 ≤ (q.2 : ℝ) →
          reg F ((q.1 : ℝ), (q.2 : ℝ)) y = F ((q.1 : ℝ), (q.2 : ℝ)) y) := hy
      simp only [_root_.not_imp] at hy'
      obtain ⟨⟨a, b⟩, -, -, hne⟩ := hy'
      exact ⟨a, b, hne⟩
    · exact Filter.Eventually.of_forall fun y h1 h2 => absurd ⟨h1, h2⟩ hq
  rw [← ae_all_iff] at hq
  filter_upwards [hq, ae_restrict_mem hI] with y hy hyI x hx1 hx2
  have y1 : 0 ≤ y.1 := hyI.1.le
  have y2 : 0 ≤ y.2 := hyI.2.le
  have key : ∀ η > 0, |reg F x y - F x y| < 4 * η := by
    intro η hη
    obtain ⟨q1, hq1, hq1'⟩ := exists_rat_btwn (show x.1 < x.1 + η by linarith)
    obtain ⟨q2, hq2, hq2'⟩ := exists_rat_btwn (show x.2 < x.2 + η by linarith)
    have e := hy (q1, q2) (by simp only; linarith) (by simp only; linarith)
    have r := reg_lip h x ((q1 : ℝ), (q2 : ℝ)) y hx1 hx2 hq1.le hq2.le
    have f := h.lip x ((q1 : ℝ), (q2 : ℝ)) y hx1 hx2 hq1.le hq2.le y1 y2
    simp only at e r f
    rw [abs_lt]; constructor <;> linarith
  by_contra hne
  have hpos : 0 < |reg F x y - F x y| := abs_pos.2 (sub_ne_zero.2 hne)
  have := key (|reg F x y - F x y| / 8) (by positivity)
  linarith

end FracTruthSched.Dev.Reg
end

section
/-!
# Lemma 2 (b): two-task separation almost everywhere

STATUS: complete, no sorry (q407, 2026-11-20). `idelta_small` is proved via `shift_err`/`pair_bounds`/
`idelta_sub`; `versions` (paper Appendix B) via the lower regularization `Reg.reg` (sup over rational
points strictly below; Borel, equal to the left diagonal limit, and equal to `W` off a null set by
the countability of discontinuities of a monotone function along each diagonal line).
Everything else is proved: mechanism side (`sepdata`: Lipschitz/monotone/complementarity/axis
identities from truthfulness, eligibility, zero-type irrelevance and `lemma_4`), `separation`,
`pair_laplace`, `idelta_limit`, `laplace_vanish` (via `lemma_10`), `ae_to_all`, `chk_lemma_2b`.
-/

set_option autoImplicit false

namespace FracTruthSched.Dev.L2b
open FracTruthSched MeasureTheory

/-- The abstract interface: two functions `W t s` (machine `i`'s full disutility, own values `t`,
opposing values `s`) and `Wj t s` (machine `j`'s full disutility; own values `s`, opposing `t`). -/
structure SepData (W Wj : ℝ × ℝ → ℝ × ℝ → ℝ) : Prop where
  mono1 : ∀ (a b t2 : ℝ) (s : ℝ × ℝ), 0 ≤ a → a ≤ b → 0 ≤ t2 → 0 ≤ s.1 → 0 ≤ s.2 →
    0 ≤ W (b, t2) s - W (a, t2) s ∧ W (b, t2) s - W (a, t2) s ≤ b - a
  mono2 : ∀ (a b t1 : ℝ) (s : ℝ × ℝ), 0 ≤ a → a ≤ b → 0 ≤ t1 → 0 ≤ s.1 → 0 ≤ s.2 →
    0 ≤ W (t1, b) s - W (t1, a) s ∧ W (t1, b) s - W (t1, a) s ≤ b - a
  monoj1 : ∀ (a b s2 : ℝ) (t : ℝ × ℝ), 0 ≤ a → a ≤ b → 0 ≤ s2 → 0 ≤ t.1 → 0 ≤ t.2 →
    0 ≤ Wj t (b, s2) - Wj t (a, s2) ∧ Wj t (b, s2) - Wj t (a, s2) ≤ b - a
  monoj2 : ∀ (a b s1 : ℝ) (t : ℝ × ℝ), 0 ≤ a → a ≤ b → 0 ≤ s1 → 0 ≤ t.1 → 0 ≤ t.2 →
    0 ≤ Wj t (s1, b) - Wj t (s1, a) ∧ Wj t (s1, b) - Wj t (s1, a) ≤ b - a
  mono_s : ∀ (t s s' : ℝ × ℝ), 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → s.1 ≤ s'.1 → s.2 ≤ s'.2 →
    W t s ≤ W t s'
  mono_tj : ∀ (t t' s : ℝ × ℝ), 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → t.1 ≤ t'.1 → t.2 ≤ t'.2 →
    Wj t s ≤ Wj t' s
  pairF1 : ∀ (t s : ℝ × ℝ) (δ : ℝ), 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → 0 < δ →
    (W (t.1 + δ, t.2) s - W t s) + (Wj t (s.1 + δ, s.2) - Wj t s) ≤ δ
  pairF2 : ∀ (t s : ℝ × ℝ) (δ : ℝ), 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → 0 < δ →
    (W (t.1, t.2 + δ) s - W t s) + (Wj t (s.1, s.2 + δ) - Wj t s) ≤ δ
  pairB1 : ∀ (t s : ℝ × ℝ) (δ : ℝ), 0 ≤ t.2 → 0 ≤ s.2 → 0 < δ → δ ≤ t.1 → δ ≤ s.1 →
    δ ≤ (W t s - W (t.1 - δ, t.2) s) + (Wj t s - Wj t (s.1 - δ, s.2))
  pairB2 : ∀ (t s : ℝ × ℝ) (δ : ℝ), 0 ≤ t.1 → 0 ≤ s.1 → 0 < δ → δ ≤ t.2 → δ ≤ s.2 →
    δ ≤ (W t s - W (t.1, t.2 - δ) s) + (Wj t s - Wj t (s.1, s.2 - δ))
  ax1 : ∀ (t1 : ℝ) (s : ℝ × ℝ), 0 ≤ t1 → 0 ≤ s.1 → 0 ≤ s.2 →
    W (t1, 0) s - W (0, 0) s = W (t1, 0) (s.1, 0) - W (0, 0) (s.1, 0)
  ax2 : ∀ (t2 : ℝ) (s : ℝ × ℝ), 0 ≤ t2 → 0 ≤ s.1 → 0 ≤ s.2 →
    W (0, t2) s - W (0, 0) s = W (0, t2) (0, s.2) - W (0, 0) (0, s.2)
  ax3 : ∀ (t : ℝ × ℝ) (s1 : ℝ), 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s1 →
    Wj t (s1, 0) - Wj t (0, 0) = Wj (t.1, 0) (s1, 0) - Wj (t.1, 0) (0, 0)
  ax4 : ∀ (t : ℝ × ℝ) (s2 : ℝ), 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s2 →
    Wj t (0, s2) - Wj t (0, 0) = Wj (0, t.2) (0, s2) - Wj (0, t.2) (0, 0)

/-! ### Laplace step in `Fin 4 → ℝ` coordinates -/

/-- Laplace transform on the orthant of `Fin 4 → ℝ`. -/
noncomputable def J (F : (Fin 4 → ℝ) → ℝ) (θ : Fin 4 → ℝ) : ℝ :=
  ∫ r in Set.Ici (0 : Fin 4 → ℝ), F r * Real.exp (-∑ ν, θ ν * r ν)

lemma restrict_Ici_pi :
    (volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici (0 : Fin 4 → ℝ)) =
      Measure.pi (fun _ : Fin 4 => (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) := by
  rw [← Measure.restrict_pi_pi, ← volume_pi]
  congr 1
  ext r
  simp [Pi.le_def]

lemma exp_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-b * x)) ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))) := by
  have := exp_neg_integrableOn_Ioi 0 hb
  exact (integrableOn_Ici_iff_integrableOn_Ioi (by simp)).2 this

lemma bound_integrable (c : Fin 4 → ℝ) (hc : ∀ ν, 0 < c ν) :
    Integrable (fun r : Fin 4 → ℝ => (∑ ν, r ν) * Real.exp (-∑ ν, c ν * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici (0 : Fin 4 → ℝ))) := by
  set K : ℝ := ∑ ν, 2 / c ν with hK
  have hint : Integrable (fun r : Fin 4 → ℝ => K * Real.exp (-∑ ν, (c ν / 2) * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici (0 : Fin 4 → ℝ))) := by
    rw [restrict_Ici_pi]
    refine Integrable.const_mul ?_ K
    have := Integrable.fintype_prod (𝕜 := ℝ)
      (f := fun (ν : Fin 4) (x : ℝ) => Real.exp (-(c ν / 2) * x))
      (μ := fun _ => (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))
      (fun ν => exp_integrable _ (by have := hc ν; positivity))
    refine this.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    ring
  refine hint.mono' ?_ ?_
  · refine (Finset.measurable_sum _ fun ν _ => measurable_pi_apply ν).aestronglyMeasurable.mul ?_
    exact (Real.measurable_exp.comp (Finset.measurable_sum _ fun ν _ =>
      (measurable_pi_apply ν).const_mul _).neg).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Set.Ici (0 : Fin 4 → ℝ)))]
      with r hr
    have hr' : ∀ ν, 0 ≤ r ν := fun ν => hr ν
    set T : ℝ := ∑ ν, (c ν / 2) * r ν with hT
    have hT0 : 0 ≤ T := Finset.sum_nonneg fun ν _ => by have := hc ν; have := hr' ν; positivity
    have h2 : ∑ ν, c ν * r ν = 2 * T := by
      rw [hT, Finset.mul_sum]; refine Finset.sum_congr rfl fun ν _ => ?_; ring
    have hrle : ∀ ν, r ν ≤ 2 / c ν * Real.exp T := by
      intro ν
      have hcν := hc ν
      have hy : (c ν / 2) * r ν ≤ T :=
        Finset.single_le_sum (f := fun ν => (c ν / 2) * r ν)
          (fun k _ => by have := hc k; have := hr' k; positivity) (Finset.mem_univ ν)
      have hexp : T ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
      have : r ν = 2 / c ν * ((c ν / 2) * r ν) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left (hy.trans hexp) (by positivity)
    have hsum : ∑ ν, r ν ≤ K * Real.exp T := by
      rw [hK, Finset.sum_mul]
      exact Finset.sum_le_sum fun ν _ => hrle ν
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Finset.sum_nonneg fun ν _ => hr' ν)
      (Real.exp_pos _).le), h2]
    have hE : Real.exp (-∑ ν, (c ν / 2) * r ν) = Real.exp (-T) := rfl
    rw [hE]
    calc (∑ ν, r ν) * Real.exp (-(2 * T)) ≤ K * Real.exp T * Real.exp (-(2 * T)) :=
          mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
      _ = K * Real.exp (-T) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma J_continuousAt (F : (Fin 4 → ℝ) → ℝ)
    (hF : AEStronglyMeasurable F ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)))
    (hg : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |F r| ≤ ∑ ν, r ν) (θ₀ : Fin 4 → ℝ)
    (hθ : ∀ ν, 0 < θ₀ ν) : ContinuousAt (J F) θ₀ := by
  unfold J
  refine continuousAt_of_dominated (bound := fun r : Fin 4 → ℝ =>
    (∑ ν, r ν) * Real.exp (-∑ ν, (θ₀ ν / 2) * r ν)) ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun θ => ?_
    refine hF.mul ?_
    exact (Real.continuous_exp.comp (continuous_neg.comp (continuous_finset_sum _ fun ν _ =>
      continuous_const.mul (continuous_apply ν)))).aestronglyMeasurable
  · have hev : ∀ᶠ θ in nhds θ₀, ∀ ν, θ₀ ν / 2 < θ ν := by
      rw [Filter.eventually_all]
      intro ν
      exact (continuous_apply ν).continuousAt.eventually (lt_mem_nhds (by have := hθ ν; linarith))
    filter_upwards [hev] with θ hθ'
    filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Set.Ici (0 : Fin 4 → ℝ)))]
      with r hr
    have hr' : ∀ ν, 0 ≤ r ν := fun ν => hr ν
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul (hg r hr) ?_ (Real.exp_pos _).le (Finset.sum_nonneg fun ν _ => hr' ν)
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    exact Finset.sum_le_sum fun ν _ => mul_le_mul_of_nonneg_right (hθ' ν).le (hr' ν)
  · exact bound_integrable (fun ν => θ₀ ν / 2) (fun ν => by have := hθ ν; positivity)
  · refine Filter.Eventually.of_forall fun r => ?_
    refine ContinuousAt.mul continuousAt_const ?_
    exact (Real.continuous_exp.comp (continuous_neg.comp (continuous_finset_sum _ fun ν _ =>
      (continuous_apply ν).mul continuous_const))).continuousAt

theorem laplace_fin4 (F G : (Fin 4 → ℝ) → ℝ)
    (hF : AEStronglyMeasurable F ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)))
    (hG : AEStronglyMeasurable G ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)))
    (hgF : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |F r| ≤ ∑ ν, r ν)
    (hgG : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |G r| ≤ ∑ ν, r ν)
    (hrel : ∀ θ : Fin 4 → ℝ, (∀ ν, 0 < θ ν) →
      θ 0 * J F θ + θ 2 * J G θ = 0 ∧ θ 1 * J F θ + θ 3 * J G θ = 0) :
    F =ᵐ[(volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)] 0 := by
  have hdet : ∀ θ : Fin 4 → ℝ, (∀ ν, 0 < θ ν) → θ 0 * θ 3 - θ 1 * θ 2 ≠ 0 → J F θ = 0 := by
    intro θ hθ hd
    obtain ⟨h1, h2⟩ := hrel θ hθ
    have : (θ 0 * θ 3 - θ 1 * θ 2) * J F θ = 0 := by linear_combination θ 3 * h1 - θ 2 * h2
    exact (mul_eq_zero.1 this).resolve_left hd
  have hall : ∀ θ : Fin 4 → ℝ, (∀ ν, 0 < θ ν) → J F θ = 0 := by
    intro θ hθ
    have hcont := J_continuousAt F hF hgF θ hθ
    set d : ℝ := θ 0 * θ 3 - θ 1 * θ 2 with hd
    set c : ℝ := -d / θ 0 with hc
    have hθ0 := hθ 0
    let path : ℝ → Fin 4 → ℝ := fun ε => Function.update θ 3 (θ 3 + ε)
    have hpath : Filter.Tendsto path (nhds 0) (nhds θ) := by
      have : Continuous path := continuous_const.update 3 (continuous_const.add continuous_id)
      have h0 : path 0 = θ := by simp [path]
      simpa [h0] using this.tendsto 0
    have hT : Filter.Tendsto (fun ε => J F (path ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (J F θ)) :=
      (hcont.tendsto.comp hpath).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), J F (path ε) = 0 := by
      have hI : Set.Ioo (0 : ℝ) (if 0 < c then c else 1) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
        refine Ioo_mem_nhdsGT ?_
        split_ifs with h
        · exact h
        · exact one_pos
      filter_upwards [hI, self_mem_nhdsWithin] with ε hε hε0
      refine hdet (path ε) ?_ ?_
      · intro ν
        by_cases hν : ν = 3
        · subst hν; simp [path]; have := hθ 3; have : (0:ℝ) < ε := hε0; linarith
        · simp [path, hν, hθ ν]
      · simp only [path]
        have h0 : (3 : Fin 4) ≠ 0 := by decide
        have h1 : (3 : Fin 4) ≠ 1 := by decide
        have h2 : (3 : Fin 4) ≠ 2 := by decide
        simp only [Function.update_self, Function.update_of_ne h0.symm, Function.update_of_ne h1.symm,
          Function.update_of_ne h2.symm]
        intro hz
        have : θ 0 * ε = -d := by rw [hd]; linarith
        have hεc : ε = c := by rw [hc]; field_simp; linarith
        have hεc' : ε < c := by
          have := hε.2
          split_ifs at this with h
          · exact this
          · exfalso; have : 0 < ε := hε.1; have : c ≤ 0 := not_lt.1 h; linarith
        linarith
    exact tendsto_nhds_unique hT (tendsto_const_nhds.congr' (hev.mono fun ε h => h.symm))
  refine lemma_10 F hF hgF ?_
  intro θ hθ
  exact hall θ hθ

/-- The closed orthant of `(t, s) ∈ ℝ² × ℝ²`. -/
def Qset : Set ((ℝ × ℝ) × (ℝ × ℝ)) := Set.Ici (0 : ℝ × ℝ) ×ˢ Set.Ici (0 : ℝ × ℝ)

/-- Laplace transform over the orthant with rates `α` (own values) and `γ` (opposing values). -/
noncomputable def lap (F : ℝ × ℝ → ℝ × ℝ → ℝ) (α γ : ℝ × ℝ) : ℝ :=
  ∫ p in Qset, F p.1 p.2 *
    Real.exp (-(α.1 * p.1.1 + α.2 * p.1.2 + γ.1 * p.2.1 + γ.2 * p.2.2))

/-- Translation formula for the Laplace integral in `Fin 4 → ℝ` coordinates. -/
theorem shift_fin4 (z : (Fin 4 → ℝ) → ℝ) (θ v : Fin 4 → ℝ) (hv : 0 ≤ v)
    (hint : Integrable (fun r => z r * Real.exp (-∑ ν, θ ν * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0))) :
    ∫ r in Set.Ici (0 : Fin 4 → ℝ), z (r + v) * Real.exp (-∑ ν, θ ν * r ν) =
      Real.exp (∑ ν, θ ν * v ν) *
        ((∫ r in Set.Ici (0 : Fin 4 → ℝ), z r * Real.exp (-∑ ν, θ ν * r ν)) -
          ∫ r in Set.Ici (0 : Fin 4 → ℝ) \ Set.Ici v, z r * Real.exp (-∑ ν, θ ν * r ν)) := by
  have hsub : Set.Ici v ⊆ Set.Ici (0 : Fin 4 → ℝ) := Set.Ici_subset_Ici.2 hv
  let g : (Fin 4 → ℝ) → ℝ := (Set.Ici v).indicator
    (fun r => Real.exp (∑ ν, θ ν * v ν) * (z r * Real.exp (-∑ ν, θ ν * r ν)))
  have h1 : ∫ r in Set.Ici (0 : Fin 4 → ℝ), z (r + v) * Real.exp (-∑ ν, θ ν * r ν) =
      ∫ r, g (r + v) := by
    rw [← integral_indicator measurableSet_Ici]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [g, Set.indicator, Set.mem_Ici]
    have hiff : v ≤ r + v ↔ 0 ≤ r := by
      constructor
      · intro h; simpa using h
      · intro h; simpa using h
    by_cases hr : (0 : Fin 4 → ℝ) ≤ r
    · rw [if_pos (show r ∈ Set.Ici (0 : Fin 4 → ℝ) from hr),
        if_pos (show r + v ∈ Set.Ici v from hiff.2 hr)]
      have : ∑ ν, θ ν * (r + v) ν = ∑ ν, θ ν * r ν + ∑ ν, θ ν * v ν := by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun ν _ => ?_
        simp [mul_add]
      have h2 : Real.exp (∑ ν, θ ν * v ν) * Real.exp (-∑ ν, θ ν * v ν) = 1 := by
        rw [← Real.exp_add]; simp
      rw [this, neg_add, Real.exp_add]
      linear_combination (-(z (r + v) * Real.exp (-∑ ν, θ ν * r ν))) * h2
    · rw [if_neg (show r ∉ Set.Ici (0 : Fin 4 → ℝ) from hr),
        if_neg (show r + v ∉ Set.Ici v from fun h => hr (hiff.1 h))]
  rw [h1, integral_add_right_eq_self g v, integral_indicator measurableSet_Ici,
    integral_const_mul]
  congr 1
  rw [setIntegral_diff measurableSet_Ici hint hsub, sub_sub_cancel]

lemma shift_ptwise (z : (Fin 4 → ℝ) → ℝ) (θ v : Fin 4 → ℝ) (r : Fin 4 → ℝ) :
    (Set.Ici (0 : Fin 4 → ℝ)).indicator (fun r => z (r + v) * Real.exp (-∑ ν, θ ν * r ν)) r =
      (Set.Ici v).indicator
        (fun r => Real.exp (∑ ν, θ ν * v ν) * (z r * Real.exp (-∑ ν, θ ν * r ν))) (r + v) := by
  simp only [Set.indicator, Set.mem_Ici]
  have hiff : v ≤ r + v ↔ 0 ≤ r := by
    constructor
    · intro h; simpa using h
    · intro h; simpa using h
  by_cases hr : (0 : Fin 4 → ℝ) ≤ r
  · rw [if_pos (show r ∈ Set.Ici (0 : Fin 4 → ℝ) from hr),
      if_pos (show r + v ∈ Set.Ici v from hiff.2 hr)]
    have : ∑ ν, θ ν * (r + v) ν = ∑ ν, θ ν * r ν + ∑ ν, θ ν * v ν := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun ν _ => ?_
      simp [mul_add]
    have h2 : Real.exp (∑ ν, θ ν * v ν) * Real.exp (-∑ ν, θ ν * v ν) = 1 := by
      rw [← Real.exp_add]; simp
    rw [this, neg_add, Real.exp_add]
    linear_combination (-(z (r + v) * Real.exp (-∑ ν, θ ν * r ν))) * h2
  · rw [if_neg (show r ∉ Set.Ici (0 : Fin 4 → ℝ) from hr),
      if_neg (show r + v ∉ Set.Ici v from fun h => hr (hiff.1 h))]

lemma shift_integrable (z : (Fin 4 → ℝ) → ℝ) (θ v : Fin 4 → ℝ) (hv : 0 ≤ v)
    (hint : Integrable (fun r => z r * Real.exp (-∑ ν, θ ν * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0))) :
    Integrable (fun r => z (r + v) * Real.exp (-∑ ν, θ ν * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)) := by
  have hsub : Set.Ici v ⊆ Set.Ici (0 : Fin 4 → ℝ) := Set.Ici_subset_Ici.2 hv
  have h1 : IntegrableOn (fun r => z r * Real.exp (-∑ ν, θ ν * r ν)) (Set.Ici v) :=
    IntegrableOn.mono_set hint hsub
  have hg : Integrable ((Set.Ici v).indicator
      (fun r => Real.exp (∑ ν, θ ν * v ν) * (z r * Real.exp (-∑ ν, θ ν * r ν)))) :=
    (integrable_indicator_iff measurableSet_Ici).2 (h1.const_mul _)
  refine (integrable_indicator_iff (measurableSet_Ici : MeasurableSet (Set.Ici (0 : Fin 4 → ℝ)))).1 ?_
  have : (Set.Ici (0 : Fin 4 → ℝ)).indicator
      (fun r => z (r + v) * Real.exp (-∑ ν, θ ν * r ν)) = fun r =>
      (Set.Ici v).indicator
        (fun r => Real.exp (∑ ν, θ ν * v ν) * (z r * Real.exp (-∑ ν, θ ν * r ν))) (r + v) :=
    funext (shift_ptwise z θ v)
  rw [this]
  exact hg.comp_add_right v

lemma exp_integrable4 (θ : Fin 4 → ℝ) (hθ : ∀ ν, 0 < θ ν) :
    Integrable (fun r : Fin 4 → ℝ => Real.exp (-∑ ν, θ ν * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici (0 : Fin 4 → ℝ))) := by
  rw [restrict_Ici_pi]
  have := Integrable.fintype_prod (𝕜 := ℝ)
    (f := fun (ν : Fin 4) (x : ℝ) => Real.exp (-θ ν * x))
    (μ := fun _ => (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))
    (fun ν => exp_integrable _ (hθ ν))
  refine this.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only
  rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- The boundary strip `{r ≥ 0, r_k < δ}`. -/
def strip (k : Fin 4) (δ : ℝ) : Set (Fin 4 → ℝ) :=
  Set.Ici (0 : Fin 4 → ℝ) \ Set.Ici (δ • Pi.single k (1 : ℝ))

lemma strip_bound (θ : Fin 4 → ℝ) (hθ : ∀ ν, 0 < θ ν) (k : Fin 4) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ →
      ∫ r in strip k δ, Real.exp (-∑ ν, θ ν * r ν) ≤ C * δ := by
  refine ⟨∏ j ∈ Finset.univ.erase k, ∫ x in Set.Ici (0 : ℝ), Real.exp (-θ j * x), ?_⟩
  intro δ hδ
  unfold strip
  let S : Fin 4 → Set ℝ := fun j => if j = k then Set.Ico (0 : ℝ) δ else Set.Ici 0
  have hsub : Set.Ici (0 : Fin 4 → ℝ) \ Set.Ici (δ • Pi.single k (1 : ℝ)) ⊆
      Set.pi Set.univ S := by
    rintro r ⟨h0, hn⟩ j _
    have h0' : ∀ i, 0 ≤ r i := fun i => h0 i
    by_cases hj : j = k
    · subst hj
      simp only [S, if_true, Set.mem_Ico]
      refine ⟨h0' j, ?_⟩
      by_contra hge
      apply hn
      intro i
      by_cases hi : i = j
      · subst hi; simpa using not_lt.1 hge
      · simp only [Pi.smul_apply, Pi.single_apply, hi, if_false, smul_zero]; exact h0' i
    · simp only [S, hj, if_false]; exact h0' j
  have hpiS : Set.pi Set.univ S ⊆ Set.Ici (0 : Fin 4 → ℝ) := by
    intro r hr j
    have := hr j (Set.mem_univ j)
    by_cases hj : j = k
    · subst hj; simp only [S, if_true, Set.mem_Ico] at this; exact this.1
    · simp only [S, hj, if_false, Set.mem_Ici] at this; exact this
  have hf : ∀ r : Fin 4 → ℝ, Real.exp (-∑ ν, θ ν * r ν) = ∏ ν, Real.exp (-θ ν * r ν) := by
    intro r
    rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun ν _ => ?_
    ring
  have hint : IntegrableOn (fun r : Fin 4 → ℝ => Real.exp (-∑ ν, θ ν * r ν))
      (Set.pi Set.univ S) := IntegrableOn.mono_set
      (exp_integrable4 θ hθ) hpiS
  calc ∫ r in Set.Ici (0 : Fin 4 → ℝ) \ Set.Ici (δ • Pi.single k (1 : ℝ)),
        Real.exp (-∑ ν, θ ν * r ν)
      ≤ ∫ r in Set.pi Set.univ S, Real.exp (-∑ ν, θ ν * r ν) :=
        by
          refine setIntegral_mono_set hint (Filter.Eventually.of_forall fun r =>
            (Real.exp_pos _).le) ?_
          exact Filter.Eventually.of_forall fun r hr => hsub hr
    _ = ∏ j, ∫ x in S j, Real.exp (-θ j * x) := by
        simp_rw [hf]
        rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod
          (f := fun (j : Fin 4) (x : ℝ) => Real.exp (-θ j * x))]
    _ ≤ (∏ j ∈ Finset.univ.erase k, ∫ x in Set.Ici (0 : ℝ), Real.exp (-θ j * x)) * δ := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), mul_comm]
        have e1 : ∏ j ∈ Finset.univ.erase k, ∫ x in S j, Real.exp (-θ j * x) =
            ∏ j ∈ Finset.univ.erase k, ∫ x in Set.Ici (0 : ℝ), Real.exp (-θ j * x) := by
          refine Finset.prod_congr rfl fun j hj => ?_
          have : j ≠ k := Finset.ne_of_mem_erase hj
          simp only [S, this, if_false]
        rw [e1]
        have hnn : 0 ≤ ∏ j ∈ Finset.univ.erase k, ∫ x in Set.Ici (0 : ℝ), Real.exp (-θ j * x) :=
          Finset.prod_nonneg fun j _ => integral_nonneg fun x => (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_left ?_ hnn
        simp only [S, if_true]
        have hn := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ))
          (s := Set.Ico (0 : ℝ) δ) (f := fun x => Real.exp (-θ k * x)) (C := 1)
          (by simp) (fun x hx => by
              rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
              have := hθ k
              exact Real.exp_le_one_iff.2 (by nlinarith [hx.1]))
        have hv : (volume : Measure ℝ).real (Set.Ico (0 : ℝ) δ) = δ := by
          simp [Measure.real, Real.volume_Ico, hδ.le]
        rw [hv, one_mul] at hn
        exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hn)

lemma strip_lt (k : Fin 4) (δ : ℝ) (r : Fin 4 → ℝ) (hr : r ∈ strip k δ) : r k < δ := by
  obtain ⟨h0, hn⟩ := hr
  have h0' : ∀ i, 0 ≤ r i := fun i => h0 i
  by_contra hge
  apply hn
  intro i
  by_cases hi : i = k
  · subst hi; simpa using not_lt.1 hge
  · simp only [Pi.smul_apply, Pi.single_apply, hi, if_false, smul_zero]; exact h0' i

lemma strip_meas (k : Fin 4) (δ : ℝ) : MeasurableSet (strip k δ) :=
  measurableSet_Ici.diff measurableSet_Ici

lemma strip_sub (k : Fin 4) (δ : ℝ) : strip k δ ⊆ Set.Ici (0 : Fin 4 → ℝ) := Set.diff_subset

lemma strip_small (z : (Fin 4 → ℝ) → ℝ) (θ : Fin 4 → ℝ) (hθ : ∀ ν, 0 < θ ν) (k : Fin 4)
    (hz : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |z r| ≤ 2 * r k) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ →
      |∫ r in strip k δ, z r * Real.exp (-∑ ν, θ ν * r ν)| ≤ C * δ ^ 2 := by
  obtain ⟨C, hC⟩ := strip_bound θ hθ k
  refine ⟨2 * C, fun δ hδ => ?_⟩
  have hw : IntegrableOn (fun r : Fin 4 → ℝ => Real.exp (-∑ ν, θ ν * r ν)) (strip k δ) :=
    IntegrableOn.mono_set (exp_integrable4 θ hθ) (strip_sub k δ)
  have hbound := norm_integral_le_of_norm_le (μ := (volume : Measure (Fin 4 → ℝ)).restrict
      (strip k δ))
    (f := fun r => z r * Real.exp (-∑ ν, θ ν * r ν))
    (g := fun r => 2 * δ * Real.exp (-∑ ν, θ ν * r ν)) (hw.const_mul (2 * δ))
    ((ae_restrict_iff' (strip_meas k δ)).2 (Filter.Eventually.of_forall fun r hr => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have h1 := hz r (strip_sub k δ hr)
      have h2 := strip_lt k δ r hr
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le))
  rw [Real.norm_eq_abs, integral_const_mul] at hbound
  have h3 := hC δ hδ
  have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ 2 * δ)
  have h5 : 2 * δ * (C * δ) = 2 * C * δ ^ 2 := by ring
  exact hbound.trans (h4.trans_eq h5)

lemma single_nonneg (k : Fin 4) (δ : ℝ) (hδ : 0 < δ) :
    (0 : Fin 4 → ℝ) ≤ δ • Pi.single k (1 : ℝ) := by
  intro i
  simp only [Pi.zero_apply, Pi.smul_apply, Pi.single_apply]
  split_ifs <;> simp [hδ.le]

lemma single_sum (θ : Fin 4 → ℝ) (k : Fin 4) (δ : ℝ) :
    ∑ ν, θ ν * (δ • Pi.single k (1 : ℝ)) ν = θ k * δ := by
  simp [Pi.single_apply]

lemma hform_lem (z : (Fin 4 → ℝ) → ℝ) (θ : Fin 4 → ℝ) (k : Fin 4)
    (hint : Integrable (fun r => z r * Real.exp (-∑ ν, θ ν * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0))) (δ : ℝ) (hδ : 0 < δ) :
    ∫ r in Set.Ici (0 : Fin 4 → ℝ),
          (z (r + δ • Pi.single k (1 : ℝ)) - z r) * Real.exp (-∑ ν, θ ν * r ν) =
        (Real.exp (θ k * δ) - 1) * J z θ - Real.exp (θ k * δ) *
          ∫ r in strip k δ, z r * Real.exp (-∑ ν, θ ν * r ν) := by
  have h1 := shift_fin4 z θ _ (single_nonneg k δ hδ) hint
  have h2 := shift_integrable z θ _ (single_nonneg k δ hδ) hint
  simp_rw [sub_mul]
  rw [integral_sub h2 hint, h1, single_sum]
  unfold J strip
  ring

lemma exp_slope (c : ℝ) :
    Filter.Tendsto (fun δ : ℝ => δ⁻¹ * (Real.exp (c * δ) - 1)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds c) := by
  have hd : HasDerivAt (fun x : ℝ => Real.exp (c * x)) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul c).exp
  have := hd.tendsto_slope_zero_right
  refine this.congr fun δ => ?_
  simp

lemma exp_lim (c : ℝ) :
    Filter.Tendsto (fun δ : ℝ => Real.exp (c * δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have : Filter.Tendsto (fun δ : ℝ => Real.exp (c * δ)) (nhds 0) (nhds (Real.exp (c * 0))) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto 0
  simpa using this.mono_left nhdsWithin_le_nhds

lemma lin_lim (C : ℝ) :
    Filter.Tendsto (fun δ : ℝ => C * δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have : Filter.Tendsto (fun δ : ℝ => C * δ) (nhds 0) (nhds (C * 0)) :=
    (continuous_const.mul continuous_id).tendsto 0
  simpa using this.mono_left nhdsWithin_le_nhds

lemma single_limit (z : (Fin 4 → ℝ) → ℝ) (θ : Fin 4 → ℝ) (hθ : ∀ ν, 0 < θ ν) (k : Fin 4)
    (hint : Integrable (fun r => z r * Real.exp (-∑ ν, θ ν * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)))
    (hz : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |z r| ≤ 2 * r k) :
    Filter.Tendsto (fun δ : ℝ => δ⁻¹ *
      (∫ r in Set.Ici (0 : Fin 4 → ℝ),
        (z (r + δ • Pi.single k (1 : ℝ)) - z r) * Real.exp (-∑ ν, θ ν * r ν)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (θ k * J z θ)) := by
  obtain ⟨C, hC⟩ := strip_small z θ hθ k hz
  have hstrip : Filter.Tendsto (fun δ : ℝ => δ⁻¹ *
      ∫ r in strip k δ, z r * Real.exp (-∑ ν, θ ν * r ν)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
    refine squeeze_zero_norm' ?_ (lin_lim C)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : 0 < δ := hδ
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hδ']
    have h1 := mul_le_mul_of_nonneg_left (hC δ hδ') (inv_nonneg.2 hδ'.le)
    have h2 : δ⁻¹ * (C * δ ^ 2) = C * δ := by
      have := hδ'.ne'
      field_simp
    exact h1.trans_eq h2
  have hlim := ((exp_slope (θ k)).mul_const (J z θ)).sub ((exp_lim (θ k)).mul hstrip)
  have hlim' : Filter.Tendsto (fun δ : ℝ => δ⁻¹ * (Real.exp (θ k * δ) - 1) * J z θ -
      Real.exp (θ k * δ) * (δ⁻¹ * ∫ r in strip k δ, z r * Real.exp (-∑ ν, θ ν * r ν)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (θ k * J z θ)) := by
    simpa using hlim
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : 0 < δ := hδ
  rw [hform_lem z θ k hint δ hδ']
  ring

theorem limit_fin4 (zA zB : (Fin 4 → ℝ) → ℝ) (θ : Fin 4 → ℝ) (hθ : ∀ ν, 0 < θ ν)
    (kA kB : Fin 4)
    (hintA : Integrable (fun r => zA r * Real.exp (-∑ ν, θ ν * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)))
    (hintB : Integrable (fun r => zB r * Real.exp (-∑ ν, θ ν * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)))
    (hzA : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |zA r| ≤ 2 * r kA)
    (hzB : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |zB r| ≤ 2 * r kB) :
    Filter.Tendsto (fun δ : ℝ => δ⁻¹ *
      ((∫ r in Set.Ici (0 : Fin 4 → ℝ),
          (zA (r + δ • Pi.single kA (1 : ℝ)) - zA r) * Real.exp (-∑ ν, θ ν * r ν)) +
       (∫ r in Set.Ici (0 : Fin 4 → ℝ),
          (zB (r + δ • Pi.single kB (1 : ℝ)) - zB r) * Real.exp (-∑ ν, θ ν * r ν))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (θ kA * J zA θ + θ kB * J zB θ)) := by
  have := (single_limit zA θ hθ kA hintA hzA).add (single_limit zB θ hθ kB hintB hzB)
  exact this.congr fun δ => (mul_add _ _ _).symm

/-- `Fin 4 → ℝ ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ)`. -/
def eEquiv : (Fin 4 → ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans <|
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
     ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
       (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow))).trans
  (MeasurableEquiv.prodAssoc.symm)

lemma eEquiv_apply (r : Fin 4 → ℝ) : eEquiv r = ((r 0, r 1), (r 2, r 3)) := rfl

theorem eEquiv_mp : MeasurePreserving eEquiv volume volume := by
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  have h2 : MeasurePreserving (Prod.map (id : ℝ → ℝ)
      ((Prod.map (id : ℝ → ℝ) MeasurableEquiv.finTwoArrow) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      ((((MeasurePreserving.id (volume : Measure ℝ)).prod
        (volume_preserving_finTwoArrow ℝ))).comp
        (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0))
  have h3 := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure (ℝ × ℝ))).symm MeasurableEquiv.prodAssoc
  exact h3.comp (h2.comp h1)

lemma eEquiv_preimage : eEquiv ⁻¹' Qset = Set.Ici (0 : Fin 4 → ℝ) := by
  ext r
  simp only [Set.mem_preimage, eEquiv_apply, Qset, Set.mem_prod, Set.mem_Ici, Prod.le_def,
    Pi.le_def, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
  constructor
  · rintro ⟨⟨a, b⟩, c, d⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨⟨h 0, h 1⟩, h 2, h 3⟩

lemma J_comp_eq (A : ℝ × ℝ → ℝ × ℝ → ℝ) (θ : Fin 4 → ℝ) :
    J (fun r => A (eEquiv r).1 (eEquiv r).2) θ = lap A (θ 0, θ 1) (θ 2, θ 3) := by
  have h := eEquiv_mp.setIntegral_preimage_emb eEquiv.measurableEmbedding
    (fun p : (ℝ × ℝ) × (ℝ × ℝ) => A p.1 p.2 *
      Real.exp (-((θ 0, θ 1).1 * p.1.1 + (θ 0, θ 1).2 * p.1.2 + (θ 2, θ 3).1 * p.2.1 +
        (θ 2, θ 3).2 * p.2.2))) Qset
  rw [eEquiv_preimage] at h
  unfold lap J
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ici fun r _ => ?_
  simp only [eEquiv_apply, Fin.sum_univ_four]

/-- A pair `(X, Y)` of "disutility versions" with the forward/backward complementarity
inequalities `x^i + x^j = 1` in difference-quotient form, in both coordinate directions. -/
structure IsPair (X Y : ℝ × ℝ → ℝ × ℝ → ℝ) : Prop where
  bdX : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → 0 ≤ X t s ∧ X t s ≤ t.1 + t.2
  bdY : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → 0 ≤ Y t s ∧ Y t s ≤ s.1 + s.2
  lipX : ∀ (t s u : ℝ × ℝ) (δ : ℝ), (u = (1, 0) ∨ u = (0, 1)) → 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 →
    0 ≤ s.2 → 0 ≤ δ → |X (t + δ • u) s - X t s| ≤ δ
  lipY : ∀ (t s u : ℝ × ℝ) (δ : ℝ), (u = (1, 0) ∨ u = (0, 1)) → 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 →
    0 ≤ s.2 → 0 ≤ δ → |Y t (s + δ • u) - Y t s| ≤ δ
  fwd : ∀ (t s u : ℝ × ℝ) (δ : ℝ), (u = (1, 0) ∨ u = (0, 1)) → 0 < t.1 → 0 < t.2 → 0 < s.1 →
    0 < s.2 → 0 < δ →
    (X (t + δ • u) s - X t s) + (Y t (s + δ • u) - Y t s) ≤ δ
  bwd : ∀ (t s u : ℝ × ℝ) (δ : ℝ), (u = (1, 0) ∨ u = (0, 1)) → 0 < δ →
    0 < t.1 - δ * u.1 → 0 < t.2 - δ * u.2 → 0 < s.1 - δ * u.1 → 0 < s.2 - δ * u.2 →
    δ ≤ (X t s - X (t - δ • u) s) + (Y t s - Y t (s - δ • u))

/-- (S1, sorried) Laplace uniqueness step: if `α_h L(A) + γ_h L(B) = 0` for `h = 1, 2` and all
positive rates then `A = 0` a.e. on the orthant.  Uses `FracTruthSched.lemma_10`. -/
theorem laplace_vanish (A B : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hA : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => A p.1 p.2))
    (hB : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => B p.1 p.2))
    (hAg : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 →
      |A t s| ≤ t.1 + t.2 + s.1 + s.2)
    (hBg : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 →
      |B t s| ≤ t.1 + t.2 + s.1 + s.2)
    (hrel : ∀ α γ : ℝ × ℝ, 0 < α.1 → 0 < α.2 → 0 < γ.1 → 0 < γ.2 →
      α.1 * lap A α γ + γ.1 * lap B α γ = 0 ∧ α.2 * lap A α γ + γ.2 * lap B α γ = 0) :
    ∀ᵐ p ∂(volume.restrict Qset), A p.1 p.2 = 0 := by
  let F : (Fin 4 → ℝ) → ℝ := fun r => A (eEquiv r).1 (eEquiv r).2
  let G : (Fin 4 → ℝ) → ℝ := fun r => B (eEquiv r).1 (eEquiv r).2
  have hFm : Measurable F := hA.comp eEquiv.measurable
  have hGm : Measurable G := hB.comp eEquiv.measurable
  have hmem : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 ∧ 0 ≤ r 3 :=
    fun r hr => ⟨hr 0, hr 1, hr 2, hr 3⟩
  have key := laplace_fin4 F G hFm.aestronglyMeasurable hGm.aestronglyMeasurable
    (by
      intro r hr
      obtain ⟨h0, h1, h2, h3⟩ := hmem r hr
      have := hAg (r 0, r 1) (r 2, r 3) h0 h1 h2 h3
      simp only [Fin.sum_univ_four]
      simpa [F, eEquiv_apply, add_assoc] using this)
    (by
      intro r hr
      obtain ⟨h0, h1, h2, h3⟩ := hmem r hr
      have := hBg (r 0, r 1) (r 2, r 3) h0 h1 h2 h3
      simp only [Fin.sum_univ_four]
      simpa [G, eEquiv_apply, add_assoc] using this)
    (by
      intro θ hθ
      have := hrel (θ 0, θ 1) (θ 2, θ 3) (hθ 0) (hθ 1) (hθ 2) (hθ 3)
      rw [← J_comp_eq A θ, ← J_comp_eq B θ] at this
      exact this)
  have hmp := (eEquiv_mp.restrict_preimage_emb eEquiv.measurableEmbedding Qset)
  rw [eEquiv_preimage] at hmp
  have hsymm := MeasurePreserving.symm eEquiv hmp
  have := hsymm.quasiMeasurePreserving.ae key
  filter_upwards [this] with y hy
  simpa [F] using hy

/-- (S2, sorried) a.e. vanishing on the orthant + continuity in `t` gives vanishing at every `t`
for almost every `s`. -/
theorem ae_to_all (A : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hA : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => A p.1 p.2))
    (hc : ∀ s : ℝ × ℝ, 0 < s.1 → 0 < s.2 → ContinuousOn (fun t => A t s) (Set.Ici (0 : ℝ × ℝ)))
    (h0 : ∀ᵐ p ∂(volume.restrict Qset), A p.1 p.2 = 0) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))), ∀ t : ℝ × ℝ,
      0 ≤ t.1 → 0 ≤ t.2 → A t s = 0 := by
  have hQ : volume.restrict Qset = (volume.restrict (Set.Ici (0 : ℝ × ℝ))).prod
      (volume.restrict (Set.Ici (0 : ℝ × ℝ))) := by
    rw [Qset, Measure.volume_eq_prod (α := ℝ × ℝ) (β := ℝ × ℝ), Measure.prod_restrict]
  rw [hQ] at h0
  have hswap := (Measure.measurePreserving_swap (μ := volume.restrict (Set.Ici (0 : ℝ × ℝ)))
    (ν := volume.restrict (Set.Ici (0 : ℝ × ℝ)))).quasiMeasurePreserving.ae h0
  have h1 := Measure.ae_ae_of_ae_prod hswap
  have hsub : Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ × ℝ) := by
    intro p hp
    exact ⟨hp.1.le, hp.2.le⟩
  have hU : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have h2 := ae_restrict_of_ae_restrict_of_subset hsub h1
  filter_upwards [h2, ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with s hs hmem
  have hcs := hc s hmem.1 hmem.2
  have hae : (fun t => A t s) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))]
      (fun _ => (0 : ℝ)) := by
    have := ae_restrict_of_ae_restrict_of_subset hsub hs
    filter_upwards [this] with t ht
    simpa using ht
  have heq := Measure.eqOn_open_of_ae_eq hae hU (hcs.mono hsub) continuousOn_const
  have hcl : Set.Ici (0 : ℝ × ℝ) ⊆ closure (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    rw [closure_prod_eq, closure_Ioi]
    intro p hp
    exact ⟨hp.1, hp.2⟩
  have heq2 := Set.EqOn.of_subset_closure heq hcs continuousOn_const hsub hcl
  intro t ht1 ht2
  exact heq2 (show t ∈ Set.Ici (0 : ℝ × ℝ) from ⟨ht1, ht2⟩)

/-- The integrated forward difference quotient of a pair `(A, B)` in direction `u` at step `δ`,
against the Laplace weight. -/
noncomputable def Idelta (A B : ℝ × ℝ → ℝ × ℝ → ℝ) (u : ℝ × ℝ) (δ : ℝ) (α γ : ℝ × ℝ) : ℝ :=
  ∫ p in Qset, Real.exp (-(α.1 * p.1.1 + α.2 * p.1.2 + γ.1 * p.2.1 + γ.2 * p.2.2)) *
    ((A (p.1 + δ • u) p.2 - A p.1 p.2) + (B p.1 (p.2 + δ • u) - B p.1 p.2))

lemma wcongr (α γ : ℝ × ℝ) (r : Fin 4 → ℝ) :
    Real.exp (-(α.1 * (eEquiv r).1.1 + α.2 * (eEquiv r).1.2 + γ.1 * (eEquiv r).2.1 +
      γ.2 * (eEquiv r).2.2)) = Real.exp (-∑ ν, (![α.1, α.2, γ.1, γ.2] : Fin 4 → ℝ) ν * r ν) := by
  simp [eEquiv_apply, Fin.sum_univ_four]

lemma idelta_eq (A B : ℝ × ℝ → ℝ × ℝ → ℝ) (u : ℝ × ℝ) (kA kB : Fin 4)
    (hsA : ∀ (δ : ℝ) (r : Fin 4 → ℝ),
      eEquiv (r + δ • Pi.single kA (1 : ℝ)) = ((eEquiv r).1 + δ • u, (eEquiv r).2))
    (hsB : ∀ (δ : ℝ) (r : Fin 4 → ℝ),
      eEquiv (r + δ • Pi.single kB (1 : ℝ)) = ((eEquiv r).1, (eEquiv r).2 + δ • u))
    (α γ : ℝ × ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hintA : Integrable (fun r => A (eEquiv r).1 (eEquiv r).2 *
      Real.exp (-∑ ν, (![α.1, α.2, γ.1, γ.2] : Fin 4 → ℝ) ν * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)))
    (hintB : Integrable (fun r => B (eEquiv r).1 (eEquiv r).2 *
      Real.exp (-∑ ν, (![α.1, α.2, γ.1, γ.2] : Fin 4 → ℝ) ν * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0))) :
    Idelta A B u δ α γ =
      (∫ r in Set.Ici (0 : Fin 4 → ℝ),
        ((fun r => A (eEquiv r).1 (eEquiv r).2) (r + δ • Pi.single kA (1 : ℝ)) -
          (fun r => A (eEquiv r).1 (eEquiv r).2) r) *
          Real.exp (-∑ ν, (![α.1, α.2, γ.1, γ.2] : Fin 4 → ℝ) ν * r ν)) +
      (∫ r in Set.Ici (0 : Fin 4 → ℝ),
        ((fun r => B (eEquiv r).1 (eEquiv r).2) (r + δ • Pi.single kB (1 : ℝ)) -
          (fun r => B (eEquiv r).1 (eEquiv r).2) r) *
          Real.exp (-∑ ν, (![α.1, α.2, γ.1, γ.2] : Fin 4 → ℝ) ν * r ν)) := by
  set θ : Fin 4 → ℝ := ![α.1, α.2, γ.1, γ.2] with hθ
  have hA1 := shift_integrable (fun r => A (eEquiv r).1 (eEquiv r).2) θ _
    (single_nonneg kA δ hδ) hintA
  have hB1 := shift_integrable (fun r => B (eEquiv r).1 (eEquiv r).2) θ _
    (single_nonneg kB δ hδ) hintB
  rw [← integral_add ((hA1.sub hintA).congr (Filter.Eventually.of_forall fun r => by simp only [Pi.sub_apply, sub_mul]))
    ((hB1.sub hintB).congr (Filter.Eventually.of_forall fun r => by simp only [Pi.sub_apply, sub_mul]))]
  unfold Idelta
  have h := eEquiv_mp.setIntegral_preimage_emb eEquiv.measurableEmbedding
    (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      Real.exp (-(α.1 * p.1.1 + α.2 * p.1.2 + γ.1 * p.2.1 + γ.2 * p.2.2)) *
        ((A (p.1 + δ • u) p.2 - A p.1 p.2) + (B p.1 (p.2 + δ • u) - B p.1 p.2))) Qset
  rw [eEquiv_preimage] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ici fun r _ => ?_
  simp only
  rw [wcongr, hsA, hsB]
  ring


lemma bd_t (A : ℝ × ℝ → ℝ × ℝ → ℝ) (u : ℝ × ℝ) (hu : u = (1, 0) ∨ u = (0, 1))
    (hAl : ∀ (t s u : ℝ × ℝ) (δ : ℝ), (u = (1, 0) ∨ u = (0, 1)) → 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 →
      0 ≤ s.2 → 0 ≤ δ → |A (t + δ • u) s - A t s| ≤ 2 * δ)
    (hAb : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → (t.1 = 0 ∨ t.2 = 0) → A t s = 0)
    (t s : ℝ × ℝ) (h1 : 0 ≤ t.1) (h2 : 0 ≤ t.2) (h3 : 0 ≤ s.1) (h4 : 0 ≤ s.2) :
    |A t s| ≤ 2 * (t.1 * u.1 + t.2 * u.2) := by
  rcases hu with rfl | rfl
  · have := hAl (0, t.2) s (1, 0) t.1 (Or.inl rfl) le_rfl h2 h3 h4 h1
    have h0 := hAb (0, t.2) s le_rfl h2 h3 h4 (Or.inl rfl)
    have e : ((0, t.2) : ℝ × ℝ) + t.1 • ((1, 0) : ℝ × ℝ) = t := by ext <;> simp
    rw [e, h0, sub_zero] at this
    simpa using this
  · have := hAl (t.1, 0) s (0, 1) t.2 (Or.inr rfl) h1 le_rfl h3 h4 h2
    have h0 := hAb (t.1, 0) s h1 le_rfl h3 h4 (Or.inr rfl)
    have e : ((t.1, 0) : ℝ × ℝ) + t.2 • ((0, 1) : ℝ × ℝ) = t := by ext <;> simp
    rw [e, h0, sub_zero] at this
    simpa using this

lemma bd_s (B : ℝ × ℝ → ℝ × ℝ → ℝ) (u : ℝ × ℝ) (hu : u = (1, 0) ∨ u = (0, 1))
    (hBl : ∀ (t s u : ℝ × ℝ) (δ : ℝ), (u = (1, 0) ∨ u = (0, 1)) → 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 →
      0 ≤ s.2 → 0 ≤ δ → |B t (s + δ • u) - B t s| ≤ 2 * δ)
    (hBb : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → (s.1 = 0 ∨ s.2 = 0) → B t s = 0)
    (t s : ℝ × ℝ) (h1 : 0 ≤ t.1) (h2 : 0 ≤ t.2) (h3 : 0 ≤ s.1) (h4 : 0 ≤ s.2) :
    |B t s| ≤ 2 * (s.1 * u.1 + s.2 * u.2) := by
  rcases hu with rfl | rfl
  · have := hBl t (0, s.2) (1, 0) s.1 (Or.inl rfl) h1 h2 le_rfl h4 h3
    have h0 := hBb t (0, s.2) h1 h2 le_rfl h4 (Or.inl rfl)
    have e : ((0, s.2) : ℝ × ℝ) + s.1 • ((1, 0) : ℝ × ℝ) = s := by ext <;> simp
    rw [e, h0, sub_zero] at this
    simpa using this
  · have := hBl t (s.1, 0) (0, 1) s.2 (Or.inr rfl) h1 h2 h3 le_rfl h4
    have h0 := hBb t (s.1, 0) h1 h2 h3 le_rfl (Or.inr rfl)
    have e : ((s.1, 0) : ℝ × ℝ) + s.2 • ((0, 1) : ℝ × ℝ) = s := by ext <;> simp
    rw [e, h0, sub_zero] at this
    simpa using this

lemma shift_data (u : ℝ × ℝ) (hu : u = (1, 0) ∨ u = (0, 1)) (α γ : ℝ × ℝ) :
    ∃ kA kB : Fin 4,
      (∀ (δ : ℝ) (r : Fin 4 → ℝ),
        eEquiv (r + δ • Pi.single kA (1 : ℝ)) = ((eEquiv r).1 + δ • u, (eEquiv r).2)) ∧
      (∀ (δ : ℝ) (r : Fin 4 → ℝ),
        eEquiv (r + δ • Pi.single kB (1 : ℝ)) = ((eEquiv r).1, (eEquiv r).2 + δ • u)) ∧
      (∀ r : Fin 4 → ℝ, (eEquiv r).1.1 * u.1 + (eEquiv r).1.2 * u.2 = r kA) ∧
      (∀ r : Fin 4 → ℝ, (eEquiv r).2.1 * u.1 + (eEquiv r).2.2 * u.2 = r kB) ∧
      ((![α.1, α.2, γ.1, γ.2] : Fin 4 → ℝ) kA = α.1 * u.1 + α.2 * u.2) ∧
      ((![α.1, α.2, γ.1, γ.2] : Fin 4 → ℝ) kB = γ.1 * u.1 + γ.2 * u.2) := by
  rcases hu with rfl | rfl
  · refine ⟨0, 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro δ r; ext <;> simp [eEquiv_apply, Pi.single_apply]
    · intro δ r; ext <;> simp [eEquiv_apply, Pi.single_apply]
    · intro r; simp [eEquiv_apply]
    · intro r; simp [eEquiv_apply]
    · simp
    · simp
  · refine ⟨1, 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro δ r; ext <;> simp [eEquiv_apply, Pi.single_apply]
    · intro δ r; ext <;> simp [eEquiv_apply, Pi.single_apply]
    · intro r; simp [eEquiv_apply]
    · intro r; simp [eEquiv_apply]
    · simp
    · simp

/-- (P2b) translation/Laplace step: for `A`, `B` Lipschitz in their own values, vanishing
on the own-value boundary and of linear growth, `δ⁻¹ · Idelta → ⟨α, u⟩ L(A) + ⟨γ, u⟩ L(B)`
(integration by parts in difference-quotient form, boundary strips `O(δ²)`). -/
theorem idelta_limit (A B : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hA : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => A p.1 p.2))
    (hB : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => B p.1 p.2))
    (hAg : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 →
      |A t s| ≤ t.1 + t.2 + s.1 + s.2)
    (hBg : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 →
      |B t s| ≤ t.1 + t.2 + s.1 + s.2)
    (hAl : ∀ (t s u : ℝ × ℝ) (δ : ℝ), (u = (1, 0) ∨ u = (0, 1)) → 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 →
      0 ≤ s.2 → 0 ≤ δ → |A (t + δ • u) s - A t s| ≤ 2 * δ)
    (hBl : ∀ (t s u : ℝ × ℝ) (δ : ℝ), (u = (1, 0) ∨ u = (0, 1)) → 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 →
      0 ≤ s.2 → 0 ≤ δ → |B t (s + δ • u) - B t s| ≤ 2 * δ)
    (hAb : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → (t.1 = 0 ∨ t.2 = 0) → A t s = 0)
    (hBb : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → (s.1 = 0 ∨ s.2 = 0) → B t s = 0)
    (u : ℝ × ℝ) (hu : u = (1, 0) ∨ u = (0, 1)) (α γ : ℝ × ℝ) (hα1 : 0 < α.1) (hα2 : 0 < α.2)
    (hγ1 : 0 < γ.1) (hγ2 : 0 < γ.2) :
    Filter.Tendsto (fun δ : ℝ => δ⁻¹ * Idelta A B u δ α γ) (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((α.1 * u.1 + α.2 * u.2) * lap A α γ + (γ.1 * u.1 + γ.2 * u.2) * lap B α γ)) := by
  obtain ⟨kA, kB, hsA, hsB, hkA, hkB, hθA, hθB⟩ := shift_data u hu α γ
  set θ : Fin 4 → ℝ := ![α.1, α.2, γ.1, γ.2] with hθdef
  have hθ : ∀ ν, 0 < θ ν := by
    intro ν; fin_cases ν <;> simp [θ, hα1, hα2, hγ1, hγ2]
  have hnn : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), 0 ≤ (eEquiv r).1.1 ∧ 0 ≤ (eEquiv r).1.2 ∧
      0 ≤ (eEquiv r).2.1 ∧ 0 ≤ (eEquiv r).2.2 := by
    intro r hr
    simp only [eEquiv_apply]
    exact ⟨hr 0, hr 1, hr 2, hr 3⟩
  have hsumr : ∀ r : Fin 4 → ℝ, ∑ ν, r ν =
      (eEquiv r).1.1 + (eEquiv r).1.2 + (eEquiv r).2.1 + (eEquiv r).2.2 := by
    intro r; simp [eEquiv_apply, Fin.sum_univ_four]
  have hmeas : ∀ Z : ℝ × ℝ → ℝ × ℝ → ℝ, Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Z p.1 p.2) →
      AEStronglyMeasurable (fun r : Fin 4 → ℝ => Z (eEquiv r).1 (eEquiv r).2 *
        Real.exp (-∑ ν, θ ν * r ν)) ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)) := by
    intro Z hZ
    refine ((hZ.comp eEquiv.measurable).aestronglyMeasurable).mul ?_
    exact (Real.continuous_exp.comp (continuous_neg.comp (continuous_finset_sum _ fun ν _ =>
      continuous_const.mul (continuous_apply ν)))).aestronglyMeasurable
  have hint : ∀ Z : ℝ × ℝ → ℝ × ℝ → ℝ, Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Z p.1 p.2) →
      (∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 →
        |Z t s| ≤ t.1 + t.2 + s.1 + s.2) →
      Integrable (fun r : Fin 4 → ℝ => Z (eEquiv r).1 (eEquiv r).2 *
        Real.exp (-∑ ν, θ ν * r ν)) ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)) := by
    intro Z hZ hg
    refine (bound_integrable θ hθ).mono' (hmeas Z hZ) ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Set.Ici (0 : Fin 4 → ℝ)))]
      with r hr
    obtain ⟨h1, h2, h3, h4⟩ := hnn r hr
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hsumr r]
    exact mul_le_mul_of_nonneg_right (hg _ _ h1 h2 h3 h4) (Real.exp_pos _).le
  have hintA := hint A hA hAg
  have hintB := hint B hB hBg
  have hzA : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |A (eEquiv r).1 (eEquiv r).2| ≤ 2 * r kA := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := hnn r hr
    have := bd_t A u hu hAl hAb _ _ h1 h2 h3 h4
    rwa [hkA r] at this
  have hzB : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |B (eEquiv r).1 (eEquiv r).2| ≤ 2 * r kB := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := hnn r hr
    have := bd_s B u hu hBl hBb _ _ h1 h2 h3 h4
    rwa [hkB r] at this
  have hlim := limit_fin4 (fun r => A (eEquiv r).1 (eEquiv r).2)
    (fun r => B (eEquiv r).1 (eEquiv r).2) θ hθ kA kB hintA hintB hzA hzB
  have hJA : J (fun r => A (eEquiv r).1 (eEquiv r).2) θ = lap A α γ := by
    have := J_comp_eq A θ
    simpa [θ] using this
  have hJB : J (fun r => B (eEquiv r).1 (eEquiv r).2) θ = lap B α γ := by
    have := J_comp_eq B θ
    simpa [θ] using this
  rw [hJA, hJB, hθA, hθB] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : 0 < δ := hδ
  rw [idelta_eq A B u kA kB hsA hsB α γ δ hδ' hintA hintB]

/-- Shifting the Laplace integral of a function bounded by `δ` by `δ e_k` costs `O(δ²)`. -/
lemma shift_err (θ : Fin 4 → ℝ) (hθ : ∀ ν, 0 < θ ν) (k : Fin 4) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ z : (Fin 4 → ℝ) → ℝ,
      Integrable (fun r => z r * Real.exp (-∑ ν, θ ν * r ν))
        ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)) →
      (∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |z r| ≤ δ) →
      |(∫ r in Set.Ici (0 : Fin 4 → ℝ), z (r + δ • Pi.single k (1 : ℝ)) *
          Real.exp (-∑ ν, θ ν * r ν)) -
        ∫ r in Set.Ici (0 : Fin 4 → ℝ), z r * Real.exp (-∑ ν, θ ν * r ν)| ≤ C * δ ^ 2 := by
  obtain ⟨C1, hC1⟩ := strip_bound θ hθ k
  set W0 : ℝ := ∫ r in Set.Ici (0 : Fin 4 → ℝ), Real.exp (-∑ ν, θ ν * r ν) with hW0
  have hW0nn : 0 ≤ W0 := setIntegral_nonneg measurableSet_Ici fun r _ => (Real.exp_pos _).le
  have hC1nn : 0 ≤ C1 := by
    have h := hC1 1 one_pos
    have : 0 ≤ ∫ r in strip k 1, Real.exp (-∑ ν, θ ν * r ν) :=
      setIntegral_nonneg (strip_meas k 1) fun r _ => (Real.exp_pos _).le
    linarith
  refine ⟨θ k * Real.exp (θ k) * W0 + Real.exp (θ k) * C1, fun δ hδ hδ1 z hint hzb => ?_⟩
  have h1 := shift_fin4 z θ _ (single_nonneg k δ hδ) hint
  rw [single_sum] at h1
  rw [h1]
  set I := ∫ r in Set.Ici (0 : Fin 4 → ℝ), z r * Real.exp (-∑ ν, θ ν * r ν) with hI
  set S := ∫ r in Set.Ici (0 : Fin 4 → ℝ) \ Set.Ici (δ • Pi.single k (1 : ℝ)),
    z r * Real.exp (-∑ ν, θ ν * r ν) with hS
  have hwi := exp_integrable4 θ hθ
  have hIb : |I| ≤ δ * W0 := by
    have := norm_integral_le_of_norm_le (μ := (volume : Measure (Fin 4 → ℝ)).restrict
        (Set.Ici 0)) (f := fun r => z r * Real.exp (-∑ ν, θ ν * r ν))
      (g := fun r => δ * Real.exp (-∑ ν, θ ν * r ν)) (hwi.const_mul δ)
      ((ae_restrict_iff' measurableSet_Ici).2 (Filter.Eventually.of_forall fun r hr => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hzb r hr) (Real.exp_pos _).le))
    rw [Real.norm_eq_abs, integral_const_mul] at this
    exact this
  have hSb : |S| ≤ δ * (C1 * δ) := by
    have hw' : IntegrableOn (fun r : Fin 4 → ℝ => Real.exp (-∑ ν, θ ν * r ν)) (strip k δ) :=
      IntegrableOn.mono_set hwi (strip_sub k δ)
    have := norm_integral_le_of_norm_le (μ := (volume : Measure (Fin 4 → ℝ)).restrict
        (strip k δ)) (f := fun r => z r * Real.exp (-∑ ν, θ ν * r ν))
      (g := fun r => δ * Real.exp (-∑ ν, θ ν * r ν)) (hw'.const_mul δ)
      ((ae_restrict_iff' (strip_meas k δ)).2 (Filter.Eventually.of_forall fun r hr => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hzb r (strip_sub k δ hr)) (Real.exp_pos _).le))
    rw [Real.norm_eq_abs, integral_const_mul] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hC1 δ hδ) hδ.le)
  set c := θ k * δ with hc
  have hc0 : 0 ≤ c := mul_nonneg (hθ k).le hδ.le
  have hcle : c ≤ θ k := by
    have := mul_le_mul_of_nonneg_left hδ1 (hθ k).le
    simpa [hc] using this
  have hec : Real.exp c ≤ Real.exp (θ k) := Real.exp_le_exp.2 hcle
  have he1 : 0 ≤ Real.exp c - 1 := by
    have := Real.add_one_le_exp c; linarith
  have he2 : Real.exp c - 1 ≤ c * Real.exp c := by
    have h := Real.add_one_le_exp (-c)
    have h2 : Real.exp (-c) * Real.exp c = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos c]
  have he3 : Real.exp c - 1 ≤ θ k * δ * Real.exp (θ k) := by
    calc Real.exp c - 1 ≤ c * Real.exp c := he2
      _ ≤ c * Real.exp (θ k) := mul_le_mul_of_nonneg_left hec hc0
  have eq : Real.exp c * (I - S) - I = (Real.exp c - 1) * I - Real.exp c * S := by ring
  rw [eq]
  calc |(Real.exp c - 1) * I - Real.exp c * S|
      ≤ |(Real.exp c - 1) * I| + |Real.exp c * S| := abs_sub _ _
    _ = (Real.exp c - 1) * |I| + Real.exp c * |S| := by
        rw [abs_mul, abs_mul, abs_of_nonneg he1, abs_of_pos (Real.exp_pos _)]
    _ ≤ (θ k * δ * Real.exp (θ k)) * (δ * W0) + Real.exp (θ k) * (δ * (C1 * δ)) := by
        gcongr
    _ = (θ k * Real.exp (θ k) * W0 + Real.exp (θ k) * C1) * δ ^ 2 := by ring

/-- Almost every point of the closed orthant is interior. -/
lemma ae_pos :
    ∀ᵐ r ∂((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)), ∀ i, 0 < r i := by
  have h : (Set.pi Set.univ fun _ : Fin 4 => Set.Ioi (0 : ℝ)) =ᵐ[(volume : Measure (Fin 4 → ℝ))]
      Set.Ici (0 : Fin 4 → ℝ) := by
    rw [volume_pi]
    exact Measure.univ_pi_Ioi_ae_eq_Ici
  rw [Measure.restrict_congr_set h.symm]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ioi)] with r hr i
  exact hr i (Set.mem_univ _)

/-- Per-pair bounds: `δ W0 - K δ² ≤ Idelta X Y ≤ δ W0`. -/
lemma pair_bounds (X Y : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hX : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => X p.1 p.2))
    (hY : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Y p.1 p.2))
    (hP : IsPair X Y) (u : ℝ × ℝ) (hu : u = (1, 0) ∨ u = (0, 1))
    (α γ : ℝ × ℝ) (hα1 : 0 < α.1) (hα2 : 0 < α.2) (hγ1 : 0 < γ.1) (hγ2 : 0 < γ.2) :
    ∃ K : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      δ * (∫ r in Set.Ici (0 : Fin 4 → ℝ),
          Real.exp (-∑ ν, (![α.1, α.2, γ.1, γ.2] : Fin 4 → ℝ) ν * r ν)) - K * δ ^ 2 ≤
        Idelta X Y u δ α γ ∧
      Idelta X Y u δ α γ ≤ δ * (∫ r in Set.Ici (0 : Fin 4 → ℝ),
          Real.exp (-∑ ν, (![α.1, α.2, γ.1, γ.2] : Fin 4 → ℝ) ν * r ν)) := by
  obtain ⟨kA, kB, hsA, hsB, -, -, -, -⟩ := shift_data u hu α γ
  set θ : Fin 4 → ℝ := ![α.1, α.2, γ.1, γ.2] with hθdef
  have hθ : ∀ ν, 0 < θ ν := by
    intro ν; fin_cases ν <;> simp [θ, hα1, hα2, hγ1, hγ2]
  obtain ⟨CA, hCA⟩ := shift_err θ hθ kA
  obtain ⟨CB, hCB⟩ := shift_err θ hθ kB
  have hnn : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), 0 ≤ (eEquiv r).1.1 ∧ 0 ≤ (eEquiv r).1.2 ∧
      0 ≤ (eEquiv r).2.1 ∧ 0 ≤ (eEquiv r).2.2 := by
    intro r hr
    simp only [eEquiv_apply]
    exact ⟨hr 0, hr 1, hr 2, hr 3⟩
  have hsumr : ∀ r : Fin 4 → ℝ, ∑ ν, r ν =
      (eEquiv r).1.1 + (eEquiv r).1.2 + (eEquiv r).2.1 + (eEquiv r).2.2 := by
    intro r; simp [eEquiv_apply, Fin.sum_univ_four]
  have hwm : Measurable (fun r : Fin 4 → ℝ => Real.exp (-∑ ν, θ ν * r ν)) :=
    (Real.continuous_exp.comp (continuous_neg.comp (continuous_finsetSum _ fun ν _ =>
      continuous_const.mul (continuous_apply ν)))).measurable
  have hint : ∀ Z : ℝ × ℝ → ℝ × ℝ → ℝ, Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Z p.1 p.2) →
      (∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 →
        |Z t s| ≤ t.1 + t.2 + s.1 + s.2) →
      Integrable (fun r : Fin 4 → ℝ => Z (eEquiv r).1 (eEquiv r).2 *
        Real.exp (-∑ ν, θ ν * r ν)) ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)) := by
    intro Z hZ hg
    refine (bound_integrable θ hθ).mono'
      (((hZ.comp eEquiv.measurable).mul hwm).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Set.Ici (0 : Fin 4 → ℝ)))]
      with r hr
    obtain ⟨h1, h2, h3, h4⟩ := hnn r hr
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hsumr r]
    exact mul_le_mul_of_nonneg_right (hg _ _ h1 h2 h3 h4) (Real.exp_pos _).le
  have hintX := hint X hX (by
    intro t s h1 h2 h3 h4
    have := hP.bdX t s h1 h2 h3 h4
    rw [abs_of_nonneg this.1]; linarith)
  have hintY := hint Y hY (by
    intro t s h1 h2 h3 h4
    have := hP.bdY t s h1 h2 h3 h4
    rw [abs_of_nonneg this.1]; linarith)
  set x : (Fin 4 → ℝ) → ℝ := fun r => X (eEquiv r).1 (eEquiv r).2 with hx
  set y : (Fin 4 → ℝ) → ℝ := fun r => Y (eEquiv r).1 (eEquiv r).2 with hy
  set w : (Fin 4 → ℝ) → ℝ := fun r => Real.exp (-∑ ν, θ ν * r ν) with hw
  refine ⟨CA + CB, fun δ hδ hδ1 => ?_⟩
  set vA : Fin 4 → ℝ := δ • Pi.single kA (1 : ℝ) with hvA
  set vB : Fin 4 → ℝ := δ • Pi.single kB (1 : ℝ) with hvB
  have hvA0 : (0 : Fin 4 → ℝ) ≤ vA := single_nonneg kA δ hδ
  have hvB0 : (0 : Fin 4 → ℝ) ≤ vB := single_nonneg kB δ hδ
  set gx : (Fin 4 → ℝ) → ℝ := fun r => x (r + vA) - x r with hgx
  set gy : (Fin 4 → ℝ) → ℝ := fun r => y (r + vB) - y r with hgy
  have hsxA := shift_integrable x θ vA hvA0 hintX
  have hsyB := shift_integrable y θ vB hvB0 hintY
  have hgxi : Integrable (fun r => gx r * w r)
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)) := by
    have := hsxA.sub hintX
    refine this.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [Pi.sub_apply, gx, w]; ring
  have hgyi : Integrable (fun r => gy r * w r)
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)) := by
    have := hsyB.sub hintY
    refine this.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [Pi.sub_apply, gy, w]; ring
  -- Idelta as a single Fin 4 integral
  have hId : Idelta X Y u δ α γ =
      ∫ r in Set.Ici (0 : Fin 4 → ℝ), (gx r + gy r) * w r := by
    rw [idelta_eq X Y u kA kB hsA hsB α γ δ hδ hintX hintY, ← integral_add hgxi hgyi]
    congr 1; ext r; simp only [gx, gy, x, y, w, θ]; ring
  have hwi := exp_integrable4 θ hθ
  -- pointwise forward inequality on the interior
  have hgxb : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |gx r| ≤ δ := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := hnn r hr
    have := hP.lipX (eEquiv r).1 (eEquiv r).2 u δ hu h1 h2 h3 h4 hδ.le
    simpa [gx, x, vA, hsA] using this
  have hgyb : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), |gy r| ≤ δ := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := hnn r hr
    have := hP.lipY (eEquiv r).1 (eEquiv r).2 u δ hu h1 h2 h3 h4 hδ.le
    simpa [gy, y, vB, hsB] using this
  have hpos := ae_pos
  constructor
  · -- lower bound via the backward inequality at the shifted point
    have hlow : ∀ᵐ r ∂((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)),
        δ * w r ≤ (gx (r + vB) + gy (r + vA)) * w r := by
      filter_upwards [hpos] with r hr
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have e1 : eEquiv (r + vB + vA) = ((eEquiv r).1 + δ • u, (eEquiv r).2 + δ • u) := by
        rw [hvA, hsA, hvB, hsB]
      have e2 : eEquiv (r + vA + vB) = ((eEquiv r).1 + δ • u, (eEquiv r).2 + δ • u) := by
        rw [hvB, hsB, hvA, hsA]
      have e3 : eEquiv (r + vB) = ((eEquiv r).1, (eEquiv r).2 + δ • u) := by rw [hvB, hsB]
      have e4 : eEquiv (r + vA) = ((eEquiv r).1 + δ • u, (eEquiv r).2) := by rw [hvA, hsA]
      have hb := hP.bwd ((eEquiv r).1 + δ • u) ((eEquiv r).2 + δ • u) u δ hu hδ
      have c1 : ((eEquiv r).1 + δ • u) - δ • u = (eEquiv r).1 := by abel
      have c2 : ((eEquiv r).2 + δ • u) - δ • u = (eEquiv r).2 := by abel
      rw [c1, c2] at hb
      have hr' : 0 < (eEquiv r).1.1 ∧ 0 < (eEquiv r).1.2 ∧ 0 < (eEquiv r).2.1 ∧
          0 < (eEquiv r).2.2 := by
        simp only [eEquiv_apply]; exact ⟨hr 0, hr 1, hr 2, hr 3⟩
      have hb' := hb (by rcases hu with rfl | rfl <;> simp <;> linarith [hr'.1, hr'.2.1])
        (by rcases hu with rfl | rfl <;> simp <;> linarith [hr'.1, hr'.2.1])
        (by rcases hu with rfl | rfl <;> simp <;> linarith [hr'.2.2.1, hr'.2.2.2])
        (by rcases hu with rfl | rfl <;> simp <;> linarith [hr'.2.2.1, hr'.2.2.2])
      simp only [gx, gy, x, y]
      rw [show r + vB + vA = r + vA + vB by abel, e2, e3, e4]
      linarith
    have hi1 := shift_integrable gx θ vB hvB0 hgxi
    have hi2 := shift_integrable gy θ vA hvA0 hgyi
    have hI : Integrable (fun r => (gx (r + vB) + gy (r + vA)) * w r)
        ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)) :=
      (hi1.add hi2).congr (Filter.Eventually.of_forall fun r => by simp only [Pi.add_apply]; ring)
    have hmono := integral_mono_ae (f := fun r => δ * w r)
      (g := fun r => (gx (r + vB) + gy (r + vA)) * w r) (hwi.const_mul δ) hI hlow
    rw [integral_const_mul] at hmono
    have hsplit : ∫ r in Set.Ici (0 : Fin 4 → ℝ), (gx (r + vB) + gy (r + vA)) * w r =
        (∫ r in Set.Ici (0 : Fin 4 → ℝ), gx (r + vB) * w r) +
          ∫ r in Set.Ici (0 : Fin 4 → ℝ), gy (r + vA) * w r := by
      rw [← integral_add hi1 hi2]; congr 1; ext r; ring
    have hsplit2 : ∫ r in Set.Ici (0 : Fin 4 → ℝ), (gx r + gy r) * w r =
        (∫ r in Set.Ici (0 : Fin 4 → ℝ), gx r * w r) +
          ∫ r in Set.Ici (0 : Fin 4 → ℝ), gy r * w r := by
      rw [← integral_add hgxi hgyi]; congr 1; ext r; ring
    have eB := hCB δ hδ hδ1 gx hgxi hgxb
    have eA := hCA δ hδ hδ1 gy hgyi hgyb
    rw [hId, hsplit2]
    rw [hsplit] at hmono
    have h1 : (∫ r in Set.Ici (0 : Fin 4 → ℝ), gx (r + vB) * w r) -
        (∫ r in Set.Ici (0 : Fin 4 → ℝ), gx r * w r) ≤ CB * δ ^ 2 := (abs_le.1 eB).2
    have h2 : (∫ r in Set.Ici (0 : Fin 4 → ℝ), gy (r + vA) * w r) -
        (∫ r in Set.Ici (0 : Fin 4 → ℝ), gy r * w r) ≤ CA * δ ^ 2 := (abs_le.1 eA).2
    have k1 : (∫ r in Set.Ici (0 : Fin 4 → ℝ), gx (r + vB) * w r) +
        (∫ r in Set.Ici (0 : Fin 4 → ℝ), gy (r + vA) * w r) ≤
        (∫ r in Set.Ici (0 : Fin 4 → ℝ), gx r * w r) +
        (∫ r in Set.Ici (0 : Fin 4 → ℝ), gy r * w r) + (CA + CB) * δ ^ 2 := by linarith
    have k2 : δ * (∫ r in Set.Ici (0 : Fin 4 → ℝ), w r) ≤
        (∫ r in Set.Ici (0 : Fin 4 → ℝ), gx (r + vB) * w r) +
        (∫ r in Set.Ici (0 : Fin 4 → ℝ), gy (r + vA) * w r) := hmono
    show δ * (∫ r in Set.Ici (0 : Fin 4 → ℝ), w r) - (CA + CB) * δ ^ 2 ≤
        (∫ r in Set.Ici (0 : Fin 4 → ℝ), gx r * w r) +
        (∫ r in Set.Ici (0 : Fin 4 → ℝ), gy r * w r)
    linarith
  · have hup : ∀ᵐ r ∂((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)),
        (gx r + gy r) * w r ≤ δ * w r := by
      filter_upwards [hpos] with r hr
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have hr' : 0 < (eEquiv r).1.1 ∧ 0 < (eEquiv r).1.2 ∧ 0 < (eEquiv r).2.1 ∧
          0 < (eEquiv r).2.2 := by
        simp only [eEquiv_apply]; exact ⟨hr 0, hr 1, hr 2, hr 3⟩
      have := hP.fwd (eEquiv r).1 (eEquiv r).2 u δ hu hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2 hδ
      simpa [gx, gy, x, y, vA, vB, hsA, hsB] using this
    have hI : Integrable (fun r => (gx r + gy r) * w r)
        ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)) :=
      (hgxi.add hgyi).congr (Filter.Eventually.of_forall fun r => by simp only [Pi.add_apply]; ring)
    have hmono := integral_mono_ae (f := fun r => (gx r + gy r) * w r)
      (g := fun r => δ * w r) hI (hwi.const_mul δ) hup
    rw [integral_const_mul] at hmono
    rw [hId]
    refine le_trans (le_of_eq ?_) hmono
    congr 1

lemma shift_diff_int (θ : Fin 4 → ℝ) (v : Fin 4 → ℝ) (hv : 0 ≤ v) (z : (Fin 4 → ℝ) → ℝ)
    (hint : Integrable (fun r => z r * Real.exp (-∑ ν, θ ν * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0))) :
    Integrable (fun r => (z (r + v) - z r) * Real.exp (-∑ ν, θ ν * r ν))
      ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)) :=
  ((shift_integrable z θ v hv hint).sub hint).congr
    (Filter.Eventually.of_forall fun r => by simp only [Pi.sub_apply]; ring)

lemma idelta_sub (X Y X' Y' : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hX : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => X p.1 p.2))
    (hY : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Y p.1 p.2))
    (hX' : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => X' p.1 p.2))
    (hY' : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Y' p.1 p.2))
    (hP : IsPair X Y) (hP' : IsPair X' Y') (u : ℝ × ℝ) (hu : u = (1, 0) ∨ u = (0, 1))
    (α γ : ℝ × ℝ) (hα1 : 0 < α.1) (hα2 : 0 < α.2) (hγ1 : 0 < γ.1) (hγ2 : 0 < γ.2)
    (δ : ℝ) (hδ : 0 < δ) :
    Idelta (fun t s => X t s - X' t s) (fun t s => Y t s - Y' t s) u δ α γ =
      Idelta X Y u δ α γ - Idelta X' Y' u δ α γ := by
  obtain ⟨kA, kB, hsA, hsB, -, -, -, -⟩ := shift_data u hu α γ
  set θ : Fin 4 → ℝ := ![α.1, α.2, γ.1, γ.2] with hθdef
  have hθ : ∀ ν, 0 < θ ν := by
    intro ν; fin_cases ν <;> simp [θ, hα1, hα2, hγ1, hγ2]
  have hnn : ∀ r ∈ Set.Ici (0 : Fin 4 → ℝ), 0 ≤ (eEquiv r).1.1 ∧ 0 ≤ (eEquiv r).1.2 ∧
      0 ≤ (eEquiv r).2.1 ∧ 0 ≤ (eEquiv r).2.2 := by
    intro r hr
    simp only [eEquiv_apply]
    exact ⟨hr 0, hr 1, hr 2, hr 3⟩
  have hsumr : ∀ r : Fin 4 → ℝ, ∑ ν, r ν =
      (eEquiv r).1.1 + (eEquiv r).1.2 + (eEquiv r).2.1 + (eEquiv r).2.2 := by
    intro r; simp [eEquiv_apply, Fin.sum_univ_four]
  have hwm : Measurable (fun r : Fin 4 → ℝ => Real.exp (-∑ ν, θ ν * r ν)) :=
    (Real.continuous_exp.comp (continuous_neg.comp (continuous_finsetSum _ fun ν _ =>
      continuous_const.mul (continuous_apply ν)))).measurable
  have hint : ∀ Z : ℝ × ℝ → ℝ × ℝ → ℝ, Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Z p.1 p.2) →
      (∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 →
        |Z t s| ≤ t.1 + t.2 + s.1 + s.2) →
      Integrable (fun r : Fin 4 → ℝ => Z (eEquiv r).1 (eEquiv r).2 *
        Real.exp (-∑ ν, θ ν * r ν)) ((volume : Measure (Fin 4 → ℝ)).restrict (Set.Ici 0)) := by
    intro Z hZ hg
    refine (bound_integrable θ hθ).mono'
      (((hZ.comp eEquiv.measurable).mul hwm).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Set.Ici (0 : Fin 4 → ℝ)))]
      with r hr
    obtain ⟨h1, h2, h3, h4⟩ := hnn r hr
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hsumr r]
    exact mul_le_mul_of_nonneg_right (hg _ _ h1 h2 h3 h4) (Real.exp_pos _).le
  have gX : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 →
      |X t s| ≤ t.1 + t.2 + s.1 + s.2 := by
    intro t s h1 h2 h3 h4; have := hP.bdX t s h1 h2 h3 h4; rw [abs_le]; constructor <;> linarith
  have gX' : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 →
      |X' t s| ≤ t.1 + t.2 + s.1 + s.2 := by
    intro t s h1 h2 h3 h4; have := hP'.bdX t s h1 h2 h3 h4; rw [abs_le]; constructor <;> linarith
  have gY : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 →
      |Y t s| ≤ t.1 + t.2 + s.1 + s.2 := by
    intro t s h1 h2 h3 h4; have := hP.bdY t s h1 h2 h3 h4; rw [abs_le]; constructor <;> linarith
  have gY' : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 →
      |Y' t s| ≤ t.1 + t.2 + s.1 + s.2 := by
    intro t s h1 h2 h3 h4; have := hP'.bdY t s h1 h2 h3 h4; rw [abs_le]; constructor <;> linarith
  have gdX : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 →
      |X t s - X' t s| ≤ t.1 + t.2 + s.1 + s.2 := by
    intro t s h1 h2 h3 h4
    have a := hP.bdX t s h1 h2 h3 h4; have b := hP'.bdX t s h1 h2 h3 h4
    rw [abs_le]; constructor <;> linarith
  have gdY : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 →
      |Y t s - Y' t s| ≤ t.1 + t.2 + s.1 + s.2 := by
    intro t s h1 h2 h3 h4
    have a := hP.bdY t s h1 h2 h3 h4; have b := hP'.bdY t s h1 h2 h3 h4
    rw [abs_le]; constructor <;> linarith
  have iX := hint X hX gX
  have iX' := hint X' hX' gX'
  have iY := hint Y hY gY
  have iY' := hint Y' hY' gY'
  rw [idelta_eq _ _ u kA kB hsA hsB α γ δ hδ (hint _ (hX.sub hX') gdX) (hint _ (hY.sub hY') gdY),
    idelta_eq X Y u kA kB hsA hsB α γ δ hδ iX iY,
    idelta_eq X' Y' u kA kB hsA hsB α γ δ hδ iX' iY']
  have sX := shift_diff_int θ _ (single_nonneg kA δ hδ) _ iX
  have sX' := shift_diff_int θ _ (single_nonneg kA δ hδ) _ iX'
  have sY := shift_diff_int θ _ (single_nonneg kB δ hδ) _ iY
  have sY' := shift_diff_int θ _ (single_nonneg kB δ hδ) _ iY'
  have e1 := integral_sub sX sX'
  have e2 := integral_sub sY sY'
  simp only [θ] at e1 e2 ⊢
  rw [show ∀ a b c d : ℝ, a + b - (c + d) = (a - c) + (b - d) by intros; ring, ← e1, ← e2]
  congr 1 <;> congr 1 <;> ext r <;> ring

theorem idelta_small (X Y X' Y' : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hX : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => X p.1 p.2))
    (hY : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Y p.1 p.2))
    (hX' : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => X' p.1 p.2))
    (hY' : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Y' p.1 p.2))
    (hP : IsPair X Y) (hP' : IsPair X' Y') (u : ℝ × ℝ) (hu : u = (1, 0) ∨ u = (0, 1))
    (α γ : ℝ × ℝ) (hα1 : 0 < α.1) (hα2 : 0 < α.2) (hγ1 : 0 < γ.1) (hγ2 : 0 < γ.2) :
    ∃ K : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      |Idelta (fun t s => X t s - X' t s) (fun t s => Y t s - Y' t s) u δ α γ| ≤ K * δ ^ 2 := by
  obtain ⟨K1, hK1⟩ := pair_bounds X Y hX hY hP u hu α γ hα1 hα2 hγ1 hγ2
  obtain ⟨K2, hK2⟩ := pair_bounds X' Y' hX' hY' hP' u hu α γ hα1 hα2 hγ1 hγ2
  refine ⟨K1 + K2, fun δ hδ hδ1 => ?_⟩
  obtain ⟨a1, a2⟩ := hK1 δ hδ hδ1
  obtain ⟨b1, b2⟩ := hK2 δ hδ hδ1
  have hlin : Idelta (fun t s => X t s - X' t s) (fun t s => Y t s - Y' t s) u δ α γ =
      Idelta X Y u δ α γ - Idelta X' Y' u δ α γ :=
    idelta_sub X Y X' Y' hX hY hX' hY' hP hP' u hu α γ hα1 hα2 hγ1 hγ2 δ hδ
  have hK1n : 0 ≤ K1 * δ ^ 2 := by nlinarith
  have hK2n : 0 ≤ K2 * δ ^ 2 := by nlinarith
  rw [hlin, abs_le]
  constructor <;> nlinarith

/-- the integrated complementarity argument (assembled from `idelta_small`, `idelta_limit`):
two pairs, whose differences vanish on the own-value boundary, have
`α_h L(A) + γ_h L(B) = 0`. -/
theorem pair_laplace (X Y X' Y' : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hX : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => X p.1 p.2))
    (hY : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Y p.1 p.2))
    (hX' : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => X' p.1 p.2))
    (hY' : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Y' p.1 p.2))
    (hP : IsPair X Y) (hP' : IsPair X' Y')
    (hbX : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → (t.1 = 0 ∨ t.2 = 0) →
      X t s = X' t s)
    (hbY : ∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → (s.1 = 0 ∨ s.2 = 0) →
      Y t s = Y' t s) :
    ∀ α γ : ℝ × ℝ, 0 < α.1 → 0 < α.2 → 0 < γ.1 → 0 < γ.2 →
      α.1 * lap (fun t s => X t s - X' t s) α γ + γ.1 * lap (fun t s => Y t s - Y' t s) α γ = 0 ∧
      α.2 * lap (fun t s => X t s - X' t s) α γ + γ.2 * lap (fun t s => Y t s - Y' t s) α γ = 0 := by
  intro α γ hα1 hα2 hγ1 hγ2
  have main : ∀ u : ℝ × ℝ, (u = (1, 0) ∨ u = (0, 1)) →
      (α.1 * u.1 + α.2 * u.2) * lap (fun t s => X t s - X' t s) α γ +
        (γ.1 * u.1 + γ.2 * u.2) * lap (fun t s => Y t s - Y' t s) α γ = 0 := by
    intro u hu
    obtain ⟨K, hK⟩ := idelta_small X Y X' Y' hX hY hX' hY' hP hP' u hu α γ hα1 hα2 hγ1 hγ2
    have hlim := idelta_limit (fun t s => X t s - X' t s) (fun t s => Y t s - Y' t s)
      (hX.sub hX') (hY.sub hY')
      (by
        intro t s h1 h2 h3 h4
        have a1 := hP.bdX t s h1 h2 h3 h4
        have a2 := hP'.bdX t s h1 h2 h3 h4
        rw [abs_le]; constructor <;> linarith)
      (by
        intro t s h1 h2 h3 h4
        have a1 := hP.bdY t s h1 h2 h3 h4
        have a2 := hP'.bdY t s h1 h2 h3 h4
        rw [abs_le]; constructor <;> linarith)
      (by
        intro t s u δ hu h1 h2 h3 h4 hδ
        have a1 := hP.lipX t s u δ hu h1 h2 h3 h4 hδ
        have a2 := hP'.lipX t s u δ hu h1 h2 h3 h4 hδ
        simp only [abs_le] at a1 a2 ⊢
        constructor <;> linarith [a1.1, a1.2, a2.1, a2.2])
      (by
        intro t s u δ hu h1 h2 h3 h4 hδ
        have a1 := hP.lipY t s u δ hu h1 h2 h3 h4 hδ
        have a2 := hP'.lipY t s u δ hu h1 h2 h3 h4 hδ
        simp only [abs_le] at a1 a2 ⊢
        constructor <;> linarith [a1.1, a1.2, a2.1, a2.2])
      (fun t s h1 h2 h3 h4 hz => by simp [hbX t s h1 h2 h3 h4 hz])
      (fun t s h1 h2 h3 h4 hz => by simp [hbY t s h1 h2 h3 h4 hz])
      u hu α γ hα1 hα2 hγ1 hγ2
    have h0 : Filter.Tendsto (fun δ : ℝ => δ⁻¹ * Idelta (fun t s => X t s - X' t s)
        (fun t s => Y t s - Y' t s) u δ α γ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hK0 : Filter.Tendsto (fun δ : ℝ => K * δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have : Filter.Tendsto (fun δ : ℝ => K * δ) (nhds 0) (nhds (K * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ hK0
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with δ hδ
      have := hK δ hδ.1 hδ.2.le
      rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hδ.1]
      calc δ⁻¹ * |Idelta _ _ u δ α γ| ≤ δ⁻¹ * (K * δ ^ 2) :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 hδ.1.le)
        _ = K * δ := by field_simp
    exact tendsto_nhds_unique hlim h0
  constructor
  · simpa using main (1, 0) (Or.inl rfl)
  · simpa using main (0, 1) (Or.inr rfl)

open FracTruthSched.Dev.Reg Filter Topology

section Vers
variable {W Wj : ℝ × ℝ → ℝ × ℝ → ℝ}

lemma hypW (h : SepData W Wj) : RegHyp W where
  lip := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ s h1 h2 h3 h4 h5 h6
    dsimp only at *
    have a := h.mono1 x1 y1 x2 s h1 h3 h2 h5 h6
    have b := h.mono2 x2 y2 y1 s h2 h4 (h1.trans h3) h5 h6
    constructor <;> linarith [a.1, a.2, b.1, b.2]
  mono := fun t s s' h1 h2 h3 h4 h5 h6 => h.mono_s t s s' h1 h2 h3 h4 h5 h6

lemma hypWj (h : SepData W Wj) : RegHyp (fun a b => Wj b a) where
  lip := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ t h1 h2 h3 h4 h5 h6
    dsimp only at *
    have a := h.monoj1 x1 y1 x2 t h1 h3 h2 h5 h6
    have b := h.monoj2 x2 y2 y1 t h2 h4 (h1.trans h3) h5 h6
    constructor <;> linarith [a.1, a.2, b.1, b.2]
  mono := fun s t t' h1 h2 h3 h4 h5 h6 => h.mono_tj t t' s h3 h4 h1 h2 h5 h6

lemma pairF_u (h : SepData W Wj) (u : ℝ × ℝ) (hu : u = (1, 0) ∨ u = (0, 1)) (t s : ℝ × ℝ)
    (δ : ℝ) (h1 : 0 ≤ t.1) (h2 : 0 ≤ t.2) (h3 : 0 ≤ s.1) (h4 : 0 ≤ s.2) (hδ : 0 < δ) :
    W (t.1 + δ * u.1, t.2 + δ * u.2) s - W t s +
      (Wj t (s.1 + δ * u.1, s.2 + δ * u.2) - Wj t s) ≤ δ := by
  rcases hu with rfl | rfl
  · simpa using h.pairF1 t s δ h1 h2 h3 h4 hδ
  · simpa using h.pairF2 t s δ h1 h2 h3 h4 hδ

lemma pairB_u (h : SepData W Wj) (u : ℝ × ℝ) (hu : u = (1, 0) ∨ u = (0, 1)) (t s : ℝ × ℝ)
    (δ : ℝ) (h1 : 0 ≤ t.1) (h2 : 0 ≤ t.2) (h3 : 0 ≤ s.1) (h4 : 0 ≤ s.2) (hδ : 0 < δ)
    (g1 : δ * u.1 ≤ t.1) (g2 : δ * u.2 ≤ t.2) (g3 : δ * u.1 ≤ s.1) (g4 : δ * u.2 ≤ s.2) :
    δ ≤ W t s - W (t.1 - δ * u.1, t.2 - δ * u.2) s +
      (Wj t s - Wj t (s.1 - δ * u.1, s.2 - δ * u.2)) := by
  rcases hu with rfl | rfl
  · simp at g1 g3 ⊢
    have := h.pairB1 t s δ h2 h4 hδ g1 g3
    linarith
  · simp at g2 g4 ⊢
    have := h.pairB2 t s δ h1 h3 hδ g2 g4
    linarith

lemma smul_eq (t u : ℝ × ℝ) (δ : ℝ) : t + δ • u = (t.1 + δ * u.1, t.2 + δ * u.2) := by
  ext <;> simp

lemma smul_eq' (t u : ℝ × ℝ) (δ : ℝ) : t - δ • u = (t.1 - δ * u.1, t.2 - δ * u.2) := by
  ext <;> simp

lemma u_nn (u : ℝ × ℝ) (hu : u = (1, 0) ∨ u = (0, 1)) :
    0 ≤ u.1 ∧ 0 ≤ u.2 ∧ u.1 + u.2 = 1 := by
  rcases hu with rfl | rfl <;> norm_num

lemma tend4 : Tendsto (fun ε : ℝ => 4 * ε) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Continuous (fun ε : ℝ => 4 * ε) := continuous_const.mul continuous_id
  have := (h0.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa using this

/-- The regularized pair. -/
noncomputable def R (W : ℝ × ℝ → ℝ × ℝ → ℝ) (t s : ℝ × ℝ) : ℝ := reg W t s
noncomputable def Rj (Wj : ℝ × ℝ → ℝ × ℝ → ℝ) (t s : ℝ × ℝ) : ℝ := reg (fun a b => Wj b a) s t

lemma R_lim (h : SepData W Wj) (t s : ℝ × ℝ) (h1 : 0 ≤ t.1) (h2 : 0 ≤ t.2) (h3 : 0 < s.1)
    (h4 : 0 < s.2) : Tendsto (fun ε : ℝ => W t (s.1 - ε, s.2 - ε)) (𝓝[>] 0) (𝓝 (R W t s)) :=
  reg_tendsto (hypW h) t s h1 h2 h3 h4

lemma Rj_lim (h : SepData W Wj) (t s : ℝ × ℝ) (h1 : 0 < t.1) (h2 : 0 < t.2) (h3 : 0 ≤ s.1)
    (h4 : 0 ≤ s.2) : Tendsto (fun ε : ℝ => Wj (t.1 - ε, t.2 - ε) s) (𝓝[>] 0) (𝓝 (Rj Wj t s)) :=
  reg_tendsto (hypWj h) s t h3 h4 h1 h2

lemma R_lip (h : SepData W Wj) (t t' s : ℝ × ℝ) (h1 : 0 ≤ t.1) (h2 : 0 ≤ t.2) (h3 : t.1 ≤ t'.1)
    (h4 : t.2 ≤ t'.2) : R W t s ≤ R W t' s ∧ R W t' s ≤ R W t s + ((t'.1 - t.1) + (t'.2 - t.2)) :=
  reg_lip (hypW h) t t' s h1 h2 h3 h4

lemma Rj_lip (h : SepData W Wj) (t s s' : ℝ × ℝ) (h1 : 0 ≤ s.1) (h2 : 0 ≤ s.2) (h3 : s.1 ≤ s'.1)
    (h4 : s.2 ≤ s'.2) :
    Rj Wj t s ≤ Rj Wj t s' ∧ Rj Wj t s' ≤ Rj Wj t s + ((s'.1 - s.1) + (s'.2 - s.2)) :=
  reg_lip (hypWj h) s s' t h1 h2 h3 h4

/-- The pair `(X, Y)`. -/
lemma pairXY (h : SepData W Wj) :
    IsPair (fun t s => R W t s - R W 0 s) (fun t s => Rj Wj t s - Rj Wj t 0) := by
  have hW := hypW h
  have hj := hypWj h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t s h1 h2 _ _
    have := R_lip h 0 t s le_rfl le_rfl h1 h2
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at this
    constructor <;> linarith [this.1, this.2]
  · intro t s _ _ h3 h4
    have := Rj_lip h t 0 s le_rfl le_rfl h3 h4
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at this
    constructor <;> linarith [this.1, this.2]
  · intro t s u δ hu h1 h2 _ _ hδ
    obtain ⟨u1, u2, -⟩ := u_nn u hu
    rw [smul_eq]
    have := R_lip h t (t.1 + δ * u.1, t.2 + δ * u.2) s h1 h2
      (by dsimp only; nlinarith) (by dsimp only; nlinarith)
    have e := u_nn u hu
    dsimp only at this
    rw [abs_le]; constructor <;> nlinarith [this.1, this.2]
  · intro t s u δ hu _ _ h3 h4 hδ
    obtain ⟨u1, u2, -⟩ := u_nn u hu
    rw [smul_eq]
    have := Rj_lip h t s (s.1 + δ * u.1, s.2 + δ * u.2) h3 h4
      (by dsimp only; nlinarith) (by dsimp only; nlinarith)
    have e := u_nn u hu
    dsimp only at this
    rw [abs_le]; constructor <;> nlinarith [this.1, this.2]
  · -- forward inequality
    intro t s u δ hu h1 h2 h3 h4 hδ
    obtain ⟨u1, u2, u12⟩ := u_nn u hu
    rw [smul_eq, smul_eq]
    set tp : ℝ × ℝ := (t.1 + δ * u.1, t.2 + δ * u.2) with htp
    set sp : ℝ × ℝ := (s.1 + δ * u.1, s.2 + δ * u.2) with hsp
    have tp1 : 0 ≤ tp.1 := by simp only [tp]; nlinarith
    have tp2 : 0 ≤ tp.2 := by simp only [tp]; nlinarith
    have sp1 : 0 ≤ sp.1 := by simp only [sp]; nlinarith
    have sp2 : 0 ≤ sp.2 := by simp only [sp]; nlinarith
    have T := (((R_lim h tp s tp1 tp2 h3 h4).sub (R_lim h t s h1.le h2.le h3 h4)).add
      ((Rj_lim h t sp h1 h2 sp1 sp2).sub (Rj_lim h t s h1 h2 h3.le h4.le))).sub tend4
    have m0 : 0 < min (min t.1 t.2) (min s.1 s.2) := lt_min (lt_min h1 h2) (lt_min h3 h4)
    have key : _ ≤ δ := le_of_tendsto T (by
      filter_upwards [Ioo_mem_nhdsGT m0] with ε hε
      have e0 := hε.1
      have et1 : ε < t.1 := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      have et2 : ε < t.2 := hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
      have es1 : ε < s.1 := hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have es2 : ε < s.2 := hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      set a : ℝ × ℝ := (t.1 - ε, t.2 - ε) with ha
      set b : ℝ × ℝ := (s.1 - ε, s.2 - ε) with hb
      have P := pairF_u h u hu a b δ (by simp only [a]; linarith) (by simp only [a]; linarith)
        (by simp only [b]; linarith) (by simp only [b]; linarith) hδ
      have L1 := hW.lip (a.1 + δ * u.1, a.2 + δ * u.2) tp b
        (by simp only [a]; nlinarith) (by simp only [a]; nlinarith)
        (by simp only [a, tp]; linarith) (by simp only [a, tp]; linarith)
        (by simp only [b]; linarith) (by simp only [b]; linarith)
      have L2 := hW.lip a t b (by simp only [a]; linarith) (by simp only [a]; linarith)
        (by simp only [a]; linarith) (by simp only [a]; linarith)
        (by simp only [b]; linarith) (by simp only [b]; linarith)
      have L3 := hj.lip (b.1 + δ * u.1, b.2 + δ * u.2) sp a
        (by simp only [b]; nlinarith) (by simp only [b]; nlinarith)
        (by simp only [b, sp]; linarith) (by simp only [b, sp]; linarith)
        (by simp only [a]; linarith) (by simp only [a]; linarith)
      have L4 := hj.lip b s a (by simp only [b]; linarith) (by simp only [b]; linarith)
        (by simp only [b]; linarith) (by simp only [b]; linarith)
        (by simp only [a]; linarith) (by simp only [a]; linarith)
      simp only [a, b, tp, sp] at P L1 L2 L3 L4 ⊢
      linarith [L1.1, L1.2, L2.1, L2.2, L3.1, L3.2, L4.1, L4.2])
    simp only [sub_zero] at key
    linarith
  · -- backward inequality
    intro t s u δ hu hδ g1 g2 g3 g4
    obtain ⟨u1, u2, u12⟩ := u_nn u hu
    rw [smul_eq', smul_eq']
    have h1 : 0 < t.1 := by nlinarith
    have h2 : 0 < t.2 := by nlinarith
    have h3 : 0 < s.1 := by nlinarith
    have h4 : 0 < s.2 := by nlinarith
    set tm : ℝ × ℝ := (t.1 - δ * u.1, t.2 - δ * u.2) with htm
    set sm : ℝ × ℝ := (s.1 - δ * u.1, s.2 - δ * u.2) with hsm
    have T := (((R_lim h t s h1.le h2.le h3 h4).sub (R_lim h tm s g1.le g2.le h3 h4)).add
      ((Rj_lim h t s h1 h2 h3.le h4.le).sub (Rj_lim h t sm h1 h2 g3.le g4.le))).add tend4
    have m0 : 0 < min (min (t.1 - δ * u.1) (t.2 - δ * u.2)) (min (s.1 - δ * u.1) (s.2 - δ * u.2)) :=
      lt_min (lt_min g1 g2) (lt_min g3 g4)
    have key : δ ≤ _ := ge_of_tendsto T (by
      filter_upwards [Ioo_mem_nhdsGT m0] with ε hε
      have e0 := hε.1
      have et1 : ε < t.1 - δ * u.1 := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
      have et2 : ε < t.2 - δ * u.2 := hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
      have es1 : ε < s.1 - δ * u.1 := hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have es2 : ε < s.2 - δ * u.2 := hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have d1 : 0 ≤ δ * u.1 := by nlinarith
      have d2 : 0 ≤ δ * u.2 := by nlinarith
      set a : ℝ × ℝ := (t.1 - ε, t.2 - ε) with ha
      set b : ℝ × ℝ := (s.1 - ε, s.2 - ε) with hb
      have P := pairB_u h u hu a b δ (by simp only [a]; linarith) (by simp only [a]; linarith)
        (by simp only [b]; linarith) (by simp only [b]; linarith) hδ
        (by simp only [a]; linarith) (by simp only [a]; linarith)
        (by simp only [b]; linarith) (by simp only [b]; linarith)
      have L1 := hW.lip a t b (by simp only [a]; linarith) (by simp only [a]; linarith)
        (by simp only [a]; linarith) (by simp only [a]; linarith)
        (by simp only [b]; linarith) (by simp only [b]; linarith)
      have L2 := hW.lip (a.1 - δ * u.1, a.2 - δ * u.2) tm b
        (by simp only [a]; linarith) (by simp only [a]; linarith)
        (by simp only [a, tm]; linarith) (by simp only [a, tm]; linarith)
        (by simp only [b]; linarith) (by simp only [b]; linarith)
      have L3 := hj.lip b s a (by simp only [b]; linarith) (by simp only [b]; linarith)
        (by simp only [b]; linarith) (by simp only [b]; linarith)
        (by simp only [a]; linarith) (by simp only [a]; linarith)
      have L4 := hj.lip (b.1 - δ * u.1, b.2 - δ * u.2) sm a
        (by simp only [b]; linarith) (by simp only [b]; linarith)
        (by simp only [b, sm]; linarith) (by simp only [b, sm]; linarith)
        (by simp only [a]; linarith) (by simp only [a]; linarith)
      simp only [a, b, tm, sm] at P L1 L2 L3 L4 ⊢
      linarith [L1.1, L1.2, L2.1, L2.2, L3.1, L3.2, L4.1, L4.2])
    simp only [add_zero] at key
    linarith

/-- The axis-separated pair `(X', Y')`. -/
lemma pairXY' (h : SepData W Wj) :
    IsPair (fun t s => R W (t.1, 0) s + R W (0, t.2) s - 2 * R W 0 s)
      (fun t s => Rj Wj t (s.1, 0) + Rj Wj t (0, s.2) - 2 * Rj Wj t 0) := by
  have hW := hypW h
  have hj := hypWj h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t s h1 h2 _ _
    have a := R_lip h 0 (t.1, 0) s le_rfl le_rfl h1 le_rfl
    have b := R_lip h 0 (0, t.2) s le_rfl le_rfl le_rfl h2
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at a b
    constructor <;> linarith [a.1, a.2, b.1, b.2]
  · intro t s _ _ h3 h4
    have a := Rj_lip h t 0 (s.1, 0) le_rfl le_rfl h3 le_rfl
    have b := Rj_lip h t 0 (0, s.2) le_rfl le_rfl le_rfl h4
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at a b
    constructor <;> linarith [a.1, a.2, b.1, b.2]
  · intro t s u δ hu h1 h2 _ _ hδ
    rcases hu with rfl | rfl
    · simp only [smul_eq, mul_one, mul_zero, add_zero]
      have a := R_lip h (t.1, 0) (t.1 + δ, 0) s h1 le_rfl (by simp only; linarith) le_rfl
      simp only at a
      rw [abs_le]; constructor <;> linarith [a.1, a.2]
    · simp only [smul_eq, mul_one, mul_zero, add_zero]
      have a := R_lip h (0, t.2) (0, t.2 + δ) s le_rfl h2 le_rfl (by simp only; linarith)
      simp only at a
      rw [abs_le]; constructor <;> linarith [a.1, a.2]
  · intro t s u δ hu _ _ h3 h4 hδ
    rcases hu with rfl | rfl
    · simp only [smul_eq, mul_one, mul_zero, add_zero]
      have a := Rj_lip h t (s.1, 0) (s.1 + δ, 0) h3 le_rfl (by simp only; linarith) le_rfl
      simp only at a
      rw [abs_le]; constructor <;> linarith [a.1, a.2]
    · simp only [smul_eq, mul_one, mul_zero, add_zero]
      have a := Rj_lip h t (0, s.2) (0, s.2 + δ) le_rfl h4 le_rfl (by simp only; linarith)
      simp only at a
      rw [abs_le]; constructor <;> linarith [a.1, a.2]
  · intro t s u δ hu h1 h2 h3 h4 hδ
    have m0 : 0 < min (min t.1 t.2) (min s.1 s.2) := lt_min (lt_min h1 h2) (lt_min h3 h4)
    rcases hu with rfl | rfl
    · simp only [smul_eq, mul_one, mul_zero, add_zero]
      have T := (((R_lim h (t.1 + δ, 0) s (by simp only; linarith) le_rfl h3 h4).sub
        (R_lim h (t.1, 0) s h1.le le_rfl h3 h4)).add
        ((Rj_lim h t (s.1 + δ, 0) h1 h2 (by simp only; linarith) le_rfl).sub
          (Rj_lim h t (s.1, 0) h1 h2 h3.le le_rfl))).sub tend4
      have key : _ ≤ δ := le_of_tendsto T (by
        filter_upwards [Ioo_mem_nhdsGT m0] with ε hε
        have e0 := hε.1
        have et1 : ε < t.1 := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
        have et2 : ε < t.2 := hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
        have es1 : ε < s.1 := hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
        have es2 : ε < s.2 := hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
        have A1 := h.ax1 (t.1 + δ) (s.1 - ε, s.2 - ε) (by linarith) (by simp only; linarith)
          (by simp only; linarith)
        have A2 := h.ax1 t.1 (s.1 - ε, s.2 - ε) (by linarith) (by simp only; linarith)
          (by simp only; linarith)
        have A3 := h.ax3 (t.1 - ε, t.2 - ε) (s.1 + δ) (by simp only; linarith)
          (by simp only; linarith) (by linarith)
        have A4 := h.ax3 (t.1 - ε, t.2 - ε) s.1 (by simp only; linarith)
          (by simp only; linarith) (by linarith)
        have P := h.pairF1 (t.1 - ε, 0) (s.1 - ε, 0) δ (by simp only; linarith) le_rfl
          (by simp only; linarith) le_rfl hδ
        have L1 := hW.lip (t.1 - ε + δ, 0) (t.1 + δ, 0) (s.1 - ε, 0) (by simp only; linarith)
          le_rfl (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl
        have L2 := hW.lip (t.1 - ε, 0) (t.1, 0) (s.1 - ε, 0) (by simp only; linarith)
          le_rfl (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl
        have L3 := hj.lip (s.1 - ε + δ, 0) (s.1 + δ, 0) (t.1 - ε, 0) (by simp only; linarith)
          le_rfl (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl
        have L4 := hj.lip (s.1 - ε, 0) (s.1, 0) (t.1 - ε, 0) (by simp only; linarith)
          le_rfl (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl
        simp only at A1 A2 A3 A4 P L1 L2 L3 L4 ⊢
        linarith [L1.1, L1.2, L2.1, L2.2, L3.1, L3.2, L4.1, L4.2])
      simp only [sub_zero] at key
      linarith
    · simp only [smul_eq, mul_one, mul_zero, add_zero]
      have T := (((R_lim h (0, t.2 + δ) s le_rfl (by simp only; linarith) h3 h4).sub
        (R_lim h (0, t.2) s le_rfl h2.le h3 h4)).add
        ((Rj_lim h t (0, s.2 + δ) h1 h2 le_rfl (by simp only; linarith)).sub
          (Rj_lim h t (0, s.2) h1 h2 le_rfl h4.le))).sub tend4
      have key : _ ≤ δ := le_of_tendsto T (by
        filter_upwards [Ioo_mem_nhdsGT m0] with ε hε
        have e0 := hε.1
        have et1 : ε < t.1 := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
        have et2 : ε < t.2 := hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
        have es1 : ε < s.1 := hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
        have es2 : ε < s.2 := hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
        have A1 := h.ax2 (t.2 + δ) (s.1 - ε, s.2 - ε) (by linarith) (by simp only; linarith)
          (by simp only; linarith)
        have A2 := h.ax2 t.2 (s.1 - ε, s.2 - ε) (by linarith) (by simp only; linarith)
          (by simp only; linarith)
        have A3 := h.ax4 (t.1 - ε, t.2 - ε) (s.2 + δ) (by simp only; linarith)
          (by simp only; linarith) (by linarith)
        have A4 := h.ax4 (t.1 - ε, t.2 - ε) s.2 (by simp only; linarith)
          (by simp only; linarith) (by linarith)
        have P := h.pairF2 (0, t.2 - ε) (0, s.2 - ε) δ le_rfl (by simp only; linarith)
          le_rfl (by simp only; linarith) hδ
        have L1 := hW.lip (0, t.2 - ε + δ) (0, t.2 + δ) (0, s.2 - ε) le_rfl
          (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl (by simp only; linarith)
        have L2 := hW.lip (0, t.2 - ε) (0, t.2) (0, s.2 - ε) le_rfl
          (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl (by simp only; linarith)
        have L3 := hj.lip (0, s.2 - ε + δ) (0, s.2 + δ) (0, t.2 - ε) le_rfl
          (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl (by simp only; linarith)
        have L4 := hj.lip (0, s.2 - ε) (0, s.2) (0, t.2 - ε) le_rfl
          (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl (by simp only; linarith)
        simp only at A1 A2 A3 A4 P L1 L2 L3 L4 ⊢
        linarith [L1.1, L1.2, L2.1, L2.2, L3.1, L3.2, L4.1, L4.2])
      simp only [sub_zero] at key
      linarith
  · intro t s u δ hu hδ g1 g2 g3 g4
    rcases hu with rfl | rfl
    · simp only [smul_eq', mul_one, mul_zero, sub_zero] at g1 g2 g3 g4 ⊢
      have m0 : 0 < min (min (t.1 - δ) t.2) (min (s.1 - δ) s.2) :=
        lt_min (lt_min g1 g2) (lt_min g3 g4)
      have T := (((R_lim h (t.1, 0) s (by linarith) le_rfl (by linarith) g4).sub
        (R_lim h (t.1 - δ, 0) s g1.le le_rfl (by linarith) g4)).add
        ((Rj_lim h t (s.1, 0) (by linarith) g2 (by simp only; linarith) le_rfl).sub
          (Rj_lim h t (s.1 - δ, 0) (by linarith) g2 g3.le le_rfl))).add tend4
      have key : δ ≤ _ := ge_of_tendsto T (by
        filter_upwards [Ioo_mem_nhdsGT m0] with ε hε
        have e0 := hε.1
        have et1 : ε < t.1 - δ := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
        have et2 : ε < t.2 := hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
        have es1 : ε < s.1 - δ := hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
        have es2 : ε < s.2 := hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
        have A1 := h.ax1 t.1 (s.1 - ε, s.2 - ε) (by linarith) (by simp only; linarith)
          (by simp only; linarith)
        have A2 := h.ax1 (t.1 - δ) (s.1 - ε, s.2 - ε) (by linarith) (by simp only; linarith)
          (by simp only; linarith)
        have A3 := h.ax3 (t.1 - ε, t.2 - ε) s.1 (by simp only; linarith)
          (by simp only; linarith) (by linarith)
        have A4 := h.ax3 (t.1 - ε, t.2 - ε) (s.1 - δ) (by simp only; linarith)
          (by simp only; linarith) (by linarith)
        have P := h.pairB1 (t.1 - ε, 0) (s.1 - ε, 0) δ le_rfl le_rfl hδ
          (by simp only; linarith) (by simp only; linarith)
        have L1 := hW.lip (t.1 - ε, 0) (t.1, 0) (s.1 - ε, 0) (by simp only; linarith)
          le_rfl (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl
        have L2 := hW.lip (t.1 - ε - δ, 0) (t.1 - δ, 0) (s.1 - ε, 0) (by simp only; linarith)
          le_rfl (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl
        have L3 := hj.lip (s.1 - ε, 0) (s.1, 0) (t.1 - ε, 0) (by simp only; linarith)
          le_rfl (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl
        have L4 := hj.lip (s.1 - ε - δ, 0) (s.1 - δ, 0) (t.1 - ε, 0) (by simp only; linarith)
          le_rfl (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl
        simp only at A1 A2 A3 A4 P L1 L2 L3 L4 ⊢
        linarith [L1.1, L1.2, L2.1, L2.2, L3.1, L3.2, L4.1, L4.2])
      simp only [add_zero] at key
      linarith
    · simp only [smul_eq', mul_one, mul_zero, sub_zero] at g1 g2 g3 g4 ⊢
      have m0 : 0 < min (min t.1 (t.2 - δ)) (min s.1 (s.2 - δ)) :=
        lt_min (lt_min g1 g2) (lt_min g3 g4)
      have T := (((R_lim h (0, t.2) s le_rfl (by linarith) g3 (by linarith)).sub
        (R_lim h (0, t.2 - δ) s le_rfl g2.le g3 (by linarith))).add
        ((Rj_lim h t (0, s.2) g1 (by linarith) le_rfl (by simp only; linarith)).sub
          (Rj_lim h t (0, s.2 - δ) g1 (by linarith) le_rfl g4.le))).add tend4
      have key : δ ≤ _ := ge_of_tendsto T (by
        filter_upwards [Ioo_mem_nhdsGT m0] with ε hε
        have e0 := hε.1
        have et1 : ε < t.1 := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
        have et2 : ε < t.2 - δ := hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
        have es1 : ε < s.1 := hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
        have es2 : ε < s.2 - δ := hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
        have A1 := h.ax2 t.2 (s.1 - ε, s.2 - ε) (by linarith) (by simp only; linarith)
          (by simp only; linarith)
        have A2 := h.ax2 (t.2 - δ) (s.1 - ε, s.2 - ε) (by linarith) (by simp only; linarith)
          (by simp only; linarith)
        have A3 := h.ax4 (t.1 - ε, t.2 - ε) s.2 (by simp only; linarith)
          (by simp only; linarith) (by linarith)
        have A4 := h.ax4 (t.1 - ε, t.2 - ε) (s.2 - δ) (by simp only; linarith)
          (by simp only; linarith) (by linarith)
        have P := h.pairB2 (0, t.2 - ε) (0, s.2 - ε) δ le_rfl le_rfl hδ
          (by simp only; linarith) (by simp only; linarith)
        have L1 := hW.lip (0, t.2 - ε) (0, t.2) (0, s.2 - ε) le_rfl
          (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl (by simp only; linarith)
        have L2 := hW.lip (0, t.2 - ε - δ) (0, t.2 - δ) (0, s.2 - ε) le_rfl
          (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl (by simp only; linarith)
        have L3 := hj.lip (0, s.2 - ε) (0, s.2) (0, t.2 - ε) le_rfl
          (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl (by simp only; linarith)
        have L4 := hj.lip (0, s.2 - ε - δ) (0, s.2 - δ) (0, t.2 - ε) le_rfl
          (by simp only; linarith) le_rfl (by simp only; linarith) le_rfl (by simp only; linarith)
        simp only at A1 A2 A3 A4 P L1 L2 L3 L4 ⊢
        linarith [L1.1, L1.2, L2.1, L2.2, L3.1, L3.2, L4.1, L4.2])
      simp only [add_zero] at key
      linarith

end Vers

/-- (V) Borel versions: from `SepData` produce measurable pairs `(X, Y)`, `(X', Y')`
(`X = Ŵ(t;s) - Ŵ(0;s)`, `X' = Ũ₁(t₁,s₁) + Ũ₂(t₂,s₂)`, the one-task parts, with `Ŵ(t;s) =
sup_{a < s, a ∈ ℚ²} W(t;a)`), agreeing a.e. in `s` with the second difference of `W`. -/
theorem versions (W Wj : ℝ × ℝ → ℝ × ℝ → ℝ) (h : SepData W Wj) :
    ∃ X Y X' Y' : ℝ × ℝ → ℝ × ℝ → ℝ,
      Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => X p.1 p.2) ∧
      Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Y p.1 p.2) ∧
      Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => X' p.1 p.2) ∧
      Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => Y' p.1 p.2) ∧
      IsPair X Y ∧ IsPair X' Y' ∧
      (∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → (t.1 = 0 ∨ t.2 = 0) →
        X t s = X' t s) ∧
      (∀ t s : ℝ × ℝ, 0 ≤ t.1 → 0 ≤ t.2 → 0 ≤ s.1 → 0 ≤ s.2 → (s.1 = 0 ∨ s.2 = 0) →
        Y t s = Y' t s) ∧
      (∀ s : ℝ × ℝ, 0 < s.1 → 0 < s.2 →
        ContinuousOn (fun t => X t s - X' t s) (Set.Ici (0 : ℝ × ℝ))) ∧
      (∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))), ∀ t : ℝ × ℝ,
        0 ≤ t.1 → 0 ≤ t.2 →
        X t s - X' t s = W (t.1, t.2) s - W (t.1, 0) s - W (0, t.2) s + W (0, 0) s) := by
  have mW := reg_measurable (hypW h)
  have mj := reg_measurable (hypWj h)
  have cW := reg_continuous (hypW h)
  refine ⟨fun t s => R W t s - R W 0 s, fun t s => Rj Wj t s - Rj Wj t 0,
    fun t s => R W (t.1, 0) s + R W (0, t.2) s - 2 * R W 0 s,
    fun t s => Rj Wj t (s.1, 0) + Rj Wj t (0, s.2) - 2 * Rj Wj t 0,
    ?_, ?_, ?_, ?_, pairXY h, pairXY' h, ?_, ?_, ?_, ?_⟩
  · exact mW.sub (mW.comp (measurable_const.prodMk measurable_snd))
  · exact (mj.comp measurable_swap).sub (mj.comp (measurable_const.prodMk measurable_fst))
  · exact ((mW.comp (((measurable_fst.comp measurable_fst).prodMk measurable_const).prodMk
      measurable_snd)).add (mW.comp ((measurable_const.prodMk
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd))).sub
      (measurable_const.mul (mW.comp (measurable_const.prodMk measurable_snd)))
  · exact ((mj.comp (((measurable_fst.comp measurable_snd).prodMk measurable_const).prodMk
      measurable_fst)).add (mj.comp ((measurable_const.prodMk
        (measurable_snd.comp measurable_snd)).prodMk measurable_fst))).sub
      (measurable_const.mul (mj.comp (measurable_const.prodMk measurable_fst)))
  · rintro ⟨t1, t2⟩ s _ _ _ _ ht
    rcases ht with h0 | h0 <;> simp only at h0 <;> subst h0 <;> simp <;>
      rw [show ((0:ℝ), (0:ℝ)) = (0 : ℝ × ℝ) from rfl] <;> ring
  · rintro t ⟨s1, s2⟩ _ _ _ _ hs
    rcases hs with h0 | h0 <;> simp only at h0 <;> subst h0 <;> simp <;>
      rw [show ((0:ℝ), (0:ℝ)) = (0 : ℝ × ℝ) from rfl] <;> ring
  · intro s _ _
    have c1 : Continuous (fun t : ℝ × ℝ => reg W t s) := cW s
    have c2 : Continuous (fun t : ℝ × ℝ => reg W (t.1, 0) s) :=
      c1.comp (continuous_fst.prodMk continuous_const)
    have c3 : Continuous (fun t : ℝ × ℝ => reg W (0, t.2) s) :=
      c1.comp (continuous_const.prodMk continuous_snd)
    exact ((c1.sub continuous_const).sub ((c2.add c3).sub continuous_const)).continuousOn
  · filter_upwards [reg_ae (hypW h)] with s hs t h1 h2
    simp only [R]
    rw [hs t h1 h2, hs (t.1, 0) h1 le_rfl, hs (0, t.2) le_rfl h2, hs 0 le_rfl le_rfl]
    simp only [Prod.mk.eta, Prod.mk_zero_zero]
    ring

/-- ANALYTIC CORE, assembled from `versions`, `pair_laplace`, `laplace_vanish`, `ae_to_all`. -/
theorem separation (W Wj : ℝ × ℝ → ℝ × ℝ → ℝ) (h : SepData W Wj) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))), ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → 0 ≤ t₂ →
      W (t₁, t₂) s - W (t₁, 0) s - W (0, t₂) s + W (0, 0) s = 0 := by
  obtain ⟨X, Y, X', Y', mX, mY, mX', mY', hP, hP', hbX, hbY, hcont, hagree⟩ :=
    versions W Wj h
  have hrel := pair_laplace X Y X' Y' mX mY mX' mY' hP hP' hbX hbY
  have hA := laplace_vanish (fun t s => X t s - X' t s) (fun t s => Y t s - Y' t s)
    (mX.sub mX') (mY.sub mY')
    (by
      intro t s h1 h2 h3 h4
      have a1 := hP.bdX t s h1 h2 h3 h4
      have a2 := hP'.bdX t s h1 h2 h3 h4
      rw [abs_le]; constructor <;> linarith)
    (by
      intro t s h1 h2 h3 h4
      have a1 := hP.bdY t s h1 h2 h3 h4
      have a2 := hP'.bdY t s h1 h2 h3 h4
      rw [abs_le]; constructor <;> linarith)
    hrel
  have hB := ae_to_all (fun t s => X t s - X' t s) (mX.sub mX') hcont hA
  filter_upwards [hB, hagree] with s h1 h2 t₁ t₂ ht1 ht2
  have := h1 (t₁, t₂) ht1 ht2
  rw [h2 (t₁, t₂) ht1 ht2] at this
  exact this

variable {n ℓ : ℕ}

/-! ### Mechanism-side lemmas -/

lemma sandwich (M : FracMech n (CoreTask n ℓ)) (htruth : IsTruthfulOn IsGraphInput M)
    (u : Fin n) (X X2 : Fin n → CoreTask n ℓ → ℝ) (g : CoreTask n ℓ)
    (hX : IsGraphInput X) (hX2 : IsGraphInput X2)
    (h : ∀ v h', (v, h') ≠ (u, g) → X v h' = X2 v h') :
    (X2 u g - X u g) * M.x X2 u g ≤ disutility M X2 u - disutility M X u ∧
    disutility M X2 u - disutility M X u ≤ (X2 u g - X u g) * M.x X u g := by
  have hsum : ∀ (a b y : CoreTask n ℓ → ℝ), (∀ k, k ≠ g → b k = a k) →
      ∑ k, b k * y k - ∑ k, a k * y k = (b g - a g) * y g := by
    intro a b y hh
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single g]
    · ring
    · intro k _ hk; rw [hh k hk]; ring
    · simp
  have hb : ∀ k, k ≠ g → X2 u k = X u k := fun k hk =>
    (h u k (fun e => hk (Prod.mk.inj e).2)).symm
  have hX2eq : Function.update X u (X2 u) = X2 := by
    funext v h'
    by_cases hv : v = u
    · subst hv; simp
    · rw [Function.update_of_ne hv]
      exact h v h' (fun e => hv (Prod.mk.inj e).1)
  have h1 := htruth X hX u (X2 u) (by rw [hX2eq]; exact hX2)
  have e2 : Function.update X2 u (X u) = X := by
    funext v h'
    by_cases hv : v = u
    · subst hv; simp
    · rw [Function.update_of_ne hv]
      exact (h v h' (fun e => hv (Prod.mk.inj e).1)).symm
  have h2 := htruth X2 hX2 u (X u) (by rw [e2]; exact hX)
  rw [hX2eq] at h1
  rw [e2] at h2
  have e4 : Function.update X2 u 0 = Function.update X u 0 := by
    rw [← hX2eq, Function.update_idem]
  have s1 := hsum (X u) (X2 u) (M.x X2 u) hb
  have s2 := hsum (X u) (X2 u) (M.x X u) hb
  unfold disutility
  rw [e4]
  constructor <;> linarith

lemma inc_three {a b c : Fin n} {e : CoreTask n ℓ} (he : e.isLeft = true)
    (ha : incident a e) (hb : incident b e) (hc : incident c e)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  rcases e with ⟨q, k⟩ | k
  · simp only [incident] at ha hb hc
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
      first
      | exact hab (ha.trans hb.symm)
      | exact hac (ha.trans hc.symm)
      | exact hbc (hb.trans hc.symm)
  · simp at he

lemma sum_two (M : FracMech n (CoreTask n ℓ)) (hel : IsEligible M)
    {Y : Fin n → CoreTask n ℓ → ℝ} (hY : IsGraphInput Y) (i u0 : Fin n) (hne : i ≠ u0)
    (e0 : CoreTask n ℓ) (hL : e0.isLeft = true) (hi : incident i e0) (hu : incident u0 e0) :
    ∑ w, M.x Y w e0 = M.x Y i e0 + M.x Y u0 e0 := by
  rw [← Finset.sum_subset (Finset.subset_univ {i, u0}), Finset.sum_pair hne]
  intro w _ hw
  apply hel Y hY w e0
  intro hwi
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  exact inc_three hL hi hu hwi hne (Ne.symm hw.1) (Ne.symm hw.2)

lemma riemann (T : ℝ) (hT : 0 ≤ T) (V V' x x' : ℝ → ℝ)
    (hV : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → V b - V a ≤ (b - a) * x a)
    (hV' : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → (b - a) * x' b ≤ V' b - V' a)
    (hxx : ∀ a, 0 ≤ a → a ≤ T → x a ≤ x' a) :
    V T - V 0 ≤ V' T - V' 0 := by
  have key : ∀ N : ℕ, 0 < N → ∀ m : ℕ, m ≤ N →
      (V (m * (T / N)) - V' (m * (T / N))) - (V 0 - V' 0) ≤
        (x' 0 - x' (m * (T / N))) * (T / N) := by
    intro N hN m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      have hNpos : (0:ℝ) < N := by exact_mod_cast hN
      have hδ0 : 0 ≤ T / (N:ℝ) := div_nonneg hT hNpos.le
      have hmN : ((m:ℝ) + 1) ≤ N := by exact_mod_cast hm
      have hNδ : (N:ℝ) * (T / N) = T := by field_simp
      have h1 : (m:ℝ) * (T / N) ≤ ((m+1:ℕ):ℝ) * (T / N) := by push_cast; nlinarith
      have h2 : ((m+1:ℕ):ℝ) * (T / N) ≤ T := by
        have := mul_le_mul_of_nonneg_right hmN hδ0
        rw [hNδ] at this; push_cast; linarith
      have h0 : 0 ≤ (m:ℝ) * (T / N) := by positivity
      have hd : ((m+1:ℕ):ℝ) * (T / N) - m * (T / N) = T / N := by push_cast; ring
      have a1 := hV (m * (T / N)) (((m+1:ℕ):ℝ) * (T / N)) h0 h1 h2
      have a2 := hV' (m * (T / N)) (((m+1:ℕ):ℝ) * (T / N)) h0 h1 h2
      have a3 := hxx (m * (T / N)) h0 (le_trans h1 h2)
      have a4 := mul_le_mul_of_nonneg_right a3 hδ0
      rw [hd] at a1 a2
      nlinarith
  by_contra hcon
  push Not at hcon
  have hDpos : 0 < (V T - V 0) - (V' T - V' 0) := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (((x' 0 - x' T) * T) / ((V T - V 0) - (V' T - V' 0)))
  have hMpos : (0:ℝ) < ((N+1:ℕ):ℝ) := by positivity
  have k := key (N+1) (by omega) (N+1) le_rfl
  have hT' : ((N+1:ℕ):ℝ) * (T / ((N+1:ℕ):ℝ)) = T := by field_simp
  rw [hT'] at k
  have e : (x' 0 - x' T) * (T / ((N+1:ℕ):ℝ)) = ((x' 0 - x' T) * T) / ((N+1:ℕ):ℝ) := by ring
  rw [e, le_div_iff₀ hMpos] at k
  rw [div_lt_iff₀ hDpos] at hN
  have : (N:ℝ) < ((N+1:ℕ):ℝ) := by push_cast; linarith
  nlinarith


lemma zti_x (M : FracMech n (CoreTask n ℓ)) (hzti : HasZeroTypeIrrelevance M)
    {X X2 : Fin n → CoreTask n ℓ → ℝ} (hX : IsGraphInput X) (hX2 : IsGraphInput X2)
    (h : CoreTask n ℓ) (hL : h.isLeft = true) (a : Fin n) (ha : incident a h)
    (h0 : X a h = 0) (h20 : X2 a h = 0) (hag : ∀ v g, g ≠ h → X v g = X2 v g)
    (u : Fin n) (g : CoreTask n ℓ) (hg : g ≠ h) : M.x X u g = M.x X2 u g :=
  hzti X X2 hX hX2 h hL hag ⟨a, ha, h0⟩ ⟨a, ha, h20⟩ u g hg

lemma d_bounds (M : FracMech n (CoreTask n ℓ)) (hfeas : IsFeasibleOn IsGraphInput M)
    (htruth : IsTruthfulOn IsGraphInput M) (u : Fin n) (g : CoreTask n ℓ)
    (X X2 : Fin n → CoreTask n ℓ → ℝ) (hX : IsGraphInput X) (hX2 : IsGraphInput X2)
    (h : ∀ v h', (v, h') ≠ (u, g) → X v h' = X2 v h') (hle : X u g ≤ X2 u g) :
    0 ≤ disutility M X2 u - disutility M X u ∧
      disutility M X2 u - disutility M X u ≤ X2 u g - X u g := by
  obtain ⟨s1, s2⟩ := sandwich M htruth u X X2 g hX hX2 h
  have a1 := (hfeas X hX).1 u g
  have a2 := (hfeas X2 hX2).1 u g
  have d0 : 0 ≤ X2 u g - X u g := by linarith
  constructor
  · nlinarith [mul_nonneg d0 a2.1]
  · nlinarith [mul_le_mul_of_nonneg_left a1.2 d0]

lemma xsum (M : FracMech n (CoreTask n ℓ)) (hfeas : IsFeasibleOn IsGraphInput M)
    (hel : IsEligible M) {Y : Fin n → CoreTask n ℓ → ℝ} (hY : IsGraphInput Y) (i u0 : Fin n)
    (hne : i ≠ u0) (g : CoreTask n ℓ) (hL : g.isLeft = true) (hi : incident i g)
    (hu : incident u0 g) : M.x Y i g + M.x Y u0 g = 1 := by
  have := (hfeas Y hY).2 g
  rwa [sum_two M hel hY i u0 hne g hL hi hu] at this

lemma pair_up (M : FracMech n (CoreTask n ℓ)) (hfeas : IsFeasibleOn IsGraphInput M)
    (htruth : IsTruthfulOn IsGraphInput M) (hel : IsEligible M) (u v : Fin n) (huv : u ≠ v)
    (g : CoreTask n ℓ) (hL : g.isLeft = true) (hu : incident u g) (hv : incident v g)
    (P Pu Pv : Fin n → CoreTask n ℓ → ℝ) (hP : IsGraphInput P) (hPu : IsGraphInput Pu)
    (hPv : IsGraphInput Pv) (hau : ∀ w h', (w, h') ≠ (u, g) → P w h' = Pu w h')
    (hav : ∀ w h', (w, h') ≠ (v, g) → P w h' = Pv w h') (δ : ℝ) (hδ : 0 < δ)
    (hdu : Pu u g = P u g + δ) (hdv : Pv v g = P v g + δ) :
    (disutility M Pu u - disutility M P u) + (disutility M Pv v - disutility M P v) ≤ δ := by
  have s1 := (sandwich M htruth u P Pu g hP hPu hau).2
  have s2 := (sandwich M htruth v P Pv g hP hPv hav).2
  have hs := xsum M hfeas hel hP u v huv g hL hu hv
  rw [hdu] at s1
  rw [hdv] at s2
  have e1 : (P u g + δ - P u g) = δ := by ring
  have e2 : (P v g + δ - P v g) = δ := by ring
  rw [e1] at s1
  rw [e2] at s2
  nlinarith

lemma pair_down (M : FracMech n (CoreTask n ℓ)) (hfeas : IsFeasibleOn IsGraphInput M)
    (htruth : IsTruthfulOn IsGraphInput M) (hel : IsEligible M) (u v : Fin n) (huv : u ≠ v)
    (g : CoreTask n ℓ) (hL : g.isLeft = true) (hu : incident u g) (hv : incident v g)
    (P Pu Pv : Fin n → CoreTask n ℓ → ℝ) (hP : IsGraphInput P) (hPu : IsGraphInput Pu)
    (hPv : IsGraphInput Pv) (hau : ∀ w h', (w, h') ≠ (u, g) → Pu w h' = P w h')
    (hav : ∀ w h', (w, h') ≠ (v, g) → Pv w h' = P w h') (δ : ℝ) (hδ : 0 < δ)
    (hdu : P u g = Pu u g + δ) (hdv : P v g = Pv v g + δ) :
    δ ≤ (disutility M P u - disutility M Pu u) + (disutility M P v - disutility M Pv v) := by
  have s1 := (sandwich M htruth u Pu P g hPu hP hau).1
  have s2 := (sandwich M htruth v Pv P g hPv hP hav).1
  have hs := xsum M hfeas hel hP u v huv g hL hu hv
  rw [hdu] at s1
  rw [hdv] at s2
  have e1 : (Pu u g + δ - Pu u g) = δ := by ring
  have e2 : (Pv v g + δ - Pv v g) = δ := by ring
  rw [e1] at s1
  rw [e2] at s2
  nlinarith

lemma axis_gen (M : FracMech n (CoreTask n ℓ)) (hfeas : IsFeasibleOn IsGraphInput M)
    (htruth : IsTruthfulOn IsGraphInput M) (u : Fin n) (g : CoreTask n ℓ)
    (Y1 Y2 : ℝ → Fin n → CoreTask n ℓ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hY1 : ∀ θ, 0 ≤ θ → IsGraphInput (Y1 θ)) (hY2 : ∀ θ, 0 ≤ θ → IsGraphInput (Y2 θ))
    (hag1 : ∀ θ θ' w h', (w, h') ≠ (u, g) → Y1 θ w h' = Y1 θ' w h')
    (hag2 : ∀ θ θ' w h', (w, h') ≠ (u, g) → Y2 θ w h' = Y2 θ' w h')
    (hv1 : ∀ θ, Y1 θ u g = θ) (hv2 : ∀ θ, Y2 θ u g = θ)
    (hx : ∀ θ, 0 ≤ θ → M.x (Y1 θ) u g = M.x (Y2 θ) u g) :
    disutility M (Y1 T) u - disutility M (Y1 0) u =
      disutility M (Y2 T) u - disutility M (Y2 0) u := by
  have key : ∀ (Ya Yb : ℝ → Fin n → CoreTask n ℓ → ℝ),
      (∀ θ, 0 ≤ θ → IsGraphInput (Ya θ)) → (∀ θ, 0 ≤ θ → IsGraphInput (Yb θ)) →
      (∀ θ θ' w h', (w, h') ≠ (u, g) → Ya θ w h' = Ya θ' w h') →
      (∀ θ θ' w h', (w, h') ≠ (u, g) → Yb θ w h' = Yb θ' w h') →
      (∀ θ, Ya θ u g = θ) → (∀ θ, Yb θ u g = θ) →
      (∀ θ, 0 ≤ θ → M.x (Ya θ) u g = M.x (Yb θ) u g) →
      disutility M (Ya T) u - disutility M (Ya 0) u ≤
        disutility M (Yb T) u - disutility M (Yb 0) u := by
    intro Ya Yb gA gB aA aB vA vB hxx
    refine riemann T hT (fun θ => disutility M (Ya θ) u) (fun θ => disutility M (Yb θ) u)
      (fun θ => M.x (Ya θ) u g) (fun θ => M.x (Yb θ) u g) ?_ ?_ (fun a ha _ => (hxx a ha).le)
    · intro a b ha hab _
      have := (sandwich M htruth u (Ya a) (Ya b) g (gA a ha) (gA b (ha.trans hab))
        (fun w h' hh => aA a b w h' hh)).2
      simpa [vA] using this
    · intro a b ha hab _
      have := (sandwich M htruth u (Yb a) (Yb b) g (gB a ha) (gB b (ha.trans hab))
        (fun w h' hh => aB a b w h' hh)).1
      simpa [vB] using this
  have k1 := key Y1 Y2 hY1 hY2 hag1 hag2 hv1 hv2 hx
  have k2 := key Y2 Y1 hY2 hY1 hag2 hag1 hv2 hv1 (fun θ h => (hx θ h).symm)
  linarith


/-! ### The slice -/

structure Ctx (M : FracMech n (CoreTask n ℓ)) (z : Fin n → CoreTask n ℓ → ℝ) (i j : Fin n)
    (e f : CoreTask n ℓ) : Prop where
  hℓ : 2 ≤ ℓ
  hfeas : IsFeasibleOn IsGraphInput M
  htruth : IsTruthfulOn IsGraphInput M
  hel : IsEligible M
  hzti : HasZeroTypeIrrelevance M
  hz : IsGraphInput z
  hij : i ≠ j
  hef : e ≠ f
  heL : e.isLeft = true
  hfL : f.isLeft = true
  hie : incident i e
  hif : incident i f
  hje : incident j e
  hjf : incident j f

section Slice
variable {M : FracMech n (CoreTask n ℓ)} {z : Fin n → CoreTask n ℓ → ℝ} {i j : Fin n}
  {e f : CoreTask n ℓ}

lemma psi_congr {t t' s s' : ℝ × ℝ} (v : Fin n) (g : CoreTask n ℓ)
    (h1 : (v = i ∧ g = e) → t.1 = t'.1) (h2 : (v = i ∧ g = f) → t.2 = t'.2)
    (h3 : (v = j ∧ g = e) → s.1 = s'.1) (h4 : (v = j ∧ g = f) → s.2 = s'.2) :
    pairSliceInput z i j e f t s v g = pairSliceInput z i j e f t' s' v g := by
  unfold pairSliceInput
  split_ifs <;> simp_all

lemma psi_ie (t s : ℝ × ℝ) : pairSliceInput z i j e f t s i e = t.1 := by
  simp [pairSliceInput]

lemma psi_if (c : Ctx M z i j e f) (t s : ℝ × ℝ) : pairSliceInput z i j e f t s i f = t.2 := by
  have := c.hef.symm
  simp [pairSliceInput, this]

lemma psi_je (c : Ctx M z i j e f) (t s : ℝ × ℝ) : pairSliceInput z i j e f t s j e = s.1 := by
  have := c.hij.symm
  simp [pairSliceInput, this]

lemma psi_jf (c : Ctx M z i j e f) (t s : ℝ × ℝ) : pairSliceInput z i j e f t s j f = s.2 := by
  have := c.hij.symm
  have := c.hef.symm
  simp [pairSliceInput, *]

lemma psi_gi (c : Ctx M z i j e f) {t s : ℝ × ℝ} (h1 : 0 ≤ t.1) (h2 : 0 ≤ t.2) (h3 : 0 ≤ s.1)
    (h4 : 0 ≤ s.2) : IsGraphInput (pairSliceInput z i j e f t s) := by
  intro u g
  unfold pairSliceInput
  by_cases a1 : u = i ∧ g = e
  · rw [if_pos a1]; obtain ⟨rfl, rfl⟩ := a1; exact ⟨h1, fun h => absurd c.hie h⟩
  rw [if_neg a1]
  by_cases a2 : u = i ∧ g = f
  · rw [if_pos a2]; obtain ⟨rfl, rfl⟩ := a2; exact ⟨h2, fun h => absurd c.hif h⟩
  rw [if_neg a2]
  by_cases a3 : u = j ∧ g = e
  · rw [if_pos a3]; obtain ⟨rfl, rfl⟩ := a3; exact ⟨h3, fun h => absurd c.hje h⟩
  rw [if_neg a3]
  by_cases a4 : u = j ∧ g = f
  · rw [if_pos a4]; obtain ⟨rfl, rfl⟩ := a4; exact ⟨h4, fun h => absurd c.hjf h⟩
  rw [if_neg a4]
  exact c.hz u g

/-- machine `i`'s full disutility -/
noncomputable def W (M : FracMech n (CoreTask n ℓ)) (z : Fin n → CoreTask n ℓ → ℝ) (i j : Fin n)
    (e f : CoreTask n ℓ) (t s : ℝ × ℝ) : ℝ :=
  disutility M (pairSliceInput z i j e f t s) i

noncomputable def Wj (M : FracMech n (CoreTask n ℓ)) (z : Fin n → CoreTask n ℓ → ℝ) (i j : Fin n)
    (e f : CoreTask n ℓ) (t s : ℝ × ℝ) : ℝ :=
  disutility M (pairSliceInput z i j e f t s) j

lemma ag_t1 (a b t2 : ℝ) (s : ℝ × ℝ) : ∀ v h, (v, h) ≠ (i, e) →
    pairSliceInput z i j e f (a, t2) s v h = pairSliceInput z i j e f (b, t2) s v h :=
  fun v h hh => psi_congr v h (fun hv => (hh (by rw [hv.1, hv.2])).elim) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl)

lemma ag_t2 (a b t1 : ℝ) (s : ℝ × ℝ) : ∀ v h, (v, h) ≠ (i, f) →
    pairSliceInput z i j e f (t1, a) s v h = pairSliceInput z i j e f (t1, b) s v h :=
  fun v h hh => psi_congr v h (fun _ => rfl) (fun hv => (hh (by rw [hv.1, hv.2])).elim)
    (fun _ => rfl) (fun _ => rfl)

lemma ag_s1 (t : ℝ × ℝ) (a b s2 : ℝ) : ∀ v h, (v, h) ≠ (j, e) →
    pairSliceInput z i j e f t (a, s2) v h = pairSliceInput z i j e f t (b, s2) v h :=
  fun v h hh => psi_congr v h (fun _ => rfl) (fun _ => rfl)
    (fun hv => (hh (by rw [hv.1, hv.2])).elim) (fun _ => rfl)

lemma ag_s2 (t : ℝ × ℝ) (a b s1 : ℝ) : ∀ v h, (v, h) ≠ (j, f) →
    pairSliceInput z i j e f t (s1, a) v h = pairSliceInput z i j e f t (s1, b) v h :=
  fun v h hh => psi_congr v h (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun hv => (hh (by rw [hv.1, hv.2])).elim)

end Slice


section Inst
variable {M : FracMech n (CoreTask n ℓ)} {z : Fin n → CoreTask n ℓ → ℝ} {i j : Fin n}
  {e f : CoreTask n ℓ}

theorem sepdata (c : Ctx M z i j e f) : SepData (W M z i j e f) (Wj M z i j e f) := by
  have hji : j ≠ i := c.hij.symm
  have hfe : f ≠ e := c.hef.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- mono1
    intro a b t2 s ha hab ht2 hs1 hs2
    have := d_bounds M c.hfeas c.htruth i e _ _ (psi_gi c ha ht2 hs1 hs2)
      (psi_gi c (ha.trans hab) ht2 hs1 hs2) (ag_t1 a b t2 s) (by rw [psi_ie, psi_ie]; exact hab)
    rw [psi_ie, psi_ie] at this
    exact this
  · -- mono2
    intro a b t1 s ha hab ht1 hs1 hs2
    have := d_bounds M c.hfeas c.htruth i f _ _ (psi_gi c ht1 ha hs1 hs2)
      (psi_gi c ht1 (ha.trans hab) hs1 hs2) (ag_t2 a b t1 s)
      (by rw [psi_if c, psi_if c]; exact hab)
    rw [psi_if c, psi_if c] at this
    exact this
  · -- monoj1
    intro a b s2 t ha hab hs2 ht1 ht2
    have := d_bounds M c.hfeas c.htruth j e _ _ (psi_gi c ht1 ht2 ha hs2)
      (psi_gi c ht1 ht2 (ha.trans hab) hs2) (ag_s1 t a b s2)
      (by rw [psi_je c, psi_je c]; exact hab)
    rw [psi_je c, psi_je c] at this
    exact this
  · -- monoj2
    intro a b s1 t ha hab hs1 ht1 ht2
    have := d_bounds M c.hfeas c.htruth j f _ _ (psi_gi c ht1 ht2 hs1 ha)
      (psi_gi c ht1 ht2 hs1 (ha.trans hab)) (ag_s2 t a b s1)
      (by rw [psi_jf c, psi_jf c]; exact hab)
    rw [psi_jf c, psi_jf c] at this
    exact this
  · -- mono_s
    intro t s s' ht1 ht2 hs1 hs2 h1 h2
    refine lemma_4 c.hℓ M c.hfeas c.htruth c.hel c.hzti i _ _ (psi_gi c ht1 ht2 hs1 hs2)
      (psi_gi c ht1 ht2 (hs1.trans h1) (hs2.trans h2)) ?_ ?_
    · intro u g hug
      refine psi_congr u g (fun _ => rfl) (fun _ => rfl) ?_ ?_
      · rintro ⟨hu, hg⟩
        rcases hug with h | h
        · exact absurd (hu.symm.trans h) c.hij.symm
        · exact (h ⟨hg ▸ c.heL, hg ▸ c.hie⟩).elim
      · rintro ⟨hu, hg⟩
        rcases hug with h | h
        · exact absurd (hu.symm.trans h) c.hij.symm
        · exact (h ⟨hg ▸ c.hfL, hg ▸ c.hif⟩).elim
    · intro u g
      unfold pairSliceInput
      split_ifs <;> first | exact le_refl _ | assumption
  · -- mono_tj
    intro t t' s ht1 ht2 hs1 hs2 h1 h2
    refine lemma_4 c.hℓ M c.hfeas c.htruth c.hel c.hzti j _ _ (psi_gi c ht1 ht2 hs1 hs2)
      (psi_gi c (ht1.trans h1) (ht2.trans h2) hs1 hs2) ?_ ?_
    · intro u g hug
      refine psi_congr u g ?_ ?_ (fun _ => rfl) (fun _ => rfl)
      · rintro ⟨hu, hg⟩
        rcases hug with h | h
        · exact absurd (hu.symm.trans h) c.hij
        · exact (h ⟨hg ▸ c.heL, hg ▸ c.hje⟩).elim
      · rintro ⟨hu, hg⟩
        rcases hug with h | h
        · exact absurd (hu.symm.trans h) c.hij
        · exact (h ⟨hg ▸ c.hfL, hg ▸ c.hjf⟩).elim
    · intro u g
      unfold pairSliceInput
      split_ifs <;> first | exact le_refl _ | assumption
  · -- pairF1
    rintro ⟨t1, t2⟩ ⟨s1, s2⟩ δ h1 h2 h3 h4 hδ
    dsimp only at *
    exact pair_up M c.hfeas c.htruth c.hel i j c.hij e c.heL c.hie c.hje _ _ _
      (psi_gi c h1 h2 h3 h4) (psi_gi c (by linarith) h2 h3 h4) (psi_gi c h1 h2 (by linarith) h4)
      (ag_t1 t1 (t1 + δ) t2 (s1, s2)) (ag_s1 (t1, t2) s1 (s1 + δ) s2) δ hδ
      (by rw [psi_ie, psi_ie]) (by rw [psi_je c, psi_je c])
  · -- pairF2
    rintro ⟨t1, t2⟩ ⟨s1, s2⟩ δ h1 h2 h3 h4 hδ
    dsimp only at *
    exact pair_up M c.hfeas c.htruth c.hel i j c.hij f c.hfL c.hif c.hjf _ _ _
      (psi_gi c h1 h2 h3 h4) (psi_gi c h1 (by linarith) h3 h4) (psi_gi c h1 h2 h3 (by linarith))
      (ag_t2 t2 (t2 + δ) t1 (s1, s2)) (ag_s2 (t1, t2) s2 (s2 + δ) s1) δ hδ
      (by rw [psi_if c, psi_if c]) (by rw [psi_jf c, psi_jf c])
  · -- pairB1
    rintro ⟨t1, t2⟩ ⟨s1, s2⟩ δ h2 h4 hδ h5 h6
    dsimp only at *
    exact pair_down M c.hfeas c.htruth c.hel i j c.hij e c.heL c.hie c.hje _ _ _
      (psi_gi c (by linarith) h2 (by linarith) h4) (psi_gi c (by linarith) h2 (by linarith) h4)
      (psi_gi c (by linarith) h2 (by linarith) h4)
      (ag_t1 (t1 - δ) t1 t2 (s1, s2)) (ag_s1 (t1, t2) (s1 - δ) s1 s2) δ hδ
      (by rw [psi_ie, psi_ie]; ring) (by rw [psi_je c, psi_je c]; ring)
  · -- pairB2
    rintro ⟨t1, t2⟩ ⟨s1, s2⟩ δ h1 h3 hδ h5 h6
    dsimp only at *
    exact pair_down M c.hfeas c.htruth c.hel i j c.hij f c.hfL c.hif c.hjf _ _ _
      (psi_gi c h1 (by linarith) h3 (by linarith)) (psi_gi c h1 (by linarith) h3 (by linarith))
      (psi_gi c h1 (by linarith) h3 (by linarith))
      (ag_t2 (t2 - δ) t2 t1 (s1, s2)) (ag_s2 (t1, t2) (s2 - δ) s2 s1) δ hδ
      (by rw [psi_if c, psi_if c]; ring) (by rw [psi_jf c, psi_jf c]; ring)
  · -- ax1
    intro t1 s ht1 hs1 hs2
    exact axis_gen M c.hfeas c.htruth i e (fun θ => pairSliceInput z i j e f (θ, 0) s)
      (fun θ => pairSliceInput z i j e f (θ, 0) (s.1, 0)) t1 ht1
      (fun θ hθ => psi_gi c hθ le_rfl hs1 hs2) (fun θ hθ => psi_gi c hθ le_rfl hs1 le_rfl)
      (fun θ θ' w h' hh => ag_t1 θ θ' 0 s w h' hh) (fun θ θ' w h' hh => ag_t1 θ θ' 0 _ w h' hh)
      (fun θ => psi_ie _ _) (fun θ => psi_ie _ _) (fun θ hθ => by
        refine zti_x (X := pairSliceInput z i j e f (θ, 0) s)
          (X2 := pairSliceInput z i j e f (θ, 0) (s.1, 0)) M c.hzti (psi_gi c hθ le_rfl hs1 hs2) (psi_gi c hθ le_rfl hs1 le_rfl) f
          c.hfL i c.hif (by rw [psi_if c]) (by rw [psi_if c]) ?_ i e c.hef
        intro v g hg
        exact psi_congr v g (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun hv => (hg hv.2).elim))
  · -- ax2
    intro t2 s ht2 hs1 hs2
    exact axis_gen M c.hfeas c.htruth i f (fun θ => pairSliceInput z i j e f (0, θ) s)
      (fun θ => pairSliceInput z i j e f (0, θ) (0, s.2)) t2 ht2
      (fun θ hθ => psi_gi c le_rfl hθ hs1 hs2) (fun θ hθ => psi_gi c le_rfl hθ le_rfl hs2)
      (fun θ θ' w h' hh => ag_t2 θ θ' 0 s w h' hh) (fun θ θ' w h' hh => ag_t2 θ θ' 0 _ w h' hh)
      (fun θ => psi_if c _ _) (fun θ => psi_if c _ _) (fun θ hθ => by
        refine zti_x (X := pairSliceInput z i j e f (0, θ) s)
          (X2 := pairSliceInput z i j e f (0, θ) (0, s.2)) M c.hzti (psi_gi c le_rfl hθ hs1 hs2) (psi_gi c le_rfl hθ le_rfl hs2) e
          c.heL i c.hie (by rw [psi_ie]) (by rw [psi_ie]) ?_ i f c.hef.symm
        intro v g hg
        exact psi_congr v g (fun _ => rfl) (fun _ => rfl) (fun hv => (hg hv.2).elim)
          (fun _ => rfl))
  · -- ax3
    rintro ⟨t1, t2⟩ s1 h1 h2 hs1
    dsimp only at *
    exact axis_gen M c.hfeas c.htruth j e (fun θ => pairSliceInput z i j e f (t1, t2) (θ, 0))
      (fun θ => pairSliceInput z i j e f (t1, 0) (θ, 0)) s1 hs1
      (fun θ hθ => psi_gi c h1 h2 hθ le_rfl) (fun θ hθ => psi_gi c h1 le_rfl hθ le_rfl)
      (fun θ θ' w h' hh => ag_s1 _ θ θ' 0 w h' hh) (fun θ θ' w h' hh => ag_s1 _ θ θ' 0 w h' hh)
      (fun θ => psi_je c _ _) (fun θ => psi_je c _ _) (fun θ hθ => by
        refine zti_x (X := pairSliceInput z i j e f (t1, t2) (θ, 0))
          (X2 := pairSliceInput z i j e f (t1, 0) (θ, 0)) M c.hzti (psi_gi c h1 h2 hθ le_rfl) (psi_gi c h1 le_rfl hθ le_rfl) f
          c.hfL j c.hjf (by rw [psi_jf c]) (by rw [psi_jf c]) ?_ j e c.hef
        intro v g hg
        exact psi_congr v g (fun _ => rfl) (fun hv => (hg hv.2).elim) (fun _ => rfl)
          (fun _ => rfl))
  · -- ax4
    rintro ⟨t1, t2⟩ s2 h1 h2 hs2
    dsimp only at *
    exact axis_gen M c.hfeas c.htruth j f (fun θ => pairSliceInput z i j e f (t1, t2) (0, θ))
      (fun θ => pairSliceInput z i j e f (0, t2) (0, θ)) s2 hs2
      (fun θ hθ => psi_gi c h1 h2 le_rfl hθ) (fun θ hθ => psi_gi c le_rfl h2 le_rfl hθ)
      (fun θ θ' w h' hh => ag_s2 _ θ θ' 0 w h' hh) (fun θ θ' w h' hh => ag_s2 _ θ θ' 0 w h' hh)
      (fun θ => psi_jf c _ _) (fun θ => psi_jf c _ _) (fun θ hθ => by
        refine zti_x (X := pairSliceInput z i j e f (t1, t2) (0, θ))
          (X2 := pairSliceInput z i j e f (0, t2) (0, θ)) M c.hzti (psi_gi c h1 h2 le_rfl hθ) (psi_gi c le_rfl h2 le_rfl hθ) e
          c.heL j c.hje (by rw [psi_je c]) (by rw [psi_je c]) ?_ j f c.hef.symm
        intro v g hg
        exact psi_congr v g (fun hv => (hg hv.2).elim) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl))

end Inst

end FracTruthSched.Dev.L2b

namespace FracTruthSched

open MeasureTheory

theorem chk_lemma_2b {n ℓ : ℕ} (hℓ : 2 ≤ ℓ) (M : FracMech n (CoreTask n ℓ))
    (hfeas : IsFeasibleOn IsGraphInput M) (htruth : IsTruthfulOn IsGraphInput M)
    (hel : IsEligible M) (hzti : HasZeroTypeIrrelevance M)
    (p : {p : Fin n × Fin n // p.1 < p.2}) (k₁ k₂ : Fin ℓ) (hk : k₁ ≠ k₂) (i j : Fin n)
    (hij : (i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1))
    (z : Fin n → CoreTask n ℓ → ℝ) (hz : IsGraphInput z) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))), ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → 0 ≤ t₂ →
      pairSliceDisutility M z i j (.inl (p, k₁)) (.inl (p, k₂)) (t₁, t₂) s =
        pairSliceDisutility M z i j (.inl (p, k₁)) (.inl (p, k₂)) (t₁, 0) s +
          pairSliceDisutility M z i j (.inl (p, k₁)) (.inl (p, k₂)) (0, t₂) s := by
  have hp := p.2
  have hne : i ≠ j := by
    rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hp.ne
    · rw [h1, h2]; exact hp.ne'
  have c : Dev.L2b.Ctx M z i j (.inl (p, k₁)) (.inl (p, k₂)) :=
    ⟨hℓ, hfeas, htruth, hel, hzti, hz, hne, by simpa using hk, rfl, rfl,
      by rcases hij with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [incident, h1],
      by rcases hij with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [incident, h1],
      by rcases hij with ⟨_, h1⟩ | ⟨_, h1⟩ <;> simp [incident, h1],
      by rcases hij with ⟨_, h1⟩ | ⟨_, h1⟩ <;> simp [incident, h1]⟩
  filter_upwards [Dev.L2b.separation _ _ (Dev.L2b.sepdata c)] with s hs t₁ t₂ h1 h2
  have := hs t₁ t₂ h1 h2
  simp only [Dev.L2b.W] at this
  simp only [pairSliceDisutility, Prod.mk_zero_zero] at this ⊢
  linarith

end FracTruthSched
end

theorem solution : type_of% @FracTruthSched.chk_lemma_2b := @FracTruthSched.chk_lemma_2b
