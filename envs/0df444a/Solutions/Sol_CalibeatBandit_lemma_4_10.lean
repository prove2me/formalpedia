-- Prove2me | solution 1 for CalibeatBandit.lemma_4_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:47:32.462542+00:00
-- url     : https://prove2.me/submissions/aea30319-2033-4c2a-af2e-90169e22ad28

import Mathlib
import Definitions.Def_CalibeatBandit_lower_bound_models
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_hard_tree_environment
import Definitions.Def_CalibeatBandit_hard_tree_analysis

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

theorem integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hm : Measurable f) {B : ℝ}
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  (integrable_const B).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb ω)

theorem integral_exp_sum_le_one {T : ℕ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (info preDraw : ℕ → MeasurableSpace Ω)
    (hinfo : ∀ a b, a ≤ b → b ≤ T → info a ≤ info b)
    (hinfo_le : ∀ n ≤ T, info n ≤ mΩ)
    (hpre : ∀ n < T, preDraw n ≤ mΩ)
    (hprev : ∀ n < T, info n ≤ preDraw n)
    (d : ℕ → Ω → ℝ) {B : ℝ}
    (hm : ∀ t < T, Measurable[info (t + 1)] (d t))
    (hb : ∀ t < T, ∀ ω, |d t ω| ≤ B)
    (hc : ∀ t < T, condExp (preDraw t) P (fun ω => Real.exp (d t ω)) ≤ᵐ[P] fun _ => 1) :
    ∫ ω, Real.exp (∑ t ∈ Finset.range T, d t ω) ∂P ≤ 1 := by
  let F (n : ℕ) (ω : Ω) := Real.exp (∑ t ∈ Finset.range n, d t ω)
  have hF (n : ℕ) (hn : n ≤ T) : Measurable[info n] (F n) := by
    refine Real.continuous_exp.measurable.comp (Finset.measurable_sum _ fun t ht => ?_)
    have hs := Nat.succ_le_of_lt (Finset.mem_range.mp ht)
    exact (hm t (lt_of_lt_of_le (Finset.mem_range.mp ht) hn)).mono
      (hinfo _ _ hs hn) le_rfl
  have hi (n : ℕ) (hn : n ≤ T) : Integrable (F n) P := by
    apply integrable_of_abs_bound ((hF n hn).mono (hinfo_le n hn) le_rfl)
    intro ω
    rw [show F n ω = Real.exp (∑ t ∈ Finset.range n, d t ω) from rfl,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ∑ _ ∈ Finset.range n, B := Finset.sum_le_sum fun t ht =>
        (le_abs_self _).trans (hb t ((Finset.mem_range.mp ht).trans_le hn) ω)
      _ = (n : ℝ) * B := by simp
  have step (n : ℕ) (hn : n < T) : (∫ ω, F (n + 1) ω ∂P) ≤ ∫ ω, F n ω ∂P := by
    let G : Ω → ℝ := fun ω => Real.exp (d n ω)
    have hG : Integrable G P := by
      refine integrable_of_abs_bound (B := Real.exp B) (Real.continuous_exp.measurable.comp
        ((hm n hn).mono (hinfo_le _ (Nat.succ_le_of_lt hn)) le_rfl)) ?_
      intro ω
      change |Real.exp (d n ω)| ≤ Real.exp B
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb n hn ω))
    have heq : F (n + 1) = F n * G := by
      funext ω
      simp [F, G, Finset.sum_range_succ, Real.exp_add]
    have hprod : Integrable (F n * G) P := heq ▸ hi (n + 1) (Nat.succ_le_of_lt hn)
    have hpull := condExp_mul_of_stronglyMeasurable_left
      ((hF n hn.le).mono (hprev n hn) le_rfl).stronglyMeasurable
      hprod hG
    rw [heq, ← integral_condExp (m := preDraw n) (hpre n hn)]
    apply integral_mono_ae integrable_condExp (hi n hn.le)
    filter_upwards [hpull, hc n hn] with ω hw hcω
    rw [hw]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) hcω
  have hbound (n : ℕ) (hn : n ≤ T) : (∫ ω, F n ω ∂P) ≤ 1 := by
    induction n with
    | zero => simp [F]
    | succ n ih =>
      have hh : n < T := Nat.lt_of_succ_le hn
      exact (step n hh).trans (ih hh.le)
  exact hbound T le_rfl

theorem integrable_finset_max {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsFiniteMeasure P] (hne : (Finset.univ : Finset ι).Nonempty)
    (F : ι → Ω → ℝ) {B : ℝ} (hm : ∀ i, Measurable (F i)) (hb : ∀ i ω, |F i ω| ≤ B) :
    Integrable (fun ω => Finset.univ.sup' hne (fun i => F i ω)) P := by
  let _ : Nonempty ι := hne.to_subtype.map Subtype.val
  apply integrable_of_abs_bound
  · simp_rw [Finset.sup'_univ_eq_ciSup]
    exact Measurable.iSup hm
  · intro ω
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun i => F i ω)
    exact hi.symm ▸ hb i ω

/-- A finite maximum is bounded in expectation by the logarithm of the number
of competitors whenever each competitor has an exponential moment at most one. -/
theorem integral_max_le_log_card {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (hne : (Finset.univ : Finset ι).Nonempty)
    (F : ι → Ω → ℝ) {η B : ℝ} (hη : 0 < η)
    (hm : ∀ i, Measurable (F i)) (hb : ∀ i ω, |F i ω| ≤ B)
    (he : ∀ i, ∫ ω, Real.exp (η * F i ω) ∂P ≤ 1) :
    ∫ ω, Finset.univ.sup' hne (fun i => F i ω) ∂P ≤ Real.log (Fintype.card ι) / η := by
  classical
  let M (ω : Ω) := Finset.univ.sup' hne (fun i => F i ω)
  let Z (ω : Ω) := ∑ i, Real.exp (η * F i ω)
  let N : ℝ := Fintype.card ι
  let H (ω : Ω) := Real.log N + (Z ω / N - 1)
  let _ : Nonempty ι := hne.to_subtype.map Subtype.val
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := ι)
  have hM : Integrable M P := integrable_finset_max hne F hm hb
  have hei (i : ι) : Integrable (fun ω => Real.exp (η * F i ω)) P := by
    refine integrable_of_abs_bound (B := Real.exp (η * B))
      (Real.continuous_exp.measurable.comp ((hm i).const_mul η)) ?_
    intro ω
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb i ω)) hη.le)
  have hZ : Integrable Z P := integrable_finsetSum _ fun i _ => hei i
  have hZi : (∫ ω, Z ω ∂P) ≤ N := by
    rw [show (∫ ω, Z ω ∂P) = ∑ i, ∫ ω, Real.exp (η * F i ω) ∂P from
      integral_finsetSum _ (fun i _ => hei i)]
    calc
      _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => he i
      _ = N := by simp [N]
  have hH : Integrable H P := (integrable_const _).add ((hZ.div_const N).sub (integrable_const _))
  have hpoint (ω : Ω) : η * M ω ≤ H ω := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun i => F i ω)
    have hle : Real.exp (η * M ω) ≤ Z ω := by
      change Real.exp (η * Finset.univ.sup' hne (fun i => F i ω)) ≤ Z ω
      rw [hi]
      exact Finset.single_le_sum (fun j _ => Real.exp_nonneg (η * F j ω)) (Finset.mem_univ i)
    have hz : 0 < Z ω := (Real.exp_pos _).trans_le hle
    have hl := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp] at hl
    have hh := Real.log_le_sub_one_of_pos (div_pos hz hN)
    rw [Real.log_div hz.ne' hN.ne'] at hh
    dsimp [H]
    linarith only [hl, hh]
  have hHi : (∫ ω, H ω ∂P) ≤ Real.log N := by
    let W : Ω → ℝ := fun ω => Z ω / N
    change (∫ ω, Real.log N + (W ω - 1) ∂P) ≤ _
    have hW : Integrable W P := hZ.div_const N
    have hdiff : Integrable (fun ω => W ω - 1) P := hW.sub (integrable_const _)
    rw [integral_add (integrable_const _) hdiff, integral_sub hW (integrable_const _)]
    dsimp only [W]
    rw [integral_div]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    linarith only [(div_le_one hN).mpr hZi]
  have hi := (integral_mono (hM.const_mul η) hH hpoint).trans hHi
  have heq : (∫ ω, η * M ω ∂P) = η * ∫ ω, M ω ∂P := integral_const_mul η M
  rw [heq] at hi
  exact (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using hi)

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

private theorem condExp_exp_centered_le_one {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable[mΩ] X) (hb : ∀ ω, |X ω| ≤ 1)
    (hc : condExp m P X =ᵐ[P] 0) (s : ℝ) :
    condExp m P (fun ω => Real.exp (s * X ω - s ^ 2 / 2)) ≤ᵐ[P] fun _ => 1 := by
  let k := Real.exp (-(s ^ 2 / 2))
  let A := k * Real.cosh s
  let B := k * Real.sinh s
  have hi : Integrable X P := @integrable_of_abs_bound Ω mΩ P _ X hX 1 hb
  have he : Integrable (fun ω => Real.exp (s * X ω - s ^ 2 / 2)) P := by
    refine @integrable_of_abs_bound Ω mΩ P _ _ (Real.continuous_exp.measurable.comp
      ((hX.const_mul s).sub measurable_const)) (Real.exp |s|) fun ω => ?_
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ s * X ω := sub_le_self _ (by positivity)
      _ ≤ |s * X ω| := le_abs_self _
      _ ≤ |s| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hb ω)
  have heq (ω : Ω) : Real.exp (s * X ω - s ^ 2 / 2) ≤ A + B * X ω := by
    rw [sub_eq_add_neg, Real.exp_add, mul_comm (Real.exp _)]
    have h := mul_le_mul_of_nonneg_left (Real.exp_mul_le_cosh_add_mul_sinh (hb ω) s)
      (Real.exp_nonneg (-(s ^ 2 / 2)))
    have hleft : Real.exp (-(s ^ 2 / 2)) * Real.exp (s * X ω) =
        Real.exp (-(s ^ 2 / 2)) * Real.exp (X ω * s) := by rw [mul_comm s]
    rw [hleft]
    exact h.trans_eq (by unfold A B k; ring)
  have hA : Integrable (fun _ : Ω => A) P := integrable_const _
  have hB : Integrable (fun ω => B * X ω) P := hi.const_mul B
  have hcond := condExp_mono (m := m) he (hA.add hB) (ae_of_all _ heq)
  have hbPull : condExp m P (fun ω => B * X ω) =ᵐ[P] fun ω => B * condExp m P X ω :=
    condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_const hB hi
  have hconst : A ≤ 1 := by
    calc
      A ≤ k * Real.exp (s ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq s) (Real.exp_nonneg _)
      _ = 1 := by unfold k; rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  filter_upwards [hcond, condExp_add hA hB m, hbPull, hc] with ω h₁ h₂ h₃ h₄
  apply h₁.trans
  rw [h₂]
  change condExp m P (fun _ : Ω => A) ω + condExp m P (fun ω => B * X ω) ω ≤ 1
  simpa only [condExp_const hm, h₃, h₄, Pi.zero_apply, mul_zero, add_zero] using hconst

/-- Lemma 4.10 for increments bounded by one. The two signs of each
martingale index the competitors in the exponential maximum. -/
theorem martingale_max_abs_le {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (info : Filtration ℕ mΩ) {T : ℕ} (hT : 0 < T) (d : ℕ → ι → Ω → ℝ)
    (hm : ∀ t < T, ∀ j, Measurable[info (t + 1)] (d t j))
    (hb : ∀ t < T, ∀ j ω, |d t j ω| ≤ 1)
    (hc : ∀ t < T, ∀ j, condExp (info t) P (d t j) =ᵐ[P] 0) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty
      (fun j => |∑ t ∈ Finset.range T, d t j ω|) ∂P) ≤
      Real.sqrt (2 * T * Real.log (2 * Fintype.card ι)) := by
  classical
  let L := Real.log (2 * Fintype.card ι)
  have hL : 0 < L := by
    apply Real.log_pos
    have h : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
    linarith
  have ht : 0 < (T : ℝ) := by exact_mod_cast hT
  let R := Real.sqrt (2 * T * L)
  have hrad : 0 < 2 * T * L := by positivity
  have hR : 0 < R := Real.sqrt_pos.mpr hrad
  let s := R / T
  have hs : 0 < s := div_pos hR ht
  let X (t : ℕ) (j : ι × Bool) : Ω → ℝ := if j.2 then d t j.1 else -d t j.1
  have hXm (t : ℕ) (ht : t < T) (j : ι × Bool) : Measurable[info (t + 1)] (X t j) := by
    unfold X
    split
    · exact hm t ht j.1
    · exact (hm t ht j.1).neg
  have hXb (t : ℕ) (ht : t < T) (j : ι × Bool) (ω : Ω) : |X t j ω| ≤ 1 := by
    unfold X
    split <;> simpa using hb t ht j.1 ω
  have hXc (t : ℕ) (ht : t < T) (j : ι × Bool) : condExp (info t) P (X t j) =ᵐ[P] 0 := by
    unfold X
    split
    · exact hc t ht j.1
    · filter_upwards [condExp_neg (μ := P) (m := info t) (f := d t j.1), hc t ht j.1] with ω h he
      simp [h, he]
  let F (j : ι × Bool) (ω : Ω) := ∑ t ∈ Finset.range T, (X t j ω - s / 2)
  have hfm (j : ι × Bool) : Measurable (F j) :=
    Finset.measurable_sum _ fun t ht =>
      ((hXm t (Finset.mem_range.mp ht) j).mono (info.le _) le_rfl).sub measurable_const
  have hfb (j : ι × Bool) (ω : Ω) : |F j ω| ≤ T * (1 + |s / 2|) := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, |X t j ω - s / 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range T, (1 + |s / 2|) := Finset.sum_le_sum fun t ht =>
        (abs_sub _ _).trans (add_le_add_left (hXb t (Finset.mem_range.mp ht) j ω) _)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hExp (j : ι × Bool) : (∫ ω, Real.exp (s * F j ω) ∂P) ≤ 1 := by
    have h := integral_exp_sum_le_one P info info
      (fun _ _ h _ => info.mono h) (fun n _ => info.le n) (fun n _ => info.le n) (fun _ _ => le_rfl)
      (fun t ω => s * X t j ω - s ^ 2 / 2)
      (B := |s| + |s ^ 2 / 2|)
      (fun t ht => ((hXm t ht j).const_mul s).sub measurable_const)
      (fun t ht ω => (abs_sub _ _).trans (by
        rw [abs_mul]
        exact add_le_add_left (mul_le_of_le_one_right (abs_nonneg _) (hXb t ht j ω)) _))
      (fun t ht => condExp_exp_centered_le_one (info.le t)
        ((hXm t ht j).mono (info.le _) le_rfl) (hXb t ht j) (hXc t ht j) s)
    have heq (ω : Ω) : s * F j ω =
        ∑ t ∈ Finset.range T, (s * X t j ω - s ^ 2 / 2) := by
      simp only [F, Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    simpa only [heq] using h
  have hF := integral_max_le_log_card P Finset.univ_nonempty F hs hfm hfb hExp
  let M (ω : Ω) := Finset.univ.sup' Finset.univ_nonempty
      (fun j : ι => |∑ t ∈ Finset.range T, d t j ω|)
  have hiM : Integrable M P := by
    apply integrable_finset_max Finset.univ_nonempty (B := T)
    · intro j
      have hmeas : Measurable (fun ω => ∑ t ∈ Finset.range T, d t j ω) :=
        Finset.measurable_sum _ fun t ht => (hm t (Finset.mem_range.mp ht) j).mono (info.le _) le_rfl
      exact continuous_abs.measurable.comp hmeas
    · intro j ω
      rw [abs_abs]
      calc
        _ ≤ ∑ t ∈ Finset.range T, |d t j ω| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) :=
          Finset.sum_le_sum fun t ht => hb t (Finset.mem_range.mp ht) j ω
        _ = _ := by simp
  have hf (ω : Ω) (j : ι) (b : Bool) :
      F (j, b) ω = (if b then ∑ t ∈ Finset.range T, d t j ω
      else -(∑ t ∈ Finset.range T, d t j ω)) - T * (s / 2) := by
    cases b <;> simp [F, X, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hM (ω : Ω) : Finset.univ.sup' Finset.univ_nonempty (fun j => F j ω) = M ω - T * (s / 2) := by
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun ⟨j, b⟩ _ => ?_
      rw [hf]
      apply sub_le_sub_right
      refine le_trans ?_ (Finset.le_sup' (fun j => |∑ t ∈ Finset.range T, d t j ω|) (Finset.mem_univ j))
      cases b <;> simp [le_abs_self, neg_le_abs]
    · obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j : ι => |∑ t ∈ Finset.range T, d t j ω|)
      change M ω = _ at hj
      rw [hj]
      let z := ∑ t ∈ Finset.range T, d t j ω
      change |z| - _ ≤ _
      by_cases hz : 0 ≤ z
      · rw [abs_of_nonneg hz, ← show F (j, true) ω = z - T * (s / 2) by simpa only [if_true] using hf ω j true]
        exact Finset.le_sup' (fun j => F j ω) (Finset.mem_univ (j, true))
      · rw [abs_of_neg (lt_of_not_ge hz), ← show F (j, false) ω = -z - T * (s / 2) by
            simpa only [Bool.false_eq_true, if_false] using hf ω j false]
        exact Finset.le_sup' (fun j => F j ω) (Finset.mem_univ (j, false))
  simp_rw [hM, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat, mul_comm _ (2 : ℝ)] at hF
  rw [integral_sub hiM (integrable_const (T * (s / 2)))] at hF
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hF
  change (∫ ω, M ω ∂P) - T * (s / 2) ≤ L / s at hF
  have hRsq : R ^ 2 = 2 * T * L := Real.sq_sqrt hrad.le
  have hhalf : L / s = R / 2 := by
    apply (div_eq_iff hs.ne').mpr
    dsimp [s]
    field_simp [ht.ne']
    nlinarith only [hRsq]
  have hother : (T : ℝ) * (s / 2) = R / 2 := by
    dsimp [s]
    field_simp [ht.ne']
  rw [hhalf, hother] at hF
  change (∫ ω, M ω ∂P) ≤ R
  linarith only [hF]

/-- Lemma 4.10 with an arbitrary positive bound on the increments. -/
theorem lemma_4_10 {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (info : Filtration ℕ mΩ) {T : ℕ} {c : ℝ} (hc : 0 < c)
    (d : ℕ → ι → Ω → ℝ)
    (hm : ∀ t < T, ∀ j, Measurable[info (t + 1)] (d t j))
    (hb : ∀ t < T, ∀ j ω, |d t j ω| ≤ c)
    (hcenter : ∀ t < T, ∀ j, condExp (info t) P (d t j) =ᵐ[P] 0) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty
      (fun j => |∑ t ∈ Finset.range T, d t j ω|) ∂P) ≤
      c * Real.sqrt (2 * T * Real.log (2 * Fintype.card ι)) := by
  by_cases hT : T = 0
  · subst T
    simp
  let X (t : ℕ) (j : ι) (ω : Ω) := d t j ω / c
  have hXm (t : ℕ) (ht : t < T) (j : ι) : Measurable[info (t + 1)] (X t j) :=
    (hm t ht j).div_const c
  have hXb (t : ℕ) (ht : t < T) (j : ι) (ω : Ω) : |X t j ω| ≤ 1 := by
    change |d t j ω / c| ≤ 1
    rw [abs_div, abs_of_pos hc]
    exact (div_le_one hc).mpr (hb t ht j ω)
  have hXc (t : ℕ) (ht : t < T) (j : ι) : condExp (info t) P (X t j) =ᵐ[P] 0 := by
    have hi : Integrable (d t j) P :=
      integrable_of_abs_bound ((hm t ht j).mono (info.le _) le_rfl) (hb t ht j)
    have hprod : Integrable ((fun _ : Ω => c⁻¹) * d t j) P := hi.const_mul _
    have heq : X t j = (fun _ : Ω => c⁻¹) * d t j := by
      funext ω
      simp only [X, Pi.mul_apply, div_eq_inv_mul]
    rw [heq]
    have hmconst : StronglyMeasurable[info t] (fun _ : Ω => c⁻¹) := stronglyMeasurable_const
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hmconst hprod hi,
      hcenter t ht j] with ω h₁ h₂
    simp [h₁, h₂]
  have h := martingale_max_abs_le P info (Nat.pos_of_ne_zero hT) X hXm hXb hXc
  have hscale (ω : Ω) :
      Finset.univ.sup' Finset.univ_nonempty (fun j => |∑ t ∈ Finset.range T, d t j ω|) =
        c * Finset.univ.sup' Finset.univ_nonempty (fun j => |∑ t ∈ Finset.range T, X t j ω|) := by
    let F (j : ι) := |∑ t ∈ Finset.range T, X t j ω|
    have hj (j : ι) : |∑ t ∈ Finset.range T, d t j ω| = c * F j := by
      unfold F X
      rw [← Finset.sum_div, abs_div, abs_of_pos hc]
      field_simp
    simp_rw [hj]
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun j hj => ?_
      exact mul_le_mul_of_nonneg_left (Finset.le_sup' F hj) hc.le
    · obtain ⟨j, hj, heq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty F
      rw [heq]
      exact Finset.le_sup' (fun j => c * F j) hj
  simp_rw [hscale]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left h hc.le

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.lemma_4_10 := @CalibeatBandit.lemma_4_10
