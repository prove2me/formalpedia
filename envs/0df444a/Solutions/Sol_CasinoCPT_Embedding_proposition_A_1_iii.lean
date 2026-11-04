-- Prove2me | solution 1 for CasinoCPT.Embedding.proposition_A_1_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T07:04:39.817949+00:00
-- url     : https://prove2.me/submissions/d120288c-def0-4d57-8aed-1fd533958824

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

open MeasureTheory ProbabilityTheory CasinoCPT.Embedding

namespace Casino31Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma sv_of_le (S : ℕ → Ω → ℤ) (τ : Ω → ℕ∞) (n : ℕ) (ω : Ω) (h : (n : ℕ∞) ≤ τ ω) :
    stoppedValue S (fun ω => min (τ ω) (n : ℕ∞)) ω = S n ω := by
  unfold stoppedValue
  congr 1
  have : (min (τ ω) (n:ℕ∞)) = (n:ℕ∞) := min_eq_right h
  exact (congrArg (fun z : ℕ∞ => WithTop.untopA (α := ℕ) z) this).trans rfl

lemma sv_of_ge (S : ℕ → Ω → ℤ) (τ : Ω → ℕ∞) (n : ℕ) (ω : Ω) (h : τ ω ≤ (n : ℕ∞)) :
    stoppedValue S (fun ω => min (τ ω) (n : ℕ∞)) ω = stoppedValue S τ ω := by
  unfold stoppedValue
  congr 1
  have : (min (τ ω) (n:ℕ∞)) = τ ω := min_eq_left h
  exact (congrArg (fun z : ℕ∞ => WithTop.untopA (α := ℕ) z) this)

lemma enat_le_of_lt_succ (a : ℕ∞) (s : ℕ) (h : a < ((s + 1 : ℕ) : ℕ∞)) : a ≤ (s : ℕ∞) := by
  induction a using ENat.recTopCoe with
  | top => simp at h
  | coe k => norm_cast at h ⊢; omega

lemma enat_succ_le_iff (a : ℕ∞) (s : ℕ) : ((s + 1 : ℕ) : ℕ∞) ≤ a ↔ ¬ a ≤ (s : ℕ∞) := by
  induction a using ENat.recTopCoe with
  | top => simp
  | coe k => norm_cast; omega

/-- pointwise recursion of the stopped walk -/
lemma stopped_succ (S : ℕ → Ω → ℤ) (τ : Ω → ℕ∞) (s : ℕ) (ω : Ω) :
    stoppedValue S (fun ω => min (τ ω) ((s + 1 : ℕ) : ℕ∞)) ω =
      stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)) ω +
        (if ((s + 1 : ℕ) : ℕ∞) ≤ τ ω then S (s + 1) ω - S s ω else 0) := by
  split_ifs with h
  · have h' : (s : ℕ∞) ≤ τ ω := le_trans (by exact_mod_cast Nat.le_succ s) h
    rw [sv_of_le _ _ _ _ h, sv_of_le _ _ _ _ h']; ring
  · have h2 : τ ω ≤ (s : ℕ∞) := (enat_succ_le_iff _ _).not_left.mp h |> fun x => by
      by_contra hc; exact h ((enat_succ_le_iff _ _).mpr hc)
    have h1 : τ ω ≤ ((s + 1 : ℕ) : ℕ∞) := h2.trans (by exact_mod_cast Nat.le_succ s)
    rw [sv_of_ge _ _ _ _ h1, sv_of_ge _ _ _ _ h2]; ring

lemma stopped_zero (S : ℕ → Ω → ℤ) (τ : Ω → ℕ∞) (ω : Ω) :
    stoppedValue S (fun ω => min (τ ω) ((0 : ℕ) : ℕ∞)) ω = S 0 ω :=
  sv_of_le _ _ _ _ (by simp)

lemma abs_S_le {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) : ∀ (t : ℕ) (ω : Ω), |S t ω| ≤ t := by
  intro t
  induction t with
  | zero => intro ω; simp [hS.zero ω]
  | succ t ih =>
    intro ω
    have h1 := ih ω
    rcases hS.step t ω with h | h <;>
    · rw [abs_le] at h1 ⊢; push_cast; constructor <;> linarith [h1.1, h1.2]

lemma parity_S {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) : ∀ (t : ℕ) (ω : Ω), Even (S t ω - t) := by
  intro t
  induction t with
  | zero => intro ω; simp [hS.zero ω]
  | succ t ih =>
    intro ω
    obtain ⟨k, hk⟩ := ih ω
    rcases hS.step t ω with h | h
    · exact ⟨k, by push_cast; linarith⟩
    · exact ⟨k - 1, by push_cast; linarith⟩

lemma stopped_bound (S : ℕ → Ω → ℤ) (hb : ∀ (t : ℕ) (ω : Ω), |S t ω| ≤ t)
    (τ : Ω → ℕ∞) (s : ℕ) (ω : Ω) :
    |stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)) ω| ≤ s := by
  induction s with
  | zero => rw [stopped_zero]; have := hb 0 ω; simpa using this
  | succ s ih =>
    rw [stopped_succ]
    split_ifs with h
    · rw [sv_of_le _ _ _ _ (le_trans (by exact_mod_cast Nat.le_succ s) h)]
      have := hb (s + 1) ω
      simp only [add_sub_cancel]; exact this
    · simp only [add_zero]; push_cast; linarith

lemma meas_stopped {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ) :
    ∀ s : ℕ, Measurable[F s] (stoppedValue S (fun ω => min (τ ω) (s : ℕ∞))) := by
  intro s
  induction s with
  | zero =>
    have : stoppedValue S (fun ω => min (τ ω) ((0 : ℕ) : ℕ∞)) = S 0 := funext (stopped_zero S τ)
    rw [this]; exact hS.adapted 0
  | succ s ih =>
    have : stoppedValue S (fun ω => min (τ ω) ((s + 1 : ℕ) : ℕ∞)) = fun ω =>
        stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)) ω +
        (if ((s + 1 : ℕ) : ℕ∞) ≤ τ ω then S (s + 1) ω - S s ω else 0) :=
      funext (stopped_succ S τ s)
    rw [this]
    have hA : MeasurableSet[F s] {ω | ((s + 1 : ℕ) : ℕ∞) ≤ τ ω} := by
      have := (hτ (s)).compl
      convert this using 1
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
      exact enat_succ_le_iff _ _
    have hmono := F.mono (Nat.le_succ s)
    apply Measurable.add (ih.mono hmono le_rfl)
    apply Measurable.ite (hmono _ hA)
    · exact (hS.adapted (s + 1)).sub ((hS.adapted s).mono hmono le_rfl)
    · exact measurable_const

end Casino31Prob

namespace Casino31Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma indep_fun_of {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (s : ℕ) (h : ℤ → ℝ) (f : Ω → ℝ) (hf : Measurable[F s] f) :
    IndepFun (fun ω => h (S (s + 1) ω - S s ω)) f P := by
  rw [IndepFun_iff_Indep]
  have h1 : MeasurableSpace.comap (fun ω => h (S (s + 1) ω - S s ω)) (borel ℝ) ≤
      MeasurableSpace.comap (fun ω => S (s + 1) ω - S s ω) inferInstance := by
    have : (fun ω => h (S (s + 1) ω - S s ω)) = h ∘ (fun ω => S (s + 1) ω - S s ω) := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_from_top (f := h)).comap_le
  have h2 : MeasurableSpace.comap f (borel ℝ) ≤ F s := hf.comap_le
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left (hS.indep s) h1) h2

lemma prob_up {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (s : ℕ) :
    P.real {ω | S (s + 1) ω - S s ω = 1} = 1 / 2 := by
  rw [measureReal_def, hS.fair s]; simp

lemma prob_down {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (s : ℕ) :
    P.real {ω | S (s + 1) ω - S s ω = -1} = 1 / 2 := by
  have hP := hS.isProb
  have hm : ∀ t, Measurable (S t) := fun t => (hS.adapted t).mono (F.le t) le_rfl
  have hDm : Measurable (fun ω => S (s + 1) ω - S s ω) := (hm (s + 1)).sub (hm s)
  have hcompl : {ω | S (s + 1) ω - S s ω = -1} = {ω | S (s + 1) ω - S s ω = 1}ᶜ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    rcases hS.step s ω with h | h <;> rw [h] <;> norm_num
  have hm1 : MeasurableSet {ω | S (s + 1) ω - S s ω = 1} := hDm (measurableSet_singleton 1)
  rw [hcompl, probReal_compl_eq_one_sub hm1, prob_up hS s]
  norm_num

/-- One step of the (possibly stopped) walk: the key expectation identity. -/
lemma key_step {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (s : ℕ) (X : Ω → ℤ) (hX : Measurable[F s] X)
    (p : Ω → Prop) [DecidablePred p] (hA : MeasurableSet[F s] {ω | p ω}) (g : ℤ → ℝ)
    (h0 : Integrable (fun ω => g (X ω)) P) (hp : Integrable (fun ω => g (X ω + 1)) P)
    (hn : Integrable (fun ω => g (X ω - 1)) P) :
    ∫ ω, g (X ω + (if p ω then S (s + 1) ω - S s ω else 0)) ∂P =
      ∫ ω, {ω | p ω}ᶜ.indicator (fun ω => g (X ω)) ω ∂P +
        ∫ ω, {ω | p ω}.indicator (fun ω => (g (X ω + 1) + g (X ω - 1)) / 2) ω ∂P := by
  have hP := hS.isProb
  set A : Set Ω := {ω | p ω} with hAdef
  set D : Ω → ℤ := fun ω => S (s + 1) ω - S s ω with hD
  let e1 : Ω → ℝ := fun ω => (fun z : ℤ => if z = 1 then (1:ℝ) else 0) (D ω)
  let e2 : Ω → ℝ := fun ω => (fun z : ℤ => if z = -1 then (1:ℝ) else 0) (D ω)
  have hF : F s ≤ mΩ := F.le s
  have hXm : Measurable X := hX.mono hF le_rfl
  have hAm : MeasurableSet A := hF _ hA
  have f1m : Measurable[F s] (A.indicator (fun ω => g (X ω + 1))) :=
    Measurable.indicator ((measurable_from_top (f := fun z : ℤ => g (z + 1))).comp hX) hA
  have f2m : Measurable[F s] (A.indicator (fun ω => g (X ω - 1))) :=
    Measurable.indicator ((measurable_from_top (f := fun z : ℤ => g (z - 1))).comp hX) hA
  have hDm : Measurable D :=
    ((hS.adapted (s + 1)).mono (F.le _) le_rfl).sub ((hS.adapted s).mono hF le_rfl)
  have e1m : Measurable e1 :=
    (measurable_from_top (f := fun z : ℤ => if z = 1 then (1:ℝ) else 0)).comp hDm
  have e2m : Measurable e2 :=
    (measurable_from_top (f := fun z : ℤ => if z = -1 then (1:ℝ) else 0)).comp hDm
  have hm1 : MeasurableSet {ω | D ω = 1} := hDm (measurableSet_singleton 1)
  have hm2 : MeasurableSet {ω | D ω = -1} := hDm (measurableSet_singleton (-1))
  have i1 := indep_fun_of hS s (fun z : ℤ => if z = 1 then (1:ℝ) else 0) _ f1m
  have i2 := indep_fun_of hS s (fun z : ℤ => if z = -1 then (1:ℝ) else 0) _ f2m
  have I1 : Integrable (A.indicator (fun ω => g (X ω + 1))) P := hp.indicator hAm
  have I2 : Integrable (A.indicator (fun ω => g (X ω - 1))) P := hn.indicator hAm
  have E1 : ∫ ω, e1 ω ∂P = 1 / 2 := by
    have : e1 = {ω | D ω = 1}.indicator 1 := by
      ext ω; simp only [e1, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [this, integral_indicator_one hm1]
    exact prob_up hS s
  have E2 : ∫ ω, e2 ω ∂P = 1 / 2 := by
    have : e2 = {ω | D ω = -1}.indicator 1 := by
      ext ω; simp only [e2, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [this, integral_indicator_one hm2]
    exact prob_down hS s
  have J1 := i1.integral_fun_mul_eq_mul_integral e1m.aestronglyMeasurable I1.1
  have J2 := i2.integral_fun_mul_eq_mul_integral e2m.aestronglyMeasurable I2.1
  have hb1 : ∀ ω, ‖e1 ω‖ ≤ 1 := by intro ω; simp only [e1]; split_ifs <;> simp
  have hb2 : ∀ ω, ‖e2 ω‖ ≤ 1 := by intro ω; simp only [e2]; split_ifs <;> simp
  have K1 : Integrable (fun ω => e1 ω * A.indicator (fun ω => g (X ω + 1)) ω) P :=
    I1.bdd_mul e1m.aestronglyMeasurable (Filter.Eventually.of_forall hb1)
  have K2 : Integrable (fun ω => e2 ω * A.indicator (fun ω => g (X ω - 1)) ω) P :=
    I2.bdd_mul e2m.aestronglyMeasurable (Filter.Eventually.of_forall hb2)
  have K0 : Integrable (Aᶜ.indicator (fun ω => g (X ω))) P := h0.indicator hAm.compl
  have hpt : ∀ ω, g (X ω + (if p ω then D ω else 0)) =
      Aᶜ.indicator (fun ω => g (X ω)) ω + (e1 ω * A.indicator (fun ω => g (X ω + 1)) ω +
        e2 ω * A.indicator (fun ω => g (X ω - 1)) ω) := by
    intro ω
    by_cases hω : ω ∈ A
    · have hω' : p ω := hω
      simp only [hω', if_true, Set.indicator_of_mem hω, Set.indicator_of_notMem
        (Set.notMem_compl_iff.mpr hω), e1, e2]
      rcases hS.step s ω with h | h
      · have : D ω = 1 := h
        rw [this]; norm_num
      · have : D ω = -1 := h
        rw [this]; norm_num; ring_nf
    · have hω' : ¬ p ω := hω
      simp only [hω', if_false, Set.indicator_of_notMem hω, Set.indicator_of_mem
        (Set.mem_compl hω)]
      simp
  refine (integral_congr_ae (Filter.Eventually.of_forall hpt)).trans ?_
  have Ksum : Integrable (fun ω => e1 ω * A.indicator (fun ω => g (X ω + 1)) ω +
      e2 ω * A.indicator (fun ω => g (X ω - 1)) ω) P := K1.add K2
  rw [integral_add K0 Ksum, integral_add K1 K2, J1, J2, E1, E2]
  congr 1
  rw [← mul_add, ← integral_add I1 I2, ← integral_const_mul]
  congr 1; ext ω
  simp only [Set.indicator]
  split_ifs <;> ring

end Casino31Prob

namespace Casino31Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma pot_map (P : Measure Ω) (X : Ω → ℤ) (hX : Measurable X) (x : ℝ) :
    potential (P.map X) x = ∫ ω, |x - (X ω : ℝ)| ∂P := by
  unfold potential
  exact integral_map hX.aemeasurable
    (measurable_from_top (f := fun y : ℤ => |x - (y : ℝ)|)).aestronglyMeasurable

lemma integrable_bdd (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℤ) (hX : Measurable X)
    (C : ℤ) (hC : ∀ ω, |X ω| ≤ C) (g : ℤ → ℝ) (k : ℤ) (x : ℝ)
    (hg : ∀ y : ℤ, |g y| ≤ |x| + |(y : ℝ)|) :
    Integrable (fun ω => g (X ω + k)) P := by
  refine Integrable.of_bound ((measurable_from_top (f := fun y : ℤ => g (y + k))).comp hX
    ).aestronglyMeasurable (|x| + C + |(k : ℝ)|) (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs]
  refine (hg _).trans ?_
  have h1 : |((X ω + k : ℤ) : ℝ)| ≤ |(X ω : ℝ)| + |(k : ℝ)| := by push_cast; exact abs_add_le _ _
  have h2 : |(X ω : ℝ)| ≤ (C : ℝ) := by
    have := hC ω; rw [← Int.cast_abs]; exact_mod_cast this
  linarith

lemma kernel_bound (x : ℝ) (y : ℤ) : |(|x - (y : ℝ)|)| ≤ |x| + |(y : ℝ)| := by
  rw [abs_abs]; exact abs_sub _ _

lemma second_diff (x y : ℤ) :
    (|(x : ℝ) - ((y + 1 : ℤ) : ℝ)| + |(x : ℝ) - ((y - 1 : ℤ) : ℝ)|) / 2 - |(x : ℝ) - (y : ℝ)| =
      if y = x then 1 else 0 := by
  have hz : |x - (y + 1)| + |x - (y - 1)| - 2 * |x - y| = if y = x then 2 else 0 := by
    split_ifs with h
    · subst h; simp
    · simp only [abs_eq_max_neg]; omega
  have hz' : ((|x - (y + 1)| + |x - (y - 1)| - 2 * |x - y| : ℤ) : ℝ)
      = ((if y = x then 2 else 0 : ℤ) : ℝ) := by rw [hz]
  push_cast at hz' ⊢
  split_ifs at hz' ⊢ <;> linarith

/-- Proposition A.1 (iii), eq. (17), in the form `t = s + 1`. -/
lemma pot_step {P : Measure Ω} {F : Filtration ℕ mΩ} {S : ℕ → Ω → ℤ} {ξ : Ω → ℝ}
    (hS : IsCasinoSpace P F S ξ) (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ) (s : ℕ) (x : ℤ) :
    potential (P.map (stoppedValue S (fun ω => min (τ ω) ((s + 1 : ℕ) : ℕ∞)))) (x : ℝ) =
      potential (P.map (stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)))) (x : ℝ) +
        (P {ω | S s ω = x ∧ ((s + 1 : ℕ) : ℕ∞) ≤ τ ω}).toReal := by
  have hP := hS.isProb
  set X := stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)) with hXdef
  have hXF : Measurable[F s] X := meas_stopped hS τ hτ s
  have hXm : Measurable X := hXF.mono (F.le s) le_rfl
  have hXF1 := meas_stopped hS τ hτ (s + 1)
  have hX1m := hXF1.mono (F.le (s + 1)) le_rfl
  have hb : ∀ ω, |X ω| ≤ (s : ℤ) := stopped_bound S (abs_S_le hS) τ s
  let g : ℤ → ℝ := fun y => |(x : ℝ) - (y : ℝ)|
  have hg : ∀ y : ℤ, |g y| ≤ |(x : ℝ)| + |(y : ℝ)| := kernel_bound _
  have I : ∀ k : ℤ, Integrable (fun ω => g (X ω + k)) P :=
    fun k => integrable_bdd P X hXm s hb g k x hg
  have I0 : Integrable (fun ω => g (X ω)) P := by simpa using I 0
  have Ip : Integrable (fun ω => g (X ω + 1)) P := I 1
  have In : Integrable (fun ω => g (X ω - 1)) P := by simpa [sub_eq_add_neg] using I (-1)
  let p : Ω → Prop := fun ω => ((s + 1 : ℕ) : ℕ∞) ≤ τ ω
  have hA : MeasurableSet[F s] {ω | p ω} := by
    have := (hτ s).compl
    convert this using 1
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, p]
    exact enat_succ_le_iff _ _
  have key := key_step hS s X hXF p hA g I0 Ip In
  rw [pot_map P _ hX1m, pot_map P _ hXm]
  have e1 : (fun ω => |(x : ℝ) - ((stoppedValue S (fun ω => min (τ ω) ((s + 1 : ℕ) : ℕ∞)) ω : ℤ) : ℝ)|)
      = fun ω => g (X ω + (if p ω then S (s + 1) ω - S s ω else 0)) := by
    ext ω; simp only [g, p]; rw [stopped_succ]
  rw [e1, key]
  have hAm : MeasurableSet {ω | p ω} := F.le s _ hA
  have split0 : ∫ ω, g (X ω) ∂P = ∫ ω, {ω | p ω}ᶜ.indicator (fun ω => g (X ω)) ω ∂P +
      ∫ ω, {ω | p ω}.indicator (fun ω => g (X ω)) ω ∂P := by
    rw [← integral_add (I0.indicator hAm.compl) (I0.indicator hAm)]
    congr 1; ext ω
    by_cases h : ω ∈ {ω | p ω}
    · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h)]; ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (Set.mem_compl h)]; ring
  have hgX : (fun ω => |(x : ℝ) - (X ω : ℝ)|) = fun ω => g (X ω) := rfl
  rw [hgX, split0, add_assoc]
  congr 1
  have hE : {ω | S s ω = x ∧ ((s + 1 : ℕ) : ℕ∞) ≤ τ ω} = {ω | p ω} ∩ {ω | X ω = x} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, p]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [hXdef, sv_of_le _ _ _ _ (le_trans (by exact_mod_cast Nat.le_succ s) h2)]; exact h1
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      rw [hXdef, sv_of_le _ _ _ _ (le_trans (by exact_mod_cast Nat.le_succ s) h2)] at h1; exact h1
  have hXx : MeasurableSet {ω | X ω = x} := hXm (measurableSet_singleton x)
  have hsum := integral_add (μ := P) (f := {ω | p ω}.indicator (fun ω => g (X ω)))
    (g := ({ω | p ω} ∩ {ω | X ω = x}).indicator (1 : Ω → ℝ)) (I0.indicator hAm)
    (by exact (integrable_const (1:ℝ)).indicator (hAm.inter hXx))
  rw [hE, ← measureReal_def, ← integral_indicator_one (hAm.inter hXx), ← hsum]
  · congr 1; ext ω
    by_cases h : ω ∈ {ω | p ω}
    · have h' : ω ∈ ({ω | p ω} ∩ {ω | X ω = x}) ↔ X ω = x := by
        simp only [Set.mem_inter_iff]; exact ⟨fun h => h.2, fun h2 => ⟨h, h2⟩⟩
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      have := second_diff x (X ω)
      simp only [g]
      by_cases hx : X ω = x
      · rw [Set.indicator_of_mem (h'.mpr hx)]; rw [if_pos hx] at this
        push_cast at this ⊢; simp only [Pi.one_apply]; linarith
      · rw [Set.indicator_of_notMem (fun hh => hx (h'.mp hh))]; rw [if_neg hx] at this
        push_cast at this ⊢; linarith
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h,
        Set.indicator_of_notMem (fun hh => h hh.1)]; ring

end Casino31Prob

open MeasureTheory ProbabilityTheory CasinoCPT.Embedding Casino31Prob

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) (hS : IsCasinoSpace P F S ξ)
    (τ : Ω → ℕ∞) (hτ : IsStoppingTime F τ)
    (hUI : UniformIntegrable
      (fun (t : ℕ) (ω : Ω) => ((stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)) ω : ℤ) : ℝ)) 1 P)
    (t : ℕ) (ht : 1 ≤ t) :
    (∀ x : ℤ,
      potential (P.map (stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)))) (x : ℝ) =
        potential (P.map (stoppedValue S (fun ω => min (τ ω) ((t - 1 : ℕ) : ℕ∞)))) (x : ℝ) +
          (if Even (x - ((t : ℤ) - 1)) then
            (P {ω | S (t - 1) ω = x ∧ (t : ℕ∞) ≤ τ ω}).toReal else 0)) ∧
      (Odd t → ∀ x : ℤ, Odd x →
        potential (P.map (stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)))) (x : ℝ) =
          potential (P.map (stoppedValue S (fun ω => min (τ ω) ((t - 1 : ℕ) : ℕ∞)))) (x : ℝ)) ∧
      (Even t → ∀ x : ℤ, Even x →
        potential (P.map (stoppedValue S (fun ω => min (τ ω) (t : ℕ∞)))) (x : ℝ) =
          potential (P.map (stoppedValue S (fun ω => min (τ ω) ((t - 1 : ℕ) : ℕ∞)))) (x : ℝ)) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hs : s + 1 - 1 = s := by omega
  rw [hs]
  have main : ∀ x : ℤ,
      potential (P.map (stoppedValue S (fun ω => min (τ ω) ((s + 1 : ℕ) : ℕ∞)))) (x : ℝ) =
        potential (P.map (stoppedValue S (fun ω => min (τ ω) (s : ℕ∞)))) (x : ℝ) +
          (if Even (x - (((s + 1 : ℕ) : ℤ) - 1)) then
            (P {ω | S s ω = x ∧ ((s + 1 : ℕ) : ℕ∞) ≤ τ ω}).toReal else 0) := by
    intro x
    rw [pot_step hS τ hτ s x]
    split_ifs with h
    · rfl
    · have hempty : {ω | S s ω = x ∧ ((s + 1 : ℕ) : ℕ∞) ≤ τ ω} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hx _
        apply h
        have := parity_S hS s ω
        rw [hx] at this
        convert this using 1; push_cast; ring
      rw [hempty]; simp
  refine ⟨main, ?_, ?_⟩
  · intro ht x hx
    rw [main x, if_neg]; · ring
    intro he
    have h1 : Even (s : ℤ) := by
      have : Odd ((s + 1 : ℕ) : ℤ) := (Int.odd_coe_nat _).mpr ht
      push_cast at this
      exact (Int.even_add_one).mpr (Int.not_even_iff_odd.mpr this) |> fun h => by
        rcases this with ⟨k, hk⟩; exact ⟨k, by omega⟩
    have : Even (x - (((s + 1 : ℕ) : ℤ) - 1)) := he
    push_cast at this
    have : Even x := by
      have := this.add h1; simpa using this
    exact (Int.not_even_iff_odd.mpr hx) this
  · intro ht x hx
    rw [main x, if_neg]; · ring
    intro he
    have : Even (x - (((s + 1 : ℕ) : ℤ) - 1)) := he
    push_cast at this
    have h2 : Even ((s : ℤ) + 1) := by exact_mod_cast (Int.even_coe_nat _).mpr ht
    have h3 : Even (x - ((s:ℤ) + 1 - 1) + ((s : ℤ) + 1) - x) := by
      have := (this.add h2).sub hx; exact this
    have : (x - ((s:ℤ) + 1 - 1) + ((s : ℤ) + 1) - x) = 1 := by ring
    rw [this] at h3
    exact absurd h3 (by decide)
