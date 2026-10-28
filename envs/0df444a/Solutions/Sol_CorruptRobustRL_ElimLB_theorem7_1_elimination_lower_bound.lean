-- Prove2me | solution 1 for CorruptRobustRL.ElimLB.theorem7_1_elimination_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T09:02:20.325012+00:00
-- url     : https://prove2.me/submissions/0c1db077-f770-44fd-8b8b-aaade5f5517d

import Mathlib
import Definitions.Def_CorruptRobustRL_ElimLB_MDP
import Definitions.Def_CorruptRobustRL_ElimLB_Setting
import Definitions.Def_CorruptRobustRL_ElimLB_ComboLock

set_option autoImplicit false

namespace ElimLBSol

open CorruptRobustRL.ElimLB
open scoped ENNReal
open MeasureTheory

section General

variable {X B : Type} [Fintype X] [Fintype B] [Nonempty B]

lemma pmf_sum_toReal (q : PMF X) : ∑ x, (q x).toReal = 1 := by
  have h1 := PMF.tsum_coe q
  rw [tsum_fintype] at h1
  rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top q x), h1, ENNReal.toReal_one]

lemma outer_le_one {α : Type} (p : PMF α) (s : Set α) : p.toOuterMeasure s ≤ 1 := by
  rw [← (p.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)]
  exact measure_mono (Set.subset_univ _)

lemma sum_pure_mul (y : X) (f : X → ℝ) : ∑ x, ((PMF.pure y) x).toReal * f x = f y := by
  classical
  rw [Finset.sum_eq_single y]
  · simp
  · intro b _ hb
    simp [PMF.pure_apply, hb]
  · simp

lemma rbar_pure_aux (c : ℝ) : (∑' r : ℝ, ((PMF.pure c) r).toReal * r) = c := by
  rw [tsum_eq_single c]
  · simp
  · intro b hb
    simp [PMF.pure_apply, hb]

lemma bind_outer_le {α β : Type} (q : PMF α) (g : α → PMF β) (S : Set β) (c : ℝ≥0∞)
    (hg : ∀ a, (g a).toOuterMeasure S ≤ c) : (q.bind g).toOuterMeasure S ≤ c := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc ∑' a, q a * (g a).toOuterMeasure S ≤ ∑' a, q a * c :=
        ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (hg a) _)
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma list_sum_ge {α : Type} (f : α → ℝ) (b : ℝ) :
    ∀ l : List α, (∀ e ∈ l, b ≤ f e) → (l.length : ℝ) * b ≤ (l.map f).sum
  | [], _ => by simp
  | e :: l, hf => by
    have ih := list_sum_ge f b l (fun e' he' => hf e' (List.mem_cons_of_mem _ he'))
    have he := hf e List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith

lemma list_sum_le {α : Type} (f : α → ℝ) (b : ℝ) :
    ∀ l : List α, (∀ e ∈ l, f e ≤ b) → (l.map f).sum ≤ (l.length : ℝ) * b
  | [], _ => by simp
  | e :: l, hf => by
    have ih := list_sum_le f b l (fun e' he' => hf e' (List.mem_cons_of_mem _ he'))
    have he := hf e List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith

variable {H : ℕ}

lemma sum_unif_toReal (T : Supervisor X B H) (h : ℕ) (x : X) :
    ∑ a, (unifPlaus T h x a).toReal = 1 := pmf_sum_toReal _

lemma Vunif_le_Vopt (inst : Instance X B) (T : Supervisor X B H) :
    ∀ n h x, Vunif inst T n h x ≤ Vopt inst n x
  | 0, _, _ => le_refl _
  | n + 1, h, x => by
    simp only [Vunif, Vopt]
    calc ∑ a, (unifPlaus T h x a).toReal *
          (inst.rbar x a + ∑ x', (inst.p x a x').toReal * Vunif inst T n (h + 1) x')
        ≤ ∑ a, (unifPlaus T h x a).toReal *
          (inst.rbar x a + ∑ x', (inst.p x a x').toReal * Vopt inst n x') := by
          refine Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
          refine add_le_add (le_refl _) (Finset.sum_le_sum (fun x' _ => ?_))
          exact mul_le_mul_of_nonneg_left (Vunif_le_Vopt inst T n (h + 1) x') ENNReal.toReal_nonneg
      _ ≤ ∑ a, (unifPlaus T h x a).toReal * Finset.univ.sup' Finset.univ_nonempty
            (fun a => inst.rbar x a + ∑ x', (inst.p x a x').toReal * Vopt inst n x') := by
          refine Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
          exact Finset.le_sup' (fun a => inst.rbar x a + ∑ x', (inst.p x a x').toReal *
            Vopt inst n x') (Finset.mem_univ a)
      _ = _ := by rw [← Finset.sum_mul, sum_unif_toReal, one_mul]

lemma valueUnif_le_Vstar (inst : Instance X B) (T : Supervisor X B H) :
    valueUnif inst T ≤ Vstar inst H := by
  unfold valueUnif Vstar
  exact Finset.sum_le_sum (fun x _ =>
    mul_le_mul_of_nonneg_left (Vunif_le_Vopt inst T H 0 x) ENNReal.toReal_nonneg)

lemma runLaw_length (inst : Instance X B) (L : Learner X B H) :
    ∀ K run, runLaw inst L K run ≠ 0 → run.length = K
  | 0, run, hne => by
    simp only [runLaw, PMF.pure_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] at hne
    rw [hne.1]; rfl
  | K + 1, run, hne => by
    rw [← PMF.mem_support_iff] at hne
    simp only [runLaw, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hne
    obtain ⟨hist, hh, T, -, τ, -, rfl⟩ := hne
    rw [PMF.mem_support_iff] at hh
    simp [runLaw_length inst L K hist hh]

end General

variable {H A : ℕ} [NeZero A]


lemma rbar_M0 (x : Fin (H + 1)) (a : Fin A) : (comboLock0 H A).rbar x a = 0 := by
  simp only [Instance.rbar, comboLock0]
  exact rbar_pure_aux 0

lemma rbar_M (x : Fin (H + 1)) (a : Fin A) :
    (comboLock H A).rbar x a = if x.val = H ∧ a = 0 then 1 else 0 := by
  simp only [Instance.rbar, comboLock]
  split_ifs <;> exact rbar_pure_aux _

lemma Vopt_M0 : ∀ n (x : Fin (H + 1)), Vopt (comboLock0 H A) n x = 0
  | 0, _ => rfl
  | n + 1, x => by
    simp only [Vopt, rbar_M0, Vopt_M0 n, mul_zero, Finset.sum_const_zero, add_zero]
    exact Finset.sup'_const _ _

lemma adm_plaus (T : Supervisor (Fin (H + 1)) (Fin A) H)
    (hT : IsAdmissible (comboLock0 H A) T) (h : ℕ) (hh : h < H) (x : Fin (H + 1)) :
    plaus T h x = Finset.univ := by
  obtain ⟨hopt, hq⟩ := hT h hh x
  have hq0 : ∀ a, Qstar (comboLock0 H A) H h x a = 0 := by
    intro a; simp [Qstar, rbar_M0, Vopt_M0]
  have hv0 : VstarAt (comboLock0 H A) H h x = 0 := by simp [VstarAt, Vopt_M0]
  have hact : T.act h x = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro a
    have : a ∈ optActions (comboLock0 H A) H h x := by
      simp [optActions, hq0, hv0]
    exact_mod_cast hopt this
  apply Finset.eq_univ_of_forall
  intro a
  unfold plaus
  simp only [Finset.mem_filter, hact, Finset.mem_univ, true_and]
  intro a' _
  have h1 := (hq a').1
  have h2 := (hq a).2
  rw [hq0] at h1 h2
  linarith

lemma adm_unif (T : Supervisor (Fin (H + 1)) (Fin A) H)
    (hT : IsAdmissible (comboLock0 H A) T) (h : ℕ) (hh : h < H) (x : Fin (H + 1)) (a : Fin A) :
    unifPlaus T h x a = (A : ℝ≥0∞)⁻¹ := by
  have hp := adm_plaus T hT h hh x
  unfold unifPlaus
  have hmem : a ∈ plaus T h x := by rw [hp]; exact Finset.mem_univ a
  split_ifs with hne
  · rw [PMF.uniformOfFinset_apply, if_pos hmem, hp, Finset.card_univ, Fintype.card_fin]
  · exact absurd ⟨a, hmem⟩ hne

/-- all actions of a trajectory are the paper's action `1` (our `0`). -/
def Zp (τ : Traj (Fin (H + 1)) (Fin A)) : Prop := ∀ s ∈ τ, s.2.1 = 0

lemma steps_Z_le (inst : Instance (Fin (H + 1)) (Fin A)) (T : Supervisor (Fin (H + 1)) (Fin A) H)
    (hU : ∀ h x a, h < H → unifPlaus T h x a = (A : ℝ≥0∞)⁻¹) :
    ∀ n h x, h + n ≤ H →
      (stepsLaw inst T n h x).toOuterMeasure {τ | Zp τ} ≤ ((A : ℝ≥0∞)⁻¹) ^ n
  | 0, h, x, _ => by simpa using outer_le_one _ _
  | n + 1, h, x, hn => by
    rw [stepsLaw, PMF.toOuterMeasure_bind_apply]
    have key : ∀ a, ((inst.R x a).bind fun r => (inst.p x a).bind fun x' =>
        (stepsLaw inst T n (h + 1) x').map fun rest => (x, a, r) :: rest).toOuterMeasure
          {τ | Zp τ} ≤ if a = 0 then ((A : ℝ≥0∞)⁻¹) ^ n else 0 := by
      intro a
      refine bind_outer_le _ _ _ _ (fun r => bind_outer_le _ _ _ _ (fun x' => ?_))
      rw [PMF.toOuterMeasure_map_apply]
      split_ifs with ha
      · calc (stepsLaw inst T n (h + 1) x').toOuterMeasure
              ((fun rest => (x, a, r) :: rest) ⁻¹' {τ | Zp τ})
            ≤ (stepsLaw inst T n (h + 1) x').toOuterMeasure {τ | Zp τ} := by
              apply measure_mono
              intro τ hτ s hs
              exact hτ s (List.mem_cons_of_mem _ hs)
          _ ≤ _ := steps_Z_le inst T hU n (h + 1) x' (by omega)
      · refine le_of_le_of_eq (measure_mono (t := (∅ : Set (Traj (Fin (H + 1)) (Fin A)))) ?_)
          measure_empty
        intro τ hτ
        exact ha (hτ _ List.mem_cons_self)
    calc ∑' a, unifPlaus T h x a * ((inst.R x a).bind fun r => (inst.p x a).bind fun x' =>
          (stepsLaw inst T n (h + 1) x').map fun rest => (x, a, r) :: rest).toOuterMeasure
            {τ | Zp τ}
        ≤ ∑' a, unifPlaus T h x a * (if a = 0 then ((A : ℝ≥0∞)⁻¹) ^ n else 0) :=
          ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (key a) _)
      _ = (A : ℝ≥0∞)⁻¹ * ((A : ℝ≥0∞)⁻¹) ^ n := by
          rw [tsum_eq_single 0 (fun b hb => by simp [hb])]
          simp [hU h x 0 (by omega)]
      _ = _ := (pow_succ' _ _).symm

lemma ep_eq_steps (inst : Instance (Fin (H + 1)) (Fin A)) (hp0 : inst.p0 = PMF.pure 1)
    (T : Supervisor (Fin (H + 1)) (Fin A) H) :
    episodeLaw inst T = stepsLaw inst T H 0 1 := by
  unfold episodeLaw
  rw [hp0, PMF.pure_bind]

lemma ep0_Z_le (T : Supervisor (Fin (H + 1)) (Fin A) H) (hT : IsAdmissible (comboLock0 H A) T) :
    (episodeLaw (comboLock0 H A) T).toOuterMeasure {τ | Zp τ} ≤ ((A : ℝ≥0∞)⁻¹) ^ H := by
  rw [ep_eq_steps _ rfl]
  exact steps_Z_le _ T (fun h x a hh => adm_unif T hT h hh x a) H 0 1 (by omega)

/-- the paper's bad pair `(x^{(H)}, action 1)` never occurs in the trajectory -/
lemma steps_eq (T : Supervisor (Fin (H + 1)) (Fin A) H) :
    ∀ (n h : ℕ) (x : Fin (H + 1)) (τ : Traj (Fin (H + 1)) (Fin A)),
      (∀ s ∈ τ, ¬ (s.1.val = H ∧ s.2.1 = 0)) →
      stepsLaw (comboLock0 H A) T n h x τ = stepsLaw (comboLock H A) T n h x τ
  | 0, _, _, _, _ => rfl
  | n + 1, h, x, τ, hτ => by
    simp only [stepsLaw, PMF.bind_apply, PMF.map_apply]
    refine tsum_congr (fun a => ?_)
    congr 1
    by_cases hxa : x.val = H ∧ a = 0
    · have hne : ∀ (r : ℝ) (rest : Traj (Fin (H + 1)) (Fin A)), ¬ τ = (x, a, r) :: rest := by
        rintro r rest rfl
        exact hτ _ List.mem_cons_self hxa
      trans (0 : ℝ≥0∞)
      · refine ENNReal.tsum_eq_zero.mpr (fun r => mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr
          (fun x' => mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr
            (fun rest => if_neg (hne r rest))))))
      · symm
        refine ENNReal.tsum_eq_zero.mpr (fun r => mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr
          (fun x' => mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr
            (fun rest => if_neg (hne r rest))))))
    · have hR : (comboLock0 H A).R x a = (comboLock H A).R x a := by
        simp [comboLock0, comboLock, hxa]
      rw [hR]
      refine tsum_congr (fun r => ?_)
      congr 1
      refine tsum_congr (fun x' => ?_)
      congr 1
      refine tsum_congr (fun rest => ?_)
      split_ifs with he
      · subst he
        exact steps_eq T n (h + 1) x' rest (fun s hs => hτ s (List.mem_cons_of_mem _ hs))
      · rfl

lemma steps_supp (hH : 0 < H) (T : Supervisor (Fin (H + 1)) (Fin A) H) :
    ∀ (n h : ℕ) (x : Fin (H + 1)) (τ : Traj (Fin (H + 1)) (Fin A)),
      stepsLaw (comboLock0 H A) T n h x τ ≠ 0 → (x.val = 0 ∨ x.val + n ≤ H + 1) →
      (∃ s ∈ τ, s.1.val = H ∧ s.2.1 = 0) → (∀ s ∈ τ, s.2.1 = 0) ∧ x.val ≠ 0
  | 0, h, x, τ, hne, _, hbad => by
    simp only [stepsLaw, PMF.pure_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] at hne
    obtain ⟨s, hs, -⟩ := hbad
    rw [hne.1] at hs
    simp at hs
  | n + 1, h, x, τ, hne, hinv, hbad => by
    rw [← PMF.mem_support_iff] at hne
    simp only [stepsLaw, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hne
    obtain ⟨a, -, r, -, x', hx', rest, hrest, rfl⟩ := hne
    rw [PMF.mem_support_iff] at hrest
    have hstep : (1 ≤ x.val ∧ x.val < H ∧ a = 0 ∧ x'.val = x.val + 1) ∨ x' = 0 := by
      simp only [comboLock0, comboTrans] at hx'
      split_ifs at hx' with hc
      · left
        simp only [PMF.support_pure, Set.mem_singleton_iff] at hx'
        exact ⟨hc.1, hc.2.1, hc.2.2, by rw [hx']⟩
      · right
        simpa using hx'
    rcases List.mem_cons.1 (show _ from hbad.choose_spec.1) with hhead | htail
    · -- the bad entry is the head
      have hb := hbad.choose_spec.2
      rw [hhead] at hb
      simp only at hb
      obtain ⟨hb1, hb2⟩ := hb
      have hn0 : n = 0 := by
        rcases hinv with h0 | h0 <;> omega
      subst hn0
      simp only [stepsLaw, PMF.pure_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] at hrest
      rw [hrest.1]
      refine ⟨?_, by omega⟩
      intro s hs
      simp only [List.mem_singleton] at hs
      rw [hs]
      exact hb2
    · have hinv' : x'.val = 0 ∨ x'.val + n ≤ H + 1 := by
        rcases hstep with ⟨h1, -, -, h4⟩ | h0
        · right; rcases hinv with h0 | h0 <;> omega
        · left; rw [h0]; rfl
      have ih := steps_supp hH T n (h + 1) x' rest hrest hinv'
        ⟨hbad.choose, htail, hbad.choose_spec.2⟩
      rcases hstep with ⟨h1, -, ha, -⟩ | h0
      · refine ⟨?_, by omega⟩
        intro s hs
        rcases List.mem_cons.1 hs with hs | hs
        · rw [hs]; exact ha
        · exact ih.1 s hs
      · exact absurd (by rw [h0]; rfl) ih.2

lemma ep_le (hH : 0 < H) (T : Supervisor (Fin (H + 1)) (Fin A) H) (τ : Traj (Fin (H + 1)) (Fin A))
    (hZ : ¬ Zp τ) :
    episodeLaw (comboLock0 H A) T τ ≤ episodeLaw (comboLock H A) T τ := by
  rw [ep_eq_steps _ rfl, ep_eq_steps _ rfl]
  by_cases h0 : stepsLaw (comboLock0 H A) T H 0 1 τ = 0
  · rw [h0]; exact zero_le
  refine le_of_eq (steps_eq T H 0 1 τ ?_)
  intro s hs hbad
  have h1 : ((1 : Fin (H + 1)) : ℕ) ≤ 1 := by
    rw [Fin.val_one']; exact Nat.mod_le _ _
  exact hZ (steps_supp hH T H 0 1 τ h0 (Or.inr (by omega)) ⟨s, hs, hbad⟩).1

/-- the good event: every supervisor admissible for `ℳ₀` and no all-`1` episode -/
def Good (run : List (Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A))) : Prop :=
  ∀ e ∈ run, IsAdmissible (comboLock0 H A) e.1 ∧ ¬ Zp e.2

def Bad (run : List (Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A))) : Prop :=
  (∀ e ∈ run, IsAdmissible (comboLock0 H A) e.1) ∧ ∃ e ∈ run, Zp e.2

lemma run_le (hH : 0 < H) (L : Learner (Fin (H + 1)) (Fin A) H) :
    ∀ K run, Good run → runLaw (comboLock0 H A) L K run ≤ runLaw (comboLock H A) L K run
  | 0, _, _ => le_refl _
  | K + 1, run, hG => by
    simp only [runLaw, PMF.bind_apply, PMF.map_apply]
    refine ENNReal.tsum_le_tsum (fun hist => ?_)
    by_cases hGh : Good hist
    · refine mul_le_mul' (run_le hH L K hist hGh) ?_
      refine ENNReal.tsum_le_tsum (fun T => mul_le_mul_right ?_ _)
      refine ENNReal.tsum_le_tsum (fun τ => ?_)
      split_ifs with he
      · have hG' := hG
        rw [he] at hG'
        exact ep_le hH T τ (hG' (T, τ) (by simp)).2
      · exact le_refl _
    · have hne : ∀ T τ, ¬ run = hist ++ [(T, τ)] := by
        intro T τ he
        rw [he] at hG
        exact hGh (fun e he' => hG e (List.mem_append_left _ he'))
      calc _ = (0 : ℝ≥0∞) := by
            refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr (fun T => mul_eq_zero_of_right _
              (ENNReal.tsum_eq_zero.mpr (fun τ => if_neg (hne T τ)))))
        _ ≤ _ := zero_le

open Classical in
lemma bad_le (L : Learner (Fin (H + 1)) (Fin A) H) :
    ∀ K, (runLaw (comboLock0 H A) L K).toOuterMeasure {run | Bad run}
      ≤ (K : ℝ≥0∞) * ((A : ℝ≥0∞)⁻¹) ^ H
  | 0 => by
    simp only [runLaw, PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq]
    rw [if_neg]
    · exact zero_le
    · rintro ⟨-, e, he, -⟩
      simp at he
  | K + 1 => by
    rw [runLaw, PMF.toOuterMeasure_bind_apply]
    set c : ℝ≥0∞ := ((A : ℝ≥0∞)⁻¹) ^ H with hc
    have key : ∀ hist, ((L hist).bind fun T => (episodeLaw (comboLock0 H A) T).map
        fun τ => hist ++ [(T, τ)]).toOuterMeasure {run | Bad run}
          ≤ (if Bad hist then 1 else 0) + c := by
      intro hist
      by_cases hb : Bad hist
      · rw [if_pos hb]
        exact le_trans (outer_le_one _ _) le_self_add
      · rw [if_neg hb, zero_add]
        refine bind_outer_le _ _ _ _ (fun T => ?_)
        rw [PMF.toOuterMeasure_map_apply]
        by_cases hT : IsAdmissible (comboLock0 H A) T
        · refine le_trans (measure_mono ?_) (ep0_Z_le T hT)
          intro τ hτ
          obtain ⟨hadm, e, he, hz⟩ := hτ
          rcases List.mem_append.1 he with he | he
          · exact absurd ⟨fun e' he' => hadm e' (List.mem_append_left _ he'), e, he, hz⟩ hb
          · simp only [List.mem_singleton] at he
            rw [he] at hz
            exact hz
        · refine le_of_le_of_eq (measure_mono (t := (∅ : Set (Traj (Fin (H + 1)) (Fin A)))) ?_)
            measure_empty |>.trans zero_le
          intro τ hτ
          exact hT (hτ.1 (T, τ) (by simp))
    calc ∑' hist, runLaw (comboLock0 H A) L K hist * ((L hist).bind fun T =>
          (episodeLaw (comboLock0 H A) T).map fun τ => hist ++ [(T, τ)]).toOuterMeasure
            {run | Bad run}
        ≤ ∑' hist, runLaw (comboLock0 H A) L K hist * ((if Bad hist then 1 else 0) + c) :=
          ENNReal.tsum_le_tsum (fun hist => mul_le_mul_right (key hist) _)
      _ = (runLaw (comboLock0 H A) L K).toOuterMeasure {run | Bad run} + c := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            PMF.toOuterMeasure_apply]
          congr 1
          refine tsum_congr (fun hist => ?_)
          by_cases hb : Bad hist
          · simp [hb]
          · simp [hb]
      _ ≤ (K : ℝ≥0∞) * c + c := add_le_add (bad_le L K) (le_refl _)
      _ = ((K + 1 : ℕ) : ℝ≥0∞) * c := by push_cast; ring

lemma pM_ne (x : Fin (H + 1)) (a : Fin A) (hc : ¬ (1 ≤ x.val ∧ x.val < H ∧ a = 0)) :
    (comboLock H A).p x a = PMF.pure 0 := by
  simp only [comboLock, comboTrans]
  rw [dif_neg hc]

lemma pM_zero (x : Fin (H + 1)) (h1 : 1 ≤ x.val) (h2 : x.val < H) :
    (comboLock H A).p x 0 = PMF.pure ⟨x.val + 1, by omega⟩ := by
  simp only [comboLock, comboTrans]
  rw [dif_pos (by first | exact ⟨h1, h2, rfl⟩ | exact ⟨h1, h2, trivial⟩)]

lemma rbar_M_nonneg (x : Fin (H + 1)) (a : Fin A) : 0 ≤ (comboLock H A).rbar x a := by
  rw [rbar_M]; split_ifs <;> norm_num

lemma Vopt_M_nonneg : ∀ n (x : Fin (H + 1)), 0 ≤ Vopt (comboLock H A) n x
  | 0, _ => le_refl _
  | n + 1, x => by
    simp only [Vopt]
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (0 : Fin A)))
    exact add_nonneg (rbar_M_nonneg x 0)
      (Finset.sum_nonneg (fun x' _ => mul_nonneg ENNReal.toReal_nonneg (Vopt_M_nonneg n x')))

lemma Vopt_M_ge : ∀ n (x : Fin (H + 1)), 1 ≤ x.val → H + 1 ≤ x.val + n →
    1 ≤ Vopt (comboLock H A) n x
  | 0, x, _, h2 => absurd x.isLt (by omega)
  | n + 1, x, h1, h2 => by
    simp only [Vopt]
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (0 : Fin A)))
    by_cases hxH : x.val = H
    · rw [rbar_M, if_pos ⟨hxH, rfl⟩]
      have := Finset.sum_nonneg (fun x' (_ : x' ∈ Finset.univ) =>
        mul_nonneg (ENNReal.toReal_nonneg (a := (comboLock H A).p x 0 x'))
          (Vopt_M_nonneg (H := H) (A := A) n x'))
      linarith
    · have hlt : x.val < H := by have := x.isLt; omega
      rw [rbar_M, if_neg (fun h => hxH h.1), pM_zero x h1 hlt, sum_pure_mul]
      have := Vopt_M_ge n ⟨x.val + 1, by omega⟩ (show 1 ≤ x.val + 1 by omega)
        (show H + 1 ≤ x.val + 1 + n by omega)
      linarith

lemma Vstar_M_ge (hH : 1 ≤ H) : 1 ≤ Vstar (comboLock H A) H := by
  unfold Vstar
  show 1 ≤ ∑ x, ((PMF.pure (1 : Fin (H + 1))) x).toReal * Vopt (comboLock H A) H x
  rw [sum_pure_mul]
  have h1 : ((1 : Fin (H + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  exact Vopt_M_ge H 1 (by omega) (by omega)

lemma Vunif_M_nonneg (T : Supervisor (Fin (H + 1)) (Fin A) H) :
    ∀ n h x, 0 ≤ Vunif (comboLock H A) T n h x
  | 0, _, _ => le_refl _
  | n + 1, h, x => by
    simp only [Vunif]
    exact Finset.sum_nonneg (fun a _ => mul_nonneg ENNReal.toReal_nonneg
      (add_nonneg (rbar_M_nonneg x a) (Finset.sum_nonneg (fun x' _ =>
        mul_nonneg ENNReal.toReal_nonneg (Vunif_M_nonneg T n (h + 1) x')))))

lemma Vunif_M_le (hH : 0 < H) (T : Supervisor (Fin (H + 1)) (Fin A) H)
    (hU : ∀ h x a, h < H → unifPlaus T h x a = (A : ℝ≥0∞)⁻¹) :
    ∀ n h (x : Fin (H + 1)), h + n ≤ H →
      Vunif (comboLock H A) T n h x ≤ if x.val = 0 then 0 else (A : ℝ)⁻¹
  | 0, h, x, _ => by
    simp only [Vunif]
    split_ifs <;> simp
  | n + 1, h, x, hn => by
    have hAinv : (A : ℝ)⁻¹ ≤ 1 := by
      have hA1 : (1 : ℝ) ≤ A := by
        have := NeZero.ne A
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
      exact inv_le_one_of_one_le₀ hA1
    have hIH := fun x' => Vunif_M_le hH T hU n (h + 1) x' (by omega)
    have hterm : ∀ a, (comboLock H A).rbar x a + ∑ x', ((comboLock H A).p x a x').toReal *
        Vunif (comboLock H A) T n (h + 1) x' ≤ if (x.val ≠ 0 ∧ a = 0) then 1 else 0 := by
      intro a
      by_cases hc : 1 ≤ x.val ∧ x.val < H ∧ a = 0
      · rw [rbar_M, if_neg (by omega), if_pos ⟨by omega, hc.2.2⟩]
        have hs : ∑ x', ((comboLock H A).p x a x').toReal * Vunif (comboLock H A) T n (h + 1) x'
            ≤ ∑ x', ((comboLock H A).p x a x').toReal * (A : ℝ)⁻¹ :=
          Finset.sum_le_sum (fun x' _ => mul_le_mul_of_nonneg_left
            (le_trans (hIH x') (by split_ifs <;> simp)) ENNReal.toReal_nonneg)
        rw [← Finset.sum_mul, pmf_sum_toReal, one_mul] at hs
        linarith
      · rw [pM_ne x a hc, sum_pure_mul]
        have h0 := hIH 0
        rw [if_pos (by simp)] at h0
        by_cases hxa : x.val ≠ 0 ∧ a = 0
        · rw [if_pos hxa, rbar_M]
          split_ifs <;> linarith
        · rw [if_neg hxa, rbar_M, if_neg]
          · linarith
          · rintro ⟨h1, h2⟩
            exact hxa ⟨by omega, h2⟩
    have hU' : ∀ a, unifPlaus T h x a = (A : ℝ≥0∞)⁻¹ := fun a => hU h x a (by omega)
    simp only [Vunif]
    refine le_trans (Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (hterm a) ENNReal.toReal_nonneg)) (le_of_eq ?_)
    simp only [hU', ENNReal.toReal_inv, ENNReal.toReal_natCast]
    by_cases hx : x.val = 0 <;> simp [hx]

lemma valueUnif_M_le (hH : 0 < H) (T : Supervisor (Fin (H + 1)) (Fin A) H)
    (hT : IsAdmissible (comboLock0 H A) T) : valueUnif (comboLock H A) T ≤ (A : ℝ)⁻¹ := by
  unfold valueUnif
  show ∑ x, ((PMF.pure (1 : Fin (H + 1))) x).toReal * Vunif (comboLock H A) T H 0 x ≤ _
  rw [sum_pure_mul]
  refine le_trans (Vunif_M_le hH T (fun h x a hh => adm_unif T hT h hh x a) H 0 1 (by omega)) ?_
  split_ifs <;> simp

open Classical in
theorem main (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (hA : 2 ≤ A) :
    ∃ M : Instance (Fin (H + 1)) (Fin A),
      ∀ (L : Learner (Fin (H + 1)) (Fin A) H) (K : ℕ),
        UniformlyAdmissible L K → (K : ℝ) ≤ (A : ℝ) ^ H / 4 →
          (K : ℝ) / 8 ≤ expRegret M L K := by
  refine ⟨comboLock H A, fun L K hUA hK => ?_⟩
  have hH0 : 0 < H := by omega
  have hC1 : 1 ≤ Vstar (comboLock H A) H := Vstar_M_ge hH
  have hAinv : (A : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num
    exact_mod_cast hA
  have hterm_nonneg : ∀ e : Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A),
      0 ≤ Vstar (comboLock H A) H - valueUnif (comboLock H A) e.1 :=
    fun e => sub_nonneg.2 (valueUnif_le_Vstar _ _)
  have hterm_le : ∀ e : Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A),
      Vstar (comboLock H A) H - valueUnif (comboLock H A) e.1 ≤ Vstar (comboLock H A) H := by
    intro e
    have : 0 ≤ valueUnif (comboLock H A) e.1 := Finset.sum_nonneg (fun x _ =>
      mul_nonneg ENNReal.toReal_nonneg (Vunif_M_nonneg _ _ _ _))
    linarith
  have hreg_nonneg : ∀ run : List (Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A)),
      0 ≤ regret (comboLock H A) run := by
    intro run
    have := list_sum_ge (fun e : Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A)
      => Vstar (comboLock H A) H - valueUnif (comboLock H A) e.1) 0 run (fun e _ => hterm_nonneg e)
    rw [mul_zero] at this
    exact this
  have hreg_le : ∀ run : List (Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A)),
      run.length = K → regret (comboLock H A) run ≤ K * Vstar (comboLock H A) H := by
    intro run hl
    have := list_sum_le (fun e : Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A)
      => Vstar (comboLock H A) H - valueUnif (comboLock H A) e.1) _ run (fun e _ => hterm_le e)
    rw [hl] at this
    exact this
  have hreg_good : ∀ run : List (Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A)),
      run.length = K → Good run → (K : ℝ) / 2 ≤ regret (comboLock H A) run := by
    intro run hl hG
    have := list_sum_ge (fun e : Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A)
      => Vstar (comboLock H A) H - valueUnif (comboLock H A) e.1) (1 / 2) run
      (fun e he => by have := valueUnif_M_le hH0 e.1 (hG e he).1; linarith)
    rw [hl] at this
    unfold regret
    linarith
  set P := runLaw (comboLock H A) L K with hP
  set P0 := runLaw (comboLock0 H A) L K with hP0
  have hPs : Summable (fun run => (P run).toReal) :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  let g : List (Supervisor (Fin (H + 1)) (Fin A) H × Traj (Fin (H + 1)) (Fin A)) → ℝ :=
    fun run => if Good run then (K : ℝ) / 2 else 0
  have hle : ∀ run, (P run).toReal * g run ≤ (P run).toReal * regret (comboLock H A) run := by
    intro run
    by_cases h0 : P run = 0
    · simp [h0]
    have hl := runLaw_length _ L K run h0
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    by_cases hG : Good run
    · simp only [g, if_pos hG]; exact hreg_good run hl hG
    · simp only [g, if_neg hG]; exact hreg_nonneg run
  have hs1 : Summable (fun run => (P run).toReal * regret (comboLock H A) run) := by
    refine Summable.of_nonneg_of_le (fun run => mul_nonneg ENNReal.toReal_nonneg (hreg_nonneg run))
      (fun run => ?_) (hPs.mul_right ((K : ℝ) * Vstar (comboLock H A) H))
    by_cases h0 : P run = 0
    · simp [h0]
    exact mul_le_mul_of_nonneg_left (hreg_le run (runLaw_length _ L K run h0))
      ENNReal.toReal_nonneg
  have hs2 : Summable (fun run => (P run).toReal * g run) := by
    refine Summable.of_nonneg_of_le (fun run => mul_nonneg ENNReal.toReal_nonneg ?_)
      (fun run => ?_) (hPs.mul_right ((K : ℝ) / 2))
    · simp only [g]; split_ifs <;> positivity
    · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      simp only [g]
      split_ifs
      · exact le_rfl
      · positivity
  have hsum_g : ∑' run, (P run).toReal * g run
      = (K : ℝ) / 2 * (P.toOuterMeasure {run | Good run}).toReal := by
    rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq (fun run =>
      ne_top_of_le_ne_top (PMF.apply_ne_top P run) (Set.indicator_le_self _ _ run)),
      ← tsum_mul_left]
    refine tsum_congr (fun run => ?_)
    by_cases hG : Good run
    · rw [Set.indicator_of_mem (show run ∈ {r | Good r} from hG)]
      simp only [g, if_pos hG]
      ring
    · rw [Set.indicator_of_notMem (show run ∉ {r | Good r} from hG)]
      simp [g, hG]
  have hPG : P0.toOuterMeasure {run | Good run} ≤ P.toOuterMeasure {run | Good run} := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine ENNReal.tsum_le_tsum (fun run => ?_)
    by_cases hG : Good run
    · rw [Set.indicator_of_mem (show run ∈ {r | Good r} from hG),
        Set.indicator_of_mem (show run ∈ {r | Good r} from hG)]
      exact run_le hH0 L K run hG
    · rw [Set.indicator_of_notMem (show run ∉ {r | Good r} from hG),
        Set.indicator_of_notMem (show run ∉ {r | Good r} from hG)]
  have hcover : P0.toOuterMeasure {run | ∀ k < K, admEvent (comboLock0 H A) k run}
      ≤ P0.toOuterMeasure ({run | Good run} ∪ {run | Bad run}) := by
    refine PMF.toOuterMeasure_mono _ ?_
    rintro run ⟨hadm, hsupp⟩
    have hl := runLaw_length _ L K run ((PMF.mem_support_iff _ _).1 hsupp)
    have hA' : ∀ e ∈ run, IsAdmissible (comboLock0 H A) e.1 := by
      intro e he
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      obtain ⟨e', he', hadm'⟩ := hadm i (by omega)
      rw [List.getElem?_eq_getElem hi] at he'
      rw [Option.some.inj he']
      exact hadm'
    by_cases hz : ∃ e ∈ run, Zp e.2
    · exact Or.inr ⟨hA', hz⟩
    · left
      intro e he
      exact ⟨hA' e he, fun h => hz ⟨e, he, h⟩⟩
  have hmain : (1 / 2 : ℝ≥0∞) ≤ P0.toOuterMeasure {run | Good run}
      + (K : ℝ≥0∞) * ((A : ℝ≥0∞)⁻¹) ^ H :=
    (hUA (comboLock0 H A)).trans (hcover.trans ((measure_union_le _ _).trans
      (add_le_add (le_refl _) (bad_le L K))))
  have hfin1 : P0.toOuterMeasure {run | Good run} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (outer_le_one _ _)
  have hfin2 : (K : ℝ≥0∞) * ((A : ℝ≥0∞)⁻¹) ^ H ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top K)
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (by exact_mod_cast (NeZero.ne A))))
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩) hmain
  rw [ENNReal.toReal_add hfin1 hfin2] at hreal
  have hKc : ((K : ℝ≥0∞) * ((A : ℝ≥0∞)⁻¹) ^ H).toReal = (K : ℝ) / (A : ℝ) ^ H := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, inv_pow, div_eq_mul_inv]
  have hhalf : ((1 / 2 : ℝ≥0∞)).toReal = 1 / 2 := by
    rw [ENNReal.toReal_div]; simp
  rw [hKc, hhalf] at hreal
  have hAH : (0 : ℝ) < (A : ℝ) ^ H := pow_pos (by exact_mod_cast (show 0 < A by omega)) _
  have hKA : (K : ℝ) / (A : ℝ) ^ H ≤ 1 / 4 := by
    rw [div_le_iff₀ hAH]; linarith
  have hP0G : 1 / 4 ≤ (P0.toOuterMeasure {run | Good run}).toReal := by linarith
  have hPG' : (P0.toOuterMeasure {run | Good run}).toReal
      ≤ (P.toOuterMeasure {run | Good run}).toReal :=
    ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (outer_le_one _ _)) hPG
  have hK0 : (0 : ℝ) ≤ (K : ℝ) / 2 := by positivity
  calc (K : ℝ) / 8 ≤ (K : ℝ) / 2 * (P.toOuterMeasure {run | Good run}).toReal := by nlinarith
    _ = ∑' run, (P run).toReal * g run := hsum_g.symm
    _ ≤ ∑' run, (P run).toReal * regret (comboLock H A) run := Summable.tsum_le_tsum hle hs2 hs1
    _ = expRegret (comboLock H A) L K := rfl

end ElimLBSol

open CorruptRobustRL.ElimLB in
theorem solution (H A : ℕ) [NeZero A] (hH : 1 ≤ H) (hA : 2 ≤ A) :
    ∃ M : Instance (Fin (H + 1)) (Fin A),
      ∀ (L : Learner (Fin (H + 1)) (Fin A) H) (K : ℕ),
        UniformlyAdmissible L K → (K : ℝ) ≤ (A : ℝ) ^ H / 4 →
          (K : ℝ) / 8 ≤ expRegret M L K := by
  exact ElimLBSol.main H A hH hA
