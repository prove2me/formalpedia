-- Prove2me | solution 1 for ChenGallegoPricing.ABE.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T06:05:44.34241+00:00
-- url     : https://prove2.me/submissions/54eecfd2-fe5b-475d-94a6-93e4e0b3124c

import Mathlib
import Definitions.Def_ChenGallegoPricing_ABE_Geometry
import Definitions.Def_ChenGallegoPricing_ABE_Model
import Definitions.Def_ChenGallegoPricing_ABE_Algorithm
import Definitions.Def_ChenGallegoPricing_ABE_Process

open MeasureTheory

namespace S226N_8068ef5d
open ChenGallegoPricing.ABE

noncomputable def Rf (p : Price) : ℝ := (p : ℝ) * (1 - (p : ℝ) / 2)

def one : Price := ⟨1, by norm_num, le_rfl⟩

lemma Rf_gap (p : Price) : Rf one - Rf p = (1 - (p : ℝ)) ^ 2 / 2 := by
  simp only [Rf, one]; ring

lemma Rf_max (q : Price) : Rf q ≤ Rf one := by
  have := Rf_gap q; nlinarith [sq_nonneg (1 - (q : ℝ))]

lemma Rf_uniq (p : Price) (hp : ∀ q, Rf q ≤ Rf p) : p = one := by
  have h1 := hp one
  have h2 := Rf_gap p
  have : (1 - (p : ℝ)) ^ 2 = 0 := by nlinarith [sq_nonneg (1 - (p : ℝ))]
  apply Subtype.ext
  simp only [one]
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

lemma opt_eq : optimizer Rf = one := by
  unfold optimizer
  have hex : ∃ p, ∀ q, Rf q ≤ Rf p := ⟨one, Rf_max⟩
  rw [dif_pos hex]
  exact Rf_uniq _ hex.choose_spec

noncomputable def D : Demand 1 := fun xp => ⟨1 - (xp.2 : ℝ) / 2, by
  constructor <;> nlinarith [xp.2.2.1, xp.2.2.2]⟩

lemma rev_eq (x : Ctx 1) : revenue D x = Rf := rfl

lemma D_meas : Measurable D := by
  apply Continuous.measurable
  apply Continuous.subtype_mk
  exact continuous_const.sub ((continuous_subtype_val.comp continuous_snd).div_const _)

def x0 : Ctx 1 := ⟨0, fun i => by simp⟩

noncomputable def μ : Measure (Ctx 1) := Measure.dirac x0

instance : IsProbabilityMeasure μ := by unfold μ; infer_instance

open Classical in
noncomputable def ν (B : Set (Ctx 1)) : Measure (Ctx 1) :=
  if x0 ∈ B then Measure.dirac x0 else if h : B.Nonempty then Measure.dirac h.some
  else Measure.dirac x0

lemma ν_dirac (B : Set (Ctx 1)) : ∃ y, ν B = Measure.dirac y := by
  unfold ν; split_ifs <;> exact ⟨_, rfl⟩

lemma bin_eq (B : Set (Ctx 1)) : binRevenue D ν B = Rf := by
  funext p
  obtain ⟨y, hy⟩ := ν_dirac B
  simp [binRevenue, hy, rev_eq]

lemma binLaw : IsBinLaw μ ν := by
  refine ⟨fun B hB => ⟨?_, ?_, ?_⟩, fun x => ?_⟩
  · obtain ⟨y, hy⟩ := ν_dirac B; rw [hy]; infer_instance
  · have hm : MeasurableSet Bᶜ := hB.2.1.compl
    unfold ν
    split_ifs with h1 h2
    · rw [Measure.dirac_apply' _ hm]; simp [h1]
    · rw [Measure.dirac_apply' _ hm]; simp [h2.some_mem]
    · exact absurd hB.1 h2
  · intro hμ
    have hm : MeasurableSet B := hB.2.1
    have h1 : x0 ∈ B := by
      by_contra h; apply hμ; simp [μ, Measure.dirac_apply' _ hm, h]
    classical
    simp [ν, h1, μ, Measure.dirac_apply' _ hm, restrict_dirac' hm]
  · unfold ν
    split_ifs with h1 h2
    · rw [Set.mem_singleton_iff.mp h1]
    · rw [Set.mem_singleton_iff.mp h2.some_mem]
    · exact absurd (Set.singleton_nonempty x) h2

lemma A2 : Assumption2 D 1 := by
  refine ⟨fun x y p => ?_, fun x p q => ?_⟩
  · simp [rev_eq]
  · rw [rev_eq, one_mul]
    have hp := p.2; have hq := q.2
    have : Rf p - Rf q = ((p:ℝ) - q) * (1 - ((p:ℝ) + q) / 2) := by simp only [Rf]; ring
    rw [this, abs_mul]
    have : |1 - ((p:ℝ) + q) / 2| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [hp.1, hp.2, hq.1, hq.2]
    nlinarith [abs_nonneg ((p:ℝ) - q)]

lemma A3 : Assumption3 D ν (1/2) (1/2) 1 := by
  intro B hB
  have hbo : binOptimalPrice D ν B = one := by
    unfold binOptimalPrice; rw [bin_eq]; exact opt_eq
  have hop : ∀ x, optimalPrice D x = one := fun x => by
    unfold optimalPrice; rw [rev_eq]; exact opt_eq
  have himg : (fun x => (optimalPrice D x : ℝ)) '' B = {1} := by
    simp only [hop]; exact hB.1.image_const _
  rw [bin_eq, hbo, himg, csInf_singleton, csSup_singleton]
  refine ⟨⟨one, Rf_max, fun p hp => Rf_uniq p hp⟩, fun p => ?_, ?_, ?_⟩
  · rw [Rf_gap]; simp only [one]; constructor <;> nlinarith
  · simp [one]
  · simp only [sub_self, one_mul]; exact Metric.diam_nonneg

noncomputable def tie : TieRule 1 := fun _ _ => 0
noncomputable def comp : Policy 1 := fun _ _ => one

lemma maxLevel_one : maxLevel 1 1 = 0 := by simp [maxLevel]

def Inv (s : State 1) : Prop := ∀ c, (s.data c).lower = 0 ∧ (s.data c).upper = 1

lemma upd_inv (M₂ : ℝ) (h : History 1) (x : Ctx 1) (z : ℝ) (s : State 1) (hs : Inv s) :
    Inv (update 1 M₂ tie h x z s) := by
  unfold update
  simp only [maxLevel_one, Nat.not_lt_zero, if_false]
  intro c
  by_cases hc : c = locate s x
  · subst hc; simp [hs _]
  · simp [Function.update_of_ne hc, hs c]

lemma fold_inv (M₂ : ℝ) : ∀ (l : History 1) (acc : State 1 × History 1), Inv acc.1 →
    Inv (l.foldl (fun acc o =>
    (update 1 M₂ tie acc.2 o.1 o.2.2 acc.1, acc.2 ++ [(o.1, o.2.1, o.2.2)])) acc).1 := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons o l ih => intro acc h; exact ih _ (upd_inv _ _ _ _ _ h)

lemma half : (asPrice ((0 + 1) / 2) : ℝ) = 1 / 2 := by
  simp [asPrice]; norm_num

lemma pol_eq (M₂ : ℝ) (h : History 1) (x : Ctx 1) :
    abePolicy 1 M₂ tie comp h x = asPrice ((0 + 1) / 2) := by
  have hinv : Inv (stateAfter 1 M₂ tie h) :=
    fold_inv M₂ h _ (fun c => ⟨rfl, rfl⟩)
  unfold abePolicy quote
  simp only [maxLevel_one, Nat.not_lt_zero, if_false]
  rw [(hinv _).1, (hinv _).2]

instance : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) := ⟨by simp⟩

end S226N_8068ef5d

open ChenGallegoPricing.ABE S226N_8068ef5d in
theorem solution : ¬ (∀ (d : ℕ)
    (hd : 0 < d)
    (M₁ M₂ M₃ M₄ : ℝ)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃) (hM₄ : 0 < M₄),
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Demand d), Measurable D →
      ∀ (μ : Measure (Ctx d)) [IsProbabilityMeasure μ]
        (ν : Set (Ctx d) → Measure (Ctx d)),
      IsBinLaw μ ν → Assumption2 D M₁ → Assumption3 D ν M₂ M₃ M₄ →
      ∀ T : ℕ, 0 < T → ∀ (tie : TieRule d) (completion : Policy d),
        IsAdmissibleABE T M₂ tie completion →
        regret D μ (abePolicy T M₂ tie completion) T ≤
          C * (T : ℝ) ^ (((d : ℝ) + 2) / ((d : ℝ) + 4)) * (Real.log T) ^ 2) := by
  intro H
  obtain ⟨C, -, hC⟩ := H 1 one_pos 1 (1/2) (1/2) 1 one_pos (by norm_num) (by norm_num) one_pos
  have hadm : IsAdmissibleABE 1 (1/2) tie comp := by
    refine ⟨fun n => measurable_const, fun n => measurable_const, fun n => ?_, ?_⟩
    · have : (fun hx : (Fin n → Observation 1) × Ctx 1 =>
          abePolicy 1 (1/2) tie comp (List.ofFn hx.1) hx.2) = fun _ => asPrice ((0 + 1) / 2) :=
        funext fun hx => pol_eq _ _ _
      rw [this]; exact measurable_const
    · intro h x
      simp only [maxLevel_one, Nat.not_lt_zero, false_imp_iff, implies_true]
  have := hC D D_meas μ ν binLaw A2 A3 1 one_pos tie comp hadm
  have hreg : regret D μ (abePolicy 1 (1/2) tie comp) 1 = 1 / 8 := by
    unfold regret
    have : (fun w : Fin 1 → Draw 1 => ((play D (abePolicy 1 (1/2) tie comp) (List.ofFn w)).map
        (fun o => optimalRevenue D o.1 - revenue D o.1 o.2.1)).sum) = fun _ => 1 / 8 := by
      funext w
      simp only [List.ofFn_succ, List.ofFn_zero, play, List.foldl, List.nil_append,
        List.map, List.sum_cons, List.sum_nil, add_zero, feedback]
      rw [pol_eq, optimalRevenue, optimalPrice, rev_eq, opt_eq]
      simp only [Rf, one, half]; norm_num
    rw [this, integral_const]
    simp [drawLaw]
  rw [hreg] at this
  simp at this
  norm_num at this
