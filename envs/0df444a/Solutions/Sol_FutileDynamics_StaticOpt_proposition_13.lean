-- Prove2me | solution 1 for FutileDynamics.StaticOpt.proposition_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:24:31.67887+00:00
-- url     : https://prove2.me/submissions/66171040-94fe-40f1-b592-e3d6fbf7d7a3

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model
open MeasureTheory FutileDynamics.StaticOpt
open MeasureTheory FutileDynamics.StaticOpt

/-- `|PrincipalUtility| ≤ T·B` against a probability distribution. -/
lemma futileAux_pu_abs {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (B : ℝ) (hB : ∀ θ ω, |G.u θ ω| ≤ B ∧ |G.v θ ω| ≤ B)
    (F : Measure Θ) [IsProbabilityMeasure F] (T : ℕ) (A : DynMech Θ Ω)
    (σ : Strategy Θ Ω A.M0 A.M) : |principalUtility G A σ F T| ≤ T * B := by
  have : IsProbabilityMeasure (noiseLaw F T) := by unfold noiseLaw; infer_instance
  unfold principalUtility
  have h := norm_integral_le_of_norm_le_const (μ := noiseLaw F T)
    (f := fun ξ => ∑ k : Fin T, G.u (ξ.1 k) (outcome G A σ F T ξ k)) (C := T * B)
    (Filter.Eventually.of_forall fun ξ => by
      calc ‖∑ k : Fin T, G.u (ξ.1 k) (outcome G A σ F T ξ k)‖
          ≤ ∑ k : Fin T, ‖G.u (ξ.1 k) (outcome G A σ F T ξ k)‖ := norm_sum_le _ _
        _ ≤ ∑ _k : Fin T, B := Finset.sum_le_sum fun k _ => by
            rw [Real.norm_eq_abs]; exact (hB _ _).1
        _ = T * B := by simp)
  simp only [probReal_univ, mul_one] at h
  rwa [Real.norm_eq_abs] at h

/-- `|OPT(F,T)| ≤ T·B`, and every IC mechanism's principal utility is at most `OPT(F,T)`. -/
lemma futileAux_opt {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (B : ℝ) (hB : ∀ θ ω, |G.u θ ω| ≤ B ∧ |G.v θ ω| ≤ B) (hB0 : 0 ≤ B)
    (F : Measure Θ) [IsProbabilityMeasure F] (T : ℕ) :
    |OPT G F T| ≤ T * B ∧
      ∀ A : DynMech Θ Ω, IsIC G A T → principalUtility G A A.recom F T ≤ OPT G F T := by
  have hTB : (0 : ℝ) ≤ T * B := mul_nonneg (Nat.cast_nonneg _) hB0
  set S := {r : ℝ | ∃ A : DynMech Θ Ω, IsIC G A T ∧ r = principalUtility G A A.recom F T} with hS
  have hO : OPT G F T = sSup S := rfl
  have hbdd : BddAbove S := by
    refine ⟨T * B, ?_⟩
    rintro r ⟨A, -, rfl⟩
    exact (le_abs_self _).trans (futileAux_pu_abs G B hB F T A A.recom)
  have hle : ∀ A : DynMech Θ Ω, IsIC G A T → principalUtility G A A.recom F T ≤ OPT G F T :=
    fun A hA => le_csSup hbdd ⟨A, hA, rfl⟩
  refine ⟨?_, hle⟩
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [hO, he, Real.sSup_empty]; simpa using hTB
  · rw [abs_le]; constructor
    · obtain ⟨r, A, hA, rfl⟩ := hne
      have := hle A hA
      have := (abs_le.1 (futileAux_pu_abs G B hB F T A A.recom)).1
      linarith
    · rw [hO]; exact csSup_le hne (fun r ⟨A, _, hr⟩ => hr ▸
        (le_abs_self _).trans (futileAux_pu_abs G B hB F T A A.recom))

/-- `|Regret(A,F,T)| ≤ 2·T·B`. -/
lemma futileAux_regret_abs {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (B : ℝ) (hB : ∀ θ ω, |G.u θ ω| ≤ B ∧ |G.v θ ω| ≤ B) (hB0 : 0 ≤ B)
    (F : Measure Θ) [IsProbabilityMeasure F] (T : ℕ) (A : DynMech Θ Ω) :
    |regret G A F T| ≤ 2 * (T * B) := by
  unfold regret
  have h1 := (futileAux_opt G B hB hB0 F T).1
  have h2 := futileAux_pu_abs G B hB F T A A.recom
  rw [abs_le] at *
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma futileAux_regret_nonneg {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (B : ℝ) (hB : ∀ θ ω, |G.u θ ω| ≤ B ∧ |G.v θ ω| ≤ B) (hB0 : 0 ≤ B)
    (F : Measure Θ) [IsProbabilityMeasure F] (T : ℕ) (A : DynMech Θ Ω) (hA : IsIC G A T) :
    0 ≤ regret G A F T := by
  unfold regret
  have := (futileAux_opt G B hB hB0 F T).2 A hA
  linarith

lemma futileAux_B {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [Nonempty Θ] (G : Game Θ Ω) :
    ∃ B : ℝ, (∀ θ ω, |G.u θ ω| ≤ B ∧ |G.v θ ω| ≤ B) ∧ 0 ≤ B := by
  obtain ⟨B, hB⟩ := G.bdd
  exact ⟨B, hB, (abs_nonneg _).trans (hB (Classical.arbitrary Θ) G.noInt).1⟩

open Classical in
/-- Measurability of the play in the exogenous randomness, for a feasible strategy. -/
lemma futileAux_hist_meas {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (hσ : σ.Feasible) (F : Measure Θ) (T : ℕ) :
    ∀ k (hk : k ≤ T), Measurable (fun ξ : Noise Θ T => hist G A σ F T ξ k hk) := by
  intro k
  induction k with
  | zero =>
    intro hk
    simp only [hist]
    exact measurable_const
  | succ k ih =>
    intro hk
    have hp := ih (Nat.le_of_succ_le hk)
    set kk : Fin T := ⟨k, hk⟩
    have hm0 : Measurable (fun ξ : Noise Θ T => σ.s0 F ξ.2.1) :=
      hσ.1.comp (measurable_const.prodMk measurable_snd.fst)
    have hm : Measurable (fun ξ : Noise Θ T => σ.s k F (ξ.1 kk) (fun j => ξ.1 ⟨j, by omega⟩)
        (σ.s0 F ξ.2.1) (hist G A σ F T ξ k (Nat.le_of_succ_le hk)).1
        (hist G A σ F T ξ k (Nat.le_of_succ_le hk)).2 (ξ.2.2.1 kk)) := by
      refine (hσ.2 k).comp (f := fun ξ : Noise Θ T => (F, ξ.1 kk, (fun j : Fin k => ξ.1 ⟨j, by omega⟩),
        σ.s0 F ξ.2.1, (hist G A σ F T ξ k (Nat.le_of_succ_le hk)).1,
        (hist G A σ F T ξ k (Nat.le_of_succ_le hk)).2, ξ.2.2.1 kk)) ?_
      refine measurable_const.prodMk (((measurable_pi_apply kk).comp measurable_fst).prodMk
        ((measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp measurable_fst).prodMk
        (hm0.prodMk (hp.fst.prodMk (hp.snd.prodMk
        ((measurable_pi_apply kk).comp measurable_snd.snd.fst))))))
    have hω : Measurable (fun ξ : Noise Θ T =>
        if σ.s0 F ξ.2.1 = A.quit then G.noInt else A.rule k (σ.s k F (ξ.1 kk)
          (fun j => ξ.1 ⟨j, by omega⟩) (σ.s0 F ξ.2.1) (hist G A σ F T ξ k (Nat.le_of_succ_le hk)).1
          (hist G A σ F T ξ k (Nat.le_of_succ_le hk)).2 (ξ.2.2.1 kk)) (σ.s0 F ξ.2.1)
          (hist G A σ F T ξ k (Nat.le_of_succ_le hk)).1 (hist G A σ F T ξ k (Nat.le_of_succ_le hk)).2
          (ξ.2.2.2 kk)) := by
      refine Measurable.ite (hm0 (measurableSet_singleton A.quit)) measurable_const ?_
      exact (A.rule_meas k).comp (hm.prodMk (hm0.prodMk (hp.fst.prodMk (hp.snd.prodMk
        ((measurable_pi_apply kk).comp measurable_snd.snd.snd)))))
    simp only [hist]
    refine Measurable.prodMk ?_ ?_
    · refine measurable_pi_iff.mpr fun i => ?_
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]; exact hm
      · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply _).comp hp.fst
    · refine measurable_pi_iff.mpr fun i => ?_
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]; exact hω
      · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply _).comp hp.snd

/-- The null direct rule: always the no-interaction outcome. -/
def futileAux_d0 {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω) : DirectRule G :=
  ⟨fun _ _ => G.noInt, measurable_const, fun _ _ => rfl⟩

lemma futileAux_hist_null {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (σ : Strategy Θ Ω (repeatDirect G (futileAux_d0 G)).M0 (repeatDirect G (futileAux_d0 G)).M)
    (F : Measure Θ) (T : ℕ) (ξ : Noise Θ T) :
    ∀ k (hk : k ≤ T) (j : Fin k), (hist G (repeatDirect G (futileAux_d0 G)) σ F T ξ k hk).2 j = G.noInt := by
  intro k
  induction k with
  | zero => intro hk j; exact j.elim0
  | succ k ih =>
    intro hk j
    rw [hist]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]
      split_ifs <;> rfl
    · simp only [Fin.snoc_castSucc]
      exact ih _ i

lemma futileAux_d0_IC {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (T : ℕ) : IsIC G (repeatDirect G (futileAux_d0 G)) T := by
  have hzero : ∀ (σ : Strategy Θ Ω (repeatDirect G (futileAux_d0 G)).M0 (repeatDirect G (futileAux_d0 G)).M)
      (F : Measure Θ), agentUtility G (repeatDirect G (futileAux_d0 G)) σ F T = 0 := by
    intro σ F
    unfold agentUtility outcome
    simp [futileAux_hist_null, G.v_noInt]
  refine ⟨⟨?_, fun k => ?_⟩, fun F _ σ' _ => by rw [hzero, hzero]⟩
  · exact measurable_const
  · exact measurable_snd.fst.prodMk measurable_const

lemma futileAux_opt_nonneg {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    [Nonempty Θ] (G : Game Θ Ω) (F : Measure Θ) [IsProbabilityMeasure F] (T : ℕ) : 0 ≤ OPT G F T := by
  obtain ⟨B, hB, hB0⟩ := futileAux_B G
  have h := (futileAux_opt G B hB hB0 F T).2 _ (futileAux_d0_IC G T)
  have h0 : principalUtility G (repeatDirect G (futileAux_d0 G)) (repeatDirect G (futileAux_d0 G)).recom F T
      = 0 := by
    unfold principalUtility outcome
    simp [futileAux_hist_null, G.u_noInt]
  linarith

/-- The single-round outcome of a direct mechanism under truthful reporting. -/
lemma futileAux_outcome_one {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (d : DirectRule G) (F : Measure Θ) (ξ : Noise Θ 1) :
    outcome G (repeatDirect G d) (repeatDirect G d).recom F 1 ξ 0 = d.1 (ξ.1 0, true) (ξ.2.2.2 0) := by
  unfold outcome
  rw [hist]
  simp [repeatDirect]
  rfl

/-- `PrincipalUtility(S, F, 1) = ∫_Θ ∫_0^1 u(θ, π̃(θ, z)) dz dF(θ)`. -/
lemma futileAux_pu_one {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (d : DirectRule G) (F : Measure Θ) [IsProbabilityMeasure F] :
    principalUtility G (repeatDirect G d) (repeatDirect G d).recom F 1 =
      ∫ θ, ∫ z, G.u θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) ∂F := by
  obtain ⟨B, hB⟩ := G.bdd
  set φ : Θ → unitInterval → ℝ := fun θ z => G.u θ (d.1 (θ, true) z) with hφ
  have hφm : Measurable (Function.uncurry φ) := by
    have h1 : Measurable (fun p : Θ × unitInterval => d.1 (p.1, true) p.2) :=
      d.2.1.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    exact G.u_meas.comp (measurable_fst.prodMk h1)
  unfold principalUtility
  simp only [Fin.sum_univ_one, futileAux_outcome_one]
  unfold noiseLaw
  have hmeas : Measurable (fun ξ : Noise Θ 1 => φ (ξ.1 0) (ξ.2.2.2 0)) :=
    hφm.comp (g := Function.uncurry φ) (f := fun ξ : Noise Θ 1 => (ξ.1 0, ξ.2.2.2 0))
      (((measurable_pi_apply 0).comp measurable_fst).prodMk
      ((measurable_pi_apply 0).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  rw [integral_prod (f := fun ξ : Noise Θ 1 => φ (ξ.1 0) (ξ.2.2.2 0))]
  · have inner : ∀ x : Fin 1 → Θ,
        ∫ y, φ (x 0) (y.2.2 0) ∂((volume : Measure unitInterval).prod
          ((Measure.pi fun _ : Fin 1 => (volume : Measure unitInterval)).prod
            (Measure.pi fun _ : Fin 1 => (volume : Measure unitInterval)))) =
          ∫ z, φ (x 0) z ∂(volume : Measure unitInterval) := by
      intro x
      rw [integral_fun_snd (f := fun w : (Fin 1 → unitInterval) × (Fin 1 → unitInterval) =>
        φ (x 0) (w.2 0))]
      rw [integral_fun_snd (f := fun w : Fin 1 → unitInterval => φ (x 0) (w 0))]
      simp only [probReal_univ, one_smul]
      exact (measurePreserving_funUnique (volume : Measure unitInterval) (Fin 1)).integral_comp'
        (fun z => φ (x 0) z)
    simp_rw [inner]
    exact (measurePreserving_funUnique F (Fin 1)).integral_comp'
      (fun θ => ∫ z, φ θ z ∂(volume : Measure unitInterval))
  · refine Integrable.of_bound hmeas.aestronglyMeasurable B (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]; exact (hB _ _).1


/-- Past noise of rounds `1, …, k`: shocks, agent uniforms, principal uniforms. -/
abbrev FPast (Θ : Type) (k : ℕ) := (Fin k → Θ) × (Fin k → unitInterval) × (Fin k → unitInterval)

open Classical in
/-- The play of the first `n ≤ k` rounds, driven by a given Round 0 report `m₀` and past noise `π`. -/
noncomputable def futileAux_histM {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (m0 : A.M0) (k : ℕ)
    (π : FPast Θ k) : (n : ℕ) → n ≤ k → ((j : Fin n) → A.M j) × (Fin n → Ω)
  | 0, _ => (fun j => j.elim0, fun j => j.elim0)
  | n + 1, hn =>
    let p := futileAux_histM G A σ F m0 k π n (Nat.le_of_succ_le hn)
    let kk : Fin k := ⟨n, hn⟩
    let m : A.M n := σ.s n F (π.1 kk) (fun j => π.1 ⟨j, by omega⟩) m0 p.1 p.2 (π.2.1 kk)
    let ω : Ω := if m0 = A.quit then G.noInt else A.rule n m m0 p.1 p.2 (π.2.2 kk)
    (Fin.snoc (α := fun i : Fin (n + 1) => A.M i) p.1 m, Fin.snoc p.2 ω)

/-- Restriction of the noise to the first `k` rounds. -/
def futileAux_restrict {Θ : Type} {T : ℕ} (k : ℕ) (hk : k ≤ T) (ξ : Noise Θ T) : FPast Θ k :=
  (fun j => ξ.1 ⟨j, by omega⟩, fun j => ξ.2.2.1 ⟨j, by omega⟩, fun j => ξ.2.2.2 ⟨j, by omega⟩)

lemma futileAux_hist_eq_histM {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (T : ℕ) (ξ : Noise Θ T) (k : ℕ)
    (hk : k ≤ T) : ∀ n (hn : n ≤ k), hist G A σ F T ξ n (hn.trans hk) =
      futileAux_histM G A σ F (σ.s0 F ξ.2.1) k (futileAux_restrict k hk ξ) n hn := by
  intro n
  induction n with
  | zero => intro hn; simp only [hist, futileAux_histM]
  | succ n ih =>
    intro hn
    rw [hist, futileAux_histM, ← ih (Nat.le_of_succ_le hn)]
    rfl

lemma futileAux_hist_prefix {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (T : ℕ) (ξ : Noise Θ T) (n : ℕ)
    (j : ℕ) (hj : j < n) : ∀ m (hnm : n ≤ m) (hm : m ≤ T),
      (hist G A σ F T ξ m hm).2 ⟨j, by omega⟩ = (hist G A σ F T ξ n (hnm.trans hm)).2 ⟨j, hj⟩ := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base => intro hm; rfl
  | succ m hnm ih =>
    intro hm
    rw [← ih (Nat.le_of_succ_le hm), hist]
    exact Fin.snoc_castSucc (α := fun _ => Ω) (i := ⟨j, by omega⟩) _ _

open Classical in
/-- The outcome of round `k + 1` as a function of the Round 0 report, the current shock, the past noise
and the current uniforms. -/
noncomputable def futileAux_roundOut {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (k : ℕ) (m0 : A.M0) (θc : Θ)
    (π : FPast Θ k) (yk zk : unitInterval) : Ω :=
  if m0 = A.quit then G.noInt else
    A.rule k (σ.s k F θc π.1 m0 (futileAux_histM G A σ F m0 k π k le_rfl).1
      (futileAux_histM G A σ F m0 k π k le_rfl).2 yk) m0 (futileAux_histM G A σ F m0 k π k le_rfl).1
      (futileAux_histM G A σ F m0 k π k le_rfl).2 zk

lemma futileAux_outcome_eq {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (F : Measure Θ) (T : ℕ) (ξ : Noise Θ T) (k : Fin T) :
    outcome G A σ F T ξ k = futileAux_roundOut G A σ F k (σ.s0 F ξ.2.1) (ξ.1 k)
      (futileAux_restrict k (le_of_lt k.2) ξ) (ξ.2.2.1 k) (ξ.2.2.2 k) := by
  unfold outcome
  have h1 := futileAux_hist_prefix G A σ F T ξ (k + 1) k (by omega) T (by omega) le_rfl
  rw [show (⟨(k : ℕ), _⟩ : Fin T) = k from rfl] at h1
  rw [h1, hist]
  have h2 := futileAux_hist_eq_histM G A σ F T ξ k (le_of_lt k.2) k le_rfl
  simp only [Fin.snoc_last]
  rw [show (⟨(k : ℕ), by omega⟩ : Fin (k + 1)) = Fin.last k from rfl]
  simp only [Fin.snoc_last]
  unfold futileAux_roundOut
  rw [← h2]
  rfl

open Classical in
/-- Joint measurability of the driven play in `(F, m₀, π)`. -/
lemma futileAux_histM_meas {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (hσ : σ.Feasible) (k : ℕ) :
    ∀ n (hn : n ≤ k), Measurable (fun q : Measure Θ × A.M0 × FPast Θ k =>
      futileAux_histM G A σ q.1 q.2.1 k q.2.2 n hn) := by
  intro n
  induction n with
  | zero =>
    intro hn
    simp only [futileAux_histM]
    exact measurable_const
  | succ n ih =>
    intro hn
    have hp := ih (Nat.le_of_succ_le hn)
    set kk : Fin k := ⟨n, hn⟩
    have hm : Measurable (fun q : Measure Θ × A.M0 × FPast Θ k => σ.s n q.1 (q.2.2.1 kk)
        (fun j => q.2.2.1 ⟨j, by omega⟩) q.2.1
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).1
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).2 (q.2.2.2.1 kk)) := by
      refine (hσ.2 n).comp (f := fun q : Measure Θ × A.M0 × FPast Θ k => (q.1, q.2.2.1 kk,
        (fun j : Fin n => q.2.2.1 ⟨j, by omega⟩), q.2.1,
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).1,
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).2, q.2.2.2.1 kk)) ?_
      refine measurable_fst.prodMk (((measurable_pi_apply kk).comp measurable_snd.snd.fst).prodMk
        ((measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp measurable_snd.snd.fst).prodMk
        (measurable_snd.fst.prodMk (hp.fst.prodMk (hp.snd.prodMk
        ((measurable_pi_apply kk).comp measurable_snd.snd.snd.fst))))))
    have hω : Measurable (fun q : Measure Θ × A.M0 × FPast Θ k =>
        if q.2.1 = A.quit then G.noInt else A.rule n (σ.s n q.1 (q.2.2.1 kk)
          (fun j => q.2.2.1 ⟨j, by omega⟩) q.2.1
          (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).1
          (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).2 (q.2.2.2.1 kk)) q.2.1
          (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).1
          (futileAux_histM G A σ q.1 q.2.1 k q.2.2 n (Nat.le_of_succ_le hn)).2 (q.2.2.2.2 kk)) := by
      refine Measurable.ite (measurable_snd.fst (measurableSet_singleton A.quit)) measurable_const ?_
      exact (A.rule_meas n).comp (hm.prodMk (measurable_snd.fst.prodMk (hp.fst.prodMk (hp.snd.prodMk
        ((measurable_pi_apply kk).comp measurable_snd.snd.snd.snd)))))
    simp only [futileAux_histM]
    refine Measurable.prodMk ?_ ?_
    · refine measurable_pi_iff.mpr fun i => ?_
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]; exact hm
      · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply _).comp hp.fst
    · refine measurable_pi_iff.mpr fun i => ?_
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]; exact hω
      · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply _).comp hp.snd

/-- Arguments of `futileAux_roundOut`. -/
abbrev RArg (Θ M0 : Type) [MeasurableSpace Θ] (k : ℕ) := Measure Θ × M0 × Θ × FPast Θ k × unitInterval × unitInterval

open Classical in
lemma futileAux_roundOut_meas {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M) (hσ : σ.Feasible) (k : ℕ) :
    Measurable (fun q : RArg Θ A.M0 k =>
      futileAux_roundOut G A σ q.1 k q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  have hf : Measurable (fun q : RArg Θ A.M0 k => (q.1, q.2.1, q.2.2.2.1)) := by fun_prop
  have hp := (futileAux_histM_meas G A σ hσ k k le_rfl).comp hf
  have hm : Measurable (fun q : RArg Θ A.M0 k =>
      σ.s k q.1 q.2.2.1 q.2.2.2.1.1 q.2.1 (futileAux_histM G A σ q.1 q.2.1 k q.2.2.2.1 k le_rfl).1
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2.2.1 k le_rfl).2 q.2.2.2.2.1) := by
    have h2 : Measurable (fun q : RArg Θ A.M0 k => (q.1, q.2.2.1, q.2.2.2.1.1, q.2.1,
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2.2.1 k le_rfl).1,
        (futileAux_histM G A σ q.1 q.2.1 k q.2.2.2.1 k le_rfl).2, q.2.2.2.2.1)) := by
      refine measurable_fst.prodMk (measurable_snd.snd.fst.prodMk
        (measurable_snd.snd.snd.fst.fst.prodMk (measurable_snd.fst.prodMk (hp.fst.prodMk
        (hp.snd.prodMk measurable_snd.snd.snd.snd.fst)))))
    exact (hσ.2 k).comp h2
  unfold futileAux_roundOut
  refine Measurable.ite (measurable_snd.fst (measurableSet_singleton A.quit)) measurable_const ?_
  exact (A.rule_meas k).comp (hm.prodMk (measurable_snd.fst.prodMk (hp.fst.prodMk (hp.snd.prodMk
    measurable_snd.snd.snd.snd.snd))))

section Rearrange
variable {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

lemma futileAux_mp_assoc (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa] [SFinite μb]
    [SFinite μc] : MeasurePreserving (fun p : (α × β) × γ => (p.1.1, (p.1.2, p.2)))
      ((μa.prod μb).prod μc) (μa.prod (μb.prod μc)) :=
  measurePreserving_prodAssoc μa μb μc

lemma futileAux_mp_assoc_symm (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa]
    [SFinite μb] [SFinite μc] : MeasurePreserving (fun p : α × (β × γ) => ((p.1, p.2.1), p.2.2))
      (μa.prod (μb.prod μc)) ((μa.prod μb).prod μc) :=
  (measurePreserving_prodAssoc μa μb μc).symm

lemma futileAux_mp_leftComm (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa]
    [SFinite μb] [SFinite μc] : MeasurePreserving (fun p : α × (β × γ) => (p.2.1, (p.1, p.2.2)))
      (μa.prod (μb.prod μc)) (μb.prod (μa.prod μc)) := by
  have h := (futileAux_mp_assoc μb μa μc).comp (((Measure.measurePreserving_swap (μ := μa) (ν := μb)).prod
    (MeasurePreserving.id μc)).comp (futileAux_mp_assoc_symm μa μb μc))
  exact h

lemma futileAux_mp_mid4 (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h := (futileAux_mp_assoc_symm μa μc (μb.prod μd)).comp
    (((MeasurePreserving.id μa).prod (futileAux_mp_leftComm μb μc μd)).comp
      (futileAux_mp_assoc μa μb (μc.prod μd)))
  exact h

end Rearrange

/-- Splitting off coordinate `k` and the coordinates before it. -/
lemma futileAux_splitAt {α : Type} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (T : ℕ)
    (k : Fin T) : MeasurePreserving (fun x : Fin T → α => (x k, fun j : Fin k => x ⟨j, by omega⟩))
      (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ : Fin k => μ)) := by
  classical
  let p : Fin T → Prop := fun i => i.val < k.val
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin T => μ) p
  let f : Fin k ≃ {i : Fin T // p i} :=
    { toFun := fun j => ⟨⟨j, by omega⟩, j.2⟩
      invFun := fun i => ⟨i.1, i.2⟩
      left_inv := fun j => rfl
      right_inv := fun i => rfl }
  have h2 := (measurePreserving_piCongrLeft (fun _ : {i : Fin T // p i} => μ) f).symm
  have h3 := measurePreserving_eval (fun _ : {i : Fin T // ¬ p i} => μ) ⟨k, lt_irrefl _⟩
  have h5 := (Measure.measurePreserving_swap).comp ((h2.prod h3).comp h1)
  convert h5 using 1
  funext x
  refine Prod.ext rfl ?_
  funext j
  simp [MeasurableEquiv.piCongrLeft, MeasurableEquiv.piEquivPiSubtypeProd, f]

/-- The law of the past noise of `k` rounds. -/
noncomputable def futileAux_W {Θ : Type} [MeasurableSpace Θ] (F : Measure Θ) (k : ℕ) : Measure (FPast Θ k) :=
  (Measure.pi fun _ : Fin k => F).prod ((Measure.pi fun _ : Fin k => (volume : Measure unitInterval)).prod
    (Measure.pi fun _ : Fin k => (volume : Measure unitInterval)))

/-- The canonical law of `(θ_k, y₀, past noise, y_k, z_k)`. -/
noncomputable def futileAux_Q {Θ : Type} [MeasurableSpace Θ] (F : Measure Θ) (k : ℕ) :
    Measure (Θ × unitInterval × FPast Θ k × unitInterval × unitInterval) :=
  F.prod ((volume : Measure unitInterval).prod ((futileAux_W F k).prod
    ((volume : Measure unitInterval).prod (volume : Measure unitInterval))))

instance futileAux_W_prob {Θ : Type} [MeasurableSpace Θ] (F : Measure Θ) [IsProbabilityMeasure F]
    (k : ℕ) : IsProbabilityMeasure (futileAux_W F k) := by unfold futileAux_W; infer_instance

lemma futileAux_mp_T {Θ : Type} [MeasurableSpace Θ] (F : Measure Θ) [IsProbabilityMeasure F] (T : ℕ)
    (k : Fin T) : MeasurePreserving (fun ξ : Noise Θ T => (ξ.1 k, (ξ.2.1,
      (futileAux_restrict k (le_of_lt k.2) ξ, (ξ.2.2.1 k, ξ.2.2.2 k))))) (noiseLaw F T) (futileAux_Q F k) := by
  set Lv := (volume : Measure unitInterval)
  set PF := Measure.pi fun _ : Fin k => F
  set PL := Measure.pi fun _ : Fin k => Lv
  have s0 := (futileAux_splitAt F T k).prod ((MeasurePreserving.id Lv).prod
    ((futileAux_splitAt Lv T k).prod (futileAux_splitAt Lv T k)))
  have r1 := futileAux_mp_assoc F PF (Lv.prod ((Lv.prod PL).prod (Lv.prod PL)))
  have r2 := (MeasurePreserving.id F).prod (futileAux_mp_leftComm PF Lv ((Lv.prod PL).prod (Lv.prod PL)))
  have r3 := (MeasurePreserving.id F).prod ((MeasurePreserving.id Lv).prod
    ((MeasurePreserving.id PF).prod (futileAux_mp_mid4 Lv PL Lv PL)))
  have r4 := (MeasurePreserving.id F).prod ((MeasurePreserving.id Lv).prod
    (futileAux_mp_leftComm PF (Lv.prod Lv) (PL.prod PL)))
  have r5 := (MeasurePreserving.id F).prod ((MeasurePreserving.id Lv).prod
    (Measure.measurePreserving_swap (μ := Lv.prod Lv) (ν := PF.prod (PL.prod PL))))
  have h := r5.comp (r4.comp (r3.comp (r2.comp (r1.comp s0))))
  exact h

lemma futileAux_mp_1 {Θ : Type} [MeasurableSpace Θ] (F : Measure Θ) [IsProbabilityMeasure F] (k : ℕ)
    (sp : unitInterval → FPast Θ k × unitInterval)
    (hs : MeasurePreserving sp (volume : Measure unitInterval) ((futileAux_W F k).prod volume)) :
    MeasurePreserving (fun ξ : Noise Θ 1 => (ξ.1 0, (ξ.2.1, ((sp (ξ.2.2.1 0)).1,
      ((sp (ξ.2.2.1 0)).2, ξ.2.2.2 0))))) (noiseLaw F 1) (futileAux_Q F k) := by
  set Lv := (volume : Measure unitInterval)
  have u0 := (measurePreserving_funUnique F (Fin 1)).prod ((MeasurePreserving.id Lv).prod
    ((measurePreserving_funUnique Lv (Fin 1)).prod (measurePreserving_funUnique Lv (Fin 1))))
  have u1 := (MeasurePreserving.id F).prod ((MeasurePreserving.id Lv).prod
    (hs.prod (MeasurePreserving.id Lv)))
  have u2 := (MeasurePreserving.id F).prod ((MeasurePreserving.id Lv).prod
    (futileAux_mp_assoc (futileAux_W F k) Lv Lv))
  have h := u2.comp (u1.comp u0)
  exact h

/-- A jointly measurable sampler: `samp F` pushes the uniform law to `F` for every probability `F`. -/
lemma futileAux_sampler (Θ : Type) [MeasurableSpace Θ] [StandardBorelSpace Θ] [Nonempty Θ] :
    ∃ samp : Measure Θ → unitInterval → Θ, Measurable (Function.uncurry samp) ∧
      ∀ F : Measure Θ, IsProbabilityMeasure F → (volume : Measure unitInterval).map (samp F) = F := by
  classical
  let θ0 : Θ := Classical.arbitrary Θ
  have hS : MeasurableSet {F : Measure Θ | F Set.univ = 1} :=
    Measure.measurable_coe MeasurableSet.univ (measurableSet_singleton 1)
  let κ : ProbabilityTheory.Kernel (Measure Θ) Θ :=
    ⟨fun F => if F Set.univ = 1 then F else Measure.dirac θ0,
      Measurable.ite hS measurable_id measurable_const⟩
  have hκ : ProbabilityTheory.IsMarkovKernel κ := by
    refine ⟨fun F => ?_⟩
    show IsProbabilityMeasure (if F Set.univ = 1 then F else Measure.dirac θ0)
    split_ifs with h
    · exact ⟨h⟩
    · infer_instance
  obtain ⟨f, hf, hfκ⟩ := κ.exists_measurable_map_eq_unitInterval
  refine ⟨f, hf, fun F hF => ?_⟩
  rw [hfκ F]
  show (if F Set.univ = 1 then F else Measure.dirac θ0) = F
  rw [if_pos hF.measure_univ]

lemma futileAux_pi_dirac {Θ : Type} [MeasurableSpace Θ] (T : ℕ) (θ : Θ) :
    Measure.pi (fun _ : Fin T => Measure.dirac θ) = Measure.dirac (fun _ : Fin T => θ) := by
  classical
  refine (Measure.pi_eq (μ := fun _ : Fin T => Measure.dirac θ) fun s hs => ?_)
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  by_cases h : ∀ i, θ ∈ s i
  · have h' : (fun _ : Fin T => θ) ∈ Set.univ.pi s := fun i _ => h i
    rw [Set.indicator_of_mem h']
    simp only [Pi.one_apply]
    symm
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Measure.dirac_apply' _ (hs i), Set.indicator_of_mem (h i)]
    rfl
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    have h' : (fun _ : Fin T => θ) ∉ Set.univ.pi s := fun hm => hi (hm i (Set.mem_univ _))
    rw [Set.indicator_of_notMem h']
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [Measure.dirac_apply' _ (hs i), Set.indicator_of_notMem hi]

/-- The law of the uniforms of a `T`-round play. -/
noncomputable def futileAux_lawN (T : ℕ) : Measure (unitInterval × (Fin T → unitInterval) × (Fin T → unitInterval)) :=
  (volume : Measure unitInterval).prod ((Measure.pi fun _ : Fin T => (volume : Measure unitInterval)).prod
    (Measure.pi fun _ : Fin T => (volume : Measure unitInterval)))

instance futileAux_lawN_prob (T : ℕ) : IsProbabilityMeasure (futileAux_lawN T) := by
  unfold futileAux_lawN; infer_instance

/-- The noise of a `T`-round play in which every shock equals `θ`. -/
def futileAux_xi {Θ : Type} (T : ℕ) (θ : Θ) (n : unitInterval × (Fin T → unitInterval) × (Fin T → unitInterval)) :
    Noise Θ T := (fun _ => θ, n)

lemma futileAux_noise_dirac {Θ : Type} [MeasurableSpace Θ] [MeasurableSingletonClass Θ] (T : ℕ) (θ : Θ)
    (h : Noise Θ T → ℝ) :
    ∫ ξ, h ξ ∂(noiseLaw (Measure.dirac θ) T) = ∫ n, h (futileAux_xi T θ n) ∂(futileAux_lawN T) := by
  unfold noiseLaw
  rw [futileAux_pi_dirac, Measure.dirac_prod]
  exact (measurableEmbedding_prodMk_left _).integral_map h

/-- "Pretend the type is `θ'`": the recommended strategy run as if the distribution were `δ_{θ'}` and every
shock were `θ'`. -/
noncomputable def futileAux_pretend {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (A : DynMech Θ Ω)
    (θ' : Θ) : Strategy Θ Ω A.M0 A.M where
  s0 := fun _ y => A.recom.s0 (Measure.dirac θ') y
  s := fun n _ _ _ m0 ms ωs y => A.recom.s n (Measure.dirac θ') θ' (fun _ => θ') m0 ms ωs y

lemma futileAux_pretend_hist {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (T : ℕ) (θ θ' : Θ) (n : unitInterval × (Fin T → unitInterval) × (Fin T → unitInterval)) :
    ∀ j (hj : j ≤ T), hist G A (futileAux_pretend A θ') (Measure.dirac θ) T (futileAux_xi T θ n) j hj =
      hist G A A.recom (Measure.dirac θ') T (futileAux_xi T θ' n) j hj := by
  intro j
  induction j with
  | zero => intro hj; simp only [hist]
  | succ j ih =>
    intro hj
    rw [hist, hist, ih]
    rfl

/-- The strategy that quits in Round 0. -/
def futileAux_quitStrat {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (A : DynMech Θ Ω) :
    Strategy Θ Ω A.M0 A.M where
  s0 := fun _ _ => A.quit
  s := A.recom.s

lemma futileAux_quit_hist {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (F : Measure Θ) (T : ℕ) (ξ : Noise Θ T) :
    ∀ j (hj : j ≤ T) (i : Fin j), (hist G A (futileAux_quitStrat A) F T ξ j hj).2 i = G.noInt := by
  intro j
  induction j with
  | zero => intro hj i; exact i.elim0
  | succ j ih =>
    intro hj i
    rw [hist]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last]
      exact if_pos rfl
    · simp only [Fin.snoc_castSucc]
      exact ih _ i

/-- Randomness used by `S(A)`: a uniformly random round and the uniforms of a simulated play. -/
abbrev FRand (T : ℕ) := Fin T × (unitInterval × (Fin T → unitInterval) × (Fin T → unitInterval))

/-- Law of `FRand T`. -/
noncomputable def futileAux_muR (T : ℕ) : Measure (FRand T) :=
  (ProbabilityTheory.uniformOn (Set.univ : Set (Fin T))).prod (futileAux_lawN T)

/-- The single-round direct rule `S(A)`: on report `(θ', true)` simulate `A` under `δ_{θ'}` with the
recommended strategy and output the outcome of a uniformly random round. -/
noncomputable def futileAux_dfun {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (A : DynMech Θ Ω) (T : ℕ) (split : unitInterval → FRand T) : Θ × Bool → unitInterval → Ω :=
  fun m z => if m.2 = true then
    outcome G A A.recom (Measure.dirac m.1) T (futileAux_xi T m.1 (split z).2) (split z).1 else G.noInt

lemma futileAux_sim_meas {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (A : DynMech Θ Ω) (hσ : A.recom.Feasible) (T : ℕ) :
    Measurable (fun p : (Θ × (unitInterval × (Fin T → unitInterval) × (Fin T → unitInterval))) × Fin T =>
      outcome G A A.recom (Measure.dirac p.1.1) T (futileAux_xi T p.1.1 p.1.2) p.2) := by
  refine measurable_from_prod_countable_left fun k => ?_
  have e : (fun p : Θ × (unitInterval × (Fin T → unitInterval) × (Fin T → unitInterval)) =>
      outcome G A A.recom (Measure.dirac p.1) T (futileAux_xi T p.1 p.2) k) = fun p =>
      futileAux_roundOut G A A.recom (Measure.dirac p.1) k (A.recom.s0 (Measure.dirac p.1) p.2.1) p.1
        (futileAux_restrict k (le_of_lt k.2) (futileAux_xi T p.1 p.2)) (p.2.2.1 k) (p.2.2.2 k) :=
    funext fun p => futileAux_outcome_eq G A A.recom _ T _ k
  simp only at e ⊢
  rw [e]
  have hd : Measurable (fun p : Θ × (unitInterval × (Fin T → unitInterval) × (Fin T → unitInterval)) =>
      Measure.dirac p.1) := Measure.measurable_dirac.comp measurable_fst
  have h0 : Measurable (fun p : Θ × (unitInterval × (Fin T → unitInterval) × (Fin T → unitInterval)) =>
      ((Measure.dirac p.1, A.recom.s0 (Measure.dirac p.1) p.2.1, p.1,
        futileAux_restrict k (le_of_lt k.2) (futileAux_xi T p.1 p.2), p.2.2.1 k, p.2.2.2 k) :
        RArg Θ A.M0 k)) := by
    refine hd.prodMk ((hσ.1.comp (hd.prodMk measurable_snd.fst)).prodMk (measurable_fst.prodMk
      (Measurable.prodMk ?_ (((measurable_pi_apply k).comp measurable_snd.snd.fst).prodMk
        ((measurable_pi_apply k).comp measurable_snd.snd.snd)))))
    refine Measurable.prodMk (measurable_pi_lambda _ fun j => measurable_fst)
      (Measurable.prodMk (measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp measurable_snd.snd.fst)
        (measurable_pi_lambda _ fun j => (measurable_pi_apply _).comp measurable_snd.snd.snd))
  exact (futileAux_roundOut_meas G A A.recom hσ k).comp h0

lemma futileAux_dfun_meas {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (A : DynMech Θ Ω) (hσ : A.recom.Feasible) (T : ℕ) (split : unitInterval → FRand T)
    (hs : Measurable split) : Measurable (Function.uncurry (futileAux_dfun G A T split)) := by
  have hf : Measurable (fun q : (Θ × Bool) × unitInterval => ((q.1.1, (split q.2).2), (split q.2).1)) :=
    (measurable_fst.fst.prodMk (hs.comp measurable_snd).snd).prodMk (hs.comp measurable_snd).fst
  have h1 := (futileAux_sim_meas G A hσ T).comp hf
  refine Measurable.ite ?_ h1 measurable_const
  exact (measurable_snd.comp measurable_fst) (measurableSet_singleton true)

lemma futileAux_unif_real (T : ℕ) [NeZero T] (t : Fin T) :
    (ProbabilityTheory.uniformOn (Set.univ : Set (Fin T))).real {t} = 1 / T := by
  rw [measureReal_def, ProbabilityTheory.uniformOn_univ, Measure.count_singleton, Fintype.card_fin]
  simp

/-- `E_z[w(θ, S(A)(θ', z))] = (1/T) E[∑_t w(θ, ω_t)]` for the simulated play under `δ_{θ'}`. -/
lemma futileAux_W_formula {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (A : DynMech Θ Ω) (hσ : A.recom.Feasible) (T : ℕ) [NeZero T]
    (split : unitInterval → FRand T)
    (hS : MeasurePreserving split (volume : Measure unitInterval) (futileAux_muR T))
    (w : Θ → Ω → ℝ) (hw : Measurable (Function.uncurry w)) (B : ℝ) (hB : ∀ θ ω, |w θ ω| ≤ B)
    (θ θ' : Θ) :
    ∫ z, w θ (futileAux_dfun G A T split (θ', true) z) ∂(volume : Measure unitInterval) =
      (1 / T) * ∫ n, ∑ t : Fin T, w θ (outcome G A A.recom (Measure.dirac θ') T (futileAux_xi T θ' n) t)
        ∂(futileAux_lawN T) := by
  set H : FRand T → ℝ := fun r =>
    w θ (outcome G A A.recom (Measure.dirac θ') T (futileAux_xi T θ' r.2) r.1) with hH
  have hHm : Measurable H := by
    have hf : Measurable (fun r : FRand T => ((θ', r.2), r.1)) :=
      (measurable_const.prodMk measurable_snd).prodMk measurable_fst
    have := (futileAux_sim_meas G A hσ T).comp hf
    exact hw.comp (measurable_const.prodMk this)
  have hHi : ∀ (μ : Measure (FRand T)) [IsFiniteMeasure μ], Integrable H μ := fun μ _ =>
    Integrable.of_bound hHm.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact hB _ _)
  have e1 : ∫ z, w θ (futileAux_dfun G A T split (θ', true) z) ∂(volume : Measure unitInterval) =
      ∫ z, H (split z) ∂(volume : Measure unitInterval) := by
    simp [futileAux_dfun, hH]
  have hμR : IsProbabilityMeasure (futileAux_muR T) := by unfold futileAux_muR; infer_instance
  rw [e1, ← integral_map hS.measurable.aemeasurable (hS.map_eq ▸ hHm.aestronglyMeasurable), hS.map_eq]
  unfold futileAux_muR
  rw [integral_prod H (hHi _)]
  rw [integral_fintype (Integrable.of_finite)]
  simp_rw [futileAux_unif_real]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    simp [smul_eq_mul, hH]
  · intro t _
    exact Integrable.of_bound (hHm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact hB _ _)

/-- Inserting an independent `F`-distributed coordinate at `t` preserves the product law. -/
lemma futileAux_insert {Θ : Type} [MeasurableSpace Θ] (F : Measure Θ) [IsProbabilityMeasure F] (T : ℕ)
    (t : Fin T) : MeasurePreserving (fun p : Θ × (Fin T → Θ) => Function.update p.2 t p.1)
      (F.prod (Measure.pi fun _ : Fin T => F)) (Measure.pi fun _ : Fin T => F) := by
  classical
  have hm : Measurable (fun p : Θ × (Fin T → Θ) => Function.update p.2 t p.1) :=
    (measurable_update' (a := t)).comp (measurable_snd.prodMk measurable_fst)
  refine ⟨hm, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hset : (fun p : Θ × (Fin T → Θ) => Function.update p.2 t p.1) ⁻¹' Set.univ.pi s =
      s t ×ˢ Set.univ.pi (Function.update s t Set.univ) := by
    ext ⟨θ, x⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h t, fun i => ?_⟩
      by_cases hi : i = t
      · subst hi; simp
      · simpa [Function.update_of_ne hi] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = t
      · subst hi; simpa using h1
      · simpa [Function.update_of_ne hi] using h2 i
  rw [hset, Measure.prod_prod, Measure.pi_pi]
  have hf : (fun i => F (Function.update s t Set.univ i)) = Function.update (fun i => F (s i)) t 1 := by
    funext i
    by_cases hi : i = t
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ t), one_mul,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ t)]

/-- The set whose supremum is `ū(F)`. -/
lemma futileAux_ubar_bdd {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (B : ℝ) (hB : ∀ θ ω, |G.u θ ω| ≤ B ∧ |G.v θ ω| ≤ B) (F : Measure Θ) [IsProbabilityMeasure F] :
    BddAbove {r : ℝ | ∃ d : DirectRule G,
      0 ≤ ∫ θ, ∫ z, G.v θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) ∂F ∧
      r = ∫ θ, ∫ z, G.u θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) ∂F} := by
  refine ⟨B, ?_⟩
  rintro r ⟨d, -, rfl⟩
  have h1 : ∀ θ, ‖∫ z, G.u θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval)‖ ≤ B := by
    intro θ
    have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure unitInterval))
      (f := fun z => G.u θ (d.1 (θ, true) z)) (C := B)
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact (hB _ _).1)
    simpa using h
  have h := norm_integral_le_of_norm_le_const (μ := F) (Filter.Eventually.of_forall h1)
  simp only [probReal_univ, mul_one] at h
  exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at h)

lemma futileAux_ubar_nonneg {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (B : ℝ) (hB : ∀ θ ω, |G.u θ ω| ≤ B ∧ |G.v θ ω| ≤ B) (F : Measure Θ) [IsProbabilityMeasure F] :
    0 ≤ ubar G F := by
  unfold ubar
  refine le_csSup_of_le (futileAux_ubar_bdd G B hB F) ⟨futileAux_d0 G, ?_, ?_⟩ le_rfl
  · simp [futileAux_d0, G.v_noInt]
  · simp [futileAux_d0, G.u_noInt]

lemma futileAux_sampAll {Θ : Type} [MeasurableSpace Θ] (samp : Measure Θ → unitInterval → Θ)
    (hsamp : Measurable (Function.uncurry samp)) (F : Measure Θ) [IsProbabilityMeasure F]
    (hsampF : (volume : Measure unitInterval).map (samp F) = F) (n : ℕ) :
    MeasurePreserving (fun u : Fin n → unitInterval => fun j => samp F (u j))
      (Measure.pi fun _ : Fin n => (volume : Measure unitInterval)) (Measure.pi fun _ : Fin n => F) := by
  have hmeas : Measurable (fun u : Fin n → unitInterval => fun j => samp F (u j)) :=
    measurable_pi_lambda _ fun j => (hsamp.comp (measurable_const.prodMk measurable_id)).comp
      (measurable_pi_apply j)
  refine ⟨hmeas, ?_⟩
  have := Measure.pi_map_pi (μ := fun _ : Fin n => (volume : Measure unitInterval))
    (f := fun _ => samp F) (fun _ => (hsamp.comp (measurable_const.prodMk measurable_id)).aemeasurable)
  rw [this]
  congr 1
  funext i
  exact hsampF

/-- Randomness for the first-best simulation: a round, uniforms for the other shocks, and play uniforms. -/
abbrev FRand1 (T : ℕ) := Fin T × ((Fin T → unitInterval) × (unitInterval × (Fin T → unitInterval) ×
  (Fin T → unitInterval)))

/-- Part 1 of Proposition 13: `PrincipalUtility(A, F, T) ≤ T · ū(F)` for IC `A`. -/
lemma futileAux_p13_part1 {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    [Nonempty Θ] (G : Game Θ Ω) (T : ℕ) (hT : 0 < T) (F : Measure Θ) [IsProbabilityMeasure F]
    (A : DynMech Θ Ω) (hA : IsIC G A T) :
    principalUtility G A A.recom F T ≤ T * ubar G F := by
  classical
  haveI : NeZero T := ⟨hT.ne'⟩
  obtain ⟨B, hB, hB0⟩ := futileAux_B G
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨samp, hsamp, hsampF⟩ := futileAux_sampler Θ
  haveI : StandardBorelSpace (Fin T → unitInterval) := inferInstance
  haveI : StandardBorelSpace ((Fin T → unitInterval) × (Fin T → unitInterval)) := inferInstance
  haveI : StandardBorelSpace (unitInterval × (Fin T → unitInterval) × (Fin T → unitInterval)) :=
    inferInstance
  haveI : StandardBorelSpace ((Fin T → unitInterval) × (unitInterval × (Fin T → unitInterval) ×
    (Fin T → unitInterval))) := inferInstance
  haveI : StandardBorelSpace (FRand1 T) := inferInstance
  set PL := Measure.pi fun _ : Fin T => (volume : Measure unitInterval)
  set PF := Measure.pi fun _ : Fin T => F
  let μ1 : Measure (FRand1 T) :=
    (ProbabilityTheory.uniformOn (Set.univ : Set (Fin T))).prod (PL.prod (futileAux_lawN T))
  haveI : IsProbabilityMeasure μ1 := by infer_instance
  obtain ⟨split, hsm, hsmap⟩ := Measure.exists_measurable_map_eq μ1
  have hS : MeasurePreserving split (volume : Measure unitInterval) μ1 := ⟨hsm, hsmap⟩
  -- the noise with shock `θ` inserted at round `t`
  let ξat : Fin T → Θ → (Fin T → unitInterval) × (unitInterval × (Fin T → unitInterval) ×
      (Fin T → unitInterval)) → Noise Θ T := fun t θ q =>
    (Function.update (fun i => samp F (q.1 i)) t θ, q.2)
  have hξat : ∀ t, Measurable (fun p : Θ × ((Fin T → unitInterval) × (unitInterval ×
      (Fin T → unitInterval) × (Fin T → unitInterval))) => ξat t p.1 p.2) := by
    intro t
    have hs : Measurable (fun p : Θ × ((Fin T → unitInterval) × (unitInterval ×
        (Fin T → unitInterval) × (Fin T → unitInterval))) => fun i => samp F (p.2.1 i)) :=
      measurable_pi_lambda _ fun i => hsamp.comp (measurable_const.prodMk
        ((measurable_pi_apply i).comp measurable_snd.fst))
    exact ((measurable_update' (a := t)).comp (hs.prodMk measurable_fst)).prodMk measurable_snd.snd
  have hout : Measurable (fun ξ : Noise Θ T => fun t => outcome G A A.recom F T ξ t) :=
    (futileAux_hist_meas G A A.recom hA.1 F T T le_rfl).snd
  have hΦ : Measurable (fun x : (Θ × ((Fin T → unitInterval) × (unitInterval ×
      (Fin T → unitInterval) × (Fin T → unitInterval)))) × Fin T =>
      outcome G A A.recom F T (ξat x.2 x.1.1 x.1.2) x.2) := by
    refine measurable_from_prod_countable_left fun t => ?_
    exact (measurable_pi_apply t).comp (hout.comp (hξat t))
  let dfun : Θ × Bool → unitInterval → Ω := fun m z =>
    if m.2 = true then outcome G A A.recom F T (ξat (split z).1 m.1 (split z).2) (split z).1 else G.noInt
  have hdm : Measurable (Function.uncurry dfun) := by
    have hf : Measurable (fun q : (Θ × Bool) × unitInterval => ((q.1.1, (split q.2).2), (split q.2).1)) :=
      (measurable_fst.fst.prodMk (hsm.comp measurable_snd).snd).prodMk (hsm.comp measurable_snd).fst
    refine Measurable.ite ?_ (hΦ.comp hf) measurable_const
    exact (measurable_snd.comp measurable_fst) (measurableSet_singleton true)
  let d : DirectRule G := ⟨dfun, hdm, fun θ z => by simp [dfun]⟩
  -- the averaging formula
  have formula : ∀ w : Θ → Ω → ℝ, Measurable (Function.uncurry w) → (∀ θ ω, |w θ ω| ≤ B) →
      ∫ θ, ∫ z, w θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) ∂F =
        (1 / T) * ∫ ξ, ∑ t : Fin T, w (ξ.1 t) (outcome G A A.recom F T ξ t) ∂(noiseLaw F T) := by
    intro w hw hwB
    have : IsProbabilityMeasure (noiseLaw F T) := by unfold noiseLaw; infer_instance
    have hK : ∀ t, Measurable (fun p : Θ × ((Fin T → Θ) × (unitInterval × (Fin T → unitInterval) ×
        (Fin T → unitInterval))) =>
        w p.1 (outcome G A A.recom F T (Function.update p.2.1 t p.1, p.2.2) t)) := by
      intro t
      have h1 : Measurable (fun p : Θ × ((Fin T → Θ) × (unitInterval × (Fin T → unitInterval) ×
          (Fin T → unitInterval))) => ((Function.update p.2.1 t p.1, p.2.2) : Noise Θ T)) :=
        ((measurable_update' (a := t)).comp (measurable_snd.fst.prodMk measurable_fst)).prodMk
          measurable_snd.snd
      exact hw.comp (measurable_fst.prodMk ((measurable_pi_apply t).comp (hout.comp h1)))
    have hbd : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ),
        Measurable f → (∀ x, |f x| ≤ B) → Integrable f μ := fun X _ μ _ f hf hfb =>
      Integrable.of_bound hf.aestronglyMeasurable B
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfb x)
    -- inner integral for a fixed `θ`
    have inner : ∀ θ : Θ, ∫ z, w θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) =
        (1 / T) * ∑ t : Fin T, ∫ q, w θ (outcome G A A.recom F T (Function.update q.1 t θ, q.2) t)
          ∂(PF.prod (futileAux_lawN T)) := by
      intro θ
      let H : FRand1 T → ℝ := fun r => w θ (outcome G A A.recom F T (ξat r.1 θ r.2) r.1)
      have hHm : Measurable H := hw.comp (measurable_const.prodMk
        (hΦ.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)))
      have e1 : ∫ z, w θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) =
          ∫ z, H (split z) ∂(volume : Measure unitInterval) := by
        simp [d, dfun, H]
      rw [e1, ← integral_map hS.measurable.aemeasurable (hS.map_eq ▸ hHm.aestronglyMeasurable),
        hS.map_eq, integral_prod H (hbd _ _ H hHm fun r => hwB _ _),
        integral_fintype Integrable.of_finite]
      simp_rw [futileAux_unif_real]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [smul_eq_mul]
      congr 1
      have hmp := (futileAux_sampAll samp hsamp F (hsampF F inferInstance) T).prod
        (MeasurePreserving.id (futileAux_lawN T))
      rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable]
      · rfl
      · rw [hmp.map_eq]
        exact ((hK t).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    simp_rw [inner]
    rw [integral_const_mul, integral_finsetSum, integral_finsetSum]
    · congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      have hg := ((futileAux_insert F T t).prod (MeasurePreserving.id (futileAux_lawN T))).comp
        (futileAux_mp_assoc_symm F PF (futileAux_lawN T))
      have hfm : Measurable (fun ξ : Noise Θ T => w (ξ.1 t) (outcome G A A.recom F T ξ t)) :=
        hw.comp (((measurable_pi_apply t).comp measurable_fst).prodMk ((measurable_pi_apply t).comp hout))
      rw [← integral_prod _ (hbd _ _ _ (hK t) fun p => hwB _ _)]
      rw [show noiseLaw F T = PF.prod (futileAux_lawN T) from rfl]
      have key := integral_map (μ := F.prod (PF.prod (futileAux_lawN T))) hg.measurable.aemeasurable
        (f := fun ξ : Noise Θ T => w (ξ.1 t) (outcome G A A.recom F T ξ t))
        (by rw [hg.map_eq]; exact hfm.aestronglyMeasurable)
      rw [hg.map_eq] at key
      rw [key]
      congr 1
      funext p
      simp
    · intro t _
      exact hbd _ _ _ (((measurable_pi_apply t).comp measurable_fst).prodMk
        ((measurable_pi_apply t).comp hout) |> hw.comp) fun ξ => hwB _ _
    · intro t _
      have hm := ((hK t).stronglyMeasurable.integral_prod_right'
        (ν := PF.prod (futileAux_lawN T))).measurable
      refine hbd _ _ _ hm fun θ => ?_
      have h := norm_integral_le_of_norm_le_const (μ := PF.prod (futileAux_lawN T))
        (f := fun q => w θ (outcome G A A.recom F T (Function.update q.1 t θ, q.2) t)) (C := B)
        (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hwB _ _)
      simpa using h
  -- conclude
  obtain ⟨hσ, hIC⟩ := hA
  have hv := formula G.v G.v_meas (fun θ ω => (hB θ ω).2)
  have hu := formula G.u G.u_meas (fun θ ω => (hB θ ω).1)
  have hquit : agentUtility G A (futileAux_quitStrat A) F T = 0 := by
    unfold agentUtility outcome
    simp [futileAux_quit_hist, G.v_noInt]
  have hIR := hIC F inferInstance (futileAux_quitStrat A) ⟨measurable_const, hσ.2⟩
  rw [hquit] at hIR
  have hmem : ∫ θ, ∫ z, G.u θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) ∂F ∈
      {r : ℝ | ∃ d : DirectRule G,
        0 ≤ ∫ θ, ∫ z, G.v θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) ∂F ∧
        r = ∫ θ, ∫ z, G.u θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) ∂F} := by
    refine ⟨d, ?_, rfl⟩
    rw [hv]
    exact mul_nonneg (by positivity) hIR
  have hle := le_csSup (futileAux_ubar_bdd G B hB F) hmem
  have hPU : principalUtility G A A.recom F T =
      T * ∫ θ, ∫ z, G.u θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) ∂F := by
    rw [hu]; unfold principalUtility; field_simp
  rw [hPU]
  exact mul_le_mul_of_nonneg_left hle hTpos.le

/-- `F ↦ ∫ g dF`, written through lower integrals so that it is measurable on the Giry space. -/
noncomputable def futileAux_intG {Θ : Type} [MeasurableSpace Θ] (g : Θ → ℝ) (F : Measure Θ) : ℝ :=
  (∫⁻ θ, ENNReal.ofReal (g θ) ∂F).toReal - (∫⁻ θ, ENNReal.ofReal (-g θ) ∂F).toReal

lemma futileAux_intG_meas {Θ : Type} [MeasurableSpace Θ] (g : Θ → ℝ) (hg : Measurable g) :
    Measurable (futileAux_intG g) :=
  ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hg)).ennreal_toReal).sub
    ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hg.neg)).ennreal_toReal)

lemma futileAux_intG_eq {Θ : Type} [MeasurableSpace Θ] (g : Θ → ℝ) (F : Measure Θ)
    (hg : Integrable g F) : futileAux_intG g F = ∫ θ, g θ ∂F :=
  (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg).symm

/-- The mechanism that ignores all reports and implements the lottery `π̃((θ⋆, true), ·)` in every round,
recommending participation iff it is worthwhile in expectation. -/
noncomputable def futileAux_fixedMech {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (θs : Θ) (d : DirectRule G) : DynMech Θ Ω where
  M0 := Bool
  quit := false
  M := fun _ => Bool
  rule := fun _ _ _ _ _ z => d.1 (θs, true) z
  rule_meas := fun _ => d.2.1.comp (measurable_const.prodMk measurable_snd.snd.snd.snd)
  recom :=
    { s0 := fun F _ => decide (0 ≤ futileAux_intG (fun θ => ∫ z, G.v θ (d.1 (θs, true) z)
          ∂(volume : Measure unitInterval)) F)
      s := fun _ _ _ _ _ _ _ _ => true }

/-- Indicator of participation. -/
def futileAux_part (b : Bool) : ℝ := if b = false then 0 else 1

lemma futileAux_fixed_outcome {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (θs : Θ) (d : DirectRule G) (w : Θ → Ω → ℝ) (hw0 : ∀ θ, w θ G.noInt = 0)
    (τ : Strategy Θ Ω (futileAux_fixedMech G θs d).M0 (futileAux_fixedMech G θs d).M) (F : Measure Θ) (T : ℕ)
    (ξ : Noise Θ T) (t : Fin T) :
    w (ξ.1 t) (outcome G (futileAux_fixedMech G θs d) τ F T ξ t) =
      futileAux_part (τ.s0 F ξ.2.1) * w (ξ.1 t) (d.1 (θs, true) (ξ.2.2.2 t)) := by
  rw [futileAux_outcome_eq]
  unfold futileAux_roundOut
  by_cases h : τ.s0 F ξ.2.1 = false
  · have hq : τ.s0 F ξ.2.1 = (futileAux_fixedMech G θs d).quit := h
    have hp : futileAux_part (τ.s0 F ξ.2.1) = 0 := if_pos h
    rw [if_pos hq, hw0, hp, zero_mul]
  · have hq : ¬ τ.s0 F ξ.2.1 = (futileAux_fixedMech G θs d).quit := h
    have hp : futileAux_part (τ.s0 F ξ.2.1) = 1 := if_neg h
    rw [if_neg hq, hp, one_mul]
    rfl

/-- Total utility under the fixed mechanism: `T · P(participate) · ∫∫ w`. -/
lemma futileAux_fixed_total {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (θs : Θ) (d : DirectRule G) (w : Θ → Ω → ℝ) (hw : Measurable (Function.uncurry w)) (B : ℝ)
    (hB : ∀ θ ω, |w θ ω| ≤ B) (hw0 : ∀ θ, w θ G.noInt = 0)
    (τ : Strategy Θ Ω (futileAux_fixedMech G θs d).M0 (futileAux_fixedMech G θs d).M)
    (hτ : Measurable (fun p : Measure Θ × unitInterval => τ.s0 p.1 p.2))
    (F : Measure Θ) [IsProbabilityMeasure F] (T : ℕ) :
    ∫ ξ, ∑ t : Fin T, w (ξ.1 t) (outcome G (futileAux_fixedMech G θs d) τ F T ξ t) ∂(noiseLaw F T) =
      T * ((∫ y, futileAux_part (τ.s0 F y) ∂(volume : Measure unitInterval)) *
        ∫ θ, ∫ z, w θ (d.1 (θs, true) z) ∂(volume : Measure unitInterval) ∂F) := by
  have : IsProbabilityMeasure (noiseLaw F T) := by unfold noiseLaw; infer_instance
  have hc : Measurable (fun y : unitInterval => futileAux_part (τ.s0 F y)) := by
    have h0 : Measurable (fun y : unitInterval => τ.s0 F y) := hτ.comp (measurable_const.prodMk measurable_id)
    exact (measurable_from_top (f := futileAux_part)).comp h0
  have hcb : ∀ y, |futileAux_part (τ.s0 F y)| ≤ 1 := by
    intro y; unfold futileAux_part; split_ifs <;> simp
  have hdd : Measurable (fun p : Θ × unitInterval => w p.1 (d.1 (θs, true) p.2)) :=
    hw.comp (measurable_fst.prodMk (d.2.1.comp (measurable_const.prodMk measurable_snd)))
  simp_rw [futileAux_fixed_outcome G θs d w hw0 τ F T]
  rw [integral_finsetSum]
  · have each : ∀ t : Fin T, ∫ ξ, futileAux_part (τ.s0 F ξ.2.1) * w (ξ.1 t) (d.1 (θs, true) (ξ.2.2.2 t))
        ∂(noiseLaw F T) = (∫ y, futileAux_part (τ.s0 F y) ∂(volume : Measure unitInterval)) *
          ∫ θ, ∫ z, w θ (d.1 (θs, true) z) ∂(volume : Measure unitInterval) ∂F := by
      intro t
      let J : Θ × unitInterval × FPast Θ t × unitInterval × unitInterval → ℝ := fun c =>
        futileAux_part (τ.s0 F c.2.1) * w c.1 (d.1 (θs, true) c.2.2.2.2)
      have hJ : Measurable J := (hc.comp measurable_snd.fst).mul
        (hdd.comp (measurable_fst.prodMk measurable_snd.snd.snd.snd))
      have hmp := futileAux_mp_T F T t
      have key := integral_map (μ := noiseLaw F T) hmp.measurable.aemeasurable (f := J)
        (by rw [hmp.map_eq]; exact hJ.aestronglyMeasurable)
      rw [hmp.map_eq] at key
      have e : ∫ ξ, futileAux_part (τ.s0 F ξ.2.1) * w (ξ.1 t) (d.1 (θs, true) (ξ.2.2.2 t))
          ∂(noiseLaw F T) = ∫ c, J c ∂(futileAux_Q F t) := key.symm
      rw [e]
      unfold futileAux_Q
      have hJi : Integrable J (F.prod ((volume : Measure unitInterval).prod ((futileAux_W F t).prod
          ((volume : Measure unitInterval).prod (volume : Measure unitInterval))))) :=
        Integrable.of_bound hJ.aestronglyMeasurable (1 * B) (Filter.Eventually.of_forall fun c => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hcb _) (hB _ _) (abs_nonneg _) zero_le_one)
      rw [integral_prod J hJi, ← integral_const_mul]
      congr 1
      funext θ
      have hJθ : Integrable (fun r : unitInterval × FPast Θ t × unitInterval × unitInterval => J (θ, r))
          ((volume : Measure unitInterval).prod ((futileAux_W F t).prod
            ((volume : Measure unitInterval).prod (volume : Measure unitInterval)))) :=
        Integrable.of_bound (hJ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable (1 * B)
          (Filter.Eventually.of_forall fun c => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul (hcb _) (hB _ _) (abs_nonneg _) zero_le_one)
      rw [integral_prod _ hJθ]
      simp only [J]
      simp_rw [integral_const_mul]
      rw [integral_mul_const]
      congr 1
      rw [integral_fun_snd (f := fun q : unitInterval × unitInterval => w θ (d.1 (θs, true) q.2))]
      rw [integral_fun_snd (f := fun z : unitInterval => w θ (d.1 (θs, true) z))]
      simp
    simp_rw [each]
    simp
  · intro t _
    have hm : Measurable (fun ξ : Noise Θ T =>
        futileAux_part (τ.s0 F ξ.2.1) * w (ξ.1 t) (d.1 (θs, true) (ξ.2.2.2 t))) :=
      (hc.comp measurable_snd.fst).mul (hdd.comp (f := fun ξ : Noise Θ T => (ξ.1 t, ξ.2.2.2 t))
        (((measurable_pi_apply t).comp measurable_fst).prodMk
        ((measurable_pi_apply t).comp measurable_snd.snd.snd)))
    exact Integrable.of_bound hm.aestronglyMeasurable (1 * B) (Filter.Eventually.of_forall fun c => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hcb _) (hB _ _) (abs_nonneg _) zero_le_one)

lemma futileAux_gv_meas {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω) (θs : Θ)
    (d : DirectRule G) (w : Θ → Ω → ℝ) (hw : Measurable (Function.uncurry w)) :
    Measurable (fun θ => ∫ z, w θ (d.1 (θs, true) z) ∂(volume : Measure unitInterval)) := by
  have h : Measurable (fun p : Θ × unitInterval => w p.1 (d.1 (θs, true) p.2)) :=
    hw.comp (measurable_fst.prodMk (d.2.1.comp (measurable_const.prodMk measurable_snd)))
  exact (h.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure unitInterval))).measurable

lemma futileAux_gv_int {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω) (θs : Θ)
    (d : DirectRule G) (w : Θ → Ω → ℝ) (hw : Measurable (Function.uncurry w)) (B : ℝ)
    (hB : ∀ θ ω, |w θ ω| ≤ B) (F : Measure Θ) [IsProbabilityMeasure F] :
    Integrable (fun θ => ∫ z, w θ (d.1 (θs, true) z) ∂(volume : Measure unitInterval)) F := by
  refine Integrable.of_bound (futileAux_gv_meas G θs d w hw).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun θ => ?_)
  have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure unitInterval))
    (f := fun z => w θ (d.1 (θs, true) z)) (C := B)
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB _ _)
  simpa using h

lemma futileAux_fixed_IC {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (θs : Θ) (d : DirectRule G) (T : ℕ) : IsIC G (futileAux_fixedMech G θs d) T := by
  obtain ⟨B, hB⟩ := G.bdd
  set gv := fun θ => ∫ z, G.v θ (d.1 (θs, true) z) ∂(volume : Measure unitInterval) with hgv
  have hgm := futileAux_gv_meas G θs d G.v G.v_meas
  have hs0 : Measurable (fun p : Measure Θ × unitInterval =>
      (futileAux_fixedMech G θs d).recom.s0 p.1 p.2) := by
    have e : (fun p : Measure Θ × unitInterval => (futileAux_fixedMech G θs d).recom.s0 p.1 p.2) =
        fun p => if 0 ≤ futileAux_intG gv p.1 then true else false := by
      funext p
      show decide _ = _
      by_cases h : 0 ≤ futileAux_intG gv p.1
      · rw [if_pos h]; exact decide_eq_true h
      · rw [if_neg h]; exact decide_eq_false h
    rw [e]
    exact Measurable.ite (measurableSet_le measurable_const
      ((futileAux_intG_meas gv hgm).comp measurable_fst)) measurable_const measurable_const
  refine ⟨⟨hs0, fun k => measurable_const⟩, fun F hF σ' hσ' => ?_⟩
  have hτ := futileAux_fixed_total G θs d G.v G.v_meas B (fun θ ω => (hB θ ω).2) G.v_noInt
  unfold agentUtility
  rw [hτ σ' hσ'.1 F T, hτ _ hs0 F T]
  set U := ∫ θ, gv θ ∂F with hU
  have hUeq : futileAux_intG gv F = U :=
    futileAux_intG_eq gv F (futileAux_gv_int G θs d G.v G.v_meas B (fun θ ω => (hB θ ω).2) F)
  have hC0 : 0 ≤ ∫ y, futileAux_part (σ'.s0 F y) ∂(volume : Measure unitInterval) :=
    integral_nonneg fun y => by unfold futileAux_part; split_ifs <;> norm_num
  have hC1 : ∫ y, futileAux_part (σ'.s0 F y) ∂(volume : Measure unitInterval) ≤ 1 := by
    have hc : Measurable (fun y : unitInterval => futileAux_part (σ'.s0 F y)) :=
      (measurable_from_top (f := futileAux_part)).comp (hσ'.1.comp (measurable_const.prodMk measurable_id))
    calc ∫ y, futileAux_part (σ'.s0 F y) ∂(volume : Measure unitInterval)
        ≤ ∫ _y, (1 : ℝ) ∂(volume : Measure unitInterval) := by
          refine integral_mono (Integrable.of_bound hc.aestronglyMeasurable 1
            (Filter.Eventually.of_forall fun y => ?_)) (integrable_const _) fun y => ?_
          · unfold futileAux_part; split_ifs <;> simp
          · unfold futileAux_part; split_ifs <;> norm_num
      _ = 1 := by simp
  have hrec : ∫ y, futileAux_part ((futileAux_fixedMech G θs d).recom.s0 F y) ∂(volume : Measure unitInterval)
      = if 0 ≤ U then 1 else 0 := by
    show ∫ y, futileAux_part (decide (0 ≤ futileAux_intG gv F)) ∂(volume : Measure unitInterval) = _
    rw [hUeq]
    by_cases h : 0 ≤ U <;> simp [h, futileAux_part]
  rw [hrec]
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  apply mul_le_mul_of_nonneg_left _ hT0
  by_cases h : 0 ≤ U
  · rw [if_pos h, one_mul]; nlinarith
  · rw [if_neg h, zero_mul]; push_neg at h; nlinarith

lemma futileAux_p13_part2 {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    [Nonempty Θ] (G : Game Θ Ω) (T : ℕ) (hT : 0 < T) (θs : Θ) :
    T * ubar G (Measure.dirac θs) ≤ OPT G (Measure.dirac θs) T := by
  obtain ⟨B, hB, hB0⟩ := futileAux_B G
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  rw [← le_div_iff₀' hTpos]
  unfold ubar
  refine csSup_le ⟨0, futileAux_d0 G, by simp [futileAux_d0, G.v_noInt], by simp [futileAux_d0, G.u_noInt]⟩ ?_
  rintro r ⟨d, hv, rfl⟩
  rw [le_div_iff₀' hTpos]
  have hIC := futileAux_fixed_IC G θs d T
  have hle := (futileAux_opt G B hB hB0 (Measure.dirac θs) T).2 _ hIC
  refine le_trans (le_of_eq ?_) hle
  have hs0 : Measurable (fun p : Measure Θ × unitInterval =>
      (futileAux_fixedMech G θs d).recom.s0 p.1 p.2) := hIC.1.1
  unfold principalUtility
  rw [futileAux_fixed_total G θs d G.u G.u_meas B (fun θ ω => (hB θ ω).1) G.u_noInt _ hs0 _ T]
  have hgv : futileAux_intG (fun θ => ∫ z, G.v θ (d.1 (θs, true) z) ∂(volume : Measure unitInterval))
      (Measure.dirac θs) = ∫ z, G.v θs (d.1 (θs, true) z) ∂(volume : Measure unitInterval) := by
    rw [futileAux_intG_eq _ _ (futileAux_gv_int G θs d G.v G.v_meas B (fun θ ω => (hB θ ω).2) _),
      integral_dirac]
  rw [integral_dirac] at hv
  have hpart : ∫ y, futileAux_part ((futileAux_fixedMech G θs d).recom.s0 (Measure.dirac θs) y)
      ∂(volume : Measure unitInterval) = 1 := by
    show ∫ y, futileAux_part (decide (0 ≤ futileAux_intG _ (Measure.dirac θs))) ∂(volume : Measure unitInterval) = 1
    rw [hgv]
    simp [hv, futileAux_part]
  rw [hpart, one_mul, integral_dirac, integral_dirac]

theorem solution {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (T : ℕ) (hT : 0 < T) :
    (∀ F : Measure Θ, IsProbabilityMeasure F → OPT G F T ≤ T * ubar G F) ∧
    ∀ θ : Θ, OPT G (Measure.dirac θ) T = T * ubar G (Measure.dirac θ) := by
  obtain ⟨B, hB, hB0⟩ := futileAux_B G
  have part1 : ∀ F : Measure Θ, IsProbabilityMeasure F → OPT G F T ≤ T * ubar G F := by
    intro F hF
    have hu := futileAux_ubar_nonneg G B hB F
    unfold OPT
    rcases (Set.eq_empty_or_nonempty {r : ℝ | ∃ A : DynMech Θ Ω, IsIC G A T ∧
        r = principalUtility G A A.recom F T}) with he | hne
    · rw [he, Real.sSup_empty]; exact mul_nonneg (Nat.cast_nonneg _) hu
    · exact csSup_le hne fun r ⟨A, hA, hr⟩ => hr ▸ futileAux_p13_part1 G T hT F A hA
  exact ⟨part1, fun θ => le_antisymm (part1 _ inferInstance) (futileAux_p13_part2 G T hT θ)⟩
