-- Prove2me | solution 1 for FutileDynamics.StaticOpt.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:12:26.184444+00:00
-- url     : https://prove2.me/submissions/3a68aa2d-712b-46f3-bd2d-734781140705

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

open Classical in
/-- The single-round report actually submitted by `τ` (a PASS-type report when quitting). -/
noncomputable def futileAux_mrep {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (d : DirectRule G)
    (τ : Strategy Θ Ω (repeatDirect G d).M0 (repeatDirect G d).M) (F : Measure Θ)
    (a : (Fin 1 → Θ) × unitInterval × (Fin 1 → unitInterval)) : Θ × Bool :=
  if τ.s0 F a.2.1 = false then (a.1 0, false) else
    (τ.s 0 F (a.1 0) (fun j => a.1 ⟨j, by omega⟩) (τ.s0 F a.2.1) (fun j => j.elim0) (fun j => j.elim0)
      (a.2.2 0) : Θ × Bool)

open Classical in
lemma futileAux_mrep_meas {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (d : DirectRule G)
    (τ : Strategy Θ Ω (repeatDirect G d).M0 (repeatDirect G d).M) (hτ : τ.Feasible) (F : Measure Θ) :
    Measurable (futileAux_mrep G d τ F) := by
  have h0 : Measurable (fun a : (Fin 1 → Θ) × unitInterval × (Fin 1 → unitInterval) => τ.s0 F a.2.1) :=
    hτ.1.comp (measurable_const.prodMk measurable_snd.fst)
  have h1 : Measurable (fun a : (Fin 1 → Θ) × unitInterval × (Fin 1 → unitInterval) =>
      τ.s 0 F (a.1 0) (fun j => a.1 ⟨j, by omega⟩) (τ.s0 F a.2.1) (fun j => j.elim0) (fun j => j.elim0)
        (a.2.2 0)) := by
    have hf : Measurable (fun a : (Fin 1 → Θ) × unitInterval × (Fin 1 → unitInterval) =>
        (F, a.1 0, (fun j : Fin 0 => a.1 ⟨j, by omega⟩), τ.s0 F a.2.1,
          (fun j => j.elim0 : (j : Fin 0) → (repeatDirect G d).M j), (fun j => j.elim0 : Fin 0 → Ω),
          a.2.2 0)) :=
      measurable_const.prodMk (((measurable_pi_apply 0).comp measurable_fst).prodMk
        ((measurable_pi_lambda _ fun j => j.elim0).prodMk (h0.prodMk (measurable_const.prodMk (measurable_const.prodMk
        ((measurable_pi_apply 0).comp measurable_snd.snd))))))
    exact (hτ.2 0).comp hf
  unfold futileAux_mrep
  exact Measurable.ite (h0 (measurableSet_singleton false))
    (((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_const) h1

open Classical in
lemma futileAux_outcome_one' {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (d : DirectRule G)
    (τ : Strategy Θ Ω (repeatDirect G d).M0 (repeatDirect G d).M) (F : Measure Θ) (ξ : Noise Θ 1) :
    outcome G (repeatDirect G d) τ F 1 ξ 0 =
      d.1 (futileAux_mrep G d τ F (ξ.1, ξ.2.1, ξ.2.2.1)) (ξ.2.2.2 0) := by
  unfold outcome futileAux_mrep
  rw [hist]
  dsimp only
  by_cases h : τ.s0 F ξ.2.1 = false
  · have hq : τ.s0 F ξ.2.1 = (repeatDirect G d).quit := h
    rw [if_pos hq]
    exact (d.2.2 _ _).symm.trans (congrArg (fun m => d.1 m (ξ.2.2.2 0)) (if_pos h)).symm
  · have hq : ¬ τ.s0 F ξ.2.1 = (repeatDirect G d).quit := h
    rw [if_neg hq]
    exact (congrArg (fun m => d.1 m (ξ.2.2.2 0)) (if_neg h)).symm

/-- Single-round agent utility of `S` against a feasible `τ`, after integrating out the principal's
uniform. -/
lemma futileAux_au_one {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (d : DirectRule G)
    (τ : Strategy Θ Ω (repeatDirect G d).M0 (repeatDirect G d).M) (hτ : τ.Feasible) (F : Measure Θ)
    [IsProbabilityMeasure F] :
    agentUtility G (repeatDirect G d) τ F 1 =
      ∫ a, (∫ z, G.v (a.1 0) (d.1 (futileAux_mrep G d τ F a) z) ∂(volume : Measure unitInterval))
        ∂((Measure.pi fun _ : Fin 1 => F).prod ((volume : Measure unitInterval).prod
          (Measure.pi fun _ : Fin 1 => (volume : Measure unitInterval)))) := by
  obtain ⟨B, hB⟩ := G.bdd
  set Lv := (volume : Measure unitInterval)
  set PF := Measure.pi fun _ : Fin 1 => F
  set PL := Measure.pi fun _ : Fin 1 => Lv
  let K : ((Fin 1 → Θ) × unitInterval × (Fin 1 → unitInterval)) × (Fin 1 → unitInterval) → ℝ :=
    fun p => G.v (p.1.1 0) (d.1 (futileAux_mrep G d τ F p.1) (p.2 0))
  have hK : Measurable K := by
    have hm : Measurable (fun p : ((Fin 1 → Θ) × unitInterval × (Fin 1 → unitInterval)) ×
        (Fin 1 → unitInterval) => futileAux_mrep G d τ F p.1) :=
      (futileAux_mrep_meas G d τ hτ F).comp measurable_fst
    have hd : Measurable (fun p : ((Fin 1 → Θ) × unitInterval × (Fin 1 → unitInterval)) ×
        (Fin 1 → unitInterval) => d.1 (futileAux_mrep G d τ F p.1) (p.2 0)) :=
      d.2.1.comp (hm.prodMk ((measurable_pi_apply 0).comp measurable_snd))
    exact G.v_meas.comp (((measurable_pi_apply 0).comp measurable_fst.fst).prodMk hd)
  have e := (futileAux_mp_assoc_symm PF (Lv.prod PL) PL).comp
    ((MeasurePreserving.id PF).prod (futileAux_mp_assoc_symm Lv PL PL))
  unfold agentUtility
  simp only [Fin.sum_univ_one]
  simp_rw [futileAux_outcome_one']
  have step1 : ∫ ξ, G.v (ξ.1 0) (d.1 (futileAux_mrep G d τ F (ξ.1, ξ.2.1, ξ.2.2.1)) (ξ.2.2.2 0))
      ∂(noiseLaw F 1) = ∫ p, K p ∂((PF.prod (Lv.prod PL)).prod PL) := by
    rw [← e.map_eq, integral_map e.measurable.aemeasurable (e.map_eq ▸ hK.aestronglyMeasurable)]
    rfl
  rw [step1, integral_prod K (Integrable.of_bound hK.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact (hB _ _).2))]
  congr 1
  funext a
  exact (measurePreserving_funUnique Lv (Fin 1)).integral_comp'
    (fun z => G.v (a.1 0) (d.1 (futileAux_mrep G d τ F a) z))

theorem solution {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (T : ℕ) (hT : 0 < T) :
    ∀ A : DynMech Θ Ω, IsIC G A T → ∃ d : DirectRule G, SingleRoundIC G d ∧
      ∀ θ : Θ, principalUtility G A A.recom (Measure.dirac θ) T =
        T * principalUtility G (repeatDirect G d) (repeatDirect G d).recom (Measure.dirac θ) 1 := by
  intro A hA
  haveI : NeZero T := ⟨hT.ne'⟩
  obtain ⟨B, hB, hB0⟩ := futileAux_B G
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  haveI : StandardBorelSpace (Fin T → unitInterval) := inferInstance
  haveI : StandardBorelSpace ((Fin T → unitInterval) × (Fin T → unitInterval)) := inferInstance
  haveI : StandardBorelSpace (unitInterval × (Fin T → unitInterval) × (Fin T → unitInterval)) :=
    inferInstance
  haveI : StandardBorelSpace (FRand T) := inferInstance
  haveI : Nonempty (FRand T) := ⟨(0, 0, fun _ => 0, fun _ => 0)⟩
  haveI hμR : IsProbabilityMeasure (futileAux_muR T) := by unfold futileAux_muR; infer_instance
  obtain ⟨split, hsm, hsmap⟩ := Measure.exists_measurable_map_eq (futileAux_muR T)
  have hS : MeasurePreserving split (volume : Measure unitInterval) (futileAux_muR T) := ⟨hsm, hsmap⟩
  let d : DirectRule G := ⟨futileAux_dfun G A T split, futileAux_dfun_meas G A hA.1 T split hsm,
    fun θ z => by simp [futileAux_dfun]⟩
  have hd1 : d.1 = futileAux_dfun G A T split := rfl
  -- utilities of `A` at a point mass, as integrals over the uniforms
  have hAU : ∀ (τ : Strategy Θ Ω A.M0 A.M) (θ : Θ), agentUtility G A τ (Measure.dirac θ) T =
      ∫ n, ∑ t : Fin T, G.v θ (outcome G A τ (Measure.dirac θ) T (futileAux_xi T θ n) t)
        ∂(futileAux_lawN T) := fun τ θ => futileAux_noise_dirac T θ _
  have hPU : ∀ (τ : Strategy Θ Ω A.M0 A.M) (θ : Θ), principalUtility G A τ (Measure.dirac θ) T =
      ∫ n, ∑ t : Fin T, G.u θ (outcome G A τ (Measure.dirac θ) T (futileAux_xi T θ n) t)
        ∂(futileAux_lawN T) := fun τ θ => futileAux_noise_dirac T θ _
  have hWv := futileAux_W_formula G A hA.1 T split hS G.v G.v_meas B (fun θ ω => (hB θ ω).2)
  have hWu := futileAux_W_formula G A hA.1 T split hS G.u G.u_meas B (fun θ ω => (hB θ ω).1)
  have hpre : ∀ (θ θ' : Θ) n (t : Fin T),
      outcome G A (futileAux_pretend A θ') (Measure.dirac θ) T (futileAux_xi T θ n) t =
        outcome G A A.recom (Measure.dirac θ') T (futileAux_xi T θ' n) t := by
    intro θ θ' n t
    unfold outcome
    rw [futileAux_pretend_hist]
  have hpreF : ∀ θ' : Θ, (futileAux_pretend A θ').Feasible := by
    intro θ'
    refine ⟨hA.1.1.comp (measurable_const.prodMk measurable_snd), fun n => ?_⟩
    have hf : Measurable (fun p : Measure Θ × Θ × (Fin n → Θ) × A.M0 × ((j : Fin n) → A.M j) ×
        (Fin n → Ω) × unitInterval => (Measure.dirac θ', θ', (fun _ : Fin n => θ'), p.2.2.2.1,
          p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2)) :=
      measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk
        measurable_snd.snd.snd))
    exact (hA.1.2 n).comp hf
  have hquitF : (futileAux_quitStrat A).Feasible := ⟨measurable_const, hA.1.2⟩
  have hquit0 : ∀ θ : Θ, agentUtility G A (futileAux_quitStrat A) (Measure.dirac θ) T = 0 := by
    intro θ
    unfold agentUtility outcome
    simp [futileAux_quit_hist, G.v_noInt]
  -- expected agent utility of each single-round report
  let Wf : Θ → Θ × Bool → ℝ := fun θ m => ∫ z, G.v θ (d.1 m z) ∂(volume : Measure unitInterval)
  have hWtrue : ∀ θ : Θ, (T : ℝ) * Wf θ (θ, true) = agentUtility G A A.recom (Measure.dirac θ) T := by
    intro θ
    simp only [Wf, hd1]
    rw [hWv θ θ, hAU]
    field_simp
  have hWle : ∀ (θ : Θ) (m : Θ × Bool), Wf θ m ≤ Wf θ (θ, true) := by
    intro θ m
    obtain ⟨θ', b⟩ := m
    have hT1 := hWtrue θ
    cases b with
    | false =>
      have h0 : Wf θ (θ', false) = 0 := by simp [Wf, d.2.2, G.v_noInt]
      rw [h0]
      have := hA.2 (Measure.dirac θ) inferInstance _ hquitF
      rw [hquit0] at this
      nlinarith
    | true =>
      have hdev := hA.2 (Measure.dirac θ) inferInstance _ (hpreF θ')
      have e : (T : ℝ) * Wf θ (θ', true) =
          agentUtility G A (futileAux_pretend A θ') (Measure.dirac θ) T := by
        simp only [Wf, hd1]
        rw [hWv θ θ', hAU]
        simp_rw [hpre]
        field_simp
      nlinarith
  have hWm : Measurable (Function.uncurry Wf) := by
    have h : Measurable (fun p : (Θ × (Θ × Bool)) × unitInterval => G.v p.1.1 (d.1 p.1.2 p.2)) :=
      G.v_meas.comp (measurable_fst.fst.prodMk (d.2.1.comp (measurable_fst.snd.prodMk measurable_snd)))
    exact (h.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure unitInterval))).measurable
  have hWb : ∀ θ m, |Wf θ m| ≤ B := by
    intro θ m
    have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure unitInterval))
      (f := fun z => G.v θ (d.1 m z)) (C := B)
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact (hB _ _).2)
    simpa using h
  refine ⟨d, ⟨⟨measurable_const, fun k => measurable_snd.fst.prodMk measurable_const⟩, ?_⟩, ?_⟩
  · -- incentive compatibility of `S(A)`
    intro F hF σ' hσ'
    have hrec : (repeatDirect G d).recom.Feasible :=
      ⟨measurable_const, fun k => measurable_snd.fst.prodMk measurable_const⟩
    rw [futileAux_au_one G d σ' hσ' F, futileAux_au_one G d _ hrec F]
    have hmr : ∀ a : (Fin 1 → Θ) × unitInterval × (Fin 1 → unitInterval),
        futileAux_mrep G d (repeatDirect G d).recom F a = (a.1 0, true) := by
      intro a
      unfold futileAux_mrep
      have hne : ¬ ((repeatDirect G d).recom.s0 F a.2.1 = false) := by intro h; cases h
      exact if_neg hne
    simp_rw [hmr]
    have hi : ∀ g : (Fin 1 → Θ) × unitInterval × (Fin 1 → unitInterval) → Θ × Bool, Measurable g →
        Integrable (fun a => Wf (a.1 0) (g a)) ((Measure.pi fun _ : Fin 1 => F).prod
          ((volume : Measure unitInterval).prod (Measure.pi fun _ : Fin 1 => (volume : Measure unitInterval)))) :=
      fun g hg => Integrable.of_bound
        (hWm.comp (((measurable_pi_apply 0).comp measurable_fst).prodMk hg)).aestronglyMeasurable B
        (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hWb _ _)
    exact integral_mono (hi _ (futileAux_mrep_meas G d σ' hσ' F))
      (hi _ (((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_const))
      (fun a => hWle _ _)
  · -- principal utility identity
    intro θ
    rw [futileAux_pu_one G d (Measure.dirac θ), integral_dirac, hd1, hWu θ θ, hPU]
    field_simp
