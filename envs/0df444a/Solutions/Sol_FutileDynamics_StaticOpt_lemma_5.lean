-- Prove2me | solution 1 for FutileDynamics.StaticOpt.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T06:39:09.153561+00:00
-- url     : https://prove2.me/submissions/70e376f0-f2eb-42f0-8e94-a4465557f7b3

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model
import Theorems.Thm_FutileDynamics_StaticOpt_claim_1

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

/-- Under truthful reporting, round `j + 1` of `S^{×T}` has outcome `π̃((θ_{j+1}, true), z_{j+1})`. -/
lemma futileAux_hist_truth {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (d : DirectRule G) (F : Measure Θ) (T : ℕ) (ξ : Noise Θ T) :
    ∀ k (hk : k ≤ T) (j : Fin k), (hist G (repeatDirect G d) (repeatDirect G d).recom F T ξ k hk).2 j =
      d.1 (ξ.1 ⟨j, by omega⟩, true) (ξ.2.2.2 ⟨j, by omega⟩) := by
  intro k
  induction k with
  | zero => intro hk j; exact j.elim0
  | succ k ih =>
    intro hk j
    rw [hist]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [Fin.snoc_last, repeatDirect]
    · simp only [Fin.snoc_castSucc]
      exact ih _ i

lemma futileAux_outcome_truth {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (d : DirectRule G) (F : Measure Θ) (T : ℕ) (ξ : Noise Θ T) (k : Fin T) :
    outcome G (repeatDirect G d) (repeatDirect G d).recom F T ξ k = d.1 (ξ.1 k, true) (ξ.2.2.2 k) := by
  unfold outcome
  rw [futileAux_hist_truth]

/-- The round-`k` marginal of `noiseLaw F T` on `(θ_k, z_k)` is `F ⊗ λ`. -/
lemma futileAux_marginal {Θ : Type} [MeasurableSpace Θ] (F : Measure Θ) [IsProbabilityMeasure F]
    (T : ℕ) (k : Fin T) (φ : Θ → unitInterval → ℝ) (hφ : Measurable (Function.uncurry φ)) (B : ℝ)
    (hB : ∀ θ z, |φ θ z| ≤ B) :
    ∫ ξ, φ (ξ.1 k) (ξ.2.2.2 k) ∂(noiseLaw F T) =
      ∫ θ, ∫ z, φ θ z ∂(volume : Measure unitInterval) ∂F := by
  unfold noiseLaw
  have hmeas : Measurable (fun ξ : Noise Θ T => φ (ξ.1 k) (ξ.2.2.2 k)) :=
    hφ.comp (g := Function.uncurry φ) (f := fun ξ : Noise Θ T => (ξ.1 k, ξ.2.2.2 k))
      (((measurable_pi_apply k).comp measurable_fst).prodMk
      ((measurable_pi_apply k).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
  rw [integral_prod (f := fun ξ : Noise Θ T => φ (ξ.1 k) (ξ.2.2.2 k))]
  · have inner : ∀ x : Fin T → Θ,
        ∫ y, φ (x k) (y.2.2 k) ∂((volume : Measure unitInterval).prod
          ((Measure.pi fun _ : Fin T => (volume : Measure unitInterval)).prod
            (Measure.pi fun _ : Fin T => (volume : Measure unitInterval)))) =
          ∫ z, φ (x k) z ∂(volume : Measure unitInterval) := by
      intro x
      rw [integral_fun_snd (f := fun w : (Fin T → unitInterval) × (Fin T → unitInterval) =>
        φ (x k) (w.2 k))]
      rw [integral_fun_snd (f := fun w : Fin T → unitInterval => φ (x k) (w k))]
      simp only [probReal_univ, one_smul]
      have hmp := measurePreserving_eval (fun _ : Fin T => (volume : Measure unitInterval)) k
      have h := integral_map (μ := Measure.pi fun _ : Fin T => (volume : Measure unitInterval))
        hmp.measurable.aemeasurable (f := fun z => φ (x k) z)
        (by rw [hmp.map_eq]; exact (hφ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      rw [hmp.map_eq] at h
      exact h.symm
    simp_rw [inner]
    have hmp := measurePreserving_eval (fun _ : Fin T => F) k
    have hg : Measurable (fun θ => ∫ z, φ θ z ∂(volume : Measure unitInterval)) :=
      (hφ.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure unitInterval))).measurable
    conv_rhs => rw [← hmp.map_eq]
    rw [integral_map hmp.measurable.aemeasurable hg.aestronglyMeasurable]
  · refine Integrable.of_bound hmeas.aestronglyMeasurable B (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]; exact hB _ _

/-- Total truthful utility of `S^{×T}` for a bounded measurable utility `w`. -/
lemma futileAux_truth_total {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ]
    (G : Game Θ Ω) (d : DirectRule G) (F : Measure Θ) [IsProbabilityMeasure F] (T : ℕ)
    (w : Θ → Ω → ℝ) (hw : Measurable (Function.uncurry w)) (B : ℝ) (hB : ∀ θ ω, |w θ ω| ≤ B) :
    ∫ ξ, ∑ k : Fin T, w (ξ.1 k) (outcome G (repeatDirect G d) (repeatDirect G d).recom F T ξ k)
        ∂(noiseLaw F T) =
      T * ∫ θ, ∫ z, w θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) ∂F := by
  let φ : Θ → unitInterval → ℝ := fun θ z => w θ (d.1 (θ, true) z)
  have hφm : Measurable (Function.uncurry φ) := by
    have h1 : Measurable (fun p : Θ × unitInterval => d.1 (p.1, true) p.2) :=
      d.2.1.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    exact hw.comp (measurable_fst.prodMk h1)
  simp_rw [futileAux_outcome_truth]
  rw [integral_finsetSum]
  · calc ∑ k : Fin T, ∫ ξ, w (ξ.1 k) (d.1 (ξ.1 k, true) (ξ.2.2.2 k)) ∂(noiseLaw F T)
        = ∑ _k : Fin T, ∫ θ, ∫ z, φ θ z ∂(volume : Measure unitInterval) ∂F :=
          Finset.sum_congr rfl fun k _ => futileAux_marginal F T k φ hφm B (fun θ z => hB _ _)
      _ = _ := by simp [φ]
  · intro k _
    have hmeas : Measurable (fun ξ : Noise Θ T => φ (ξ.1 k) (ξ.2.2.2 k)) :=
      hφm.comp (g := Function.uncurry φ) (f := fun ξ : Noise Θ T => (ξ.1 k, ξ.2.2.2 k))
        (((measurable_pi_apply k).comp measurable_fst).prodMk
        ((measurable_pi_apply k).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
    have : IsProbabilityMeasure (noiseLaw F T) := by unfold noiseLaw; infer_instance
    exact Integrable.of_bound hmeas.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hB _ _)

theorem solution {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (T : ℕ) (hT : 0 < T) :
    ∀ d : DirectRule G, SingleRoundIC G d → IsIC G (repeatDirect G d) T ∧
      ∀ F : Measure Θ, IsProbabilityMeasure F →
        principalUtility G (repeatDirect G d) (repeatDirect G d).recom F T =
          T * principalUtility G (repeatDirect G d) (repeatDirect G d).recom F 1 := by
  intro d hd
  obtain ⟨B, hB, hB0⟩ := futileAux_B G
  have totU : ∀ (F : Measure Θ) [IsProbabilityMeasure F] (n : ℕ),
      principalUtility G (repeatDirect G d) (repeatDirect G d).recom F n =
        n * ∫ θ, ∫ z, G.u θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) ∂F :=
    fun F _ n => futileAux_truth_total G d F n G.u G.u_meas B (fun θ ω => (hB θ ω).1)
  have totV : ∀ (F : Measure Θ) [IsProbabilityMeasure F] (n : ℕ),
      agentUtility G (repeatDirect G d) (repeatDirect G d).recom F n =
        n * ∫ θ, ∫ z, G.v θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) ∂F :=
    fun F _ n => futileAux_truth_total G d F n G.v G.v_meas B (fun θ ω => (hB θ ω).2)
  refine ⟨⟨hd.1, fun F hF σ' hσ' => ?_⟩, fun F hF => by rw [totU F T, totU F 1]; simp⟩
  have hN : IsProbabilityMeasure (noiseLaw F T) := by unfold noiseLaw; infer_instance
  -- split the agent's total utility into per-round utilities
  have hsplit : agentUtility G (repeatDirect G d) σ' F T =
      ∑ k : Fin T, roundAgentUtility G (repeatDirect G d) σ' F T k := by
    unfold agentUtility roundAgentUtility
    rw [integral_finsetSum]
    intro k _
    have hh := futileAux_hist_meas G (repeatDirect G d) σ' hσ' F T T le_rfl
    have hmeas : Measurable (fun ξ : Noise Θ T => G.v (ξ.1 k) (outcome G (repeatDirect G d) σ' F T ξ k)) :=
      G.v_meas.comp (g := Function.uncurry G.v)
        (f := fun ξ : Noise Θ T => (ξ.1 k, outcome G (repeatDirect G d) σ' F T ξ k))
        (((measurable_pi_apply k).comp measurable_fst).prodMk ((measurable_pi_apply k).comp hh.snd))
    exact Integrable.of_bound hmeas.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact (hB _ _).2)
  have hround : ∀ k : Fin T, roundAgentUtility G (repeatDirect G d) σ' F T k ≤
      agentUtility G (repeatDirect G d) (repeatDirect G d).recom F 1 := by
    intro k
    obtain ⟨σ'', hσ'', hV, -⟩ := claim_1 G T hT d F hF σ' hσ' k
    rw [← hV]
    exact hd.2 F hF σ'' hσ''
  rw [hsplit, totV F T]
  calc ∑ k : Fin T, roundAgentUtility G (repeatDirect G d) σ' F T k
      ≤ ∑ _k : Fin T, agentUtility G (repeatDirect G d) (repeatDirect G d).recom F 1 :=
        Finset.sum_le_sum fun k _ => hround k
    _ = _ := by rw [totV F 1]; simp
