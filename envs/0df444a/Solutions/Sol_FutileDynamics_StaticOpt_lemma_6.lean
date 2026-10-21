-- Prove2me | solution 1 for FutileDynamics.StaticOpt.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T06:32:06.776526+00:00
-- url     : https://prove2.me/submissions/3ef624e3-0e7d-4ae9-8d5e-d084302c0acc

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model

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

theorem solution {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (𝓕 : Set (Measure Θ)) (h𝓕 : ∀ F ∈ 𝓕, IsProbabilityMeasure F) :
    ∀ d : DirectRule G, SingleRoundIC G d →
      sSup ((fun F => (∫ θ, OPT G (Measure.dirac θ) 1 ∂F) -
          principalUtility G (repeatDirect G d) (repeatDirect G d).recom F 1) '' 𝓕) ≤
        ⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1 := by
  intro d hd
  obtain ⟨B, hB, hB0⟩ := futileAux_B G
  set sup := ⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1 with hsup
  have hsup0 : 0 ≤ sup := Real.iSup_nonneg fun θ =>
    futileAux_regret_nonneg G B hB hB0 (Measure.dirac θ) 1 _ hd
  set g : Θ → ℝ := fun θ => ∫ z, G.u θ (d.1 (θ, true) z) ∂(volume : Measure unitInterval) with hg
  set O : Θ → ℝ := fun θ => OPT G (Measure.dirac θ) 1 with hO
  have hgm : Measurable g := by
    have h1 : Measurable (fun p : Θ × unitInterval => d.1 (p.1, true) p.2) :=
      d.2.1.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    have h2 : Measurable (fun p : Θ × unitInterval => G.u p.1 (d.1 (p.1, true) p.2)) :=
      G.u_meas.comp (measurable_fst.prodMk h1)
    exact (h2.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure unitInterval))).measurable
  have hgb : ∀ θ, |g θ| ≤ B := by
    intro θ
    have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure unitInterval))
      (f := fun z => G.u θ (d.1 (θ, true) z)) (C := B)
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact (hB _ _).1)
    simpa using h
  have hreg : ∀ θ, O θ - g θ ≤ sup := by
    intro θ
    have hbdd : BddAbove (Set.range fun θ : Θ => regret G (repeatDirect G d) (Measure.dirac θ) 1) := by
      refine ⟨2 * ((1 : ℕ) * B), ?_⟩
      rintro r ⟨θ', rfl⟩
      exact (le_abs_self _).trans (futileAux_regret_abs G B hB hB0 _ 1 _)
    have := le_ciSup hbdd θ
    have hpu := futileAux_pu_one G d (Measure.dirac θ)
    rw [integral_dirac] at hpu
    simp only [regret] at this
    rw [hpu] at this
    exact this
  have hOnn : ∀ θ, 0 ≤ O θ := fun θ => futileAux_opt_nonneg G (Measure.dirac θ) 1
  have each : ∀ F : Measure Θ, IsProbabilityMeasure F →
      (∫ θ, O θ ∂F) - principalUtility G (repeatDirect G d) (repeatDirect G d).recom F 1 ≤ sup := by
    intro F hF
    rw [futileAux_pu_one G d F]
    have hgi : Integrable g F := Integrable.of_bound hgm.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun θ => by rw [Real.norm_eq_abs]; exact hgb θ)
    by_cases hOi : Integrable O F
    · rw [← integral_sub hOi hgi]
      calc ∫ θ, (O θ - g θ) ∂F ≤ ∫ _θ, sup ∂F :=
            integral_mono (hOi.sub hgi) (integrable_const _) hreg
        _ = sup := by simp
    · rw [integral_undef hOi, zero_sub, ← integral_neg]
      calc ∫ θ, -g θ ∂F ≤ ∫ _θ, sup ∂F :=
            integral_mono hgi.neg (integrable_const _) (fun θ => by linarith [hreg θ, hOnn θ])
        _ = sup := by simp
  rcases 𝓕.eq_empty_or_nonempty with he | hne
  · rw [he, Set.image_empty, Real.sSup_empty]; exact hsup0
  · exact csSup_le (hne.image _) (fun r ⟨F, hF, hr⟩ => hr ▸ each F (h𝓕 F hF))
