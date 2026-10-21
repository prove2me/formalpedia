-- Prove2me | solution 1 for FutileDynamics.StaticOpt.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T06:27:41.415886+00:00
-- url     : https://prove2.me/submissions/4e1f93df-41e2-42c9-917a-281f54efe5b0

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model
import Theorems.Thm_FutileDynamics_StaticOpt_lemma_4
import Theorems.Thm_FutileDynamics_StaticOpt_proposition_1

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

theorem solution {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (𝓕 : Set (Measure Θ)) (h𝓕 : ∀ F ∈ 𝓕, IsProbabilityMeasure F) (T : ℕ) (hT : 0 < T) (h1 : Assumption1 𝓕) :
    ∀ A : DynMech Θ Ω, IsIC G A T → ∃ d : DirectRule G, SingleRoundIC G d ∧
      T * (⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1) ≤ worstRegret G A 𝓕 T := by
  intro A hA
  obtain ⟨d, hd, hPU⟩ := lemma_4 G T hT A hA
  have P1 := proposition_1 G T hT
  obtain ⟨B, hB, hB0⟩ := futileAux_B G
  refine ⟨d, hd, ?_⟩
  have key : ∀ θ : Θ, (T : ℝ) * regret G (repeatDirect G d) (Measure.dirac θ) 1 =
      regret G A (Measure.dirac θ) T := by
    intro θ; unfold regret; rw [P1 θ, hPU θ]; ring
  have hbdd : BddAbove ((fun F => regret G A F T) '' 𝓕) := by
    refine ⟨2 * (T * B), ?_⟩
    rintro r ⟨F, hF, rfl⟩
    haveI := h𝓕 F hF
    exact (le_abs_self _).trans (futileAux_regret_abs G B hB hB0 F T A)
  rw [Real.mul_iSup_of_nonneg (Nat.cast_nonneg _)]
  refine ciSup_le fun θ => ?_
  rw [key θ]
  exact le_csSup hbdd ⟨_, h1 θ, rfl⟩
