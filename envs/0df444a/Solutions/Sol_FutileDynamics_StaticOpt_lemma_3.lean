-- Prove2me | solution 1 for FutileDynamics.StaticOpt.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T06:28:32.197886+00:00
-- url     : https://prove2.me/submissions/3dd0bba8-980f-4b5b-93ed-632cb69b97c4

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model
import Theorems.Thm_FutileDynamics_StaticOpt_lemma_5
import Theorems.Thm_FutileDynamics_StaticOpt_lemma_6
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
    (G : Game Θ Ω) (𝓕 : Set (Measure Θ)) (h𝓕 : ∀ F ∈ 𝓕, IsProbabilityMeasure F) (T : ℕ) (hT : 0 < T) (h2 : Assumption2 G 𝓕 T) :
    ∀ d : DirectRule G, SingleRoundIC G d →
      worstRegret G (repeatDirect G d) 𝓕 T ≤
        T * ⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1 := by
  intro d hd
  obtain ⟨B, hB, hB0⟩ := futileAux_B G
  have L5 := (lemma_5 G T hT d hd).2
  have P1 := proposition_1 G T hT
  set sup := ⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1 with hsup
  have hsup0 : 0 ≤ sup := Real.iSup_nonneg fun θ =>
    futileAux_regret_nonneg G B hB hB0 (Measure.dirac θ) 1 _ hd
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have each : ∀ F ∈ 𝓕, regret G (repeatDirect G d) F T ≤ T * sup := by
    intro F hF
    haveI := h𝓕 F hF
    have L6 := lemma_6 G {F} (fun F' hF' => by rw [Set.mem_singleton_iff.1 hF']; infer_instance) d hd
    rw [Set.image_singleton, csSup_singleton] at L6
    have hint : (∫ θ, OPT G (Measure.dirac θ) T ∂F) = T * ∫ θ, OPT G (Measure.dirac θ) 1 ∂F := by
      rw [← integral_const_mul]; congr 1; funext θ; exact P1 θ
    unfold regret
    rw [L5 F inferInstance]
    have := h2 F hF
    calc OPT G F T - T * principalUtility G (repeatDirect G d) (repeatDirect G d).recom F 1
        ≤ (∫ θ, OPT G (Measure.dirac θ) T ∂F) -
            T * principalUtility G (repeatDirect G d) (repeatDirect G d).recom F 1 := by linarith
      _ = T * ((∫ θ, OPT G (Measure.dirac θ) 1 ∂F) -
            principalUtility G (repeatDirect G d) (repeatDirect G d).recom F 1) := by rw [hint]; ring
      _ ≤ T * sup := mul_le_mul_of_nonneg_left L6 hT0
  unfold worstRegret
  rcases 𝓕.eq_empty_or_nonempty with he | hne
  · rw [he, Set.image_empty, Real.sSup_empty]; exact mul_nonneg hT0 hsup0
  · exact csSup_le (hne.image _) (fun r ⟨F, hF, hr⟩ => hr ▸ each F hF)
