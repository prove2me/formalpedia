-- Prove2me | solution 1 for FutileDynamics.StaticOpt.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T06:25:35.260643+00:00
-- url     : https://prove2.me/submissions/c98b13d5-a4cf-4f5f-b51b-7f47ce47befc

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model
import Theorems.Thm_FutileDynamics_StaticOpt_lemma_2
import Theorems.Thm_FutileDynamics_StaticOpt_lemma_3
import Theorems.Thm_FutileDynamics_StaticOpt_lemma_5

open MeasureTheory FutileDynamics.StaticOpt

/-- Principal utilities against a probability distribution are uniformly bounded above. -/
lemma futileAux_pu_bdd {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] (G : Game Θ Ω)
    (F : Measure Θ) [IsProbabilityMeasure F] (T : ℕ) :
    ∃ C : ℝ, ∀ (A : DynMech Θ Ω) (σ : Strategy Θ Ω A.M0 A.M), principalUtility G A σ F T ≤ C := by
  obtain ⟨B, hB⟩ := G.bdd
  refine ⟨T * B, fun A σ => ?_⟩
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
  exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at h)

/-- The single-round regret of an IC single-round direct mechanism at a point mass is nonnegative. -/
lemma futileAux_regret_nonneg {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω]
    [StandardBorelSpace Θ] (G : Game Θ Ω) (d : DirectRule G) (hd : SingleRoundIC G d) (θ : Θ) :
    0 ≤ regret G (repeatDirect G d) (Measure.dirac θ) 1 := by
  unfold regret OPT
  obtain ⟨C, hC⟩ := futileAux_pu_bdd G (Measure.dirac θ) 1
  have hb : BddAbove {r : ℝ | ∃ A : DynMech Θ Ω, IsIC G A 1 ∧
      r = principalUtility G A A.recom (Measure.dirac θ) 1} := by
    refine ⟨C, ?_⟩
    rintro r ⟨A, -, rfl⟩
    exact hC A A.recom
  have := le_csSup hb ⟨repeatDirect G d, hd, rfl⟩
  linarith

lemma futileAux_sup_nonneg {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω]
    [StandardBorelSpace Θ] (G : Game Θ Ω) (d : DirectRule G) (hd : SingleRoundIC G d) :
    0 ≤ ⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1 :=
  Real.iSup_nonneg fun θ => futileAux_regret_nonneg G d hd θ

theorem solution {Θ Ω : Type} [MeasurableSpace Θ] [MeasurableSpace Ω] [StandardBorelSpace Θ] [Nonempty Θ]
    (G : Game Θ Ω) (𝓕 : Set (Measure Θ)) (h𝓕 : ∀ F ∈ 𝓕, IsProbabilityMeasure F) (T : ℕ) (hT : 0 < T)
    (h1 : Assumption1 𝓕) (h2 : Assumption2 G 𝓕 T) :
    minimaxRegret G 𝓕 T = T * singleRoundValue G ∧
    (∀ ε : ℝ, 0 ≤ ε → ∀ d : DirectRule G, SingleRoundIC G d →
      (⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1) ≤ singleRoundValue G + ε / T →
      worstRegret G (repeatDirect G d) 𝓕 T ≤ minimaxRegret G 𝓕 T + ε) ∧
    ((∃ A : DynMech Θ Ω, IsIC G A T ∧ worstRegret G A 𝓕 T = minimaxRegret G 𝓕 T) ↔
      (∃ d : DirectRule G, SingleRoundIC G d ∧
        (⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1) = singleRoundValue G)) := by
  have L2 := lemma_2 G 𝓕 h𝓕 T hT h1
  have L3 := lemma_3 G 𝓕 h𝓕 T hT h2
  have L5 := lemma_5 G T hT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  -- notation
  set sup : DirectRule G → ℝ := fun d => ⨆ θ : Θ, regret G (repeatDirect G d) (Measure.dirac θ) 1
    with hsup
  set Sset : Set ℝ := sup '' {d | SingleRoundIC G d} with hSset
  set Mset : Set ℝ := {r : ℝ | ∃ A : DynMech Θ Ω, IsIC G A T ∧ r = worstRegret G A 𝓕 T} with hMset
  have hV : singleRoundValue G = sInf Sset := rfl
  have hM : minimaxRegret G 𝓕 T = sInf Mset := rfl
  have hSbdd : BddBelow Sset := by
    refine ⟨0, ?_⟩
    rintro r ⟨d, hd, rfl⟩
    exact futileAux_sup_nonneg G d hd
  have hVle : ∀ d, SingleRoundIC G d → singleRoundValue G ≤ sup d := fun d hd =>
    csInf_le hSbdd ⟨d, hd, rfl⟩
  -- every element of the minimax set is at least `T * V`
  have hMlow : ∀ r ∈ Mset, (T : ℝ) * singleRoundValue G ≤ r := by
    rintro r ⟨A, hA, rfl⟩
    obtain ⟨d, hd, hle⟩ := L2 A hA
    calc (T : ℝ) * singleRoundValue G ≤ T * sup d :=
          mul_le_mul_of_nonneg_left (hVle d hd) hTpos.le
      _ ≤ _ := hle
  have hMbdd : BddBelow Mset := ⟨_, hMlow⟩
  have hMle : ∀ d, SingleRoundIC G d → minimaxRegret G 𝓕 T ≤ worstRegret G (repeatDirect G d) 𝓕 T :=
    fun d hd => csInf_le hMbdd ⟨repeatDirect G d, (L5 d hd).1, rfl⟩
  -- Part 1
  have P1 : minimaxRegret G 𝓕 T = T * singleRoundValue G := by
    by_cases hne : ∃ d : DirectRule G, SingleRoundIC G d
    · obtain ⟨d0, hd0⟩ := hne
      apply le_antisymm
      · -- minimaxRegret / T ≤ sup d for all d
        have key : minimaxRegret G 𝓕 T / T ≤ singleRoundValue G := by
          rw [hV]
          apply le_csInf (⟨sup d0, d0, hd0, rfl⟩ : Sset.Nonempty)
          rintro r ⟨d, hd, rfl⟩
          rw [div_le_iff₀ hTpos, mul_comm]
          exact (hMle d hd).trans (L3 d hd)
        rw [div_le_iff₀ hTpos] at key
        linarith
      · rw [hM]
        exact le_csInf (⟨_, repeatDirect G d0, (L5 d0 hd0).1, rfl⟩ : Mset.Nonempty) hMlow
    · have hS : Sset = ∅ := by
        rw [hSset, Set.image_eq_empty]
        ext d; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hd => hne ⟨d, hd⟩
      have hMe : Mset = ∅ := by
        ext r; simp only [hMset, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨A, hA, -⟩
        obtain ⟨d, hd, -⟩ := L2 A hA
        exact hne ⟨d, hd⟩
      rw [hV, hM, hS, hMe, Real.sInf_empty]; simp
  refine ⟨P1, ?_, ?_⟩
  · -- Part 2
    intro ε hε d hd hsd
    calc worstRegret G (repeatDirect G d) 𝓕 T ≤ T * sup d := L3 d hd
      _ ≤ T * (singleRoundValue G + ε / T) := mul_le_mul_of_nonneg_left hsd hTpos.le
      _ = minimaxRegret G 𝓕 T + ε := by rw [P1]; field_simp
  · -- Part 3
    constructor
    · rintro ⟨A, hA, hAeq⟩
      obtain ⟨d, hd, hle⟩ := L2 A hA
      refine ⟨d, hd, le_antisymm ?_ (hVle d hd)⟩
      have : (T : ℝ) * sup d ≤ T * singleRoundValue G := by
        rw [← P1, ← hAeq]; exact hle
      exact le_of_mul_le_mul_left this hTpos
    · rintro ⟨d, hd, hdeq⟩
      refine ⟨repeatDirect G d, (L5 d hd).1, le_antisymm ?_ (hMle d hd)⟩
      calc worstRegret G (repeatDirect G d) 𝓕 T ≤ T * sup d := L3 d hd
        _ = minimaxRegret G 𝓕 T := by rw [P1]; simp only [hsup] at hdeq ⊢; rw [hdeq]
