-- Prove2me | solution 1 for FutileDynamics.StaticOpt.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T06:29:21.880996+00:00
-- url     : https://prove2.me/submissions/e49e2a24-3dbe-4634-a97f-7ce6c8e153fe

import Mathlib
import Definitions.Def_FutileDynamics_StaticOpt_Model
import Theorems.Thm_FutileDynamics_StaticOpt_lemma_4
import Theorems.Thm_FutileDynamics_StaticOpt_lemma_5

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
    (G : Game Θ Ω) (T : ℕ) (hT : 0 < T) :
    ∀ θ : Θ, OPT G (Measure.dirac θ) T = T * OPT G (Measure.dirac θ) 1 := by
  intro θ
  obtain ⟨B, hB, hB0⟩ := futileAux_B G
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  set ST := {r : ℝ | ∃ A : DynMech Θ Ω, IsIC G A T ∧
    r = principalUtility G A A.recom (Measure.dirac θ) T} with hST
  set S1 := {r : ℝ | ∃ A : DynMech Θ Ω, IsIC G A 1 ∧
    r = principalUtility G A A.recom (Measure.dirac θ) 1} with hS1
  have hOT : OPT G (Measure.dirac θ) T = sSup ST := rfl
  have hO1 : OPT G (Measure.dirac θ) 1 = sSup S1 := rfl
  rcases S1.eq_empty_or_nonempty with he | hne
  · have heT : ST = ∅ := by
      ext r; simp only [hST, Set.mem_empty_iff_false, iff_false]
      rintro ⟨A, hA, -⟩
      obtain ⟨d, hd, -⟩ := lemma_4 G T hT A hA
      have : principalUtility G (repeatDirect G d) (repeatDirect G d).recom (Measure.dirac θ) 1 ∈ S1 :=
        ⟨_, hd, rfl⟩
      rw [he] at this; exact this
    rw [hOT, hO1, he, heT, Real.sSup_empty]; simp
  · obtain ⟨r1, A1, hA1, rfl⟩ := hne
    obtain ⟨d1, hd1, -⟩ := lemma_4 G 1 one_pos A1 hA1
    have hneT : ST.Nonempty := ⟨_, repeatDirect G d1, (lemma_5 G T hT d1 hd1).1, rfl⟩
    apply le_antisymm
    · rw [hOT]
      refine csSup_le hneT ?_
      rintro r ⟨A, hA, rfl⟩
      obtain ⟨d, hd, hPU⟩ := lemma_4 G T hT A hA
      rw [hPU θ]
      exact mul_le_mul_of_nonneg_left
        ((futileAux_opt G B hB hB0 (Measure.dirac θ) 1).2 _ hd) hTpos.le
    · have key : OPT G (Measure.dirac θ) 1 ≤ OPT G (Measure.dirac θ) T / T := by
        rw [hO1]
        refine csSup_le ⟨_, A1, hA1, rfl⟩ ?_
        rintro r ⟨A, hA, rfl⟩
        obtain ⟨d, hd, hPU⟩ := lemma_4 G 1 one_pos A hA
        obtain ⟨hICT, hPUT⟩ := lemma_5 G T hT d hd
        have h := (futileAux_opt G B hB hB0 (Measure.dirac θ) T).2 _ hICT
        rw [hPUT _ inferInstance] at h
        rw [hPU θ, le_div_iff₀ hTpos]
        simp only [Nat.cast_one, one_mul]
        linarith
      rw [le_div_iff₀ hTpos] at key
      linarith
