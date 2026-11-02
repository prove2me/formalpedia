-- Prove2me | solution 1 for FKZAvg.WStar.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T15:16:42.804198+00:00
-- url     : https://prove2.me/submissions/78741c04-e823-429c-a206-da3cba25e6e5

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions
import Theorems.Thm_FKZAvg_WStar_theorem_1
import Theorems.Thm_FKZAvg_WStar_lemma_6
import Theorems.Thm_FKZAvg_WStar_lemma_7
import Theorems.Thm_FKZAvg_WStar_lemma_2_fullW
import Theorems.Thm_FKZAvg_WStar_lemma_3_lsc

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt FKZAvg.WStar

theorem solution {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M)
    (hW : CondWStar M) (hB : CondBLow M) :
    (∃ φ : X → A, ∃ hφ : IsStationary M φ, Ineq9 M (uAvg M) φ ∧ Eq10 M hφ) ∧
    (LowerSemicontinuous (uAvg M) ∧ ∀ x, uAvg M x ≠ ⊤) ∧
    ((∀ x, (AsupStar M x).Nonempty) ∧
      MeasurableSet {p : X × A | p.2 ∈ AsupStar M p.1} ∧
      ∀ x, IsCompact (AsupStar M x)) ∧
    (∀ φ : X → A, ∀ hφ : IsStationary M φ, (∀ x, φ x ∈ AsupStar M x) →
      IsAvgOpt M hφ ∧ Ineq9 M (uAvg M) φ) ∧
    ((∃ φ : X → A, IsStationary M φ ∧ ∀ x, φ x ∈ AsubStar M (uAvg M) x) ∧
      ∀ x, AsubStar M (uAvg M) x ⊆ AsupStar M x) ∧
    (CondWu M → InfCompactOn (uAvg M) Set.univ) := by
  -- Lemma 6: statements (a) and (e)
  obtain ⟨⟨hlsc, hfin, -⟩, -, h6e⟩ := lemma_6 M hsel hB
  have hmeas : Measurable (uAvg M) := hlsc.measurable
  -- Lemma 7: the optimality inequality (31), minimum attained
  have h7 := lemma_7 M hsel hW hB
  have hη : ∀ x a, eta M (uAvg M) 1 x a =
      M.toMDP.cost x a + ∫⁻ y, uAvg M y ∂(M.toMDP.q (x, a)) := by
    intro x a; simp [eta]
  -- inclusion A_*(x) ⊆ A*(x)
  have hincl : ∀ x, AsubStar M (uAvg M) x ⊆ AsupStar M x := by
    intro x a ha
    refine ⟨ha.1, ?_⟩
    rw [← hη, ← ha.2]
    exact (h7 x).2
  -- a stationary selector of A_* (Lemma 3, corrected), or the empty map when 𝕏 = ∅
  have hsub : ∃ φ : X → A, IsStationary M φ ∧ ∀ x, φ x ∈ AsubStar M (uAvg M) x := by
    rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
    · obtain ⟨φ, hφ⟩ := hsel
      exact ⟨φ, hφ, fun x => isEmptyElim x⟩
    · have hL : InL (uAvg M) := ⟨hlsc, x₀, hfin x₀⟩
      obtain ⟨-, ⟨f, hf, hfeq⟩, -⟩ := lemma_3_lsc M hsel hW (uAvg M) hL
      exact ⟨f, hf, fun x => ⟨hf.2 x, hfeq x⟩⟩
  obtain ⟨φ₀, hφ₀, hφ₀sub⟩ := hsub
  have h9₀ : Ineq9 M (uAvg M) φ₀ := fun x => (hincl x (hφ₀sub x)).2
  obtain ⟨-, h10⟩ := theorem_1 M hsel hB.1 (uAvg M) hmeas hfin φ₀ hφ₀ h9₀
  -- w̄ = w* < ∞ (when 𝕏 is nonempty)
  refine ⟨⟨φ₀, hφ₀, h9₀, h10⟩, ⟨hlsc, hfin⟩, ⟨?_, ?_, ?_⟩, ?_, ⟨⟨φ₀, hφ₀, hφ₀sub⟩, hincl⟩, fun hWu => (h6e hWu).1.1⟩
  · intro x
    obtain ⟨⟨a, ha, haeq⟩, -⟩ := h7 x
    exact ⟨a, hincl x ⟨ha, haeq.symm⟩⟩
  · have h1 : Measurable (fun p : X × A =>
        M.toMDP.cost p.1 p.2 + ∫⁻ y, uAvg M y ∂(M.toMDP.q (p.1, p.2))) := by
      refine M.cost_meas.add ?_
      simpa using (hmeas.lintegral_kernel (κ := M.toMDP.q))
    have h2 : Measurable (fun p : X × A => gUpper M + uAvg M p.1) :=
      measurable_const.add (hmeas.comp measurable_fst)
    exact M.graph_meas.inter (measurableSet_le h1 h2)
  · intro x
    have hgU : gUpper M ≠ ⊤ := by
      rw [((h10 x).2.2.2)]; exact hB.1.ne
    have hfinL : gUpper M + uAvg M x ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hgU, hfin x⟩
    have hL : InL (uAvg M) := ⟨hlsc, x, hfin x⟩
    have hc := (lemma_2_fullW M hsel x).2 hW (uAvg M) hL 1 zero_le_one
      (gUpper M + uAvg M x).toNNReal
    convert hc using 1
    ext a
    simp only [AsupStar, Set.mem_ofPred_eq, ENNReal.coe_toNNReal hfinL, hη]
  · intro φ hφ hφA
    have h9 : Ineq9 M (uAvg M) φ := fun x => (hφA x).2
    exact ⟨(theorem_1 M hsel hB.1 (uAvg M) hmeas hfin φ hφ h9).1, h9⟩
