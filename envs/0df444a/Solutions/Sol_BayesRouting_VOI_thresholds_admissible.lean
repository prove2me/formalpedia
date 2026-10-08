-- Prove2me | solution 1 for BayesRouting.VOI.thresholds_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T22:13:48.86522+00:00
-- url     : https://prove2.me/submissions/9e26d3ec-eedc-4b4f-89c2-e9aca2444731

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential
import Definitions.Def_BayesRouting_VOI_Flows
import Definitions.Def_BayesRouting_VOI_Pairwise

open Finset BayesRouting.VOI in
theorem BayesRouting_VOI_impact_nonneg_aux {I : Type} [Fintype I] [DecidableEq I] {T : I → Type}
    [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type}
    [Fintype S] [Fintype E] [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (i : I) (f : R → ((k : I) → T k) → ℝ) (hf : f ∈ flowBase G) :
    0 ≤ impact G i f := by
  obtain ⟨_, hsum, _⟩ := hf
  let t : (k : I) → T k := fun k => Classical.arbitrary (T k)
  unfold impact
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ t))
  have h1 : ∑ r, univ.inf' univ_nonempty (fun ti : T i => f r (Function.update t i ti))
      ≤ ∑ r, f r t := by
    apply Finset.sum_le_sum
    intro r _
    calc univ.inf' univ_nonempty (fun ti : T i => f r (Function.update t i ti))
        ≤ f r (Function.update t i (t i)) := Finset.inf'_le _ (Finset.mem_univ (t i))
      _ = f r t := by rw [Function.update_eq_self]
  have h2 := hsum t
  linarith

open Finset BayesRouting.VOI in
theorem BayesRouting_VOI_rest_aux {I : Type} [Fintype I] [DecidableEq I]
    (i j : I) (hij : i ≠ j) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I) :
    1 - restSize lam i j = lam i + lam j := by
  obtain ⟨_, hs⟩ := hlam
  unfold restSize
  have hj : j ∈ univ.erase i := Finset.mem_erase.2 ⟨fun h => hij h.symm, Finset.mem_univ j⟩
  have e1 := Finset.add_sum_erase (univ : Finset I) lam (Finset.mem_univ i)
  have e2 := Finset.add_sum_erase (univ.erase i) lam hj
  linarith

open BayesRouting.VOI in
theorem solution {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (i j : I) (hij : i ≠ j) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I)
    (hi : 0 < lam i) (hj : 0 < lam j) :
    0 ≤ lowThr G lam i j ∧ lowThr G lam i j ≤ highThr G lam i j ∧
      highThr G lam i j ≤ 1 - restSize lam i j := by
  have hD := G.D_pos
  have hrest := BayesRouting_VOI_rest_aux i j hij lam hlam
  set c := 1 - restSize lam i j with hc
  have hc0 : 0 ≤ c := by rw [hrest]; linarith
  have hopt : ∀ f ∈ pairOptimal G lam i j,
      0 ≤ impact G i f ∧ 0 ≤ impact G j f ∧ impact G i f + impact G j f ≤ c * G.D := by
    intro f hf
    have hf' : f ∈ pairFeasible G lam i j := hf.1
    exact ⟨BayesRouting_VOI_impact_nonneg_aux G i f hf'.1,
      BayesRouting_VOI_impact_nonneg_aux G j f hf'.1, hf'.2.2⟩
  have hlow0 : 0 ≤ sInf (impact G i '' pairOptimal G lam i j) := by
    apply Real.sInf_nonneg
    rintro x ⟨f, hf, rfl⟩
    exact (hopt f hf).1
  have hhigh : sSup ((fun f => c * G.D - impact G j f) '' pairOptimal G lam i j) ≤ c * G.D := by
    apply Real.sSup_le
    · rintro x ⟨f, hf, rfl⟩
      have := (hopt f hf).2.1
      simp only
      linarith
    · positivity
  have hDinv : 0 < 1 / G.D := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold lowThr
    exact mul_nonneg hDinv.le hlow0
  · unfold lowThr highThr
    rw [← hc]
    apply mul_le_mul_of_nonneg_left _ hDinv.le
    rcases (pairOptimal G lam i j).eq_empty_or_nonempty with h | ⟨f, hf⟩
    · simp [h]
    · have hb : BddBelow (impact G i '' pairOptimal G lam i j) := by
        refine ⟨0, ?_⟩
        rintro x ⟨g, hg, rfl⟩
        exact (hopt g hg).1
      have ha : BddAbove ((fun f => c * G.D - impact G j f) '' pairOptimal G lam i j) := by
        refine ⟨c * G.D, ?_⟩
        rintro x ⟨g, hg, rfl⟩
        have := (hopt g hg).2.1
        simp only
        linarith
      have h1 := csInf_le hb (Set.mem_image_of_mem _ hf)
      have h2 := le_csSup ha (Set.mem_image_of_mem (fun f => c * G.D - impact G j f) hf)
      have h3 := (hopt f hf).2.2
      linarith
  · unfold highThr
    rw [← hc]
    calc 1 / G.D * sSup ((fun f => c * G.D - impact G j f) '' pairOptimal G lam i j)
        ≤ 1 / G.D * (c * G.D) := mul_le_mul_of_nonneg_left hhigh hDinv.le
      _ = c := by field_simp
