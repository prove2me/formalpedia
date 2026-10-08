-- Prove2me | solution 1 for DoubleGreedyUSM.Deterministic.tight_example
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-05T12:12:09.104353+00:00
-- url     : https://prove2.me/submissions/d87961ce-b258-4b74-b78e-ec99a58ab911

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_DoubleGreedyUSM_Deterministic_Algorithm1

open DoubleGreedyUSM.Deterministic

private def arc (a b : Fin 5) (S : Finset (Fin 5)) : ℝ :=
  if a ∈ S ∧ b ∉ S then 1 else 0

private theorem arc_nonneg (a b : Fin 5) (S : Finset (Fin 5)) : 0 ≤ arc a b S := by
  unfold arc
  split_ifs <;> norm_num

private theorem arc_submodular (a b : Fin 5) :
    NonmonotoneSubmod.Shared.Submodular (arc a b) := by
  intro S T
  by_cases haS : a ∈ S <;> by_cases hbS : b ∈ S <;>
    by_cases haT : a ∈ T <;> by_cases hbT : b ∈ T <;>
    simp [arc, haS, hbS, haT, hbT]

-- Figure 1: u₁ corresponds to 0, ..., u₅ to 4. The two dashed edges
-- point from u₁ to u₂/u₃ and have weight 1 - δ; the six other edges have weight 1.
private def tightFun (δ : ℝ) (S : Finset (Fin 5)) : ℝ :=
  (1 - δ) * (arc 0 1 S + arc 0 2 S) + arc 1 0 S + arc 2 0 S +
    arc 3 1 S + arc 3 2 S + arc 4 1 S + arc 4 2 S

private theorem tight_nonneg (δ : ℝ) (hδ : δ ≤ 1) (S : Finset (Fin 5)) :
    0 ≤ tightFun δ S := by
  have hw : 0 ≤ 1 - δ := sub_nonneg.mpr hδ
  have h01 := arc_nonneg 0 1 S
  have h02 := arc_nonneg 0 2 S
  have h10 := arc_nonneg 1 0 S
  have h20 := arc_nonneg 2 0 S
  have h31 := arc_nonneg 3 1 S
  have h32 := arc_nonneg 3 2 S
  have h41 := arc_nonneg 4 1 S
  have h42 := arc_nonneg 4 2 S
  unfold tightFun
  positivity

private theorem tight_submodular (δ : ℝ) (hδ : δ ≤ 1) :
    NonmonotoneSubmod.Shared.Submodular (tightFun δ) := by
  intro S T
  have h01 := arc_submodular 0 1 S T
  have h02 := arc_submodular 0 2 S T
  have h10 := arc_submodular 1 0 S T
  have h20 := arc_submodular 2 0 S T
  have h31 := arc_submodular 3 1 S T
  have h32 := arc_submodular 3 2 S T
  have h41 := arc_submodular 4 1 S T
  have h42 := arc_submodular 4 2 S T
  have hw := mul_le_mul_of_nonneg_left (add_le_add h01 h02) (sub_nonneg.mpr hδ)
  dsimp [tightFun]
  linear_combination hw + h10 + h20 + h31 + h32 + h41 + h42

private theorem tight_run (δ : ℝ) (hδ : 0 < δ) :
    state (tightFun δ) [0, 1, 2, 3, 4] 5 = ({1, 2, 3, 4}, {1, 2, 3, 4}) := by
  have huniv : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide
  have h0 : step (tightFun δ) (∅, Finset.univ) 0 = (∅, {1, 2, 3, 4}) := by
    have hn : ¬ removeGain (tightFun δ) (∅, Finset.univ) 0 ≤
        addGain (tightFun δ) (∅, Finset.univ) 0 := by
      norm_num [removeGain, addGain, tightFun, arc, huniv, Fin.ext_iff]
      linarith
    simp only [step, if_neg hn]
    norm_num [huniv, Fin.ext_iff]
  have h1 : step (tightFun δ) (∅, {1, 2, 3, 4}) 1 = ({1}, {1, 2, 3, 4}) := by
    norm_num [step, removeGain, addGain, tightFun, arc, Fin.ext_iff]
  have h2 : step (tightFun δ) ({1}, {1, 2, 3, 4}) 2 = ({1, 2}, {1, 2, 3, 4}) := by
    norm_num [step, removeGain, addGain, tightFun, arc, Fin.ext_iff] <;> decide
  have h3 : step (tightFun δ) ({1, 2}, {1, 2, 3, 4}) 3 =
      ({1, 2, 3}, {1, 2, 3, 4}) := by
    norm_num [step, removeGain, addGain, tightFun, arc, Fin.ext_iff] <;> decide
  have h4 : step (tightFun δ) ({1, 2, 3}, {1, 2, 3, 4}) 4 =
      ({1, 2, 3, 4}, {1, 2, 3, 4}) := by
    norm_num [step, removeGain, addGain, tightFun, arc, Fin.ext_iff] <;> decide
  change step (tightFun δ) (step (tightFun δ) (step (tightFun δ)
    (step (tightFun δ) (step (tightFun δ) (∅, Finset.univ) 0) 1) 2) 3) 4 = _
  rw [h0, h1, h2, h3, h4]

private theorem tight_opt_lower (δ : ℝ) :
    6 - 2 * δ ≤ NonmonotoneSubmod.Shared.OPT (tightFun δ) := by
  have hval : tightFun δ {0, 3, 4} = 6 - 2 * δ := by
    norm_num [tightFun, arc, Fin.ext_iff]
    ring
  rw [← hval]
  exact Finset.le_sup' (tightFun δ) (Finset.mem_univ _)

theorem solution :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ f : Finset (Fin n) → ℝ, ∃ l : List (Fin n),
      l.Nodup ∧ (∀ x, x ∈ l) ∧ (∀ S, 0 ≤ f S) ∧ NonmonotoneSubmod.Shared.Submodular f ∧
        0 < NonmonotoneSubmod.Shared.OPT f ∧
        f (state f l l.length).1 ≤ (1 / 3 + ε) * NonmonotoneSubmod.Shared.OPT f := by
  intro ε hε
  let δ : ℝ := min ε (1 / 2)
  have hδpos : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδone : δ ≤ 1 := by linarith
  refine ⟨5, tightFun δ, [0, 1, 2, 3, 4], by decide, ?_,
    tight_nonneg δ hδone, tight_submodular δ hδone, ?_, ?_⟩
  · intro x
    fin_cases x <;> simp
  · have hb := tight_opt_lower δ
    linarith
  · have hb := tight_opt_lower δ
    have hout : tightFun δ (state (tightFun δ) [0, 1, 2, 3, 4] 5).1 = 2 := by
      rw [tight_run δ hδpos]
      norm_num [tightFun, arc, Fin.ext_iff]
    change tightFun δ (state (tightFun δ) [0, 1, 2, 3, 4] 5).1 ≤ _
    rw [hout]
    have hmul := mul_le_mul_of_nonneg_left hb (show 0 ≤ 1 / 3 + ε by linarith)
    have hprod := mul_le_mul_of_nonneg_left hδhalf (le_of_lt hε)
    nlinarith
