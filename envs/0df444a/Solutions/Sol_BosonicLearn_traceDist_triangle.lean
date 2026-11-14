-- Prove2me | solution 1 for BosonicLearn.traceDist_triangle
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T06:53:50.051607+00:00
-- url     : https://prove2.me/submissions/822361ea-1353-4e45-b9da-71a7098ec6dd

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)

open scoped ENNReal

open BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion IsDensity IsTraceClass)
open QAlgorithms.RealRegisters (Hilbert)
open Filter Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Rank-one representations with a countable index set -/

/-- `NucRep X w`: the matrix `X` is a sum `∑ₐ |Lₐ⟩⟨Rₐ|` over a countable index set, with total weight
`∑ₐ ‖Lₐ‖‖Rₐ‖ = w`. -/
private def NucRep {I : Type} (X : Matrix I I ℂ) (w : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (L R : ι → Hilbert I),
    HasSum (fun a => ‖L a‖ * ‖R a‖) w ∧ ∀ i j, HasSum (fun a => L a i * star (R a j)) (X i j)

/-- A representation of weight `w` bounds the trace size by `w`: re-index it by `ℕ`. -/
private lemma rep_traceSize {I : Type} {X : Matrix I I ℂ} {w : ℝ} (h : NucRep X w) :
    traceSize X ≤ ENNReal.ofReal w := by
  obtain ⟨ι, hι, L, R, hw, hX⟩ := h
  obtain ⟨g, hg⟩ := exists_injective_nat ι
  have key1 : (fun n => ‖Function.extend g L 0 n‖ * ‖Function.extend g R 0 n‖) =
      Function.extend g (fun a => ‖L a‖ * ‖R a‖) 0 := by
    funext n
    by_cases hn : ∃ a, g a = n
    · obtain ⟨a, rfl⟩ := hn
      simp [hg.extend_apply]
    · simp [Function.extend_apply' _ _ _ hn]
  have key2 : ∀ i j, (fun n => (Function.extend g L 0 n) i * star ((Function.extend g R 0 n) j)) =
      Function.extend g (fun a => L a i * star (R a j)) 0 := by
    intro i j
    funext n
    by_cases hn : ∃ a, g a = n
    · obtain ⟨a, rfl⟩ := hn
      simp [hg.extend_apply]
    · simp [Function.extend_apply' _ _ _ hn]
  let e : NuclearExpansion X :=
    { left := Function.extend g L 0
      right := Function.extend g R 0
      summable := by
        rw [key1]
        exact (summable_extend_zero hg).mpr hw.summable
      coefficients := by
        intro i j
        rw [key2 i j, tsum_extend_zero hg]
        exact (hX i j).tsum_eq.symm }
  refine (iInf_le _ e).trans (le_of_eq ?_)
  congr 1
  show ∑' n, ‖Function.extend g L 0 n‖ * ‖Function.extend g R 0 n‖ = w
  rw [key1, tsum_extend_zero hg]
  exact hw.tsum_eq

private lemma rep_add {I : Type} {X Y : Matrix I I ℂ} {w v : ℝ} (hX : NucRep X w) (hY : NucRep Y v) :
    NucRep (X + Y) (w + v) := by
  obtain ⟨ι₁, hι₁, L₁, R₁, hw, hX⟩ := hX
  obtain ⟨ι₂, hι₂, L₂, R₂, hv, hY⟩ := hY
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim L₁ L₂, Sum.elim R₁ R₂, ?_, fun i j => ?_⟩
  · exact HasSum.sum (f := fun a => ‖Sum.elim L₁ L₂ a‖ * ‖Sum.elim R₁ R₂ a‖) hw hv
  · exact HasSum.sum (f := fun a => Sum.elim L₁ L₂ a i * star (Sum.elim R₁ R₂ a j)) (hX i j) (hY i j)

/-- A nuclear expansion is a representation with the same weight. -/
private lemma rep_of_expansion {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    NucRep X (∑' n, ‖e.left n‖ * ‖e.right n‖) := by
  refine ⟨ℕ, inferInstance, e.left, e.right, e.summable.hasSum, fun i j => ?_⟩
  rw [e.coefficients i j]
  have h : Summable fun a => e.left a i * star (e.right a j) := by
    refine Summable.of_norm_bounded e.summable fun a => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm (by norm_num) (e.left a) i)
      (lp.norm_apply_le_norm (by norm_num) (e.right a) j) (norm_nonneg _) (norm_nonneg _)
  exact h.hasSum

/-- Subadditivity of the trace norm. -/
private lemma traceSize_add_le {I : Type} (X Y : Matrix I I ℂ) :
    traceSize (X + Y) ≤ traceSize X + traceSize Y := by
  have key : ∀ (eX : NuclearExpansion X) (eY : NuclearExpansion Y), traceSize (X + Y) ≤
      ENNReal.ofReal (∑' n, ‖eX.left n‖ * ‖eX.right n‖) +
        ENNReal.ofReal (∑' n, ‖eY.left n‖ * ‖eY.right n‖) := by
    intro eX eY
    refine (rep_traceSize (rep_add (rep_of_expansion eX) (rep_of_expansion eY))).trans ?_
    rw [ENNReal.ofReal_add (tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  show traceSize (X + Y) ≤
    (⨅ e : NuclearExpansion X, ENNReal.ofReal (∑' n, ‖e.left n‖ * ‖e.right n‖)) +
      ⨅ e : NuclearExpansion Y, ENNReal.ofReal (∑' n, ‖e.left n‖ * ‖e.right n‖)
  rw [ENNReal.iInf_add]
  refine le_iInf fun eX => ?_
  rw [ENNReal.add_iInf]
  exact le_iInf fun eY => key eX eY

theorem solution {I : Type} (A B C : Matrix I I ℂ) :
    traceDist A C ≤ traceDist A B + traceDist B C := by
  unfold traceDist
  rw [← sub_add_sub_cancel A B C, ← ENNReal.add_div]
  exact ENNReal.div_le_div_right (traceSize_add_le _ _) 2
