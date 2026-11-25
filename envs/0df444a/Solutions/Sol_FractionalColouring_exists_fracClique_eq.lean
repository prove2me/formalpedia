-- Prove2me | solution 1 for FractionalColouring.exists_fracClique_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:39:37.936877+00:00
-- url     : https://prove2.me/submissions/eb03d6cb-836a-4f8a-a4a1-95aa5445f9bd

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Definitions.Def_FractionalLib_Basic
public import Theorems.Thm_FractionalColouring_weights_nonempty
public import Theorems.Thm_FractionalColouring_fracChromaticNumber_le
public import Theorems.Thm_FiniteLP_covering_packing_duality
public import Theorems.Thm_FiniteLP_toE_apply
attribute [local simp] FiniteLP.toE_apply



set_option autoImplicit true
@[expose] public section
public section
open Finset
open FractionalColouring
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
variable {G}
open Classical
namespace FractionalColouring
theorem _root_.solution : ∃ g, IsFracClique G g ∧ ∑ v, g v = fracChromaticNumber G := by
  let A : Finset V → V → ℝ := fun s v => if v ∈ s ∧ G.IsIndepSet (s : Set V) then 1 else 0
  obtain ⟨w, hw0, hwle, hweq⟩ := FiniteLP.covering_packing_duality A (fun _ => 1)
    (fun s v => by dsimp only [A]; split_ifs <;> norm_num) (fun _ => zero_le_one)
    (fun v => ⟨{v}, by simp [A]⟩)
  refine ⟨w, ⟨hw0, fun s hs => ?_⟩, ?_⟩
  · have := hwle s
    simp only [A, hs, and_true, ite_mul, one_mul, zero_mul] at this
    rwa [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter] at this
  · rw [hweq]
    -- the covering LP of `A` has the same infimum as `χ_f(G)`
    apply le_antisymm
    · refine le_csInf weights_nonempty ?_
      rintro _ ⟨x, hx, rfl⟩
      refine csInf_le ⟨0, ?_⟩ ⟨x, hx.1, fun v => ?_, by simp⟩
      · rintro _ ⟨y, hy, -, rfl⟩
        exact Finset.sum_nonneg fun s _ => by simpa using hy s
      · refine le_trans (hx.2.2 v) (le_of_eq ?_)
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun s _ => ?_
        by_cases hvs : v ∈ s
        · by_cases hs : G.IsIndepSet (s : Set V)
          · simp [A, hvs, hs]
          · simp [A, hvs, hs, hx.2.1 s hs]
        · simp [A, hvs]
    · refine le_csInf ⟨_, fun _ => 1, fun _ => zero_le_one, fun v => ?_, rfl⟩ ?_
      · exact le_trans (by simp [A]) (Finset.single_le_sum (f := fun s => A s v * 1)
          (fun s _ => by dsimp only [A]; split_ifs <;> norm_num) (Finset.mem_univ {v}))
      · rintro _ ⟨y, hy0, hycov, rfl⟩
        let x : Finset V → ℝ := fun s => if G.IsIndepSet (s : Set V) then y s else 0
        have hx : IsFracColouring G x := by
          refine ⟨fun s => by dsimp only [x]; split_ifs <;> simp [hy0 s], fun s hs => by
            simp [x, hs], fun v => ?_⟩
          refine le_trans (hycov v) (le_of_eq ?_)
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun s _ => ?_
          by_cases hvs : v ∈ s <;> by_cases hs : G.IsIndepSet (s : Set V) <;> simp [A, x, hvs, hs]
        refine le_trans (fracChromaticNumber_le hx) (Finset.sum_le_sum fun s _ => ?_)
        dsimp only [x]
        split_ifs <;> simp [hy0 s]
end FractionalColouring
