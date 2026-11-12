-- Prove2me | solution 1 for BrouwerLaplacian.theorem_3_1_brouwer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:14:37.680222+00:00
-- url     : https://prove2.me/submissions/a7744a44-5c34-4320-ad74-45fea6f21207
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_BrouwerLaplacian_centering
import Definitions.Def_BrouwerLaplacian_routingM
import Theorems.Thm_BrouwerLaplacian_lemma_5_1
import Theorems.Thm_BrouwerLaplacian_lemma_5_6

section
namespace BrouwerLaplacian.Dev.Common

open Matrix

end BrouwerLaplacian.Dev.Common
end

section
namespace BrouwerLaplacian.Dev.L52

open Finset Matrix

theorem symm_of {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : BrouwerLaplacian.IsOrthProj P k)
    (i j : Fin n) : P j i = P i j := by
  have := hP.1.apply i j
  simpa using this

end BrouwerLaplacian.Dev.L52

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.OpN

open Matrix WainwrightHDS.NucNorm

end BrouwerLaplacian.Dev.OpN
end

section
namespace BrouwerLaplacian.Dev.NLem

open Finset Matrix BrouwerLaplacian

end BrouwerLaplacian.Dev.NLem

namespace BrouwerLaplacian
open Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.L56

open Finset Matrix BrouwerLaplacian

end BrouwerLaplacian.Dev.L56

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.L53

open Finset Matrix BrouwerLaplacian

theorem half_sum {n : ℕ} (g : Fin n → Fin n → ℝ) (hg : ∀ i j, g i j = g j i) :
    ∑ i, ∑ j with i ≠ j, g i j = 2 * ∑ i, ∑ j with i < j, g i j := by
  have h1 : ∀ i, ∑ j with i ≠ j, g i j
      = ∑ j with i < j, g i j + ∑ j with j < i, g i j := by
    intro i
    have : (univ.filter fun j => i ≠ j) = (univ.filter fun j => i < j) ∪ (univ.filter fun j => j < i) := by
      ext j
      simp only [mem_filter, mem_union, mem_univ, true_and]
      constructor
      · intro h; exact lt_or_gt_of_ne h
      · rintro (h | h)
        · exact ne_of_lt h
        · exact ne_of_gt h
    rw [this, sum_union]
    rw [disjoint_filter]; intro j _ h1 h2; exact absurd h1 (not_lt.2 h2.le)
  simp only [h1, sum_add_distrib]
  have h2 : ∑ i, ∑ j with j < i, g i j = ∑ i, ∑ j with i < j, g i j := by
    simp only [sum_filter]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [hg]
  rw [h2]; ring

end BrouwerLaplacian.Dev.L53

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.Transfer

open Finset Matrix

theorem eig_sum_transfer {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {A : Matrix V V ℝ} {B : Matrix W W ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hch : A.charpoly = B.charpoly) (k : ℕ) :
    ∑ i : Fin (Fintype.card V) with i.val < k, hA.eigenvalues₀ i
      = ∑ i : Fin (Fintype.card W) with i.val < k, hB.eigenvalues₀ i := by
  rw [← List.sum_take_ofFn, ← List.sum_take_ofFn, ← hA.sort_roots_charpoly_eq_eigenvalues₀,
    ← hB.sort_roots_charpoly_eq_eigenvalues₀, hch]

theorem lap_comap {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (e : Fin n ≃ V) :
    (G.comap e).lapMatrix ℝ = Matrix.reindex e.symm e.symm (G.lapMatrix ℝ) := by
  ext a b
  have hdeg : (G.comap e).degree a = G.degree (e a) :=
    ((SimpleGraph.Iso.comap e G).degree_eq a).symm
  by_cases hab : a = b
  · subst hab
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, hdeg]
  · simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, hab, SimpleGraph.adjMatrix_apply,
      e.injective.ne hab]

theorem edge_card_comap {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (e : Fin n ≃ V) :
    #(G.comap e).edgeFinset = #G.edgeFinset :=
  (SimpleGraph.Iso.comap e G).card_edgeFinset_eq

theorem eig_sum_graph {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (e : Fin n ≃ V) (k : ℕ) :
    ∑ i : Fin (Fintype.card V) with i.val < k, (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i
      = ∑ i : Fin (Fintype.card (Fin n)) with i.val < k,
          ((G.comap e).isHermitian_lapMatrix ℝ).eigenvalues₀ i := by
  apply eig_sum_transfer
  rw [lap_comap G e, Matrix.charpoly_reindex]

end BrouwerLaplacian.Dev.Transfer
end

section
namespace BrouwerLaplacian.Dev.L31

open Finset Matrix BrouwerLaplacian

theorem hproj_of_56 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k) (hP1 : P *ᵥ (fun _ => 1) = 0) :
    ∑ i, ∑ j with i < j ∧ G.Adj i j, (P i i + P j j - 2 * P i j - 1)
      ≤ ((k + 1).choose 2 : ℕ) := by
  have h56 := BrouwerLaplacian.lemma_5_6 P hP hP1
  set f : Fin n → Fin n → ℝ := fun i j => max (P i i + P j j - 2 * P i j - 1) 0 with hf
  have hfs : ∀ i j, f i j = f j i := by
    intro i j; simp only [hf, L52.symm_of hP i j]; congr 1; ring
  have hhalf := L53.half_sum f hfs
  have hf0 : ∀ i j, 0 ≤ f i j := fun i j => le_max_right _ _
  have h1 : ∑ i, ∑ j with i < j ∧ G.Adj i j, (P i i + P j j - 2 * P i j - 1)
      ≤ ∑ i, ∑ j with i < j, f i j := by
    refine sum_le_sum fun i _ => ?_
    calc ∑ j with i < j ∧ G.Adj i j, (P i i + P j j - 2 * P i j - 1)
        ≤ ∑ j with i < j ∧ G.Adj i j, f i j := sum_le_sum fun j _ => le_max_left _ _
      _ ≤ ∑ j with i < j, f i j := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj; simp only [mem_filter] at hj ⊢; exact ⟨hj.1, hj.2.1⟩
        · intro j _ _; exact hf0 i j
  have h2 : ((k + 1).choose 2 : ℝ) = (k + 1) * k / 2 := by
    rw [Nat.cast_choose_two]; simp
  have : (((k + 1).choose 2 : ℕ) : ℝ) = (k + 1) * k / 2 := h2
  rw [this]
  have h56' : ∑ i, ∑ j with i ≠ j, f i j ≤ k * (k + 1) := h56
  linarith

theorem main {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∑ i : Fin (Fintype.card V) with i.val < k, (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i
      ≤ (#G.edgeFinset : ℝ) + ((k + 1).choose 2 : ℕ) := by
  by_cases hk : k = Fintype.card V
  · subst hk
    set hA := G.isHermitian_lapMatrix ℝ with hAdef
    have hall : (univ.filter fun i : Fin (Fintype.card V) => i.val < Fintype.card V) = univ := by
      ext i; simp
    rw [hall]
    let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin (Fintype.card V))))
    have h1 : ∑ i : Fin (Fintype.card V), hA.eigenvalues₀ i = (G.lapMatrix ℝ).trace := by
      have := hA.trace_eq_sum_eigenvalues
      simp only [RCLike.ofReal_real_eq_id, id] at this
      rw [this]
      exact (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))).symm.sum_comp
        hA.eigenvalues₀ |>.symm
    have h2 : (G.lapMatrix ℝ).trace = 2 * (#G.edgeFinset : ℝ) := by
      have : (G.lapMatrix ℝ).trace = ∑ v, (G.degree v : ℝ) := by
        simp [Matrix.trace, SimpleGraph.lapMatrix, SimpleGraph.degMatrix]
      rw [this]
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have h3 : (#G.edgeFinset : ℝ) ≤ (((Fintype.card V + 1).choose 2 : ℕ) : ℝ) := by
      have a := G.card_edgeFinset_le_card_choose_two
      have b : (Fintype.card V).choose 2 ≤ (Fintype.card V + 1).choose 2 :=
        Nat.choose_le_choose 2 (Nat.le_succ _)
      exact_mod_cast a.trans b
    rw [h1, h2]
    linarith
  · set n := Fintype.card V with hn
    let e : Fin n ≃ V := (Fintype.equivFin V).symm
    rw [Transfer.eig_sum_graph G e k, ← Transfer.edge_card_comap G e]
    exact BrouwerLaplacian.lemma_5_1 (G.comap e) k hk1 (by omega)
      (fun P hP hP1 => hproj_of_56 (G.comap e) k P hP hP1)

end BrouwerLaplacian.Dev.L31

namespace BrouwerLaplacian
open Finset
theorem chk_theorem_3_1_brouwer {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ Fintype.card V) :
    ∑ i : Fin (Fintype.card V) with i.val < k, (G.isHermitian_lapMatrix ℝ).eigenvalues₀ i
      ≤ (#G.edgeFinset : ℝ) + ((k + 1).choose 2 : ℕ) := Dev.L31.main G k hk1 hkn
end BrouwerLaplacian
end

theorem solution : type_of% @BrouwerLaplacian.chk_theorem_3_1_brouwer := @BrouwerLaplacian.chk_theorem_3_1_brouwer
