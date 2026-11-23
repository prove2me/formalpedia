-- Prove2me | solution 1 for FlowSparsSchur.Main.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:11:00.766362+00:00
-- url     : https://prove2.me/submissions/473d0789-a178-4781-833c-1da8e4664457

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Routing

open FlowSparsSchur.Main
open Matrix

theorem solution {n m T : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    {r : Fin T → ℕ} (H : ∀ i, CGraph S (Fin (r i))) (hS : 2 ≤ S.card)
    (hG : G.NoLoops ∧ G.PosCap ∧ G.Connected)
    (hH : ∀ i, (H i).NoLoops ∧ (H i).PosCap ∧ (H i).Connected)
    (hemb : ∀ i, QEmbeds 1 G (H i) (fun s : S => s.val) (fun s : S => s))
    (lam : Fin T → ℝ) (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) :
    QEmbeds 1 G (CGraph.combo lam H) (fun s : S => s.val) (fun s : S => s) := by
  intro a D hD hRout
  choose F hRoutes hLoad using fun i => hemb i a D hD hRout
  let Flam : Matrix (Σ i, Fin (r i)) (Fin a) ℝ := fun x j => lam x.1 * F x.1 x.2 j
  refine ⟨Flam, ?_, ?_⟩
  · unfold Routes
    ext s j
    have hcombo_inc : ∀ x : Σ i, Fin (r i),
        (CGraph.combo lam H).incidence x s = (H x.1).incidence x.2 s := fun _ => rfl
    calc
      (((CGraph.combo lam H).incidence)ᵀ * Flam) s j
          = ∑ x : Σ i, Fin (r i), (CGraph.combo lam H).incidence x s * (lam x.1 * F x.1 x.2 j) := by
              rfl
      _ = ∑ i : Fin T, ∑ f : Fin (r i), (H i).incidence f s * (lam i * F i f j) := by
            rw [Fintype.sum_sigma]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun f _ => ?_
            rw [hcombo_inc ⟨i, f⟩]
      _ = ∑ i : Fin T, lam i * (∑ f : Fin (r i), (H i).incidence f s * F i f j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun f _ => by ring
      _ = ∑ i : Fin T, lam i * extendDemand (fun s : S => s) D s j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have hi := congr_fun (congr_fun (hRoutes i) s) j
            simp only [Routes, Matrix.mul_apply, Matrix.transpose_apply] at hi
            rw [hi]
      _ = (∑ i : Fin T, lam i) * extendDemand (fun s : S => s) D s j := by
            rw [Finset.sum_mul]
      _ = extendDemand (fun s : S => s) D s j := by
            rw [hlam1, one_mul]
  · intro x
    calc
      load Flam x
          = ∑ j : Fin a, |lam x.1 * F x.1 x.2 j| := rfl
      _ = ∑ j : Fin a, lam x.1 * |F x.1 x.2 j| := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [abs_mul, abs_of_nonneg (hlam0 x.1)]
      _ = lam x.1 * load (F x.1) x.2 := by
            rw [← Finset.mul_sum]
            rfl
      _ ≤ lam x.1 * (1 * (H x.1).cap x.2) :=
            mul_le_mul_of_nonneg_left (hLoad x.1 x.2) (hlam0 x.1)
      _ = 1 * (CGraph.combo lam H).cap x := by
            simp only [CGraph.combo]
            ring
