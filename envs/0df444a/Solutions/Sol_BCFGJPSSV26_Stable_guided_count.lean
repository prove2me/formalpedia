-- Prove2me | solution 1 for BCFGJPSSV26.Stable.guided_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:56:20.221205+00:00
-- url     : https://prove2.me/submissions/208bdde0-9c9b-472c-bc84-9e784337b366

module

public import Definitions.Def_BCFGJPSSV26_Model
public import Definitions.Def_BuhaiPapers_Background_Sampling
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Fin.Basic
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coins
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_Coins

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset Sampling

open Classical in
/-- **Guided counting.** -/
theorem guided_count {σ χ : Type*} [Fintype χ] (step : ℕ → σ → χ → σ) (x₀ : σ)
    (Inv : ℕ → σ → Prop) (G : ℕ → σ → χ → Prop) {q : ℝ} (hq : 0 ≤ q) (M : ℕ) (h0 : Inv 0 x₀)
    (hstep : ∀ t < M, ∀ x u, Inv t x → G t x u → Inv (t + 1) (step t x u))
    (hG : ∀ t < M, ∀ x, Inv t x → q * Fintype.card χ ≤ (univ.filter fun u ↦ G t x u).card) :
    q ^ M * (Fintype.card χ : ℝ) ^ M ≤
      (univ.filter fun u : Fin M → χ ↦ Inv M (runFin step x₀ M u)).card := by
  induction M with
  | zero =>
    have : (univ.filter fun u : Fin 0 → χ ↦ Inv 0 (runFin step x₀ 0 u)) = univ :=
      filter_true_of_mem fun u _ ↦ h0
    rw [this, card_univ]
    simp
  | succ M ih =>
    have ih' := ih (fun t ht ↦ hstep t (by omega)) (fun t ht ↦ hG t (by omega))
    have hsub : (univ.filter fun u : Fin (M + 1) → χ ↦
        Inv M (runFin step x₀ M fun i ↦ u i.castSucc) ∧
          G M (runFin step x₀ M fun i ↦ u i.castSucc) (u (Fin.last M))) ⊆
        univ.filter fun u ↦ Inv (M + 1) (runFin step x₀ (M + 1) u) := by
      intro u hu
      simp only [mem_filter, mem_univ, true_and] at hu ⊢
      exact hstep M (by omega) _ _ hu.1 hu.2
    have he : (univ.filter fun u : Fin (M + 1) → χ ↦
        Inv M (runFin step x₀ M fun i ↦ u i.castSucc) ∧
          G M (runFin step x₀ M fun i ↦ u i.castSucc) (u (Fin.last M))).card =
        (univ.filter fun p : (Fin M → χ) × χ ↦
          Inv M (runFin step x₀ M p.1) ∧ G M (runFin step x₀ M p.1) p.2).card := by
      refine card_equiv ((Fin.snocEquiv (fun _ ↦ χ)).symm.trans (Equiv.prodComm _ _))
        fun u ↦ ?_
      simp only [mem_filter, mem_univ, true_and, Equiv.trans_apply, Equiv.prodComm_apply,
        Prod.fst_swap, Prod.snd_swap]
      rfl
    have h := card_prod_filter_ge (fun v ↦ Inv M (runFin step x₀ M v))
      (fun v c ↦ G M (runFin step x₀ M v) c) (mul_nonneg hq (Nat.cast_nonneg _)) ih'
      (fun v hv ↦ hG M (by omega) _ hv)
    calc q ^ (M + 1) * (Fintype.card χ : ℝ) ^ (M + 1) =
          (q ^ M * (Fintype.card χ : ℝ) ^ M) * (q * Fintype.card χ) := by ring
      _ ≤ _ := h
      _ = _ := by rw [← he]
      _ ≤ _ := by exact_mod_cast card_le_card hsub

-- The bounds `0 ≤ q ≤ 1` are not needed: the bound holds for every `q`.

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.guided_count := @BCFGJPSSV26.Stable.guided_count
