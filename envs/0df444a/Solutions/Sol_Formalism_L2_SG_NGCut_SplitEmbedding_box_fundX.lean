-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.box_fundX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:11:09.473505+00:00
-- url     : https://prove2.me/submissions/f3275059-e991-4260-8ae5-5f2b159a4484

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CovolOneEqOne
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFundX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
namespace Formalism.L2.SG.NGCut.SplitEmbedding
theorem _root_.solution {ι P : Type} [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (A : P → AddSubgroup (ι → ℂ)) (F : P → Set (ι → ℂ)) (hFd : ∀ p (v : ι → ℂ), ∃! a : A p, (a : ι → ℂ) + v ∈ F p)
    (x : ι → P → ℂ) :
    ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ A p) ∧
      lawX BX γ x ∈ {y : ι → P → ℂ | ∀ p, (fun v => y v p) ∈ F p} := by
  classical
  let w : P → (ι → P → ℂ) → (ι → ℂ) := fun p γ => τ p γ + fun v => x v p + BX p (γ v) (x v)
  let c : P → (ι → P → ℂ) → (ι → ℂ) := fun p γ =>
    ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ
  have hloc : ∀ p (γ γ' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, γ v q = γ' v q) → c p γ = c p γ' := by
    intro p γ γ' hg
    have h1 : τ p γ = τ p γ' := hτ p γ γ' hg
    have h2 : w p γ = w p γ' := by
      show (τ p γ + fun v => x v p + BX p (γ v) (x v)) = τ p γ' + fun v => x v p + BX p (γ' v) (x v)
      rw [h1]
      congr 1
      funext v
      rw [hBd p (γ v) (γ' v) (x v) (x v) (fun q hq => ⟨hg q hq v, rfl⟩)]
    have hch : ∀ u u' : ι → ℂ, u = u' →
        ((hFd p u).exists.choose : ι → ℂ) = ((hFd p u').exists.choose : ι → ℂ) := by
      rintro u _ rfl
      rfl
    show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = ((hFd p (w p γ')).exists.choose : ι → ℂ) + τ p γ'
    rw [h1, hch _ _ h2]
  have key : ∀ p (γ : ι → P → ℂ), ((fun v => γ v p) - τ p γ ∈ A p ∧ (fun v => lawX BX γ x v p) ∈ F p) ↔
      (fun v => γ v p) = c p γ := by
    intro p γ
    obtain ⟨a, ha, huniq⟩ := hFd p (w p γ)
    have hc : c p γ = (a : ι → ℂ) + τ p γ := by
      show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = (a : ι → ℂ) + τ p γ
      rw [huniq _ (hFd p (w p γ)).exists.choose_spec]
    have hlaw : (fun v => lawX BX γ x v p) = ((fun v => γ v p) - τ p γ) + w p γ := by
      funext v
      simp only [lawX, w, Pi.add_apply, Pi.sub_apply]
      ring
    rw [hc, hlaw]
    constructor
    · rintro ⟨hA, hF⟩
      have e := congrArg Subtype.val (huniq ⟨_, hA⟩ hF)
      simp only at e
      rw [← e]
      abel
    · intro hg
      rw [hg, add_sub_cancel_right]
      exact ⟨a.2, ha⟩
  let Φ : (ι → P → ℂ) → (ι → P → ℂ) := fun γ v p => c p γ v
  have hit : ∀ k (γ γ' : ι → P → ℂ), ∀ p, h p < k → ∀ v, (Φ^[k] γ) v p = (Φ^[k] γ') v p := by
    intro k
    induction k with
    | zero => intro γ γ' p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ k ih =>
      intro γ γ' p hp v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show c p (Φ^[k] γ) v = c p (Φ^[k] γ') v
      rw [hloc p _ _ (fun q hq v => ih γ γ' q (by omega) v)]
  have hN : ∀ p, h p < Finset.univ.sup h + 1 := fun p =>
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p))
  have hcond : ∀ γ : ι → P → ℂ, ((∀ p, (fun v => γ v p) - τ p γ ∈ A p) ∧
      lawX BX γ x ∈ {y : ι → P → ℂ | ∀ p, (fun v => y v p) ∈ F p}) ↔ Φ γ = γ := by
    intro γ
    rw [Set.mem_setOf_eq, ← forall_and, forall_congr' (fun p => key p γ)]
    constructor
    · intro H
      funext v p
      exact (congrFun (H p) v).symm
    · intro H p
      funext v
      exact (congrFun (congrFun H v) p).symm
  refine ⟨Φ^[Finset.univ.sup h + 1] 0, (hcond _).2 ?_, fun γ hγ => ?_⟩
  · rw [← Function.iterate_succ_apply' Φ _ 0, Function.iterate_succ_apply]
    funext v p
    exact hit _ (Φ 0) 0 p (hN p) v
  · have e1 : Φ^[Finset.univ.sup h + 1] γ = γ := Function.iterate_fixed ((hcond γ).1 hγ) _
    funext v p
    calc γ v p = (Φ^[Finset.univ.sup h + 1] γ) v p := by rw [e1]
      _ = _ := hit _ γ 0 p (hN p) v
end Formalism.L2.SG.NGCut.SplitEmbedding
