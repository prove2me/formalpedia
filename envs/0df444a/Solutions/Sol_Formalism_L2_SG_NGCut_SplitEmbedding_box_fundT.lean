-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.box_fundT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:04:31.504382+00:00
-- url     : https://prove2.me/submissions/e1c4088a-04b4-44bf-b47b-6bdef55d7090

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFund
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFundT

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
variable {P : Type} [Fintype P] [DecidableEq P] {α : P → Type} [∀ p, AddCommGroup (α p)]
  (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
  (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
  (τ : ∀ p, (∀ q, α q) → α p) (hτ : ∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
  (A : ∀ p, AddSubgroup (α p)) (F : ∀ p, Set (α p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)
include hBd hτ hFd
namespace Formalism.L2.SG.NGCut.SplitEmbedding
theorem _root_.solution (g : ∀ q, α q) :
    ∃! γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) ∧ ∀ p, mlaw B γ g p ∈ F p := by
  let c : (∀ q, α q) → ∀ p, A p := fun x p => (hFd p (τ p x + g p + B p x g)).exists.choose
  have hc : ∀ x p, ((c x p : A p) : α p) + (τ p x + g p + B p x g) ∈ F p :=
    fun x p => (hFd p (τ p x + g p + B p x g)).exists.choose_spec
  let Φ : (∀ q, α q) → ∀ q, α q := fun x p => τ p x + (c x p : α p)
  have hΦ : ∀ (k : ℕ) (x x' : ∀ q, α q), (∀ q, h q < k → x q = x' q) →
      ∀ p, h p < k + 1 → Φ x p = Φ x' p := by
    intro k x x' hxx p hp
    have e1 : ∀ q, h q < h p → x q = x' q := fun q hq => hxx q (by omega)
    have h1 : τ p x = τ p x' := hτ p x x' e1
    have h2 : B p x g = B p x' g := hBd p x x' g g fun q hq => ⟨e1 q hq, rfl⟩
    show τ p x + ((hFd p (τ p x + g p + B p x g)).exists.choose : α p) =
      τ p x' + ((hFd p (τ p x' + g p + B p x' g)).exists.choose : α p)
    rw [h1, h2]
  have hit : ∀ (n : ℕ) p, h p < n → Φ (Φ^[n] 0) p = (Φ^[n] 0) p := by
    intro n
    induction n with
    | zero => intro p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ k ih =>
      intro p hp
      rw [Function.iterate_succ_apply']
      exact hΦ k _ _ ih p hp
  have uniq : ∀ x y : ∀ q, α q, ((∀ p, x p - τ p x ∈ A p) ∧ ∀ p, mlaw B x g p ∈ F p) →
      ((∀ p, y p - τ p y ∈ A p) ∧ ∀ p, mlaw B y g p ∈ F p) → x = y := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    have step : ∀ (n : ℕ) p, h p < n → x p = y p := by
      intro n
      induction n with
      | zero => intro p hp; exact absurd hp (Nat.not_lt_zero _)
      | succ k ih =>
        intro p hp
        have e1 : ∀ q, h q < h p → x q = y q := fun q hq => ih q (by omega)
        have ht : τ p x = τ p y := hτ p x y e1
        have hb : B p x g = B p y g := hBd p x y g g fun q hq => ⟨e1 q hq, rfl⟩
        have hx2' : ((⟨x p - τ p x, hx1 p⟩ : A p) : α p) + (τ p x + g p + B p x g) ∈ F p := by
          have hm : x p + g p + B p x g ∈ F p := hx2 p
          rw [show ((⟨x p - τ p x, hx1 p⟩ : A p) : α p) = x p - τ p x from rfl,
            show x p - τ p x + (τ p x + g p + B p x g) = x p + g p + B p x g by abel]
          exact hm
        have hy2' : ((⟨y p - τ p y, hy1 p⟩ : A p) : α p) + (τ p x + g p + B p x g) ∈ F p := by
          have hm : y p + g p + B p y g ∈ F p := hy2 p
          rw [ht, hb, show ((⟨y p - τ p y, hy1 p⟩ : A p) : α p) = y p - τ p y from rfl,
            show y p - τ p y + (τ p y + g p + B p y g) = y p + g p + B p y g by abel]
          exact hm
        have h3 : x p - τ p x = y p - τ p y :=
          congrArg Subtype.val ((hFd p _).unique hx2' hy2')
        rw [ht] at h3
        exact sub_left_injective h3
    funext p
    exact step _ p (Nat.lt_succ_self _)
  have hfix : ∀ p, τ p (Φ^[Finset.univ.sup h + 1] 0) + (c (Φ^[Finset.univ.sup h + 1] 0) p : α p) =
      (Φ^[Finset.univ.sup h + 1] 0) p :=
    fun p => hit _ p (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p)))
  have hsol : (∀ p, (Φ^[Finset.univ.sup h + 1] 0) p - τ p (Φ^[Finset.univ.sup h + 1] 0) ∈ A p) ∧
      ∀ p, mlaw B (Φ^[Finset.univ.sup h + 1] 0) g p ∈ F p := by
    constructor
    · intro p
      rw [← hfix p, add_sub_cancel_left]
      exact (c _ p).2
    · intro p
      show (Φ^[Finset.univ.sup h + 1] 0) p + g p + B p (Φ^[Finset.univ.sup h + 1] 0) g ∈ F p
      rw [← hfix p]
      rw [show τ p (Φ^[Finset.univ.sup h + 1] 0) + (c (Φ^[Finset.univ.sup h + 1] 0) p : α p) + g p +
          B p (Φ^[Finset.univ.sup h + 1] 0) g = (c (Φ^[Finset.univ.sup h + 1] 0) p : α p) +
          (τ p (Φ^[Finset.univ.sup h + 1] 0) + g p + B p (Φ^[Finset.univ.sup h + 1] 0) g) by abel]
      exact hc _ p
  exact ⟨_, hsol, fun y hy => uniq y _ hy hsol⟩
end Formalism.L2.SG.NGCut.SplitEmbedding
