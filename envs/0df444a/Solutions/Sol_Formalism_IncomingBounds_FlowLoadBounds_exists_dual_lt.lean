-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.exists_dual_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:00.768857+00:00
-- url     : https://prove2.me/submissions/8b328011-40e6-424a-b785-474ee5a675a7

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_load_zero
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_flowVal_zero
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_pair_eq
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_convex_K
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_isClosed_K
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Set
open scoped Pointwise
namespace Formalism.IncomingBounds
namespace FlowLoadBounds
variable {l d : ℕ} [NeZero d]
private theorem isFlow_zero_of_nonneg {D : ZMod d → ℝ} (hD : 0 ≤ D) : IsFlow l d D 0 := by
  unfold IsFlow
  exact ⟨fun s i => by simp, fun s => by simpa using hD s⟩
private theorem mem_Kset_iff' {q : (ZMod d → ℝ) × ℝ} :
    q ∈ Kset l d ↔ ∃ x : ZMod d → ℕ → ℝ, (∀ s i, 0 ≤ x s i) ∧
      (∀ s, dpLoad l d x s ≤ q.1 s) ∧ q.2 ≤ Formalism.IncomingBounds.flowVal d x := Iff.rfl
end FlowLoadBounds
open FlowLoadBounds
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set
open scoped Pointwise
open Formalism Formalism.IncomingBounds
open Formalism.IncomingBounds.FlowLoadBounds
variable {l d : ℕ} [NeZero d]
namespace Formalism.IncomingBounds.FlowLoadBounds
theorem _root_.solution (hl : 1 ≤ l) (D : ZMod d → ℝ) (hD : 0 ≤ D) {v : ℝ}
    (hv : ∀ y, IsFlow l d D y → flowVal d y ≤ v) {ε : ℝ} (hε : 0 < ε) :
    ∃ sig : ZMod d → ℝ, (∀ s, 0 ≤ sig s) ∧
      (∀ s, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))) ∧
      ∑ s, D s * sig s < v + ε := by
  have hv0 : 0 ≤ v := by simpa [flowVal_zero] using hv 0 (isFlow_zero_of_nonneg hD)
  have hnot : ((D, v + ε) : (ZMod d → ℝ) × ℝ) ∉ Kset l d := by
    intro hmem
    obtain ⟨x, hxn, hxl, hxv⟩ := mem_Kset_iff'.1 hmem
    have hxF : IsFlow l d D x := by
      unfold IsFlow
      exact ⟨hxn, hxl⟩
    have h1 := hv x hxF
    have h2 : v + ε ≤ Formalism.IncomingBounds.flowVal d x := hxv
    linarith
  obtain ⟨f, u, hfu, hfb⟩ :=
    geometric_hahn_banach_point_closed (convex_K (l := l) (d := d))
      (isClosed_K hl) hnot
  have key : ∀ q : (ZMod d → ℝ) × ℝ, f q = ∑ t, q.1 t * f ((Pi.single t (1 : ℝ) : ZMod d → ℝ), (0 : ℝ)) +
      q.2 * f ((0 : ZMod d → ℝ), (1 : ℝ)) := by
    intro q
    have hq : q = ∑ t, q.1 t • ((Pi.single t (1 : ℝ) : ZMod d → ℝ), (0 : ℝ)) +
        q.2 • ((0 : ZMod d → ℝ), (1 : ℝ)) := by
      refine Prod.ext ?_ ?_
      · funext t'
        simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    conv_lhs => rw [hq]
    simp only [map_add, map_sum, map_smul, smul_eq_mul]
  obtain ⟨a, c, key'⟩ : ∃ (a : ZMod d → ℝ) (c : ℝ),
      ∀ q : (ZMod d → ℝ) × ℝ, f q = ∑ t, q.1 t * a t + q.2 * c := ⟨_, _, key⟩
  have hrec : ∀ q : (ZMod d → ℝ) × ℝ, (∀ s, 0 ≤ q.1 s) → q.2 ≤ 0 → q ∈ Kset l d :=
    fun q h1 h2 => mem_Kset_iff'.2 ⟨0, fun _ _ => by simp,
      fun s => by simpa [load_zero] using h1 s, by simpa [flowVal_zero] using h2⟩
  have hu : u < 0 := by simpa using hfb 0 (hrec 0 (fun s => by simp) (by simp))
  have hat : ∀ t, f ((Pi.single t (1 : ℝ) : ZMod d → ℝ), (0 : ℝ)) = a t := by
    intro t
    rw [key']
    simp [Pi.single_apply]
  have ha : ∀ t, 0 ≤ a t := by
    intro t
    by_contra hneg
    push_neg at hneg
    have hq : ((u / a t) • ((Pi.single t (1 : ℝ) : ZMod d → ℝ), (0 : ℝ))) ∈ Kset l d := by
      refine hrec _ (fun s => ?_) (by simp)
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      refine mul_nonneg (div_pos_iff.2 (Or.inr ⟨hu, hneg⟩)).le ?_
      rw [Pi.single_apply]
      split_ifs <;> norm_num
    have h1 := hfb _ hq
    rw [map_smul, hat, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at h1
    exact lt_irrefl _ h1
  have hc : c < 0 := by
    by_contra hc'
    push_neg at hc'
    have h1 := key' (D, v + ε)
    dsimp only at h1
    have h2 : 0 ≤ ∑ t, D t * a t := Finset.sum_nonneg fun t _ => mul_nonneg (hD t) (ha t)
    have h3 : 0 ≤ (v + ε) * c := mul_nonneg (by linarith) hc'
    linarith
  have hcpos : 0 < -c := neg_pos.2 hc
  have hw : ∀ s, ∀ i ∈ oddLevels d, 0 ≤ (l : ℝ) ^ i * a s + a (s + (i : ZMod d)) + c := by
    intro s i hi
    by_contra hw0
    push_neg at hw0
    obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (l : ℝ) ^ i * a s + a (s + (i : ZMod d)) + c := ⟨_, rfl⟩
    rw [← hW] at hw0
    have hτ : 0 < u / W := div_pos_iff.2 (Or.inr ⟨hu, hw0⟩)
    obtain ⟨x, hxdef⟩ : ∃ x : ZMod d → ℕ → ℝ,
        x = fun t j => if j = i then (if t = s then u / W else 0) else 0 := ⟨_, rfl⟩
    have hx0 : ∀ t j, 0 ≤ x t j := by
      intro t j
      simp only [hxdef]
      split_ifs <;> first | exact hτ.le | exact le_rfl
    have hsum : ∀ g : ZMod d → ℕ → ℝ, ∑ t, ∑ j ∈ oddLevels d, g t j * x t j = g s i * (u / W) := by
      intro g
      simp [hxdef, mul_ite, Finset.sum_ite_eq', hi]
    have hflow : Formalism.IncomingBounds.flowVal d x = u / W := by
      have h := hsum (fun _ _ => 1)
      simp only [one_mul] at h
      exact h
    have hq : ((fun t => dpLoad l d x t, Formalism.IncomingBounds.flowVal d x) : (ZMod d → ℝ) × ℝ) ∈ Kset l d :=
      mem_Kset_iff'.2 ⟨x, hx0, fun t => le_rfl, le_rfl⟩
    have h1 := hfb _ hq
    rw [key'] at h1
    dsimp only at h1
    have h2 : ∑ t, dpLoad l d x t * a t = ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) * (u / W) := by
      rw [← hsum (fun t j => (l : ℝ) ^ j * a t + a (t + (j : ZMod d))), ← pair_eq]
      exact Finset.sum_congr rfl fun t _ => mul_comm _ _
    rw [h2, hflow] at h1
    have h3 : u / W * W = u := div_mul_cancel₀ _ hw0.ne
    have h4 : ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) * (u / W) + u / W * c = u / W * W := by
      rw [hW]
      ring
    linarith
  refine ⟨fun s => a s / -c, fun s => div_nonneg (ha s) hcpos.le, fun s i hi => ?_, ?_⟩
  · show 1 ≤ (l : ℝ) ^ i * (a s / -c) + a (s + (i : ZMod d)) / -c
    rw [show (l : ℝ) ^ i * (a s / -c) + a (s + (i : ZMod d)) / -c =
        ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) / -c by ring, le_div_iff₀ hcpos]
    linarith [hw s i hi]
  · show ∑ s, D s * (a s / -c) < v + ε
    have h1 := key' (D, v + ε)
    dsimp only at h1
    rw [show ∑ s, D s * (a s / -c) = (∑ s, D s * a s) / -c by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun s _ => by ring, div_lt_iff₀ hcpos]
    linarith
end Formalism.IncomingBounds.FlowLoadBounds
