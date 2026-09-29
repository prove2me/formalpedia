-- Prove2me | solution 1 for ContDiff.exists_forall_norm_iteratedDeriv_slice_le_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4c5e13fe-f027-583a-ad7b-9cda87160bfb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ContDiff_exists_forall_norm_iteratedDeriv_slice_le_of_isCompact

set_option autoImplicit false

namespace Ws31
namespace SmoothFamily

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def dU (G : E × ℝ → F) : ℕ → (E × ℝ → F)
  | 0 => G
  | n + 1 => fun p => fderiv ℝ (dU G n) p (0, 1)

theorem contDiff_dU (G : E × ℝ → F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (dU G n) := by
  intro n
  induction n with
  | zero => exact hG
  | succ n ih =>
    show ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ (dU G n) p (0, 1))
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (dU G n)) := ih.fderiv_right (by simp)
    exact h1.clm_apply contDiff_const

theorem iteratedDeriv_slice (G : E × ℝ → F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ∀ (n : ℕ) (a : E) (u : ℝ), iteratedDeriv n (fun u => G (a, u)) u = dU G n (a, u) := by
  intro n
  induction n with
  | zero => intro a u; rfl
  | succ n ih =>
    intro a u
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv n (fun u => G (a, u)) = fun u => dU G n (a, u) := funext (ih a)
    rw [hfun]
    show deriv (fun u => dU G n (a, u)) u = fderiv ℝ (dU G n) (a, u) (0, 1)
    have hd : DifferentiableAt ℝ (dU G n) (a, u) :=
      ((contDiff_dU G hG n).differentiable (by simp)).differentiableAt
    have hγ : HasDerivAt (fun u : ℝ => ((a, u) : E × ℝ)) ((0 : E), (1 : ℝ)) u :=
      (hasDerivAt_const u a).prodMk (hasDerivAt_id u)
    exact (hd.hasFDerivAt.comp_hasDerivAt u hγ).deriv

theorem main {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : E → ℝ → F) (hΨ : ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => Ψ p.1 p.2))
    (S : Set E) (hS : IsCompact S) (R : ℝ) (N : ℕ) :
    (∀ a : E, ContDiff ℝ N (Ψ a)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ S, ∀ u ∈ Set.Icc (-R) R, ∀ n ≤ N, ‖iteratedDeriv n (Ψ a) u‖ ≤ C := by
  set G : E × ℝ → F := fun p => Ψ p.1 p.2 with hGdef
  have hslice : ∀ a : E, ContDiff ℝ (⊤ : ℕ∞) (Ψ a) := fun a => by
    have : Ψ a = G ∘ fun u : ℝ => ((a, u) : E × ℝ) := rfl
    rw [this]
    exact hΨ.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨fun a => (hslice a).of_le (by exact_mod_cast le_top), ?_⟩

  have hK : IsCompact (S ×ˢ Set.Icc (-R) R) := hS.prod isCompact_Icc
  have hb : ∀ n : ℕ, ∃ Cn : ℝ, ∀ p ∈ S ×ˢ Set.Icc (-R) R, ‖dU G n p‖ ≤ Cn := fun n =>
    hK.exists_bound_of_continuousOn ((contDiff_dU G hΨ n).continuous.continuousOn)
  choose Cn hCn using hb
  refine ⟨∑ n ∈ Finset.range (N + 1), |Cn n|, Finset.sum_nonneg fun n _ => abs_nonneg _, ?_⟩
  intro a ha u hu n hn
  have hmem : ((a, u) : E × ℝ) ∈ S ×ˢ Set.Icc (-R) R := ⟨ha, hu⟩
  have h1 : ‖iteratedDeriv n (Ψ a) u‖ ≤ |Cn n| := by
    rw [show Ψ a = fun u => G (a, u) from rfl, iteratedDeriv_slice G hΨ n a u]
    exact (hCn n _ hmem).trans (le_abs_self _)
  refine h1.trans ?_
  exact Finset.single_le_sum (f := fun n => |Cn n|) (fun n _ => abs_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

end Ws31.SmoothFamily

theorem solution
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : E → ℝ → F) (hΨ : ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => Ψ p.1 p.2))
    (S : Set E) (hS : IsCompact S) (R : ℝ) (N : ℕ) :
    (∀ a : E, ContDiff ℝ N (Ψ a)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ S, ∀ u ∈ Set.Icc (-R) R, ∀ n ≤ N, ‖iteratedDeriv n (Ψ a) u‖ ≤ C :=
  Ws31.SmoothFamily.main Ψ hΨ S hS R N

end S_ContDiff_exists_forall_norm_iteratedDeriv_slice_le_of_isCompact
end P2MW
export P2MW.S_ContDiff_exists_forall_norm_iteratedDeriv_slice_le_of_isCompact (solution)
