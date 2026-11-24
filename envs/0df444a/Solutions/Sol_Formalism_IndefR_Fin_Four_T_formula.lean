-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.T_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:14:39.402626+00:00
-- url     : https://prove2.me/submissions/a97c52f4-e6aa-46eb-a595-0aec8ea90f87

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Theorems.Thm_Formalism_IndefR_Fin_Four_mk_out_sub
import Theorems.Thm_Formalism_IndefR_Fin_Four_finite_out_smul
import Theorems.Thm_Formalism_IndefR_Fin_Four_isSB_indk
import Theorems.Thm_Formalism_IndefR_Fin_Four_T_indk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdX : ∀ x ∈ X, (∀ y ∈ L ⊓ Y, χ x y = 1) → x ∈ L)
  (hdivX : ∀ k : ℕ, 0 < k → ∀ s ∈ X, ∃ t ∈ X, k • t = s)
  (hdivY : ∀ k : ℕ, 0 < k → ∀ s ∈ Y, ∃ t ∈ Y, k • t = s)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
include hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf
open Classical
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (T : (W → ℂ) →ₗ[ℂ] V)
    (htr : ∀ Φ, IsSB L X Φ → ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ))
    (hmo : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ))
    (hva : T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀)
    {Φ : W → ℂ} {k : ℕ} (hk : 0 < k) (hs : ∀ t, Φ t ≠ 0 → t ∈ X)
    (hi : ∀ u ∈ L ⊓ X, ∀ t, Φ (t + k • u) = Φ t) (hl : ∀ t, Φ t ≠ 0 → k • t ∈ L) :
    T Φ = ∑ᶠ q : W ⧸ smulSub k (L ⊓ X), Φ q.out • ρ (-q.out) (Pk ρ L Y f₀ k) := by
  haveI := hfinX (k * k) (Nat.mul_pos hk hk)
  have hfin : {q : W ⧸ smulSub k (L ⊓ X) | Φ q.out ≠ 0}.Finite := by
    refine (finite_out_smul (L ⊓ X) (htf k hk)).subset ?_
    intro q hq
    exact AddSubgroup.mem_inf.mpr ⟨hl _ hq, nsmul_mem (hs _ hq) k⟩
  have hinv : ∀ t, Φ ((QuotientAddGroup.mk t : W ⧸ smulSub k (L ⊓ X)).out) = Φ t := by
    intro t
    obtain ⟨l, hl', he⟩ := mk_out_sub (smulSub k (L ⊓ X)) t
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.mp hl'
    rw [he]
    exact hi u hu t
  have hone : ∀ t, indk L X k (t + -(QuotientAddGroup.mk t : W ⧸ smulSub k (L ⊓ X)).out) = 1 := by
    intro t
    obtain ⟨l, hl', he⟩ := mk_out_sub (smulSub k (L ⊓ X)) t
    rw [he]
    unfold indk
    apply if_pos
    have h3 : t + -(t + l) = -l := by abel
    rw [h3]
    exact neg_mem hl'
  have hzero : ∀ t (q : W ⧸ smulSub k (L ⊓ X)), q ≠ QuotientAddGroup.mk t →
      indk L X k (t + -q.out) = 0 := by
    intro t q hq
    unfold indk
    apply if_neg
    intro hm
    apply hq
    rw [← QuotientAddGroup.out_eq' q]
    apply QuotientAddGroup.eq.mpr
    rw [add_comm]
    exact hm
  have hdec : Φ = ∑ q ∈ hfin.toFinset, Φ q.out • (fun t => indk L X k (t + -q.out)) := by
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (QuotientAddGroup.mk t)]
    · rw [hone, mul_one, hinv]
    · intro q _ hq
      rw [hzero t q hq, mul_zero]
    · intro hn
      rw [hone, mul_one, hinv]
      by_contra h0
      apply hn
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hinv]
      exact h0
  have hX : ∀ q ∈ hfin.toFinset, -q.out ∈ X := by
    intro q hq
    exact neg_mem (hs _ (hfin.mem_toFinset.mp hq))
  have hsub : (Function.support fun q : W ⧸ smulSub k (L ⊓ X) =>
      Φ q.out • ρ (-q.out) (Pk ρ L Y f₀ k)) ⊆ ↑hfin.toFinset := by
    intro q hq
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    apply hq
    simp only [h0, zero_smul]
  rw [finsum_eq_sum_of_support_subset _ hsub]
  conv_lhs => rw [hdec]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [map_smul, htr _ (isSB_indk hk) _ (hX q hq),
    T_indk hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf T hmo hva hk]
end Formalism.IndefR.Fin.Four
