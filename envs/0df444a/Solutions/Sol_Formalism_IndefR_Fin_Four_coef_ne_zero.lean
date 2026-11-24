-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.coef_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:43:19.604797+00:00
-- url     : https://prove2.me/submissions/4683e82c-bfe3-4289-9e23-ee72e8155c43

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_trans

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
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
  (hoX : ∀ x ∈ X, ∃ k : ℕ, 0 < k ∧ k • x ∈ L) (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L)
  (hfX : ∀ u ∈ L ⊓ X, ρ u f₀ = f₀) (hfY : ∀ u ∈ L ⊓ Y, ρ u f₀ = f₀)
include hχl hχr hχ0 hLL hdY hoY hfinX
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {Φ : W → ℂ} (h : IsSB L X Φ) {k : ℕ} (hk : 0 < k) (hi : ∀ u ∈ L ⊓ X, ∀ t, Φ (t + k • u) = Φ t)
    {a y : W} (hy : y ∈ Y) (hc : coef χ L X Φ a y ≠ 0) : (∃ t ∈ L ⊓ X, Φ (a + t) ≠ 0) ∧ k • y ∈ L := by
  unfold coef at hc
  obtain ⟨G, hG⟩ : ∃ G : W → ℂ, G = fun t => Φ (a + t) * (χ t y)⁻¹ := ⟨_, rfl⟩
  rw [← hG] at hc
  unfold integ at hc
  by_cases hex : ∃ K, 0 < K ∧ IsInv K (L ⊓ X) G
  swap
  · rw [dif_neg hex] at hc; exact absurd rfl hc
  rw [dif_pos hex] at hc
  have hK := hex.choose_spec.1
  have hI := hex.choose_spec.2
  haveI := hfinX _ hK
  classical
  haveI := Fintype.ofFinite (Qt hex.choose (L ⊓ X))
  unfold avg at hc
  rw [finsum_eq_sum_of_fintype] at hc
  have hS : ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) ≠ 0 := by
    intro h0; apply hc; rw [h0, mul_zero]
  refine ⟨?_, ?_⟩
  · by_contra hno
    push_neg at hno
    apply hS
    refine Finset.sum_eq_zero fun q _ => ?_
    simp only [hG]
    rw [hno _ (q.out).2, zero_mul]
  · have h0 : ∀ b, χ 0 b = 1 := by
      intro b
      have h1 := hχl 0 0 b
      rw [add_zero] at h1
      exact mul_left_cancel₀ (hχ0 0 b) (h1.symm.trans (mul_one _).symm)
    have h0' : ∀ a, χ a 0 = 1 := by
      intro a
      have h1 := hχr a 0 0
      rw [add_zero] at h1
      exact mul_left_cancel₀ (hχ0 a 0) (h1.symm.trans (mul_one _).symm)
    have hpow : ∀ (n : ℕ) (a b : W), χ (n • a) b = χ a b ^ n := by
      intro n a b
      induction n with
      | zero => rw [zero_smul, pow_zero, h0]
      | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]
    have hpow' : ∀ (n : ℕ) (a b : W), χ a (n • b) = χ a b ^ n := by
      intro n a b
      induction n with
      | zero => rw [zero_smul, pow_zero, h0']
      | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]
    apply hdY (k • y) (Y.nsmul_mem hy k)
    intro x hx
    have hGshift : ∀ t, G (t + k • x) = (χ x (k • y))⁻¹ * G t := by
      intro t
      simp only [hG]
      rw [← add_assoc, hi x hx (a + t), hχl, hpow, ← hpow', mul_inv]
      ring
    obtain ⟨z, hz⟩ : ∃ z : ↥(L ⊓ X), (z : W) = k • x := ⟨⟨k • x, (L ⊓ X).nsmul_mem hx k⟩, rfl⟩
    have hshift : ∀ q : Qt hex.choose (L ⊓ X), G (((q.out : ↥(L ⊓ X)) : W) + k • x) =
        G (((q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))).out : ↥(L ⊓ X)) : W) := by
      intro q
      have hq : (q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))) =
          QuotientAddGroup.mk (q.out + z) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
      have h1 := (QuotientAddGroup.out_eq' (q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X)))).trans hq
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
      simp only [smulSub, AddSubgroup.mem_map, nsmulAddMonoidHom_apply] at h1
      obtain ⟨v, hv, hv'⟩ := h1
      have h2 : ((q.out : ↥(L ⊓ X)) : W) + k • x =
          ((q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))).out : ↥(L ⊓ X)) + hex.choose • v := by
        rw [hv', ← hz]
        push_cast
        first
          | exact (add_neg_cancel_left _ _).symm
          | simp
          | abel
      rw [h2]
      exact hI _ ((q + (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X))).out).2 v hv
    have hshift_sum : ∑ q : Qt hex.choose (L ⊓ X), G (((q.out : ↥(L ⊓ X)) : W) + k • x) =
        ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) := by
      rw [Fintype.sum_congr _ _ hshift]
      exact Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk z : Qt hex.choose (L ⊓ X)))
        (fun q => G ((q.out : ↥(L ⊓ X)) : W))
    have hmul : (χ x (k • y))⁻¹ * ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) =
        ∑ q : Qt hex.choose (L ⊓ X), G ((q.out : ↥(L ⊓ X)) : W) := by
      rw [Finset.mul_sum]
      simp_rw [← hGshift]
      exact hshift_sum
    have h1 := mul_right_cancel₀ hS (hmul.trans (one_mul _).symm)
    exact inv_eq_one.1 h1
end Formalism.IndefR.Fin.Four
