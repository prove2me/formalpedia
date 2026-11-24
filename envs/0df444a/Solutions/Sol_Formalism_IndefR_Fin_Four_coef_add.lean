-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.coef_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:02:18.8547+00:00
-- url     : https://prove2.me/submissions/4bacc240-c6da-4b71-8536-ec3a200276c3

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_trans
import Theorems.Thm_Formalism_IndefR_Fin_Four_coef_inv
import Theorems.Thm_Formalism_IndefR_Fin_Four_avg_mul


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
include hχl hχr hχ0 hLL hoY hfinX
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {Φ Φ' : W → ℂ} (h : IsSB L X Φ) (h' : IsSB L X Φ') (a : W) {y : W} (hy : y ∈ Y) :
    coef χ L X (Φ + Φ') a y = coef χ L X Φ a y + coef χ L X Φ' a y := by
  have inv_mul : ∀ (H : AddSubgroup W) (g : W → ℂ) (k m : ℕ), IsInv k H g → IsInv (k * m) H g := by
    intro H g k m h t ht u hu
    rw [← smul_smul]
    exact h t ht _ (H.nsmul_mem hu m)
  have avg_mul : ∀ (H : AddSubgroup W) (g : W → ℂ) (k m : ℕ), Finite (Qt k H) → Finite (Qt (k * m) H) →
      IsInv k H g → avg (k * m) H g = avg k H g := by
    intro H g k m hfk hfkm hg
    classical
    haveI := Fintype.ofFinite (Qt k H)
    haveI := Fintype.ofFinite (Qt (k * m) H)
    have hle : (smulSub (k * m) H).addSubgroupOf H ≤ (smulSub k H).addSubgroupOf H := by
      intro h hh
      rw [AddSubgroup.mem_addSubgroupOf] at hh ⊢
      simp only [smulSub, AddSubgroup.mem_map, nsmulAddMonoidHom_apply] at hh ⊢
      obtain ⟨v, hv, hv'⟩ := hh
      exact ⟨m • v, H.nsmul_mem hv m, by rw [← hv', smul_smul]⟩
    let π : Qt (k * m) H →+ Qt k H := QuotientAddGroup.map _ _ (AddMonoidHom.id H) (fun x hx => hle hx)
    have hπ : ∀ x : H, π (QuotientAddGroup.mk x) = QuotientAddGroup.mk x := fun x => rfl
    have hsurj : Function.Surjective π := by
      intro r
      refine ⟨QuotientAddGroup.mk r.out, ?_⟩
      rw [hπ, QuotientAddGroup.out_eq']
    have hval : ∀ q : Qt (k * m) H, g ((q.out : H) : W) = g (((π q).out : H) : W) := by
      intro q
      have hq : π q = QuotientAddGroup.mk q.out := by rw [← hπ, QuotientAddGroup.out_eq']
      have h1 := (QuotientAddGroup.out_eq' (π q)).trans hq
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
      simp only [smulSub, AddSubgroup.mem_map, nsmulAddMonoidHom_apply] at h1
      obtain ⟨v, hv, hv'⟩ := h1
      have h2 : ((q.out : H) : W) = ((π q).out : H) + k • v := by
        rw [hv']
        push_cast
        abel
      rw [h2]
      exact hg _ ((π q).out).2 v hv
    obtain ⟨N, hN⟩ : ∃ N, N = (Finset.univ.filter fun q : Qt (k * m) H => π q = 0).card := ⟨_, rfl⟩
    have hfib : ∀ r : Qt k H, (Finset.univ.filter fun q : Qt (k * m) H => π q = r).card = N := by
      intro r
      rw [hN]
      exact AddMonoidHom.card_fiber_eq_of_mem_range π (hsurj r) (hsurj 0)
    have hN0 : N ≠ 0 := by
      rw [hN]
      exact (Finset.card_pos.2 ⟨0, by simp⟩).ne'
    have hsum : ∑ q : Qt (k * m) H, g ((q.out : H) : W) = N * ∑ r : Qt k H, g ((r.out : H) : W) := by
      rw [Fintype.sum_congr _ _ hval, Finset.sum_comp (fun r : Qt k H => g ((r.out : H) : W)) π,
        Finset.image_univ_of_surjective hsurj]
      simp_rw [hfib]
      rw [← Finset.smul_sum, nsmul_eq_mul]
    have hcard : Fintype.card (Qt (k * m) H) = N * Fintype.card (Qt k H) := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
      simp_rw [hfib]
      simp [mul_comm]
    unfold avg
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, hsum, hcard]
    have hN0' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
    push_cast
    field_simp
  obtain ⟨k1, hk1, hi1⟩ := coef_inv (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hoY := hoY) h a hy
  obtain ⟨k2, hk2, hi2⟩ := coef_inv (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hoY := hoY) h' a hy
  unfold coef
  obtain ⟨g1, hg1⟩ : ∃ g : W → ℂ, g = fun t => Φ (a + t) * (χ t y)⁻¹ := ⟨_, rfl⟩
  obtain ⟨g2, hg2⟩ : ∃ g : W → ℂ, g = fun t => Φ' (a + t) * (χ t y)⁻¹ := ⟨_, rfl⟩
  rw [← hg1] at hi1
  rw [← hg2] at hi2
  rw [← hg1, ← hg2]
  have hsum : (fun t => (Φ + Φ') (a + t) * (χ t y)⁻¹) = fun t => g1 t + g2 t := by
    funext t; rw [hg1, hg2]; simp [add_mul]
  rw [hsum]
  have hi3 : IsInv (k1 * k2) (L ⊓ X) (fun t => g1 t + g2 t) := by
    intro t ht u hu
    have e1 := inv_mul _ _ k1 k2 hi1 t ht u hu
    have e2 := inv_mul _ _ k2 k1 hi2 t ht u hu
    rw [mul_comm k2 k1] at e2
    show g1 (t + (k1 * k2) • u) + g2 (t + (k1 * k2) • u) = g1 t + g2 t
    rw [e1, e2]
  have hex1 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) g1 := ⟨k1, hk1, hi1⟩
  have hex2 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) g2 := ⟨k2, hk2, hi2⟩
  have hex3 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => g1 t + g2 t) := ⟨k1 * k2, Nat.mul_pos hk1 hk2, hi3⟩
  unfold integ
  rw [dif_pos hex1, dif_pos hex2, dif_pos hex3]
  have hK1 := hex1.choose_spec.1
  have hI1 := hex1.choose_spec.2
  have hK2 := hex2.choose_spec.1
  have hI2 := hex2.choose_spec.2
  have hK3 := hex3.choose_spec.1
  have hI3 := hex3.choose_spec.2
  have hpos : 0 < hex1.choose * (hex2.choose * hex3.choose) := by positivity
  have f1 := avg_mul _ _ hex1.choose (hex2.choose * hex3.choose) (hfinX _ hK1) (hfinX _ hpos) hI1
  have f2 := avg_mul _ _ hex2.choose (hex1.choose * hex3.choose) (hfinX _ hK2)
    (hfinX _ (by positivity)) hI2
  have f3 := avg_mul _ _ hex3.choose (hex1.choose * hex2.choose) (hfinX _ hK3)
    (hfinX _ (by positivity)) hI3
  have e2 : hex2.choose * (hex1.choose * hex3.choose) = hex1.choose * (hex2.choose * hex3.choose) := by ring
  have e3 : hex3.choose * (hex1.choose * hex2.choose) = hex1.choose * (hex2.choose * hex3.choose) := by ring
  rw [e2] at f2
  rw [e3] at f3
  rw [← f1, ← f2, ← f3]
  haveI := hfinX _ hpos
  simp only [avg]
  rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _), mul_add]
end Formalism.IndefR.Fin.Four
