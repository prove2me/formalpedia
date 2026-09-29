-- Prove2me | solution 1 for CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d042fa9a-4759-5a0c-a06f-26f441693e82

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_RatPair_exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add
import Theorems.Thm_CerednikDrinfeld_Omega_RatPair_v_evalAt_lt_of_forall_v_evalAt_add_evalAt_lt_on_sphere
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt.CerednikDrinfeld.Omega Polynomial Filter"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.RatPair Omega.RatPair.exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add Omega.RatPair.v_evalAt_lt_of_forall_v_evalAt_add_evalAt_lt_on_sphere"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "RatPair RatPair.add RatPair.neg RatPair.isPoleFreeOn_add RatPair.isPoleFreeOn_neg RatPair.evalAt_add RatPair.evalAt_neg vRestrict v_lt_iff_vRestrict_lt tendstoUniformly_iff_vRestrict exists_bound holOn mem_holOn_iff RatPair.exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add RatPair.v_evalAt_lt_of_forall_v_evalAt_add_evalAt_lt_on_sphere"
namespace TwoGlueAux
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem unif_eps {α : Type} {F : ℕ → α → K} {φ : α → K} (h : TendstoUniformly F φ atTop) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z, Valued.v (F k z - φ z) < Valued.v e := fun e he => by
  rw [tendstoUniformly_iff_vRestrict] at h
  have hwe : vRestrict K e ≠ 0 := by rwa [ne_eq, map_eq_zero]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h (Units.mk0 _ hwe))
  exact ⟨N, fun k hk z => (v_lt_iff_vRestrict_lt K _ _).2 (hN k hk z)⟩

theorem tendstoUniformly_of_eps {α : Type} {F : ℕ → α → K} {φ : α → K}
    (h : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z, Valued.v (F k z - φ z) < Valued.v e) :
    TendstoUniformly F φ atTop := by
  rw [tendstoUniformly_iff_vRestrict]
  intro γ
  obtain ⟨e, he⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass (Valued.v (R := K)) : K →*₀ Γ₀)
    (γ : MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := K)) : K →*₀ Γ₀))
  have he' : vRestrict K e = γ := he
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0, map_zero] at he'
    exact γ.ne_zero he'.symm
  obtain ⟨N, hN⟩ := h e he0
  refine Filter.eventually_atTop.2 ⟨N, fun k hk z => ?_⟩
  rw [← he']
  exact (v_lt_iff_vRestrict_lt K _ _).1 (hN k hk z)

theorem degree_cross_lt {a b c d : K[X]} (ha : a.degree < b.degree) (hc : c.degree < d.degree)
    (hb : b ≠ 0) (hd : d ≠ 0) : (a * d + -c * b).degree < (b * d).degree := by
  rw [degree_mul]
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
  · refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    exact WithBot.add_lt_add_right (degree_ne_bot.mpr hd) ha
  · refine lt_of_le_of_lt (degree_mul_le _ _) ?_
    rw [degree_neg, add_comm b.degree]
    exact WithBot.add_lt_add_right (degree_ne_bot.mpr hb) hc

theorem den_ne_zero_of_isPoleFreeOn {r : RatPair K} {S : Set K} (h : r.IsPoleFreeOn S) {z : K} (hz : z ∈ S) :
    r.den ≠ 0 := fun h0 => h z hz (by rw [h0, eval_zero])

end CerednikDrinfeld.Omega.TwoGlueAux

open CerednikDrinfeld.Omega.TwoGlueAux in

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S₁ S₂ : Set K) (t₀ π₀ : K) (hπ₀ : π₀ ≠ 0) (Z : Finset K)
    (h₁ : ∀ z ∈ S₁, Valued.v π₀ ≤ Valued.v (z - t₀))
    (h₂ : ∀ z ∈ S₂, z ∈ S₁ ∨ Valued.v (z - t₀) < Valued.v π₀)
    (hC : ∀ z : K, Valued.v (z - t₀) = Valued.v π₀ → (∀ ζ ∈ Z, Valued.v π₀ ≤ Valued.v (z - ζ)) → z ∈ S₁ ∩ S₂)
    (h : ↥(S₁ ∪ S₂) → K)
    (hh₁ : (fun z : ↥S₁ => h ⟨(z : K), Or.inl z.2⟩) ∈ holOn K S₁)
    (hh₂ : (fun z : ↥S₂ => h ⟨(z : K), Or.inr z.2⟩) ∈ holOn K S₂) :
    h ∈ holOn K (S₁ ∪ S₂) := by
  classical
  rw [mem_holOn_iff] at hh₁ hh₂ ⊢
  obtain ⟨C₁, hC₁⟩ := hh₁.bounded
  obtain ⟨C₂, hC₂⟩ := hh₂.bounded
  obtain ⟨r₁, hpf₁, -, hlim₁⟩ := hh₁
  obtain ⟨r₂, hpf₂, -, hlim₂⟩ := hh₂
  have u₁ := unif_eps hlim₁
  have u₂ := unif_eps hlim₂

  choose A₁ B₁ hA₁ hdA₁ hB₁ hs₁ using fun k => CerednikDrinfeld.Omega.RatPair.exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add K (r₁ k) t₀ π₀ hπ₀
  choose A₂ B₂ hA₂ hdA₂ hB₂ hs₂ using fun k => CerednikDrinfeld.Omega.RatPair.exists_isPoleFreeOn_le_and_degree_lt_and_evalAt_eq_add K (r₂ k) t₀ π₀ hπ₀

  have hrimpt : Valued.v π₀ ≤ Valued.v (t₀ + π₀ - t₀) := by rw [add_sub_cancel_left]
  have hA₁ne : ∀ k, (A₁ k).den ≠ 0 := fun k => den_ne_zero_of_isPoleFreeOn (hA₁ k) (Or.inr hrimpt)
  have hA₂ne : ∀ k, (A₂ k).den ≠ 0 := fun k => den_ne_zero_of_isPoleFreeOn (hA₂ k) (Or.inr hrimpt)

  have hGpf : ∀ k, ((A₂ k).add (B₁ k)).IsPoleFreeOn (S₁ ∪ S₂) := by
    intro k z hz
    refine RatPair.isPoleFreeOn_add (S := S₁ ∪ S₂) (fun w hw => ?_) (fun w hw => ?_) z hz
    · rcases hw with hw | hw
      · exact hA₂ k w (Or.inr (h₁ w hw))
      · exact hA₂ k w (Or.inl (hpf₂ k w hw))
    · rcases hw with hw | hw
      · exact hB₁ k w (Or.inl (hpf₁ k w hw))
      · rcases h₂ w hw with hw' | hw'
        · exact hB₁ k w (Or.inl (hpf₁ k w hw'))
        · exact hB₁ k w (Or.inr hw')

  have hstep : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ w : ↥(S₁ ∪ S₂),
      Valued.v (((A₂ k).add (B₁ k)).evalAt w - h w) < Valued.v e := by
    intro e he
    obtain ⟨N₁, hN₁⟩ := u₁ e he
    obtain ⟨N₂, hN₂⟩ := u₂ e he
    refine ⟨max N₁ N₂, fun k hk w => ?_⟩
    have hk₁ : N₁ ≤ k := le_of_max_le_left hk
    have hk₂ : N₂ ≤ k := le_of_max_le_right hk

    have hor := CerednikDrinfeld.Omega.RatPair.v_evalAt_lt_of_forall_v_evalAt_add_evalAt_lt_on_sphere K
      ((A₂ k).add (A₁ k).neg) ((B₂ k).add (B₁ k).neg) t₀ π₀ hπ₀ Z
      (RatPair.isPoleFreeOn_add (fun z hz => hA₂ k z (Or.inr hz))
        (RatPair.isPoleFreeOn_neg (fun z hz => hA₁ k z (Or.inr hz))))
      (degree_cross_lt (hdA₂ k) (hdA₁ k) (hA₂ne k) (hA₁ne k))
      (RatPair.isPoleFreeOn_add (fun z hz => hB₂ k z (Or.inr hz))
        (RatPair.isPoleFreeOn_neg (fun z hz => hB₁ k z (Or.inr hz))))
      (fun z hz hZ => by
        obtain ⟨hz₁, hz₂⟩ := hC z hz hZ
        simp only [RatPair.add, RatPair.neg, eval_mul]
        exact mul_ne_zero (hB₂ k z (Or.inl (hpf₂ k z hz₂))) (hB₁ k z (Or.inl (hpf₁ k z hz₁))))
      e
      (fun z hz hZ => by
        obtain ⟨hz₁, hz₂⟩ := hC z hz hZ
        have hzext : Valued.v π₀ ≤ Valued.v (z - t₀) := hz.ge
        have eA : ((A₂ k).add (A₁ k).neg).evalAt z = (A₂ k).evalAt z - (A₁ k).evalAt z := by
          rw [RatPair.evalAt_add (q := (A₁ k).neg) (hA₂ k z (Or.inr hzext)) (hA₁ k z (Or.inr hzext)), RatPair.evalAt_neg,
            ← sub_eq_add_neg]
        have eB : ((B₂ k).add (B₁ k).neg).evalAt z = (B₂ k).evalAt z - (B₁ k).evalAt z := by
          rw [RatPair.evalAt_add (q := (B₁ k).neg) (hB₂ k z (Or.inl (hpf₂ k z hz₂))) (hB₁ k z (Or.inl (hpf₁ k z hz₁))),
            RatPair.evalAt_neg, ← sub_eq_add_neg]
        rw [eA, eB, show (A₂ k).evalAt z - (A₁ k).evalAt z + ((B₂ k).evalAt z - (B₁ k).evalAt z) =
            ((A₂ k).evalAt z + (B₂ k).evalAt z) - ((A₁ k).evalAt z + (B₁ k).evalAt z) by ring,
          ← hs₂ k z (hpf₂ k z hz₂), ← hs₁ k z (hpf₁ k z hz₁),
          show (r₂ k).evalAt z - (r₁ k).evalAt z =
            ((r₂ k).evalAt z - h ⟨z, Or.inr hz₂⟩) - ((r₁ k).evalAt z - h ⟨z, Or.inl hz₁⟩) by ring]
        exact Valuation.map_sub_lt _ (hN₂ k hk₂ ⟨z, hz₂⟩) (hN₁ k hk₁ ⟨z, hz₁⟩))
    obtain ⟨hin, hout⟩ := hor
    obtain ⟨w, hw⟩ := w
    by_cases hw₁ : w ∈ S₁
    ·
      have hzext : Valued.v π₀ ≤ Valued.v (w - t₀) := h₁ w hw₁
      have eG : ((A₂ k).add (B₁ k)).evalAt w = (A₂ k).evalAt w + (B₁ k).evalAt w :=
        RatPair.evalAt_add (hA₂ k w (Or.inr hzext)) (hB₁ k w (Or.inl (hpf₁ k w hw₁)))
      have eA : ((A₂ k).add (A₁ k).neg).evalAt w = (A₂ k).evalAt w - (A₁ k).evalAt w := by
        rw [RatPair.evalAt_add (q := (A₁ k).neg) (hA₂ k w (Or.inr hzext)) (hA₁ k w (Or.inr hzext)), RatPair.evalAt_neg,
          ← sub_eq_add_neg]
      have e1 : ((A₂ k).add (B₁ k)).evalAt w - h ⟨w, hw⟩ =
          ((A₂ k).add (A₁ k).neg).evalAt w + ((r₁ k).evalAt w - h ⟨w, Or.inl hw₁⟩) := by
        rw [eG, eA, hs₁ k w (hpf₁ k w hw₁)]
        ring
      rw [e1]
      exact Valuation.map_add_lt _ (hin w hzext) (hN₁ k hk₁ ⟨w, hw₁⟩)
    ·
      have hw₂ : w ∈ S₂ := hw.resolve_left hw₁
      have hwin : Valued.v (w - t₀) < Valued.v π₀ := (h₂ w hw₂).resolve_left hw₁
      have eG : ((A₂ k).add (B₁ k)).evalAt w = (A₂ k).evalAt w + (B₁ k).evalAt w :=
        RatPair.evalAt_add (hA₂ k w (Or.inl (hpf₂ k w hw₂))) (hB₁ k w (Or.inr hwin))
      have eB : ((B₂ k).add (B₁ k).neg).evalAt w = (B₂ k).evalAt w - (B₁ k).evalAt w := by
        rw [RatPair.evalAt_add (q := (B₁ k).neg) (hB₂ k w (Or.inr hwin)) (hB₁ k w (Or.inr hwin)), RatPair.evalAt_neg,
          ← sub_eq_add_neg]
      have e1 : ((A₂ k).add (B₁ k)).evalAt w - h ⟨w, hw⟩ =
          -((B₂ k).add (B₁ k).neg).evalAt w + ((r₂ k).evalAt w - h ⟨w, Or.inr hw₂⟩) := by
        rw [eG, eB, hs₂ k w (hpf₂ k w hw₂)]
        ring
      rw [e1]
      refine Valuation.map_add_lt _ ?_ (hN₂ k hk₂ ⟨w, hw₂⟩)
      rw [Valuation.map_neg]
      exact hout w hwin

  obtain ⟨N₀, hN₀⟩ := hstep 1 one_ne_zero
  obtain ⟨Bd, -, hC₁B, hC₂B, h1B⟩ := exists_bound C₁ C₂
  refine ⟨fun k => (A₂ (k + N₀)).add (B₁ (k + N₀)), fun k => hGpf _, ⟨Bd, fun k w => ?_⟩,
    tendstoUniformly_of_eps fun e he => ?_⟩
  · have e1 : ((A₂ (k + N₀)).add (B₁ (k + N₀))).evalAt w =
        (((A₂ (k + N₀)).add (B₁ (k + N₀))).evalAt w - h w) + h w := by ring
    rw [e1]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · exact ((hN₀ (k + N₀) (Nat.le_add_left _ _) w).le.trans (by rw [map_one])).trans h1B
    · obtain ⟨w, hw⟩ := w
      rcases hw with hw' | hw'
      · exact (hC₁ ⟨w, hw'⟩).trans hC₁B
      · exact (hC₂ ⟨w, hw'⟩).trans hC₂B
  · obtain ⟨N, hN⟩ := hstep e he
    exact ⟨N, fun k hk w => hN (k + N₀) (le_trans hk (Nat.le_add_right _ _)) w⟩

end S_CerednikDrinfeld_Omega_mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt (solution)
