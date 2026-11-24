-- Prove2me | solution 1 for Formalism.CohomologicalDescent.shiftSumBound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:40:49.974+00:00
-- url     : https://prove2.me/submissions/42409f0c-3b88-4786-9c47-a7d81df9afd7

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeBoundHolds
import Theorems.Thm_Formalism_CohomologicalDescent_we_msum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution : KapSum := by
  intro l b t κ U kap hl htl hU hkap hle
  have : NeZero l := ⟨by omega⟩
  have hlpos : (0 : ℤ) < (l : ℤ) := by exact_mod_cast hl
  obtain ⟨lo, hlo⟩ : ∃ lo : ℤ, lo = b - (κ : ℤ) := ⟨_, rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi : ℤ, hi = b + (t : ℤ) - 1 + (κ : ℤ) := ⟨_, rfl⟩
  have hwin : hi < lo + l := by omega
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℤ, ∀ u, g u = lo + (u - lo) % (l : ℤ) := ⟨_, fun _ => rfl⟩
  have g_ge : ∀ u, lo ≤ g u := fun u => by
    rw [hg]
    have := Int.emod_nonneg (u - lo) hlpos.ne'
    linarith
  have g_fix : ∀ v, lo ≤ v → v ≤ hi → g v = v := fun v h1 h2 => by
    rw [hg, Int.emod_eq_of_lt (by linarith) (by linarith)]
    ring
  have g_mod : ∀ u, g u ≡ u [ZMOD (l : ℤ)] := fun u => by
    have h := (Int.mod_modEq (u - lo) (l : ℤ)).add_left lo
    rw [hg]
    rwa [show lo + (u - lo) = u by ring] at h
  have g_cong : ∀ u v, u ≡ v [ZMOD (l : ℤ)] → g u = g v := fun u v h => by
    have e : (u - lo) % (l : ℤ) = (v - lo) % (l : ℤ) := Int.ModEq.sub_right lo h
    rw [hg, hg, e]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ZMod l → ℤ, ∀ u : ℤ, ρ (u : ZMod l) = g u :=
    ⟨fun z => lo + ((z - (lo : ZMod l)).val : ℤ), fun u => by
      show lo + ((((u : ZMod l) - (lo : ZMod l))).val : ℤ) = g u
      rw [← Int.cast_sub, ZMod.val_intCast, hg]⟩
  have hvW : ∀ s : Fin t, lo ≤ b + ((s : ℕ) : ℤ) - kap s ∧ b + ((s : ℕ) : ℤ) - kap s ≤ hi :=
    fun s => by
      have h1 := s.isLt
      have h2 := abs_le.1 (hkap s)
      omega
  have hY : Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val ≤
      Multiset.map g U.val := by
    have h1 := Multiset.map_le_map (f := ρ) hle
    rw [Multiset.map_map, Multiset.map_map] at h1
    refine Eq.trans_le (Multiset.map_congr rfl fun s _ => ?_)
      (h1.trans_eq (Multiset.map_congr rfl fun u _ => ?_))
    · simp only [Function.comp_apply]
      rw [hρ, g_fix _ (hvW s).1 (hvW s).2]
    · simp only [Function.comp_apply]
      rw [hρ]
  have hYA : Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val ≤
      Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) := by
    have hself : Multiset.filter (fun x => x ≤ hi)
        (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val) =
        Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val :=
      Multiset.filter_eq_self.2 (fun a ha => by
        rw [Multiset.mem_map] at ha
        obtain ⟨s, -, rfl⟩ := ha
        exact (hvW s).2)
    rw [← hself]
    exact Multiset.filter_le_filter (p := fun x => x ≤ hi) hY
  have hin : ∀ a ∈ Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val), lo ≤ a ∧ a ≤ hi := by
    intro a ha
    rw [Multiset.mem_filter, Multiset.mem_map] at ha
    obtain ⟨⟨u, -, rfl⟩, h⟩ := ha
    exact ⟨g_ge u, h⟩
  have hF : Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) =
      Multiset.map g (Multiset.filter (fun u => g u ≤ hi) U.val) := by
    rw [Multiset.filter_map]
    exact congrArg (Multiset.map g) (Multiset.filter_congr fun _ _ => Iff.rfl)
  have hfirst : Multiset.filter (fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1))
      (Multiset.filter (fun u => g u ≤ hi) U.val) =
      Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val := by
    have hinj : Function.Injective (fun s : Fin t => b + ((s : ℕ) : ℤ)) := by
      intro s1 s2 h
      have h' : b + ((s1 : ℕ) : ℤ) = b + ((s2 : ℕ) : ℤ) := h
      exact Fin.ext (by omega)
    have hnd1 : (Multiset.filter (fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1))
        (Multiset.filter (fun u => g u ≤ hi) U.val)).Nodup := by
      apply Multiset.Nodup.filter
      apply Multiset.Nodup.filter
      exact U.nodup
    rw [Multiset.Nodup.ext hnd1 (Multiset.Nodup.map hinj (Finset.nodup _))]
    intro a
    simp only [Multiset.mem_filter, Finset.mem_val, Finset.mem_Icc, Multiset.mem_map,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨-, -⟩, h1, h2⟩
      have hn := Int.toNat_of_nonneg (show 0 ≤ a - b by omega)
      refine ⟨⟨(a - b).toNat, by omega⟩, ?_⟩
      show b + (((a - b).toNat : ℕ) : ℤ) = a
      omega
    · rintro ⟨s, rfl⟩
      have hs := s.isLt
      refine ⟨⟨hU s, ?_⟩, by omega, by omega⟩
      rw [g_fix _ (by omega) (by omega)]
      omega
  have hA : Multiset.filter (fun x => x ≤ hi) (Multiset.map g U.val) =
      Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val +
      Multiset.map g (Multiset.filter (fun u => u ∉ Finset.Icc b (b + (t : ℤ) - 1))
        (Multiset.filter (fun u => g u ≤ hi) U.val)) := by
    rw [hF]
    conv_lhs => rw [← Multiset.filter_add_not (p := fun u => u ∈ Finset.Icc b (b + (t : ℤ) - 1))
      (s := Multiset.filter (fun u => g u ≤ hi) U.val)]
    rw [Multiset.map_add, hfirst, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun s _ => by
      have hs := s.isLt
      simp only [Function.comp_apply]
      exact g_fix _ (by omega) (by omega)
  have hR : ∀ u, (∃ x ∈ Finset.Icc (b - (κ : ℤ)) (b + (t : ℤ) - 1 + (κ : ℤ)),
      x ≡ u [ZMOD (l : ℤ)]) ↔ g u ≤ hi := by
    intro u
    constructor
    · rintro ⟨x, hx, hxu⟩
      rw [Finset.mem_Icc] at hx
      rw [← g_cong x u hxu, g_fix x (by omega) (by omega)]
      omega
    · intro hu
      exact ⟨g u, Finset.mem_Icc.2 ⟨by have := g_ge u; omega, by omega⟩, g_mod u⟩
  have hcard : Multiset.card (Multiset.filter (fun u => u ∉ Finset.Icc b (b + (t : ℤ) - 1))
      (Multiset.filter (fun u => g u ≤ hi) U.val)) = mwCount l b t κ U := by
    unfold mwCount
    rw [← Finset.card_val, Finset.filter_val, Finset.filter_val,
      Multiset.filter_filter, Multiset.filter_filter]
    congr 1
    have e : Multiset.filter (fun a => a ∉ Finset.Icc b (b + (t : ℤ) - 1) ∧ g a ≤ hi) U.val =
        Multiset.filter (fun a => (∃ x ∈ Finset.Icc (b - (κ : ℤ)) (b + (t : ℤ) - 1 + (κ : ℤ)),
          x ≡ a [ZMOD (l : ℤ)]) ∧ a ∉ Finset.Icc b (b + (t : ℤ) - 1)) U.val :=
      Multiset.filter_congr (fun u _ => by rw [hR u]; exact and_comm)
    convert e using 2
  have key := we_msum _ _ _ _ lo hi hYA hA
    (by rw [Multiset.card_map, Multiset.card_map]) hin
  rw [Multiset.card_map, hcard] at key
  have hBs : (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ)) Finset.univ.val).sum =
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ)) := (Finset.sum_eq_multiset_sum _ _).symm
  have hYs : (Multiset.map (fun s : Fin t => b + ((s : ℕ) : ℤ) - kap s) Finset.univ.val).sum =
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ) - kap s) := (Finset.sum_eq_multiset_sum _ _).symm
  rw [hBs, hYs, Finset.sum_sub_distrib, sub_sub_cancel] at key
  refine key.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  omega
end Formalism.CohomologicalDescent
