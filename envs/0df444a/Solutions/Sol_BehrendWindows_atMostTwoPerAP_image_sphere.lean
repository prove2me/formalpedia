-- Prove2me | solution 1 for BehrendWindows.atMostTwoPerAP_image_sphere
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-21T01:56:12.600911+00:00
-- url     : https://prove2.me/submissions/d0962e7d-6c5b-44bb-9626-3edbb332d39d

import Mathlib
import Definitions.Def_BehrendWindows_AtMostTwoPerAP
import Theorems.Thm_BehrendWindows_eq_of_sphere_relation
import Theorems.Thm_BehrendWindows_relation_of_map_relation

open BehrendWindows

private lemma map_lt_pow {b : ℕ} : ∀ {n : ℕ} (x : Fin n → ℕ), (∀ i, x i < b) →
    Behrend.map b x < b ^ n
  | 0, x, _ => by simp
  | n + 1, x, hx => by
    rw [Behrend.map_succ', pow_succ]
    have ih := map_lt_pow (x ∘ Fin.succ) (fun i => hx _)
    have h0 := hx 0
    have := Nat.mul_le_mul_right b (Nat.succ_le_of_lt ih)
    nlinarith

theorem solution (S d m k : ℕ) (hd : 1 ≤ d) (hm : 3 ≤ m) :
    AtMostTwoPerAP ((Behrend.sphere S d k).image (fun x => (Behrend.map (m * d) x : ℤ))) m ∧
      (Behrend.sphere S d k).image (fun x => (Behrend.map (m * d) x : ℤ)) ⊆
        Finset.Ico (0 : ℤ) ((m * d) ^ S : ℕ) := by
  have mem : ∀ {x : Fin S → ℕ}, x ∈ Behrend.sphere S d k → (∀ i, x i < d) ∧ ∑ i, x i ^ 2 = k := by
    intro x hx
    simp only [Behrend.sphere, Finset.mem_filter, Behrend.mem_box] at hx
    exact hx
  have hdm : d ≤ m * d := Nat.le_mul_of_pos_left d (by omega)
  refine ⟨?_, ?_⟩
  · intro a δ hδ k₁ k₂ k₃ h12 h23 h3 ⟨m1, m2, m3⟩
    obtain ⟨x, hx, ex⟩ := Finset.mem_image.1 m1
    obtain ⟨y, hy, ey⟩ := Finset.mem_image.1 m2
    obtain ⟨z, hz, ez⟩ := Finset.mem_image.1 m3
    obtain ⟨hxd, hxk⟩ := mem hx
    obtain ⟨hyd, hyk⟩ := mem hy
    obtain ⟨hzd, hzk⟩ := mem hz
    set p := k₃ - k₂ with hp
    set q := k₂ - k₁ with hq
    have hpz : (p : ℤ) = k₃ - k₂ := by rw [hp]; push_cast [h23.le]; ring
    have hqz : (q : ℤ) = k₂ - k₁ := by rw [hq]; push_cast [h12.le]; ring
    have rel : p * Behrend.map (m * d) x + q * Behrend.map (m * d) z =
        (p + q) * Behrend.map (m * d) y := by
      have : ((p * Behrend.map (m * d) x + q * Behrend.map (m * d) z : ℕ) : ℤ) =
          ((p + q) * Behrend.map (m * d) y : ℕ) := by
        push_cast
        rw [ex, ey, ez, hpz, hqz]
        ring
      exact_mod_cast this
    have vrel := relation_of_map_relation d m p q x y z hxd hyd hzd (by omega) (by omega)
      (by omega) rel
    have hxz := eq_of_sphere_relation x y z (hxk.trans hyk.symm) (hzk.trans hyk.symm) p q
      (by omega) (by omega) vrel
    subst hxz
    have : ((k₃ : ℤ) - k₁) * δ = 0 := by linear_combination ex - ez
    rcases mul_eq_zero.1 this with h0 | h0
    · omega
    · exact hδ h0
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ht
    have := map_lt_pow (b := m * d) x (fun i => ((mem hx).1 i).trans_le hdm)
    simp only [Finset.mem_Ico]
    exact ⟨by positivity, by exact_mod_cast this⟩
