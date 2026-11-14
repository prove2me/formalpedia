-- Prove2me | solution 1 for CountingLLL.DetCount.positive_probability_ratio_telescope
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:29:04.613232+00:00
-- url     : https://prove2.me/submissions/8bec183b-b4f5-4925-9fab-13a5e0a80cd1

import Definitions.Def_CountingLLL_DetCount_Expansion

set_option autoImplicit false
open scoped Classical
namespace CountingLLL.DetCount
open CSP

private theorem telescoping_nonzero_ratios (f : ℕ → ℝ) (n : ℕ)
    (hf : ∀ i ≤ n, f i ≠ 0) :
    (∏ i ∈ Finset.range n, f i / f (i + 1)) = f 0 / f n := by
  induction n with
  | zero => simp [hf 0 (by omega)]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih (fun i hi => hf i (by omega))]
    have h : f n ≠ 0 := hf n (by omega)
    field_simp

private theorem reciprocal_marginal_telescope (f : ℕ → ℝ) (n : ℕ)
    (hf : ∀ i ≤ n, f i ≠ 0) :
    (∏ j : Fin n, 1 / (1 - (1 - f (j.val + 1) / f j.val))) = f 0 / f n := by
  simp only [sub_sub_cancel, one_div_div]
  calc
    _ = ∏ i ∈ Finset.range n, f i / f (i + 1) :=
      Fin.prod_univ_eq_prod_range (fun i : ℕ => f i / f (i + 1)) n
    _ = f 0 / f n := telescoping_nonzero_ratios f n hf

private noncomputable def basePrefix (Φ : CSP) (B H : Finset (Fin Φ.m))
    (e : Fin (H \ B).card → Fin Φ.m) (i : ℕ) : Finset (Fin Φ.m) :=
  B ∪ (Finset.univ.filter (fun j : Fin (H \ B).card => j.val < i)).image e

private theorem enum_onto (Φ : CSP) (B H : Finset (Fin Φ.m))
    (e : Fin (H \ B).card → Fin Φ.m)
    (he : Function.Injective e ∧ ∀ j, e j ∈ H \ B) :
    Finset.univ.image e = H \ B := by
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
    exact he.2 j
  · rw [Finset.card_image_of_injective _ he.1]
    simp

private theorem basePrefix_zero (Φ : CSP) (B H : Finset (Fin Φ.m))
    (e : Fin (H \ B).card → Fin Φ.m) : basePrefix Φ B H e 0 = B := by simp [basePrefix]

private theorem basePrefix_succ (Φ : CSP) (B H : Finset (Fin Φ.m))
    (e : Fin (H \ B).card → Fin Φ.m) (i : Fin (H \ B).card) :
    basePrefix Φ B H e (i.val + 1) = insert (e i) (basePrefix Φ B H e i.val) := by
  ext c
  simp only [basePrefix, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro (hB | ⟨j, hj, rfl⟩)
    · exact Or.inr (Or.inl hB)
    · have hj' : j.val ≤ i.val := Nat.lt_succ_iff.mp hj
      rcases eq_or_lt_of_le hj' with h | h
      · left; congr 1; exact Fin.ext h
      · exact Or.inr (Or.inr ⟨j, h, rfl⟩)
  · rintro (rfl | hB | ⟨j, hj, rfl⟩)
    · exact Or.inr ⟨i, Nat.lt_succ_self _, rfl⟩
    · exact Or.inl hB
    · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, rfl⟩

private theorem basePrefix_fresh (Φ : CSP) (B H : Finset (Fin Φ.m))
    (e : Fin (H \ B).card → Fin Φ.m)
    (he : Function.Injective e ∧ ∀ j, e j ∈ H \ B) (i : Fin (H \ B).card) :
    e i ∉ basePrefix Φ B H e i.val := by
  simp only [basePrefix, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, not_or, not_exists]
  constructor
  · exact (Finset.mem_sdiff.mp (he.2 i)).2
  · intro j hj
    have hh : j = i := he.1 hj.2
    subst j
    exact Nat.lt_irrefl _ hj.1

private theorem basePrefix_erase (Φ : CSP) (B H : Finset (Fin Φ.m))
    (e : Fin (H \ B).card → Fin Φ.m)
    (he : Function.Injective e ∧ ∀ j, e j ∈ H \ B) (i : Fin (H \ B).card) :
    (basePrefix Φ B H e (i.val + 1)).erase (e i) = basePrefix Φ B H e i.val := by
  rw [basePrefix_succ]
  simp [basePrefix_fresh Φ B H e he]

private theorem basePrefix_full (Φ : CSP) (B H : Finset (Fin Φ.m)) (hBH : B ⊆ H)
    (e : Fin (H \ B).card → Fin Φ.m)
    (he : Function.Injective e ∧ ∀ j, e j ∈ H \ B) :
    basePrefix Φ B H e (H \ B).card = H := by
  have hU : Finset.univ.filter (fun j : Fin (H \ B).card => j.val < (H \ B).card) = Finset.univ := by
    ext j; simp [j.isLt]
  rw [basePrefix, hU, enum_onto Φ B H e he]
  exact Finset.union_sdiff_of_subset hBH

private theorem basePrefix_mono (Φ : CSP) (B H : Finset (Fin Φ.m))
    (e : Fin (H \ B).card → Fin Φ.m) {i j : ℕ} (h : i ≤ j) :
    basePrefix Φ B H e i ⊆ basePrefix Φ B H e j := by
  unfold basePrefix
  apply Finset.union_subset_union_right
  apply Finset.image_mono
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact lt_of_lt_of_le hx h

private theorem prefix_is_base_succ (Φ : CSP) (B H : Finset (Fin Φ.m))
    (e : Fin (H \ B).card → Fin Φ.m) (i : Fin (H \ B).card) :
    Φ.prefixFam B e i = basePrefix Φ B H e (i.val+1) := by
  unfold CSP.prefixFam basePrefix
  congr 1
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => Nat.lt_succ_of_le h, fun h => Nat.le_of_lt_succ h⟩

private theorem z_antitone (Φ : CSP) {E F : Finset (Fin Φ.m)} (h : E ⊆ F) : Φ.Z F ≤ Φ.Z E := by
  apply Finset.card_le_card
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  intro c hc
  exact hσ c (h hc)

theorem general_ratio_local (Φ : CSP)
    (B H : Finset (Fin Φ.m)) (hpos : 0 < Φ.Z H) (hBH : B ⊆ H)
    (e : Fin (H \ B).card → Fin Φ.m)
    (he : Function.Injective e ∧ ∀ j, e j ∈ H \ B) :
    Φ.prob (Φ.SatAll B) / Φ.prob (Φ.SatAll H) =
      ∏ j : Fin (H \ B).card, 1 / (1 - Φ.r (Φ.prefixFam B e j) (e j)) := by
  let f : ℕ → ℝ := fun i => (Φ.Z (basePrefix Φ B H e i) : ℝ)
  have hf : ∀ i ≤ (H \ B).card, f i ≠ 0 := by
    intro i hi
    have hz := z_antitone Φ (basePrefix_mono Φ B H e hi)
    rw [basePrefix_full Φ B H hBH e he] at hz
    have hp : 0 < Φ.Z (basePrefix Φ B H e i) := lt_of_lt_of_le hpos hz
    change (Φ.Z (basePrefix Φ B H e i) : ℝ) ≠ 0
    exact_mod_cast (ne_of_gt hp)
  have hc : (Fintype.card Φ.Config : ℝ) ≠ 0 := by
    letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Φ.Config))
  have hleft : Φ.prob (Φ.SatAll B) / Φ.prob (Φ.SatAll H) = f 0 / f (H \ B).card := by
    change ((Φ.Z B : ℝ) / (Fintype.card Φ.Config : ℝ)) /
      ((Φ.Z H : ℝ) / (Fintype.card Φ.Config : ℝ)) = _
    rw [div_div_div_cancel_right₀ hc]
    simp only [f, basePrefix_zero, basePrefix_full Φ B H hBH e he]
  rw [hleft, ← reciprocal_marginal_telescope f (H \ B).card hf]
  apply Finset.prod_congr rfl
  intro j hj
  rw [prefix_is_base_succ, CSP.r, basePrefix_erase Φ B H e he j]

end CountingLLL.DetCount

open CountingLLL.DetCount

theorem solution (Φ : CSP)
    (B H : Finset (Fin Φ.m)) (hpos : 0 < Φ.Z H) (hBH : B ⊆ H)
    (e : Fin (H \ B).card → Fin Φ.m)
    (he : Function.Injective e ∧ ∀ j, e j ∈ H \ B) :
    Φ.prob (Φ.SatAll B) / Φ.prob (Φ.SatAll H) =
      ∏ j : Fin (H \ B).card, 1 / (1 - Φ.r (Φ.prefixFam B e j) (e j)) :=
  general_ratio_local Φ B H hpos hBH e he
