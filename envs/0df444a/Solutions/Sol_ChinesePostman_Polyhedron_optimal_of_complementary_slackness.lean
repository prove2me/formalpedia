-- Prove2me | solution 1 for ChinesePostman.Polyhedron.optimal_of_complementary_slackness
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:55:11.200737+00:00
-- url     : https://prove2.me/submissions/b6bc777f-9852-4d7e-9105-f11fd022d67e

import Mathlib
import Definitions.Def_ChinesePostman_Polyhedron_Setting

open Classical

namespace ChinesePostman.Polyhedron

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma card_mem_ends_mod (G : Graph V E) (S : Finset V) (e : E) :
    ∃ k : ℕ, (S.filter (fun n => n ∈ G.ends e)).card = 2 * k + (if Meets G e S then 1 else 0) := by
  have hne := G.loopless e
  induction h : G.ends e using Sym2.ind with
  | _ u v =>
    rw [h] at hne
    have huv : u ≠ v := by simpa using hne
    have hmem : ∀ n, n ∈ s(u, v) ↔ n = u ∨ n = v := fun n => by simp [Sym2.mem_iff]
    have hmeets : Meets G e S ↔ (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) := by
      unfold Meets
      rw [h]
      constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨ha, hb⟩
        · exact Or.inr ⟨ha, hb⟩
      · rintro (⟨a, b⟩ | ⟨a, b⟩)
        · exact ⟨u, v, rfl, a, b⟩
        · exact ⟨v, u, Sym2.eq_swap, a, b⟩
    have hfil : S.filter (fun n => n ∈ s(u, v)) = S.filter (fun n => n = u ∨ n = v) := by
      apply Finset.filter_congr; intro n _; rw [hmem]
    rw [hfil]
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · refine ⟨1, ?_⟩
      have : S.filter (fun n => n = u ∨ n = v) = {u, v} := by
        ext n; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl) <;> simp [*]
      rw [this, Finset.card_pair huv]
      simp [hmeets, hu, hv]
    · refine ⟨0, ?_⟩
      have : S.filter (fun n => n = u ∨ n = v) = {u} := by
        ext n; simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hn, rfl | rfl⟩ <;> simp_all
        · rintro rfl; simp [hu]
      rw [this]; simp [hmeets, hu, hv]
    · refine ⟨0, ?_⟩
      have : S.filter (fun n => n = u ∨ n = v) = {v} := by
        ext n; simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hn, rfl | rfl⟩ <;> simp_all
        · rintro rfl; simp [hv]
      rw [this]; simp [hmeets, hu, hv]
    · refine ⟨0, ?_⟩
      have : S.filter (fun n => n = u ∨ n = v) = ∅ := by
        ext n; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        rintro ⟨hn, rfl | rfl⟩ <;> simp_all
      rw [this]; simp [hmeets, hu, hv]

lemma sum_incident_eq (G : Graph V E) (z : E → ℤ) (S : Finset V) :
    ∃ m : ℤ, ∑ n ∈ S, incidentSum G z n = 2 * m + cutSum G z S := by
  have h1 : ∑ n ∈ S, incidentSum G z n = ∑ e, z e * ((S.filter (fun n => n ∈ G.ends e)).card : ℤ) := by
    unfold incidentSum
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    rw [← Finset.sum_filter]
    simp [mul_comm]
  choose k hk using card_mem_ends_mod G S
  refine ⟨∑ e, z e * k e, ?_⟩
  rw [h1]
  unfold cutSum
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro e _
  rw [hk e]; push_cast
  split_ifs <;> ring

theorem odd_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (z : E → ℤ)
    (hz : ∀ n, incidentSum G z n ≡ bParity G n [ZMOD 2])
    (S : Finset V) (hS : IsOddSet G S) :
    cutSum G z S ≡ 1 [ZMOD 2] := by
  obtain ⟨m, hm⟩ := sum_incident_eq G z S
  have hb : ∑ n ∈ S, bParity G n = ((S.filter (fun n => Odd (degree G n))).card : ℤ) := by
    unfold bParity
    rw [Finset.sum_ite]; simp
  obtain ⟨j, hj⟩ := hS
  have h2 : 2 ∣ ∑ n ∈ S, (incidentSum G z n - bParity G n) :=
    Finset.dvd_sum (fun n _ => (Int.modEq_iff_dvd.mp (hz n).symm |> fun h => by
      simpa using h))
  rw [Finset.sum_sub_distrib, hm, hb, hj] at h2
  rw [Int.modEq_iff_dvd]
  obtain ⟨t, ht⟩ := h2
  exact ⟨-(t) + m - 0 + (-j) , by push_cast at ht; linarith⟩

lemma cutSum_nonneg (G : Graph V E) (x : E → ℝ) (hx : ∀ e, 0 ≤ x e) (S : Finset V) :
    0 ≤ cutSum G x S := Finset.sum_nonneg (fun e _ => hx e)

lemma cutSum_mono (G : Graph V E) (x x' : E → ℝ) (h : ∀ e, x e ≤ x' e) (S : Finset V) :
    cutSum G x S ≤ cutSum G x' S := Finset.sum_le_sum (fun e _ => h e)

lemma cutSum_comb (G : Graph V E) (x y : E → ℝ) (a b : ℝ) (S : Finset V) :
    cutSum G (fun e => a * x e + b * y e) S = a * cutSum G x S + b * cutSum G y S := by
  unfold cutSum
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

lemma postman_convex (G : Graph V E) : Convex ℝ (postmanPolyhedron G) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun e => ?_, fun S hS => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e))
  · have := cutSum_comb G x y a b S
    have e1 : (a • x + b • y) = fun e => a * x e + b * y e := by
      funext e; simp
    rw [e1, this]
    have h1 := hx.2 S hS
    have h2 := hy.2 S hS
    nlinarith

theorem hull_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) :
    convexHull ℝ (parityPoints G) ⊆ postmanPolyhedron G := by
  apply convexHull_min _ (postman_convex G)
  rintro x ⟨z, hz0, hz, rfl⟩
  refine ⟨fun e => by show (0:ℝ) ≤ (z e : ℝ); exact_mod_cast hz0 e, fun S hS => ?_⟩
  have hodd := odd_core G z hz S hS
  have hnn : 0 ≤ cutSum G z S := Finset.sum_nonneg (fun e _ => hz0 e)
  have hne : cutSum G z S ≠ 0 := by
    intro h0; rw [h0] at hodd
    have := Int.emod_emod_of_dvd 0 (dvd_refl 2)
    unfold Int.ModEq at hodd; simp at hodd
  have h1 : (1 : ℤ) ≤ cutSum G z S := by omega
  have : (cutSum G (fun e => (z e : ℝ)) S) = ((cutSum G z S : ℤ) : ℝ) := by
    unfold cutSum; push_cast; rfl
  rw [this]; exact_mod_cast h1

lemma sum_cut_eq (G : Graph V E) (x : E → ℝ) (y : Finset V → ℝ) :
    ∑ S ∈ oddSets G, y S * cutSum G x S = ∑ e, x e * dualLoad G y e := by
  unfold cutSum dualLoad
  simp_rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro e _
  apply Finset.sum_congr rfl; intro S _
  split_ifs <;> ring

theorem wd_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (c : E → ℝ)
    (x : E → ℝ) (hx : x ∈ postmanPolyhedron G)
    (y : Finset V → ℝ) (hy : IsDualFeasible G c y) :
    dualValue G y ≤ objective c x := by
  have h1 : dualValue G y ≤ ∑ S ∈ oddSets G, y S * cutSum G x S := by
    unfold dualValue
    apply Finset.sum_le_sum; intro S hS
    have hS' : IsOddSet G S := by simpa [oddSets] using hS
    have := hx.2 S hS'
    have := hy.1 S hS
    nlinarith
  rw [sum_cut_eq] at h1
  refine h1.trans ?_
  unfold objective
  apply Finset.sum_le_sum; intro e _
  have := hy.2 e
  have := hx.1 e
  nlinarith

lemma dualValue_eq (G : Graph V E) (c : E → ℝ) (x : E → ℝ) (hx : x ∈ postmanPolyhedron G)
    (y : Finset V → ℝ) (hy : IsDualFeasible G c y)
    (h311 : ∀ e, 0 < x e → dualLoad G y e = c e)
    (h312 : ∀ S ∈ oddSets G, 0 < y S → cutSum G x S = 1) :
    objective c x = dualValue G y := by
  have h1 : dualValue G y = ∑ S ∈ oddSets G, y S * cutSum G x S := by
    unfold dualValue
    apply Finset.sum_congr rfl; intro S hS
    rcases (hy.1 S hS).eq_or_lt with h | h
    · rw [← h]; ring
    · rw [h312 S hS h]; ring
  rw [h1, sum_cut_eq]
  unfold objective
  apply Finset.sum_congr rfl; intro e _
  rcases (hx.1 e).eq_or_lt with h | h
  · rw [← h]; ring
  · rw [h311 e h]; ring

theorem cs_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (c : E → ℝ)
    (x : E → ℝ) (hx : x ∈ postmanPolyhedron G)
    (y : Finset V → ℝ) (hy : IsDualFeasible G c y)
    (h311 : ∀ e, 0 < x e → dualLoad G y e = c e)
    (h312 : ∀ S ∈ oddSets G, 0 < y S → cutSum G x S = 1) :
    (∀ x' ∈ postmanPolyhedron G, objective c x ≤ objective c x') ∧
      (∀ y' : Finset V → ℝ, IsDualFeasible G c y' → dualValue G y' ≤ dualValue G y) := by
  have h := dualValue_eq G c x hx y hy h311 h312
  refine ⟨fun x' hx' => ?_, fun y' hy' => ?_⟩
  · rw [h]; exact wd_core G c x' hx' y hy
  · rw [← h]; exact wd_core G c x hx y' hy'

lemma obj_shift (c x : E → ℝ) (e₀ : E) (t : ℝ) :
    objective c (x + t • Pi.single e₀ 1) = objective c x + t * c e₀ := by
  unfold objective
  have : ∀ e, c e * (x + t • Pi.single e₀ (1:ℝ) : E → ℝ) e = c e * x e + (if e = e₀ then t * c e₀ else 0) := by
    intro e
    by_cases h : e = e₀
    · subst h; simp; ring
    · simp [h, Pi.single_apply]
  simp_rw [this]
  rw [Finset.sum_add_distrib]; simp

lemma exists_k (c x : E → ℝ) (e₀ : E) (h : c e₀ < 0) (M : ℝ) :
    ∃ k : ℕ, 0 < k ∧ objective c (x + ((2 * k : ℕ) : ℝ) • Pi.single e₀ (1:ℝ)) < M := by
  set d := -c e₀ with hd
  have hdpos : 0 < d := by linarith
  refine ⟨⌈(objective c x - M) / d⌉₊ + 1, Nat.succ_pos _, ?_⟩
  rw [obj_shift]
  have h1 := Nat.le_ceil ((objective c x - M) / d)
  have h2 : (objective c x - M) ≤ (⌈(objective c x - M) / d⌉₊ : ℝ) * d := by
    have := (div_le_iff₀ hdpos).mp h1
    exact this
  push_cast
  have h3 : (0:ℝ) ≤ (⌈(objective c x - M) / d⌉₊ : ℝ) := Nat.cast_nonneg _
  have : c e₀ = -d := by linarith
  rw [this]; nlinarith

theorem unb_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (c : E → ℝ)
    (e₀ : E) (h : c e₀ < 0) :
    (∀ x ∈ postmanPolyhedron G, ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧
        x + t • Pi.single e₀ 1 ∈ postmanPolyhedron G ∧
        objective c (x + t • Pi.single e₀ 1) < M) ∧
      (∀ x ∈ parityPoints G, ∀ M : ℝ, ∃ k : ℕ, 0 < k ∧
        x + (2 * k : ℝ) • Pi.single e₀ 1 ∈ parityPoints G ∧
        objective c (x + (2 * k : ℝ) • Pi.single e₀ 1) < M) := by
  constructor
  · intro x hx M
    obtain ⟨k, hk, hlt⟩ := exists_k c x e₀ h M
    refine ⟨((2 * k : ℕ) : ℝ), Nat.cast_nonneg _, ?_, hlt⟩
    have hle : ∀ e, x e ≤ (x + ((2 * k : ℕ) : ℝ) • Pi.single e₀ (1:ℝ) : E → ℝ) e := by
      intro e
      by_cases hh : e = e₀
      · subst hh; simp
      · simp [hh, Pi.single_apply]
    refine ⟨fun e => (hx.1 e).trans (hle e), fun S hS => (hx.2 S hS).trans (cutSum_mono G _ _ hle S)⟩
  · intro x hx M
    obtain ⟨k, hk, hlt⟩ := exists_k c x e₀ h M
    refine ⟨k, hk, ?_, by simpa using hlt⟩
    obtain ⟨z, hz0, hz, rfl⟩ := hx
    refine ⟨fun e => z e + if e = e₀ then 2 * (k : ℤ) else 0, fun e => ?_, fun n => ?_, ?_⟩
    · have := hz0 e
      show (0:ℤ) ≤ z e + if e = e₀ then 2 * (k:ℤ) else 0
      split_ifs <;> omega
    · have : incidentSum G (fun e => z e + if e = e₀ then 2 * (k : ℤ) else 0) n
          = incidentSum G z n + (if n ∈ G.ends e₀ then 2 * (k : ℤ) else 0) := by
        unfold incidentSum
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_ite_eq']
        simp
      rw [this]
      refine Int.ModEq.trans ?_ (hz n)
      split_ifs
      · unfold Int.ModEq; omega
      · simp
    · funext e
      by_cases hh : e = e₀
      · subst hh; simp
      · simp [hh, Pi.single_apply]

end ChinesePostman.Polyhedron

open ChinesePostman.Polyhedron


theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ChinesePostman.Polyhedron.Graph V E) (c : E → ℝ)
    (x : E → ℝ) (hx : x ∈ postmanPolyhedron G)
    (y : Finset V → ℝ) (hy : IsDualFeasible G c y)
    (h311 : ∀ e, 0 < x e → dualLoad G y e = c e)
    (h312 : ∀ S ∈ oddSets G, 0 < y S → cutSum G x S = 1) :
    (∀ x' ∈ postmanPolyhedron G, objective c x ≤ objective c x') ∧
      (∀ y' : Finset V → ℝ, IsDualFeasible G c y' → dualValue G y' ≤ dualValue G y) := by
  exact cs_core G c x hx y hy h311 h312
