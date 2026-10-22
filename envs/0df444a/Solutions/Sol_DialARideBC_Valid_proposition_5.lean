-- Prove2me | solution 1 for DialARideBC.Valid.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T14:25:11.425782+00:00
-- url     : https://prove2.me/submissions/8cfe98ea-554a-44b4-a3f8-bec3a843cf7c

import Mathlib
import Definitions.Def_DialARideBC_Valid_Model

set_option autoImplicit false

namespace DARP5

open DialARideBC.Valid

lemma arcs_cons_cons (a b : ℕ) (t : List ℕ) :
    arcs (a :: b :: t) = (a, b) :: arcs (b :: t) := rfl

lemma fst_mem_of_mem_arcs {w : List ℕ} {a b : ℕ} (h : (a, b) ∈ arcs w) : a ∈ w :=
  (List.of_mem_zip h).1

lemma arcs_unique : ∀ (w : List ℕ), w.Nodup → ∀ a b c : ℕ,
    (a, b) ∈ arcs w → (a, c) ∈ arcs w → b = c
  | [], _, a, b, c, hb, _ => by simp [arcs] at hb
  | [_], _, a, b, c, hb, _ => by simp [arcs] at hb
  | x :: y :: t, hnd, a, b, c, hb, hc => by
    rw [arcs_cons_cons] at hb hc
    have hx : x ∉ y :: t := (List.nodup_cons.mp hnd).1
    have ih := arcs_unique (y :: t) (List.nodup_cons.mp hnd).2 a b c
    rcases List.mem_cons.mp hb with hb | hb <;> rcases List.mem_cons.mp hc with hc | hc
    · simp only [Prod.mk.injEq] at hb hc
      rw [hb.2, hc.2]
    · simp only [Prod.mk.injEq] at hb
      exact absurd (hb.1 ▸ fst_mem_of_mem_arcs hc) hx
    · simp only [Prod.mk.injEq] at hc
      exact absurd (hc.1 ▸ fst_mem_of_mem_arcs hb) hx
    · exact ih hb hc

lemma arcs_no_loop : ∀ (w : List ℕ), w.Nodup → ∀ a : ℕ, (a, a) ∉ arcs w
  | [], _, a, h => by simp [arcs] at h
  | [_], _, a, h => by simp [arcs] at h
  | x :: y :: t, hnd, a, h => by
    rw [arcs_cons_cons] at h
    rcases List.mem_cons.mp h with h | h
    · simp only [Prod.mk.injEq] at h
      have hx : x ∉ y :: t := (List.nodup_cons.mp hnd).1
      apply hx
      rw [← h.1, h.2]
      exact List.mem_cons_self
    · exact arcs_no_loop (y :: t) (List.nodup_cons.mp hnd).2 a h

/-- In `r ++ [z]` with `z ∉ S`, starting from an element `c ∈ S` of `r`, there is a later
element `a ∈ S` of `r` all of whose outgoing arcs leave `S`. -/
lemma sink_exists (S : Finset ℕ) (z : ℕ) (hz : z ∉ S) : ∀ (r : List ℕ) (c : ℕ),
    (r ++ [z]).Nodup → c ∈ r → c ∈ S →
    ∃ a ∈ r, a ∈ S ∧ r.idxOf c ≤ r.idxOf a ∧ ∀ b, (a, b) ∈ arcs (r ++ [z]) → b ∉ S
  | [], c, _, hc, _ => by simp at hc
  | x :: r', c, hnd, hc, hcS => by
    obtain ⟨y, t, hyt⟩ : ∃ y t, r' ++ [z] = y :: t := by
      cases r' with
      | nil => exact ⟨z, [], rfl⟩
      | cons p q => exact ⟨p, q ++ [z], rfl⟩
    have hnd' : (x :: (r' ++ [z])).Nodup := by simpa using hnd
    have hx : x ∉ r' ++ [z] := (List.nodup_cons.mp hnd').1
    have hnd2 : (r' ++ [z]).Nodup := (List.nodup_cons.mp hnd').2
    have harcs : arcs (x :: r' ++ [z]) = (x, y) :: arcs (r' ++ [z]) := by
      rw [List.cons_append, hyt, arcs_cons_cons]
    by_cases hcase : c = x ∧ y ∉ S
    · refine ⟨x, List.mem_cons_self, hcase.1 ▸ hcS, by rw [hcase.1], ?_⟩
      intro b hb
      rw [harcs] at hb
      rcases List.mem_cons.mp hb with hb | hb
      · simp only [Prod.mk.injEq] at hb
        rw [hb.2]; exact hcase.2
      · exact absurd (fst_mem_of_mem_arcs hb) hx
    · -- pick the next starting point inside `r'`
      have hstart : ∃ c' ∈ r', c' ∈ S ∧ (c ≠ x → c' = c) := by
        by_cases hcx : c = x
        · have hyS : y ∈ S := by
            by_contra hy; exact hcase ⟨hcx, hy⟩
          have hy : y ∈ r' ++ [z] := by rw [hyt]; exact List.mem_cons_self
          have hyz : y ≠ z := fun e => hz (e ▸ hyS)
          rcases List.mem_append.mp hy with hy | hy
          · exact ⟨y, hy, hyS, fun h => absurd hcx h⟩
          · simp at hy; exact absurd hy hyz
        · rcases List.mem_cons.mp hc with hc | hc
          · exact absurd hc hcx
          · exact ⟨c, hc, hcS, fun _ => rfl⟩
      obtain ⟨c', hc'r, hc'S, hc'c⟩ := hstart
      obtain ⟨a, har, haS, hidx, hsink⟩ := sink_exists S z hz r' c' hnd2 hc'r hc'S
      have hax : a ≠ x := fun e => hx (List.mem_append_left _ (e ▸ har))
      refine ⟨a, List.mem_cons_of_mem _ har, haS, ?_, ?_⟩
      · rw [List.idxOf_cons_ne _ (Ne.symm hax)]
        by_cases hcx : c = x
        · rw [hcx, List.idxOf_cons_self]; exact Nat.zero_le _
        · rw [List.idxOf_cons_ne _ (Ne.symm hcx), ← hc'c hcx]
          exact Nat.succ_le_succ hidx
      · intro b hb
        rw [harcs] at hb
        rcases List.mem_cons.mp hb with hb | hb
        · simp only [Prod.mk.injEq] at hb; exact absurd hb.1 hax
        · exact hsink b hb

lemma fullPath_nodup {n : ℕ} (r : List ℕ) (hr : r.Nodup) (hsub : ∀ v ∈ r, v ∈ PD n) :
    (fullPath n r).Nodup := by
  unfold fullPath
  have h0 : (0 : ℕ) ∉ r := fun h => by
    have := hsub 0 h; simp [PD] at this
  have hz : 2 * n + 1 ∉ r := fun h => by
    have := hsub _ h; simp [PD] at this
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨h0, by omega⟩
  · rw [List.nodup_append]
    refine ⟨hr, List.nodup_singleton _, ?_⟩
    intro a ha b hb
    simp at hb; subst hb; exact fun e => hz (e ▸ ha)

lemma not_mem_arcs_other {n : ℕ} (r : List ℕ) (i j : ℕ) (hi : i ∈ PD n) (hir : i ∉ r) :
    (i, j) ∉ arcs (fullPath n r) := by
  intro h
  have := fst_mem_of_mem_arcs h
  unfold fullPath at this
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at this
  simp [PD] at hi
  rcases this with h1 | h1 | h1
  · omega
  · exact hir h1
  · omega

variable {n : ℕ} {K : Type} [Fintype K] {I : Instance n K}

lemma x_eq (s : Solution I) (i : ℕ) (hi : i ∈ PD n) (k0 : K) (hk0 : i ∈ s.route k0) (j : ℕ) :
    s.x i j = s.xk k0 i j := by
  unfold Solution.x
  rw [Finset.sum_eq_single k0]
  · intro k _ hk
    have hik : i ∉ s.route k := by
      intro h
      obtain ⟨k1, _, hk1⟩ := s.served i hi
      exact hk ((hk1 k h).trans (hk1 k0 hk0).symm)
    simp [Solution.xk, not_mem_arcs_other _ i j hi hik]
  · intro h; exact absurd (Finset.mem_univ k0) h

lemma x_nonneg (s : Solution I) (i j : ℕ) : 0 ≤ s.x i j := by
  unfold Solution.x
  apply Finset.sum_nonneg
  intro k _
  unfold Solution.xk
  split_ifs <;> norm_num

lemma out_le_one (s : Solution I) (S : Finset ℕ) (i : ℕ) (hi : i ∈ PD n) :
    ∑ j ∈ S, s.x i j ≤ 1 := by
  obtain ⟨k0, hk0, _⟩ := s.served i hi
  have hnd := fullPath_nodup (n := n) (s.route k0) (s.nodup k0) (s.sub k0)
  rw [Finset.sum_congr rfl (fun j _ => x_eq s i hi k0 hk0 j)]
  unfold Solution.xk
  rw [Finset.sum_boole]
  have : (S.filter (fun j => (i, j) ∈ arcs (fullPath n (s.route k0)))).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact arcs_unique _ hnd i a b ha.2 hb.2
  exact_mod_cast this

lemma x_self (s : Solution I) (i : ℕ) (hi : i ∈ PD n) : s.x i i = 0 := by
  obtain ⟨k0, hk0, _⟩ := s.served i hi
  have hnd := fullPath_nodup (n := n) (s.route k0) (s.nodup k0) (s.sub k0)
  rw [x_eq s i hi k0 hk0]
  simp [Solution.xk, arcs_no_loop _ hnd i]

lemma sink_T (s : Solution I) (u : ℕ) (hu : u ∈ P n) (T : Finset ℕ) (hT : T ⊆ PD n)
    (hn : n + u ∈ T) : ∃ w ∈ T, w ≠ u ∧ ∑ j ∈ T, s.x w j = 0 := by
  have huPD : u ∈ PD n := by simp [P, PD] at hu ⊢; omega
  obtain ⟨k0, hk0, _⟩ := s.served u huPD
  have hk0' : n + u ∈ s.route k0 := (s.pairing u hu k0).mp hk0
  have hprec := s.precedence u hu k0 hk0
  have hz : 2 * n + 1 ∉ T := fun h => by have := hT h; simp [PD] at this
  have hnd := fullPath_nodup (n := n) (s.route k0) (s.nodup k0) (s.sub k0)
  have hnd2 : (s.route k0 ++ [2 * n + 1]).Nodup := by
    unfold fullPath at hnd; exact (List.nodup_cons.mp hnd).2
  obtain ⟨a, har, haT, hidx, hsink⟩ :=
    sink_exists T (2 * n + 1) hz (s.route k0) (n + u) hnd2 hk0' hn
  have hau : a ≠ u := by
    intro e; rw [e] at hidx; omega
  have haPD : a ∈ PD n := hT haT
  refine ⟨a, haT, hau, ?_⟩
  apply Finset.sum_eq_zero
  intro j hj
  rw [x_eq s a haPD k0 har]
  unfold Solution.xk
  rw [if_neg]
  intro hmem
  unfold fullPath at hmem
  obtain ⟨y, t, hyt⟩ : ∃ y t, s.route k0 ++ [2 * n + 1] = y :: t := by
    cases s.route k0 with
    | nil => exact ⟨_, [], rfl⟩
    | cons p q => exact ⟨p, q ++ [2 * n + 1], rfl⟩
  rw [hyt, arcs_cons_cons, ← hyt] at hmem
  rcases List.mem_cons.mp hmem with h | h
  · simp only [Prod.mk.injEq] at h
    have := hT haT; rw [h.1] at this; simp [PD] at this
  · exact hsink j h hj

lemma sum_le_of_sub (S Z : Finset ℕ) (hZ : Z ⊆ S) (f : ℕ → ℝ) (hf : ∀ i ∈ S, f i ≤ 1) :
    ∑ i ∈ S, f i ≤ ∑ i ∈ Z, f i + ((S.card : ℝ) - Z.card) := by
  rw [← Finset.sum_sdiff hZ]
  have h1 : ∑ i ∈ S \ Z, f i ≤ ∑ i ∈ S \ Z, (1 : ℝ) :=
    Finset.sum_le_sum (fun i hi => hf i (Finset.mem_sdiff.mp hi).1)
  have h2 := Finset.card_sdiff_add_card_eq_card hZ
  have h3 : ((S \ Z).card : ℝ) + Z.card = S.card := by exact_mod_cast h2
  simp at h1
  linarith

end DARP5

open DialARideBC.Valid in
theorem solution {n : ℕ} {K : Type} [Fintype K] (I : Instance n K) (s : Solution I)
    (m : ℕ) (u : Fin m → ℕ) (hu : Function.Injective u) (huP : ∀ h, u h ∈ P n)
    (H : Finset ℕ) (hH : H ⊆ PD n) (T : Fin m → Finset ℕ) (hT : ∀ h, T h ⊆ PD n)
    (hiT : ∀ h, u h ∈ T h ∧ n + u h ∈ T h) (hHT : ∀ h, H ∩ T h = {u h}) :
    xset s.x H + ∑ h, xset s.x (T h) ≤ (H.card : ℝ) + ∑ h, ((T h).card : ℝ) - 2 * m := by
  have huH : ∀ h, u h ∈ H := fun h => by
    have : u h ∈ H ∩ T h := by rw [hHT h]; exact Finset.mem_singleton_self _
    exact (Finset.mem_inter.mp this).1
  have huPD : ∀ h, u h ∈ PD n := fun h => hH (huH h)
  -- per-set bound for each T h
  have hTb : ∀ h, xset s.x (T h) ≤ ∑ j ∈ T h, s.x (u h) j + (((T h).card : ℝ) - 2) := by
    intro h
    obtain ⟨w, hwT, hwu, hw0⟩ := DARP5.sink_T s (u h) (huP h) (T h) (hT h) (hiT h).2
    have hZ : ({u h, w} : Finset ℕ) ⊆ T h := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv | hv
      · rw [hv]; exact (hiT h).1
      · rw [hv]; exact hwT
    have := DARP5.sum_le_of_sub (T h) {u h, w} hZ (fun i => ∑ j ∈ T h, s.x i j)
      (fun i hi => DARP5.out_le_one s (T h) i (hT h hi))
    rw [Finset.sum_pair (Ne.symm hwu), Finset.card_pair (Ne.symm hwu)] at this
    unfold xset
    try dsimp only at this
    rw [hw0] at this
    push_cast at this
    linarith
  -- bound for H
  have hHb : xset s.x H ≤ ∑ h, ∑ j ∈ H, s.x (u h) j + ((H.card : ℝ) - m) := by
    have hZ : (Finset.univ.image u) ⊆ H := by
      intro v hv
      obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hv
      exact huH h
    have := DARP5.sum_le_of_sub H (Finset.univ.image u) hZ (fun i => ∑ j ∈ H, s.x i j)
      (fun i hi => DARP5.out_le_one s H i (hH hi))
    rw [Finset.sum_image (fun a _ b _ e => hu e),
      Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin] at this
    unfold xset
    exact this
  -- the out-flow of `u h` into `H` and into `T h` is at most one in total
  have hpair : ∀ h, ∑ j ∈ H, s.x (u h) j + ∑ j ∈ T h, s.x (u h) j ≤ 1 := by
    intro h
    rw [← Finset.sum_union_inter, hHT h, Finset.sum_singleton,
      DARP5.x_self s (u h) (huPD h), add_zero]
    exact DARP5.out_le_one s _ _ (huPD h)
  have hsumT : ∑ h, xset s.x (T h) ≤
      ∑ h, (∑ j ∈ T h, s.x (u h) j + (((T h).card : ℝ) - 2)) :=
    Finset.sum_le_sum (fun h _ => hTb h)
  have hsumP : ∑ h, (∑ j ∈ H, s.x (u h) j + ∑ j ∈ T h, s.x (u h) j) ≤ ∑ _h : Fin m, (1 : ℝ) :=
    Finset.sum_le_sum (fun h _ => hpair h)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsumT hsumP
  linarith
