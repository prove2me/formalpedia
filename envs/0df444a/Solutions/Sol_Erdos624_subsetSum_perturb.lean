-- Prove2me | solution 1 for Erdos624.subsetSum_perturb
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:41:10.608159+00:00
-- url     : https://prove2.me/submissions/895857a4-e064-4436-a532-16f47e5bb5d9

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset


namespace E624R5
open Finset

variable {U : Type*} [DecidableEq U]

lemma sum_symmDiff {G : Type*} [AddCommGroup G] (h2 : ∀ x : G, x + x = 0)
    (v : U → G) (A D : Finset U) :
    ∑ a ∈ symmDiff A D, v a = ∑ a ∈ A, v a + ∑ a ∈ D, v a := by
  have hA : ∑ a ∈ A \ D, v a + ∑ a ∈ A ∩ D, v a = ∑ a ∈ A, v a := by
    rw [← sum_sdiff (inter_subset_left : A ∩ D ⊆ A), sdiff_inter_self_left]
  have hD : ∑ a ∈ D \ A, v a + ∑ a ∈ D ∩ A, v a = ∑ a ∈ D, v a := by
    rw [← sum_sdiff (inter_subset_left : D ∩ A ⊆ D), sdiff_inter_self_left]
  have hs : ∑ a ∈ symmDiff A D, v a = ∑ a ∈ A \ D, v a + ∑ a ∈ D \ A, v a := by
    rw [symmDiff_def, sup_eq_union, sum_union disjoint_sdiff_sdiff]
  rw [hs, ← hA, ← hD, inter_comm D A]
  have := h2 (∑ a ∈ A ∩ D, v a)
  calc _ = ∑ a ∈ A \ D, v a + ∑ a ∈ D \ A, v a + 0 := by rw [add_zero]
    _ = _ := by rw [← this]; abel

/-- Pivot reduction: flipping by sets `D_x` with `D_x ∩ X = {x}` that leave `φ` invariant. -/
lemma pivot_reduce {β : Type*} (φ : Finset U → β) (Y X : Finset U)
    (hD : ∀ x ∈ X, ∃ D ⊆ Y, D ∩ X = {x} ∧ ∀ A, φ (symmDiff A D) = φ A) :
    ∀ A ⊆ Y, ∃ A' ⊆ Y \ X, φ A' = φ A := by
  suffices h : ∀ m, ∀ A ⊆ Y, #(A ∩ X) = m → ∃ A' ⊆ Y \ X, φ A' = φ A from
    fun A hA => h _ A hA rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro A hA hm
    by_cases he : A ∩ X = ∅
    · refine ⟨A, ?_, rfl⟩
      intro y hy
      rw [mem_sdiff]
      refine ⟨hA hy, fun hyX => ?_⟩
      have : y ∈ A ∩ X := mem_inter.2 ⟨hy, hyX⟩
      rw [he] at this; simp at this
    · obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 he
      rw [mem_inter] at hx
      obtain ⟨D, hDY, hDX, hφ⟩ := hD x hx.2
      have hxD : x ∈ D := by
        have : x ∈ D ∩ X := by rw [hDX]; exact mem_singleton_self x
        exact (mem_inter.1 this).1
      have hnew : symmDiff A D ∩ X = (A ∩ X).erase x := by
        ext y
        simp only [mem_inter, mem_erase, mem_symmDiff]
        by_cases hyX : y ∈ X
        · by_cases hyx : y = x
          · subst hyx; simp [hxD, hx.1]
          · have hyD : y ∉ D := by
              intro hyD
              have : y ∈ D ∩ X := mem_inter.2 ⟨hyD, hyX⟩
              rw [hDX, mem_singleton] at this; exact hyx this
            simp [hyD, hyx, hyX]
        · simp [hyX]
      have hlt : #(symmDiff A D ∩ X) < m := by
        rw [hnew, ← hm]
        exact card_erase_lt_of_mem (mem_inter.2 hx)
      have hsub : symmDiff A D ⊆ Y := by
        intro y hy
        rw [mem_symmDiff] at hy
        rcases hy with ⟨h, _⟩ | ⟨h, _⟩
        · exact hA h
        · exact hDY h
      obtain ⟨A', hA', hφ'⟩ := ih _ hlt (symmDiff A D) hsub rfl
      exact ⟨A', hA', by rw [hφ', hφ]⟩

lemma image_card_pivot {β : Type*} [DecidableEq β] (φ : Finset U → β) (Y X : Finset U)
    (hXY : X ⊆ Y)
    (hD : ∀ x ∈ X, ∃ D ⊆ Y, D ∩ X = {x} ∧ ∀ A, φ (symmDiff A D) = φ A) :
    2 ^ #X * #(Y.powerset.image φ) ≤ 2 ^ #Y := by
  have hsub : Y.powerset.image φ ⊆ (Y \ X).powerset.image φ := by
    intro b hb
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hb
    obtain ⟨A', hA', he⟩ := pivot_reduce φ Y X hD A (mem_powerset.1 hA)
    exact mem_image.2 ⟨A', mem_powerset.2 hA', he⟩
  have h1 : #(Y.powerset.image φ) ≤ 2 ^ (#Y - #X) := by
    calc _ ≤ #((Y \ X).powerset.image φ) := card_le_card hsub
      _ ≤ #(Y \ X).powerset := card_image_le
      _ = 2 ^ (#Y - #X) := by rw [card_powerset, card_sdiff_of_subset hXY]
  have hle : #X ≤ #Y := card_le_card hXY
  calc 2 ^ #X * #(Y.powerset.image φ) ≤ 2 ^ #X * 2 ^ (#Y - #X) := Nat.mul_le_mul_left _ h1
    _ = 2 ^ #Y := by rw [← pow_add]; congr 1; omega


variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- One zero-sum set of size `≤ 2t` inside `R` (pigeonhole on `t`-subsets). -/
lemma one_zero_sum (h2 : ∀ x : G, x + x = 0) (v : U → G) (t : ℕ) (R : Finset U)
    (hc : Fintype.card G < (#R).choose t) :
    ∃ D ⊆ R, D.Nonempty ∧ #D ≤ 2 * t ∧ ∑ a ∈ D, v a = 0 := by
  have hc' : (univ : Finset G).card < (powersetCard t R).card := by
    rw [card_univ, card_powersetCard]; exact hc
  obtain ⟨A, hA, B, hB, hAB, he⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hc'
    (f := fun A => ∑ a ∈ A, v a) (fun _ _ => mem_univ _)
  rw [mem_powersetCard] at hA hB
  refine ⟨symmDiff A B, ?_, ?_, ?_, ?_⟩
  · intro x hx; rw [mem_symmDiff] at hx
    rcases hx with ⟨h, _⟩ | ⟨h, _⟩
    · exact hA.1 h
    · exact hB.1 h
  · rw [nonempty_iff_ne_empty]; intro h
    exact hAB (symmDiff_eq_bot.1 h)
  · calc #(symmDiff A B) ≤ #(A ∪ B) := card_le_card (by
          intro x hx; rw [mem_symmDiff] at hx; rw [mem_union]; tauto)
      _ ≤ #A + #B := card_union_le _ _
      _ = 2 * t := by rw [hA.2, hB.2]; ring
  · rw [sum_symmDiff h2, ← he]; exact h2 _

/-- `d` pivots with zero-sum flip sets, all inside a set of size `≤ 2td`. -/
lemma pivots (h2 : ∀ x : G, x + x = 0) (v : U → G) (t : ℕ) :
    ∀ d : ℕ, ∀ R : Finset U, (d = 0 ∨ Fintype.card G < (#R - 2 * t * (d - 1)).choose t) →
      ∃ Z X : Finset U, Z ⊆ R ∧ #Z ≤ 2 * t * d ∧ X ⊆ Z ∧ #X = d ∧
        ∀ x ∈ X, ∃ D ⊆ Z, D ∩ X = {x} ∧ ∑ a ∈ D, v a = 0 := by
  intro d
  induction d with
  | zero =>
    intro R _
    exact ⟨∅, ∅, empty_subset _, by simp, empty_subset _, by simp, by simp⟩
  | succ e ih =>
    intro R hR
    have hc : Fintype.card G < (#R - 2 * t * e).choose t := by
      rcases hR with h | h
      · omega
      · simpa using h
    have hc2 : Fintype.card G < (#R).choose t :=
      lt_of_lt_of_le hc (Nat.choose_le_choose _ (Nat.sub_le _ _))
    obtain ⟨D, hDR, hDne, hDc, hDs⟩ := one_zero_sum h2 v t R hc2
    obtain ⟨x, hxD⟩ := hDne
    have hR' : e = 0 ∨ Fintype.card G < (#(R \ D) - 2 * t * (e - 1)).choose t := by
      rcases Nat.eq_zero_or_pos e with he | he
      · exact Or.inl he
      · right
        obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
        refine lt_of_lt_of_le hc (Nat.choose_le_choose _ ?_)
        rw [card_sdiff_of_subset hDR]
        have : 2 * t * (f + 1) = 2 * t * f + 2 * t := by ring
        simp only [Nat.add_sub_cancel]
        omega
    obtain ⟨Z, X, hZR, hZc, hXZ, hXc, hX⟩ := ih (R \ D) hR'
    have hxX : x ∉ X := by
      intro hx; have := hZR (hXZ hx); rw [mem_sdiff] at this; exact this.2 hxD
    have hDX : D ∩ X = ∅ := by
      ext y; simp only [mem_inter, notMem_empty, iff_false, not_and]
      intro hyD hyX; have := hZR (hXZ hyX); rw [mem_sdiff] at this; exact this.2 hyD
    refine ⟨Z ∪ D, insert x X, union_subset (hZR.trans sdiff_subset) hDR, ?_, ?_, ?_, ?_⟩
    · calc #(Z ∪ D) ≤ #Z + #D := card_union_le _ _
        _ ≤ 2 * t * e + 2 * t := by omega
        _ = 2 * t * (e + 1) := by ring
    · exact insert_subset (mem_union_right _ hxD) (hXZ.trans subset_union_left)
    · rw [card_insert_of_notMem hxX, hXc]
    · intro y hy
      rw [mem_insert] at hy
      rcases hy with rfl | hy
      · refine ⟨D, subset_union_right, ?_, hDs⟩
        rw [inter_insert_of_mem hxD, hDX]; rfl
      · obtain ⟨D', hD'Z, hD'X, hD's⟩ := hX y hy
        refine ⟨D', hD'Z.trans subset_union_left, ?_, hD's⟩
        have hxD' : x ∉ D' := by
          intro h; have := hZR (hD'Z h); rw [mem_sdiff] at this; exact this.2 hxD
        rw [inter_insert_of_notMem hxD', hD'X]


end E624R5

namespace E624R5
open Finset

abbrev Vk (k : ℕ) := Fin k → ZMod 2

lemma vk_add_self {k r : ℕ} (x : Fin r → Vk k) : x + x = 0 := by
  funext i j
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i j = z
  fin_cases z <;> rfl

lemma zmod_add_self {k : ℕ} (x : Vk k) : x + x = 0 := by
  funext j
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x j = z
  fin_cases z <;> rfl

lemma card_G (k r : ℕ) : Fintype.card (Fin r → Vk k) = (2 ^ k) ^ r := by
  simp [ZMod.card]

/-- Finite structured common-hole theorem (13)–(15). -/
theorem subsetSum_finite (k r d t : ℕ) (hk : 2 * t * d ≤ k)
    (hc : (2 ^ k) ^ r < (2 ^ k - 2 * t * (d - 1)).choose t)
    (v : Fin r → Fin (2 ^ k) → Vk k) (ψ : Fin r → Vk k → Fin (2 ^ k)) :
    ∃ Y : Finset (Fin (2 ^ k)), #Y = k ∧
      (∀ i, 2 ^ d * #(Y.powerset.image (fun A => ψ i (∑ a ∈ A, v i a))) ≤ 2 ^ k) ∧
      2 ^ d * #(((univ : Finset (Fin r)) ×ˢ Y.powerset).image
        (fun p => ψ p.1 (∑ a ∈ p.2, v p.1 a))) ≤ r * 2 ^ k := by
  let w : Fin (2 ^ k) → (Fin r → Vk k) := fun a i => v i a
  have hcG : Fintype.card (Fin r → Vk k) < (#(univ : Finset (Fin (2 ^ k))) - 2 * t * (d - 1)).choose t := by
    rw [card_G, card_univ, Fintype.card_fin]; exact hc
  obtain ⟨Z, X, -, hZc, hXZ, hXc, hX⟩ := pivots vk_add_self w t d univ (Or.inr hcG)
  have hk2 : k ≤ Fintype.card (Fin (2 ^ k)) := by
    rw [Fintype.card_fin]; exact (Nat.lt_two_pow_self).le
  obtain ⟨Y, hZY, hYc⟩ := exists_superset_card_eq (hZc.trans hk) hk2
  have htrack : ∀ i, 2 ^ d * #(Y.powerset.image (fun A => ψ i (∑ a ∈ A, v i a))) ≤ 2 ^ k := by
    intro i
    have := image_card_pivot (fun A => ψ i (∑ a ∈ A, v i a)) Y X (hXZ.trans hZY) (by
      intro x hx
      obtain ⟨D, hDZ, hDX, hDs⟩ := hX x hx
      refine ⟨D, hDZ.trans hZY, hDX, fun A => ?_⟩
      have hDi : ∑ a ∈ D, v i a = 0 := by
        have := congrFun hDs i
        simpa [w, Finset.sum_apply] using this
      show ψ i (∑ a ∈ symmDiff A D, v i a) = ψ i (∑ a ∈ A, v i a)
      rw [sum_symmDiff zmod_add_self, hDi, add_zero])
    rw [hXc, hYc] at this; exact this
  refine ⟨Y, hYc, htrack, ?_⟩
  have hsub : ((univ : Finset (Fin r)) ×ˢ Y.powerset).image (fun p => ψ p.1 (∑ a ∈ p.2, v p.1 a)) ⊆
      (univ : Finset (Fin r)).biUnion (fun i => Y.powerset.image (fun A => ψ i (∑ a ∈ A, v i a))) := by
    intro b hb
    obtain ⟨⟨i, A⟩, hp, rfl⟩ := mem_image.1 hb
    rw [mem_product] at hp
    exact mem_biUnion.2 ⟨i, mem_univ _, mem_image.2 ⟨A, hp.2, rfl⟩⟩
  calc 2 ^ d * #(((univ : Finset (Fin r)) ×ˢ Y.powerset).image _)
      ≤ 2 ^ d * ∑ i, #(Y.powerset.image (fun A => ψ i (∑ a ∈ A, v i a))) :=
        Nat.mul_le_mul_left _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ i, 2 ^ d * #(Y.powerset.image (fun A => ψ i (∑ a ∈ A, v i a))) := by rw [mul_sum]
    _ ≤ ∑ _i : Fin r, 2 ^ k := sum_le_sum (fun i _ => htrack i)
    _ = r * 2 ^ k := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- Common hole under the finite conditions, when `r < 2^d`. -/
theorem subsetSum_hole_finite (k r d t : ℕ) (hk : 2 * t * d ≤ k)
    (hc : (2 ^ k) ^ r < (2 ^ k - 2 * t * (d - 1)).choose t) (hrd : r < 2 ^ d)
    (v : Fin r → Fin (2 ^ k) → Vk k) (ψ : Fin r → Vk k → Fin (2 ^ k)) :
    ∃ Y : Finset (Fin (2 ^ k)), #Y = k ∧ ∃ u, ∀ i, ∀ A ⊆ Y, ψ i (∑ a ∈ A, v i a) ≠ u := by
  obtain ⟨Y, hY, -, hU⟩ := subsetSum_finite k r d t hk hc v ψ
  refine ⟨Y, hY, ?_⟩
  set S := ((univ : Finset (Fin r)) ×ˢ Y.powerset).image (fun p => ψ p.1 (∑ a ∈ p.2, v p.1 a))
  have hlt : #S < 2 ^ k := by
    have h1 : r * 2 ^ k < 2 ^ d * 2 ^ k := Nat.mul_lt_mul_of_pos_right hrd (by positivity)
    have h2 : 2 ^ d * #S < 2 ^ d * 2 ^ k := lt_of_le_of_lt hU (by linarith)
    exact Nat.lt_of_mul_lt_mul_left h2
  obtain ⟨u, hu⟩ : ∃ u, u ∉ S := by
    by_contra hc'; push Not at hc'
    have : S = univ := eq_univ_of_forall hc'
    rw [this, card_univ, Fintype.card_fin] at hlt; omega
  refine ⟨u, fun i A hA he => hu (mem_image.2 ⟨(i, A), mem_product.2 ⟨mem_univ _, mem_powerset.2 hA⟩, he⟩)⟩

/-- `N^t ≤ t^t · C(N,t)` for `t ≤ N`. -/
lemma pow_le_choose_mul (t : ℕ) : ∀ N, t ≤ N → N ^ t ≤ t ^ t * N.choose t := by
  induction t with
  | zero => intro N _; simp
  | succ s ih =>
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hsM : s ≤ M := by omega
    have hrec : (M + 1) * M.choose s = (M + 1).choose (s + 1) * (s + 1) := Nat.add_one_mul_choose_eq M s
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs; simp
    have ih' := ih M hsM
    -- (M+1)^s * s^s ≤ (s+1)^s * M^s
    have hb : ((M + 1) * s) ^ s ≤ ((s + 1) * M) ^ s := Nat.pow_le_pow_left (by nlinarith) s
    rw [mul_pow, mul_pow] at hb
    have key : s ^ s * (M + 1) ^ s ≤ s ^ s * ((s + 1) ^ s * M.choose s) := by
      calc s ^ s * (M + 1) ^ s = (M + 1) ^ s * s ^ s := by ring
        _ ≤ (s + 1) ^ s * M ^ s := hb
        _ ≤ (s + 1) ^ s * (s ^ s * M.choose s) := Nat.mul_le_mul_left _ ih'
        _ = s ^ s * ((s + 1) ^ s * M.choose s) := by ring
    have key2 : (M + 1) ^ s ≤ (s + 1) ^ s * M.choose s :=
      Nat.le_of_mul_le_mul_left key (by positivity)
    calc (M + 1) ^ (s + 1) = (M + 1) ^ s * (M + 1) := pow_succ _ _
      _ ≤ (s + 1) ^ s * M.choose s * (M + 1) := Nat.mul_le_mul_right _ key2
      _ = (s + 1) ^ s * ((M + 1) * M.choose s) := by ring
      _ = (s + 1) ^ s * ((M + 1).choose (s + 1) * (s + 1)) := by rw [hrec]
      _ = (s + 1) ^ (s + 1) * (M + 1).choose (s + 1) := by ring

/-- Fixed-`r` common-hole theorem for subset-sum-factor maps over `𝔽₂^k`. -/
theorem subsetSum_common_hole (r : ℕ) : ∃ k0, ∀ k ≥ k0,
    ∀ (v : Fin r → Fin (2 ^ k) → Vk k) (ψ : Fin r → Vk k → Fin (2 ^ k)),
      ∃ Y : Finset (Fin (2 ^ k)), #Y = k ∧ ∃ u, ∀ i, ∀ A ⊆ Y, ψ i (∑ a ∈ A, v i a) ≠ u := by
  set t := r + 1 with ht
  set K := t ^ t * 2 ^ r + 2 * t * r + 1 with hK
  refine ⟨K + 1, fun k hk v ψ => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set m := 2 ^ j with hm
  have hjm : j < m := Nat.lt_two_pow_self
  have hn : 2 ^ (j + 1) = 2 * m := by rw [pow_succ]; ring
  have htt : 1 ≤ t ^ t := Nat.one_le_pow _ _ (by omega)
  have hm1 : t ^ t * 2 ^ r < m := by omega
  have hm2 : 2 * t * (r - 1) ≤ m := by
    have : 2 * t * (r - 1) ≤ 2 * t * r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  set N := 2 ^ (j + 1) - 2 * t * (r - 1) with hN
  have hNm : m ≤ N := by omega
  have htN : t ≤ N := by
    have h1 : t ≤ t ^ t := Nat.le_self_pow (by omega) t
    have h2 : t ^ t ≤ t ^ t * 2 ^ r := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos r)
    omega
  have hc : (2 ^ (j + 1)) ^ r < N.choose t := by
    have h1 : t ^ t * (2 ^ (j + 1)) ^ r < N ^ t := by
      rw [hn, mul_pow]
      calc t ^ t * (2 ^ r * m ^ r) = (t ^ t * 2 ^ r) * m ^ r := by ring
        _ < m * m ^ r := Nat.mul_lt_mul_of_pos_right hm1 (pow_pos (by omega : 0 < m) r)
        _ = m ^ t := by rw [ht, pow_succ]; ring
        _ ≤ N ^ t := Nat.pow_le_pow_left hNm t
    have h2 := pow_le_choose_mul t N htN
    exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le h1 h2)
  exact subsetSum_hole_finite (j + 1) r r t (by omega) hc Nat.lt_two_pow_self v ψ


/-- Perturbation version (17): the structured witness `Y` controls every nearby family `g`. -/
theorem subsetSum_perturb (k r d t : ℕ) (hk : 2 * t * d ≤ k)
    (hc : (2 ^ k) ^ r < (2 ^ k - 2 * t * (d - 1)).choose t)
    (v : Fin r → Fin (2 ^ k) → Vk k) (ψ : Fin r → Vk k → Fin (2 ^ k)) :
    ∃ Y : Finset (Fin (2 ^ k)), #Y = k ∧
      ∀ g : Fin r → Finset (Fin (2 ^ k)) → Fin (2 ^ k),
        2 ^ d * #(((univ : Finset (Fin r)) ×ˢ Y.powerset).image (fun p => g p.1 p.2)) ≤
          r * 2 ^ k + 2 ^ d * ∑ i, #(Y.powerset.filter
            (fun A => g i A ≠ ψ i (∑ a ∈ A, v i a))) := by
  obtain ⟨Y, hY, -, hU⟩ := subsetSum_finite k r d t hk hc v ψ
  refine ⟨Y, hY, fun g => ?_⟩
  set Ih := ((univ : Finset (Fin r)) ×ˢ Y.powerset).image (fun p => ψ p.1 (∑ a ∈ p.2, v p.1 a))
  have hsub : ((univ : Finset (Fin r)) ×ˢ Y.powerset).image (fun p => g p.1 p.2) ⊆
      Ih ∪ (univ : Finset (Fin r)).biUnion (fun i => (Y.powerset.filter
        (fun A => g i A ≠ ψ i (∑ a ∈ A, v i a))).image (g i)) := by
    intro b hb
    obtain ⟨⟨i, A⟩, hp, rfl⟩ := mem_image.1 hb
    by_cases he : g i A = ψ i (∑ a ∈ A, v i a)
    · exact mem_union_left _ (mem_image.2 ⟨(i, A), hp, he.symm⟩)
    · rw [mem_product] at hp
      exact mem_union_right _ (mem_biUnion.2 ⟨i, mem_univ _,
        mem_image.2 ⟨A, mem_filter.2 ⟨hp.2, he⟩, rfl⟩⟩)
  have h1 := card_le_card hsub
  have h2 := card_union_le Ih ((univ : Finset (Fin r)).biUnion (fun i => (Y.powerset.filter
        (fun A => g i A ≠ ψ i (∑ a ∈ A, v i a))).image (g i)))
  have h3 : #((univ : Finset (Fin r)).biUnion (fun i => (Y.powerset.filter
        (fun A => g i A ≠ ψ i (∑ a ∈ A, v i a))).image (g i))) ≤
      ∑ i, #(Y.powerset.filter (fun A => g i A ≠ ψ i (∑ a ∈ A, v i a))) :=
    card_biUnion_le.trans (sum_le_sum (fun i _ => card_image_le))
  have := Nat.mul_le_mul_left (2 ^ d) (h1.trans (h2.trans (Nat.add_le_add_left h3 _)))
  rw [mul_add] at this
  omega

end E624R5


namespace Erdos624

theorem subsetSum_perturb (k r d t : ℕ) (hk : 2 * t * d ≤ k)
    (hc : (2 ^ k) ^ r < (2 ^ k - 2 * t * (d - 1)).choose t)
    (v : Fin r → Fin (2 ^ k) → (Fin k → ZMod 2)) (ψ : Fin r → (Fin k → ZMod 2) → Fin (2 ^ k)) :
    ∃ Y : Finset (Fin (2 ^ k)), #Y = k ∧
      ∀ g : Fin r → Finset (Fin (2 ^ k)) → Fin (2 ^ k),
        2 ^ d * #(((univ : Finset (Fin r)) ×ˢ Y.powerset).image (fun p => g p.1 p.2)) ≤
          r * 2 ^ k + 2 ^ d * ∑ i, #(Y.powerset.filter
            (fun A => g i A ≠ ψ i (∑ a ∈ A, v i a))) :=
  E624R5.subsetSum_perturb k r d t hk hc v ψ

end Erdos624

open Erdos624 in
theorem solution (k r d t : ℕ) (hk : 2 * t * d ≤ k)
    (hc : (2 ^ k) ^ r < (2 ^ k - 2 * t * (d - 1)).choose t)
    (v : Fin r → Fin (2 ^ k) → (Fin k → ZMod 2)) (ψ : Fin r → (Fin k → ZMod 2) → Fin (2 ^ k)) :
    ∃ Y : Finset (Fin (2 ^ k)), #Y = k ∧
      ∀ g : Fin r → Finset (Fin (2 ^ k)) → Fin (2 ^ k),
        2 ^ d * #(((univ : Finset (Fin r)) ×ˢ Y.powerset).image (fun p => g p.1 p.2)) ≤
          r * 2 ^ k + 2 ^ d * ∑ i, #(Y.powerset.filter
            (fun A => g i A ≠ ψ i (∑ a ∈ A, v i a))) :=
  Erdos624.subsetSum_perturb k r d t hk hc v ψ

#print axioms solution
