-- Prove2me | solution 1 for Chowla.cauchy_davenport
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:55:55.021681+00:00
-- url     : https://prove2.me/submissions/b7fd6729-0ab3-4efb-abd5-8b502e724591

import Mathlib.Combinatorics.Additive.ETransform
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

/-!
# Chowla's theorem via the Dyson e-transform

If `A, B ⊆ ℤ/m` are nonempty with `|A| + |B| ≤ m` and every nonzero difference of two
elements of `B` is a unit, then `|A + B| ≥ |A| + |B| - 1`.
-/

namespace Chowla

open Finset

open scoped Pointwise

theorem card_add_singleton {m : ℕ} (A : Finset (ZMod m)) (b : ZMod m) :
    (A + {b}).card = A.card := by
  have h : (A + {b}) = A.image (fun a => a + b) := by
    ext x
    rw [mem_add, mem_image]
    constructor
    · rintro ⟨a, ha, b', hb', rfl⟩
      rw [mem_singleton] at hb'
      exact ⟨a, ha, by rw [hb']⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, b, mem_singleton_self _, by simp⟩
  rw [h]
  exact card_image_of_injective _ (fun x y h => add_right_cancel h)

theorem closure_iterate {m : ℕ} {A B : Finset (ZMod m)} (hAB : A + B ⊆ A) {a₀ : ZMod m}
    (ha₀ : a₀ ∈ A) {b₁ b₂ : ZMod m} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) :
    ∀ n k : ℕ, k ≤ n → a₀ + k • b₁ + (n - k) • b₂ ∈ A := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using ha₀
  | succ n IH =>
    intro k hk
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · have h1 : a₀ + k • b₁ + (n - k) • b₂ ∈ A := IH k (by omega)
      have h2 : a₀ + k • b₁ + (n + 1 - k) • b₂
          = (a₀ + k • b₁ + (n - k) • b₂) + b₂ := by
        have hke : n + 1 - k = (n - k) + 1 := by omega
        rw [hke, add_nsmul, one_nsmul]
        ac_rfl
      rw [h2]
      exact hAB (mem_add.2 ⟨_, h1, b₂, hb₂, rfl⟩)
    · have hk1 : k = n + 1 := by omega
      subst hk1
      have h1 : a₀ + n • b₁ + (n + 1 - (n + 1)) • b₂ ∈ A := by
        have hnn : n + 1 - (n + 1) = n - n := by omega
        rw [hnn]
        exact IH n (by omega)
      have h2 : a₀ + (n + 1) • b₁ + (n + 1 - (n + 1)) • b₂
          = (a₀ + n • b₁ + (n + 1 - (n + 1)) • b₂) + b₁ := by
        rw [show (n + 1) • b₁ = n • b₁ + b₁ by rw [add_nsmul, one_nsmul]]
        ac_rfl
      rw [h2]
      exact hAB (mem_add.2 ⟨_, h1, b₁, hb₁, rfl⟩)

/-- Main induction, under the WLOG normalization `(0 : ZMod m) ∈ B`. -/
theorem chowla_aux : ∀ (Bcard : ℕ) {m : ℕ} (_ : 0 < m) (A B : Finset (ZMod m)),
    A.Nonempty → B.Nonempty → (0 : ZMod m) ∈ B → A.card + B.card ≤ m →
    (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → IsUnit (b - b')) →
    B.card ≤ Bcard → A.card + B.card - 1 ≤ (A + B).card := by
  intro Bcard
  induction Bcard with
  | zero =>
    intro m hm A B hA hB hB0 _ _ hBcard
    have := Finset.card_ne_zero.2 hB
    omega
  | succ n IH =>
    intro m hm A B hA hB hB0 hcard hunit hBcard
    have hBne0 : B.card ≠ 0 := Finset.card_ne_zero.2 hB
    rcases Nat.lt_or_ge B.card 2 with hB2 | hB2
    · have h1 : B.card = 1 := by omega
      obtain ⟨b, hb⟩ := Finset.card_eq_one.1 h1
      have hb0 : b = 0 := by
        rw [hb] at hB0
        have h01 : (0 : ZMod m) = b := by simpa using hB0
        exact h01.symm
      rw [hb, hb0, card_add_singleton, Finset.card_singleton]
      omega
    · by_cases hex : ∃ e ∈ A, ¬ ((e : ZMod m) +ᵥ B) ⊆ A
      · obtain ⟨e, heA, he⟩ := hex
        have hsub : (Finset.addDysonETransform e (A, B)).1
            + (Finset.addDysonETransform e (A, B)).2 ⊆ A + B :=
          Finset.addDysonETransform.subset e (A, B)
        have hcardp : (Finset.addDysonETransform e (A, B)).1.card
            + (Finset.addDysonETransform e (A, B)).2.card = A.card + B.card :=
          Finset.addDysonETransform.card e (A, B)
        have hA1 : (Finset.addDysonETransform e (A, B)).1 = A ∪ (e +ᵥ B) := by
          simp [Finset.addDysonETransform]
        have hB1 : (Finset.addDysonETransform e (A, B)).2 = B ∩ ((-e) +ᵥ A) := by
          simp [Finset.addDysonETransform]
        have hB1sub : (Finset.addDysonETransform e (A, B)).2 ⊆ B := by
          rw [hB1]; exact inter_subset_left
        have hlt : (Finset.addDysonETransform e (A, B)).2.card < B.card := by
          obtain ⟨x, hx1, hx2⟩ : ∃ x ∈ (e +ᵥ B), x ∉ A := by
            by_contra hcon
            push_neg at hcon
            exact he hcon
          have h1 : A ⊂ (A ∪ (e +ᵥ B)) :=
            ⟨Finset.subset_union_left,
              fun h => hx2 (h (Finset.mem_union_right _ hx1))⟩
          have h2 : A.card < (Finset.addDysonETransform e (A, B)).1.card := by
            rw [hA1]
            exact Finset.card_lt_card h1
          omega
        rcases (Finset.addDysonETransform e (A, B)).2.eq_empty_or_nonempty with hB1e | hB1ne
        · -- B₁ empty: A ∪ (e +ᵥ B) ⊆ A + B (here 0 ∈ B is used for the A part)
          have hAu : (Finset.addDysonETransform e (A, B)).1 ⊆ A + B := by
            rw [hA1]
            intro x hx
            rcases Finset.mem_union.1 hx with h | h
            · exact mem_add.2 ⟨_, h, 0, hB0, by simp⟩
            · obtain ⟨b, hb, rfl⟩ := mem_vadd_finset.1 h
              exact mem_add.2 ⟨e, heA, b, hb, by rw [vadd_eq_add]⟩
          have hB1card : (Finset.addDysonETransform e (A, B)).2.card = 0 := by
            rw [hB1e]; simp
          have hle : (Finset.addDysonETransform e (A, B)).1.card ≤ (A + B).card :=
            card_mono hAu
          omega
        · -- recurse along the transform; 0 stays in B₁ because e ∈ A
          have hB1ne0 : (0 : ZMod m) ∈ (Finset.addDysonETransform e (A, B)).2 := by
            rw [hB1, mem_inter]
            refine ⟨hB0, mem_vadd_finset.2 ⟨e, heA, ?_⟩⟩
            rw [vadd_eq_add, neg_add_cancel]
          have hcard₁ : (Finset.addDysonETransform e (A, B)).1.card
              + (Finset.addDysonETransform e (A, B)).2.card ≤ m := by omega
          have hunit₁ : ∀ b ∈ (Finset.addDysonETransform e (A, B)).2,
              ∀ b' ∈ (Finset.addDysonETransform e (A, B)).2, b ≠ b' → IsUnit (b - b') :=
            fun b hb b' hb' h => hunit b (hB1sub hb) b' (hB1sub hb') h
          have hA1ne : (Finset.addDysonETransform e (A, B)).1.Nonempty := by
            rw [hA1]
            exact Finset.union_nonempty.2 (Or.inl hA)
          have hIH := IH hm (Finset.addDysonETransform e (A, B)).1
            (Finset.addDysonETransform e (A, B)).2 hA1ne hB1ne hB1ne0 hcard₁ hunit₁
            (by omega)
          have hle : ((Finset.addDysonETransform e (A, B)).1
            + (Finset.addDysonETransform e (A, B)).2).card ≤ (A + B).card :=
            card_mono hsub
          omega
      · push_neg at hex
        -- A + B ⊆ A
        have hAB : A + B ⊆ A := by
          intro x hx
          obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hx
          have hva : a + b ∈ a +ᵥ B := mem_vadd_finset.2 ⟨_, hb, rfl⟩
          exact hex a ha hva
        obtain ⟨b₁, hb₁, b₂, hb₂, hb12⟩ : ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ ≠ b₂ := by
          rcases Finset.one_lt_card_iff.1 (by omega : 1 < B.card) with ⟨x, y, hx, hy, hxy⟩
          exact ⟨x, hx, y, hy, hxy⟩
        obtain ⟨a₀, ha₀⟩ := hA
        obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.1 (hunit b₁ hb₁ b₂ hb₂ hb12)
        have hmem : ∀ k < m, a₀ + k • (b₁ - b₂) ∈ A := by
          intro k hk
          have h2 : a₀ + k • b₁ + (m - k) • b₂ = a₀ + k • (b₁ - b₂) := by
            have hz : m • b₂ = 0 := ZModModule.char_nsmul_eq_zero m b₂
            have hsplit : k • b₂ + (m - k) • b₂ = m • b₂ := by
              rw [← add_nsmul]
              congr 1
              omega
            have hsub : (m - k) • b₂ = m • b₂ - k • b₂ := by
              rw [← hsplit]
              abel
            rw [hsub, hz, zero_sub, smul_sub]
            abel
          have h1 : a₀ + k • (b₁ - b₂) ∈ A := by
            have h1' : a₀ + k • b₁ + (m - k) • b₂ ∈ A :=
              closure_iterate hAB ha₀ hb₁ hb₂ m k (by omega)
            rw [h2] at h1'
            exact h1'
          exact h1
        have himgS : ((Finset.range m).image (fun k => a₀ + k • (b₁ - b₂))) ⊆ A := by
          intro x hx
          obtain ⟨k, hk, rfl⟩ := mem_image.1 hx
          exact hmem k (Finset.mem_range.1 hk)
        have hinj : Set.InjOn (fun k : ℕ => a₀ + k • (b₁ - b₂)) ((Finset.range m) : Set ℕ) := by
          intro k hk k' hk' heq
          simp only [nsmul_eq_mul] at heq
          have hklt : k < m := Finset.mem_range.1 (by exact hk)
          have hklt' : k' < m := Finset.mem_range.1 (by exact hk')
          have h2 : ((k : ℕ) : ZMod m) = ((k' : ℕ) : ZMod m) := by
            have hstep : ((k : ℕ) : ZMod m) * (b₁ - b₂)
                = ((k' : ℕ) : ZMod m) * (b₁ - b₂) := add_left_cancel heq
            have hc := congrArg (fun z => z * u) hstep
            simp only [mul_assoc, hu, mul_one] at hc
            exact hc
          have hval : k % m = k' % m := by
            simpa [Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hklt'] using congrArg ZMod.val h2
          have hkk : k % m = k := Nat.mod_eq_of_lt hklt
          have hkk' : k' % m = k' := Nat.mod_eq_of_lt hklt'
          omega
        have himgcard : ((Finset.range m).image (fun k => a₀ + k • (b₁ - b₂))).card = m := by
          rw [Finset.card_image_of_injOn hinj, card_range]
        have hle : ((Finset.range m).image (fun k => a₀ + k • (b₁ - b₂))).card ≤ A.card :=
          card_mono himgS
        omega

/-- **Chowla's theorem**: if `A, B ⊆ ℤ/m` are nonempty, `|A| + |B| ≤ m`, and every
nonzero difference of elements of `B` is a unit, then `|A + B| ≥ |A| + |B| - 1`. -/
theorem chowla {m : ℕ} (hm : 0 < m) {A B : Finset (ZMod m)}
    (hA : A.Nonempty) (hB : B.Nonempty) (hcard : A.card + B.card ≤ m)
    (hunit : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → IsUnit (b - b')) :
    A.card + B.card - 1 ≤ (A + B).card := by
  obtain ⟨b₀, hb₀⟩ := hB
  have hB₀card : (B.image (fun b => b - b₀)).card = B.card :=
    card_image_of_injective _ (fun x y h => by
      apply_fun (fun z => z + b₀) at h
      simpa using h)
  have hB₀ne : (B.image (fun b => b - b₀)).Nonempty :=
    ⟨0, mem_image.2 ⟨b₀, hb₀, by simp⟩⟩
  have hcard₀ : A.card + (B.image (fun b => b - b₀)).card ≤ m := by
    rw [hB₀card]; exact hcard
  have hunit₀ : ∀ b ∈ (B.image (fun b => b - b₀)), ∀ b' ∈ (B.image (fun b => b - b₀)),
      b ≠ b' → IsUnit (b - b') := by
    intro b hb b' hb' h
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hb
    obtain ⟨c', hc', rfl⟩ := mem_image.1 hb'
    have hcc' : c ≠ c' := by
      by_contra hcon
      exact h (by rw [hcon])
    have hconv : c - b₀ - (c' - b₀) = c - c' := by abel
    rw [hconv]
    exact hunit c hc c' hc' hcc'
  have hmain := chowla_aux B.card hm A (B.image (fun b => b - b₀)) hA hB₀ne
    (mem_image.2 ⟨b₀, hb₀, by simp⟩) hcard₀ hunit₀ (by rw [hB₀card])
  -- translation: (A + B₀) + {b₀} = A + B
  have hBshift : ((B.image (fun b => b - b₀)) + {b₀}) = B := by
    ext x
    simp only [Finset.mem_add, mem_singleton, mem_image]
    constructor
    · rintro ⟨y, hy, hyx⟩
      obtain ⟨c, hc, hcy⟩ := hy
      obtain ⟨z, hz, hyz⟩ := hyx
      have hzc : z = b₀ := by rw [← hz]
      have hxc : x = c := by rw [← hyz, hzc, ← hcy]; abel
      rw [hxc]
      exact hc
    · intro hx
      exact ⟨x - b₀, ⟨x, hx, rfl⟩, b₀, rfl, by abel⟩
  have htrans : ((A + (B.image (fun b => b - b₀))) + {b₀}) = A + B := by
    rw [add_assoc, hBshift]
  have hcardtr : (A + (B.image (fun b => b - b₀))).card = (A + B).card := by
    rw [← htrans, card_add_singleton]
  rwa [hcardtr, hB₀card] at hmain

/-- **Cauchy–Davenport** (derived from Chowla's theorem). -/
theorem cauchy_davenport {p : ℕ} (hp : p.Prime) {A B : Finset (ZMod p)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 1) ≤ (A + B).card := by
  classical
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Nat.lt_or_ge (A.card + B.card) (p + 1) with hlt | hge
  · -- |A| + |B| ≤ p : Chowla's theorem directly
    have hunits : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → IsUnit (b - b') := by
      intro b _ b' _ h
      have h0 : b - b' ≠ (0 : ZMod p) := sub_ne_zero.2 h
      exact (isUnit_iff_ne_zero (a := b - b')).mpr h0
    exact (min_le_right _ _).trans (Chowla.chowla hp.pos hA hB (by omega) hunits)
  · -- |A| + |B| ≥ p + 1 : pigeonhole, A + B is everything
    have huniv : A + B = Finset.univ := by
      ext x
      simp only [Finset.mem_univ, iff_true]
      by_contra hcon
      -- the translate x - A is disjoint from B
      have hTcard : (A.image (fun a => x - a)).card = A.card :=
        Finset.card_image_of_injective _
          (fun a a' h => sub_right_inj.1 h)
      have hdisj : Disjoint (A.image (fun a => x - a)) B := by
        rw [Finset.disjoint_right]
        intro b hb
        rw [mem_image]
        push_neg
        intro a ha hxa
        exact hcon (mem_add.2 ⟨a, ha, b, hb, by
          rw [← hxa]
          abel⟩)
      have h1 := Finset.card_union_add_card_inter
        (A.image (fun a => x - a)) B
      rw [Finset.disjoint_iff_inter_eq_empty.1 hdisj, card_empty, add_zero] at h1
      have hcard : A.card + B.card ≤ (Finset.univ : Finset (ZMod p)).card := by
        rw [← hTcard, ← h1]
        exact card_le_card (subset_univ _)
      rw [Finset.card_univ, ZMod.card] at hcard
      omega
    rw [huniv, Finset.card_univ, ZMod.card]
    omega

end Chowla

open scoped Pointwise

theorem solution {p : ℕ} (hp : p.Prime) {A B : Finset (ZMod p)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 1) ≤ (A + B).card :=
  Chowla.cauchy_davenport hp hA hB
