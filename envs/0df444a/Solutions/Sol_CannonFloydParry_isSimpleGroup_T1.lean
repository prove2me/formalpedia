-- Prove2me | solution 1 for CannonFloydParry.isSimpleGroup_T1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-25T20:16:36.885584+00:00
-- url     : https://prove2.me/submissions/96206976-7c0a-4b41-b4e2-f0af1b67fbee

import Definitions.Def_CannonFloydParry_T
import Definitions.Def_CannonFloydParry_Presentations
import Mathlib
import Theorems.Thm_CannonFloydParry_exists_mulEquiv_closure_A_B_F
import Theorems.Thm_CannonFloydParry_exists_eq_mul_CT1_pow_mul_inv
import Theorems.Thm_CannonFloydParry_CT1_pow_relations
import Theorems.Thm_CannonFloydParry_mul_comm_quotient_of_ne_bot
import Theorems.Thm_CannonFloydParry_exists_biInvariant_linearOrder

/-! The algebra of `T₁` (CFP pp. 236–238): relations, the map `F₁ → T₁`, `XₙXₖ = XₖXₙ₊₁`,
Lemma 5.5 and Lemma 5.6. -/

namespace CannonFloydParry.S5

open PresentedGroup

local notation "a" => (PresentedGroup.of FormalABC.A : T1)
local notation "b" => (PresentedGroup.of FormalABC.B : T1)
local notation "c" => (PresentedGroup.of FormalABC.C : T1)

lemma mem_rels {r : FreeGroup FormalABC} (h : r ∈ relsT1) : (PresentedGroup.mk relsT1 r) = 1 :=
  PresentedGroup.one_of_mem h

lemma rel1 : (a * b⁻¹) * (a⁻¹ * b * a) * (a * b⁻¹)⁻¹ * (a⁻¹ * b * a)⁻¹ = 1 := by
  have h := mem_rels (r := _) (Or.inl rfl)
  simp only [map_mul, map_inv] at h
  exact h

lemma rel2 : (a * b⁻¹) * (a⁻¹ ^ 2 * b * a ^ 2) * (a * b⁻¹)⁻¹ * (a⁻¹ ^ 2 * b * a ^ 2)⁻¹ = 1 := by
  have h := mem_rels (r := _) (Or.inr (Or.inl rfl))
  simp only [map_mul, map_inv, map_pow] at h
  exact h

lemma rel3 : c = b * (a⁻¹ * c * b) := by
  have h := mem_rels (r := _) (Or.inr (Or.inr (Or.inl rfl)))
  simp only [map_mul, map_inv] at h
  change c⁻¹ * b * (a⁻¹ * c * b) = 1 at h
  calc c = c * (c⁻¹ * b * (a⁻¹ * c * b)) := by rw [h, mul_one]
    _ = _ := by group

lemma rel4 : (a⁻¹ * c * b) * (a⁻¹ * b * a) = b * (a⁻¹ ^ 2 * c * b ^ 2) := by
  have h := mem_rels (r := _) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  simp only [map_mul, map_inv, map_pow] at h
  change ((a⁻¹ * c * b) * (a⁻¹ * b * a))⁻¹ * b * (a⁻¹ ^ 2 * c * b ^ 2) = 1 at h
  calc _ = ((a⁻¹ * c * b) * (a⁻¹ * b * a)) *
        (((a⁻¹ * c * b) * (a⁻¹ * b * a))⁻¹ * b * (a⁻¹ ^ 2 * c * b ^ 2)) := by rw [h, mul_one]
    _ = _ := by group

lemma rel5 : c * a = (a⁻¹ * c * b) ^ 2 := by
  have h := mem_rels (r := _) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  simp only [map_mul, map_inv, map_pow] at h
  change (c * a)⁻¹ * (a⁻¹ * c * b) ^ 2 = 1 at h
  calc c * a = (c * a) * ((c * a)⁻¹ * (a⁻¹ * c * b) ^ 2) := by rw [h, mul_one]
    _ = _ := by group

/-- The map `F₁ → T₁`, `A ↦ A`, `B ↦ B`. -/
noncomputable def fromF1 : F1 →* T1 :=
  PresentedGroup.toGroup (f := fun s => match s with | FormalAB.A => a | FormalAB.B => b) (by
    intro r hr
    rcases hr with rfl | rfl
    · simpa using rel1
    · simpa using rel2)

@[simp] lemma fromF1_A : fromF1 (PresentedGroup.of FormalAB.A) = a := PresentedGroup.toGroup.of _
@[simp] lemma fromF1_B : fromF1 (PresentedGroup.of FormalAB.B) = b := PresentedGroup.toGroup.of _


section Lemma56
variable (n : ℕ) (hn : 0 < n)
include hn

end Lemma56

end CannonFloydParry.S5

/-! Theorem 5.8: `T₁` is simple (CFP pp. 239–240). -/

namespace CannonFloydParry.S5

local notation "a" => (PresentedGroup.of FormalABC.A : T1)
local notation "b" => (PresentedGroup.of FormalABC.B : T1)
local notation "c" => (PresentedGroup.of FormalABC.C : T1)

/-- `F` is torsion-free: it carries a bi-invariant total order (Theorem 4.11). -/
lemma F_pow_ne_one {w : F} (hw : w ≠ 1) (k : ℕ) : w ^ (k + 1) ≠ 1 := by
  obtain ⟨l, hl⟩ := exists_biInvariant_linearOrder
  let _ := l
  have mono : ∀ x y z : F, x ≤ y → x * z ≤ y * z := fun x y z h => (hl x y z h).2
  rcases lt_or_gt_of_ne hw with h | h
  · -- w < 1: every positive power is < 1
    have : ∀ k : ℕ, w ^ (k + 1) < 1 := by
      intro k
      induction k with
      | zero => simpa using h
      | succ k ih =>
        rw [pow_succ]
        calc w ^ (k + 1) * w ≤ 1 * w := mono _ _ _ ih.le
          _ = w := one_mul w
          _ < 1 := h
    exact (this k).ne
  · have : ∀ k : ℕ, 1 < w ^ (k + 1) := by
      intro k
      induction k with
      | zero => simpa using h
      | succ k ih =>
        rw [pow_succ]
        calc (1 : F) < w := h
          _ = 1 * w := (one_mul w).symm
          _ ≤ w ^ (k + 1) * w := mono _ _ _ ih.le
    exact (this k).ne'

lemma mapA_ne_one : mapA ≠ 1 := by
  intro h
  have := congrArg (fun f : UI ≃o UI => ((f ⟨1/2, by norm_num, by norm_num⟩ : UI) : ℝ)) h
  simp only [mapA, restrict_coe, lineA_apply] at this
  rw [aFun_of_mem1 (by norm_num) (by norm_num)] at this
  norm_num at this

lemma mapB_ne_one : mapB ≠ 1 := by
  intro h
  have := congrArg (fun f : UI ≃o UI => ((f ⟨5/8, by norm_num, by norm_num⟩ : UI) : ℝ)) h
  simp only [mapB, restrict_coe, lineB_apply] at this
  rw [bFun_of_mem1 (by norm_num) (by norm_num)] at this
  norm_num at this

/-- Theorem 5.8. -/
theorem isSimpleGroup_T1' : IsSimpleGroup T1 := by
  obtain ⟨e, heA, heB⟩ := exists_mulEquiv_closure_A_B_F
  set K := Subgroup.closure ({a, b} : Set T1) with hK
  have haK : a ∈ K := Subgroup.subset_closure (by simp)
  have hbK : b ∈ K := Subgroup.subset_closure (by simp)
  have ha1 : a ≠ 1 := by
    intro h
    apply mapA_ne_one
    rw [← heA haK]
    have : (⟨a, haK⟩ : K) = 1 := Subtype.ext h
    rw [this, map_one]; rfl
  have hb1 : b ≠ 1 := by
    intro h
    apply mapB_ne_one
    rw [← heB hbK]
    have : (⟨b, hbK⟩ : K) = 1 := Subtype.ext h
    rw [this, map_one]; rfl
  have hXK : ∀ i, XT1 i ∈ K := by
    intro i; cases i with
    | zero => exact haK
    | succ i => exact K.mul_mem (K.mul_mem (K.inv_mem (K.pow_mem haK _)) hbK) (K.pow_mem haK _)
  have hX1 : ∀ i, XT1 i ≠ 1 := by
    intro i h
    cases i with
    | zero => exact ha1 h
    | succ i =>
      apply hb1
      simp only [XT1] at h
      calc b = (a ^ i) * ((a ^ i)⁻¹ * b * a ^ i) * (a ^ i)⁻¹ := by group
        _ = 1 := by rw [h]; group
  have hposK : ∀ p, IsPositiveT1 p → p ∈ K := by
    intro p hp
    exact (Submonoid.closure_le (S := K.toSubmonoid)).2 (by rintro _ ⟨i, rfl⟩; exact hXK i) hp
  -- torsion-freeness inside `K ≅ F`
  have torsion : ∀ w ∈ K, w ≠ 1 → ∀ k : ℕ, w ^ (k + 1) ≠ 1 := by
    intro w hw hw1 k h
    have hne : e ⟨w, hw⟩ ≠ 1 := by
      intro h'; apply hw1; have := congrArg Subtype.val (e.injective (h'.trans (map_one e).symm)); simpa using this
    apply F_pow_ne_one hne k
    rw [← map_pow]
    have : (⟨w, hw⟩ : K) ^ (k + 1) = 1 := Subtype.ext (by simpa using h)
    rw [this, map_one]
  have : Nontrivial T1 := ⟨⟨a, 1, ha1⟩⟩
  refine ⟨fun N hN => ?_⟩
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  let θ : T1 →* T1 ⧸ N := QuotientGroup.mk' N
  have hθ : ∀ x, θ x = 1 ↔ x ∈ N := fun x => QuotientGroup.eq_one_iff x
  obtain ⟨g, hgN, hg1⟩ : ∃ g ∈ N, g ≠ 1 := by
    by_contra h; push Not at h
    exact hbot ((Subgroup.eq_bot_iff_forall N).2 h)
  obtain ⟨p, q, m, n, hp, hq, hmn, rfl⟩ := exists_eq_mul_CT1_pow_mul_inv g
  have hθg : θ (p * CT1 n ^ m * q⁻¹) = 1 := (hθ _).2 hgN
  have hCq : θ (CT1 n ^ m) = θ (p⁻¹ * q) := by
    simp only [map_mul, map_inv] at hθg ⊢
    calc θ (CT1 n ^ m) = (θ p)⁻¹ * (θ p * θ (CT1 n ^ m) * (θ q)⁻¹) * θ q := by group
      _ = _ := by rw [hθg]; group
  -- the map `α : F → T₁/N`
  let α : F →* T1 ⧸ N := θ.comp (K.subtype.comp e.symm.toMonoidHom)
  have hαK : ∀ w : K, α (e w) = θ w := by intro w; simp [α]
  -- a nontrivial kernel element of `α` makes `θ A`, `θ B` commute
  have commute_of : ∀ w ∈ K, w ≠ 1 → θ w = 1 → θ (a * b) = θ (b * a) := by
    intro w hw hw1 hθw
    have hker : α.ker ≠ ⊥ := by
      intro hk
      have hmem : e ⟨w, hw⟩ ∈ α.ker := by rw [MonoidHom.mem_ker, hαK]; exact hθw
      rw [hk, Subgroup.mem_bot] at hmem
      apply hw1
      have := congrArg Subtype.val (e.injective (hmem.trans (map_one e).symm))
      simpa using this
    have hc := mul_comm_quotient_of_ne_bot α.ker hker (QuotientGroup.mk (e ⟨a, haK⟩))
      (QuotientGroup.mk (e ⟨b, hbK⟩))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, MonoidHom.mem_ker,
      map_mul, map_inv, inv_mul_eq_one] at hc
    have e1 : α (e ⟨b, hbK⟩ * e ⟨a, haK⟩) = θ (b * a) := by
      rw [← map_mul, hαK]; rfl
    have e2 : α (e ⟨a, haK⟩ * e ⟨b, hbK⟩) = θ (a * b) := by
      rw [← map_mul, hαK]; rfl
    rw [e1, e2] at hc
    exact hc
  have hab : θ (a * b) = θ (b * a) := by
    by_cases hpq : p⁻¹ * q = 1
    · have hpq' : p = q := by rw [inv_mul_eq_one] at hpq; exact hpq
      have hCm : θ (CT1 n ^ m) = 1 := by rw [hCq, hpq, map_one]
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · exfalso; apply hg1; rw [hpq']; simp [CT1]
        · exact hn
      have hm : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · exfalso; apply hg1; rw [hpq']; simp
        · exact hm
      obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := CT1_pow_relations n m 0 0 hn hm (by omega) (by omega) (by omega)
      obtain ⟨-, -, -, -, -, -, -, -, h9⟩ := CT1_pow_relations (n + 1) 1 0 0 (by omega) le_rfl (by omega) (by omega) (by omega)
      have hX : θ (XT1 (m - 1)) = θ (CT1 (n + 1) ^ (m + 1)) := by
        have := hCm; rw [h8, map_mul, map_inv, mul_inv_eq_one] at this; exact this.symm
      refine commute_of (XT1 (m - 1) ^ (n + 2 + 1)) (K.pow_mem (hXK _) _)
        (torsion _ (hXK _) (hX1 _) _) ?_
      rw [map_pow, hX, ← map_pow, ← pow_mul, mul_comm, pow_mul,
        show n + 2 + 1 = n + 1 + 2 by omega, h9, one_pow, map_one]
    · refine commute_of ((p⁻¹ * q) ^ (n + 1 + 1)) (K.pow_mem (K.mul_mem (K.inv_mem (hposK p hp))
        (hposK q hq)) _) (torsion _ (K.mul_mem (K.inv_mem (hposK p hp)) (hposK q hq)) hpq _) ?_
      rw [map_pow, ← hCq, ← map_pow, ← pow_mul, mul_comm, pow_mul]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [CT1]
      · obtain ⟨-, -, -, -, -, -, -, -, h9⟩ := CT1_pow_relations n 1 0 0 hn le_rfl (by omega) (by omega) (by omega)
        rw [h9, one_pow, map_one]
  -- relations 3)–5) now kill the generators
  set A' := θ a
  set B' := θ b
  set C' := θ c
  have hc : A' * B' = B' * A' := by simpa [map_mul] using hab
  have h4 : (A'⁻¹ * C' * B') * (A'⁻¹ * B' * A') = B' * (A'⁻¹ ^ 2 * C' * B' ^ 2) := by
    simpa [map_mul, map_inv, map_pow] using congrArg θ rel4
  have h3 : C' = B' * (A'⁻¹ * C' * B') := by simpa [map_mul, map_inv] using congrArg θ rel3
  have h5 : C' * A' = (A'⁻¹ * C' * B') ^ 2 := by
    simpa [map_mul, map_inv, map_pow] using congrArg θ rel5
  have hconj : A'⁻¹ * B' * A' = B' := by
    calc A'⁻¹ * B' * A' = A'⁻¹ * (B' * A') := by group
      _ = A'⁻¹ * (A' * B') := by rw [hc]
      _ = B' := by group
  rw [hconj] at h4
  have key : A'⁻¹ * (C' * B' ^ 2) = B' * A'⁻¹ ^ 2 * (C' * B' ^ 2) := by
    calc A'⁻¹ * (C' * B' ^ 2) = (A'⁻¹ * C' * B') * B' := by rw [sq]; simp only [mul_assoc]
      _ = B' * (A'⁻¹ ^ 2 * C' * B' ^ 2) := h4
      _ = B' * A'⁻¹ ^ 2 * (C' * B' ^ 2) := by group
  have hinv : A'⁻¹ = B' * A'⁻¹ ^ 2 := by
    calc A'⁻¹ = A'⁻¹ * (C' * B' ^ 2) * (C' * B' ^ 2)⁻¹ := by group
      _ = B' * A'⁻¹ ^ 2 * (C' * B' ^ 2) * (C' * B' ^ 2)⁻¹ := by rw [key]
      _ = B' * A'⁻¹ ^ 2 := by group
  have hAB : A' = B' := by
    calc A' = A'⁻¹ * A' ^ 2 := by group
      _ = (B' * A'⁻¹ ^ 2) * A' ^ 2 := by rw [← hinv]
      _ = B' := by group
  have hB : B' = 1 := by
    have : C' = C' * B' := by
      calc C' = B' * (A'⁻¹ * C' * B') := h3
        _ = C' * B' := by rw [hAB]; group
    exact (mul_eq_left.1 this.symm)
  have hA : A' = 1 := hAB.trans hB
  have hC : C' = 1 := by
    rw [hA, hB] at h5
    have : C' = C' ^ 2 := by simpa using h5
    rw [sq] at this
    exact (mul_eq_left.1 this.symm)
  rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, ← hθ]
  cases s
  · exact hA
  · exact hB
  · exact hC

end CannonFloydParry.S5

open CannonFloydParry

theorem solution : IsSimpleGroup T1 :=
  CannonFloydParry.S5.isSimpleGroup_T1'
