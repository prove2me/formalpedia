-- Prove2me | solution 1 for CannonFloydParry.CT1_pow_relations
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T09:20:19.985356+00:00
-- url     : https://prove2.me/submissions/8891bd83-d456-4ccd-b1c9-341f97d3ccfd

import Theorems.Thm_CannonFloydParry_XT1_mul_XT1
import Definitions.Def_CannonFloydParry_T
import Definitions.Def_CannonFloydParry_Presentations
import Mathlib

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

lemma rel6 : c ^ 3 = 1 := by
  have h := mem_rels (r := _) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  simp only [map_pow] at h
  exact h

/-- The map `F₁ → T₁`, `A ↦ A`, `B ↦ B`. -/
noncomputable def fromF1 : F1 →* T1 :=
  PresentedGroup.toGroup (f := fun s => match s with | FormalAB.A => a | FormalAB.B => b) (by
    intro r hr
    rcases hr with rfl | rfl
    · simpa using rel1
    · simpa using rel2)

@[simp] lemma fromF1_A : fromF1 (PresentedGroup.of FormalAB.A) = a := PresentedGroup.toGroup.of _
@[simp] lemma fromF1_B : fromF1 (PresentedGroup.of FormalAB.B) = b := PresentedGroup.toGroup.of _

/-- p. 236: `XₙXₖ = XₖXₙ₊₁` for `k < n`. -/
theorem XT1_mul_XT1' (k n : ℕ) (hkn : k < n) : XT1 n * XT1 k = XT1 k * XT1 (n + 1) :=
  by
  first
    | exact CannonFloydParry.XT1_mul_XT1
    | exact CannonFloydParry.XT1_mul_XT1 ..
    | (apply CannonFloydParry.XT1_mul_XT1 <;> first | assumption | infer_instance)
    | simpa using CannonFloydParry.XT1_mul_XT1


lemma XT1_zero : XT1 0 = a := rfl
lemma XT1_one : XT1 1 = b := by simp [XT1]
lemma CT1_one : CT1 1 = c := by simp [CT1]

lemma conj_XT1 (j : ℕ) : a⁻¹ * XT1 (j + 1) * a = XT1 (j + 2) := by
  simp only [XT1]; group

lemma conj_CT1 (n : ℕ) : a⁻¹ * CT1 (n + 1) * b = CT1 (n + 2) := by
  simp only [CT1]; group

/-- Lemma 5.5 i). -/
lemma CT1_eq (n : ℕ) (hn : 0 < n) : CT1 n = XT1 n * CT1 (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [CT1, XT1]
  calc (a ^ m)⁻¹ * c * b ^ m = (a ^ m)⁻¹ * (b * (a⁻¹ * c * b)) * b ^ m := by rw [← rel3]
    _ = _ := by group

/-- Lemma 5.5 ii). -/
lemma CT1_mul_XT1 : ∀ k n : ℕ, 0 < k → k ≤ n → CT1 n * XT1 k = XT1 (k - 1) * CT1 (n + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro n hk hkn
  rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | h3
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [CT1, XT1]; group
  · -- k = 2: induction on n ≥ 2
    induction n with
    | zero => omega
    | succ n ihn =>
      rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
      · simp only [CT1, XT1]
        have := rel4
        calc (a ^ 1)⁻¹ * c * b ^ 1 * ((a ^ 1)⁻¹ * b * a ^ 1)
            = (a⁻¹ * c * b) * (a⁻¹ * b * a) := by group
          _ = b * (a⁻¹ ^ 2 * c * b ^ 2) := this
          _ = _ := by group
      · have h1 := CT1_eq n (by omega)
        have h2 := ihn hn2
        have h3 := XT1_mul_XT1' 1 n (by omega)
        have h4 := CT1_eq (n + 1) (by omega)
        show CT1 (n + 1) * XT1 2 = XT1 1 * CT1 (n + 1 + 1)
        have e : CT1 (n + 1) = (XT1 n)⁻¹ * CT1 n := by rw [h1]; group
        rw [e, mul_assoc, h2]
        simp only [Nat.add_one_sub_one] at *
        calc (XT1 n)⁻¹ * (XT1 1 * CT1 (n + 1)) = (XT1 n)⁻¹ * XT1 1 * CT1 (n + 1) := by group
          _ = XT1 1 * (XT1 (n + 1))⁻¹ * CT1 (n + 1) := by
            congr 1
            calc (XT1 n)⁻¹ * XT1 1 = (XT1 n)⁻¹ * (XT1 n * XT1 1 * (XT1 (n + 1))⁻¹) := by
                  rw [h3]; group
              _ = _ := by group
          _ = XT1 1 * CT1 (n + 1 + 1) := by rw [h4]; group
  · -- k ≥ 3: from k - 1 and n - 1
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have hC : CT1 (m + 3) = a⁻¹ * CT1 (m + 2) * b := by rw [← conj_CT1]
    have hB : b * XT1 (j + 3) = XT1 (j + 2) * b := by
      have := XT1_mul_XT1' 1 (j + 2) (by omega)
      rw [XT1_one] at this; exact this.symm
    have ih' := ih (j + 2) (by omega) (m + 2) (by omega) (by omega)
    simp only [show j + 2 - 1 = j + 1 by omega, show m + 2 + 1 = m + 3 by omega] at ih'
    simp only [show j + 3 - 1 = j + 2 by omega]
    rw [hC, mul_assoc, hB, ← mul_assoc, mul_assoc (a⁻¹), ih', ← conj_XT1 j, ← conj_CT1 (m + 2)]
    group

/-- Lemma 5.5 iii). -/
lemma CT1_mul_A : ∀ n : ℕ, 0 < n → CT1 n * a = CT1 (n + 1) ^ 2 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp only [CT1]
      have := rel5
      simp only [pow_one, pow_zero, inv_one, one_mul, mul_one] at *
      rw [this]
    · have hC : CT1 (n + 1) = a⁻¹ * CT1 n * b := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [← conj_CT1]
      have hBA : b * a = a * XT1 2 := by simp only [XT1]; group
      have h2 := CT1_mul_XT1 2 (n + 1) (by omega) (by omega)
      simp only [show 2 - 1 = 1 by omega, XT1_one] at h2
      calc CT1 (n + 1) * a = a⁻¹ * CT1 n * (b * a) := by rw [hC]; group
        _ = a⁻¹ * (CT1 n * a) * XT1 2 := by rw [hBA]; group
        _ = a⁻¹ * CT1 (n + 1) * (CT1 (n + 1) * XT1 2) := by rw [ih hn', sq]; group
        _ = a⁻¹ * CT1 (n + 1) * (b * CT1 (n + 1 + 1)) := by rw [h2]
        _ = (a⁻¹ * CT1 (n + 1) * b) * CT1 (n + 1 + 1) := by group
        _ = CT1 (n + 1 + 1) ^ 2 := by
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          rw [conj_CT1, sq]


section Lemma56
variable (n : ℕ) (hn : 0 < n)
include hn

omit hn in
/-- Lemma 5.6 i), first line. -/
lemma l56_first : ∀ m r : ℕ, m ≤ r → r ≤ n →
    CT1 n ^ m * XT1 r = XT1 (r - m) * CT1 (n + 1) ^ m := by
  intro m
  induction m with
  | zero => intro r _ _; simp
  | succ m ih =>
    intro r hmr hrn
    have h1 := CT1_mul_XT1 r n (by omega) hrn
    have h2 := ih (r - 1) (by omega) (by omega)
    rw [show r - (m + 1) = r - 1 - m by omega, pow_succ, mul_assoc, h1, ← mul_assoc, h2, pow_succ,
      mul_assoc]

/-- Lemma 5.6 i), second line. -/
lemma l56_second (r : ℕ) (hr : r ≤ n) : CT1 n ^ (r + 1) * XT1 r = CT1 (n + 1) ^ (r + 2) := by
  have h := l56_first n r r le_rfl hr
  rw [Nat.sub_self, XT1_zero] at h
  rw [pow_succ', mul_assoc, h, ← mul_assoc, CT1_mul_A n hn, ← pow_add, add_comm 2 r]

/-- Lemma 5.6 iii). -/
lemma l56_iii (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n + 1) :
    CT1 n ^ m = XT1 (n + 1 - m) * CT1 (n + 1) ^ m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have h := l56_first n j n (by omega) le_rfl
  have e := CT1_eq n hn
  calc CT1 n ^ (j + 1) = CT1 n ^ j * (XT1 n * CT1 (n + 1)) := by rw [← e, pow_succ]
    _ = (CT1 n ^ j * XT1 n) * CT1 (n + 1) := by rw [mul_assoc]
    _ = _ := by rw [h, show n + 1 - (j + 1) = n - j by omega, mul_assoc, ← pow_succ]

/-- Lemma 5.6 i), third line. -/
lemma l56_third (m r : ℕ) (hmn : m ≤ n + 1) (hr : r + 1 < m) :
    CT1 n ^ m * XT1 r = XT1 (r + (n + 2 - m)) * CT1 (n + 1) ^ (m + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + (r + 1) := ⟨m - (r + 1), by omega⟩
  rw [pow_add, mul_assoc, l56_second n hn r (by omega), l56_iii n hn j (by omega) (by omega),
    mul_assoc, ← pow_add, show n + 1 - j = r + (n + 2 - (j + (r + 1))) by omega,
    show j + (r + 2) = j + (r + 1) + 1 by omega]

end Lemma56

/-- Lemma 5.6 v). -/
lemma l56_v : ∀ t : ℕ, 0 < t → CT1 t ^ (t + 2) = 1 := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with rfl | ht'
    · rw [CT1_one]; exact rel6
    · have h := l56_iii t ht' (t + 1) (by omega) le_rfl
      rw [Nat.sub_self, XT1_zero] at h
      have : CT1 t ^ (t + 2) = CT1 (t + 1) ^ (t + 1 + 2) := by
        rw [pow_succ', h, ← mul_assoc, CT1_mul_A t ht', ← pow_add]
        congr 1; omega
      rw [← this, ih ht']


theorem CT1_pow_relations' (n m r s : ℕ) (hn : 0 < n) (hm : 1 ≤ m) (hmn : m ≤ n + 1)
    (hr : r ≤ n) (hs : s ≤ n) :
    (m ≤ r → CT1 n ^ m * XT1 r = XT1 (r - m) * CT1 (n + 1) ^ m) ∧
      (r + 1 = m → CT1 n ^ m * XT1 r = CT1 (n + 1) ^ (m + 1)) ∧
      (r + 1 < m → CT1 n ^ m * XT1 r = XT1 (r + (n + 2 - m)) * CT1 (n + 1) ^ (m + 1)) ∧
      (n + 2 ≤ s + m →
        (XT1 s)⁻¹ * CT1 n ^ m = CT1 (n + 1) ^ (m + 1) * (XT1 (s + m - (n + 2)))⁻¹) ∧
      (s + m = n + 1 → (XT1 s)⁻¹ * CT1 n ^ m = CT1 (n + 1) ^ m) ∧
      (s + m ≤ n → (XT1 s)⁻¹ * CT1 n ^ m = CT1 (n + 1) ^ m * (XT1 (s + m))⁻¹) ∧
      CT1 n ^ m = XT1 (n + 1 - m) * CT1 (n + 1) ^ m ∧
      CT1 n ^ m = CT1 (n + 1) ^ (m + 1) * (XT1 (m - 1))⁻¹ ∧
      CT1 n ^ (n + 2) = 1 := by
  refine ⟨fun h => l56_first n m r h hr, ?_, fun h => l56_third n hn m r hmn h, ?_, ?_, ?_,
    l56_iii n hn m hm hmn, ?_, l56_v n hn⟩
  · rintro rfl; exact l56_second n hn r hr
  · intro h
    have e := l56_third n hn m (s + m - (n + 2)) hmn (by omega)
    rw [show s + m - (n + 2) + (n + 2 - m) = s by omega] at e
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]; group
  · intro h
    rw [l56_iii n hn m hm hmn, show n + 1 - m = s by omega]; group
  · intro h
    have e := l56_first n m (s + m) (by omega) (by omega)
    rw [show s + m - m = s by omega] at e
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]; group
  · have e := l56_second n hn (m - 1) (by omega)
    rw [show m - 1 + 1 = m by omega, show m - 1 + 2 = m + 1 by omega] at e
    rw [← e]; group

end CannonFloydParry.S5

open CannonFloydParry

theorem solution (n m r s : ℕ) (hn : 0 < n) (hm : 1 ≤ m) (hmn : m ≤ n + 1)
    (hr : r ≤ n) (hs : s ≤ n) :
    (m ≤ r → CT1 n ^ m * XT1 r = XT1 (r - m) * CT1 (n + 1) ^ m) ∧
      (r + 1 = m → CT1 n ^ m * XT1 r = CT1 (n + 1) ^ (m + 1)) ∧
      (r + 1 < m → CT1 n ^ m * XT1 r = XT1 (r + (n + 2 - m)) * CT1 (n + 1) ^ (m + 1)) ∧
      (n + 2 ≤ s + m →
        (XT1 s)⁻¹ * CT1 n ^ m = CT1 (n + 1) ^ (m + 1) * (XT1 (s + m - (n + 2)))⁻¹) ∧
      (s + m = n + 1 → (XT1 s)⁻¹ * CT1 n ^ m = CT1 (n + 1) ^ m) ∧
      (s + m ≤ n → (XT1 s)⁻¹ * CT1 n ^ m = CT1 (n + 1) ^ m * (XT1 (s + m))⁻¹) ∧
      CT1 n ^ m = XT1 (n + 1 - m) * CT1 (n + 1) ^ m ∧
      CT1 n ^ m = CT1 (n + 1) ^ (m + 1) * (XT1 (m - 1))⁻¹ ∧
      CT1 n ^ (n + 2) = 1 :=
  CannonFloydParry.S5.CT1_pow_relations' n m r s hn hm hmn hr hs
