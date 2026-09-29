-- Prove2me | solution 1 for CannonFloydParry.CV1_pow_mul_piV1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T10:52:07.15763+00:00
-- url     : https://prove2.me/submissions/a5f56192-59a0-4220-8fdc-025780f2b5d4

import Definitions.Def_CannonFloydParry_V
import Theorems.Thm_CannonFloydParry_CT1_succ_relations
import Theorems.Thm_CannonFloydParry_CT1_pow_relations
import Theorems.Thm_CannonFloydParry_XT1_mul_XT1
import Mathlib

/-! The algebra of `V₁` (CFP p. 242): its relators, the map `T₁ → V₁`, and Lemmas 5.5, 5.6
carried into `V₁`. -/

namespace CannonFloydParry.S6

open PresentedGroup

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)
local notation "cV" => (PresentedGroup.of FormalV.C : V1)
local notation "pV" => (PresentedGroup.of FormalV.P : V1)

lemma mk_of (s : FormalV) : PresentedGroup.mk relsV1 (FreeGroup.of s) = PresentedGroup.of s := rfl

lemma XV1_zero : XV1 0 = aV := rfl
lemma XV1_succ (n : ℕ) : XV1 (n + 1) = (aV ^ n)⁻¹ * bV * aV ^ n := by
  simp [XV1, wordX, map_mul, map_inv, map_pow, mk_of]
lemma CV1_zero : CV1 0 = 1 := by simp [CV1, wordC]
lemma CV1_succ (n : ℕ) : CV1 (n + 1) = (aV ^ n)⁻¹ * cV * bV ^ n := by
  simp [CV1, wordC, map_mul, map_inv, map_pow, mk_of]
lemma piV1_zero : piV1 0 = pV := rfl
lemma piV1_succ (n : ℕ) : piV1 (n + 1) = (aV ^ n)⁻¹ * ((CV1 2)⁻¹ * pV * CV1 2) * aV ^ n := by
  simp only [piV1, wordPi, map_mul, map_inv, map_pow, mk_of]; rfl

lemma rel (r : FreeGroup FormalV) (h : r ∈ relsV1) : PresentedGroup.mk relsV1 r = 1 :=
  PresentedGroup.one_of_mem h

/-- The fourteen relations of `V₁`, as equations. -/
lemma relV1 :
    (aV * bV⁻¹) * XV1 2 * (aV * bV⁻¹)⁻¹ * (XV1 2)⁻¹ = 1 ∧
    (aV * bV⁻¹) * XV1 3 * (aV * bV⁻¹)⁻¹ * (XV1 3)⁻¹ = 1 ∧
    CV1 1 = bV * CV1 2 ∧
    CV1 2 * XV1 2 = bV * CV1 3 ∧
    CV1 1 * aV = CV1 2 ^ 2 ∧
    CV1 1 ^ 3 = 1 ∧
    piV1 1 ^ 2 = 1 ∧
    piV1 1 * piV1 3 = piV1 3 * piV1 1 ∧
    (piV1 2 * piV1 1) ^ 3 = 1 ∧
    XV1 3 * piV1 1 = piV1 1 * XV1 3 ∧
    piV1 1 * XV1 2 = bV * piV1 2 * piV1 1 ∧
    piV1 2 * bV = bV * piV1 3 ∧
    piV1 1 * CV1 3 = CV1 3 * piV1 2 ∧
    (piV1 1 * CV1 2) ^ 3 = 1 := by
  have R := fun r (h : r ∈ relsV1) => rel r h
  have h1 := R _ (Or.inl rfl)
  have h2 := R _ (Or.inr (Or.inl rfl))
  have h3 := R _ (Or.inr (Or.inr (Or.inl rfl)))
  have h4 := R _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h7 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h8 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h9 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h10 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl rfl))))))))))
  have h11 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl rfl)))))))))))
  have h12 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl rfl))))))))))))
  have h13 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))
  have h14 := R _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))))))
  simp only [map_mul, map_inv, map_pow, mk_of] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  change (aV * bV⁻¹) * XV1 2 * (aV * bV⁻¹)⁻¹ * (XV1 2)⁻¹ = 1 at h1
  change (aV * bV⁻¹) * XV1 3 * (aV * bV⁻¹)⁻¹ * (XV1 3)⁻¹ = 1 at h2
  change bV * CV1 2 * (CV1 1)⁻¹ = 1 at h3
  change bV * CV1 3 * (CV1 2 * XV1 2)⁻¹ = 1 at h4
  change CV1 2 ^ 2 * (CV1 1 * aV)⁻¹ = 1 at h5
  change CV1 1 ^ 3 = 1 at h6
  change piV1 1 ^ 2 = 1 at h7
  change piV1 3 * piV1 1 * (piV1 1 * piV1 3)⁻¹ = 1 at h8
  change (piV1 2 * piV1 1) ^ 3 = 1 at h9
  change piV1 1 * XV1 3 * (XV1 3 * piV1 1)⁻¹ = 1 at h10
  change bV * piV1 2 * piV1 1 * (piV1 1 * XV1 2)⁻¹ = 1 at h11
  change bV * piV1 3 * (piV1 2 * bV)⁻¹ = 1 at h12
  change CV1 3 * piV1 2 * (piV1 1 * CV1 3)⁻¹ = 1 at h13
  change (piV1 1 * CV1 2) ^ 3 = 1 at h14
  refine ⟨h1, h2, (mul_inv_eq_one.1 h3).symm, (mul_inv_eq_one.1 h4).symm,
    (mul_inv_eq_one.1 h5).symm, h6, h7, (mul_inv_eq_one.1 h8).symm, h9, (mul_inv_eq_one.1 h10).symm,
    (mul_inv_eq_one.1 h11).symm, (mul_inv_eq_one.1 h12).symm, (mul_inv_eq_one.1 h13).symm, h14⟩

/-- The map `T₁ → V₁`, `A, B, C ↦ A, B, C`. -/
noncomputable def fromT1 : T1 →* V1 :=
  PresentedGroup.toGroup (f := fun s => match s with
    | FormalABC.A => aV | FormalABC.B => bV | FormalABC.C => cV) (by
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := relV1
    simp only [XV1_succ, CV1_succ, pow_one, pow_zero, inv_one, one_mul, mul_one] at h1 h2 h3 h4 h5 h6
    intro r hr
    simp only [relsT1, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
    · exact h1
    · rw [inv_pow]; exact h2
    · calc _ = cV⁻¹ * (bV * (aV⁻¹ * cV * bV)) := by group
        _ = 1 := by rw [← h3]; group
    · calc _ = ((aV⁻¹ * cV * bV) * (aV⁻¹ * bV * aV))⁻¹ * (bV * ((aV ^ 2)⁻¹ * cV * bV ^ 2)) := by
            rw [inv_pow]; group
        _ = 1 := by rw [← h4]; group
    · calc _ = (cV * aV)⁻¹ * (aV⁻¹ * cV * bV) ^ 2 := rfl
        _ = 1 := by rw [h5]; group
    · exact h6)

@[simp] lemma fromT1_A : fromT1 (PresentedGroup.of FormalABC.A) = aV := PresentedGroup.toGroup.of _
@[simp] lemma fromT1_B : fromT1 (PresentedGroup.of FormalABC.B) = bV := PresentedGroup.toGroup.of _
@[simp] lemma fromT1_C : fromT1 (PresentedGroup.of FormalABC.C) = cV := PresentedGroup.toGroup.of _

lemma fromT1_XT1 (n : ℕ) : fromT1 (XT1 n) = XV1 n := by
  cases n
  · rfl
  · simp [XT1, XV1_succ, map_mul, map_inv, map_pow]

lemma fromT1_CT1 (n : ℕ) : fromT1 (CT1 n) = CV1 n := by
  cases n
  · simp [CT1, CV1_zero]
  · simp [CT1, CV1_succ, map_mul, map_inv, map_pow]

/-- Lemma 5.5 in `V₁`. -/
lemma CV1_succ_relations (k n : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    CV1 n = XV1 n * CV1 (n + 1) ∧ CV1 n * XV1 k = XV1 (k - 1) * CV1 (n + 1) ∧
      CV1 n * aV = CV1 (n + 1) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := CT1_succ_relations k n hk hkn
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg fromT1 h1; simpa [map_mul, fromT1_XT1, fromT1_CT1] using this
  · have := congrArg fromT1 h2; simpa [map_mul, fromT1_XT1, fromT1_CT1] using this
  · have := congrArg fromT1 h3; simpa [map_mul, map_pow, fromT1_CT1] using this

/-- Lemma 5.6 in `V₁`. -/
lemma CV1_pow_relations (n m r s : ℕ) (hn : 0 < n) (hm : 1 ≤ m) (hmn : m ≤ n + 1)
    (hr : r ≤ n) (hs : s ≤ n) :
    (m ≤ r → CV1 n ^ m * XV1 r = XV1 (r - m) * CV1 (n + 1) ^ m) ∧
      (r + 1 = m → CV1 n ^ m * XV1 r = CV1 (n + 1) ^ (m + 1)) ∧
      (r + 1 < m → CV1 n ^ m * XV1 r = XV1 (r + (n + 2 - m)) * CV1 (n + 1) ^ (m + 1)) ∧
      (n + 2 ≤ s + m →
        (XV1 s)⁻¹ * CV1 n ^ m = CV1 (n + 1) ^ (m + 1) * (XV1 (s + m - (n + 2)))⁻¹) ∧
      (s + m = n + 1 → (XV1 s)⁻¹ * CV1 n ^ m = CV1 (n + 1) ^ m) ∧
      (s + m ≤ n → (XV1 s)⁻¹ * CV1 n ^ m = CV1 (n + 1) ^ m * (XV1 (s + m))⁻¹) ∧
      CV1 n ^ m = XV1 (n + 1 - m) * CV1 (n + 1) ^ m ∧
      CV1 n ^ m = CV1 (n + 1) ^ (m + 1) * (XV1 (m - 1))⁻¹ ∧
      CV1 n ^ (n + 2) = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := CT1_pow_relations n m r s hn hm hmn hr hs
  have T : ∀ {x y : T1}, x = y → fromT1 x = fromT1 y := fun h => congrArg _ h
  simp only [← fromT1_XT1, ← fromT1_CT1, ← map_pow, ← map_mul, ← map_inv]
  exact ⟨fun h => T (h1 h), fun h => T (h2 h), fun h => T (h3 h), fun h => T (h4 h),
    fun h => T (h5 h), fun h => T (h6 h), T h7, T h8, by rw [h9, map_one]⟩

/-- p. 236 in `V₁`: `XₙXₖ = XₖXₙ₊₁` for `k < n`. -/
lemma XV1_mul_XV1 (k n : ℕ) (hkn : k < n) : XV1 n * XV1 k = XV1 k * XV1 (n + 1) := by
  have := congrArg fromT1 (XT1_mul_XT1 k n hkn)
  simpa [map_mul, fromT1_XT1] using this

lemma conj_XV1 (m : ℕ) : aV⁻¹ * XV1 (m + 1) * aV = XV1 (m + 2) := by
  simp only [XV1_succ]; group

lemma conj_piV1 (m : ℕ) : aV⁻¹ * piV1 (m + 1) * aV = piV1 (m + 2) := by
  simp only [piV1_succ]; group

lemma conj_CV1 (m : ℕ) : aV⁻¹ * CV1 (m + 1) * bV = CV1 (m + 2) := by
  simp only [CV1_succ]; group

lemma conjpow_XV1 (m k : ℕ) : (aV ^ k)⁻¹ * XV1 (m + 1) * aV ^ k = XV1 (m + 1 + k) := by
  simp only [XV1_succ]; rw [show m + 1 + k = (m + k) + 1 by omega, XV1_succ]; group

lemma conjpow_piV1 (m k : ℕ) : (aV ^ k)⁻¹ * piV1 (m + 1) * aV ^ k = piV1 (m + 1 + k) := by
  simp only [piV1_succ]; rw [show m + 1 + k = (m + k) + 1 by omega, piV1_succ]; group

end CannonFloydParry.S6

/-! Lemma 6.2 (CFP pp. 243–244), with `Commute` doing the bookkeeping. -/

namespace CannonFloydParry.S6

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)

/-- Conjugating a commuting pair. -/
lemma comm_conj {u x : V1} (h : Commute u x) (w : V1) : Commute (w * u * w⁻¹) (w * x * w⁻¹) := by
  simpa [MulAut.conj_apply] using h.map (MulAut.conj w)

lemma commute_of_comm_eq_one {u x : V1} (h : u * x * u⁻¹ * x⁻¹ = 1) : Commute u x := by
  have := mul_inv_eq_one.1 h
  exact mul_inv_eq_iff_eq_mul.1 this

lemma XV1_one : XV1 1 = bV := by simp [XV1_succ]

lemma XV1_eq_conj (n : ℕ) : XV1 (n + 1) = (aV ^ n)⁻¹ * bV * aV ^ n := XV1_succ n

lemma piV1_eq_conj (m k : ℕ) : piV1 (m + 1 + k) = (aV ^ k)⁻¹ * piV1 (m + 1) * aV ^ k :=
  (conjpow_piV1 m k).symm

lemma XV1_eq_conjpow (m k : ℕ) : XV1 (m + 1 + k) = (aV ^ k)⁻¹ * XV1 (m + 1) * aV ^ k :=
  (conjpow_XV1 m k).symm

/-- `AB⁻¹` commutes with `Xₙ` for `n ≥ 2`. -/
lemma u_comm_XV1 : ∀ n, 2 ≤ n → Commute (aV * bV⁻¹) (XV1 n) := by
  obtain ⟨h1, h2, -⟩ := relV1
  have c2 := commute_of_comm_eq_one h1
  have c3 := commute_of_comm_eq_one h2
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases (show n + 1 = 2 ∨ n + 1 = 3 ∨ 3 ≤ n by omega) with h | h | h
    · rw [h]; exact c2
    · rw [h]; exact c3
    · have e : XV1 (n + 1) = (XV1 2)⁻¹ * XV1 n * XV1 2 := by
        rw [mul_assoc, XV1_mul_XV1 2 n (by omega)]; group
      rw [e]
      exact (c2.inv_right.mul_right (ih (by omega))).mul_right c2

/-- `AB⁻¹` commutes with `πₙ` for `n ≥ 2`. -/
lemma u_comm_piV1 : ∀ n, 2 ≤ n → Commute (aV * bV⁻¹) (piV1 n) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, h12, -, -⟩ := relV1
  have c2 : Commute (aV * bV⁻¹) (piV1 2) := by
    have e1 : aV⁻¹ * piV1 2 * aV = piV1 3 := conj_piV1 1
    have e2 : bV⁻¹ * piV1 2 * bV = piV1 3 := by
      calc bV⁻¹ * piV1 2 * bV = bV⁻¹ * (piV1 2 * bV) := by group
        _ = bV⁻¹ * (bV * piV1 3) := by rw [h12]
        _ = _ := by group
    -- A⁻¹π₂A = B⁻¹π₂B, so π₂ commutes with BA⁻¹, hence with AB⁻¹
    have key : (bV * aV⁻¹) * piV1 2 * (bV * aV⁻¹)⁻¹ = piV1 2 := by
      calc (bV * aV⁻¹) * piV1 2 * (bV * aV⁻¹)⁻¹ = bV * (aV⁻¹ * piV1 2 * aV) * bV⁻¹ := by group
        _ = bV * (bV⁻¹ * piV1 2 * bV) * bV⁻¹ := by rw [e1, e2]
        _ = _ := by group
    have hc : Commute (bV * aV⁻¹) (piV1 2) := mul_inv_eq_iff_eq_mul.1 key
    have : aV * bV⁻¹ = (bV * aV⁻¹)⁻¹ := by group
    rw [this]; exact hc.inv_left
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases (show n + 1 = 2 ∨ 2 ≤ n by omega) with h | h
    · rw [h]; exact c2
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      set u := aV * bV⁻¹
      set w := aV ^ m
      -- conjugating by w takes π_{m+1}, X_{m+1}, X_{m+2} to π₁, B, X₂
      have eπ : piV1 (m + 1) = w⁻¹ * piV1 1 * w := by
        have := piV1_eq_conj 0 m; rwa [show 0 + 1 + m = m + 1 by omega] at this
      have eX1 : XV1 (m + 1) = w⁻¹ * bV * w := XV1_eq_conj m
      have eX2 : XV1 (m + 2) = w⁻¹ * XV1 2 * w := by
        have := XV1_eq_conjpow 1 m; rw [show 1 + 1 + m = m + 2 by omega] at this; exact this
      have eπ2 : piV1 (m + 2) = w⁻¹ * piV1 2 * w := by
        have := piV1_eq_conj 1 m; rw [show 1 + 1 + m = m + 2 by omega] at this; exact this
      have back : ∀ x : V1, w * (w⁻¹ * x * w) * w⁻¹ = x := fun x => by group
      have k1 : Commute (w * u * w⁻¹) (piV1 1) := by
        have := comm_conj (ih (by omega)) w; rwa [eπ, back] at this
      have kB : Commute (w * u * w⁻¹) bV := by
        have := comm_conj (u_comm_XV1 (m + 1) (by omega)) w; rwa [eX1, back] at this
      have kX2 : Commute (w * u * w⁻¹) (XV1 2) := by
        have := comm_conj (u_comm_XV1 (m + 2) (by omega)) w; rwa [eX2, back] at this
      have e11 : piV1 2 = bV⁻¹ * piV1 1 * XV1 2 * (piV1 1)⁻¹ := by
        calc piV1 2 = bV⁻¹ * (bV * piV1 2 * piV1 1) * (piV1 1)⁻¹ := by group
          _ = _ := by rw [← h11]; group
      have k2 : Commute (w * u * w⁻¹) (piV1 2) := by
        rw [e11]; exact ((kB.inv_right.mul_right k1).mul_right kX2).mul_right k1.inv_right
      have := comm_conj k2 w⁻¹
      rw [show w⁻¹ * (w * u * w⁻¹) * w⁻¹⁻¹ = u by group, inv_inv, ← eπ2] at this
      exact this

/-- Lemma 6.2 i). -/
lemma l62_i : ∀ i j : ℕ, 0 < i → j < i → piV1 i * XV1 j = XV1 j * piV1 (i + 1) := by
  have one : ∀ i, 1 < i → piV1 i * bV = bV * piV1 (i + 1) := by
    intro i hi
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hu : (aV * bV⁻¹) * piV1 (m + 1) * (aV * bV⁻¹)⁻¹ = piV1 (m + 1) :=
      mul_inv_eq_of_eq_mul (u_comm_piV1 (m + 1) hi).eq
    have hA : aV⁻¹ * piV1 (m + 1) * aV = piV1 (m + 2) := conj_piV1 m
    have hB : bV⁻¹ * piV1 (m + 1) * bV = piV1 (m + 2) := by
      rw [← hA]
      calc bV⁻¹ * piV1 (m + 1) * bV
          = aV⁻¹ * ((aV * bV⁻¹) * piV1 (m + 1) * (aV * bV⁻¹)⁻¹) * aV := by group
        _ = _ := by rw [hu]
    calc piV1 (m + 1) * bV = bV * (bV⁻¹ * piV1 (m + 1) * bV) := by group
      _ = bV * piV1 (m + 2) := by rw [hB]
  intro i j hi hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    rw [XV1_zero, ← conj_piV1 m]; group
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, i = m + k + 2 := ⟨i - k - 2, by omega⟩
    have h := one (m + 2) (by omega)
    have e1 : piV1 (m + k + 2) = (aV ^ k)⁻¹ * piV1 (m + 2) * aV ^ k := by
      have := piV1_eq_conj (m + 1) k; rwa [show m + 1 + 1 + k = m + k + 2 by omega] at this
    have e2 : piV1 (m + k + 2 + 1) = (aV ^ k)⁻¹ * piV1 (m + 2 + 1) * aV ^ k := by
      have := piV1_eq_conj (m + 2) k; rwa [show m + 2 + 1 + k = m + k + 2 + 1 by omega] at this
    rw [e1, e2, XV1_eq_conj k]
    calc (aV ^ k)⁻¹ * piV1 (m + 2) * aV ^ k * ((aV ^ k)⁻¹ * bV * aV ^ k)
        = (aV ^ k)⁻¹ * (piV1 (m + 2) * bV) * aV ^ k := by group
      _ = (aV ^ k)⁻¹ * (bV * piV1 (m + 2 + 1)) * aV ^ k := by rw [h]
      _ = _ := by group

/-- `π₁` commutes with `X_j` for `j ≥ 3`. -/
lemma pi1_comm_XV1 : ∀ j, 3 ≤ j → Commute (piV1 1) (XV1 j) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, h11, -, -, -⟩ := relV1
  have c3 : Commute (piV1 1) (XV1 3) := h10.symm
  have c24 : Commute (piV1 2) (XV1 4) := by
    have := comm_conj c3 aV⁻¹
    rwa [inv_inv, conj_piV1 0, show XV1 3 = XV1 (2 + 1) from rfl, conj_XV1 2] at this
  have x324 : XV1 3 * XV1 2 = XV1 2 * XV1 4 := XV1_mul_XV1 2 3 (by omega)
  have x31 : XV1 3 * bV = bV * XV1 4 := by
    have := XV1_mul_XV1 1 3 (by omega); rwa [XV1_one] at this
  have c4 : Commute (piV1 1) (XV1 4) := by
    have key : bV * piV1 2 * (piV1 1 * XV1 4) = bV * piV1 2 * (XV1 4 * piV1 1) := by
      calc bV * piV1 2 * (piV1 1 * XV1 4) = (bV * piV1 2 * piV1 1) * XV1 4 := by group
        _ = piV1 1 * XV1 2 * XV1 4 := by rw [← h11]
        _ = piV1 1 * (XV1 3 * XV1 2) := by rw [x324]; group
        _ = XV1 3 * (piV1 1 * XV1 2) := by rw [← mul_assoc, c3.eq]; group
        _ = XV1 3 * bV * piV1 2 * piV1 1 := by rw [h11]; group
        _ = bV * (XV1 4 * piV1 2) * piV1 1 := by rw [x31]; group
        _ = bV * (piV1 2 * XV1 4) * piV1 1 := by rw [c24.eq]
        _ = _ := by group
    exact mul_left_cancel key
  intro j hj
  induction j with
  | zero => omega
  | succ n ih =>
    rcases (show n + 1 = 3 ∨ n + 1 = 4 ∨ 4 ≤ n by omega) with h | h | h
    · rw [h]; exact c3
    · rw [h]; exact c4
    · have ihn := ih (by omega)
      have e : XV1 3 * XV1 (n + 1) = XV1 n * XV1 3 := (XV1_mul_XV1 3 n (by omega)).symm
      have key : XV1 3 * (piV1 1 * XV1 (n + 1)) = XV1 3 * (XV1 (n + 1) * piV1 1) := by
        calc XV1 3 * (piV1 1 * XV1 (n + 1)) = (XV1 3 * piV1 1) * XV1 (n + 1) := by group
          _ = piV1 1 * (XV1 3 * XV1 (n + 1)) := by rw [← c3.eq]; group
          _ = piV1 1 * (XV1 n * XV1 3) := by rw [e]
          _ = (piV1 1 * XV1 n) * XV1 3 := by group
          _ = XV1 n * (piV1 1 * XV1 3) := by rw [ihn.eq]; group
          _ = XV1 n * XV1 3 * piV1 1 := by rw [c3.eq]; group
          _ = _ := by rw [← e]; group
      exact mul_left_cancel key

/-- Lemma 6.2 ii). -/
lemma l62_ii : ∀ i j : ℕ, 0 < i → i + 2 ≤ j → piV1 i * XV1 j = XV1 j * piV1 i := by
  intro i j hi hj
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 + 1 + k := ⟨j - 3 - k, by omega⟩
  have h := comm_conj (pi1_comm_XV1 (m + 2 + 1) (by omega)) (aV ^ k)⁻¹
  rw [inv_inv, ← XV1_eq_conjpow (m + 2) k] at h
  have e1 : (aV ^ k)⁻¹ * piV1 1 * aV ^ k = piV1 (k + 1) := by
    have := piV1_eq_conj 0 k; rw [show 0 + 1 + k = k + 1 by omega] at this; exact this.symm
  rw [e1] at h
  exact h.eq

end CannonFloydParry.S6

/-! Lemma 6.2 iii) (CFP p. 244) and the assembled Lemma 6.2. -/

namespace CannonFloydParry.S6

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)
local notation "cV" => (PresentedGroup.of FormalV.C : V1)

lemma CV1_eq_XV1_mul (n : ℕ) (hn : 0 < n) : CV1 n = XV1 n * CV1 (n + 1) :=
  (CV1_succ_relations 1 n (by omega) hn).1

lemma CV1_mul_A (n : ℕ) (hn : 0 < n) : CV1 n * aV = CV1 (n + 1) ^ 2 :=
  (CV1_succ_relations 1 n (by omega) hn).2.2

/-- `C_i π₂ = π₁ C_i` for `i ≥ 3`. -/
lemma CV1_pi2 : ∀ i, 3 ≤ i → CV1 i * piV1 2 = piV1 1 * CV1 i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, -⟩ := relV1
  intro i hi
  induction i with
  | zero => omega
  | succ n ih =>
    rcases (show n + 1 = 3 ∨ 3 ≤ n by omega) with h | h
    · rw [h]; exact h13.symm
    · have e := CV1_eq_XV1_mul n (by omega)
      have c := (pi1_comm_XV1 n h).eq
      have key : XV1 n * (CV1 (n + 1) * piV1 2) = XV1 n * (piV1 1 * CV1 (n + 1)) := by
        calc XV1 n * (CV1 (n + 1) * piV1 2) = CV1 n * piV1 2 := by rw [e]; group
          _ = piV1 1 * CV1 n := ih h
          _ = (piV1 1 * XV1 n) * CV1 (n + 1) := by rw [e]; group
          _ = _ := by rw [c]; group
      exact mul_left_cancel key

/-- `C_i π_j = π_{j-1} C_i` for `1 < j < i`. -/
lemma CV1_pi_ge2 : ∀ j i, 1 < j → j < i → CV1 i * piV1 j = piV1 (j - 1) * CV1 i := by
  intro j
  induction j with
  | zero => intro i h; omega
  | succ j ih =>
    intro i hj hji
    rcases (show j + 1 = 2 ∨ 2 ≤ j by omega) with h | h
    · rw [h]; exact CV1_pi2 i (by omega)
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hC : CV1 (k + 2) = aV⁻¹ * CV1 (k + 1) * bV := (conj_CV1 k).symm
      have hB : piV1 j * bV = bV * piV1 (j + 1) := by
        have := l62_i j 1 (by omega) (by omega); rwa [XV1_one] at this
      have hIH := ih (k + 1) (by omega) (by omega)
      have hA : aV⁻¹ * piV1 (j - 1) * aV = piV1 j := by
        obtain ⟨t, rfl⟩ : ∃ t, j = t + 2 := ⟨j - 2, by omega⟩
        exact conj_piV1 t
      show CV1 (k + 1 + 1) * piV1 (j + 1) = piV1 (j + 1 - 1) * CV1 (k + 1 + 1)
      rw [show j + 1 - 1 = j by omega, hC]
      calc aV⁻¹ * CV1 (k + 1) * bV * piV1 (j + 1)
          = aV⁻¹ * CV1 (k + 1) * (bV * piV1 (j + 1)) := by group
        _ = aV⁻¹ * CV1 (k + 1) * (piV1 j * bV) := by rw [hB]
        _ = aV⁻¹ * (CV1 (k + 1) * piV1 j) * bV := by group
        _ = aV⁻¹ * (piV1 (j - 1) * CV1 (k + 1)) * bV := by rw [hIH]
        _ = (aV⁻¹ * piV1 (j - 1) * aV) * (aV⁻¹ * CV1 (k + 1) * bV) := by group
        _ = _ := by rw [hA]

/-- `C_i π₁ = π₀ C_i` for `i > 1`. -/
lemma CV1_pi1 : ∀ i, 1 < i → CV1 i * piV1 1 = piV1 0 * CV1 i := by
  intro i hi
  induction i with
  | zero => omega
  | succ n ih =>
    rcases (show n + 1 = 2 ∨ 2 ≤ n by omega) with h | h
    · rw [h]
      have e : piV1 1 = (CV1 2)⁻¹ * piV1 0 * CV1 2 := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, piV1_succ]; simp [piV1_zero]
      rw [e]; group
    · have hA := CV1_mul_A n (by omega)
      have h12 : aV⁻¹ * piV1 1 * aV = piV1 2 := conj_piV1 0
      have h2 := CV1_pi2 (n + 1) (by omega)
      have key : (CV1 (n + 1) * piV1 1) * CV1 (n + 1) = (piV1 0 * CV1 (n + 1)) * CV1 (n + 1) := by
        calc (CV1 (n + 1) * piV1 1) * CV1 (n + 1) = CV1 (n + 1) * (piV1 1 * CV1 (n + 1)) := by group
          _ = CV1 (n + 1) * (CV1 (n + 1) * piV1 2) := by rw [h2]
          _ = CV1 (n + 1) ^ 2 * piV1 2 := by rw [sq]; group
          _ = CV1 n * aV * (aV⁻¹ * piV1 1 * aV) := by rw [← hA, h12]
          _ = (CV1 n * piV1 1) * aV := by group
          _ = piV1 0 * (CV1 n * aV) := by rw [ih (by omega)]; group
          _ = _ := by rw [hA, sq]; group
      exact mul_right_cancel key

/-- Lemma 6.2 iii). -/
lemma l62_iii (i j : ℕ) (hj : 0 < j) (hji : j < i) : CV1 i * piV1 j = piV1 (j - 1) * CV1 i := by
  rcases (show j = 1 ∨ 1 < j by omega) with rfl | h
  · exact CV1_pi1 i hji
  · exact CV1_pi_ge2 j i h hji


end CannonFloydParry.S6

/-! Lemma 6.3 (CFP pp. 244–245). -/

namespace CannonFloydParry.S6

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)

lemma piV1_succ_conj (k : ℕ) : piV1 (k + 1) = (aV ^ k)⁻¹ * piV1 1 * aV ^ k := by
  have := piV1_eq_conj 0 k; rwa [show 0 + 1 + k = k + 1 by omega] at this

lemma piV1_zero_conj : piV1 0 = CV1 2 * piV1 1 * (CV1 2)⁻¹ := by
  rw [CV1_pi1 2 (by omega)]; group

lemma conj_pow' (w x : V1) (n : ℕ) : (w * x * w⁻¹) ^ n = w * x ^ n * w⁻¹ := by
  simpa [MulAut.conj_apply] using (map_pow (MulAut.conj w) x n).symm

/-- Lemma 6.3 i). -/
lemma l63_i (i : ℕ) : piV1 i ^ 2 = 1 := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := relV1
  rcases i with _ | k
  · rw [piV1_zero_conj, conj_pow', h7]; group
  · have := conj_pow' (aV ^ k)⁻¹ (piV1 1) 2
    rw [inv_inv, h7] at this
    rw [piV1_succ_conj, this]; group


end CannonFloydParry.S6

/-! Lemma 6.4 (CFP p. 245). -/

namespace CannonFloydParry.S6

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)

lemma piV1_inv (i : ℕ) : (piV1 i)⁻¹ = piV1 i := by
  rw [inv_eq_iff_mul_eq_one, ← sq, l63_i]

/-- Lemma 5.5 ii) in `V₁`: `C_n X_k = X_{k-1} C_{n+1}` for `0 < k ≤ n`. -/
lemma CV1_XV1 (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) : CV1 n * XV1 k = XV1 (k - 1) * CV1 (n + 1) :=
  (CV1_succ_relations k n hk hkn).2.1

/-- Lemma 6.4 i). -/
lemma l64_i (i j : ℕ) (hj : i + 2 ≤ j) : piV1 i * XV1 j = XV1 j * piV1 i := by
  rcases i with _ | k
  · -- `π₀ X_j C_{j+2} = X_j π₀ C_{j+2}`
    set n := j + 1
    have e1 : XV1 j * CV1 (n + 1) = CV1 n * XV1 (j + 1) := by
      rw [CV1_XV1 n (j + 1) (by omega) (by omega)]; rfl
    have e2 : piV1 0 * CV1 n = CV1 n * piV1 1 := (CV1_pi1 n (by omega)).symm
    have e3 : piV1 1 * XV1 (j + 1) = XV1 (j + 1) * piV1 1 := (pi1_comm_XV1 (j + 1) (by omega)).eq
    have e4 : CV1 (n + 1) * piV1 1 = piV1 0 * CV1 (n + 1) := CV1_pi1 (n + 1) (by omega)
    have key : piV1 0 * XV1 j * CV1 (n + 1) = XV1 j * piV1 0 * CV1 (n + 1) := by
      calc piV1 0 * XV1 j * CV1 (n + 1) = piV1 0 * (XV1 j * CV1 (n + 1)) := by group
        _ = (piV1 0 * CV1 n) * XV1 (j + 1) := by rw [e1]; group
        _ = CV1 n * (piV1 1 * XV1 (j + 1)) := by rw [e2]; group
        _ = (CV1 n * XV1 (j + 1)) * piV1 1 := by rw [e3]; group
        _ = XV1 j * (CV1 (n + 1) * piV1 1) := by rw [← e1]; group
        _ = _ := by rw [e4]; group
    exact mul_right_cancel key
  · exact l62_ii (k + 1) j (by omega) hj

/-- Lemma 6.4 ii). -/
lemma l64_ii (i : ℕ) : piV1 i * XV1 (i + 1) = XV1 i * piV1 (i + 1) * piV1 i := by
  obtain ⟨-, -, -, h4, -, -, -, -, -, -, h11, -⟩ := relV1
  rcases i with _ | k
  · -- `π₀ B C₃ = A π₁ π₀ C₃`
    have e1 : bV * CV1 3 = CV1 2 * XV1 2 := h4.symm
    have e2 : piV1 0 * CV1 2 = CV1 2 * piV1 1 := (CV1_pi1 2 (by omega)).symm
    have e3 : CV1 2 * bV = aV * CV1 3 := by
      have := CV1_XV1 2 1 (by omega) (by omega); rwa [XV1_one] at this
    have e4 : CV1 3 * piV1 2 = piV1 1 * CV1 3 := CV1_pi2 3 le_rfl
    have e5 : CV1 3 * piV1 1 = piV1 0 * CV1 3 := CV1_pi1 3 (by omega)
    have key : piV1 0 * bV * CV1 3 = aV * piV1 1 * piV1 0 * CV1 3 := by
      calc piV1 0 * bV * CV1 3 = piV1 0 * (bV * CV1 3) := by group
        _ = (piV1 0 * CV1 2) * XV1 2 := by rw [e1]; group
        _ = CV1 2 * (piV1 1 * XV1 2) := by rw [e2]; group
        _ = (CV1 2 * bV) * piV1 2 * piV1 1 := by rw [h11]; group
        _ = aV * (CV1 3 * piV1 2) * piV1 1 := by rw [e3]; group
        _ = aV * piV1 1 * (CV1 3 * piV1 1) := by rw [e4]; group
        _ = _ := by rw [e5]; group
    have := mul_right_cancel key
    rw [XV1_zero, XV1_one]; exact this
  · -- conjugate relator 11 by `A^k`
    have r : piV1 1 * XV1 2 = XV1 1 * piV1 2 * piV1 1 := by rw [XV1_one]; exact h11
    have h := congrArg (fun x => (aV ^ k)⁻¹ * x * aV ^ k) r
    have c : ∀ x y : V1, (aV ^ k)⁻¹ * (x * y) * aV ^ k =
        ((aV ^ k)⁻¹ * x * aV ^ k) * ((aV ^ k)⁻¹ * y * aV ^ k) := fun x y => by group
    rw [c, c, c, conjpow_piV1 0 k, conjpow_XV1 1 k, conjpow_XV1 0 k, conjpow_piV1 1 k] at h
    rw [show k + 1 + 1 = 1 + 1 + k by omega, show k + 1 = 0 + 1 + k by omega]
    exact h

/-- Lemma 6.4 iii). -/
lemma l64_iii (i : ℕ) : piV1 i * XV1 i = XV1 (i + 1) * piV1 i * piV1 (i + 1) := by
  have h := l64_ii i
  have hi := l63_i i
  have hi1 := l63_i (i + 1)
  rw [sq] at hi hi1
  calc piV1 i * XV1 i = piV1 i * (XV1 i * piV1 (i + 1) * piV1 i) * piV1 i * piV1 (i + 1) := by
        rw [show piV1 i * (XV1 i * piV1 (i + 1) * piV1 i) * piV1 i * piV1 (i + 1)
          = piV1 i * XV1 i * piV1 (i + 1) * (piV1 i * piV1 i) * piV1 (i + 1) by group, hi,
          mul_one, mul_assoc, hi1, mul_one]
    _ = piV1 i * (piV1 i * XV1 (i + 1)) * piV1 i * piV1 (i + 1) := by rw [h]
    _ = (piV1 i * piV1 i) * XV1 (i + 1) * piV1 i * piV1 (i + 1) := by group
    _ = _ := by rw [hi, one_mul]


end CannonFloydParry.S6

/-! Lemma 6.5 (CFP pp. 245–246). -/

namespace CannonFloydParry.S6

/-- `π₀ π₁ ⋯ π_{n-1}`. -/
def PP (n : ℕ) : V1 := ((List.range n).map piV1).prod
/-- `π_{n-1} ⋯ π₁ π₀`. -/
def RR (n : ℕ) : V1 := ((List.range n).reverse.map piV1).prod

lemma PP_succ (n : ℕ) : PP (n + 1) = PP n * piV1 n := by
  simp [PP, List.range_succ]

lemma RR_succ (n : ℕ) : RR (n + 1) = piV1 n * RR n := by
  simp [RR, List.range_succ]

lemma RR_eq_inv (n : ℕ) : RR n = (PP n)⁻¹ := by
  induction n with
  | zero => simp [RR, PP]
  | succ n ih => rw [RR_succ, PP_succ, ih, mul_inv_rev, piV1_inv]

lemma CV1_pow_four_two : CV1 2 ^ (2 + 2) = 1 :=
  (CV1_pow_relations 2 1 0 0 (by omega) le_rfl (by omega) (by omega) (by omega)).2.2.2.2.2.2.2.2

/-- Shifting `C_n` through a product of `π`s with indices in `(0, n)`. -/
lemma CV1_shift (n : ℕ) : ∀ L : List ℕ, (∀ x ∈ L, 0 < x ∧ x < n) →
    CV1 n * (L.map piV1).prod = ((L.map (· - 1)).map piV1).prod * CV1 n := by
  intro L
  induction L with
  | nil => intro; simp
  | cons x L ih =>
    intro h
    have hx := h x (by simp)
    have hL := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, l62_iii n x hx.1 hx.2, mul_assoc, hL, mul_assoc]

/-- `RR (m+1) = (π_m ⋯ π₁) π₀`, with the first factor shifted. -/
lemma RR_succ' (m : ℕ) :
    RR (m + 1) = ((((List.range m).map Nat.succ).reverse).map piV1).prod * piV1 0 := by
  simp [RR, List.range_succ_eq_map, List.map_reverse]

lemma shift_back (m : ℕ) :
    (((List.range m).map Nat.succ).reverse.map (· - 1)) = (List.range m).reverse := by
  rw [List.map_reverse, List.map_map]; simp [Function.comp_def]

/-- Lemma 6.5 ii). -/
lemma l65_ii : ∀ m, CV1 (m + 2) * piV1 0 = PP (m + 2) * CV1 (m + 2) ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h14⟩ := relV1
  intro m
  induction m with
  | zero =>
    set c := CV1 2
    set p := piV1 1
    have hp : p * p = 1 := by rw [← sq]; exact l63_i 1
    have hpi : p⁻¹ = p := piV1_inv 1
    have h4 : c ^ 4 = 1 := CV1_pow_four_two
    have h1 : c * p * c = p * c⁻¹ * p := by
      have e : c * p * c = p⁻¹ * (p * c) ^ 3 * c⁻¹ * p⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul]; group
      rw [e, h14, hpi]; group
    have hc2 : c⁻¹ * c⁻¹ = c ^ 2 := by
      calc c⁻¹ * c⁻¹ = c⁻¹ * c⁻¹ * c ^ 4 := by rw [h4, mul_one]
        _ = c ^ 2 := by group
    have e0 : piV1 0 = c * p * c⁻¹ := piV1_zero_conj
    have eP : PP 2 = piV1 0 * p := by simp [PP, List.range_succ]; rfl
    rw [eP, e0]
    calc c * (c * p * c⁻¹) = c * (c * p * c) * c⁻¹ * c⁻¹ := by group
      _ = c * (p * c⁻¹ * p) * c⁻¹ * c⁻¹ := by rw [h1]
      _ = c * p * c⁻¹ * p * (c⁻¹ * c⁻¹) := by group
      _ = _ := by rw [hc2]
  | succ m ih =>
    -- `n = m + 2`
    have eC : CV1 (m + 2) = XV1 (m + 2) * CV1 (m + 3) := CV1_eq_XV1_mul (m + 2) (by omega)
    have e55 : CV1 (m + 2) * XV1 (m + 2) = XV1 (m + 1) * CV1 (m + 3) :=
      CV1_XV1 (m + 2) (m + 2) (by omega) le_rfl
    have e64 : piV1 (m + 1) * XV1 (m + 1) = XV1 (m + 2) * piV1 (m + 1) * piV1 (m + 2) :=
      l64_iii (m + 1)
    have hcomm : Commute (XV1 (m + 2)) (PP (m + 1)) := by
      apply Commute.list_prod_right
      intro y hy
      simp only [List.mem_map, List.mem_range] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      exact (l64_i i (m + 2) (by omega)).symm
    have key : XV1 (m + 2) * (CV1 (m + 3) * piV1 0) =
        XV1 (m + 2) * (PP (m + 3) * CV1 (m + 3) ^ 2) := by
      calc XV1 (m + 2) * (CV1 (m + 3) * piV1 0) = CV1 (m + 2) * piV1 0 := by rw [eC]; group
        _ = PP (m + 1) * piV1 (m + 1) * CV1 (m + 2) * CV1 (m + 2) := by
            rw [ih, PP_succ, sq]; group
        _ = PP (m + 1) * piV1 (m + 1) * (CV1 (m + 2) * XV1 (m + 2)) * CV1 (m + 3) := by
            rw [eC]; group
        _ = PP (m + 1) * (piV1 (m + 1) * XV1 (m + 1)) * CV1 (m + 3) * CV1 (m + 3) := by
            rw [e55]; group
        _ = (PP (m + 1) * XV1 (m + 2)) * piV1 (m + 1) * piV1 (m + 2) * CV1 (m + 3) ^ 2 := by
            rw [e64, sq]; group
        _ = XV1 (m + 2) * (PP (m + 1) * piV1 (m + 1) * piV1 (m + 2) * CV1 (m + 3) ^ 2) := by
            rw [← hcomm.eq]; group
        _ = _ := by rw [PP_succ (m + 2), PP_succ (m + 1)]
    exact mul_left_cancel key

/-- Lemma 6.5 iii). -/
lemma l65_iii (m : ℕ) : CV1 (m + 2) ^ 2 * piV1 0 = RR (m + 2) * CV1 (m + 2) := by
  set C := CV1 (m + 2)
  have h := l65_ii m
  have h0 : piV1 0 * piV1 0 = 1 := by rw [← sq]; exact l63_i 0
  rw [RR_eq_inv]
  calc C ^ 2 * piV1 0 = (PP (m + 2))⁻¹ * (PP (m + 2) * C ^ 2) * piV1 0 := by group
    _ = (PP (m + 2))⁻¹ * (C * piV1 0) * piV1 0 := by rw [h]
    _ = (PP (m + 2))⁻¹ * C * (piV1 0 * piV1 0) := by group
    _ = _ := by rw [h0, mul_one]

/-- Lemma 6.5 iv). -/
lemma l65_iv (m : ℕ) : CV1 (m + 2) ^ 3 * piV1 0 = piV1 (m + 1) * CV1 (m + 2) ^ 3 := by
  have hs := CV1_shift (m + 2) (((List.range (m + 1)).map Nat.succ).reverse) (by
    intro x hx
    simp only [List.mem_reverse, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    omega)
  rw [shift_back] at hs
  have hR : RR (m + 2) = ((((List.range (m + 1)).map Nat.succ).reverse).map piV1).prod * piV1 0 :=
    RR_succ' (m + 1)
  have tel : RR (m + 1) * PP (m + 2) = piV1 (m + 1) := by
    rw [RR_eq_inv, PP_succ (m + 1)]; group
  calc CV1 (m + 2) ^ 3 * piV1 0 = CV1 (m + 2) * (CV1 (m + 2) ^ 2 * piV1 0) := by group
    _ = CV1 (m + 2) * RR (m + 2) * CV1 (m + 2) := by rw [l65_iii]; group
    _ = (CV1 (m + 2) * ((((List.range (m + 1)).map Nat.succ).reverse).map piV1).prod) *
          (piV1 0 * CV1 (m + 2)) := by rw [hR]; group
    _ = RR (m + 1) * CV1 (m + 2) * (piV1 0 * CV1 (m + 2)) := by rw [hs]; rfl
    _ = RR (m + 1) * (CV1 (m + 2) * piV1 0) * CV1 (m + 2) := by group
    _ = RR (m + 1) * PP (m + 2) * CV1 (m + 2) ^ 3 := by rw [l65_ii]; group
    _ = _ := by rw [tel]


end CannonFloydParry.S6

/-! Lemma 6.6 (CFP pp. 246–247). -/

namespace CannonFloydParry.S6

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)


/-- Lemma 6.6 i). -/
lemma l66_i (n : ℕ) : ∀ m k, m ≤ k → k < n → CV1 n ^ m * piV1 k = piV1 (k - m) * CV1 n ^ m := by
  intro m
  induction m with
  | zero => intro k _ _; simp
  | succ m ih =>
    intro k hmk hkn
    rw [pow_succ, mul_assoc, l62_iii n k (by omega) hkn, ← mul_assoc, ih (k - 1) (by omega) (by omega),
      show k - 1 - m = k - (m + 1) by omega]
    ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)

/-- The case `n = 1` (p. 246): `C² π₀ = π₀ C` and `C π₀ = π₀ C²`. -/
lemma l66_n1 : CV1 1 ^ 2 * piV1 0 = piV1 0 * CV1 1 ∧ CV1 1 * piV1 0 = piV1 0 * CV1 1 ^ 2 := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := relV1
  -- `C² B = C₂³`
  have e1 : CV1 1 ^ 2 * bV = CV1 2 ^ 3 := by
    have := (CV1_pow_relations 1 2 1 0 (by omega) (by omega) (by omega) le_rfl (by omega)).2.1 rfl
    rwa [XV1_one] at this
  have e2 : CV1 2 ^ 3 * piV1 0 = piV1 1 * CV1 2 ^ 3 := l65_iv 0
  have e3 : CV1 2 * piV1 0 = piV1 0 * piV1 1 * CV1 2 ^ 2 := by
    have := l65_ii 0; rwa [show PP 2 = piV1 0 * piV1 1 by simp [PP, List.range_succ]] at this
  have e4 : CV1 2 * piV1 1 = piV1 0 * CV1 2 := CV1_pi1 2 (by omega)
  have h00 : piV1 0 * piV1 0 = 1 := by rw [← sq]; exact l63_i 0
  have h11 : piV1 1 * piV1 1 = 1 := by rw [← sq]; exact l63_i 1
  -- `C² B π₀ π₁ = π₀ C₂²`
  have e5 : CV1 1 ^ 2 * bV * piV1 0 * piV1 1 = piV1 0 * CV1 2 ^ 2 := by
    calc CV1 1 ^ 2 * bV * piV1 0 * piV1 1 = (CV1 2 ^ 3 * piV1 0) * piV1 1 := by rw [e1]
      _ = (piV1 0 * piV1 0) * piV1 1 * CV1 2 ^ 2 * CV1 2 * piV1 1 := by rw [e2, h00]; ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
      _ = piV1 0 * (piV1 0 * piV1 1 * CV1 2 ^ 2) * CV1 2 * piV1 1 := by ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
      _ = piV1 0 * (CV1 2 * piV1 0) * (CV1 2 * piV1 1) := by rw [← e3]; ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
      _ = piV1 0 * CV1 2 * piV1 0 * piV1 0 * CV1 2 := by rw [e4]; ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
      _ = piV1 0 * CV1 2 * (piV1 0 * piV1 0) * CV1 2 := by ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
      _ = _ := by rw [h00]; ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
  -- `π₀ A = B π₀ π₁` (6.4 iii) and `C A = C₂²` (5.5 iii)
  have e6 : piV1 0 * aV = bV * piV1 0 * piV1 1 := by
    have := l64_iii 0; rwa [XV1_zero, XV1_one] at this
  have e7 : CV1 1 * aV = CV1 2 ^ 2 := CV1_mul_A 1 (by omega)
  have key : CV1 1 ^ 2 * piV1 0 * aV = piV1 0 * CV1 1 * aV := by
    calc CV1 1 ^ 2 * piV1 0 * aV = CV1 1 ^ 2 * (piV1 0 * aV) := by ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
      _ = CV1 1 ^ 2 * bV * piV1 0 * piV1 1 := by rw [e6]; ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
      _ = piV1 0 * (CV1 1 * aV) := by rw [e5, e7]
      _ = _ := by ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
  have i1 := mul_right_cancel key
  refine ⟨i1, ?_⟩
  calc CV1 1 * piV1 0 = CV1 1 ^ 3 * CV1 1 * piV1 0 := by rw [h6, one_mul]
    _ = CV1 1 ^ 2 * (CV1 1 ^ 2 * piV1 0) := by ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
    _ = CV1 1 ^ 2 * (piV1 0 * CV1 1) := by rw [i1]
    _ = (CV1 1 ^ 2 * piV1 0) * CV1 1 := by ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
    _ = piV1 0 * CV1 1 * CV1 1 := by rw [i1]
    _ = _ := by ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)

/-- Lemma 6.6, as stated. -/
theorem CV1_pow_mul_piV1' (k m n : ℕ) (hmn : m < n + 2) (hkn : k < n) :
    (m ≤ k → CV1 n ^ m * piV1 k = piV1 (k - m) * CV1 n ^ m) ∧
      (m = k + 1 → CV1 n ^ m * piV1 k = ((List.range n).map piV1).prod * CV1 n ^ (m + 1)) ∧
      (m = k + 2 → CV1 n ^ m * piV1 k = ((List.range n).reverse.map piV1).prod * CV1 n ^ (m - 1)) ∧
      (k + 2 < m → CV1 n ^ m * piV1 k = piV1 (k + (n + 2 - m)) * CV1 n ^ m) := by
  have base : CV1 n ^ k * piV1 k = piV1 0 * CV1 n ^ k := by
    have := l66_i n k k le_rfl hkn; rwa [Nat.sub_self] at this
  refine ⟨fun h => l66_i n m k h hkn, ?_, ?_, ?_⟩
  · rintro rfl
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn
    · obtain rfl : k = 0 := by omega
      simpa [List.range_succ] using l66_n1.2
    · obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n - 2, by omega⟩
      have := l65_ii t
      calc CV1 (t + 2) ^ (k + 1) * piV1 k = CV1 (t + 2) * (CV1 (t + 2) ^ k * piV1 k) := by
            rw [pow_succ']; ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
        _ = (CV1 (t + 2) * piV1 0) * CV1 (t + 2) ^ k := by rw [base]; ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
        _ = _ := by rw [this]; unfold PP; ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
  · rintro rfl
    rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn
    · obtain rfl : k = 0 := by omega
      simpa [List.range_succ] using l66_n1.1
    · obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n - 2, by omega⟩
      have := l65_iii t
      calc CV1 (t + 2) ^ (k + 2) * piV1 k = CV1 (t + 2) ^ 2 * (CV1 (t + 2) ^ k * piV1 k) := by
            ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
        _ = (CV1 (t + 2) ^ 2 * piV1 0) * CV1 (t + 2) ^ k := by rw [base]; ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
        _ = _ := by rw [this, show k + 2 - 1 = k + 1 by omega]; unfold RR; ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
  · intro hm
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n - 2, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, m = s + k + 3 := ⟨m - k - 3, by omega⟩
    have h4 := l65_iv t
    have hi := l66_i (t + 2) s (t + 1) (by omega) (by omega)
    calc CV1 (t + 2) ^ (s + k + 3) * piV1 k
        = CV1 (t + 2) ^ s * CV1 (t + 2) ^ 3 * (CV1 (t + 2) ^ k * piV1 k) := by ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
      _ = CV1 (t + 2) ^ s * (CV1 (t + 2) ^ 3 * piV1 0) * CV1 (t + 2) ^ k := by rw [base]; ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
      _ = (CV1 (t + 2) ^ s * piV1 (t + 1)) * CV1 (t + 2) ^ (k + 3) := by rw [h4]; ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
      _ = piV1 (t + 1 - s) * CV1 (t + 2) ^ (s + k + 3) := by rw [hi]; ((try simp only [pow_succ, pow_zero, one_mul]) <;> group)
      _ = _ := by rw [show t + 1 - s = k + (t + 2 + 2 - (s + k + 3)) by omega]

end CannonFloydParry.S6

open CannonFloydParry in
theorem solution (k m n : ℕ) (hmn : m < n + 2) (hkn : k < n) :
    (m ≤ k → CV1 n ^ m * piV1 k = piV1 (k - m) * CV1 n ^ m) ∧
      (m = k + 1 → CV1 n ^ m * piV1 k = ((List.range n).map piV1).prod * CV1 n ^ (m + 1)) ∧
      (m = k + 2 → CV1 n ^ m * piV1 k = ((List.range n).reverse.map piV1).prod * CV1 n ^ (m - 1)) ∧
      (k + 2 < m → CV1 n ^ m * piV1 k = piV1 (k + (n + 2 - m)) * CV1 n ^ m) := by
  exact S6.CV1_pow_mul_piV1' k m n hmn hkn
