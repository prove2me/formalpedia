-- Prove2me | solution 1 for CannonFloydParry.CV1_pow_mul_eq_mul_CV1_pow_and_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T11:05:31.51698+00:00
-- url     : https://prove2.me/submissions/db31d79e-5d4a-4710-9810-b98f0b21785f

import Theorems.Thm_CannonFloydParry_CV1_pow_mul_piV1
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

/-- Conjugation by `C_n` shifts indices down by one, for `0 < j < n`. -/
lemma CV1_conj_pi (n j : ℕ) (hj : 0 < j) (hjn : j < n) :
    CV1 n * piV1 j * (CV1 n)⁻¹ = piV1 (j - 1) := by
  rw [l62_iii n j hj hjn]; group

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

/-- Lemma 6.3 ii). -/
lemma l63_ii (i : ℕ) : (piV1 (i + 1) * piV1 i) ^ 3 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := relV1
  rcases i with _ | k
  · have e : piV1 1 * piV1 0 = CV1 3 * (piV1 2 * piV1 1) * (CV1 3)⁻¹ := by
      have h1 := CV1_conj_pi 3 2 (by omega) (by omega)
      have h0 := CV1_conj_pi 3 1 (by omega) (by omega)
      calc piV1 1 * piV1 0 = (CV1 3 * piV1 2 * (CV1 3)⁻¹) * (CV1 3 * piV1 1 * (CV1 3)⁻¹) := by
            rw [h1, h0]
        _ = _ := by group
    rw [e, conj_pow', h9]; group
  · have e : piV1 (k + 1 + 1) * piV1 (k + 1) =
        (aV ^ k)⁻¹ * (piV1 2 * piV1 1) * ((aV ^ k)⁻¹)⁻¹ := by
      rw [piV1_succ_conj (k + 1), piV1_succ_conj k,
        show piV1 2 = aV⁻¹ * piV1 1 * aV from (conj_piV1 0).symm]
      group
    rw [e, conj_pow', h9]; group

/-- `π₁` commutes with `π_j` for `j ≥ 3`. -/
lemma pi1_comm_pi : ∀ j, 3 ≤ j → Commute (piV1 1) (piV1 j) := by
  obtain ⟨-, -, -, -, -, -, -, h8, -, -, h11, -⟩ := relV1
  have c3 : Commute (piV1 1) (piV1 3) := h8
  have c24 : Commute (piV1 2) (piV1 4) := by
    have := comm_conj c3 aV⁻¹
    rwa [inv_inv, conj_piV1 0, conj_piV1 2] at this
  have x32 : piV1 3 * XV1 2 = XV1 2 * piV1 4 := l62_i 3 2 (by omega) (by omega)
  have x31 : piV1 3 * bV = bV * piV1 4 := by
    have := l62_i 3 1 (by omega) (by omega); rwa [XV1_one] at this
  have c4 : Commute (piV1 1) (piV1 4) := by
    have key : bV * piV1 2 * (piV1 1 * piV1 4) = bV * piV1 2 * (piV1 4 * piV1 1) := by
      calc bV * piV1 2 * (piV1 1 * piV1 4) = (bV * piV1 2 * piV1 1) * piV1 4 := by group
        _ = piV1 1 * XV1 2 * piV1 4 := by rw [← h11]
        _ = piV1 1 * (piV1 3 * XV1 2) := by rw [x32]; group
        _ = piV1 3 * (piV1 1 * XV1 2) := by rw [← mul_assoc, c3.eq]; group
        _ = piV1 3 * bV * piV1 2 * piV1 1 := by rw [h11]; group
        _ = bV * (piV1 4 * piV1 2) * piV1 1 := by rw [x31]; group
        _ = bV * (piV1 2 * piV1 4) * piV1 1 := by rw [c24.eq]
        _ = _ := by group
    exact mul_left_cancel key
  intro j hj
  induction j with
  | zero => omega
  | succ n ih =>
    rcases (show n + 1 = 3 ∨ n + 1 = 4 ∨ 4 ≤ n by omega) with h | h | h
    · rw [h]; exact c3
    · rw [h]; exact c4
    · have ihn := (ih (by omega)).eq
      have x3 := (pi1_comm_XV1 3 le_rfl).eq
      have e : piV1 n * XV1 3 = XV1 3 * piV1 (n + 1) := l62_i n 3 (by omega) (by omega)
      have key : XV1 3 * (piV1 1 * piV1 (n + 1)) = XV1 3 * (piV1 (n + 1) * piV1 1) := by
        calc XV1 3 * (piV1 1 * piV1 (n + 1)) = (XV1 3 * piV1 1) * piV1 (n + 1) := by group
          _ = piV1 1 * (XV1 3 * piV1 (n + 1)) := by rw [← x3]; group
          _ = piV1 1 * (piV1 n * XV1 3) := by rw [e]
          _ = (piV1 1 * piV1 n) * XV1 3 := by group
          _ = piV1 n * (piV1 1 * XV1 3) := by rw [ihn]; group
          _ = piV1 n * XV1 3 * piV1 1 := by rw [x3]; group
          _ = _ := by rw [e]; group
      exact mul_left_cancel key

/-- Lemma 6.3 iii). -/
lemma l63_iii (i j : ℕ) (hj : i + 2 ≤ j) : piV1 i * piV1 j = piV1 j * piV1 i := by
  -- first for `i ≥ 1`
  have pos : ∀ k j, k + 3 ≤ j → Commute (piV1 (k + 1)) (piV1 j) := by
    intro k j hkj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 + k := ⟨j - 1 - k, by omega⟩
    have h := comm_conj (pi1_comm_pi (m + 1) (by omega)) (aV ^ k)⁻¹
    rw [inv_inv, ← piV1_succ_conj, conjpow_piV1 m k] at h
    exact h
  rcases i with _ | k
  · -- conjugate `π₁ π_{j+1}` by `C_{j+2}`
    have h := comm_conj (pos 0 (j + 1) (by omega)) (CV1 (j + 2))
    rw [CV1_conj_pi (j + 2) (0 + 1) (by omega) (by omega),
      CV1_conj_pi (j + 2) (j + 1) (by omega) (by omega)] at h
    simpa using h.eq
  · exact (pos k j (by omega)).eq


end CannonFloydParry.S6

/-! Lemma 6.4 (CFP p. 245). -/

namespace CannonFloydParry.S6

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)

lemma piV1_inv (i : ℕ) : (piV1 i)⁻¹ = piV1 i := by
  rw [inv_eq_iff_mul_eq_one, ← sq, l63_i]


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


end CannonFloydParry.S6

/-! Lemma 6.6 (CFP pp. 246–247). -/

namespace CannonFloydParry.S6

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)

/-- Lemma 6.6, as stated. -/
theorem CV1_pow_mul_piV1' (k m n : ℕ) (hmn : m < n + 2) (hkn : k < n) :
    (m ≤ k → CV1 n ^ m * piV1 k = piV1 (k - m) * CV1 n ^ m) ∧
      (m = k + 1 → CV1 n ^ m * piV1 k = ((List.range n).map piV1).prod * CV1 n ^ (m + 1)) ∧
      (m = k + 2 → CV1 n ^ m * piV1 k = ((List.range n).reverse.map piV1).prod * CV1 n ^ (m - 1)) ∧
      (k + 2 < m → CV1 n ^ m * piV1 k = piV1 (k + (n + 2 - m)) * CV1 n ^ m) :=
  by
  try haveI := k; try haveI := m; try haveI := n; try haveI := hmn; try haveI := hkn; first
    | exact CannonFloydParry.CV1_pow_mul_piV1 k m n hmn hkn
    | exact CannonFloydParry.CV1_pow_mul_piV1
    | exact CannonFloydParry.CV1_pow_mul_piV1 ..
    | (apply CannonFloydParry.CV1_pow_mul_piV1 <;> first | assumption | infer_instance)
    | simpa using CannonFloydParry.CV1_pow_mul_piV1


end CannonFloydParry.S6

/-! `Π(n)` is finite: a coset count, `|Π(k+1) : Π(k)| ≤ k + 2`. -/

namespace CannonFloydParry.S6

/-- `W j t = π_{j+t-1} ⋯ π_{j+1} π_j`. -/
def W (j : ℕ) : ℕ → V1
  | 0 => 1
  | t + 1 => piV1 (j + t) * W j t
lemma W_succ (j t : ℕ) : W j (t + 1) = piV1 (j + t) * W j t := rfl

lemma W_split (j a b : ℕ) : W j (a + b) = W (j + b) a * W j b := by
  induction a with
  | zero => simp [W]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, W_succ, ih, W_succ,
      show j + b + a = j + (a + b) by omega, mul_assoc]

lemma W_bottom (j t : ℕ) : W j (t + 1) = W (j + 1) t * piV1 j := by
  rw [W_split j t 1]; simp [W]

lemma pi_comm (x y : ℕ) (h : x + 2 ≤ y ∨ y + 2 ≤ x) : Commute (piV1 x) (piV1 y) := by
  rcases h with h | h
  · exact l63_iii x y h
  · exact (l63_iii y x h).symm

lemma W_comm (x j : ℕ) : ∀ t, (∀ y, j ≤ y → y < j + t → x + 2 ≤ y ∨ y + 2 ≤ x) →
    Commute (piV1 x) (W j t) := by
  intro t
  induction t with
  | zero => intro; exact Commute.one_right _
  | succ t ih =>
    intro h
    rw [W_succ]
    exact (pi_comm x (j + t) (h _ (by omega) (by omega))).mul_right
      (ih fun y h1 h2 => h y h1 (by omega))

lemma piV1_mem_PiSub {i n : ℕ} (h : i < n) : piV1 i ∈ PiSub n :=
  Subgroup.subset_closure ⟨i, h, rfl⟩

lemma braid (i : ℕ) : piV1 (i + 1) * piV1 i * piV1 (i + 1) = piV1 i * piV1 (i + 1) * piV1 i := by
  have h := l63_ii i
  have e : piV1 (i + 1) * piV1 i * piV1 (i + 1) =
      (piV1 (i + 1) * piV1 i) ^ 3 * (piV1 i * piV1 (i + 1) * piV1 i)⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul]; group
  rw [e, h, one_mul]
  simp only [mul_inv_rev, piV1_inv]
  group

lemma sq_one' (i : ℕ) : piV1 i * piV1 i = 1 := by rw [← sq]; exact l63_i i

/-- One right multiplication by a generator keeps us in the union of the `k + 2` cosets. -/
lemma step (k j i : ℕ) (hj : j ≤ k + 1) (hi : i < k + 1) :
    ∃ j', j' ≤ k + 1 ∧ ∃ h' ∈ PiSub k, W j (k + 1 - j) * piV1 i = h' * W j' (k + 1 - j') := by
  rcases (show i + 2 ≤ j ∨ i + 1 = j ∨ i = j ∨ j < i by omega) with h | h | h | h
  · -- commute past
    refine ⟨j, hj, piV1 i, piV1_mem_PiSub (by omega), ?_⟩
    exact (W_comm i j _ (fun y h1 _ => Or.inl (by omega))).eq.symm
  · -- extend at the bottom
    subst h
    refine ⟨i, by omega, 1, one_mem _, ?_⟩
    rw [one_mul, show k + 1 - i = (k + 1 - (i + 1)) + 1 by omega, W_bottom]
  · -- cancel at the bottom
    subst h
    refine ⟨i + 1, by omega, 1, one_mem _, ?_⟩
    rw [one_mul, show k + 1 - i = (k + 1 - (i + 1)) + 1 by omega, W_bottom, mul_assoc, sq_one',
      mul_one]
  · -- braid move
    obtain ⟨a, b, ha, hb⟩ : ∃ a b, a = k - i ∧ b = i - 1 - j := ⟨_, _, rfl, rfl⟩
    obtain ⟨c, rfl⟩ : ∃ c, i = c + 1 := ⟨i - 1, by omega⟩
    have ht : k + 1 - j = (a + 2) + b := by omega
    have hcb : j + b = c := by omega
    refine ⟨j, hj, piV1 c, piV1_mem_PiSub (by omega), ?_⟩
    have e1 : W j (k + 1 - j) = W (c + 2) a * (piV1 (c + 1) * piV1 c) * W j b := by
      rw [ht, W_split j (a + 2) b, hcb, W_split c a 2]
      simp [W, show c + 2 = c + 2 from rfl]
    have cb : Commute (piV1 (c + 1)) (W j b) :=
      W_comm (c + 1) j b (fun y h1 h2 => Or.inr (by omega))
    have ca : Commute (piV1 c) (W (c + 2) a) :=
      W_comm c (c + 2) a (fun y h1 h2 => Or.inl (by omega))
    rw [e1]
    calc W (c + 2) a * (piV1 (c + 1) * piV1 c) * W j b * piV1 (c + 1)
        = W (c + 2) a * (piV1 (c + 1) * piV1 c) * (W j b * piV1 (c + 1)) := by group
      _ = W (c + 2) a * (piV1 (c + 1) * piV1 c * piV1 (c + 1)) * W j b := by rw [← cb.eq]; group
      _ = W (c + 2) a * (piV1 c * piV1 (c + 1) * piV1 c) * W j b := by rw [braid]
      _ = (W (c + 2) a * piV1 c) * (piV1 (c + 1) * piV1 c) * W j b := by group
      _ = _ := by rw [← ca.eq]; group

lemma cover (k : ℕ) {g : V1} (hg : g ∈ PiSub (k + 1)) :
    ∃ j, j ≤ k + 1 ∧ ∃ h ∈ PiSub k, g = h * W j (k + 1 - j) := by
  unfold PiSub at hg
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨k + 1, le_rfl, 1, one_mem _, by simp [W]⟩
  | mul_right x hx y hy ih =>
    obtain ⟨i, hi, rfl⟩ := hy
    obtain ⟨j, hj, h, hh, rfl⟩ := ih
    obtain ⟨j', hj', h', hh', e⟩ := step k j i hj hi
    exact ⟨j', hj', h * h', mul_mem hh hh', by rw [mul_assoc, e, mul_assoc]⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨i, hi, rfl⟩ := hy
    obtain ⟨j, hj, h, hh, rfl⟩ := ih
    obtain ⟨j', hj', h', hh', e⟩ := step k j i hj hi
    exact ⟨j', hj', h * h', mul_mem hh hh', by rw [piV1_inv, mul_assoc, e, mul_assoc]⟩

lemma finite_PiSub_all (n : ℕ) : (PiSub n : Set V1).Finite := by
  induction n with
  | zero =>
    have : PiSub 0 = ⊥ := by
      unfold PiSub
      rw [show piV1 '' Set.Iio 0 = ∅ by ext; simp, Subgroup.closure_empty]
    rw [this]; exact Set.finite_singleton 1
  | succ k ih =>
    refine Set.Finite.subset
      ((Finset.range (k + 2)).finite_toSet.biUnion fun j _ =>
        ih.image (fun h => h * W j (k + 1 - j))) ?_
    intro g hg
    obtain ⟨j, hj, h, hh, rfl⟩ := cover k hg
    simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_image]
    exact ⟨j, by omega, h, hh, rfl⟩

end CannonFloydParry.S6

/-! Lemmas 6.7 and 6.8 (CFP p. 247). -/

namespace CannonFloydParry.S6


lemma PP_mem (n : ℕ) : PP n ∈ PiSub n := by
  unfold PP
  apply Subgroup.list_prod_mem
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact piV1_mem_PiSub hi

lemma RR_mem (n : ℕ) : RR n ∈ PiSub n := by
  rw [RR_eq_inv]; exact inv_mem (PP_mem n)

lemma CV1_pow_n2 (n : ℕ) (hn : 0 < n) : CV1 n ^ (n + 2) = 1 :=
  (CV1_pow_relations n 1 0 0 hn le_rfl (by omega) (by omega) (by omega)).2.2.2.2.2.2.2.2

/-- The generator step of Lemma 6.8 i), from Lemma 6.6. -/
lemma gen68 (n k m : ℕ) (hk : k < n) (hm : 0 < m) (hmn : m < n + 2) :
    ∃ π' ∈ PiSub n, ∃ m', 0 < m' ∧ m' < n + 2 ∧ CV1 n ^ m * piV1 k = π' * CV1 n ^ m' := by
  obtain ⟨h1, h2, h3, h4⟩ := CV1_pow_mul_piV1' k m n hmn hk
  rcases (show m ≤ k ∨ m = k + 1 ∨ m = k + 2 ∨ k + 2 < m by omega) with h | h | h | h
  · exact ⟨_, piV1_mem_PiSub (by omega), m, hm, hmn, h1 h⟩
  · exact ⟨_, PP_mem n, m + 1, by omega, by omega, h2 h⟩
  · exact ⟨_, RR_mem n, m - 1, by omega, by omega, h3 h⟩
  · exact ⟨_, piV1_mem_PiSub (by omega), m, hm, hmn, h4 h⟩

lemma l68_i (n : ℕ) {x : V1} (hx : x ∈ PiSub n) :
    ∀ m, 0 < m → m < n + 2 →
      ∃ π' ∈ PiSub n, ∃ m', 0 < m' ∧ m' < n + 2 ∧ CV1 n ^ m * x = π' * CV1 n ^ m' := by
  unfold PiSub at hx
  induction hx using Subgroup.closure_induction_right with
  | one => intro m hm hmn; exact ⟨1, one_mem _, m, hm, hmn, by group⟩
  | mul_right x hx y hy ih =>
    obtain ⟨k, hk, rfl⟩ := hy
    intro m hm hmn
    obtain ⟨π1, h1, m1, hm1, hm1n, e1⟩ := ih m hm hmn
    obtain ⟨π2, h2, m2, hm2, hm2n, e2⟩ := gen68 n k m1 hk hm1 hm1n
    exact ⟨π1 * π2, mul_mem h1 h2, m2, hm2, hm2n, by rw [← mul_assoc, e1, mul_assoc, e2, mul_assoc]⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨k, hk, rfl⟩ := hy
    intro m hm hmn
    obtain ⟨π1, h1, m1, hm1, hm1n, e1⟩ := ih m hm hmn
    obtain ⟨π2, h2, m2, hm2, hm2n, e2⟩ := gen68 n k m1 hk hm1 hm1n
    exact ⟨π1 * π2, mul_mem h1 h2, m2, hm2, hm2n,
      by rw [piV1_inv, ← mul_assoc, e1, mul_assoc, e2, mul_assoc]⟩

/-- Every element of `⟨Π(n), Cₙ⟩` is `π Cₙ^m` with `π ∈ Π(n)`, `m < n + 2`. -/
lemma l68_form (n : ℕ) (hn : 0 < n) {g : V1}
    (hg : g ∈ Subgroup.closure (insert (CV1 n) (PiSub n : Set V1))) :
    ∃ π ∈ PiSub n, ∃ m, m < n + 2 ∧ g = π * CV1 n ^ m := by
  have hC := CV1_pow_n2 n hn
  have red : ∀ π ∈ PiSub n, ∀ m : ℕ, ∃ π' ∈ PiSub n, ∃ m', m' < n + 2 ∧ π * CV1 n ^ m = π' * CV1 n ^ m' :=
    fun π hπ m => ⟨π, hπ, m % (n + 2), Nat.mod_lt _ (by omega), by rw [← pow_eq_pow_mod m hC]⟩
  -- right multiplication by an element of `Π(n)`
  have byPi : ∀ π ∈ PiSub n, ∀ m, m < n + 2 → ∀ y ∈ PiSub n,
      ∃ π' ∈ PiSub n, ∃ m', m' < n + 2 ∧ π * CV1 n ^ m * y = π' * CV1 n ^ m' := by
    intro π hπ m hm y hy
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact ⟨π * y, mul_mem hπ hy, 0, by omega, by group⟩
    · obtain ⟨π', h', m', -, hm', e⟩ := l68_i n hy m hm0 hm
      exact ⟨π * π', mul_mem hπ h', m', hm', by rw [mul_assoc, e, ← mul_assoc]⟩
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨1, one_mem _, 0, by omega, by group⟩
  | mul_right x hx y hy ih =>
    obtain ⟨π, hπ, m, hm, rfl⟩ := ih
    rcases hy with rfl | hy
    · obtain ⟨π', h', m', hm', e⟩ := red π hπ (m + 1)
      exact ⟨π', h', m', hm', by rw [← e, pow_succ, mul_assoc]⟩
    · exact byPi π hπ m hm y hy
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨π, hπ, m, hm, rfl⟩ := ih
    rcases hy with rfl | hy
    · obtain ⟨π', h', m', hm', e⟩ := red π hπ (m + (n + 1))
      refine ⟨π', h', m', hm', ?_⟩
      rw [← e, pow_add]
      have : CV1 n ^ (n + 1) = (CV1 n)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, hC]
      rw [this, mul_assoc]
    · exact byPi π hπ m hm y⁻¹ (inv_mem hy)

/-- Lemma 6.8. -/
theorem CV1_pow_mul_eq_mul_CV1_pow_and_finite' :
    (∀ m n : ℕ, 0 < m → 0 < n → m < n + 2 → ∀ π ∈ PiSub n,
      ∃ π' ∈ PiSub n, ∃ m' : ℕ, 0 < m' ∧ m' < n + 2 ∧ CV1 n ^ m * π = π' * CV1 n ^ m') ∧
      ∀ n : ℕ, 0 < n → Finite (Subgroup.closure (insert (CV1 n) (PiSub n : Set V1))) := by
  refine ⟨fun m n hm _ hmn π hπ => l68_i n hπ m hm hmn, fun n hn => ?_⟩
  have hfin : ((fun p : V1 × ℕ => p.1 * CV1 n ^ p.2) ''
      ((PiSub n : Set V1) ×ˢ Set.Iio (n + 2))).Finite :=
    ((finite_PiSub_all n).prod (Set.finite_Iio _)).image _
  refine Set.Finite.to_subtype (hfin.subset ?_)
  intro g hg
  obtain ⟨π, hπ, m, hm, rfl⟩ := l68_form n hn hg
  exact ⟨(π, m), ⟨hπ, hm⟩, rfl⟩

end CannonFloydParry.S6

open CannonFloydParry in
theorem solution :
    (∀ m n : ℕ, 0 < m → 0 < n → m < n + 2 → ∀ π ∈ PiSub n,
      ∃ π' ∈ PiSub n, ∃ m' : ℕ, 0 < m' ∧ m' < n + 2 ∧ CV1 n ^ m * π = π' * CV1 n ^ m') ∧
      ∀ n : ℕ, 0 < n → Finite (Subgroup.closure (insert (CV1 n) (PiSub n : Set V1))) := by
  exact S6.CV1_pow_mul_eq_mul_CV1_pow_and_finite'
