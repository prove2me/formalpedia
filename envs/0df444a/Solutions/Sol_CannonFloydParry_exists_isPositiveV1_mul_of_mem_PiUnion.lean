-- Prove2me | solution 1 for CannonFloydParry.exists_isPositiveV1_mul_of_mem_PiUnion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-26T11:03:36.694981+00:00
-- url     : https://prove2.me/submissions/5024668b-96d1-4e48-82dd-cc4d8e76fe43

import Theorems.Thm_CannonFloydParry_piV1_mul_XV1
import Definitions.Def_CannonFloydParry_V
import Theorems.Thm_CannonFloydParry_CT1_succ_relations
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

/-- p. 236 in `V₁`: `XₙXₖ = XₖXₙ₊₁` for `k < n`. -/
lemma XV1_mul_XV1 (k n : ℕ) (hkn : k < n) : XV1 n * XV1 k = XV1 k * XV1 (n + 1) := by
  have := congrArg fromT1 (XT1_mul_XT1 k n hkn)
  simpa [map_mul, fromT1_XT1] using this

lemma conj_XV1 (m : ℕ) : aV⁻¹ * XV1 (m + 1) * aV = XV1 (m + 2) := by
  simp only [XV1_succ]; group

lemma conj_piV1 (m : ℕ) : aV⁻¹ * piV1 (m + 1) * aV = piV1 (m + 2) := by
  simp only [piV1_succ]; group

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

lemma XV1_one : XV1 1 = bV := by simp [XV1_succ]

lemma piV1_eq_conj (m k : ℕ) : piV1 (m + 1 + k) = (aV ^ k)⁻¹ * piV1 (m + 1) * aV ^ k :=
  (conjpow_piV1 m k).symm

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

/-- Lemma 6.4, as stated. -/
theorem piV1_mul_XV1' (i j : ℕ) :
    (i + 2 ≤ j → piV1 i * XV1 j = XV1 j * piV1 i) ∧
      piV1 i * XV1 (i + 1) = XV1 i * piV1 (i + 1) * piV1 i ∧
      piV1 i * XV1 i = XV1 (i + 1) * piV1 i * piV1 (i + 1) ∧
      (j < i → piV1 i * XV1 j = XV1 j * piV1 (i + 1)) :=
  by
  try haveI := i; try haveI := j; first
    | exact CannonFloydParry.piV1_mul_XV1 i j
    | exact CannonFloydParry.piV1_mul_XV1
    | exact CannonFloydParry.piV1_mul_XV1 ..
    | (apply CannonFloydParry.piV1_mul_XV1 <;> first | assumption | infer_instance)
    | simpa using CannonFloydParry.piV1_mul_XV1


end CannonFloydParry.S6

/-! Lemma 6.5 (CFP pp. 245–246). -/

namespace CannonFloydParry.S6


end CannonFloydParry.S6

/-! Lemma 6.6 (CFP pp. 246–247). -/

namespace CannonFloydParry.S6

local notation "aV" => (PresentedGroup.of FormalV.A : V1)
local notation "bV" => (PresentedGroup.of FormalV.B : V1)


end CannonFloydParry.S6

/-! `Π(n)` is finite: a coset count, `|Π(k+1) : Π(k)| ≤ k + 2`. -/

namespace CannonFloydParry.S6

lemma piV1_mem_PiSub {i n : ℕ} (h : i < n) : piV1 i ∈ PiSub n :=
  Subgroup.subset_closure ⟨i, h, rfl⟩

end CannonFloydParry.S6

/-! Lemmas 6.7 and 6.8 (CFP p. 247). -/

namespace CannonFloydParry.S6

/-- `π_i X_j = X_{j'} π'` with `π' ∈ Π(n+1)`, for `i < n` (Lemma 6.4). -/
lemma gen67 (n i j : ℕ) (hi : i < n) :
    ∃ j', ∃ π' ∈ PiSub (n + 1), piV1 i * XV1 j = XV1 j' * π' := by
  obtain ⟨h1, h2, h3, h4⟩ := piV1_mul_XV1' i j
  rcases (show i + 2 ≤ j ∨ j = i + 1 ∨ j = i ∨ j < i by omega) with h | h | h | h
  · exact ⟨j, piV1 i, piV1_mem_PiSub (by omega), h1 h⟩
  · subst h
    exact ⟨i, piV1 (i + 1) * piV1 i,
      mul_mem (piV1_mem_PiSub (by omega)) (piV1_mem_PiSub (by omega)), by rw [h2, mul_assoc]⟩
  · subst h
    exact ⟨j + 1, piV1 j * piV1 (j + 1),
      mul_mem (piV1_mem_PiSub (by omega)) (piV1_mem_PiSub (by omega)), by rw [h3, mul_assoc]⟩
  · exact ⟨j, piV1 (i + 1), piV1_mem_PiSub (by omega), h4 h⟩

lemma gen67' (n : ℕ) {x : V1} (hx : x ∈ PiSub n) :
    ∀ j, ∃ j', ∃ π' ∈ PiSub (n + 1), x * XV1 j = XV1 j' * π' := by
  unfold PiSub at hx
  induction hx using Subgroup.closure_induction_right with
  | one => intro j; exact ⟨j, 1, one_mem _, by group⟩
  | mul_right x hx y hy ih =>
    obtain ⟨i, hi, rfl⟩ := hy
    intro j
    obtain ⟨j1, π1, h1, e1⟩ := gen67 n i j hi
    obtain ⟨j2, π2, h2, e2⟩ := ih j1
    exact ⟨j2, π2 * π1, mul_mem h2 h1, by rw [mul_assoc, e1, ← mul_assoc, e2, mul_assoc]⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨i, hi, rfl⟩ := hy
    intro j
    obtain ⟨j1, π1, h1, e1⟩ := gen67 n i j hi
    obtain ⟨j2, π2, h2, e2⟩ := ih j1
    exact ⟨j2, π2 * π1, mul_mem h2 h1, by rw [piV1_inv, mul_assoc, e1, ← mul_assoc, e2, mul_assoc]⟩

/-- Lemma 6.7. -/
theorem exists_isPositiveV1_mul_of_mem_PiUnion' {p π : V1} (hp : IsPositiveV1 p)
    (hπ : π ∈ PiUnion) :
    ∃ p' π', IsPositiveV1 p' ∧ π' ∈ PiUnion ∧ π * p = p' * π' := by
  unfold IsPositiveV1 at hp
  induction hp using Submonoid.closure_induction generalizing π with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hπ
    obtain ⟨j', π', h', e⟩ := gen67' n hn j
    exact ⟨XV1 j', π', Submonoid.subset_closure ⟨j', rfl⟩, Set.mem_iUnion.2 ⟨n + 1, h'⟩, e⟩
  | one => exact ⟨1, π, one_mem _, hπ, by group⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨p1, π1, hp1, hπ1, e1⟩ := ihx hπ
    obtain ⟨p2, π2, hp2, hπ2, e2⟩ := ihy hπ1
    exact ⟨p1 * p2, π2, mul_mem hp1 hp2, hπ2, by rw [← mul_assoc, e1, mul_assoc, e2, mul_assoc]⟩


end CannonFloydParry.S6

open CannonFloydParry in
theorem solution {p π : V1} (hp : IsPositiveV1 p) (hπ : π ∈ PiUnion) :
    ∃ p' π', IsPositiveV1 p' ∧ π' ∈ PiUnion ∧ π * p = p' * π' := by
  exact S6.exists_isPositiveV1_mul_of_mem_PiUnion' hp hπ
