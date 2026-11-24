-- Prove2me | solution 1 for Formalism.UG.P.spherical_iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:39:51.348651+00:00
-- url     : https://prove2.me/submissions/637af6a8-bfe1-4eb3-b125-848d1c41bcd9

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Spherical
import Theorems.Thm_Formalism_UG_P_spherical_upper_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Formalism.UG
namespace Formalism.UG.P
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
private lemma exists_GLint_of_integral_inverse {n : ℕ} (A B : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hA : ∀ i j, A i j ∈ Ov F v) (hB : ∀ i j, B i j ∈ Ov F v) (hAB : A * B = 1) (hBA : B * A = 1) :
    ∃ k ∈ GLint (Fin n) (Ov F v), (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = A := by
  let A' : Matrix (Fin n) (Fin n) (Ov F v) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix (Fin n) (Fin n) (Ov F v) := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have hinj : ∀ M N : Matrix (Fin n) (Fin n) (Ov F v),
      RingHom.mapMatrix (Ov F v).subtype M = RingHom.mapMatrix (Ov F v).subtype N → M = N := by
    intro M N h
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  have hmA : RingHom.mapMatrix (Ov F v).subtype A' = A := Matrix.ext fun i j => rfl
  have hmB : RingHom.mapMatrix (Ov F v).subtype B' = B := Matrix.ext fun i j => rfl
  have hAB' : A' * B' = 1 := hinj _ _ (by rw [map_mul, map_one, hmA, hmB, hAB])
  have hBA' : B' * A' = 1 := hinj _ _ (by rw [map_mul, map_one, hmA, hmB, hBA])
  let u : GL (Fin n) (Ov F v) := ⟨A', B', hAB', hBA'⟩
  exact ⟨bc (Ov F v).subtype u, ⟨u, rfl⟩, Matrix.ext fun i j => rfl⟩
private lemma mul_column_operation_apply {R : Type*} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (r : Fin n)
    (c : Fin n → R) (x b : Fin n) :
    (M * Matrix.of fun a b => (if a = b then (1 : R) else 0) + (if a = r ∧ b ≠ r then c b else 0)) x b =
      M x b + (if b ≠ r then M x r * c b else 0) := by
  by_cases hb : b = r
  · subst hb
    simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply, hb, mul_add, Finset.sum_add_distrib]
private lemma column_operation_mul_neg_eq_one {R : Type*} [CommRing R] {n : ℕ} (r : Fin n) (c : Fin n → R) :
    (Matrix.of fun a b => (if a = b then (1 : R) else 0) + (if a = r ∧ b ≠ r then c b else 0)) *
      (Matrix.of fun a b => (if a = b then (1 : R) else 0) + (if a = r ∧ b ≠ r then -c b else 0)) = 1 := by
  ext a b
  rw [mul_column_operation_apply _ r (fun b => -c b)]
  by_cases hbr : b = r
  · subst hbr
    simp [Matrix.one_apply]
  · by_cases har : a = r
    · subst har
      have hne : a ≠ b := fun h => hbr h.symm
      simp [Matrix.one_apply, hbr, hne]
    · simp [Matrix.one_apply, hbr, har]
private lemma exists_GLint_eq_column_operation {n : ℕ} (r : Fin n) (c : Fin n → v.adicCompletion F)
    (hc : ∀ b, c b ∈ Ov F v) :
    ∃ k ∈ GLint (Fin n) (Ov F v), (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      Matrix.of fun a b => (if a = b then (1 : v.adicCompletion F) else 0) +
        (if a = r ∧ b ≠ r then c b else 0) := by
  refine exists_GLint_of_integral_inverse F v _
    (Matrix.of fun a b => (if a = b then (1 : v.adicCompletion F) else 0) + (if a = r ∧ b ≠ r then -c b else 0))
    ?_ ?_ (column_operation_mul_neg_eq_one r c) ?_
  · intro i j
    simp only [Matrix.of_apply]
    refine Subring.add_mem _ ?_ ?_
    · split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · split_ifs
      · exact hc j
      · exact Subring.zero_mem _
  · intro i j
    simp only [Matrix.of_apply]
    refine Subring.add_mem _ ?_ ?_
    · split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · split_ifs
      · exact Subring.neg_mem _ (hc j)
      · exact Subring.zero_mem _
  · have h := column_operation_mul_neg_eq_one r (fun b => -c b)
    simpa using h
private lemma mem_Ov_of_valuation_le_one (x : v.adicCompletion F) (h : Valued.v x ≤ 1) : x ∈ Ov F v := by
  change x ∈ v.adicCompletionIntegers F
  exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr h
private lemma exists_GLint_mul_clears_below_diag_from {n : ℕ} (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (i0 : Fin n)
    (hM : ∀ i j : Fin n, i0 < i → j < i → M i j = 0) :
    ∃ k ∈ GLint (Fin n) (Ov F v), ∀ i j : Fin n, i0 ≤ i → j < i →
      (M * (k : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i j = 0 := by
  classical
  by_cases hz : ∀ j, j < i0 → M i0 j = 0
  · refine ⟨1, Subgroup.one_mem _, fun i j hi hj => ?_⟩
    simp only [Units.val_one, Matrix.mul_one]
    rcases hi.lt_or_eq with h | h
    · exact hM i j h hj
    · subst h
      exact hz j hj
  push_neg at hz
  obtain ⟨j1, hj1, hj1ne⟩ := hz
  obtain ⟨p, hpS, hpmax⟩ := Finset.exists_max_image (Finset.univ.filter (fun j => j ≤ i0))
    (fun j => Valued.v (M i0 j)) ⟨i0, by simp⟩
  have hp : p ≤ i0 := (Finset.mem_filter.mp hpS).2
  have hmax : ∀ j, j ≤ i0 → Valued.v (M i0 j) ≤ Valued.v (M i0 p) := fun j hj => hpmax j (by simp [hj])
  have hppos : 0 < Valued.v (M i0 p) :=
    lt_of_lt_of_le ((Valuation.pos_iff _).mpr hj1ne) (hmax j1 hj1.le)
  obtain ⟨k1, hk1, hrows1, hpiv1, hne1⟩ : ∃ k1 ∈ GLint (Fin n) (Ov F v),
      (∀ i j : Fin n, i0 < i → j < i →
        (M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i j = 0) ∧
      (∀ j, j ≤ i0 → Valued.v ((M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i0 j) ≤
        Valued.v ((M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i0 i0)) ∧
      (M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i0 i0 ≠ 0 := by
    by_cases heq : Valued.v (M i0 i0) = Valued.v (M i0 p)
    · refine ⟨1, Subgroup.one_mem _, ?_, ?_, ?_⟩
      · simpa using hM
      · intro j hj
        simpa [heq] using hmax j hj
      · simp only [Units.val_one, Matrix.mul_one]
        intro h0
        rw [h0, map_zero] at heq
        exact (ne_of_lt hppos) heq
    · have hlt : Valued.v (M i0 i0) < Valued.v (M i0 p) := lt_of_le_of_ne (hmax i0 le_rfl) heq
      have hpi0 : p ≠ i0 := fun h => heq (by rw [h])
      obtain ⟨k1, hk1, hk1eq⟩ := exists_GLint_eq_column_operation F v p (fun b => if b = i0 then 1 else 0) (fun b => by
        split_ifs
        · exact Subring.one_mem _
        · exact Subring.zero_mem _)
      have hdiag : (M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i0 i0 = M i0 i0 + M i0 p := by
        rw [hk1eq, mul_column_operation_apply]
        simp [Ne.symm hpi0]
      refine ⟨k1, hk1, ?_, ?_, ?_⟩
      · intro i j hi hj
        rw [hk1eq, mul_column_operation_apply, hM i j hi hj, hM i p hi (lt_of_le_of_lt hp hi)]
        simp
      · intro j hj
        rw [hdiag, Valuation.map_add_eq_of_lt_right _ hlt]
        by_cases hji : j = i0
        · subst hji
          rw [hdiag, Valuation.map_add_eq_of_lt_right _ hlt]
        · rw [hk1eq, mul_column_operation_apply]
          simp only [hji, if_false, mul_zero, ite_self, add_zero]
          exact hmax j hj
      · rw [hdiag]
        intro h0
        have h1 := Valuation.map_add_eq_of_lt_right Valued.v hlt
        rw [h0, map_zero] at h1
        exact (ne_of_lt hppos) h1
  set M1 := M * (k1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) with hM1
  obtain ⟨k2, hk2, hk2eq⟩ := exists_GLint_eq_column_operation F v i0
    (fun b => if b < i0 then -(M1 i0 b / M1 i0 i0) else 0) (fun b => by
      split_ifs with hb
      · apply mem_Ov_of_valuation_le_one
        rw [Valuation.map_neg, map_div₀]
        exact div_le_one_of_le₀ (hpiv1 b hb.le) zero_le'
      · exact Subring.zero_mem _)
  refine ⟨k1 * k2, Subgroup.mul_mem _ hk1 hk2, fun i j hi hj => ?_⟩
  rw [Units.val_mul, ← Matrix.mul_assoc, ← hM1, hk2eq, mul_column_operation_apply]
  rcases hi.lt_or_eq with h | h
  · rw [hrows1 i j h hj, hrows1 i i0 h h]
    simp
  · subst h
    have hji : j ≠ i0 := ne_of_lt hj
    simp only [hji, ne_eq, not_false_eq_true, if_true, hj]
    field_simp
    ring
end Formalism.UG.P
end

set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.UG Formalism.UG.P
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution {n : ℕ} (g : GL (Fin n) (v.adicCompletion F)) :
    ∃ b k : GL (Fin n) (v.adicCompletion F),
      (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id ∧
      k ∈ GLint (Fin n) (Ov F v) ∧ g = b * k := by
  classical
  have key : ∀ r, r ≤ n → ∃ k ∈ GLint (Fin n) (Ov F v), ∀ i j : Fin n, n - r ≤ i.val → j < i →
      ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (k : Matrix (Fin n) (Fin n) (v.adicCompletion F))) i j = 0 := by
    intro r
    induction r with
    | zero =>
      intro _
      refine ⟨1, Subgroup.one_mem _, fun i j hi _ => ?_⟩
      have := i.isLt
      omega
    | succ r ih =>
      intro hr
      obtain ⟨k, hk, hup⟩ := ih (by omega)
      obtain ⟨k2, hk2, h2⟩ := exists_GLint_mul_clears_below_diag_from F v
        ((g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (k : Matrix (Fin n) (Fin n) (v.adicCompletion F)))
        ⟨n - r - 1, by omega⟩ (fun i j hi hj => hup i j (by rw [Fin.lt_def] at hi; simp at hi; omega) hj)
      refine ⟨k * k2, Subgroup.mul_mem _ hk hk2, fun i j hi hj => ?_⟩
      rw [Units.val_mul, ← Matrix.mul_assoc]
      exact h2 i j (by rw [Fin.le_def]; simp; omega) hj
  obtain ⟨k, hk, hup⟩ := key n le_rfl
  refine ⟨g * k, k⁻¹, ?_, Subgroup.inv_mem _ hk, by group⟩
  rw [← spherical_upper_iff]
  intro i j hji
  rw [Units.val_mul]
  exact hup i j (by omega) hji
end Formalism.UG.P
