-- Prove2me | solution 1 for BakerScudder1990.Tolerance.case1_slope
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T10:06:08.590637+00:00
-- url     : https://prove2.me/submissions/ad057d39-906b-4043-95b0-d7f487c8284c

import Mathlib
import Definitions.Def_BakerScudder1990_Tolerance_Instance

set_option autoImplicit false

open BakerScudder1990.Tolerance in
lemma p2m_d29ed133_C_add_le {n : ℕ} (I : Instance n) {i k : Fin n} (hik : i < k) :
    I.C i + I.p k ≤ I.C k := by
  unfold Instance.C
  have hk : k ∉ Finset.univ.filter (fun l : Fin n => l ≤ i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]; exact hik
  rw [add_comm, ← Finset.sum_insert hk]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    rcases hl with h | h
    · exact h ▸ le_rfl
    · exact le_trans h hik.le
  · intro l _ hl
    have hne : i ≠ l := by
      rintro rfl
      apply hl
      simp
    have := I.htol i l hne
    have := I.hu i
    have := I.hv l
    linarith

open BakerScudder1990.Tolerance in
lemma p2m_d29ed133_early {n : ℕ} (I : Instance n) (k : Fin (n + 1)) (d : ℝ)
    (hlo : ∀ i : Fin n, i.val + 1 = k.val → I.C i + I.u i < d)
    (j : Fin n) (hj : j.val < k.val) : I.C j + I.u j < d := by
  by_cases h : j.val + 1 = k.val
  · exact hlo j h
  · have hkn := k.isLt
    have hk : k.val - 1 < n := by omega
    have hji : j < (⟨k.val - 1, hk⟩ : Fin n) :=
      Fin.lt_def.mpr (by simp only; omega)
    have h1 := p2m_d29ed133_C_add_le I hji
    have h2 := hlo ⟨k.val - 1, hk⟩ (by simp only; omega)
    have h3 := I.htol j ⟨k.val - 1, hk⟩ (ne_of_lt hji)
    have h4 := I.hv ⟨k.val - 1, hk⟩
    have h5 := I.hu ⟨k.val - 1, hk⟩
    linarith

open BakerScudder1990.Tolerance in
lemma p2m_d29ed133_tardy {n : ℕ} (I : Instance n) (k : Fin (n + 1)) (d ε : ℝ)
    (hhi : ∀ i : Fin n, i.val = k.val → d + ε < I.C i - I.v i)
    (j : Fin n) (hj : k.val ≤ j.val) : d + ε < I.C j - I.v j := by
  by_cases h : j.val = k.val
  · exact hhi j h
  · have hjn := j.isLt
    have hk : k.val < n := by omega
    have hij : (⟨k.val, hk⟩ : Fin n) < j :=
      Fin.lt_def.mpr (by simp only; omega)
    have h1 := p2m_d29ed133_C_add_le I hij
    have h2 := hhi ⟨k.val, hk⟩ rfl
    have h3 := I.htol ⟨k.val, hk⟩ j (ne_of_lt hij)
    have h4 := I.hv j
    have h5 := I.hu ⟨k.val, hk⟩
    have h6 := I.hv ⟨k.val, hk⟩
    linarith

open BakerScudder1990.Tolerance BakerScudder1990.Tolerance.Instance in
theorem solution {n : ℕ} (I : Instance n) (k : Fin (n + 1)) (d ε : ℝ) (hε : 0 < ε)
    (hlo : ∀ i : Fin n, i.val + 1 = k.val → I.C i + I.u i < d)
    (hhi : ∀ i : Fin n, i.val = k.val → d + ε < I.C i - I.v i) :
    I.cost (d + ε) - I.cost d =
      ((∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val), I.α i) -
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val), I.β i)) * ε := by
  have hterm : ∀ j : Fin n,
      (I.α j * I.earliness (d + ε) j + I.β j * I.tardiness (d + ε) j) -
        (I.α j * I.earliness d j + I.β j * I.tardiness d j) =
      if j.val < k.val then I.α j * ε else -(I.β j * ε) := by
    intro j
    unfold Instance.earliness Instance.tardiness
    have hu := I.hu j
    have hv := I.hv j
    split_ifs with hj
    · have he := p2m_d29ed133_early I k d hlo j hj
      have e1 : max 0 (d + ε - I.C j - I.u j) = d + ε - I.C j - I.u j :=
        max_eq_right (by linarith)
      have e2 : max 0 (d - I.C j - I.u j) = d - I.C j - I.u j :=
        max_eq_right (by linarith)
      have e3 : max 0 (I.C j - (d + ε) - I.v j) = 0 := max_eq_left (by linarith)
      have e4 : max 0 (I.C j - d - I.v j) = 0 := max_eq_left (by linarith)
      rw [e1, e2, e3, e4]
      ring
    · have ht := p2m_d29ed133_tardy I k d ε hhi j (by omega)
      have e1 : max 0 (d + ε - I.C j - I.u j) = 0 := max_eq_left (by linarith)
      have e2 : max 0 (d - I.C j - I.u j) = 0 := max_eq_left (by linarith)
      have e3 : max 0 (I.C j - (d + ε) - I.v j) = I.C j - (d + ε) - I.v j :=
        max_eq_right (by linarith)
      have e4 : max 0 (I.C j - d - I.v j) = I.C j - d - I.v j :=
        max_eq_right (by linarith)
      rw [e1, e2, e3, e4]
      ring
  unfold Instance.cost
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun j _ => hterm j),
    Finset.sum_ite, Finset.sum_neg_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  simp only [not_lt]
  ring
