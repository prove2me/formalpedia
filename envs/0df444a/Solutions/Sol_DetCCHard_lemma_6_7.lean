-- Prove2me | solution 1 for DetCCHard.lemma_6_7
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T13:43:41.74242+00:00
-- url     : https://prove2.me/submissions/c0c10ef1-c40a-41b3-807f-e5867fd22ba6

import Mathlib

theorem solution (k q : ℕ) (hq : q = 2 ^ k) (V : Finset (List Bool))
    (hV : ∀ v ∈ V, ∀ w ∈ V, v <+: w → v = w) (hdepth : ∀ v ∈ V, v.length ≤ k)
    (h z : List Bool → ℕ) (hz : ∀ v ∈ V, z v ≤ h v) (hsum : q < ∑ v ∈ V, (h v + z v)) :
    ∃ v ∈ V, q / 2 ^ v.length < h v + z v ∧
      (2 ≤ q / 2 ^ v.length → q / 2 ^ v.length / 2 + 1 ≤ h v) ∧
      (q / 2 ^ v.length = 1 → 2 ≤ h v ∨ (h v = 1 ∧ z v = 1)) := by
  classical
  -- Kraft inequality in `ℕ`: the Kraft sum is at most `q`.
  have hkraft : ∑ v ∈ V, q / 2 ^ v.length ≤ q := by
    by_cases hempty : [] ∈ V
    · -- `[] ∈ V` forces `V = {[]}`
      have hVs : V = {[]} := by
        ext v
        simp only [Finset.mem_singleton]
        constructor
        · intro hv
          exact (hV [] hempty v hv ⟨v, rfl⟩).symm
        · intro hv
          subst hv
          exact hempty
      rw [hVs]
      simp
    · -- `[] ∉ V`: prefix-freeness gives unique decodability, then Kraft–McMillan
      have prefix_cmp : ∀ {v w a b : List Bool}, v ++ a = w ++ b → v <+: w ∨ w <+: v := by
        intro v w a b hab
        rcases le_total v.length w.length with hle | hle
        · left
          rw [List.prefix_iff_eq_take]
          calc v = (v ++ a).take v.length := (List.take_left (l₁ := v) (l₂ := a)).symm
            _ = (w ++ b).take v.length := by rw [hab]
            _ = w.take v.length := List.take_append_of_le_length hle
        · right
          rw [List.prefix_iff_eq_take]
          calc w = (w ++ b).take w.length := (List.take_left (l₁ := w) (l₂ := b)).symm
            _ = (v ++ a).take w.length := by rw [← hab]
            _ = v.take w.length := List.take_append_of_le_length hle
      have huniq : InformationTheory.UniquelyDecodable (V : Set (List Bool)) := by
        intro L₁
        induction L₁ with
        | nil =>
            intro L₂ h1 h2 hflat
            cases L₂ with
            | nil => rfl
            | cons w L₂ =>
                exfalso
                have hw : w = [] := by
                  simp only [List.flatten_cons, List.flatten_nil] at hflat
                  exact (List.append_eq_nil_iff.mp hflat.symm).1
                exact hempty (hw ▸ h2 w List.mem_cons_self)
        | cons v L₁ ih =>
            intro L₂ h1 h2 hflat
            cases L₂ with
            | nil =>
                exfalso
                have hv : v = [] := by
                  simp only [List.flatten_cons, List.flatten_nil] at hflat
                  exact (List.append_eq_nil_iff.mp hflat).1
                exact hempty (hv ▸ h1 v List.mem_cons_self)
            | cons w L₂ =>
                simp only [List.flatten_cons] at hflat
                have hv : v ∈ V := h1 v List.mem_cons_self
                have hw : w ∈ V := h2 w List.mem_cons_self
                have hvw : v = w := by
                  rcases prefix_cmp hflat with h | h
                  · exact hV v hv w hw h
                  · exact (hV w hw v hv h).symm
                have hflat' : L₁.flatten = L₂.flatten := by
                  have hh := hflat
                  rw [hvw] at hh
                  exact List.append_cancel_left hh
                have h1' : ∀ x ∈ L₁, x ∈ (V : Set (List Bool)) :=
                  fun x hx => h1 x (List.mem_cons_of_mem v hx)
                have h2' : ∀ x ∈ L₂, x ∈ (V : Set (List Bool)) :=
                  fun x hx => h2 x (List.mem_cons_of_mem w hx)
                rw [ih L₂ h1' h2' hflat', hvw]
      have hKraft : ∑ v ∈ V, (1 / 2 : ℝ) ^ v.length ≤ 1 := by
        have hK := InformationTheory.kraft_mcmillan_inequality (S := V) huniq
        simpa using hK
      -- each Kraft term is `2^k * (1/2)^{|v|}`
      have hterm : ∀ v ∈ V, ((q / 2 ^ v.length : ℕ) : ℝ)
          = (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ v.length := by
        intro v hv
        have hlen := hdepth v hv
        have hdiv : q / 2 ^ v.length = 2 ^ (k - v.length) := by
          rw [hq]
          exact Nat.pow_div hlen (by norm_num)
        rw [hdiv]
        push_cast
        have hk : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - v.length) * (2 : ℝ) ^ v.length := by
          rw [← pow_add, Nat.sub_add_cancel hlen]
        rw [hk, one_div, inv_pow]
        rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), mul_one]
      have hR : ∑ v ∈ V, ((q / 2 ^ v.length : ℕ) : ℝ) ≤ (q : ℝ) := by
        calc ∑ v ∈ V, ((q / 2 ^ v.length : ℕ) : ℝ)
            = ∑ v ∈ V, (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ v.length := Finset.sum_congr rfl hterm
          _ = (2 : ℝ) ^ k * ∑ v ∈ V, (1 / 2 : ℝ) ^ v.length := by rw [Finset.mul_sum]
          _ ≤ (2 : ℝ) ^ k * 1 :=
              mul_le_mul_of_nonneg_left hKraft (by positivity)
          _ = (q : ℝ) := by rw [hq]; push_cast; ring
      exact_mod_cast hR
  -- some `v` beats its Kraft share
  have hex : ∃ v ∈ V, q / 2 ^ v.length < h v + z v := by
    by_contra hcon
    have hle : ∑ v ∈ V, (h v + z v) ≤ ∑ v ∈ V, q / 2 ^ v.length := by
      apply Finset.sum_le_sum
      intro v hv
      have hc : ¬ (q / 2 ^ v.length < h v + z v) := fun hlt => hcon ⟨v, hv, hlt⟩
      omega
    have hfin := le_trans hle hkraft
    omega
  obtain ⟨v, hv, hvQ⟩ := hex
  have hzle : z v ≤ h v := hz v hv
  have h2h : h v + z v ≤ 2 * h v := by omega
  refine ⟨v, hv, hvQ, ?_, ?_⟩
  · intro hQ
    have hlt : q / 2 ^ v.length < 2 * h v := by omega
    omega
  · intro hQ
    by_cases h2 : 2 ≤ h v
    · exact Or.inl h2
    · right
      have hhv : h v = 1 := by omega
      exact ⟨hhv, by omega⟩
