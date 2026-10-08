-- Prove2me | solution 1 for BealeConvexMin.QuadSimplex.iteration_terminates
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T01:16:45.884769+00:00
-- url     : https://prove2.me/submissions/4908f8c8-5b3a-46fd-9d46-09b9ec7f8074

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep

set_option autoImplicit false

/- Complete checked body: AttributedBeale -/
section

/- Complete attributed body: Sol_BealeConvexMin_QuadSimplex_pivotC_formula_37 -/
section
-- Prove2me | solution 1 for BealeConvexMin.QuadSimplex.pivotC_formula_37
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:04:28.99113+00:00
-- url     : https://prove2.me/submissions/5fbaa144-8af1-43ee-b69a-b356f4ae388e


namespace BealeConvexMin.QuadSimplex

open Matrix

/-- The substitution matrix: `z = S z'` with `z_p = Σ e_m z'_m`, `z_k = z'_k` for `k ≠ p`. -/
noncomputable def aux_q37_S {N : ℕ} (e : Fin (N + 1) → ℝ) (p : Fin (N + 1)) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun k m => if k = p then e m else if k = m then 1 else 0

lemma aux_q37_mulS {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (e : Fin (N + 1) → ℝ) (p k l : Fin (N + 1)) :
    (A * aux_q37_S e p) k l = if l = p then A k p * e p else A k l + A k p * e l := by
  rw [Matrix.mul_apply, Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ p)]
  have h : ∀ m ∈ Finset.univ \ {p}, A k m * aux_q37_S e p m l
      = if m = l then A k m else 0 := by
    intro m hm
    have hmp : m ≠ p := by simpa using hm
    simp [aux_q37_S, hmp]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  by_cases hl : l = p
  · subst hl; simp [aux_q37_S]
  · simp [aux_q37_S, hl]; ring

lemma aux_q37_Smul {N : ℕ} (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (e : Fin (N + 1) → ℝ) (p k l : Fin (N + 1)) :
    ((aux_q37_S e p).transpose * B) k l = if k = p then B p l * e p else B k l + B p l * e k := by
  rw [Matrix.mul_apply, Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ p)]
  have h : ∀ m ∈ Finset.univ \ {p}, (aux_q37_S e p).transpose k m * B m l
      = if m = k then B m l else 0 := by
    intro m hm
    have hmp : m ≠ p := by simpa using hm
    simp [aux_q37_S, hmp]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  by_cases hk : k = p
  · subst hk; simp [aux_q37_S]; ring
  · simp [aux_q37_S, hk]; ring

lemma aux_q37_pivotC_eq {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p : Fin (N + 1))
    (d : Fin (N + 1) → ℝ) :
    pivotC c p d = (aux_q37_S (pivotE d p) p).transpose * (c * aux_q37_S (pivotE d p) p) := by
  have h1 : pivotCPrime c p d = c * aux_q37_S (pivotE d p) p := by
    ext k l
    rw [aux_q37_mulS]
    simp [pivotCPrime]
  ext k l
  rw [aux_q37_Smul, ← h1]
  simp [pivotC]

lemma aux_q37_quad {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (z : Fin (N + 1) → ℝ) :
    quadValue A z = z ⬝ᵥ (A *ᵥ z) := by
  simp only [quadValue, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

lemma aux_q37_update {N : ℕ} (e : Fin (N + 1) → ℝ) (p : Fin (N + 1)) (z' : Fin (N + 1) → ℝ) :
    Function.update z' p (∑ l, e l * z' l) = aux_q37_S e p *ᵥ z' := by
  ext k
  by_cases hk : k = p
  · subst hk; simp [aux_q37_S, Matrix.mulVec, dotProduct]
  · simp [aux_q37_S, Matrix.mulVec, dotProduct, hk]

end BealeConvexMin.QuadSimplex

open BealeConvexMin.QuadSimplex

theorem checked_pivotC_formula_37 {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p : Fin (N + 1))
    (d : Fin (N + 1) → ℝ) :
    let e := pivotE d p
    pivotC c p d p p = c p p * e p ^ 2 ∧
    (∀ l, l ≠ p → pivotC c p d p l = c p l * e p + c p p * e p * e l) ∧
    (∀ k, k ≠ p → pivotC c p d k p = c k p * e p + c p p * e k * e p) ∧
    (∀ k l, k ≠ p → l ≠ p →
      pivotC c p d k l = c k l + c k p * e l + c p l * e k + c p p * e k * e l) ∧
    (c.IsSymm → (pivotC c p d).IsSymm) ∧
    ∀ z' : Fin (N + 1) → ℝ,
      quadValue c (Function.update z' p (∑ l, e l * z' l)) = quadValue (pivotC c p d) z' := by
  intro e
  have hpp : pivotC c p d p p = c p p * e p ^ 2 := by
    simp [pivotC, pivotCPrime, e]; ring
  have hpl : ∀ l, l ≠ p → pivotC c p d p l = c p l * e p + c p p * e p * e l := by
    intro l hl
    simp [pivotC, pivotCPrime, e, hl]; ring
  have hkp : ∀ k, k ≠ p → pivotC c p d k p = c k p * e p + c p p * e k * e p := by
    intro k hk
    simp [pivotC, pivotCPrime, e, hk]; ring
  have hkl : ∀ k l, k ≠ p → l ≠ p →
      pivotC c p d k l = c k l + c k p * e l + c p l * e k + c p p * e k * e l := by
    intro k l hk hl
    simp [pivotC, pivotCPrime, e, hk, hl]; ring
  refine ⟨hpp, hpl, hkp, hkl, ?_, ?_⟩
  · intro hc
    have hc' : ∀ i j, c j i = c i j := fun i j => hc.apply i j
    refine Matrix.IsSymm.ext fun i j => ?_
    by_cases hi : i = p <;> by_cases hj : j = p
    · subst hi; subst hj; rfl
    · subst hi; rw [hpl j hj, hkp j hj, hc' j]; ring
    · subst hj; rw [hpl i hi, hkp i hi, hc' i]; ring
    · rw [hkl i j hi hj, hkl j i hj hi, hc' i j, hc' i p, hc' j p]; ring
  · intro z'
    rw [aux_q37_update, aux_q37_pivotC_eq, aux_q37_quad, aux_q37_quad]
    set S := aux_q37_S e p
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
end

/- Complete attributed body: Sol_BealeConvexMin_QuadSimplex_lemma1 -/
section
-- Prove2me | solution 1 for BealeConvexMin.QuadSimplex.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:36:00.019435+00:00
-- url     : https://prove2.me/submissions/aaf5c9de-6097-4a4c-a371-515c377f59f6


namespace BealeConvexMin.QuadSimplex

end BealeConvexMin.QuadSimplex

open BealeConvexMin.QuadSimplex

theorem checked_lemma1 {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hc : c.IsSymm)
    (p : Fin (N + 1)) (hp : c p p ≠ 0) :
    pivotE (c p) p p = 1 / c p p ∧
    (∀ l, l ≠ p → pivotE (c p) p l = -c p l / c p p) ∧
    ∀ k, k ≠ p → pivotC c p (c p) p k = 0 ∧ pivotC c p (c p) k p = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pivotE]
  · intro l hl
    simp [pivotE, hl]
  · intro k hk
    have hsym : c k p = c p k := by
      have := congrFun (congrFun hc p) k
      simpa [Matrix.transpose_apply] using this
    refine ⟨?_, ?_⟩
    · simp only [pivotC, pivotCPrime, pivotE, Matrix.of_apply, if_true, hk, if_false]
      field_simp
      ring
    · simp only [pivotC, pivotCPrime, pivotE, Matrix.of_apply, if_true, hk, if_false]
      rw [hsym]
      field_simp
      ring
end

/- Complete attributed body: Sol_BealeConvexMin_QuadSimplex_lemma2 -/
section
-- Prove2me | solution 1 for BealeConvexMin.QuadSimplex.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:43:05.036428+00:00
-- url     : https://prove2.me/submissions/c1d36712-7c9c-4921-be4a-8de44dd5eb79


namespace BealeConvexMin.QuadSimplex

theorem aux_bl2_e_zero {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p l : Fin (N + 1))
    (hlp : l ≠ p) (hl : ∀ k, k ≠ l → c k l = 0 ∧ c l k = 0) :
    pivotE (c p) p l = 0 := by
  have h := (hl p (Ne.symm hlp)).1
  simp [pivotE, hlp, h]

theorem aux_bl2_cprime_row_p {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p l : Fin (N + 1))
    (hlp : l ≠ p) (hl : ∀ k, k ≠ l → c k l = 0 ∧ c l k = 0) :
    pivotCPrime c p (c p) p l = 0 := by
  have he := aux_bl2_e_zero c p l hlp hl
  have h := (hl p (Ne.symm hlp)).1
  simp [pivotCPrime, hlp, h, he]

end BealeConvexMin.QuadSimplex

open BealeConvexMin.QuadSimplex

theorem checked_lemma2 {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (p l : Fin (N + 1))
    (hp : c p p ≠ 0) (hlp : l ≠ p) (hl : ∀ k, k ≠ l → c k l = 0 ∧ c l k = 0) :
    pivotE (c p) p l = 0 ∧
    ∀ k, k ≠ l → pivotC c p (c p) k l = 0 ∧ pivotC c p (c p) l k = 0 := by
  have he := aux_bl2_e_zero c p l hlp hl
  have hrow := aux_bl2_cprime_row_p c p l hlp hl
  refine ⟨he, fun k hk => ⟨?_, ?_⟩⟩
  · by_cases hkp : k = p
    · subst hkp
      simp [pivotC, hrow]
    · have hkl := (hl k hk).1
      have hpl := (hl p (Ne.symm hlp)).1
      simp [pivotC, hkp, pivotCPrime, hlp, hkl, he, hpl]
  · have hlk := (hl k hk).2
    have hlp' := (hl p (Ne.symm hlp)).2
    by_cases hkp : k = p
    · subst hkp
      simp [pivotC, hlp, pivotCPrime, hlp', he]
    · simp [pivotC, hlp, pivotCPrime, hkp, hlk, hlp', he]
end

/- Complete attributed body: Sol_BealeConvexMin_QuadSimplex_cost_decreases -/
section
-- Prove2me | solution 1 for BealeConvexMin.QuadSimplex.cost_decreases
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:56:15.205855+00:00
-- url     : https://prove2.me/submissions/c83522d6-f50b-426b-b622-6cb4651764f9


namespace BealeConvexMin.QuadSimplex

theorem aux_cd_pivotC00 {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (P : Fin (N + 1))
    (hP : P ≠ 0) (d : Fin (N + 1) → ℝ) :
    pivotC c P d 0 0 = c 0 0 + c 0 P * (-d 0 / d P) +
      (c P 0 + c P P * (-d 0 / d P)) * (-d 0 / d P) := by
  have h0 : (0 : Fin (N + 1)) ≠ P := fun h => hP h.symm
  simp only [pivotC, pivotCPrime, pivotE, Matrix.of_apply, if_neg h0]

theorem aux_cd_real (c a b t : ℝ) (ha : a < 0) (ht : 0 < t) (hbt : b * t ≤ -a) :
    c + a * t + (a + b * t) * t < c := by
  have h := mul_neg_of_neg_of_pos (by linarith : 2 * a + b * t < 0) ht
  nlinarith [h]

theorem aux_cd_orient_facts {n N : ℕ} (T : Tableau n N) (p : Fin N) (hsymm : T.c.IsSymm)
    (hlab : LabelsConsistent T) (hpos : BasicPositive T) (hadm : AdmissibleChoice T p) :
    (orient T p).c 0 0 = T.c 0 0 ∧
    (orient T p).c 0 p.succ = (orient T p).c p.succ 0 ∧
    (orient T p).c p.succ 0 < 0 ∧
    ∀ q, (orient T p).row q p.succ < 0 → 0 < (orient T p).row q 0 := by
  have hs : ∀ i j, T.c i j = T.c j i := fun i j => (hsymm.apply j i)
  have hne : (0 : Fin (N + 1)) ≠ p.succ := (Fin.succ_ne_zero p).symm
  unfold orient
  split_ifs with hc
  · have hfree : T.lab p = none := by
      rcases hadm.1 with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · exact absurd h (not_lt.mpr hc.le)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [negateSlot, hne]
    · simp [negateSlot, hne, hs 0 p.succ]
    · simp [negateSlot, hne]; linarith
    · intro q hq
      simp only [negateSlot, if_neg hne] at hq ⊢
      apply hpos
      intro k hk
      have hrowq := congrFun (hlab.2 k q hk) p.succ
      have hkp : k ≠ p := by
        rintro rfl
        rw [hfree] at hk
        cases hk
      rw [hrowq, Pi.single_apply, if_neg (fun h => hkp (Fin.succ_injective _ h).symm)] at hq
      simp at hq
  · refine ⟨rfl, hs 0 p.succ, ?_, ?_⟩
    · rcases hadm.1 with ⟨_, h⟩ | ⟨_, h⟩
      · push Not at hc; exact lt_of_le_of_ne hc h
      · exact h
    · intro q hq
      apply hpos
      intro k hk
      have hrowq := congrFun (hlab.2 k q hk) p.succ
      rw [hrowq, Pi.single_apply] at hq
      split_ifs at hq <;> linarith

end BealeConvexMin.QuadSimplex

open BealeConvexMin.QuadSimplex

theorem checked_cost_decreases {n N : ℕ} (T T' : Tableau n N) (hsymm : T.c.IsSymm)
    (hlab : LabelsConsistent T) (hpos : BasicPositive T) (hstep : BealeStep T T') :
    T'.c 0 0 < T.c 0 0 := by
  obtain ⟨p, hadm, hcase⟩ := hstep
  obtain ⟨h00, hsym, ha, hrow⟩ := aux_cd_orient_facts T p hsymm hlab hpos hadm
  have hP : p.succ ≠ 0 := Fin.succ_ne_zero p
  rcases hcase with ⟨q, ⟨hqneg, _⟩, hb, rfl⟩ | ⟨hb, _, rfl⟩
  · show pivotC (orient T p).c p.succ ((orient T p).row q) 0 0 < T.c 0 0
    rw [aux_cd_pivotC00 _ _ hP, hsym, h00]
    have hd0 := hrow q hqneg
    have htpos : 0 < -(orient T p).row q 0 / (orient T p).row q p.succ := by
      rw [neg_div, ← div_neg]; exact div_pos hd0 (neg_pos.mpr hqneg)
    have hratio : ratio (orient T p) p q =
        -(orient T p).row q 0 / (orient T p).row q p.succ := by
      simp only [ratio]; rw [div_neg, neg_div]
    rw [hratio] at hb
    generalize -(orient T p).row q 0 / (orient T p).row q p.succ = t at htpos hb ⊢
    apply aux_cd_real _ _ _ _ ha htpos
    rcases hb with hb | hb
    · nlinarith
    · by_cases hbpos : 0 < (orient T p).c p.succ p.succ
      · rw [le_div_iff₀ hbpos] at hb; linarith
      · push Not at hbpos; nlinarith
  · show pivotC (orient T p).c p.succ ((orient T p).c p.succ) 0 0 < T.c 0 0
    rw [aux_cd_pivotC00 _ _ hP, hsym, h00]
    have hbt : (orient T p).c p.succ p.succ *
        (-(orient T p).c p.succ 0 / (orient T p).c p.succ p.succ) = -(orient T p).c p.succ 0 := by
      field_simp
    have htpos : 0 < -(orient T p).c p.succ 0 / (orient T p).c p.succ p.succ :=
      div_pos (neg_pos.mpr ha) hb
    exact aux_cd_real _ _ _ _ ha htpos hbt.le
end

/- Complete attributed body: Sol_BealeConvexMin_QuadSimplex_standard_form_minimal -/
section
-- Prove2me | solution 1 for BealeConvexMin.QuadSimplex.standard_form_minimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:45:50.906985+00:00
-- url     : https://prove2.me/submissions/f5632da7-5eac-47bc-9a5b-26a54f294717


namespace BealeConvexMin.QuadSimplex

theorem aux_sfm_lin {n N : ℕ} (T : Tableau n N) (hstd : IsStandardForm T)
    (z : Fin (N + 1) → ℝ)
    (hzres : ∀ k : Fin N, T.lab k ≠ none → z k.succ = 0) (i : Fin N) :
    T.c i.succ 0 * z i.succ = 0 := by
  by_cases h : T.lab i = none
  · rw [hstd i h, zero_mul]
  · rw [hzres i h, mul_zero]

end BealeConvexMin.QuadSimplex

open BealeConvexMin.QuadSimplex

theorem checked_standard_form_minimal {n N : ℕ} (T : Tableau n N) (hsymm : T.c.IsSymm)
    (hpsd : (T.c.submatrix Fin.succ Fin.succ).PosSemidef) (hstd : IsStandardForm T)
    (z : Fin (N + 1) → ℝ) (hz0 : z 0 = 1)
    (hzres : ∀ k : Fin N, T.lab k ≠ none → z k.succ = 0) :
    T.c 0 0 ≤ quadValue T.c z := by
  have hq := hpsd.dotProduct_mulVec_nonneg (fun i => z i.succ)
  simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.submatrix_apply] at hq
  have hsym : ∀ i j, T.c i j = T.c j i := fun i j => by
    have := congrFun (congrFun hsymm j) i
    simpa [Matrix.transpose_apply] using this
  have h1 : ∀ i : Fin N, T.c 0 i.succ * z i.succ = 0 := fun i => by
    rw [hsym]; exact aux_sfm_lin T hstd z hzres i
  have h2 : ∀ i : Fin N, T.c i.succ 0 * z i.succ = 0 := fun i =>
    aux_sfm_lin T hstd z hzres i
  unfold quadValue
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ (f := fun l => T.c _ l * z _ * z l), hz0, mul_one, h1, h2,
    Finset.sum_const_zero, add_zero, zero_add]
  have : ∑ i : Fin N, z i.succ * ∑ j : Fin N, T.c i.succ j.succ * z j.succ
      = ∑ i : Fin N, ∑ j : Fin N, T.c i.succ j.succ * z i.succ * z j.succ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  linarith
end

/- Complete attributed body: Sol_BealeConvexMin_QuadSimplex_optimality_criterion -/
section
-- Prove2me | solution 1 for BealeConvexMin.QuadSimplex.optimality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:33:24.470379+00:00
-- url     : https://prove2.me/submissions/7ff0a3db-abfc-4432-8dd0-2fd9503f430e


namespace BealeConvexMin.QuadSimplex

theorem aux_optcrit_lin {n N : ℕ} (T : Tableau n N)
    (hopt : ∀ k : Fin N, ¬ IsProfitable T k)
    (z : Fin (N + 1) → ℝ)
    (hzres : ∀ k : Fin N, T.lab k ≠ none → 0 ≤ z k.succ) (k : Fin N) :
    0 ≤ T.c k.succ 0 * z k.succ := by
  have h := hopt k
  unfold IsProfitable at h
  push Not at h
  by_cases hl : T.lab k = none
  · have := h.1 hl
    rw [this, zero_mul]
  · exact mul_nonneg (h.2 hl) (hzres k hl)

theorem aux_optcrit_quad {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hpsd : (c.submatrix Fin.succ Fin.succ).PosSemidef) (z : Fin (N + 1) → ℝ) :
    0 ≤ ∑ k : Fin N, ∑ l : Fin N, c k.succ l.succ * z k.succ * z l.succ := by
  have h := hpsd.dotProduct_mulVec_nonneg (fun k => z k.succ)
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, star_trivial,
    Finset.mul_sum] at h
  refine le_of_le_of_eq h (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_)
  ring

end BealeConvexMin.QuadSimplex

open BealeConvexMin.QuadSimplex

theorem checked_optimality_criterion {n N : ℕ} (T : Tableau n N) (hsymm : T.c.IsSymm)
    (hpsd : (T.c.submatrix Fin.succ Fin.succ).PosSemidef)
    (hopt : ∀ k : Fin N, ¬ IsProfitable T k)
    (z : Fin (N + 1) → ℝ) (hz0 : z 0 = 1)
    (hzres : ∀ k : Fin N, T.lab k ≠ none → 0 ≤ z k.succ)
    (_hrow : ∀ j : Fin n, 0 ≤ ∑ l, T.row j l * z l) :
    T.c 0 0 ≤ quadValue T.c z := by
  have hq := aux_optcrit_quad T.c hpsd z
  have hl : 0 ≤ ∑ k : Fin N, T.c k.succ 0 * z k.succ :=
    Finset.sum_nonneg fun k _ => aux_optcrit_lin T hopt z hzres k
  have hs : ∀ l : Fin N, T.c 0 l.succ = T.c l.succ 0 := fun l => hsymm.apply l.succ 0
  unfold quadValue
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ (fun l => T.c _ l * _ * z l), hz0, hs, Finset.sum_add_distrib]
  simp only [mul_one]
  linarith
end






end

/- Complete checked body: CoordinateTransport -/
section

namespace BealeConvexMin.QuadSimplexProof
open BealeConvexMin.QuadSimplex Matrix

/-- A later coordinate vector can be evaluated in the earlier tableau without changing
its constant coordinate, any restricted-variable value, or its objective value. -/
def Transports {n N : ℕ} (T U : Tableau n N) : Prop :=
  ∀ z : Fin (N+1) → ℝ, ∃ w : Fin (N+1) → ℝ,
    w 0 = z 0 ∧ (∀ j, T.row j ⬝ᵥ w = U.row j ⬝ᵥ z) ∧ quadValue T.c w = quadValue U.c z

theorem transports_refl {n N : ℕ} (T : Tableau n N) : Transports T T := by
  intro z
  exact ⟨z,rfl,fun _ => rfl,rfl⟩

theorem Transports.trans {n N : ℕ} {T U W : Tableau n N}
    (hTU : Transports T U) (hUW : Transports U W) : Transports T W := by
  intro z
  obtain ⟨v,hv0,hvr,hvc⟩ := hUW z
  obtain ⟨w,hw0,hwr,hwc⟩ := hTU v
  exact ⟨w,hw0.trans hv0,fun j => (hwr j).trans (hvr j),hwc.trans hvc⟩

theorem row_substitution {N : ℕ} (r e : Fin (N+1) → ℝ) (p : Fin (N+1))
    (z : Fin (N+1) → ℝ) :
    r ⬝ᵥ Function.update z p (∑ l, e l*z l) = substVec r e p ⬝ᵥ z := by
  have hr : vecMul r (aux_q37_S e p) = substVec r e p := by
    funext l
    change ((Matrix.of fun (_ : Fin (N+1)) j => r j) * aux_q37_S e p) 0 l = _
    rw [aux_q37_mulS]
    rfl
  rw [aux_q37_update, dotProduct_mulVec, hr]

theorem transports_pivot {n N : ℕ} (T : Tableau n N) (p : Fin N)
    (d : Fin (N+1) → ℝ) (lab : Option (Fin n)) : Transports T (pivotTableau T p d lab) := by
  intro z
  refine ⟨Function.update z p.succ (∑ l, pivotE d p.succ l*z l),?_,?_,?_⟩
  · simp only [Function.update_of_ne (Fin.succ_ne_zero p).symm]
  · intro j
    exact row_substitution (T.row j) (pivotE d p.succ) p.succ z
  · exact (checked_pivotC_formula_37 T.c p.succ d).2.2.2.2.2 z

theorem transports_negate {n N : ℕ} (T : Tableau n N) (p : Fin N) :
    Transports T (negateSlot T p) := by
  intro z
  let w : Fin (N+1) → ℝ := fun l => if l = p.succ then -z l else z l
  refine ⟨w,?_,?_,?_⟩
  · simp only [w, if_neg (Fin.succ_ne_zero p).symm]
  · intro j
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : l = p.succ <;> simp [w,negateSlot,hl]
  · unfold quadValue
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hk : k = p.succ <;> by_cases hl : l = p.succ <;>
      simp [w,negateSlot,hk,hl]

theorem transports_orient {n N : ℕ} (T : Tableau n N) (p : Fin N) :
    Transports T (orient T p) := by
  unfold orient
  split_ifs
  · exact transports_negate T p
  · exact transports_refl T

theorem bealeStep_transports {n N : ℕ} {T U : Tableau n N} (h : BealeStep T U) :
    Transports T U := by
  obtain ⟨p,_,h⟩ := h
  rcases h with ⟨q,_,_,rfl⟩ | ⟨_,_,rfl⟩
  · exact (transports_orient T p).trans (transports_pivot _ p _ _)
  · exact (transports_orient T p).trans (transports_pivot _ p _ _)

theorem run_transports {n N : ℕ} (T : ℕ → Tableau n N)
    (hstep : ∀ k, BealeStep (T k) (T (k+1))) {i j : ℕ} (hij : i ≤ j) :
    Transports (T i) (T j) := by
  induction j,hij using Nat.le_induction with
  | base => exact transports_refl _
  | succ k _ ih => exact ih.trans (bealeStep_transports (hstep k))

end BealeConvexMin.QuadSimplexProof

end

/- Complete checked body: QuadraticTransport -/
section

namespace BealeConvexMin.QuadSimplexProof
open BealeConvexMin.QuadSimplex Matrix

theorem quadValue_zero_coordinate {N : ℕ} (c : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (z : Fin (N+1) → ℝ) (hz : z 0 = 0) :
    quadValue c z = (fun i : Fin N => z i.succ) ⬝ᵥ
      (c.submatrix Fin.succ Fin.succ *ᵥ (fun i : Fin N => z i.succ)) := by
  simp only [quadValue,Fin.sum_univ_succ,hz,zero_mul,mul_zero,Finset.sum_const_zero,
    zero_add,dotProduct,Matrix.mulVec,Matrix.submatrix_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem Transports.posSemidef {n N : ℕ} {T U : Tableau n N} (h : Transports T U)
    (hT : (T.c.submatrix Fin.succ Fin.succ).PosSemidef) (hU : U.c.IsSymm) :
    (U.c.submatrix Fin.succ Fin.succ).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (Matrix.isHermitian_iff_isSymm.mpr (hU.submatrix Fin.succ))
  intro y
  let z : Fin (N+1) → ℝ := Fin.cons 0 y
  obtain ⟨w,hw0,_,hwc⟩ := h z
  have hw : w 0 = 0 := hw0
  have hn := hT.dotProduct_mulVec_nonneg (fun i => w i.succ)
  simp only [star_trivial] at hn ⊢
  rw [← quadValue_zero_coordinate T.c w hw,hwc,quadValue_zero_coordinate U.c z rfl] at hn
  exact hn

end BealeConvexMin.QuadSimplexProof

end

/- Complete checked body: SlotBasics -/
section

set_option autoImplicit false

namespace BealeConvexMin.QuadSimplexProof
open BealeConvexMin.QuadSimplex

variable {n N : ℕ}

def IsIsolatedSlot (T : Tableau n N) (p : Fin N) : Prop :=
  ∀ k : Fin (N+1), k ≠ p.succ → T.c k p.succ = 0 ∧ T.c p.succ k = 0

noncomputable def isolatedFree (T : Tableau n N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun p => T.lab p = none ∧ IsIsolatedSlot T p)

@[simp] theorem mem_isolatedFree (T : Tableau n N) (p : Fin N) :
    p ∈ isolatedFree T ↔ T.lab p = none ∧ IsIsolatedSlot T p := by
  classical
  simp [isolatedFree]

theorem isolatedFree_card_le (T : Tableau n N) : (isolatedFree T).card ≤ N := by
  simpa using Finset.card_le_card (Finset.subset_univ (isolatedFree T))

@[simp] theorem orient_lab_eq (T : Tableau n N) (p : Fin N) :
    (orient T p).lab = T.lab := by
  unfold orient
  split_ifs <;> rfl

theorem orient_isSymm (T : Tableau n N) (p : Fin N) (hs : T.c.IsSymm) :
    (orient T p).c.IsSymm := by
  unfold orient
  split_ifs
  · apply Matrix.IsSymm.ext
    intro i j
    change (if j = p.succ then (-1:ℝ) else 1) *
        (if i = p.succ then (-1:ℝ) else 1) * T.c j i =
      (if i = p.succ then (-1:ℝ) else 1) *
        (if j = p.succ then (-1:ℝ) else 1) * T.c i j
    rw [hs.apply i j]
    ring
  · exact hs

theorem isolated_orient (T : Tableau n N) (p l : Fin N) (hl : IsIsolatedSlot T l) :
    IsIsolatedSlot (orient T p) l := by
  unfold orient
  split_ifs
  · intro k hk
    obtain ⟨h1,h2⟩ := hl k hk
    constructor <;> simp only [negateSlot,Matrix.of_apply,h1,h2,mul_zero]
  · exact hl

theorem exists_free_profitable_of_not_standard (T : Tableau n N)
    (h : ¬ IsStandardForm T) : ∃ p : Fin N, T.lab p = none ∧ T.c p.succ 0 ≠ 0 := by
  unfold IsStandardForm at h
  push Not at h
  exact h

theorem nonstandard_choice_free (T : Tableau n N) (p : Fin N)
    (h : ¬ IsStandardForm T) (hp : AdmissibleChoice T p) : T.lab p = none :=
  hp.2 (exists_free_profitable_of_not_standard T h)

theorem profitable_not_isolated (T : Tableau n N) (p : Fin N)
    (hp : IsProfitable T p) : ¬ IsIsolatedSlot T p := by
  intro hi
  have he := (hi 0 (Fin.succ_ne_zero p).symm).2
  rcases hp with ⟨_,h⟩ | ⟨_,h⟩
  · exact h he
  · linarith

theorem numFree_pivot_none (T : Tableau n N) (p : Fin N)
    (d : Fin (N+1) → ℝ) (hp : T.lab p = none) :
    numFree (pivotTableau T p d none) = numFree T := by
  classical
  have he : Function.update T.lab p none = T.lab := by
    funext k
    by_cases hk : k=p
    · subst k
      simp [hp]
    · simp [hk]
  simp only [numFree,pivotTableau,he]

theorem numFree_pivot_some (T : Tableau n N) (p : Fin N)
    (d : Fin (N+1) → ℝ) (q : Fin n) (hp : T.lab p = none) :
    numFree (pivotTableau T p d (some q)) + 1 = numFree T := by
  classical
  have he : Finset.univ.filter (fun k : Fin N => (Function.update T.lab p (some q)) k = none) =
      (Finset.univ.filter (fun k : Fin N => T.lab k = none)).erase p := by
    ext k
    by_cases hk : k=p
    · subst k
      simp
    · simp [Function.update_apply,hk]
  unfold numFree
  change (Finset.univ.filter (fun k : Fin N => (Function.update T.lab p (some q)) k = none)).card + 1 = _
  rw [he]
  exact Finset.card_erase_add_one (by simp [hp])

end BealeConvexMin.QuadSimplexProof

end

/- Complete checked body: LabelInvariants -/
section

namespace BealeConvexMin.QuadSimplexProof
open BealeConvexMin.QuadSimplex

theorem substVec_of_zero {N : ℕ} (r e : Fin (N+1) → ℝ) (p : Fin (N+1))
    (hr : r p = 0) : substVec r e p = r := by
  funext l
  by_cases hl : l = p <;> simp [substVec,hl,hr]

theorem pivotRow_self {N : ℕ} (d : Fin (N+1) → ℝ) (p : Fin (N+1)) (hp : d p ≠ 0) :
    pivotRow d p d = Pi.single p 1 := by
  funext l
  by_cases hl : l = p
  · subst l
    simp [pivotRow,substVec,pivotE,hp]
  · simp only [pivotRow,substVec,pivotE,Pi.single_apply,if_neg hl]
    field_simp [hp]
    ring

theorem negate_labels_consistent {n N : ℕ} (T : Tableau n N) (p : Fin N)
    (h : LabelsConsistent T) (hfree : T.lab p = none) : LabelsConsistent (negateSlot T p) := by
  refine ⟨h.1,?_⟩
  intro k j hk
  have hkT : T.lab k = some j := hk
  have hkp : k ≠ p := by
    rintro rfl
    rw [hfree] at hkT
    cases hkT
  funext l
  change (if l=p.succ then -T.row j l else T.row j l) = _
  rw [h.2 k j hkT]
  by_cases hl : l=p.succ
  · subst l
    simp [hkp]
  · simp [hl]

theorem orient_labels_consistent {n N : ℕ} (T : Tableau n N) (p : Fin N)
    (h : LabelsConsistent T) (hadm : AdmissibleChoice T p) : LabelsConsistent (orient T p) := by
  unfold orient
  split_ifs with hp
  · apply negate_labels_consistent T p h
    rcases hadm.1 with ⟨hf,_⟩ | ⟨_,hn⟩
    · exact hf
    · exact (not_lt_of_ge hp.le hn).elim
  · exact h

theorem pivot_labels_consistent {n N : ℕ} (T : Tableau n N) (p : Fin N)
    (d : Fin (N+1) → ℝ) (lab : Option (Fin n)) (h : LabelsConsistent T)
    (hnew : ∀ j, lab = some j → IsBasic T j ∧ pivotRow (T.row j) p.succ d = Pi.single p.succ 1) :
    LabelsConsistent (pivotTableau T p d lab) := by
  constructor
  · intro k l j hk hl
    change Function.update T.lab p lab k = some j at hk
    change Function.update T.lab p lab l = some j at hl
    by_cases hkp : k=p
    · subst k
      rw [Function.update_self] at hk
      by_cases hlp : l=p
      · exact hlp.symm
      · rw [Function.update_of_ne hlp] at hl
        exact ((hnew j hk).1 l hl).elim
    · rw [Function.update_of_ne hkp] at hk
      by_cases hlp : l=p
      · subst l
        rw [Function.update_self] at hl
        exact ((hnew j hl).1 k hk).elim
      · rw [Function.update_of_ne hlp] at hl
        exact h.1 k l j hk hl
  · intro k j hk
    change Function.update T.lab p lab k = some j at hk
    change pivotRow (T.row j) p.succ d = Pi.single k.succ 1
    by_cases hkp : k=p
    · subst k
      rw [Function.update_self] at hk
      exact (hnew j hk).2
    · rw [Function.update_of_ne hkp] at hk
      rw [h.2 k j hk]
      apply substVec_of_zero
      simp [hkp]

theorem basic_of_negative_row {n N : ℕ} (T : Tableau n N) (h : LabelsConsistent T)
    (q : Fin n) (p : Fin N) (hn : T.row q p.succ < 0) : IsBasic T q := by
  intro k hk
  rw [h.2 k q hk] at hn
  by_cases hkp : k=p <;> norm_num [hkp] at hn

theorem bealeStep_labels_consistent {n N : ℕ} {T U : Tableau n N}
    (hT : LabelsConsistent T) (hstep : BealeStep T U) : LabelsConsistent U := by
  obtain ⟨p,hadm,hstep⟩ := hstep
  have ho := orient_labels_consistent T p hT hadm
  rcases hstep with ⟨q,hq,_,rfl⟩ | ⟨_,_,rfl⟩
  · apply pivot_labels_consistent _ p _ _ ho
    intro j hj
    have hqj : q=j := Option.some.inj hj
    subst j
    exact ⟨basic_of_negative_row _ ho q p hq.1,pivotRow_self _ _ hq.1.ne⟩
  · apply pivot_labels_consistent _ p _ _ ho
    intro j hj
    cases hj

end BealeConvexMin.QuadSimplexProof

end

/- Complete checked body: StepInvariants -/
section

namespace BealeConvexMin.QuadSimplexProof
open BealeConvexMin.QuadSimplex

theorem bealeStep_isSymm {n N : ℕ} {T U : Tableau n N}
    (hT : T.c.IsSymm) (hstep : BealeStep T U) : U.c.IsSymm := by
  obtain ⟨p,_,hstep⟩ := hstep
  have ho := orient_isSymm T p hT
  rcases hstep with ⟨q,_,_,rfl⟩ | ⟨_,_,rfl⟩
  · exact (checked_pivotC_formula_37 _ _ _).2.2.2.2.1 ho
  · exact (checked_pivotC_formula_37 _ _ _).2.2.2.2.1 ho

theorem bealeStep_invariants {n N : ℕ} {T U : Tableau n N}
    (hs : T.c.IsSymm) (hp : (T.c.submatrix Fin.succ Fin.succ).PosSemidef)
    (hl : LabelsConsistent T) (hstep : BealeStep T U) :
    U.c.IsSymm ∧ (U.c.submatrix Fin.succ Fin.succ).PosSemidef ∧ LabelsConsistent U := by
  have hsU := bealeStep_isSymm hs hstep
  exact ⟨hsU,(bealeStep_transports hstep).posSemidef hp hsU,
    bealeStep_labels_consistent hl hstep⟩

theorem run_invariants {n N : ℕ} (T : ℕ → Tableau n N)
    (hs : (T 0).c.IsSymm) (hp : ((T 0).c.submatrix Fin.succ Fin.succ).PosSemidef)
    (hl : LabelsConsistent (T 0)) (hstep : ∀ k, BealeStep (T k) (T (k+1))) :
    ∀ k, (T k).c.IsSymm ∧ ((T k).c.submatrix Fin.succ Fin.succ).PosSemidef ∧
      LabelsConsistent (T k) := by
  intro k
  induction k with
  | zero => exact ⟨hs,hp,hl⟩
  | succ k ih => exact bealeStep_invariants ih.1 ih.2.1 ih.2.2 (hstep k)

end BealeConvexMin.QuadSimplexProof

end

/- Complete checked body: NoReturn -/
section

namespace BealeConvexMin.QuadSimplexProof
open BealeConvexMin.QuadSimplex Matrix

theorem quadValue_associated {N : ℕ} (c : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    quadValue c (Pi.single 0 1) = c 0 0 := by
  simp [quadValue,Pi.single_apply]

theorem same_restricted_cost_ge {n N : ℕ} {T U : Tableau n N}
    (htrans : Transports T U) (hs : T.c.IsSymm)
    (hp : (T.c.submatrix Fin.succ Fin.succ).PosSemidef)
    (hlT : LabelsConsistent T) (hlU : LabelsConsistent U)
    (hstd : IsStandardForm T) (hset : restrictedNonbasic T = restrictedNonbasic U) :
    T.c 0 0 ≤ U.c 0 0 := by
  let z : Fin (N+1) → ℝ := Pi.single 0 1
  obtain ⟨w,hw0,hwr,hwc⟩ := htrans z
  have h0 : w 0 = 1 := by simpa [z] using hw0
  have hzero (k : Fin N) (hk : T.lab k ≠ none) : w k.succ = 0 := by
    cases htk : T.lab k with
    | none => exact (hk htk).elim
    | some r =>
      have hrT : r ∈ restrictedNonbasic T := ⟨k,htk⟩
      have hrU : r ∈ restrictedNonbasic U := hset ▸ hrT
      obtain ⟨l,hl⟩ := hrU
      have hh := hwr r
      rw [hlT.2 k r htk,hlU.2 l r hl] at hh
      simpa [z] using hh
  have hb := checked_standard_form_minimal T hs hp hstd w h0 hzero
  rw [hwc] at hb
  simpa only [z,quadValue_associated] using hb

theorem no_return_standard_form {n N : ℕ} (T : ℕ → Tableau n N)
    (hs : (T 0).c.IsSymm) (hp : ((T 0).c.submatrix Fin.succ Fin.succ).PosSemidef)
    (hl : LabelsConsistent (T 0)) (hstep : ∀ k, BealeStep (T k) (T (k+1)))
    (hpos : ∀ k, BasicPositive (T k)) {i j : ℕ} (hij : i < j)
    (hi : IsStandardForm (T i)) : restrictedNonbasic (T i) ≠ restrictedNonbasic (T j) := by
  intro he
  have hinv := run_invariants T hs hp hl hstep
  have hge := same_restricted_cost_ge (run_transports T hstep hij.le)
    (hinv i).1 (hinv i).2.1 (hinv i).2.2 (hinv j).2.2 hi he
  have hanti : StrictAnti (fun k => (T k).c 0 0) := strictAnti_nat_of_succ_lt (fun k =>
    checked_cost_decreases (T k) (T (k+1)) (hinv k).1 (hinv k).2.2 (hpos k) (hstep k))
  exact (not_lt_of_ge hge) (hanti hij)

end BealeConvexMin.QuadSimplexProof

end

/- Complete checked body: SlotProgress -/
section

set_option autoImplicit false

namespace BealeConvexMin.QuadSimplexProof
open BealeConvexMin.QuadSimplex

variable {n N : ℕ}

theorem isolatedFree_grows_free_pivot (T : Tableau n N) (p : Fin N)
    (hs : T.c.IsSymm) (hp : IsProfitable T p)
    (hd : 0 < (orient T p).c p.succ p.succ) :
    insert p (isolatedFree T) ⊆
      isolatedFree (pivotTableau (orient T p) p ((orient T p).c p.succ) none) := by
  classical
  intro l hl
  rcases Finset.mem_insert.mp hl with heq | hl
  · subst l
    apply (mem_isolatedFree _ p).mpr
    constructor
    · simp [pivotTableau]
    · intro k hk
      have hh := (checked_lemma1 (orient T p).c (orient_isSymm T p hs) p.succ hd.ne').2.2 k hk
      exact ⟨hh.2,hh.1⟩
  · obtain ⟨hlfree,hliso⟩ := (mem_isolatedFree T l).mp hl
    have hlp : l ≠ p := by
      intro he
      apply profitable_not_isolated T p hp
      simpa only [he] using hliso
    have hnew := (checked_lemma2 (orient T p).c p.succ l.succ hd.ne'
      (fun h => hlp (Fin.succ_injective N h)) (isolated_orient T p l hliso)).2
    apply (mem_isolatedFree _ l).mpr
    constructor
    · simp [pivotTableau,hlp,hlfree]
    · exact hnew

noncomputable def progressRank (T : Tableau n N) : ℕ :=
  (N+1)*numFree T + (N-(isolatedFree T).card)

theorem progressRank_decreases (T T' : Tableau n N) (hs : T.c.IsSymm)
    (hstd : ¬ IsStandardForm T) (hstep : BealeStep T T') :
    progressRank T' < progressRank T := by
  classical
  obtain ⟨p,hp,hcase⟩ := hstep
  have hfree := nonstandard_choice_free T p hstd hp
  have hfreeU : (orient T p).lab p = none := by rw [orient_lab_eq]; exact hfree
  have hcountU : numFree (orient T p) = numFree T := by simp only [numFree,orient_lab_eq]
  have hnot : p ∉ isolatedFree T := by
    intro hh
    exact profitable_not_isolated T p hp.1 ((mem_isolatedFree T p).mp hh).2
  rcases hcase with ⟨q,_,_,rfl⟩ | ⟨hd,_,rfl⟩
  · have hcount := numFree_pivot_some (orient T p) p ((orient T p).row q) q hfreeU
    rw [hcountU] at hcount
    have hcard := isolatedFree_card_le T
    have hcard' := isolatedFree_card_le (pivotTableau (orient T p) p ((orient T p).row q) (some q))
    unfold progressRank
    rw [← hcount,Nat.mul_add,Nat.mul_one]
    omega
  · have hcount := numFree_pivot_none (orient T p) p ((orient T p).c p.succ) hfreeU
    rw [hcountU] at hcount
    have hsub := isolatedFree_grows_free_pivot T p hs hp.1 hd
    have hinc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnot] at hinc
    have hcard := isolatedFree_card_le T
    have hcard' := isolatedFree_card_le (pivotTableau (orient T p) p ((orient T p).c p.succ) none)
    unfold progressRank
    rw [hcount]
    omega

end BealeConvexMin.QuadSimplexProof

end

/- Complete checked body: StandardRecurrence -/
section

set_option autoImplicit false

namespace BealeConvexMin.QuadSimplexProof
open BealeConvexMin.QuadSimplex

variable {n N : ℕ}

theorem exists_standard_later (T : ℕ → Tableau n N)
    (hs : ∀ k, (T k).c.IsSymm) (hstep : ∀ k, BealeStep (T k) (T (k+1)))
    (k : ℕ) : ∃ j, k ≤ j ∧ IsStandardForm (T j) := by
  by_contra h
  push Not at h
  have hbound : ∀ m : ℕ, progressRank (T (k+m)) + m ≤ progressRank (T k) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hd := progressRank_decreases (T (k+m)) (T (k+m+1)) (hs (k+m))
        (h (k+m) (Nat.le_add_right k m)) (hstep (k+m))
      have he : k+(m+1)=k+m+1 := by omega
      rw [he]
      omega
  have hh := hbound (progressRank (T k)+1)
  omega

theorem contradiction_of_standard_no_return (T : ℕ → Tableau n N)
    (hs : ∀ k, (T k).c.IsSymm) (hstep : ∀ k, BealeStep (T k) (T (k+1)))
    (hno : ∀ i j, i<j → IsStandardForm (T i) →
      restrictedNonbasic (T i) ≠ restrictedNonbasic (T j)) : False := by
  classical
  let S : Set ℕ := {k | IsStandardForm (T k)}
  have hi : Set.InjOn (fun k => restrictedNonbasic (T k)) S := by
    intro a ha b hb he
    by_contra hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact hno a b hlt ha he
    · exact hno b a hgt hb he.symm
  have hf : S.Finite := Set.Finite.of_finite_image (Set.toFinite _) hi
  obtain ⟨B,hB⟩ := hf.bddAbove
  obtain ⟨j,hj,hstd⟩ := exists_standard_later T hs hstep (B+1)
  have hb : j ≤ B := hB hstd
  omega

end BealeConvexMin.QuadSimplexProof

end

/- Complete checked body: BealeRoot -/
section

namespace BealeConvexMin.QuadSimplex

/-- Beale (1955), §3, p. 177: the iteration for a convex quadratic `C` terminates. From an initial
tableau with symmetric `(c_kl)`, positive semidefinite quadratic block (convex `C`) and consistent
labels, there is no infinite run `T 0 → T 1 → ⋯` of steps along which every basic restricted
variable stays strictly positive in the associated solution (the ε-perturbation device of p. 174,
stated as a hypothesis on the run). -/
theorem iteration_terminates {n N : ℕ} (T₀ : Tableau n N) (hsymm : T₀.c.IsSymm)
    (hpsd : (T₀.c.submatrix Fin.succ Fin.succ).PosSemidef) (hlab : LabelsConsistent T₀) :
    ¬ ∃ T : ℕ → Tableau n N, T 0 = T₀ ∧ (∀ k, BealeStep (T k) (T (k + 1))) ∧
      ∀ k, BasicPositive (T k) := by
  rintro ⟨T,hinit,hstep,hpos⟩
  have hs : (T 0).c.IsSymm := by simpa only [hinit] using hsymm
  have hp : ((T 0).c.submatrix Fin.succ Fin.succ).PosSemidef := by
    simpa only [hinit] using hpsd
  have hl : LabelsConsistent (T 0) := by simpa only [hinit] using hlab
  have hinv := BealeConvexMin.QuadSimplexProof.run_invariants T hs hp hl hstep
  apply BealeConvexMin.QuadSimplexProof.contradiction_of_standard_no_return T
    (fun k => (hinv k).1) hstep
  intro i j hij hi
  exact BealeConvexMin.QuadSimplexProof.no_return_standard_form T hs hp hl hstep hpos hij hi

end BealeConvexMin.QuadSimplex

end

open BealeConvexMin.QuadSimplex

theorem solution {n N : ℕ} (T₀ : Tableau n N) (hsymm : T₀.c.IsSymm)
    (hpsd : (T₀.c.submatrix Fin.succ Fin.succ).PosSemidef) (hlab : LabelsConsistent T₀) :
    ¬ ∃ T : ℕ → Tableau n N, T 0 = T₀ ∧ (∀ k, BealeStep (T k) (T (k + 1))) ∧
      ∀ k, BasicPositive (T k) := by
  exact BealeConvexMin.QuadSimplex.iteration_terminates T₀ hsymm hpsd hlab

#print axioms BealeConvexMin.QuadSimplex.iteration_terminates
#print axioms solution
