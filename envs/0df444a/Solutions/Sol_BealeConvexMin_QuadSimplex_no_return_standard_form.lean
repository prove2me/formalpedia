-- Prove2me | solution 1 for BealeConvexMin.QuadSimplex.no_return_standard_form
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T07:38:31.637001+00:00
-- url     : https://prove2.me/submissions/71e3998a-a293-492a-a5a2-faa09dcc78ad

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep



namespace BealeConvexMin.QuadSimplex

def nrS {N : ℕ} (e : Fin (N + 1) → ℝ) (P : Fin (N + 1)) (z : Fin (N + 1) → ℝ) :
    Fin (N + 1) → ℝ :=
  fun l => if l = P then ∑ m, e m * z m else z l

theorem nr_substVec_dot {N : ℕ} (v e : Fin (N + 1) → ℝ) (P : Fin (N + 1))
    (z : Fin (N + 1) → ℝ) :
    ∑ l, substVec v e P l * z l = ∑ l, v l * nrS e P z l := by
  have h1 : ∀ l, substVec v e P l * z l =
      v l * z l + v P * (e l * z l) - (if l = P then v P * z P else 0) := by
    intro l; unfold substVec; split_ifs with h
    · subst h; ring
    · ring
  have h2 : ∀ l, v l * nrS e P z l =
      v l * z l + (if l = P then v P * (∑ m, e m * z m) - v P * z P else 0) := by
    intro l; unfold nrS; split_ifs with h
    · subst h; ring
    · ring
  simp only [h1, h2, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, ← Finset.mul_sum]
  ring

theorem nr_quad_eq {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (z : Fin (N + 1) → ℝ) :
    quadValue c z = ∑ k, z k * ∑ l, c k l * z l := by
  unfold quadValue
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_; ring

theorem nr_quad_pivotC {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (P : Fin (N + 1))
    (d z : Fin (N + 1) → ℝ) :
    quadValue (pivotC c P d) z = quadValue c (nrS (pivotE d P) P z) := by
  set e := pivotE d P
  have hcp : ∀ k, (fun l => pivotCPrime c P d k l) = substVec (c k) e P := by
    intro k; funext l; simp [pivotCPrime, substVec, e]
  have hc : ∀ l, (fun k => pivotC c P d k l) = substVec (fun k => pivotCPrime c P d k l) e P := by
    intro l; funext k; simp [pivotC, substVec, e]
  have step1 : quadValue (pivotC c P d) z =
      ∑ l, z l * ∑ k, pivotC c P d k l * z k := by
    unfold quadValue
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
  rw [step1]
  have step2 : ∀ l, ∑ k, pivotC c P d k l * z k =
      ∑ k, pivotCPrime c P d k l * nrS e P z k := by
    intro l
    have := nr_substVec_dot (fun k => pivotCPrime c P d k l) e P z
    rw [← this, ← hc l]
  simp only [step2]
  have step3 : ∑ l, z l * ∑ k, pivotCPrime c P d k l * nrS e P z k =
      ∑ k, nrS e P z k * ∑ l, pivotCPrime c P d k l * z l := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_; ring
  rw [step3, nr_quad_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have := nr_substVec_dot (c k) e P z
  rw [← this, ← hcp k]


def NRRel {n N : ℕ} (T T' : Tableau n N) : Prop :=
  ∀ z' : Fin (N + 1) → ℝ, ∃ z : Fin (N + 1) → ℝ, z 0 = z' 0 ∧
    quadValue T.c z = quadValue T'.c z' ∧
    ∀ j, ∑ l, T.row j l * z l = ∑ l, T'.row j l * z' l

theorem nrRel_refl {n N : ℕ} (T : Tableau n N) : NRRel T T :=
  fun z' => ⟨z', rfl, rfl, fun _ => rfl⟩

theorem nrRel_trans {n N : ℕ} {T1 T2 T3 : Tableau n N} (h12 : NRRel T1 T2) (h23 : NRRel T2 T3) :
    NRRel T1 T3 := by
  intro z3
  obtain ⟨z2, a2, b2, c2⟩ := h23 z3
  obtain ⟨z1, a1, b1, c1⟩ := h12 z2
  exact ⟨z1, a1.trans a2, b1.trans b2, fun j => (c1 j).trans (c2 j)⟩

theorem nrRel_negate {n N : ℕ} (T : Tableau n N) (p : Fin N) : NRRel T (negateSlot T p) := by
  intro z'
  refine ⟨fun l => if l = p.succ then -z' l else z' l, ?_, ?_, ?_⟩
  · simp [(Fin.succ_ne_zero p).symm]
  · unfold quadValue
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [negateSlot, Matrix.of_apply]
    split_ifs <;> ring
  · intro j
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [negateSlot]
    split_ifs <;> ring

theorem nrRel_orient {n N : ℕ} (T : Tableau n N) (p : Fin N) : NRRel T (orient T p) := by
  unfold orient; split_ifs
  · exact nrRel_negate T p
  · exact nrRel_refl T

theorem nrRel_pivot {n N : ℕ} (T : Tableau n N) (p : Fin N) (d : Fin (N + 1) → ℝ)
    (nl : Option (Fin n)) : NRRel T (pivotTableau T p d nl) := by
  intro z'
  refine ⟨nrS (pivotE d p.succ) p.succ z', ?_, ?_, ?_⟩
  · simp [nrS, (Fin.succ_ne_zero p).symm]
  · exact (nr_quad_pivotC _ _ _ _).symm
  · intro j
    exact (nr_substVec_dot _ _ _ _).symm

theorem nrRel_step {n N : ℕ} (T T' : Tableau n N) (h : BealeStep T T') : NRRel T T' := by
  obtain ⟨p, _, hc⟩ := h
  refine nrRel_trans (nrRel_orient T p) ?_
  rcases hc with ⟨q, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact nrRel_pivot _ _ _ _

theorem nr_symm_orient {n N : ℕ} (T : Tableau n N) (p : Fin N) (hs : T.c.IsSymm) :
    (orient T p).c.IsSymm := by
  unfold orient; split_ifs
  · apply Matrix.IsSymm.ext
    intro i j
    simp only [negateSlot, Matrix.of_apply, hs.apply i j]
    ring
  · exact hs

theorem nr_symm_pivotC {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (P : Fin (N + 1))
    (d : Fin (N + 1) → ℝ) (hs : c.IsSymm) : (pivotC c P d).IsSymm := by
  have h : ∀ i j, c j i = c i j := fun i j => hs.apply i j
  apply Matrix.IsSymm.ext
  intro i j
  simp only [pivotC, pivotCPrime, Matrix.of_apply]
  by_cases hi : i = P <;> by_cases hj : j = P
  · subst hi; subst hj; rfl
  · subst hi; simp only [hj, if_true, if_false]; linear_combination pivotE d i i * h i j
  · subst hj; simp only [hi, if_true, if_false]; linear_combination pivotE d j j * h i j
  · simp only [hi, hj, if_false]; rw [h i j, h i P, h j P]; ring


theorem nr_free_of_pos {n N : ℕ} (T : Tableau n N) (p : Fin N) (hadm : AdmissibleChoice T p)
    (hc : 0 < T.c p.succ 0) : T.lab p = none := by
  rcases hadm.1 with ⟨h, _⟩ | ⟨_, h⟩
  · exact h
  · exact absurd h (not_lt.mpr hc.le)

theorem nr_lc_orient {n N : ℕ} (T : Tableau n N) (p : Fin N) (hadm : AdmissibleChoice T p)
    (hlab : LabelsConsistent T) : LabelsConsistent (orient T p) := by
  unfold orient; split_ifs with hc
  · have hfree := nr_free_of_pos T p hadm hc
    refine ⟨hlab.1, ?_⟩
    intro k j hk
    change T.lab k = some j at hk
    have hkp : k ≠ p := by rintro rfl; rw [hfree] at hk; cases hk
    have hr := hlab.2 k j hk
    funext l
    simp only [negateSlot, hr]
    split_ifs with hl
    · subst hl
      rw [Pi.single_apply, if_neg (fun h => hkp (Fin.succ_injective _ h).symm)]; simp
    · rfl
  · exact hlab

theorem nr_pivotRow_single {N : ℕ} (k p : Fin N) (hkp : k ≠ p) (d : Fin (N + 1) → ℝ) :
    pivotRow (Pi.single k.succ 1) p.succ d = Pi.single k.succ 1 := by
  have h0 : (Pi.single k.succ (1:ℝ) : Fin (N+1) → ℝ) p.succ = 0 := by
    rw [Pi.single_apply, if_neg (fun h => hkp (Fin.succ_injective _ h).symm)]
  funext l
  simp only [pivotRow, substVec, h0, zero_mul, add_zero]
  split_ifs with hl
  · subst hl; exact h0.symm
  · rfl

theorem nr_lc_pivot_free {n N : ℕ} (U : Tableau n N) (p : Fin N) (d : Fin (N + 1) → ℝ)
    (hlab : LabelsConsistent U) : LabelsConsistent (pivotTableau U p d none) := by
  refine ⟨?_, ?_⟩
  · intro k k' j hk hk'
    simp only [pivotTableau] at hk hk'
    by_cases h1 : k = p
    · subst h1; simp at hk
    by_cases h2 : k' = p
    · subst h2; simp at hk'
    rw [Function.update_of_ne h1] at hk
    rw [Function.update_of_ne h2] at hk'
    exact hlab.1 k k' j hk hk'
  · intro k j hk
    simp only [pivotTableau] at hk ⊢
    by_cases h1 : k = p
    · subst h1; simp at hk
    rw [Function.update_of_ne h1] at hk
    rw [hlab.2 k j hk]
    exact nr_pivotRow_single k p h1 d

theorem nr_lc_pivot_some {n N : ℕ} (U : Tableau n N) (p : Fin N) (q : Fin n)
    (hq : U.row q p.succ < 0)
    (hlab : LabelsConsistent U) : LabelsConsistent (pivotTableau U p (U.row q) (some q)) := by
  have hnot : ∀ k, k ≠ p → U.lab k ≠ some q := by
    intro k hkp hk
    have := congrFun (hlab.2 k q hk) p.succ
    rw [Pi.single_apply, if_neg (fun h => hkp (Fin.succ_injective _ h).symm)] at this
    linarith
  refine ⟨?_, ?_⟩
  · intro k k' j hk hk'
    simp only [pivotTableau] at hk hk'
    by_cases h1 : k = p <;> by_cases h2 : k' = p
    · rw [h1, h2]
    · subst h1; simp at hk; subst hk
      rw [Function.update_of_ne h2] at hk'; exact absurd hk' (hnot k' h2)
    · subst h2; simp at hk'; subst hk'
      rw [Function.update_of_ne h1] at hk; exact absurd hk (hnot k h1)
    · rw [Function.update_of_ne h1] at hk
      rw [Function.update_of_ne h2] at hk'
      exact hlab.1 k k' j hk hk'
  · intro k j hk
    simp only [pivotTableau] at hk ⊢
    by_cases h1 : k = p
    · subst h1; simp at hk; subst hk
      have hne : U.row q k.succ ≠ 0 := hq.ne
      funext l
      simp only [pivotRow, substVec, pivotE, Pi.single_apply]
      split_ifs with hl
      · subst hl; field_simp
      · field_simp; ring
    rw [Function.update_of_ne h1] at hk
    rw [hlab.2 k j hk]
    exact nr_pivotRow_single k p h1 _

theorem nr_inv_step {n N : ℕ} (T T' : Tableau n N) (h : BealeStep T T') (hs : T.c.IsSymm)
    (hlab : LabelsConsistent T) : T'.c.IsSymm ∧ LabelsConsistent T' := by
  obtain ⟨p, hadm, hc⟩ := h
  have hs' := nr_symm_orient T p hs
  have hl' := nr_lc_orient T p hadm hlab
  rcases hc with ⟨q, hq, _, rfl⟩ | ⟨_, _, rfl⟩
  · exact ⟨nr_symm_pivotC _ _ _ hs', nr_lc_pivot_some _ p q hq.1 hl'⟩
  · exact ⟨nr_symm_pivotC _ _ _ hs', nr_lc_pivot_free _ p _ hl'⟩

theorem nr_cd_pivotC00 {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (P : Fin (N + 1))
    (hP : P ≠ 0) (d : Fin (N + 1) → ℝ) :
    pivotC c P d 0 0 = c 0 0 + c 0 P * (-d 0 / d P) +
      (c P 0 + c P P * (-d 0 / d P)) * (-d 0 / d P) := by
  have h0 : (0 : Fin (N + 1)) ≠ P := fun h => hP h.symm
  simp only [pivotC, pivotCPrime, pivotE, Matrix.of_apply, if_neg h0]

theorem nr_cd_real (c a b t : ℝ) (ha : a < 0) (ht : 0 < t) (hbt : b * t ≤ -a) :
    c + a * t + (a + b * t) * t < c := by
  have h := mul_neg_of_neg_of_pos (by linarith : 2 * a + b * t < 0) ht
  nlinarith [h]

theorem nr_cd_orient_facts {n N : ℕ} (T : Tableau n N) (p : Fin N) (hsymm : T.c.IsSymm)
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

theorem nr_cost_decreases {n N : ℕ} (T T' : Tableau n N) (hsymm : T.c.IsSymm)
    (hlab : LabelsConsistent T) (hpos : BasicPositive T) (hstep : BealeStep T T') :
    T'.c 0 0 < T.c 0 0 := by
  obtain ⟨p, hadm, hcase⟩ := hstep
  obtain ⟨h00, hsym, ha, hrow⟩ := nr_cd_orient_facts T p hsymm hlab hpos hadm
  have hP : p.succ ≠ 0 := Fin.succ_ne_zero p
  rcases hcase with ⟨q, ⟨hqneg, _⟩, hb, rfl⟩ | ⟨hb, _, rfl⟩
  · show pivotC (orient T p).c p.succ ((orient T p).row q) 0 0 < T.c 0 0
    rw [nr_cd_pivotC00 _ _ hP, hsym, h00]
    have hd0 := hrow q hqneg
    have htpos : 0 < -(orient T p).row q 0 / (orient T p).row q p.succ := by
      rw [neg_div, ← div_neg]; exact div_pos hd0 (neg_pos.mpr hqneg)
    have hratio : ratio (orient T p) p q =
        -(orient T p).row q 0 / (orient T p).row q p.succ := by
      simp only [ratio]; rw [div_neg, neg_div]
    rw [hratio] at hb
    generalize -(orient T p).row q 0 / (orient T p).row q p.succ = t at htpos hb ⊢
    apply nr_cd_real _ _ _ _ ha htpos
    rcases hb with hb | hb
    · nlinarith
    · by_cases hbpos : 0 < (orient T p).c p.succ p.succ
      · rw [le_div_iff₀ hbpos] at hb; linarith
      · push Not at hbpos; nlinarith
  · show pivotC (orient T p).c p.succ ((orient T p).c p.succ) 0 0 < T.c 0 0
    rw [nr_cd_pivotC00 _ _ hP, hsym, h00]
    have hbt : (orient T p).c p.succ p.succ *
        (-(orient T p).c p.succ 0 / (orient T p).c p.succ p.succ) = -(orient T p).c p.succ 0 := by
      field_simp
    have htpos : 0 < -(orient T p).c p.succ 0 / (orient T p).c p.succ p.succ :=
      div_pos (neg_pos.mpr ha) hb
    exact nr_cd_real _ _ _ _ ha htpos hbt.le

theorem nr_qnonneg_of_psd {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hpsd : (c.submatrix Fin.succ Fin.succ).PosSemidef) (w : Fin (N + 1) → ℝ) (hw : w 0 = 0) :
    0 ≤ quadValue c w := by
  have hq := hpsd.dotProduct_mulVec_nonneg (fun i => w i.succ)
  simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.submatrix_apply] at hq
  rw [nr_quad_eq, Fin.sum_univ_succ, hw, zero_mul, zero_add]
  refine le_of_le_of_eq hq (Finset.sum_congr rfl fun i _ => ?_)
  rw [Fin.sum_univ_succ (f := fun l => c i.succ l * w l), hw, mul_zero, zero_add]

theorem nr_min {n N : ℕ} (T : Tableau n N) (hsymm : T.c.IsSymm)
    (hq : ∀ w : Fin (N + 1) → ℝ, w 0 = 0 → 0 ≤ quadValue T.c w) (hstd : IsStandardForm T)
    (z : Fin (N + 1) → ℝ) (hz0 : z 0 = 1)
    (hzres : ∀ k : Fin N, T.lab k ≠ none → z k.succ = 0) :
    T.c 0 0 ≤ quadValue T.c z := by
  have hsym : ∀ i j, T.c i j = T.c j i := fun i j => hsymm.apply j i
  have h2 : ∀ i : Fin N, T.c i.succ 0 * z i.succ = 0 := fun i => by
    by_cases h : T.lab i = none
    · rw [hstd i h, zero_mul]
    · rw [hzres i h, mul_zero]
  have h1 : ∀ i : Fin N, T.c 0 i.succ * z i.succ = 0 := fun i => by rw [hsym]; exact h2 i
  have hw := hq (Function.update z 0 0) (by simp)
  have e1 : quadValue T.c z = T.c 0 0 +
      ∑ i : Fin N, z i.succ * ∑ j : Fin N, T.c i.succ j.succ * z j.succ := by
    rw [nr_quad_eq, Fin.sum_univ_succ]
    simp only [Fin.sum_univ_succ (f := fun l => T.c _ l * z l), hz0, one_mul, mul_one]
    have : ∀ i : Fin N, z i.succ * (T.c i.succ 0 + ∑ j : Fin N, T.c i.succ j.succ * z j.succ)
        = T.c i.succ 0 * z i.succ + z i.succ * ∑ j : Fin N, T.c i.succ j.succ * z j.succ := by
      intro i; ring
    simp only [this, Finset.sum_add_distrib, h1, h2, Finset.sum_const_zero]
    ring
  have e2 : quadValue T.c (Function.update z 0 0) =
      ∑ i : Fin N, z i.succ * ∑ j : Fin N, T.c i.succ j.succ * z j.succ := by
    rw [nr_quad_eq, Fin.sum_univ_succ]
    simp [Fin.sum_univ_succ (f := fun l => T.c _ l * Function.update z 0 0 l),
      ]
  linarith


theorem nr_core {n N : ℕ} (T : ℕ → Tableau n N) (hsymm : (T 0).c.IsSymm)
    (hpsd : ((T 0).c.submatrix Fin.succ Fin.succ).PosSemidef) (hlab : LabelsConsistent (T 0))
    {i j : ℕ} (hij : i < j) (hstep : ∀ k < j, BealeStep (T k) (T (k + 1)))
    (hpos : ∀ k ≤ j, BasicPositive (T k))
    (hi : IsStandardForm (T i)) (hj : IsStandardForm (T j)) :
    restrictedNonbasic (T i) ≠ restrictedNonbasic (T j) := by
  have inv : ∀ k ≤ j, (T k).c.IsSymm ∧ LabelsConsistent (T k) := by
    intro k hk
    induction k with
    | zero => exact ⟨hsymm, hlab⟩
    | succ k ih =>
      obtain ⟨a, b⟩ := ih (by omega)
      exact nr_inv_step _ _ (hstep k (by omega)) a b
  have rel : ∀ a b, a ≤ b → b ≤ j → NRRel (T a) (T b) := by
    intro a b hab hb
    induction b, hab using Nat.le_induction with
    | base => exact nrRel_refl _
    | succ b _ ih => exact nrRel_trans (ih (by omega)) (nrRel_step _ _ (hstep b (by omega)))
  have dec : ∀ b, i < b → b ≤ j → (T b).c 0 0 < (T i).c 0 0 := by
    intro b hib hb
    induction b, hib using Nat.le_induction with
    | base =>
      obtain ⟨a, b⟩ := inv i (by omega)
      exact nr_cost_decreases _ _ a b (hpos i (by omega)) (hstep i (by omega))
    | succ b hb' ih =>
      obtain ⟨a, c⟩ := inv b (by omega)
      have := nr_cost_decreases _ _ a c (hpos b (by omega)) (hstep b (by omega))
      linarith [ih (by omega)]
  intro heq
  have hqi : ∀ w : Fin (N + 1) → ℝ, w 0 = 0 → 0 ≤ quadValue (T i).c w := by
    intro w' hw'
    obtain ⟨w, hw0, hwq, _⟩ := rel 0 i (by omega) (by omega) w'
    rw [← hwq]
    exact nr_qnonneg_of_psd _ hpsd w (hw0.trans hw')
  obtain ⟨z, hz0, hzq, hzr⟩ := rel i j hij.le le_rfl (Pi.single 0 1)
  have hqj : quadValue (T j).c (Pi.single 0 1) = (T j).c 0 0 := by
    unfold quadValue
    simp [Pi.single_apply]
  have hres : ∀ k : Fin N, (T i).lab k ≠ none → z k.succ = 0 := by
    intro k hk
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hk
    have hrow := (inv i hij.le).2.2 k r hr
    have h1 := hzr r
    rw [hrow] at h1
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    have hmem : r ∈ restrictedNonbasic (T j) := heq ▸ ⟨k, hr⟩
    obtain ⟨k', hk'⟩ := hmem
    rw [(inv j le_rfl).2.2 k' r hk'] at h1
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, (Fin.succ_ne_zero k').symm, if_false] at h1
    exact h1
  have hmin := nr_min (T i) (inv i hij.le).1 hqi hi z (by simpa using hz0) hres
  rw [hzq, hqj] at hmin
  linarith [dec j hij le_rfl]

end BealeConvexMin.QuadSimplex

open BealeConvexMin.QuadSimplex


theorem solution {n N : ℕ} (T : ℕ → Tableau n N) (hsymm : (T 0).c.IsSymm)
    (hpsd : ((T 0).c.submatrix Fin.succ Fin.succ).PosSemidef) (hlab : LabelsConsistent (T 0))
    {i j : ℕ} (hij : i < j) (hstep : ∀ k < j, BealeStep (T k) (T (k + 1)))
    (hpos : ∀ k ≤ j, BasicPositive (T k))
    (hi : IsStandardForm (T i)) (hj : IsStandardForm (T j)) :
    restrictedNonbasic (T i) ≠ restrictedNonbasic (T j) := by
  exact nr_core T hsymm hpsd hlab hij hstep hpos hi hj
