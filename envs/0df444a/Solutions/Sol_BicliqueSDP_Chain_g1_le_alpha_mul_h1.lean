-- Prove2me | solution 1 for BicliqueSDP.Chain.g1_le_alpha_mul_h1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:41:58.951185+00:00
-- url     : https://prove2.me/submissions/4d22be8a-f7d3-4c4b-888c-ba7b428c3069

import Mathlib
import Definitions.Def_BicliqueSDP_Chain_Model

open Matrix

noncomputable section

namespace BicliqueSDP.Chain.R4

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma psd_of_bordered {X : Matrix ι ι ℝ} (hX : (bordered X).PosSemidef) :
    X.PosSemidef := by
  exact hX.submatrix (Sum.inr : ι → Unit ⊕ ι)

lemma diag_le_one_of_bordered {X : Matrix ι ι ℝ} (hX : (bordered X).PosSemidef)
    (i : ι) : X i i ≤ 1 := by
  have hd := hX.dotProduct_mulVec_nonneg
    (Pi.single (Sum.inl ()) (-X i i) + Pi.single (Sum.inr i) 1)
  simp [Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    Matrix.mulVec_single, single_dotProduct, bordered, Matrix.fromBlocks] at hd
  nlinarith

lemma trace_le_card_of_bordered {X : Matrix ι ι ℝ}
    (hX : (bordered X).PosSemidef) : X.trace ≤ Fintype.card ι := by
  calc
    X.trace = ∑ i, X i i := rfl
    _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => diag_le_one_of_bordered hX i)
    _ = Fintype.card ι := by simp

omit [Fintype ι] in
lemma bordered_zero_psd : (bordered (0 : Matrix ι ι ℝ)).PosSemidef := by
  have hd : (Matrix.diagonal (fun u : Unit ⊕ ι =>
      match u with | .inl _ => (1 : ℝ) | .inr _ => 0)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro u
    cases u <;> simp
  convert hd using 1
  ext u v
  cases u <;> cases v <;> simp [bordered, Matrix.diagonal, Matrix.fromBlocks]

lemma las1_values_bddAbove (G : SimpleGraph ι) :
    BddAbove ((fun X : Matrix ι ι ℝ => X.trace) ''
      {X | (bordered X).PosSemidef ∧ ∀ i j, G.Adj i j → X i j = 0}) := by
  refine ⟨Fintype.card ι, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  exact trace_le_card_of_bordered hX.1

lemma trace_le_las1 {G : SimpleGraph ι} {X : Matrix ι ι ℝ}
    (hX : (bordered X).PosSemidef) (hE : ∀ i j, G.Adj i j → X i j = 0) :
    X.trace ≤ las1 G := by
  exact le_csSup (las1_values_bddAbove G) ⟨X, ⟨hX, hE⟩, rfl⟩

lemma psd_entry_le_diag_avg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (i j : ι) :
    X i j ≤ (X i i + X j j) / 2 := by
  have hs : X j i = X i j := by simpa using hX.isHermitian.apply i j
  have h := hX.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    Matrix.mulVec_single, single_dotProduct] at h
  linarith

lemma psd_entry_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) (htr : X.trace = 1) (i j : ι) :
    X i j ≤ 1 := by
  have hdiag (k : ι) : X k k ≤ 1 := by
    calc X k k ≤ ∑ l, X l l := Finset.single_le_sum (f := fun l => X l l) (fun l _ => hX.diag_nonneg) (Finset.mem_univ k)
         _ = 1 := htr
  have hpair := psd_entry_le_diag_avg hX i j
  linarith [hdiag i, hdiag j]

variable {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]

lemma h1_objective_bddAbove (E : V1 → V2 → Prop) :
    BddAbove ((fun X => frob Cmat X) '' {X | H1Feasible E X}) := by
  refine ⟨∑ _ : V1 ⊕ V2, ∑ _ : V1 ⊕ V2, (1 : ℝ), ?_⟩
  rintro z ⟨X, hX, rfl⟩
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  have hx := psd_entry_le_one hX.1 hX.2.1 u v
  cases u <;> cases v <;> simp [Cmat, Matrix.fromBlocks] <;> linarith

lemma h1_nonneg (E : V1 → V2 → Prop) : 0 ≤ h1 E := by
  classical
  by_cases hn : Nonempty (V1 ⊕ V2)
  · obtain ⟨u⟩ := hn
    let X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ := Matrix.diagonal (Pi.single u 1)
    have hX : H1Feasible E X := by
      refine ⟨Matrix.PosSemidef.diagonal ?_, ?_, ?_⟩
      · intro v
        simp only [Pi.single_apply]
        split <;> norm_num
      · simp [X, Matrix.trace_diagonal]
      · intro v w hvw
        exact Matrix.diagonal_apply_ne _ hvw.ne
    have hobj : frob Cmat X = 0 := by
      simp [frob, X, Matrix.diagonal, Cmat, Matrix.fromBlocks]
    rw [← hobj]
    exact le_csSup (h1_objective_bddAbove E) ⟨X, hX, rfl⟩
  · have : IsEmpty (V1 ⊕ V2) := not_nonempty_iff.mp hn
    have he : {X | H1Feasible E X} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro X hX
      have ht : X.trace = 0 := by simp [Matrix.trace]
      exact zero_ne_one (ht.symm.trans hX.2.1)
    simp [h1, he]

lemma g1_objective_bddAbove (E : V1 → V2 → Prop) :
    BddAbove ((fun X => frob Cmat X) '' {X | G1Feasible E X}) := by
  refine ⟨∑ _ : V1 ⊕ V2, ∑ _ : V1 ⊕ V2, (1 : ℝ), ?_⟩
  rintro z ⟨X, hX, rfl⟩
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  have hx := psd_entry_le_diag_avg (psd_of_bordered hX.1) u v
  have hu := diag_le_one_of_bordered hX.1 u
  have hv := diag_le_one_of_bordered hX.1 v
  cases u <;> cases v <;> simp [Cmat, Matrix.fromBlocks] <;> linarith

omit [Fintype V1] [Fintype V2] in
lemma g1_zero_feasible (E : V1 → V2 → Prop) :
    G1Feasible E (0 : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ) := by
  exact ⟨bordered_zero_psd, fun _ _ _ => rfl⟩

lemma g1_nonneg (E : V1 → V2 → Prop) : 0 ≤ g1 E := by
  have hmem : 0 ∈ (fun X => frob Cmat X) '' {X | G1Feasible E X} := by
    exact ⟨0, g1_zero_feasible E, by simp [frob]⟩
  exact le_csSup (g1_objective_bddAbove E) hmem

omit [DecidableEq ι] in
lemma frob_smul_right (a : ℝ) (M X : Matrix ι ι ℝ) :
    frob M (a • X) = a * frob M X := by
  simp [frob, Finset.mul_sum, mul_left_comm]

lemma frob_nonpos_of_trace_zero {X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ}
    (hX : X.PosSemidef) (ht : X.trace = 0) : frob Cmat X ≤ 0 := by
  have hdiag (k : V1 ⊕ V2) : X k k ≤ 0 := by
    calc
      X k k ≤ ∑ l, X l l :=
        Finset.single_le_sum (f := fun l => X l l)
          (fun l _ => hX.diag_nonneg) (Finset.mem_univ k)
      _ = 0 := ht
  apply Finset.sum_nonpos
  intro u _
  apply Finset.sum_nonpos
  intro v _
  have hx := psd_entry_le_diag_avg hX u v
  have hu := hdiag u
  have hv := hdiag v
  cases u <;> cases v <;> simp [Cmat, Matrix.fromBlocks] <;> linarith

lemma psd_objective_le_trace_mul_h1 (E : V1 → V2 → Prop)
    {X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ} (hp : X.PosSemidef)
    (hE : VanishesOnEdges E X) :
    frob Cmat X ≤ X.trace * h1 E := by
  obtain ht | ht := eq_or_lt_of_le hp.trace_nonneg
  · rw [← ht, zero_mul]
    exact frob_nonpos_of_trace_zero hp ht.symm
  · have hnorm : H1Feasible E (X.trace⁻¹ • X) := by
      refine ⟨hp.smul (inv_nonneg.mpr ht.le), ?_, ?_⟩
      · simp [Matrix.trace_smul, ht.ne']
      · intro u v huv
        simp [hE u v huv]
    have hle := le_csSup (h1_objective_bddAbove E) ⟨X.trace⁻¹ • X, hnorm, rfl⟩
    change frob Cmat (X.trace⁻¹ • X) ≤ h1 E at hle
    rw [frob_smul_right] at hle
    have := (div_le_iff₀ ht).mp (show frob Cmat X / X.trace ≤ h1 E by
      simpa [div_eq_mul_inv, mul_comm] using hle)
    simpa [mul_comm] using this

lemma g1_objective_le_trace_mul_h1 (E : V1 → V2 → Prop)
    {X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ} (hX : G1Feasible E X) :
    frob Cmat X ≤ X.trace * h1 E :=
  psd_objective_le_trace_mul_h1 E (psd_of_bordered hX.1) hX.2

lemma g1_le_las1_mul_h1 (E : V1 → V2 → Prop) :
    g1 E ≤ las1 (bipGraph E) * h1 E := by
  apply csSup_le
  · exact ⟨frob Cmat 0, 0, g1_zero_feasible E, rfl⟩
  · rintro z ⟨X, hX, rfl⟩
    exact (g1_objective_le_trace_mul_h1 E hX).trans
      (mul_le_mul_of_nonneg_right (trace_le_las1 hX.1 hX.2) (h1_nonneg E))

lemma theta_objective_bddAbove {V : Type} [Fintype V] (G : SimpleGraph V) :
    BddAbove ((fun X : Matrix V V ℝ => ∑ i, ∑ j, X i j) ''
      {X | X.PosSemidef ∧ X.trace = 1 ∧ ∀ i j, G.Adj i j → X i j = 0}) := by
  classical
  refine ⟨∑ _ : V, ∑ _ : V, (1 : ℝ), ?_⟩
  rintro z ⟨X, hX, rfl⟩
  exact Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j _ => psd_entry_le_one hX.1 hX.2.1 i j

lemma sum_le_theta {V : Type} [Fintype V] (G : SimpleGraph V)
    (X : Matrix V V ℝ)
    (hX : X.PosSemidef ∧ X.trace = 1 ∧ ∀ i j, G.Adj i j → X i j = 0) :
    (∑ i, ∑ j, X i j) ≤ theta G := by
  exact le_csSup (theta_objective_bddAbove G) ⟨X, hX, rfl⟩

lemma theta_nonneg {V : Type} [Fintype V] (G : SimpleGraph V) : 0 ≤ theta G := by
  by_cases hn : {X : Matrix V V ℝ | X.PosSemidef ∧ X.trace = 1 ∧
      ∀ i j, G.Adj i j → X i j = 0}.Nonempty
  · obtain ⟨X, hX⟩ := hn
    have hz : 0 ≤ ∑ i, ∑ j, X i j := by
      simpa [dotProduct, Matrix.mulVec] using
        hX.1.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
    exact hz.trans (sum_le_theta G X hX)
  · simp [theta, Set.not_nonempty_iff_eq_empty.mp hn]

omit [DecidableEq ι] in
lemma trace_sq_le_sum_of_bordered {X : Matrix ι ι ℝ}
    (hX : (bordered X).PosSemidef) : X.trace ^ 2 ≤ ∑ i, ∑ j, X i j := by
  have h := hX.dotProduct_mulVec_nonneg
    (Sum.elim (fun _ : Unit => -X.trace) (fun _ : ι => (1 : ℝ)))
  simp [dotProduct, Matrix.mulVec, bordered, Matrix.fromBlocks,
    Fintype.sum_sum_type, Finset.mul_sum,
    Matrix.trace, Matrix.diag] at h ⊢
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul] at h
  nlinarith

omit [DecidableEq ι] in
lemma trace_le_theta {G : SimpleGraph ι} {X : Matrix ι ι ℝ}
    (hX : (bordered X).PosSemidef) (hE : ∀ i j, G.Adj i j → X i j = 0) :
    X.trace ≤ theta G := by
  have hp := psd_of_bordered hX
  obtain ht | ht := eq_or_lt_of_le hp.trace_nonneg
  · rw [← ht]
    exact theta_nonneg G
  · have hnorm : (X.trace⁻¹ • X).PosSemidef ∧ (X.trace⁻¹ • X).trace = 1 ∧
        ∀ i j, G.Adj i j → (X.trace⁻¹ • X) i j = 0 := by
      refine ⟨hp.smul (inv_nonneg.mpr ht.le), ?_, ?_⟩
      · simp [Matrix.trace_smul, ht.ne']
      · intro i j hij
        simp [hE i j hij]
    have hle := sum_le_theta G (X.trace⁻¹ • X) hnorm
    have hdiv : (∑ i, ∑ j, X i j) / X.trace ≤ theta G := by
      simpa [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, mul_comm] using hle
    have hs := (div_le_iff₀ ht).mp hdiv
    have hsq := trace_sq_le_sum_of_bordered hX
    nlinarith

lemma las1_le_theta (G : SimpleGraph ι) : las1 G ≤ theta G := by
  apply csSup_le
  · refine ⟨0, 0, ⟨bordered_zero_psd, ?_⟩, by simp⟩
    intro i j _
    rfl
  · rintro z ⟨X, hX, rfl⟩
    exact trace_le_theta hX.1 hX.2

lemma g1_le_theta_mul_h1 (E : V1 → V2 → Prop) :
    g1 E ≤ theta (bipGraph E) * h1 E := by
  exact (g1_le_las1_mul_h1 E).trans
    (mul_le_mul_of_nonneg_right (las1_le_theta (bipGraph E)) (h1_nonneg E))


end BicliqueSDP.Chain.R4

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators

namespace BicliqueSDP.Chain.FractionalAlpha

noncomputable section

lemma integrable_interval_indicator (l u c : ℝ) :
    Integrable ((Ioc l u).indicator (fun _ : ℝ => c)) := by
  apply (integrable_indicator_iff measurableSet_Ioc).2
  exact integrableOn_const (by simp [Real.volume_Ioc])

lemma integral_interval_indicator (l u c : ℝ) (h : l ≤ u) :
    (∫ t : ℝ, (Ioc l u).indicator (fun _ : ℝ => c) t) = (u - l) * c := by
  rw [integral_indicator_const c measurableSet_Ioc, Real.volume_real_Ioc_of_le h,
    smul_eq_mul]

theorem fractional_biindep_sum_le_alpha
    {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1] [DecidableEq V2]
    (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)]
    (a : V1 → ℝ) (b : V2 → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1)
    (hab : ∀ i j, E i j → a i + b j ≤ 1) :
    (∑ i, a i) + (∑ j, b j) ≤ alpha E := by
  classical
  let F : ℝ → ℝ := fun t => ∑ i, (Ioc 0 (a i)).indicator (fun _ => (1 : ℝ)) t
  let G : ℝ → ℝ := fun t => ∑ j, (Ioc (1 - b j) 1).indicator (fun _ => (1 : ℝ)) t
  have hF : Integrable F :=
    integrable_finsetSum _ (fun i _ => integrable_interval_indicator 0 (a i) 1)
  have hG : Integrable G :=
    integrable_finsetSum _ (fun j _ => integrable_interval_indicator (1 - b j) 1 1)
  have hpoint (t : ℝ) : F t + G t ≤ (Ioc (0 : ℝ) 1).indicator (fun _ => alpha E) t := by
    let A : Finset V1 := Finset.univ.filter (fun i => t ∈ Ioc 0 (a i))
    let B : Finset V2 := Finset.univ.filter (fun j => t ∈ Ioc (1 - b j) 1)
    have hFcard : F t = (A.card : ℝ) := by
      simp [F, A, Set.indicator_apply]
    have hGcard : G t = (B.card : ℝ) := by
      simp [G, B, Set.indicator_apply]
    have hpair : (A, B) ∈ pairs E := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro i hi j hj hij
      have hi' : 0 < t ∧ t ≤ a i := (Finset.mem_filter.mp hi).2
      have hj' : 1 - b j < t ∧ t ≤ 1 := (Finset.mem_filter.mp hj).2
      have hedge := hab i j hij
      linarith
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · rw [Set.indicator_of_mem ht, hFcard, hGcard]
      exact Finset.le_sup' (fun p => (p.1.card : ℝ) + p.2.card) hpair
    · rw [Set.indicator_of_notMem ht]
      have hA : A = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hi' : 0 < t ∧ t ≤ a i := (Finset.mem_filter.mp hi).2
        exact ht ⟨hi'.1, hi'.2.trans (ha i).2⟩
      have hB : B = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        have hj' : 1 - b j < t ∧ t ≤ 1 := (Finset.mem_filter.mp hj).2
        exact ht ⟨by linarith [(hb j).2], hj'.2⟩
      simp [hFcard, hGcard, hA, hB]
  have hFA : (∫ t : ℝ, F t) = ∑ i, a i := by
    dsimp [F]
    rw [integral_finsetSum _ (fun i _ => integrable_interval_indicator 0 (a i) 1)]
    apply Finset.sum_congr rfl
    intro i _
    simpa using integral_interval_indicator 0 (a i) 1 (ha i).1
  have hGB : (∫ t : ℝ, G t) = ∑ j, b j := by
    dsimp [G]
    rw [integral_finsetSum _ (fun j _ => integrable_interval_indicator (1 - b j) 1 1)]
    apply Finset.sum_congr rfl
    intro j _
    have h := integral_interval_indicator (1 - b j) 1 1 (by linarith [(hb j).1])
    simpa using h
  have hbound := integral_mono (hF.add hG)
    (integrable_interval_indicator 0 1 (alpha E)) hpoint
  rw [integral_add' hF hG, hFA, hGB,
    integral_interval_indicator 0 1 (alpha E) (by norm_num)] at hbound
  simpa using hbound

end

end BicliqueSDP.Chain.FractionalAlpha

namespace BicliqueSDP.Chain.R4

lemma diag_add_le_one_of_bordered {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : (bordered X).PosSemidef) (i j : ι)
    (hij : X i j = 0) : X i i + X j j ≤ 1 := by
  have hji : X j i = 0 := by
    have hs : X j i = X i j := by simpa using (psd_of_bordered hX).isHermitian.apply i j
    exact hs.trans hij
  have hq := hX.dotProduct_mulVec_nonneg
    (Pi.single (Sum.inl ()) (-(X i i + X j j)) +
      Pi.single (Sum.inr i) 1 + Pi.single (Sum.inr j) 1)
  simp [Matrix.mulVec_add, add_dotProduct, dotProduct_add,
    Matrix.mulVec_single, single_dotProduct, bordered, Matrix.fromBlocks,
    hij, hji] at hq
  nlinarith

lemma g1_edge_diag_add_le_one {V1 V2 : Type} [Fintype V1] [Fintype V2]
    [DecidableEq V1] [DecidableEq V2] (E : V1 → V2 → Prop)
    {X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ} (hX : G1Feasible E X)
    (i : V1) (j : V2) (hij : E i j) :
    X (Sum.inl i) (Sum.inl i) + X (Sum.inr j) (Sum.inr j) ≤ 1 := by
  apply diag_add_le_one_of_bordered hX.1
  exact hX.2 _ _ hij


lemma trace_le_alpha {V1 V2 : Type} [Fintype V1] [Fintype V2]
    [DecidableEq V1] [DecidableEq V2] (E : V1 → V2 → Prop)
    [∀ i j, Decidable (E i j)]
    {X : Matrix (V1 ⊕ V2) (V1 ⊕ V2) ℝ} (hX : G1Feasible E X) :
    X.trace ≤ alpha E := by
  have hp := psd_of_bordered hX.1
  have h := FractionalAlpha.fractional_biindep_sum_le_alpha E
    (fun i => X (Sum.inl i) (Sum.inl i))
    (fun j => X (Sum.inr j) (Sum.inr j))
    (fun i => ⟨hp.diag_nonneg, diag_le_one_of_bordered hX.1 (Sum.inl i)⟩)
    (fun j => ⟨hp.diag_nonneg, diag_le_one_of_bordered hX.1 (Sum.inr j)⟩)
    (fun i j hij => g1_edge_diag_add_le_one E hX i j hij)
  simpa [Matrix.trace, Matrix.diag, Fintype.sum_sum_type] using h

end BicliqueSDP.Chain.R4

open BicliqueSDP.Chain

/-- §3.3, p. 18: `g₁(G) ≤ α(G) h₁(G)`. -/
theorem solution {V1 V2 : Type} [Fintype V1] [Fintype V2] [DecidableEq V1]
    [DecidableEq V2] (E : V1 → V2 → Prop) [∀ i j, Decidable (E i j)] :
    g1 E ≤ alpha E * h1 E := by
  apply csSup_le
  · exact ⟨frob Cmat 0, 0, R4.g1_zero_feasible E, rfl⟩
  · rintro z ⟨X, hX, rfl⟩
    exact (R4.g1_objective_le_trace_mul_h1 E hX).trans
      (mul_le_mul_of_nonneg_right (R4.trace_le_alpha E hX) (R4.h1_nonneg E))
