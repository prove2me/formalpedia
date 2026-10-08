-- Prove2me | solution 1 for BurkholderDFI.Gundy.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:17:43.210892+00:00
-- url     : https://prove2.me/submissions/e948a8da-ad9e-4783-b62b-b9f01521a6fc

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal


namespace BurkholderDFI.Gundy
open BurkholderDFI.SquareFnLp

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

/-- `|f_n|` with the convention `f_0 = 0`. -/
noncomputable def absZ (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun n ω => if n = 0 then 0 else |f n ω|

lemma absZ_nonneg (f : ℕ → Ω → ℝ) : 0 ≤ absZ f := by
  intro n ω
  simp only [absZ, Pi.zero_apply]
  split_ifs <;> simp [abs_nonneg]

lemma absZ_pos (f : ℕ → Ω → ℝ) {n : ℕ} (hn : 1 ≤ n) : absZ f n = fun ω => |f n ω| := by
  funext ω; simp [absZ, Nat.one_le_iff_ne_zero.mp hn]

lemma absZ_zero (f : ℕ → Ω → ℝ) : absZ f 0 = 0 := by
  funext ω; simp [absZ]

lemma absZ_submartingale [IsFiniteMeasure P]
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)) :
    Submartingale (absZ f) ℱ P := by
  have hsub : Submartingale f ℱ P := hf.elim (fun h => h.submartingale) (fun h => h.1)
  have hadp : StronglyAdapted ℱ (absZ f) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [absZ_zero]; exact stronglyMeasurable_const
    · rw [absZ_pos f hn]
      have := (hsub.stronglyAdapted n).norm
      simpa [Real.norm_eq_abs] using this
  have hint : ∀ n, Integrable (absZ f n) P := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [absZ_zero]; exact integrable_zero _ _ _
    · rw [absZ_pos f hn]; exact (hsub.integrable n).abs
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [absZ_zero]
    exact condExp_nonneg (Eventually.of_forall (absZ_nonneg f j))
  · have hj : 1 ≤ j := le_trans hi hij
    rw [absZ_pos f hi, absZ_pos f hj]
    rcases hf with hm | ⟨hs, hnn⟩
    · have h := (hm.submartingale.sup hm.neg.submartingale).2.1 i j hij
      have e : ∀ k, (f ⊔ -f) k = fun ω => |f k ω| := by
        intro k; funext ω; simp [abs_eq_max_neg]
      simpa [e] using h
    · have h1 := hs.2.1 i j hij
      have e1 : f i =ᵐ[P] fun ω => |f i ω| := by
        filter_upwards [hnn i hi] with ω hω; simp [abs_of_nonneg hω]
      have e2 : f j =ᵐ[P] fun ω => |f j ω| := by
        filter_upwards [hnn j hj] with ω hω; simp [abs_of_nonneg hω]
      have h2 : P[f j | ℱ i] =ᵐ[P] P[fun ω => |f j ω| | ℱ i] := condExp_congr_ae e2
      filter_upwards [h1, e1, h2] with ω h1 e1 h2
      rw [← e1, ← h2]; exact h1


/-! ### `f` with the convention `f_0 = 0` -/

/-- `f_n` with `f_0 = 0`. -/
noncomputable def gZ (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun n ω => if n = 0 then 0 else f n ω

lemma gZ_zero (f : ℕ → Ω → ℝ) : gZ f 0 = 0 := by funext ω; simp [gZ]

lemma gZ_pos (f : ℕ → Ω → ℝ) {n : ℕ} (hn : 1 ≤ n) : gZ f n = f n := by
  funext ω; simp [gZ, Nat.one_le_iff_ne_zero.mp hn]

lemma valAt_coe (f : ℕ → Ω → ℝ) (fInf : Ω → ℝ) (k : ℕ) (ω : Ω) :
    valAt f fInf (k : ℕ∞) ω = gZ f k ω := by
  by_cases hk : k = 0
  · subst hk; simp [valAt, gZ]
  · simp [valAt, gZ, hk]

lemma valAt_top (f : ℕ → Ω → ℝ) (fInf : Ω → ℝ) (ω : Ω) : valAt f fInf ⊤ ω = fInf ω := by
  simp [valAt]

lemma sqFnAt_coe (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : sqFnAt f (k : ℕ∞) ω = sqFnN f k ω := by
  simp [sqFnAt]

lemma sqFnAt_top (f : ℕ → Ω → ℝ) (ω : Ω) : sqFnAt f ⊤ ω = sqFn f ω := by
  simp [sqFnAt]

lemma dseq_eq_gZ (f : ℕ → Ω → ℝ) {k : ℕ} (hk : 1 ≤ k) (ω : Ω) :
    dseq f k ω = gZ f k ω - gZ f (k - 1) ω := by
  rcases Nat.exists_eq_add_of_le' hk with ⟨m, rfl⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [dseq, gZ]
  · simp [dseq, gZ, Nat.one_le_iff_ne_zero.mp hm]

lemma gZ_sq_identity (f : ℕ → Ω → ℝ) (ω : Ω) (n : ℕ) :
    gZ f n ω ^ 2 = ∑ k ∈ Finset.Icc 1 n, dseq f k ω ^ 2
      + 2 * ∑ k ∈ Finset.Icc 1 n, gZ f (k - 1) ω * dseq f k ω := by
  induction n with
  | zero => simp [gZ]
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have hd : dseq f (m + 1) ω = gZ f (m + 1) ω - gZ f m ω := by
      rw [dseq_eq_gZ f (by omega)]; simp
    simp only [Nat.add_sub_cancel]
    rw [hd]
    linear_combination ih

/-- The finite identity behind Lemma 2.1: for `n ≥ 1`,
`S_{n-1}² + f_{n-1}² + 2 Σ_{k ≤ n} f_{k-1} d_k = 2 f_n f_{n-1}`. -/
lemma stopped_identity (f : ℕ → Ω → ℝ) (ω : Ω) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 (n - 1), dseq f k ω ^ 2 + gZ f (n - 1) ω ^ 2
      + 2 * ∑ k ∈ Finset.Icc 1 n, gZ f (k - 1) ω * dseq f k ω
      = 2 * (gZ f n ω * gZ f (n - 1) ω) := by
  rcases Nat.exists_eq_add_of_le' hn with ⟨m, rfl⟩
  simp only [Nat.add_sub_cancel]
  rw [Finset.sum_Icc_succ_top (by omega)]
  have := gZ_sq_identity f ω m
  have hd : dseq f (m + 1) ω = gZ f (m + 1) ω - gZ f m ω := by
    rw [dseq_eq_gZ f (by omega)]; simp
  simp only [Nat.add_sub_cancel]
  rw [hd]
  nlinarith [this]

/-! ### The exit time -/

lemma one_le_exitTime (f : ℕ → Ω → ℝ) (l : ℝ) (ω : Ω) : 1 ≤ exitTime f l ω :=
  le_iInf₂ fun n hn => by exact_mod_cast hn.1

lemma exitTime_le_of (f : ℕ → Ω → ℝ) (l : ℝ) (ω : Ω) {n : ℕ} (hn : 1 ≤ n) (h : l < |f n ω|) :
    exitTime f l ω ≤ n :=
  iInf₂_le n ⟨hn, h⟩

lemma abs_gZ_le_of_lt_exitTime (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) (ω : Ω) {k : ℕ}
    (hk : (k : ℕ∞) < exitTime f l ω) : |gZ f k ω| ≤ l := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp [gZ, hl.le]
  · rw [gZ_pos f hk1]
    by_contra h
    push_neg at h
    exact absurd (exitTime_le_of f l ω hk1 h) (not_le.mpr hk)

lemma exitTime_le_iff (f : ℕ → Ω → ℝ) (l : ℝ) (ω : Ω) (n : ℕ) :
    exitTime f l ω ≤ n ↔ ∃ k, 1 ≤ k ∧ k ≤ n ∧ l < |f k ω| := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have : ((n + 1 : ℕ) : ℕ∞) ≤ exitTime f l ω := by
      refine le_iInf₂ fun k hk => ?_
      have : n + 1 ≤ k := by
        by_contra hlt; push_neg at hlt
        exact absurd hk.2 (not_lt.mpr (hcon k hk.1 (by omega)))
      exact_mod_cast this
    have h2 := this.trans h
    have h3 : n + 1 ≤ n := by exact_mod_cast h2
    omega
  · rintro ⟨k, hk1, hkn, hk⟩
    exact (exitTime_le_of f l ω hk1 hk).trans (by exact_mod_cast hkn)

lemma isStoppingTime_exitTime (hadp : StronglyAdapted ℱ f) (l : ℝ) :
    IsStoppingTime ℱ (exitTime f l) := by
  intro n
  have : {ω | exitTime f l ω ≤ (n : ℕ∞)} = ⋃ k ∈ Finset.Icc 1 n, {ω | l < ‖f k ω‖} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Icc, exists_prop, Real.norm_eq_abs]
    rw [exitTime_le_iff]
    constructor
    · rintro ⟨k, h1, h2, h3⟩; exact ⟨k, ⟨h1, h2⟩, h3⟩
    · rintro ⟨k, ⟨h1, h2⟩, h3⟩; exact ⟨k, h1, h2, h3⟩
  have key : MeasurableSet[ℱ n] {ω | exitTime f l ω ≤ (n : ℕ∞)} := by
    rw [this]
    refine Finset.measurableSet_biUnion _ fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hm : Measurable[ℱ k] fun ω => ‖f k ω‖ := (hadp k).norm.measurable
    have hc : Measurable[ℱ k] fun _ : Ω => l := measurable_const
    have hs : MeasurableSet[ℱ k] {ω | l < ‖f k ω‖} := measurableSet_lt hc hm
    exact ℱ.mono hk.2 _ hs
  exact key

/-! ### Measurability helpers -/

lemma measurable_comp_nat {F : ℕ → Ω → ℝ} (hF : ∀ k, Measurable (F k)) {t : Ω → ℕ}
    (ht : Measurable t) : Measurable fun ω => F (t ω) ω := by
  have h : Measurable fun p : Ω × ℕ => F p.2 p.1 :=
    measurable_from_prod_countable_left (fun k => hF k)
  exact h.comp (measurable_id.prodMk ht)

lemma measurable_comp_enat {F : ℕ∞ → Ω → ℝ} (hF : ∀ k, Measurable (F k)) {t : Ω → ℕ∞}
    (ht : Measurable t) : Measurable fun ω => F (t ω) ω := by
  have h : Measurable fun p : Ω × ℕ∞ => F p.2 p.1 :=
    measurable_from_prod_countable_left (fun k => hF k)
  exact h.comp (measurable_id.prodMk ht)

lemma measurable_gZ (hadp : StronglyAdapted ℱ f) (k : ℕ) : Measurable (gZ f k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [gZ_zero]; exact measurable_const
  · rw [gZ_pos f hk]; exact (hadp k).measurable.le (ℱ.le k)

lemma measurable_dseq (hadp : StronglyAdapted ℱ f) (k : ℕ) : Measurable (dseq f k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : dseq f 0 = fun _ => 0 := by funext ω; simp [dseq]
    rw [this]; exact measurable_const
  · have : dseq f k = fun ω => gZ f k ω - gZ f (k - 1) ω := by
      funext ω; exact dseq_eq_gZ f hk ω
    rw [this]; exact (measurable_gZ hadp k).sub (measurable_gZ hadp (k - 1))

lemma measurable_valAt (hadp : StronglyAdapted ℱ f) {g : Ω → ℝ} (hg : Measurable g)
    {μ : Ω → ℕ∞} (hμ : Measurable μ) : Measurable fun ω => valAt f g (μ ω) ω := by
  refine measurable_comp_enat (F := fun m ω => valAt f g m ω) (fun m => ?_) hμ
  induction m using ENat.recTopCoe with
  | top => simp only [valAt_top]; exact hg
  | coe k => simp only [valAt_coe]; exact measurable_gZ hadp k


/-! ### The predictable terms `1_{k ≤ μ} f_{k-1} d_k` -/

/-- `1_{k ≤ μ} f_{k-1} d_k`. -/
noncomputable def term (f : ℕ → Ω → ℝ) (l : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if (k : ℕ∞) ≤ exitTime f l ω then gZ f (k - 1) ω * dseq f k ω else 0

lemma term_eq (f : ℕ → Ω → ℝ) (l : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    term f l k = fun ω =>
      Set.indicator {ω | (k : ℕ∞) ≤ exitTime f l ω} (gZ f (k - 1)) ω * (f k ω - gZ f (k - 1) ω) := by
  funext ω
  simp only [term]
  by_cases h : (k : ℕ∞) ≤ exitTime f l ω
  · simp [Set.indicator_of_mem, h, dseq_eq_gZ f hk, gZ_pos f hk]
  · simp [Set.indicator_of_notMem, h]

lemma term_facts [IsProbabilityMeasure P]
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    {l : ℝ} (hl : 0 < l) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (term f l k) P ∧ 0 ≤ ∫ ω, term f l k ω ∂P ∧
      (Martingale f ℱ P → ∫ ω, term f l k ω ∂P = 0) := by
  have hsub : Submartingale f ℱ P := hf.elim (fun h => h.submartingale) (fun h => h.1)
  have hμ := isStoppingTime_exitTime hsub.stronglyAdapted l
  rcases Nat.exists_eq_add_of_le' hk with ⟨m, rfl⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- k = 1: the term vanishes since f_0 = 0
    have h0 : term f l (0 + 1) = 0 := by
      funext ω; simp [term, gZ]
    rw [h0]
    exact ⟨integrable_zero _ _ _, by simp, fun _ => by simp⟩
  -- k = m + 1 with m ≥ 1
  set j := m with hj
  have hjk : j ≤ j + 1 := Nat.le_succ j
  set S : Set Ω := {ω | ((j + 1 : ℕ) : ℕ∞) ≤ exitTime f l ω} with hSdef
  have hS : MeasurableSet[ℱ j] S := by
    have : S = {ω | exitTime f l ω ≤ (j : ℕ∞)}ᶜ := by
      ext ω
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_compl_iff, not_le, Nat.cast_succ]
      exact ENat.add_one_le_iff (ENat.coe_ne_top j)
    rw [this]
    exact (hμ j).compl
  set h : Ω → ℝ := S.indicator (f j) with hhdef
  have hh : StronglyMeasurable[ℱ j] h := (hsub.stronglyAdapted j).indicator hS
  have hh' : AEStronglyMeasurable h P := (hh.mono (ℱ.le j)).aestronglyMeasurable
  have hbound : ∀ ω, ‖h ω‖ ≤ l := by
    intro ω
    simp only [hhdef, Real.norm_eq_abs]
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have hlt : (j : ℕ∞) < exitTime f l ω := by
        have := hω
        simp only [hSdef, Set.mem_setOf_eq, Nat.cast_succ] at this
        exact (ENat.add_one_le_iff (ENat.coe_ne_top j)).mp this
      have := abs_gZ_le_of_lt_exitTime f hl ω hlt
      rwa [gZ_pos f hm] at this
    · rw [Set.indicator_of_notMem hω]; simp [hl.le]
  have hterm : term f l (j + 1) = fun ω => h ω * f (j + 1) ω - h ω * f j ω := by
    rw [term_eq f l (by omega)]
    funext ω
    simp only [Nat.add_sub_cancel, gZ_pos f hm, hhdef, hSdef, mul_sub]
  have hint1 : Integrable (fun ω => h ω * f (j + 1) ω) P :=
    (hsub.integrable (j + 1)).bdd_mul hh' (Eventually.of_forall hbound)
  have hint2 : Integrable (fun ω => h ω * f j ω) P :=
    (hsub.integrable j).bdd_mul hh' (Eventually.of_forall hbound)
  have hint3 : Integrable (fun ω => h ω * (P[f (j + 1) | ℱ j]) ω) P :=
    integrable_condExp.bdd_mul hh' (Eventually.of_forall hbound)
  have hintT : Integrable (term f l (j + 1)) P := by
    rw [hterm]; exact hint1.sub hint2
  -- pull-out property
  have hce : P[fun ω => h ω * f (j + 1) ω | ℱ j] =ᵐ[P] fun ω => h ω * (P[f (j + 1) | ℱ j]) ω :=
    condExp_mul_of_stronglyMeasurable_left hh hint1 (hsub.integrable (j + 1))
  have hI1 : ∫ ω, h ω * f (j + 1) ω ∂P = ∫ ω, h ω * (P[f (j + 1) | ℱ j]) ω ∂P := by
    rw [← integral_condExp (ℱ.le j)]
    exact integral_congr_ae hce
  have hI : ∫ ω, term f l (j + 1) ω ∂P
      = ∫ ω, h ω * ((P[f (j + 1) | ℱ j]) ω - f j ω) ∂P := by
    rw [hterm, integral_sub hint1 hint2, hI1, ← integral_sub hint3 hint2]
    congr 1; funext ω; ring
  refine ⟨hintT, ?_, ?_⟩
  · rw [hI]
    apply integral_nonneg_of_ae
    rcases hf with hmart | ⟨hs, hnn⟩
    · have h1 : P[f (j + 1) | ℱ j] =ᵐ[P] f j := hmart.condExp_ae_eq hjk
      filter_upwards [h1] with ω h1
      simp [h1]
    · have h1 := hs.2.1 j (j + 1) hjk
      filter_upwards [h1, hnn j hm] with ω h1 h2
      have hh0 : 0 ≤ h ω := by
        simp only [hhdef]
        by_cases hω : ω ∈ S
        · rw [Set.indicator_of_mem hω]; exact h2
        · rw [Set.indicator_of_notMem hω]
      exact mul_nonneg hh0 (sub_nonneg.mpr h1)
  · intro hmart
    rw [hI]
    have h1 : P[f (j + 1) | ℱ j] =ᵐ[P] f j := hmart.condExp_ae_eq hjk
    have : (fun ω => h ω * ((P[f (j + 1) | ℱ j]) ω - f j ω)) =ᵐ[P] fun _ => 0 := by
      filter_upwards [h1] with ω h1
      simp [h1]
    rw [integral_congr_ae this]; simp


/-! ### The truncated exit times `τ_N = μ ∧ (N+1)` -/

/-- `τ_N = μ ∧ (N + 1)`. -/
noncomputable def tauN (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) : Ω → ℕ∞ :=
  fun ω => min (exitTime f l ω) ((N + 1 : ℕ) : ℕ∞)

/-- `τ_N` as a natural number. -/
noncomputable def tN (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) : Ω → ℕ := fun ω => (tauN f l N ω).toNat

lemma tauN_ne_top (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) : tauN f l N ω ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.coe_ne_top _) (min_le_right _ _)

lemma coe_tN (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) : (tN f l N ω : ℕ∞) = tauN f l N ω :=
  ENat.natCast_toNat (tauN_ne_top f l N ω)

lemma one_le_tN (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) : 1 ≤ tN f l N ω := by
  have h : (1 : ℕ∞) ≤ tauN f l N ω :=
    le_min (one_le_exitTime f l ω) (by exact_mod_cast Nat.succ_pos N)
  rw [← coe_tN] at h
  exact_mod_cast h

lemma tN_le (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) : tN f l N ω ≤ N + 1 := by
  have h : tauN f l N ω ≤ ((N + 1 : ℕ) : ℕ∞) := min_le_right _ _
  rw [← coe_tN] at h
  exact_mod_cast h

lemma coe_tN_le_exit (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) :
    (tN f l N ω : ℕ∞) ≤ exitTime f l ω := by
  rw [coe_tN]; exact min_le_left _ _

lemma coe_sub_one (t : ℕ) : ((t : ℕ∞)) - 1 = ((t - 1 : ℕ) : ℕ∞) := by
  rw [ENat.natCast_sub]; simp

lemma tN_sub_one_lt_exit (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) :
    ((tN f l N ω - 1 : ℕ) : ℕ∞) < exitTime f l ω := by
  refine lt_of_lt_of_le ?_ (coe_tN_le_exit f l N ω)
  have := one_le_tN f l N ω
  exact_mod_cast (Nat.sub_lt (by omega) one_pos)

lemma le_tN_iff (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) {k : ℕ} (hk : k ≤ N + 1) :
    (k : ℕ∞) ≤ exitTime f l ω ↔ k ≤ tN f l N ω := by
  have h1 : ((k : ℕ∞) ≤ tauN f l N ω) ↔ (k : ℕ∞) ≤ exitTime f l ω := by
    simp only [tauN, le_min_iff]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, by exact_mod_cast hk⟩
  rw [← h1, ← coe_tN, Nat.cast_le]

lemma tauN_sub_one (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) :
    tauN f l N ω - 1 = ((tN f l N ω - 1 : ℕ) : ℕ∞) := by
  rw [← coe_tN, coe_sub_one]

lemma untopA_eq_toNat (x : ℕ∞) (hx : x ≠ ⊤) : x.untopA = x.toNat := by
  induction x using ENat.recTopCoe with
  | top => exact absurd rfl hx
  | coe k => rfl

lemma isStoppingTime_tauN (hadp : StronglyAdapted ℱ f) (l : ℝ) (N : ℕ) :
    IsStoppingTime ℱ (tauN f l N) :=
  (isStoppingTime_exitTime hadp l).min_const (N + 1)

lemma measurable_tN (hadp : StronglyAdapted ℱ f) (l : ℝ) (N : ℕ) : Measurable (tN f l N) := by
  refine measurable_to_countable' fun k => ?_
  have h1 : tN f l N ⁻¹' {k} = {ω | tauN f l N ω = (k : ℕ∞)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    rw [← coe_tN]
    exact Nat.cast_inj.symm
  rw [h1]
  exact ℱ.le k _ ((isStoppingTime_tauN hadp l N).measurableSet_eq k)

/-- The real-valued `S_{τ_N - 1}²`. -/
noncomputable def SQ (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (tN f l N ω - 1), dseq f k ω ^ 2

/-- `f_{τ_N - 1}`. -/
noncomputable def G1 (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) : ℝ := gZ f (tN f l N ω - 1) ω

/-- `f_{τ_N}`. -/
noncomputable def G0 (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) : ℝ := gZ f (tN f l N ω) ω

lemma SQ_nonneg (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) : 0 ≤ SQ f l N ω :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma measurable_SQ (hadp : StronglyAdapted ℱ f) (l : ℝ) (N : ℕ) : Measurable (SQ f l N) :=
  measurable_comp_nat (F := fun t ω => ∑ k ∈ Finset.Icc 1 (t - 1), dseq f k ω ^ 2)
    (fun t => Finset.measurable_sum _ fun k _ => (measurable_dseq hadp k).pow_const 2)
    (measurable_tN hadp l N)

lemma measurable_G1 (hadp : StronglyAdapted ℱ f) (l : ℝ) (N : ℕ) : Measurable (G1 f l N) :=
  measurable_comp_nat (F := fun t ω => gZ f (t - 1) ω) (fun t => measurable_gZ hadp (t - 1))
    (measurable_tN hadp l N)

lemma measurable_G0 (hadp : StronglyAdapted ℱ f) (l : ℝ) (N : ℕ) : Measurable (G0 f l N) :=
  measurable_comp_nat (F := fun t ω => gZ f t ω) (fun t => measurable_gZ hadp t)
    (measurable_tN hadp l N)

lemma abs_G1_le (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) (N : ℕ) (ω : Ω) : |G1 f l N ω| ≤ l :=
  abs_gZ_le_of_lt_exitTime f hl ω (tN_sub_one_lt_exit f l N ω)

lemma G0_eq_stoppedValue (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) :
    G0 f l N = stoppedValue f (tauN f l N) := by
  funext ω
  simp only [G0, stoppedValue, untopA_eq_toNat _ (tauN_ne_top f l N ω)]
  rw [gZ_pos f (one_le_tN f l N ω)]; rfl

lemma integrable_G0 [IsFiniteMeasure P] (hsub : Submartingale f ℱ P) (l : ℝ) (N : ℕ) :
    Integrable (G0 f l N) P := by
  rw [G0_eq_stoppedValue]
  exact hsub.integrable_stoppedValue (isStoppingTime_tauN hsub.stronglyAdapted l N)
    (N := N + 1) (fun ω => min_le_right _ _)

lemma sum_term_eq (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.Icc 1 (N + 1), term f l k ω
      = ∑ k ∈ Finset.Icc 1 (tN f l N ω), gZ f (k - 1) ω * dseq f k ω := by
  simp only [term]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, (le_tN_iff f l N ω h2).mp h3⟩
  · rintro ⟨h1, h2⟩
    have h3 : k ≤ N + 1 := h2.trans (tN_le f l N ω)
    exact ⟨⟨h1, h3⟩, (le_tN_iff f l N ω h3).mpr h2⟩

lemma pointwise_identity (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) :
    SQ f l N ω + G1 f l N ω ^ 2 + 2 * ∑ k ∈ Finset.Icc 1 (N + 1), term f l k ω
      = 2 * (G0 f l N ω * G1 f l N ω) := by
  rw [sum_term_eq]
  exact stopped_identity f ω (one_le_tN f l N ω)

lemma sqFnAt_tauN_sq (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) :
    sqFnAt f (tauN f l N ω - 1) ω ^ 2 = ENNReal.ofReal (SQ f l N ω) := by
  rw [tauN_sub_one, sqFnAt_coe, sqFnN, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rfl

lemma valAt_tauN_sub_one (f : ℕ → Ω → ℝ) (fInf : Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) :
    valAt f fInf (tauN f l N ω - 1) ω = G1 f l N ω := by
  rw [tauN_sub_one, valAt_coe]; rfl

lemma valAt_tauN (f : ℕ → Ω → ℝ) (fInf : Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) :
    valAt f fInf (tauN f l N ω) ω = G0 f l N ω := by
  rw [← coe_tN, valAt_coe]; rfl

/-- The finite-`N` version of Lemma 2.1. -/
lemma finite_bound [IsProbabilityMeasure P]
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    {l : ℝ} (hl : 0 < l) (fInf : Ω → ℝ) (N : ℕ) :
    (∫⁻ ω, sqFnAt f (tauN f l N ω - 1) ω ^ 2 ∂P
        + ∫⁻ ω, ENNReal.ofReal (valAt f fInf (tauN f l N ω - 1) ω ^ 2) ∂P
      ≤ ENNReal.ofReal (2 * ∫ ω, valAt f fInf (tauN f l N ω) ω
          * valAt f fInf (tauN f l N ω - 1) ω ∂P)) ∧
    (Martingale f ℱ P →
      ∫⁻ ω, sqFnAt f (tauN f l N ω - 1) ω ^ 2 ∂P
        + ∫⁻ ω, ENNReal.ofReal (valAt f fInf (tauN f l N ω - 1) ω ^ 2) ∂P
      = ENNReal.ofReal (2 * ∫ ω, valAt f fInf (tauN f l N ω) ω
          * valAt f fInf (tauN f l N ω - 1) ω ∂P)) := by
  have hsub : Submartingale f ℱ P := hf.elim (fun h => h.submartingale) (fun h => h.1)
  have hadp := hsub.stronglyAdapted
  simp only [sqFnAt_tauN_sq, valAt_tauN_sub_one, valAt_tauN]
  -- integrability
  have hG1m : AEStronglyMeasurable (G1 f l N) P := (measurable_G1 hadp l N).aestronglyMeasurable
  have hG1b : ∀ᵐ ω ∂P, ‖G1 f l N ω‖ ≤ l :=
    Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_G1_le f hl N ω
  have hG0 : Integrable (G0 f l N) P := integrable_G0 hsub l N
  have hprod : Integrable (fun ω => G0 f l N ω * G1 f l N ω) P := by
    have := hG0.bdd_mul hG1m hG1b
    simpa [mul_comm] using this
  have hG1sq : Integrable (fun ω => G1 f l N ω ^ 2) P := by
    refine memLp_one_iff_integrable.mp (MemLp.of_bound (hG1m.pow 2) (l ^ 2) ?_)
    filter_upwards [hG1b] with ω hω
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rwa [Real.norm_eq_abs] at hω) 2
  have hterm : ∀ k ∈ Finset.Icc 1 (N + 1), Integrable (term f l k) P := fun k hk =>
    (term_facts hf hl (Finset.mem_Icc.mp hk).1).1
  have hsum : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 (N + 1), term f l k ω) P :=
    integrable_finsetSum _ hterm
  have hSQ : Integrable (SQ f l N) P := by
    have : SQ f l N = fun ω => 2 * (G0 f l N ω * G1 f l N ω) - G1 f l N ω ^ 2
        - 2 * ∑ k ∈ Finset.Icc 1 (N + 1), term f l k ω := by
      funext ω; have := pointwise_identity f l N ω; linarith
    rw [this]
    exact ((hprod.const_mul 2).sub hG1sq).sub (hsum.const_mul 2)
  -- integrate the identity
  have hint : ∫ ω, SQ f l N ω ∂P + ∫ ω, G1 f l N ω ^ 2 ∂P
      + 2 * ∑ k ∈ Finset.Icc 1 (N + 1), ∫ ω, term f l k ω ∂P
      = 2 * ∫ ω, G0 f l N ω * G1 f l N ω ∂P := by
    have hA : Integrable (fun ω => SQ f l N ω + G1 f l N ω ^ 2) P := hSQ.add hG1sq
    have hB : Integrable (fun ω => 2 * ∑ k ∈ Finset.Icc 1 (N + 1), term f l k ω) P :=
      hsum.const_mul 2
    have e1 : ∫ ω, 2 * (G0 f l N ω * G1 f l N ω) ∂P
        = ∫ ω, (SQ f l N ω + G1 f l N ω ^ 2 + 2 * ∑ k ∈ Finset.Icc 1 (N + 1), term f l k ω) ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => (pointwise_identity f l N ω).symm)
    have e2 : ∫ ω, (SQ f l N ω + G1 f l N ω ^ 2 + 2 * ∑ k ∈ Finset.Icc 1 (N + 1), term f l k ω) ∂P
        = ∫ ω, (SQ f l N ω + G1 f l N ω ^ 2) ∂P
          + ∫ ω, 2 * ∑ k ∈ Finset.Icc 1 (N + 1), term f l k ω ∂P := integral_add hA hB
    have e3 : ∫ ω, (SQ f l N ω + G1 f l N ω ^ 2) ∂P
        = ∫ ω, SQ f l N ω ∂P + ∫ ω, G1 f l N ω ^ 2 ∂P := integral_add hSQ hG1sq
    have e4 : ∫ ω, 2 * ∑ k ∈ Finset.Icc 1 (N + 1), term f l k ω ∂P
        = 2 * ∫ ω, ∑ k ∈ Finset.Icc 1 (N + 1), term f l k ω ∂P := integral_const_mul 2 _
    have e5 : ∫ ω, ∑ k ∈ Finset.Icc 1 (N + 1), term f l k ω ∂P
        = ∑ k ∈ Finset.Icc 1 (N + 1), ∫ ω, term f l k ω ∂P := integral_finsetSum _ hterm
    have e6 : ∫ ω, 2 * (G0 f l N ω * G1 f l N ω) ∂P
        = 2 * ∫ ω, G0 f l N ω * G1 f l N ω ∂P := integral_const_mul 2 _
    linarith
  have hL : ∫⁻ ω, ENNReal.ofReal (SQ f l N ω) ∂P + ∫⁻ ω, ENNReal.ofReal (G1 f l N ω ^ 2) ∂P
      = ENNReal.ofReal (∫ ω, SQ f l N ω ∂P + ∫ ω, G1 f l N ω ^ 2 ∂P) := by
    rw [ENNReal.ofReal_add (integral_nonneg (SQ_nonneg f l N))
      (integral_nonneg fun ω => sq_nonneg _),
      ofReal_integral_eq_lintegral_ofReal hSQ (Eventually.of_forall (SQ_nonneg f l N)),
      ofReal_integral_eq_lintegral_ofReal hG1sq (Eventually.of_forall fun ω => sq_nonneg _)]
  rw [hL]
  have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 (N + 1), ∫ ω, term f l k ω ∂P :=
    Finset.sum_nonneg fun k hk => (term_facts hf hl (Finset.mem_Icc.mp hk).1).2.1
  refine ⟨ENNReal.ofReal_le_ofReal (by linarith), fun hmart => ?_⟩
  have hsum_zero : ∑ k ∈ Finset.Icc 1 (N + 1), ∫ ω, term f l k ω ∂P = 0 :=
    Finset.sum_eq_zero fun k hk => (term_facts hf hl (Finset.mem_Icc.mp hk).1).2.2 hmart
  congr 1
  linarith


/-! ### The L¹ bound on `f_μ` (Doob), for an arbitrary a.e. limit `fInf` -/

lemma abs_valAt_coe (f : ℕ → Ω → ℝ) (fInf : Ω → ℝ) (k : ℕ) (ω : Ω) :
    |valAt f fInf (k : ℕ∞) ω| = absZ f k ω := by
  by_cases hk : k = 0
  · subst hk; simp [valAt, absZ]
  · simp [valAt, absZ, hk]

lemma abs_valAt_untopA (f : ℕ → Ω → ℝ) (fInf : Ω → ℝ) (t : ℕ∞) (ht : t ≠ ⊤) (ω : Ω) :
    |valAt f fInf t ω| = absZ f t.untopA ω := by
  induction t using ENat.recTopCoe with
  | top => exact absurd rfl ht
  | coe k => exact abs_valAt_coe f fInf k ω

lemma stoppedValue_coe_eq (f : ℕ → Ω → ℝ) (fInf : Ω → ℝ) (μ : Ω → ℕ∞) (n : ℕ) (ω : Ω) :
    ENNReal.ofReal |valAt f fInf (min (μ ω) n) ω|
      = ENNReal.ofReal (stoppedValue (absZ f) (fun ω => min (μ ω) n) ω) := by
  have ht : min (μ ω) (n : ℕ∞) ≠ ⊤ :=
    ne_top_of_le_ne_top (WithTop.coe_ne_top) (min_le_right _ _)
  rw [stoppedValue, abs_valAt_untopA f fInf _ ht]; rfl

lemma eLpNorm_one_le_pNorm (P : Measure Ω) (f : ℕ → Ω → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    eLpNorm (f n) 1 P ≤ pNorm P 1 f := by
  refine le_trans ?_ (le_iSup₂ (f := fun n (_ : n ∈ Set.Ici 1) =>
    lpNormE P 1 (fun ω => ENNReal.ofReal |f n ω|)) n hn)
  simp only [lpNormE, ENNReal.rpow_one, one_div, inv_one, eLpNorm_one_eq_lintegral_enorm,
    Real.enorm_eq_ofReal_abs]
  exact le_rfl

lemma stopped_L1_bound [IsProbabilityMeasure P]
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (fInf : Ω → ℝ) (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω)))
    (μ : Ω → ℕ∞) (hμ : IsStoppingTime ℱ μ) :
    ∫⁻ ω, ENNReal.ofReal |valAt f fInf (μ ω) ω| ∂P ≤ pNorm P 1 f := by
  have hG := absZ_submartingale hf
  set τ : ℕ → Ω → ℕ∞ := fun n ω => min (μ ω) n with hτdef
  have hτ : ∀ n, IsStoppingTime ℱ (τ n) := fun n => hμ.min_const n
  have hτle : ∀ n ω, τ n ω ≤ n := fun n ω => min_le_right _ _
  set u : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal |valAt f fInf (τ n ω) ω| with hu
  have hu_eq : ∀ n, u n = fun ω => ENNReal.ofReal (stoppedValue (absZ f) (τ n) ω) := by
    intro n; funext ω; exact stoppedValue_coe_eq f fInf μ n ω
  have hu_meas : ∀ n, AEMeasurable (u n) P := by
    intro n; rw [hu_eq n]
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hG.integrable_stoppedValue (hτ n) (hτle n)).aemeasurable
  have hu_bound : ∀ n, 1 ≤ n → ∫⁻ ω, u n ω ∂P ≤ pNorm P 1 f := by
    intro n hn
    have hrw : ∫⁻ ω, u n ω ∂P
        = ∫⁻ ω, ENNReal.ofReal (stoppedValue (absZ f) (τ n) ω) ∂P := by
      rw [hu_eq n]
    rw [hrw]
    have hnn : ∀ τ : Ω → ℕ∞, 0 ≤ᵐ[P] stoppedValue (absZ f) τ :=
      fun τ => Eventually.of_forall fun ω => absZ_nonneg f _ ω
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hG.integrable_stoppedValue (hτ n) (hτle n)) (hnn _)]
    have hos := hG.expected_stoppedValue_mono (hτ n) (isStoppingTime_const ℱ n)
      (hτle n) (N := n) (fun ω => le_rfl)
    rw [stoppedValue_const] at hos
    calc ENNReal.ofReal (∫ ω, stoppedValue (absZ f) (τ n) ω ∂P)
        ≤ ENNReal.ofReal (∫ ω, absZ f n ω ∂P) := ENNReal.ofReal_le_ofReal hos
      _ = ∫⁻ ω, ENNReal.ofReal (absZ f n ω) ∂P :=
          ofReal_integral_eq_lintegral_ofReal (hG.integrable n)
            (Eventually.of_forall (absZ_nonneg f n))
      _ = eLpNorm (f n) 1 P := by
          rw [eLpNorm_one_eq_lintegral_enorm, absZ_pos f hn]
          simp only [Real.enorm_eq_ofReal_abs]
      _ ≤ pNorm P 1 f := eLpNorm_one_le_pNorm P f hn
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => u n ω) atTop
      (𝓝 (ENNReal.ofReal |valAt f fInf (μ ω) ω|)) := by
    filter_upwards [hlim] with ω hω
    show Tendsto (fun n : ℕ => ENNReal.ofReal |valAt f fInf (min (μ ω) (n : ℕ∞)) ω|) atTop _
    by_cases hμω : μ ω = ⊤
    · rw [hμω]
      have hmin : ∀ n : ℕ, min (⊤ : ℕ∞) n = n := fun n => min_eq_right le_top
      simp only [hmin]
      have hv : valAt f fInf ⊤ ω = fInf ω := by simp [valAt]
      rw [hv]
      have h1 : Tendsto (fun n => ENNReal.ofReal |f n ω|) atTop (𝓝 (ENNReal.ofReal |fInf ω|)) :=
        (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_abs.tendsto _).comp hω)
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      simp [valAt, Nat.one_le_iff_ne_zero.mp hn]
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hμω
      rw [← hm]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop m] with n hn
      have : min (m : ℕ∞) n = m := min_eq_left (by exact_mod_cast hn)
      rw [this]
  have hliminf : (fun ω => ENNReal.ofReal |valAt f fInf (μ ω) ω|)
      =ᵐ[P] fun ω => liminf (fun n => u n ω) atTop := by
    filter_upwards [hconv] with ω hω
    exact hω.liminf_eq.symm
  calc ∫⁻ ω, ENNReal.ofReal |valAt f fInf (μ ω) ω| ∂P
      = ∫⁻ ω, liminf (fun n => u n ω) atTop ∂P := lintegral_congr_ae hliminf
    _ ≤ liminf (fun n => ∫⁻ ω, u n ω ∂P) atTop := lintegral_liminf_le' hu_meas
    _ ≤ pNorm P 1 f := by
        apply Filter.liminf_le_of_frequently_le'
        exact (Filter.eventually_atTop.mpr ⟨1, fun n hn => hu_bound n hn⟩).frequently

/-! ### Limits `N → ∞` -/

lemma top_sub_one : (⊤ : ℕ∞) - 1 = ⊤ := by
  simpa using ENat.top_sub_natCast 1

lemma measurable_exitTime (hadp : StronglyAdapted ℱ f) (l : ℝ) : Measurable (exitTime f l) := by
  have hμ := isStoppingTime_exitTime hadp l
  refine measurable_to_countable' fun x => ?_
  induction x using ENat.recTopCoe with
  | top =>
    have : exitTime f l ⁻¹' {⊤} = ⋂ n : ℕ, {ω | exitTime f l ω ≤ (n : ℕ∞)}ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_setOf_eq, not_le]
      exact ENat.eq_top_iff_forall_gt
    rw [this]
    exact MeasurableSet.iInter fun n => (ℱ.le n _ (hμ n)).compl
  | coe k =>
    have : exitTime f l ⁻¹' {(k : ℕ∞)} = {ω | exitTime f l ω = (k : ℕ∞)} := by
      ext ω; simp
    rw [this]
    exact ℱ.le k _ (hμ.measurableSet_eq k)

lemma valAt_congr (f : ℕ → Ω → ℝ) {g g' : Ω → ℝ} {ω : Ω} (h : g ω = g' ω) (x : ℕ∞) :
    valAt f g x ω = valAt f g' x ω := by
  induction x using ENat.recTopCoe with
  | top => simp [valAt_top, h]
  | coe k => simp [valAt_coe]

lemma abs_fInf_le (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) {fInf : Ω → ℝ} {ω : Ω}
    (hω : Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω))) (htop : exitTime f l ω = ⊤) :
    |fInf ω| ≤ l := by
  have h1 : Tendsto (fun n => |f n ω|) atTop (𝓝 |fInf ω|) := (continuous_abs.tendsto _).comp hω
  refine le_of_tendsto h1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have := abs_gZ_le_of_lt_exitTime f hl ω (k := n) (by rw [htop]; exact WithTop.coe_lt_top n)
  rwa [gZ_pos f hn] at this

lemma abs_valAt_exit_sub_one_le (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) {fInf : Ω → ℝ} {ω : Ω}
    (hω : Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω))) :
    |valAt f fInf (exitTime f l ω - 1) ω| ≤ l := by
  by_cases htop : exitTime f l ω = ⊤
  · rw [htop, top_sub_one, valAt_top]; exact abs_fInf_le f hl hω htop
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hm, coe_sub_one, valAt_coe]
    have hm1 : 1 ≤ m := by
      have := one_le_exitTime f l ω; rw [← hm] at this; exact_mod_cast this
    refine abs_gZ_le_of_lt_exitTime f hl ω ?_
    rw [← hm]; exact_mod_cast Nat.sub_lt (by omega) one_pos

lemma tendsto_valAt_tauN_sub_one (f : ℕ → Ω → ℝ) (l : ℝ) {fInf : Ω → ℝ} {ω : Ω}
    (hω : Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω))) :
    Tendsto (fun N => valAt f fInf (tauN f l N ω - 1) ω) atTop
      (𝓝 (valAt f fInf (exitTime f l ω - 1) ω)) := by
  by_cases htop : exitTime f l ω = ⊤
  · rw [htop, top_sub_one, valAt_top]
    refine hω.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : tauN f l N ω - 1 = (N : ℕ∞) := by
      simp only [tauN, htop, min_eq_right le_top]
      rw [coe_sub_one]; simp
    rw [this, valAt_coe, gZ_pos f hN]
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m] with N hN
    have : tauN f l N ω = exitTime f l ω := by
      simp only [tauN]; rw [← hm]
      exact min_eq_left (by exact_mod_cast (by omega : m ≤ N + 1))
    rw [this]

lemma tendsto_valAt_tauN (f : ℕ → Ω → ℝ) (l : ℝ) {fInf : Ω → ℝ} {ω : Ω}
    (hω : Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω))) :
    Tendsto (fun N => valAt f fInf (tauN f l N ω) ω) atTop
      (𝓝 (valAt f fInf (exitTime f l ω) ω)) := by
  by_cases htop : exitTime f l ω = ⊤
  · rw [htop, valAt_top]
    have h2 : Tendsto (fun N => f (N + 1) ω) atTop (𝓝 (fInf ω)) :=
      hω.comp (tendsto_add_atTop_nat 1)
    refine h2.congr' ?_
    filter_upwards with N
    have : tauN f l N ω = ((N + 1 : ℕ) : ℕ∞) := by
      simp only [tauN, htop, min_eq_right le_top]
    rw [this, valAt_coe, gZ_pos f (Nat.succ_pos N)]
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m] with N hN
    have : tauN f l N ω = exitTime f l ω := by
      simp only [tauN]; rw [← hm]
      exact min_eq_left (by exact_mod_cast (by omega : m ≤ N + 1))
    rw [this]

lemma sqFnN_mono (f : ℕ → Ω → ℝ) (ω : Ω) : Monotone fun n => sqFnN f n ω := by
  intro n m hnm
  simp only [sqFnN]
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hnm)
    (fun _ _ _ => sq_nonneg _)

lemma sqFnAt_mono (f : ℕ → Ω → ℝ) (ω : Ω) : Monotone fun m => sqFnAt f m ω := by
  intro a b hab
  show sqFnAt f a ω ≤ sqFnAt f b ω
  induction b using ENat.recTopCoe with
  | top =>
    induction a using ENat.recTopCoe with
    | top => exact le_rfl
    | coe k => rw [sqFnAt_coe, sqFnAt_top, sqFn]; exact le_iSup (fun n => sqFnN f n ω) k
  | coe m =>
    induction a using ENat.recTopCoe with
    | top => exact absurd hab (not_le.mpr (WithTop.coe_lt_top m))
    | coe k => rw [sqFnAt_coe, sqFnAt_coe]; exact sqFnN_mono f ω (by exact_mod_cast hab)

lemma tauN_mono (f : ℕ → Ω → ℝ) (l : ℝ) (ω : Ω) : Monotone fun N => tauN f l N ω := by
  intro N M hNM
  simp only [tauN]
  exact min_le_min_left _ (by exact_mod_cast Nat.succ_le_succ hNM)

lemma iSup_sqFnAt_tauN (f : ℕ → Ω → ℝ) (l : ℝ) (ω : Ω) :
    ⨆ N, sqFnAt f (tauN f l N ω - 1) ω ^ 2 = sqFnAt f (exitTime f l ω - 1) ω ^ 2 := by
  apply le_antisymm
  · refine iSup_le fun N => ?_
    apply pow_le_pow_left₀ bot_le
    exact sqFnAt_mono f ω (tsub_le_tsub_right (min_le_left _ _) 1)
  · by_cases htop : exitTime f l ω = ⊤
    · rw [htop, top_sub_one, sqFnAt_top, sqFn, ENNReal.iSup_pow]
      refine iSup_le fun n => le_iSup_of_le n (le_of_eq ?_)
      have : tauN f l n ω - 1 = (n : ℕ∞) := by
        simp only [tauN, htop, min_eq_right le_top]
        rw [coe_sub_one]; simp
      rw [this, sqFnAt_coe]
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
      refine le_iSup_of_le m (le_of_eq ?_)
      have : tauN f l m ω = exitTime f l ω := by
        simp only [tauN]; rw [← hm]
        exact min_eq_left (by exact_mod_cast (by omega : m ≤ m + 1))
      rw [this]


lemma abs_G0_le (f : ℕ → Ω → ℝ) (fInf : Ω → ℝ) {l : ℝ} (hl : 0 < l) (N : ℕ) (ω : Ω) :
    |G0 f l N ω| ≤ |valAt f fInf (exitTime f l ω) ω| + l := by
  by_cases h : exitTime f l ω ≤ ((N + 1 : ℕ) : ℕ∞)
  · have : tauN f l N ω = exitTime f l ω := min_eq_left h
    rw [← valAt_tauN f fInf, this]
    exact le_add_of_nonneg_right hl.le
  · push_neg at h
    have ht : tauN f l N ω = ((N + 1 : ℕ) : ℕ∞) := min_eq_right h.le
    have htN : tN f l N ω = N + 1 := by
      have := coe_tN f l N ω; rw [ht] at this; exact_mod_cast this
    have : G0 f l N ω = gZ f (N + 1) ω := by simp only [G0, htN]
    rw [this]
    exact le_add_of_nonneg_left (abs_nonneg _) |>.trans'
      (abs_gZ_le_of_lt_exitTime f hl ω h) |> fun h' => by linarith [abs_nonneg (valAt f fInf (exitTime f l ω) ω), abs_gZ_le_of_lt_exitTime f hl ω h]

/-- Lemma 2.1 of Burkholder, with the exit time `μ = inf {n ≥ 1 : |f_n| > λ}`. -/
theorem lemma_2_1_core {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (hL1 : BurkholderDFI.SquareFnLp.pNorm P 1 f < ⊤) (fInf : Ω → ℝ)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω)))
    (l : ℝ) (hl : 0 < l) :
    (∫⁻ ω, BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2 ∂P
        + ∫⁻ ω, ENNReal.ofReal (BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2) ∂P
      ≤ ENNReal.ofReal (2 * ∫ ω, BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω) ω
                                 * BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ∂P)) ∧
    (2 * ∫ ω, BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω) ω * BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ∂P
      ≤ 2 * l * (BurkholderDFI.SquareFnLp.pNorm P 1 f).toReal) ∧
    (Martingale f ℱ P →
      ∫⁻ ω, BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2 ∂P
          + ∫⁻ ω, ENNReal.ofReal (BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2) ∂P
        = ENNReal.ofReal (2 * ∫ ω, BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω) ω
                                   * BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ∂P)) := by
  have hsub : Submartingale f ℱ P := hf.elim (fun h => h.submartingale) (fun h => h.1)
  have hadp := hsub.stronglyAdapted
  have hμ : IsStoppingTime ℱ (exitTime f l) := isStoppingTime_exitTime hadp l
  have hμm : Measurable (exitTime f l) := measurable_exitTime hadp l
  -- a measurable version of the limit
  set R : ℝ≥0 := (max (eLpNorm (f 0) 1 P) (pNorm P 1 f)).toNNReal with hR
  have hRtop : max (eLpNorm (f 0) 1 P) (pNorm P 1 f) ≠ ⊤ := by
    have h0 : eLpNorm (f 0) 1 P < ⊤ :=
      (memLp_one_iff_integrable.mpr (hsub.integrable 0)).eLpNorm_lt_top
    exact (max_lt h0 hL1).ne
  have hbdd : ∀ n, eLpNorm (f n) 1 P ≤ R := by
    intro n
    rw [hR, ENNReal.coe_toNNReal hRtop]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact le_max_left _ _
    · exact (eLpNorm_one_le_pNorm P f hn).trans (le_max_right _ _)
  have hglim := hsub.ae_tendsto_limitProcess hbdd
  set g := ℱ.limitProcess f P with hgdef
  have hg : Measurable g :=
    (ℱ.stronglyMeasurable_limitProcess (f := f) (μ := P)).measurable.mono
      (iSup_le fun n => ℱ.le n) le_rfl
  have hfg : fInf =ᵐ[P] g := by
    filter_upwards [hlim, hglim] with ω h1 h2
    exact tendsto_nhds_unique h1 h2
  have hV : (fun ω => valAt f fInf (exitTime f l ω) ω) =ᵐ[P]
      fun ω => valAt f g (exitTime f l ω) ω := by
    filter_upwards [hfg] with ω h; exact valAt_congr f h _
  have hV1 : (fun ω => valAt f fInf (exitTime f l ω - 1) ω) =ᵐ[P]
      fun ω => valAt f g (exitTime f l ω - 1) ω := by
    filter_upwards [hfg] with ω h; exact valAt_congr f h _
  have hVm : AEStronglyMeasurable (fun ω => valAt f fInf (exitTime f l ω) ω) P :=
    (measurable_valAt hadp hg hμm).aestronglyMeasurable.congr hV.symm
  have hV1m : AEStronglyMeasurable (fun ω => valAt f fInf (exitTime f l ω - 1) ω) P :=
    (measurable_valAt hadp hg
      ((measurable_of_countable (fun x : ℕ∞ => x - 1)).comp hμm)).aestronglyMeasurable.congr hV1.symm
  -- the L¹ bound
  have hbound := stopped_L1_bound hf fInf hlim (exitTime f l) hμ
  have hVint : Integrable (fun ω => valAt f fInf (exitTime f l ω) ω) P := by
    refine ⟨hVm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp only [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt hbound hL1
  have hV1b : ∀ᵐ ω ∂P, |valAt f fInf (exitTime f l ω - 1) ω| ≤ l := by
    filter_upwards [hlim] with ω hω
    exact abs_valAt_exit_sub_one_le f hl hω
  -- part (b)
  have hprodInt : Integrable (fun ω => valAt f fInf (exitTime f l ω) ω
      * valAt f fInf (exitTime f l ω - 1) ω) P :=
    hVint.mul_bdd hV1m (by filter_upwards [hV1b] with ω h; rwa [Real.norm_eq_abs])
  have hB : ∫ ω, valAt f fInf (exitTime f l ω) ω * valAt f fInf (exitTime f l ω - 1) ω ∂P
      ≤ l * (pNorm P 1 f).toReal := by
    calc ∫ ω, valAt f fInf (exitTime f l ω) ω * valAt f fInf (exitTime f l ω - 1) ω ∂P
        ≤ ∫ ω, |valAt f fInf (exitTime f l ω) ω| * l ∂P := by
          refine integral_mono_ae hprodInt (hVint.abs.mul_const l) ?_
          filter_upwards [hV1b] with ω h
          calc valAt f fInf (exitTime f l ω) ω * valAt f fInf (exitTime f l ω - 1) ω
              ≤ |valAt f fInf (exitTime f l ω) ω * valAt f fInf (exitTime f l ω - 1) ω| :=
                le_abs_self _
            _ = |valAt f fInf (exitTime f l ω) ω| * |valAt f fInf (exitTime f l ω - 1) ω| :=
                abs_mul _ _
            _ ≤ |valAt f fInf (exitTime f l ω) ω| * l :=
                mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = (∫ ω, |valAt f fInf (exitTime f l ω) ω| ∂P) * l := integral_mul_const l _
      _ = (∫⁻ ω, ENNReal.ofReal |valAt f fInf (exitTime f l ω) ω| ∂P).toReal * l := by
          rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => abs_nonneg _)
            hVint.abs.aestronglyMeasurable]
      _ ≤ (pNorm P 1 f).toReal * l := by
          exact mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hL1.ne hbound) hl.le
      _ = l * (pNorm P 1 f).toReal := mul_comm _ _
  -- limit (1): the square function term, by monotone convergence
  have hmeas1 : ∀ N, Measurable fun ω => sqFnAt f (tauN f l N ω - 1) ω ^ 2 := by
    intro N
    simp_rw [sqFnAt_tauN_sq]
    exact ENNReal.measurable_ofReal.comp (measurable_SQ hadp l N)
  have hmono1 : Monotone fun N ω => sqFnAt f (tauN f l N ω - 1) ω ^ 2 := by
    intro N M h ω
    exact pow_le_pow_left₀ bot_le (sqFnAt_mono f ω (tsub_le_tsub_right (tauN_mono f l ω h) 1)) 2
  have hL1lim : Tendsto (fun N => ∫⁻ ω, sqFnAt f (tauN f l N ω - 1) ω ^ 2 ∂P) atTop
      (𝓝 (∫⁻ ω, sqFnAt f (exitTime f l ω - 1) ω ^ 2 ∂P)) := by
    have heq : ∫⁻ ω, sqFnAt f (exitTime f l ω - 1) ω ^ 2 ∂P
        = ⨆ N, ∫⁻ ω, sqFnAt f (tauN f l N ω - 1) ω ^ 2 ∂P := by
      rw [← lintegral_iSup hmeas1 hmono1]
      congr 1; funext ω
      exact (iSup_sqFnAt_tauN f l ω).symm
    rw [heq]
    exact tendsto_atTop_iSup fun N M h => lintegral_mono (hmono1 h)
  -- limit (2): the `f_{μ-1}²` term, by dominated convergence
  have hL2lim : Tendsto (fun N => ∫⁻ ω, ENNReal.ofReal (valAt f fInf (tauN f l N ω - 1) ω ^ 2) ∂P)
      atTop (𝓝 (∫⁻ ω, ENNReal.ofReal (valAt f fInf (exitTime f l ω - 1) ω ^ 2) ∂P)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal (l ^ 2))
      (fun N => ?_) (fun N => Eventually.of_forall fun ω => ?_) (by simp) ?_
    · simp_rw [valAt_tauN_sub_one]
      exact ENNReal.measurable_ofReal.comp ((measurable_G1 hadp l N).pow_const 2)
    · apply ENNReal.ofReal_le_ofReal
      rw [valAt_tauN_sub_one, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_G1_le f hl N ω) 2
    · filter_upwards [hlim] with ω hω
      exact (ENNReal.continuous_ofReal.tendsto _).comp ((tendsto_valAt_tauN_sub_one f l hω).pow 2)
  -- limit (3): the product term, by dominated convergence
  have hElim : Tendsto (fun N => ∫ ω, valAt f fInf (tauN f l N ω) ω
      * valAt f fInf (tauN f l N ω - 1) ω ∂P) atTop
      (𝓝 (∫ ω, valAt f fInf (exitTime f l ω) ω * valAt f fInf (exitTime f l ω - 1) ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ω => (|valAt f fInf (exitTime f l ω) ω| + l) * l) (fun N => ?_)
      ((hVint.abs.add (integrable_const l)).mul_const l) (fun N => Eventually.of_forall fun ω => ?_) ?_
    · simp_rw [valAt_tauN, valAt_tauN_sub_one]
      exact ((measurable_G0 hadp l N).mul (measurable_G1 hadp l N)).aestronglyMeasurable
    · rw [valAt_tauN, valAt_tauN_sub_one, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (abs_G0_le f fInf hl N ω) (abs_G1_le f hl N ω) (abs_nonneg _)
        (by linarith [abs_nonneg (valAt f fInf (exitTime f l ω) ω)])
    · filter_upwards [hlim] with ω hω
      exact (tendsto_valAt_tauN f l hω).mul (tendsto_valAt_tauN_sub_one f l hω)
  have hLlim := hL1lim.add hL2lim
  have hRlim : Tendsto (fun N => ENNReal.ofReal (2 * ∫ ω, valAt f fInf (tauN f l N ω) ω
      * valAt f fInf (tauN f l N ω - 1) ω ∂P)) atTop
      (𝓝 (ENNReal.ofReal (2 * ∫ ω, valAt f fInf (exitTime f l ω) ω
        * valAt f fInf (exitTime f l ω - 1) ω ∂P))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hElim.const_mul 2)
  refine ⟨le_of_tendsto_of_tendsto' hLlim hRlim fun N => (finite_bound hf hl fInf N).1,
    by linarith [hB], fun hmart => ?_⟩
  exact tendsto_nhds_unique hLlim
    (hRlim.congr fun N => ((finite_bound hf hl fInf N).2 hmart).symm)

end BurkholderDFI.Gundy

open BurkholderDFI.Gundy


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (hL1 : BurkholderDFI.SquareFnLp.pNorm P 1 f < ⊤) (fInf : Ω → ℝ)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (fInf ω)))
    (l : ℝ) (hl : 0 < l) :
    (∫⁻ ω, BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2 ∂P
        + ∫⁻ ω, ENNReal.ofReal (BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2) ∂P
      ≤ ENNReal.ofReal (2 * ∫ ω, BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω) ω
                                 * BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ∂P)) ∧
    (2 * ∫ ω, BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω) ω * BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ∂P
      ≤ 2 * l * (BurkholderDFI.SquareFnLp.pNorm P 1 f).toReal) ∧
    (Martingale f ℱ P →
      ∫⁻ ω, BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2 ∂P
          + ∫⁻ ω, ENNReal.ofReal (BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ^ 2) ∂P
        = ENNReal.ofReal (2 * ∫ ω, BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω) ω
                                   * BurkholderDFI.SquareFnLp.valAt f fInf (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ∂P)) := by
  exact lemma_2_1_core hf hL1 fInf hlim l hl
