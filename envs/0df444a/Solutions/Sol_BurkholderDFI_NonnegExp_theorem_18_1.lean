-- Prove2me | solution 1 for BurkholderDFI.NonnegExp.theorem_18_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:44:14.608995+00:00
-- url     : https://prove2.me/submissions/1607e8b2-b8f7-49ae-a0d0-fe9d415593c7

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace BurkholderDFI.NonnegExp
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


/-! ### (18.5): the tail integral after the stopping threshold -/

section E185

/-- `S_n(f)²` as a real number. -/
noncomputable def SSQ (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.Icc 1 n, dseq f k ω ^ 2

lemma SSQ_zero (f : ℕ → Ω → ℝ) (ω : Ω) : SSQ f 0 ω = 0 := by simp [SSQ]

lemma SSQ_succ (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    SSQ f (n + 1) ω = SSQ f n ω + dseq f (n + 1) ω ^ 2 := by
  simp only [SSQ]; rw [Finset.sum_Icc_succ_top (by omega)]

lemma SSQ_mono (f : ℕ → Ω → ℝ) (ω : Ω) : Monotone fun n => SSQ f n ω := by
  intro n m h
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h)
    (fun _ _ _ => sq_nonneg _)

lemma SQ_eq_SSQ (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) :
    SQ f l N ω = SSQ f (tN f l N ω - 1) ω := rfl

lemma measurable_gZ_filt (hadp : StronglyAdapted ℱ f) {k n : ℕ} (hkn : k ≤ n) :
    Measurable[ℱ n] (gZ f k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [gZ_zero]; exact measurable_const
  · rw [gZ_pos f hk]; exact (hadp k).measurable.mono (ℱ.mono hkn) le_rfl

lemma measurable_dseq_filt (hadp : StronglyAdapted ℱ f) {k n : ℕ} (hkn : k ≤ n) :
    Measurable[ℱ n] (dseq f k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : dseq f 0 = fun _ => (0 : ℝ) := by funext ω; simp [dseq]
    rw [this]; exact measurable_const
  · have : dseq f k = fun ω => gZ f k ω - gZ f (k - 1) ω := by
      funext ω; exact dseq_eq_gZ f hk ω
    rw [this]; exact (measurable_gZ_filt hadp hkn).sub (measurable_gZ_filt hadp (by omega))

lemma measurable_SSQ_filt (hadp : StronglyAdapted ℱ f) (n : ℕ) : Measurable[ℱ n] (SSQ f n) :=
  Finset.measurable_sum _ (fun k hk =>
    (measurable_dseq_filt hadp (Finset.mem_Icc.mp hk).2).pow_const 2)

/-- `ν = inf {n ≥ 1 : S_n(f)² > a}`. -/
noncomputable def nuT (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n ∧ a < SSQ f n ω), (n : ℕ∞)

lemma one_le_nuT (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : 1 ≤ nuT f a ω :=
  le_iInf₂ fun n hn => by exact_mod_cast hn.1

lemma nuT_le_of (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) {n : ℕ} (hn : 1 ≤ n) (h : a < SSQ f n ω) :
    nuT f a ω ≤ n :=
  iInf₂_le n ⟨hn, h⟩

lemma SSQ_le_of_lt_nuT (f : ℕ → Ω → ℝ) {a : ℝ} (ha : 0 < a) (ω : Ω) {k : ℕ}
    (hk : (k : ℕ∞) < nuT f a ω) : SSQ f k ω ≤ a := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [SSQ_zero]; exact ha.le
  · by_contra h
    push_neg at h
    exact absurd (nuT_le_of f a ω hk1 h) (not_le.mpr hk)

lemma nuT_le_iff (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) (n : ℕ) :
    nuT f a ω ≤ n ↔ ∃ k, 1 ≤ k ∧ k ≤ n ∧ a < SSQ f k ω := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have : ((n + 1 : ℕ) : ℕ∞) ≤ nuT f a ω := by
      refine le_iInf₂ fun k hk => ?_
      have : n + 1 ≤ k := by
        by_contra hlt; push_neg at hlt
        exact absurd hk.2 (not_lt.mpr (hcon k hk.1 (by omega)))
      exact_mod_cast this
    have h2 := this.trans h
    have h3 : n + 1 ≤ n := by exact_mod_cast h2
    omega
  · rintro ⟨k, hk1, hkn, hk⟩
    exact (nuT_le_of f a ω hk1 hk).trans (by exact_mod_cast hkn)

lemma isStoppingTime_nuT (hadp : StronglyAdapted ℱ f) (a : ℝ) :
    IsStoppingTime ℱ (nuT f a) := by
  intro n
  have : {ω | nuT f a ω ≤ (n : ℕ∞)} = ⋃ k ∈ Finset.Icc 1 n, {ω | a < SSQ f k ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Icc, exists_prop]
    rw [nuT_le_iff]
    constructor
    · rintro ⟨k, h1, h2, h3⟩; exact ⟨k, ⟨h1, h2⟩, h3⟩
    · rintro ⟨k, ⟨h1, h2⟩, h3⟩; exact ⟨k, h1, h2, h3⟩
  have key : MeasurableSet[ℱ n] {ω | nuT f a ω ≤ (n : ℕ∞)} := by
    rw [this]
    refine Finset.measurableSet_biUnion _ fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hs : MeasurableSet[ℱ k] {ω | a < SSQ f k ω} :=
      measurableSet_lt measurable_const (measurable_SSQ_filt hadp k)
    exact ℱ.mono hk.2 _ hs
  exact key

lemma nuT_spec (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) {n : ℕ} (h : nuT f a ω = n) :
    1 ≤ n ∧ a < SSQ f n ω := by
  have h1 : nuT f a ω ≤ n := h.le
  obtain ⟨k, hk1, hkn, hk⟩ := (nuT_le_iff f a ω n).mp h1
  have h2 := nuT_le_of f a ω hk1 hk
  rw [h] at h2
  have h3 : n ≤ k := by exact_mod_cast h2
  have : k = n := le_antisymm hkn h3
  subst this
  exact ⟨hk1, hk⟩

lemma lt_nuT_of_lt_coe (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) {n k : ℕ} (h : nuT f a ω = n)
    (hk : k < n) : (k : ℕ∞) < nuT f a ω := by
  rw [h]; exact_mod_cast hk

/-- `e_k = 1_{ν < k} d_k`. -/
noncomputable def ee (f : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if nuT f a ω < k then dseq f k ω else 0

/-- `h_k = Σ_{j ≤ k} e_j = f_k − f_ν` on `{ν < k}`. -/
noncomputable def hh (f : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, ee f a j ω

lemma hh_zero (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : hh f a 0 ω = 0 := by simp [hh]

lemma hh_succ (f : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) (ω : Ω) :
    hh f a (k + 1) ω = hh f a k ω + ee f a (k + 1) ω := by
  simp only [hh]; rw [Finset.sum_Icc_succ_top (by omega)]

lemma ee_eq_zero_of_le (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) {k : ℕ} (h : (k : ℕ∞) ≤ nuT f a ω) :
    ee f a k ω = 0 := by
  simp [ee, not_lt.mpr h]

lemma ee_eq_of_lt (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) {k : ℕ} (h : nuT f a ω < k) :
    ee f a k ω = dseq f k ω := by
  simp [ee, h]

lemma hh_eq_zero_of_le (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) {k : ℕ} (h : (k : ℕ∞) ≤ nuT f a ω) :
    hh f a k ω = 0 := by
  induction k with
  | zero => exact hh_zero f a ω
  | succ k ih =>
    rw [hh_succ, ih (le_trans (by exact_mod_cast Nat.le_succ k) h), ee_eq_zero_of_le f a ω h,
      add_zero]

lemma hh_eq_of_nuT (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) {n k : ℕ} (hν : nuT f a ω = n)
    (hnk : n ≤ k) : hh f a k ω = gZ f k ω - gZ f n ω := by
  induction k, hnk using Nat.le_induction with
  | base => rw [hh_eq_zero_of_le f a ω (by rw [hν])]; ring
  | succ k hnk ih =>
    rw [hh_succ, ih, ee_eq_of_lt f a ω (by rw [hν]; exact_mod_cast Nat.lt_succ_of_le hnk),
      dseq_eq_gZ f (by omega)]
    simp only [Nat.add_sub_cancel]
    ring

lemma SSQ_eq_of_nuT (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) {n k : ℕ} (hν : nuT f a ω = n)
    (hnk : n ≤ k) : SSQ f k ω = SSQ f n ω + ∑ j ∈ Finset.Icc 1 k, ee f a j ω ^ 2 := by
  induction k, hnk using Nat.le_induction with
  | base =>
    rw [Finset.sum_eq_zero, add_zero]
    intro j hj
    rw [ee_eq_zero_of_le f a ω (by rw [hν]; exact_mod_cast (Finset.mem_Icc.mp hj).2)]
    ring
  | succ k hnk ih =>
    rw [SSQ_succ, ih, Finset.sum_Icc_succ_top (by omega),
      ee_eq_of_lt f a ω (by rw [hν]; exact_mod_cast Nat.lt_succ_of_le hnk)]
    ring

lemma gZ_hh (f : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) (ω : Ω) : gZ (hh f a) k ω = hh f a k ω := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [hh_zero]; simp [gZ]
  · rw [gZ_pos _ hk]

lemma dseq_hh (f : ℕ → Ω → ℝ) (a : ℝ) {k : ℕ} (hk : 1 ≤ k) (ω : Ω) :
    dseq (hh f a) k ω = ee f a k ω := by
  rw [dseq_eq_gZ _ hk, gZ_hh, gZ_hh]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [hh_succ]; simp

/-- The stopped identity for the transformed sequence. -/
lemma hh_identity (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) {m : ℕ} (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Icc 1 (m - 1), ee f a k ω ^ 2 + hh f a (m - 1) ω ^ 2
      + 2 * ∑ k ∈ Finset.Icc 1 m, hh f a (k - 1) ω * ee f a k ω
      = 2 * (hh f a m ω * hh f a (m - 1) ω) := by
  have := stopped_identity (hh f a) ω hm
  simp only [gZ_hh] at this
  have e1 : ∑ k ∈ Finset.Icc 1 (m - 1), dseq (hh f a) k ω ^ 2
      = ∑ k ∈ Finset.Icc 1 (m - 1), ee f a k ω ^ 2 :=
    Finset.sum_congr rfl (fun k hk => by rw [dseq_hh f a (Finset.mem_Icc.mp hk).1])
  have e2 : ∑ k ∈ Finset.Icc 1 m, hh f a (k - 1) ω * dseq (hh f a) k ω
      = ∑ k ∈ Finset.Icc 1 m, hh f a (k - 1) ω * ee f a k ω :=
    Finset.sum_congr rfl (fun k hk => by rw [dseq_hh f a (Finset.mem_Icc.mp hk).1])
  rw [e1, e2] at this
  exact this

lemma sum_ite_le_exit (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 (N + 1), (if (k : ℕ∞) ≤ exitTime f l ω then g k else 0)
      = ∑ k ∈ Finset.Icc 1 (tN f l N ω), g k := by
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

lemma lt_exit_of_le_tN_sub_one (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) {k : ℕ}
    (hk : k ≤ tN f l N ω - 1) : (k : ℕ∞) < exitTime f l ω :=
  lt_of_le_of_lt (by exact_mod_cast hk) (tN_sub_one_lt_exit f l N ω)

lemma abs_hh_le (f : ℕ → Ω → ℝ) (a : ℝ) {l : ℝ} (hl : 0 < l) (ω : Ω) {k : ℕ}
    (hk : (k : ℕ∞) < exitTime f l ω) : |hh f a k ω| ≤ 2 * l := by
  rcases le_or_gt (k : ℕ∞) (nuT f a ω) with h | h
  · rw [hh_eq_zero_of_le f a ω h]; simp; linarith
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h)
    have hnk : n ≤ k := by
      have := h; rw [← hn] at this; exact_mod_cast this.le
    rw [hh_eq_of_nuT f a ω hn.symm hnk]
    have h1 := abs_gZ_le_of_lt_exitTime f hl ω hk
    have h2 := abs_gZ_le_of_lt_exitTime f hl ω (lt_of_le_of_lt (by exact_mod_cast hnk) hk)
    calc |gZ f k ω - gZ f n ω| ≤ |gZ f k ω| + |gZ f n ω| := abs_sub _ _
      _ ≤ 2 * l := by linarith

/-- The set `{ν < k ≤ μ}`. -/
def Ek (f : ℕ → Ω → ℝ) (l a : ℝ) (k : ℕ) : Set Ω :=
  {ω | (k : ℕ∞) ≤ exitTime f l ω ∧ nuT f a ω < k}

lemma measurableSet_Ek (hadp : StronglyAdapted ℱ f) (l a : ℝ) (j : ℕ) :
    MeasurableSet[ℱ j] (Ek f l a (j + 1)) := by
  have h1 : {ω | ((j + 1 : ℕ) : ℕ∞) ≤ exitTime f l ω} = {ω | exitTime f l ω ≤ (j : ℕ∞)}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le, Nat.cast_succ]
    exact ENat.add_one_le_iff (ENat.coe_ne_top j)
  have h2 : {ω | nuT f a ω < ((j + 1 : ℕ) : ℕ∞)} = {ω | nuT f a ω ≤ (j : ℕ∞)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Nat.cast_succ]
    exact ENat.lt_add_one_iff (ENat.coe_ne_top j)
  have : Ek f l a (j + 1) = {ω | ((j + 1 : ℕ) : ℕ∞) ≤ exitTime f l ω}
      ∩ {ω | nuT f a ω < ((j + 1 : ℕ) : ℕ∞)} := by
    ext ω; simp [Ek]
  rw [this, h1, h2]
  exact ((isStoppingTime_exitTime hadp l j).compl).inter (isStoppingTime_nuT hadp a j)

lemma measurable_ee_filt (hadp : StronglyAdapted ℱ f) (a : ℝ) {k n : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n) : Measurable[ℱ n] (ee f a k) := by
  have : ee f a k = {ω | nuT f a ω < k}.indicator (dseq f k) := by
    funext ω; simp [ee, Set.indicator_apply]
  rw [this]
  refine Measurable.indicator (measurable_dseq_filt hadp hkn) ?_
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  have h2 : {ω | nuT f a ω < ((j + 1 : ℕ) : ℕ∞)} = {ω | nuT f a ω ≤ (j : ℕ∞)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Nat.cast_succ]
    exact ENat.lt_add_one_iff (ENat.coe_ne_top j)
  rw [h2]
  exact ℱ.mono (by omega) _ (isStoppingTime_nuT hadp a j)

lemma measurable_hh_filt (hadp : StronglyAdapted ℱ f) (a : ℝ) (k : ℕ) :
    Measurable[ℱ k] (hh f a k) :=
  Finset.measurable_sum _ (fun j hj =>
    measurable_ee_filt hadp a (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)

lemma measurable_ee (hadp : StronglyAdapted ℱ f) (a : ℝ) (k : ℕ) : Measurable (ee f a k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : ee f a 0 = fun _ => (0 : ℝ) := by
      funext ω; simp [ee]
    rw [this]; exact measurable_const
  · exact (measurable_ee_filt hadp a hk le_rfl).mono (ℱ.le k) le_rfl

lemma measurable_hh (hadp : StronglyAdapted ℱ f) (a : ℝ) (k : ℕ) : Measurable (hh f a k) :=
  (measurable_hh_filt hadp a k).mono (ℱ.le k) le_rfl

lemma measurable_nuT (hadp : StronglyAdapted ℱ f) (a : ℝ) : Measurable (nuT f a) := by
  have hμ := isStoppingTime_nuT hadp a
  refine measurable_to_countable' fun x => ?_
  induction x using ENat.recTopCoe with
  | top =>
    have : nuT f a ⁻¹' {⊤} = ⋂ n : ℕ, {ω | nuT f a ω ≤ (n : ℕ∞)}ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_setOf_eq, not_le]
      exact ENat.eq_top_iff_forall_gt
    rw [this]
    exact MeasurableSet.iInter fun n => (ℱ.le n _ (hμ n)).compl
  | coe k =>
    have : nuT f a ⁻¹' {(k : ℕ∞)} = {ω | nuT f a ω = (k : ℕ∞)} := by
      ext ω; simp
    rw [this]
    exact ℱ.le k _ (hμ.measurableSet_eq k)

/-- The multiplier `1_{ν<k≤μ} h_{k-1}`. -/
noncomputable def Yk (f : ℕ → Ω → ℝ) (l a : ℝ) (k : ℕ) : Ω → ℝ :=
  (Ek f l a k).indicator (hh f a (k - 1))

/-- The multiplier `1_{ν<k≤μ} (λ − f_ν)`, written as `λ − f_{k-1} + h_{k-1}`. -/
noncomputable def Zk (f : ℕ → Ω → ℝ) (l a : ℝ) (k : ℕ) : Ω → ℝ :=
  (Ek f l a k).indicator (fun ω => l - gZ f (k - 1) ω + hh f a (k - 1) ω)

lemma abs_Yk_le (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) (a : ℝ) (k : ℕ) (ω : Ω) :
    ‖Yk f l a k ω‖ ≤ 2 * l := by
  simp only [Yk, Real.norm_eq_abs]
  by_cases hω : ω ∈ Ek f l a k
  · rw [Set.indicator_of_mem hω]
    refine abs_hh_le f a hl ω ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact lt_of_lt_of_le (by simp) (one_le_exitTime f l ω)
    · refine lt_of_lt_of_le ?_ hω.1
      exact_mod_cast Nat.sub_lt hk one_pos
  · rw [Set.indicator_of_notMem hω]; simp; linarith

lemma abs_Zk_le (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) (a : ℝ) (k : ℕ) (ω : Ω) :
    ‖Zk f l a k ω‖ ≤ 4 * l := by
  simp only [Zk, Real.norm_eq_abs]
  by_cases hω : ω ∈ Ek f l a k
  · rw [Set.indicator_of_mem hω]
    have hlt : ((k - 1 : ℕ) : ℕ∞) < exitTime f l ω := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact lt_of_lt_of_le (by simp) (one_le_exitTime f l ω)
      · refine lt_of_lt_of_le ?_ hω.1
        exact_mod_cast Nat.sub_lt hk one_pos
    have h1 := abs_hh_le f a hl ω hlt
    have h2 := abs_gZ_le_of_lt_exitTime f hl ω hlt
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  · rw [Set.indicator_of_notMem hω]; simp; linarith

lemma stronglyMeasurable_Yk (hadp : StronglyAdapted ℱ f) (l a : ℝ) (j : ℕ) :
    StronglyMeasurable[ℱ j] (Yk f l a (j + 1)) := by
  simp only [Yk, Nat.add_sub_cancel]
  exact ((measurable_hh_filt hadp a j).indicator (measurableSet_Ek hadp l a j)).stronglyMeasurable

lemma stronglyMeasurable_Zk (hadp : StronglyAdapted ℱ f) (l a : ℝ) (j : ℕ) :
    StronglyMeasurable[ℱ j] (Zk f l a (j + 1)) := by
  simp only [Zk, Nat.add_sub_cancel]
  refine Measurable.stronglyMeasurable (Measurable.indicator ?_ (measurableSet_Ek hadp l a j))
  exact ((measurable_const.sub (measurable_gZ_filt hadp le_rfl)).add (measurable_hh_filt hadp a j))

lemma Yk_one (f : ℕ → Ω → ℝ) (l a : ℝ) : Yk f l a 1 = 0 := by
  funext ω
  simp only [Yk]
  rw [Set.indicator_of_notMem]
  · rfl
  · intro h
    exact absurd (lt_of_le_of_lt (one_le_nuT f a ω) h.2) (by simp)

lemma Zk_one (f : ℕ → Ω → ℝ) (l a : ℝ) : Zk f l a 1 = 0 := by
  funext ω
  simp only [Zk]
  rw [Set.indicator_of_notMem]
  · rfl
  · intro h
    exact absurd (lt_of_le_of_lt (one_le_nuT f a ω) h.2) (by simp)

/-- The martingale transform with a bounded predictable multiplier has mean zero. -/
lemma integral_mul_dseq (hf : Martingale f ℱ P) [IsProbabilityMeasure P] {j : ℕ} (hj : 1 ≤ j)
    {Y : Ω → ℝ} (hY : StronglyMeasurable[ℱ j] Y) {C : ℝ} (hb : ∀ ω, ‖Y ω‖ ≤ C) :
    Integrable (fun ω => Y ω * dseq f (j + 1) ω) P ∧
      ∫ ω, Y ω * dseq f (j + 1) ω ∂P = 0 := by
  have hsub := hf.submartingale
  have hY' : AEStronglyMeasurable Y P := (hY.mono (ℱ.le j)).aestronglyMeasurable
  have hd : (fun ω => Y ω * dseq f (j + 1) ω) = fun ω => Y ω * f (j + 1) ω - Y ω * f j ω := by
    funext ω
    rw [dseq_eq_gZ f (by omega : 1 ≤ j + 1), gZ_pos f (by omega : 1 ≤ j + 1),
      Nat.add_sub_cancel, gZ_pos f hj]
    ring
  have hint1 : Integrable (fun ω => Y ω * f (j + 1) ω) P :=
    (hsub.integrable (j + 1)).bdd_mul hY' (Eventually.of_forall hb)
  have hint2 : Integrable (fun ω => Y ω * f j ω) P :=
    (hsub.integrable j).bdd_mul hY' (Eventually.of_forall hb)
  have hint3 : Integrable (fun ω => Y ω * (P[f (j + 1) | ℱ j]) ω) P :=
    integrable_condExp.bdd_mul hY' (Eventually.of_forall hb)
  have hce : P[fun ω => Y ω * f (j + 1) ω | ℱ j] =ᵐ[P] fun ω => Y ω * (P[f (j + 1) | ℱ j]) ω :=
    condExp_mul_of_stronglyMeasurable_left hY hint1 (hsub.integrable (j + 1))
  have hI1 : ∫ ω, Y ω * f (j + 1) ω ∂P = ∫ ω, Y ω * (P[f (j + 1) | ℱ j]) ω ∂P := by
    rw [← integral_condExp (ℱ.le j)]
    exact integral_congr_ae hce
  refine ⟨by rw [hd]; exact hint1.sub hint2, ?_⟩
  rw [hd, integral_sub hint1 hint2, hI1, ← integral_sub hint3 hint2]
  have h1 : P[f (j + 1) | ℱ j] =ᵐ[P] f j := hf.condExp_ae_eq (Nat.le_succ j)
  have : (fun ω => Y ω * (P[f (j + 1) | ℱ j]) ω - Y ω * f j ω) =ᵐ[P] fun _ => 0 := by
    filter_upwards [h1] with ω h1
    simp [h1]
  rw [integral_congr_ae this]
  simp

lemma Yk_facts (hf : Martingale f ℱ P) [IsProbabilityMeasure P] {l : ℝ} (hl : 0 < l) (a : ℝ)
    {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun ω => Yk f l a k ω * dseq f k ω) P ∧
      ∫ ω, Yk f l a k ω * dseq f k ω ∂P = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [Nat.zero_add, Yk_one, Pi.zero_apply, zero_mul]
    exact ⟨integrable_zero _ _ _, by simp⟩
  · exact integral_mul_dseq hf hj (stronglyMeasurable_Yk hf.submartingale.stronglyAdapted l a j)
      (abs_Yk_le f hl a (j + 1))

lemma Zk_facts (hf : Martingale f ℱ P) [IsProbabilityMeasure P] {l : ℝ} (hl : 0 < l) (a : ℝ)
    {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun ω => Zk f l a k ω * dseq f k ω) P ∧
      ∫ ω, Zk f l a k ω * dseq f k ω ∂P = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [Nat.zero_add, Zk_one, Pi.zero_apply, zero_mul]
    exact ⟨integrable_zero _ _ _, by simp⟩
  · exact integral_mul_dseq hf hj (stronglyMeasurable_Zk hf.submartingale.stronglyAdapted l a j)
      (abs_Zk_le f hl a (j + 1))

/-! #### The stopped quantities at `τ_N` -/

/-- `h_{τ_N}`. -/
noncomputable def H0 (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) : ℝ := hh f a (tN f l N ω) ω

/-- `h_{τ_N - 1}`. -/
noncomputable def H1 (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) : ℝ := hh f a (tN f l N ω - 1) ω

/-- `Σ_{k < τ_N} e_k²`. -/
noncomputable def AA (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (tN f l N ω - 1), ee f a k ω ^ 2

/-- The event `{ν < τ_N}`. -/
def SN (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) : Set Ω := {ω | nuT f a ω < tauN f l N ω}

/-- `f_ν 1_{ν < τ_N}`. -/
noncomputable def FNU (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) : Ω → ℝ :=
  (SN f l a N).indicator (fun ω => gZ f (nuT f a ω).toNat ω)

lemma measurable_H0 (hadp : StronglyAdapted ℱ f) (l a : ℝ) (N : ℕ) : Measurable (H0 f l a N) :=
  measurable_comp_nat (F := fun t ω => hh f a t ω) (fun t => measurable_hh hadp a t)
    (measurable_tN hadp l N)

lemma measurable_H1 (hadp : StronglyAdapted ℱ f) (l a : ℝ) (N : ℕ) : Measurable (H1 f l a N) :=
  measurable_comp_nat (F := fun t ω => hh f a (t - 1) ω) (fun t => measurable_hh hadp a (t - 1))
    (measurable_tN hadp l N)

lemma measurable_AA (hadp : StronglyAdapted ℱ f) (l a : ℝ) (N : ℕ) : Measurable (AA f l a N) :=
  measurable_comp_nat (F := fun t ω => ∑ k ∈ Finset.Icc 1 (t - 1), ee f a k ω ^ 2)
    (fun t => Finset.measurable_sum _ fun k _ => (measurable_ee hadp a k).pow_const 2)
    (measurable_tN hadp l N)

lemma measurableSet_SN (hadp : StronglyAdapted ℱ f) (l a : ℝ) (N : ℕ) :
    MeasurableSet (SN f l a N) := by
  have : SN f l a N = ⋃ j : ℕ, ({ω | nuT f a ω = (j : ℕ∞)} ∩ {ω | tauN f l N ω ≤ (j : ℕ∞)}ᶜ) := by
    ext ω
    simp only [SN, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff, not_le]
    constructor
    · intro h
      obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h)
      exact ⟨j, hj.symm, by rw [hj]; exact h⟩
    · rintro ⟨j, h1, h2⟩
      rw [h1]; exact h2
  rw [this]
  refine MeasurableSet.iUnion fun j => MeasurableSet.inter ?_ ?_
  · exact ℱ.le j _ ((isStoppingTime_nuT hadp a).measurableSet_eq j)
  · exact (ℱ.le j _ ((isStoppingTime_tauN hadp l N) j)).compl

lemma measurable_FNU (hadp : StronglyAdapted ℱ f) (l a : ℝ) (N : ℕ) :
    Measurable (FNU f l a N) := by
  refine Measurable.indicator ?_ (measurableSet_SN hadp l a N)
  exact measurable_comp_nat (F := fun t ω => gZ f t ω) (fun t => measurable_gZ hadp t)
    (measurable_from_top.comp (measurable_nuT hadp a))

lemma abs_FNU_le (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) (a : ℝ) (N : ℕ) (ω : Ω) :
    ‖FNU f l a N ω‖ ≤ l := by
  simp only [FNU, Real.norm_eq_abs]
  by_cases hω : ω ∈ SN f l a N
  · rw [Set.indicator_of_mem hω]
    have h : nuT f a ω < tauN f l N ω := hω
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h)
    have hlt : ((nuT f a ω).toNat : ℕ∞) < exitTime f l ω := by
      rw [ENat.natCast_toNat (ne_top_of_lt h)]
      exact lt_of_lt_of_le h (min_le_left _ _)
    exact abs_gZ_le_of_lt_exitTime f hl ω hlt
  · rw [Set.indicator_of_notMem hω]; simp [hl.le]

lemma abs_H1_le (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) (a : ℝ) (N : ℕ) (ω : Ω) :
    ‖H1 f l a N ω‖ ≤ 2 * l :=
  abs_hh_le f a hl ω (tN_sub_one_lt_exit f l N ω)

/-- In the case `ν < τ_N`: `ν = n` with `1 ≤ n < τ_N`. -/
lemma SN_cases (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) (hω : ω ∈ SN f l a N) :
    ∃ n : ℕ, nuT f a ω = n ∧ 1 ≤ n ∧ n < tN f l N ω ∧ FNU f l a N ω = gZ f n ω := by
  have h : nuT f a ω < tauN f l N ω := hω
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt h)
  refine ⟨n, hn.symm, ?_, ?_, ?_⟩
  · have := one_le_nuT f a ω; rw [← hn] at this; exact_mod_cast this
  · have := h; rw [← hn, ← coe_tN] at this; exact_mod_cast this
  · simp only [FNU, Set.indicator_of_mem hω, ← hn, ENat.toNat_coe]

lemma not_SN (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) (hω : ω ∉ SN f l a N) :
    ((tN f l N ω : ℕ) : ℕ∞) ≤ nuT f a ω := by
  have h : ¬ nuT f a ω < tauN f l N ω := hω
  rw [coe_tN]; exact not_lt.mp h

lemma abs_H0_le (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) (a : ℝ) (N : ℕ) (ω : Ω) :
    ‖H0 f l a N ω‖ ≤ ‖G0 f l N ω‖ + l := by
  simp only [H0, G0, Real.norm_eq_abs]
  by_cases hω : ω ∈ SN f l a N
  · obtain ⟨n, hn, hn1, hnm, -⟩ := SN_cases f l a N ω hω
    rw [hh_eq_of_nuT f a ω hn hnm.le]
    have h2 := abs_gZ_le_of_lt_exitTime f hl ω
      (lt_of_le_of_lt (by exact_mod_cast (by omega : n ≤ tN f l N ω - 1))
        (tN_sub_one_lt_exit f l N ω))
    calc |gZ f (tN f l N ω) ω - gZ f n ω| ≤ |gZ f (tN f l N ω) ω| + |gZ f n ω| := abs_sub _ _
      _ ≤ _ := by linarith
  · rw [hh_eq_zero_of_le f a ω (not_SN f l a N ω hω)]
    simp only [abs_zero]
    positivity

/-- Pointwise: the transform sum with `Y`. -/
lemma sum_Yk_eq (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.Icc 1 (N + 1), Yk f l a k ω * dseq f k ω
      = ∑ k ∈ Finset.Icc 1 (tN f l N ω), hh f a (k - 1) ω * ee f a k ω := by
  rw [← sum_ite_le_exit f l N ω]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Yk, ee]
  by_cases h1 : (k : ℕ∞) ≤ exitTime f l ω
  · by_cases h2 : nuT f a ω < k
    · rw [Set.indicator_of_mem (show ω ∈ Ek f l a k from ⟨h1, h2⟩), if_pos h1, if_pos h2]
    · rw [Set.indicator_of_notMem (fun h => h2 h.2), if_pos h1, if_neg h2]; simp
  · rw [Set.indicator_of_notMem (fun h => h1 h.1), if_neg h1]; simp

/-- Pointwise: the transform sum with `Z` equals `(λ − f_ν) h_{τ_N}`. -/
lemma sum_Zk_eq (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.Icc 1 (N + 1), Zk f l a k ω * dseq f k ω
      = (l - FNU f l a N ω) * H0 f l a N ω := by
  have h1 : ∑ k ∈ Finset.Icc 1 (N + 1), Zk f l a k ω * dseq f k ω
      = ∑ k ∈ Finset.Icc 1 (tN f l N ω),
          (if nuT f a ω < k then (l - gZ f (k - 1) ω + hh f a (k - 1) ω) * dseq f k ω else 0) := by
    rw [← sum_ite_le_exit f l N ω]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Zk]
    by_cases h1 : (k : ℕ∞) ≤ exitTime f l ω
    · by_cases h2 : nuT f a ω < k
      · rw [Set.indicator_of_mem (show ω ∈ Ek f l a k from ⟨h1, h2⟩), if_pos h1, if_pos h2]
      · rw [Set.indicator_of_notMem (fun h => h2 h.2), if_pos h1, if_neg h2]; simp
    · rw [Set.indicator_of_notMem (fun h => h1 h.1), if_neg h1]; simp
  rw [h1]
  have h2 : (l - FNU f l a N ω) * H0 f l a N ω
      = ∑ k ∈ Finset.Icc 1 (tN f l N ω), (l - FNU f l a N ω) * ee f a k ω := by
    simp only [H0, hh, Finset.mul_sum]
  rw [h2]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h2 : nuT f a ω < k
  · rw [if_pos h2, ee_eq_of_lt f a ω h2]
    have hω : ω ∈ SN f l a N := by
      show nuT f a ω < tauN f l N ω
      exact lt_of_lt_of_le h2 (by rw [← coe_tN]; exact_mod_cast (Finset.mem_Icc.mp hk).2)
    obtain ⟨n, hn, hn1, -, hF⟩ := SN_cases f l a N ω hω
    have hnk : n ≤ k - 1 := by
      have := h2; rw [hn] at this
      have : n < k := by exact_mod_cast this
      omega
    rw [hF, hh_eq_of_nuT f a ω hn hnk]
    ring
  · rw [if_neg h2, ee_eq_zero_of_le f a ω (not_lt.mp h2)]; ring

/-- Pointwise: `h_{τ_N} h_{τ_N - 1} ≤ (λ − f_ν) h_{τ_N} + λ² 1_{ν < τ_N}` for nonnegative `f`. -/
lemma H0_mul_H1_le (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) (a : ℝ) (N : ℕ) (ω : Ω)
    (hnn : ∀ k, 0 ≤ gZ f k ω) :
    H0 f l a N ω * H1 f l a N ω
      ≤ (l - FNU f l a N ω) * H0 f l a N ω + l ^ 2 * (SN f l a N).indicator 1 ω := by
  by_cases hω : ω ∈ SN f l a N
  · rw [Set.indicator_of_mem hω]
    obtain ⟨n, hn, hn1, hnm, hF⟩ := SN_cases f l a N ω hω
    simp only [H0, H1, Pi.one_apply, mul_one]
    rw [hF, hh_eq_of_nuT f a ω hn hnm.le, hh_eq_of_nuT f a ω hn (by omega)]
    have hx := hnn (tN f l N ω)
    have hy0 := hnn (tN f l N ω - 1)
    have hz0 := hnn n
    have hy1 := abs_gZ_le_of_lt_exitTime f hl ω (tN_sub_one_lt_exit f l N ω)
    have hz1 := abs_gZ_le_of_lt_exitTime f hl ω
      (lt_of_le_of_lt (by exact_mod_cast (by omega : n ≤ tN f l N ω - 1))
        (tN_sub_one_lt_exit f l N ω))
    rw [abs_le] at hy1 hz1
    have e1 : 0 ≤ gZ f (tN f l N ω) ω * (l - gZ f (tN f l N ω - 1) ω) :=
      mul_nonneg hx (by linarith)
    have e2 : gZ f n ω * (l - gZ f (tN f l N ω - 1) ω) ≤ l * l :=
      mul_le_mul hz1.2 (by linarith) (by linarith) hl.le
    nlinarith
  · rw [Set.indicator_of_notMem hω]
    simp only [H0, H1]
    rw [hh_eq_zero_of_le f a ω (not_SN f l a N ω hω)]
    simp

/-- Pointwise: `S_{τ_N-1}² − (a + λ²) ≤ Σ_{ν<k<τ_N} d_k²` for nonnegative `f`. -/
lemma SQ_sub_le_AA (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) {a : ℝ} (ha : 0 < a) (N : ℕ) (ω : Ω)
    (hnn : ∀ k, 0 ≤ gZ f k ω) :
    SQ f l N ω - (a + l ^ 2) ≤ AA f l a N ω := by
  rw [SQ_eq_SSQ]
  by_cases hω : ω ∈ SN f l a N
  · obtain ⟨n, hn, hn1, hnm, -⟩ := SN_cases f l a N ω hω
    have hnm1 : n ≤ tN f l N ω - 1 := by omega
    rw [SSQ_eq_of_nuT f a ω hn hnm1]
    obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le' hn1
    rw [SSQ_succ]
    have h1 : SSQ f p ω ≤ a :=
      SSQ_le_of_lt_nuT f ha ω (lt_nuT_of_lt_coe f a ω hn (Nat.lt_succ_self p))
    have h2 : dseq f (p + 1) ω ^ 2 ≤ l ^ 2 := by
      rw [dseq_eq_gZ f (by omega : 1 ≤ p + 1)]
      simp only [Nat.add_sub_cancel]
      have hz1 := abs_gZ_le_of_lt_exitTime f hl ω
        (lt_of_le_of_lt (by exact_mod_cast hnm1) (tN_sub_one_lt_exit f l N ω))
      have hz2 := abs_gZ_le_of_lt_exitTime f hl ω
        (lt_of_le_of_lt (by exact_mod_cast (by omega : p ≤ tN f l N ω - 1))
          (tN_sub_one_lt_exit f l N ω))
      rw [abs_le] at hz1 hz2
      have := hnn (p + 1)
      have := hnn p
      nlinarith
    simp only [AA]
    linarith
  · have : ((tN f l N ω - 1 : ℕ) : ℕ∞) < nuT f a ω :=
      lt_of_lt_of_le (by exact_mod_cast Nat.sub_lt (one_le_tN f l N ω) one_pos)
        (not_SN f l a N ω hω)
    have h1 := SSQ_le_of_lt_nuT f ha ω this
    have h2 : 0 ≤ AA f l a N ω := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith

/-- `{ν < τ_N} ⊆ {a < S_{τ_N-1}²}`. -/
lemma SN_subset (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) :
    SN f l a N ⊆ {ω | a < SQ f l N ω} := by
  intro ω hω
  obtain ⟨n, hn, hn1, hnm, -⟩ := SN_cases f l a N ω hω
  have h1 := (nuT_spec f a ω hn).2
  show a < SQ f l N ω
  rw [SQ_eq_SSQ]
  exact lt_of_lt_of_le h1 (SSQ_mono f ω (by omega))

/-- The pointwise identity at `τ_N`. -/
lemma AA_identity (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) :
    AA f l a N ω = 2 * (H0 f l a N ω * H1 f l a N ω) - H1 f l a N ω ^ 2
      - 2 * ∑ k ∈ Finset.Icc 1 (N + 1), Yk f l a k ω * dseq f k ω := by
  rw [sum_Yk_eq]
  have := hh_identity f a ω (one_le_tN f l N ω)
  simp only [AA, H0, H1]
  linarith

/-- The finite-`N` bound (18.5). -/
lemma finite_bound_185 [IsProbabilityMeasure P] (hf : Martingale f ℱ P)
    (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n) {l : ℝ} (hl : 0 < l) {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (SQ f l N ω - (a + l ^ 2)) ∂P
      ≤ ENNReal.ofReal (2 * l ^ 2) * P {ω | ENNReal.ofReal a < ENNReal.ofReal (SQ f l N ω)} := by
  have hadp := hf.submartingale.stronglyAdapted
  -- a.e. nonnegativity of all `f_k`
  have hnn' : ∀ᵐ ω ∂P, ∀ k, 0 ≤ gZ f k ω := by
    have : ∀ᵐ ω ∂P, ∀ n, 1 ≤ n → 0 ≤ f n ω := by
      rw [ae_all_iff]
      intro n
      by_cases hn : 1 ≤ n
      · filter_upwards [hnn n hn] with ω hω
        intro _; exact hω
      · exact ae_of_all _ (fun ω h => absurd h hn)
    filter_upwards [this] with ω hω
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [gZ]
    · rw [gZ_pos f hk]; exact hω k hk
  -- integrability
  have hH1 : Integrable (H1 f l a N) P :=
    Integrable.mono' (integrable_const (2 * l)) (measurable_H1 hadp l a N).aestronglyMeasurable
      (ae_of_all _ (abs_H1_le f hl a N))
  have hH0 : Integrable (H0 f l a N) P :=
    Integrable.mono' ((integrable_G0 hf.submartingale l N).norm.add (integrable_const l))
      (measurable_H0 hadp l a N).aestronglyMeasurable (ae_of_all _ (abs_H0_le f hl a N))
  have hH0H1 : Integrable (fun ω => H0 f l a N ω * H1 f l a N ω) P := by
    have := hH0.bdd_mul (measurable_H1 hadp l a N).aestronglyMeasurable
      (Eventually.of_forall (abs_H1_le f hl a N))
    exact this.congr (ae_of_all _ (fun ω => mul_comm _ _))
  have hH1sq : Integrable (fun ω => H1 f l a N ω ^ 2) P := by
    have := hH1.bdd_mul (measurable_H1 hadp l a N).aestronglyMeasurable
      (Eventually.of_forall (abs_H1_le f hl a N))
    exact this.congr (ae_of_all _ (fun ω => by simp [sq]))
  have hFH : Integrable (fun ω => (l - FNU f l a N ω) * H0 f l a N ω) P := by
    refine hH0.bdd_mul (c := 2 * l)
      (measurable_const.sub (measurable_FNU hadp l a N)).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    have := abs_FNU_le f hl a N ω
    rw [Real.norm_eq_abs, abs_le] at this ⊢
    constructor <;> linarith
  have hYsum : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 (N + 1), Yk f l a k ω * dseq f k ω) P :=
    integrable_finset_sum _ (fun k hk => (Yk_facts hf hl a (Finset.mem_Icc.mp hk).1).1)
  have hYint : ∫ ω, ∑ k ∈ Finset.Icc 1 (N + 1), Yk f l a k ω * dseq f k ω ∂P = 0 := by
    rw [integral_finset_sum _ (fun k hk => (Yk_facts hf hl a (Finset.mem_Icc.mp hk).1).1)]
    exact Finset.sum_eq_zero (fun k hk => (Yk_facts hf hl a (Finset.mem_Icc.mp hk).1).2)
  have hZint : ∫ ω, (l - FNU f l a N ω) * H0 f l a N ω ∂P = 0 := by
    have h1 : (fun ω => (l - FNU f l a N ω) * H0 f l a N ω)
        = fun ω => ∑ k ∈ Finset.Icc 1 (N + 1), Zk f l a k ω * dseq f k ω := by
      funext ω; exact (sum_Zk_eq f l a N ω).symm
    rw [h1, integral_finset_sum _ (fun k hk => (Zk_facts hf hl a (Finset.mem_Icc.mp hk).1).1)]
    exact Finset.sum_eq_zero (fun k hk => (Zk_facts hf hl a (Finset.mem_Icc.mp hk).1).2)
  have hAAeq : AA f l a N = fun ω => 2 * (H0 f l a N ω * H1 f l a N ω) - H1 f l a N ω ^ 2
      - 2 * ∑ k ∈ Finset.Icc 1 (N + 1), Yk f l a k ω * dseq f k ω := by
    funext ω; exact AA_identity f l a N ω
  have hAA : Integrable (AA f l a N) P := by
    rw [hAAeq]
    exact ((hH0H1.const_mul 2).sub hH1sq).sub (hYsum.const_mul 2)
  have hSmeas : MeasurableSet (SN f l a N) := measurableSet_SN hadp l a N
  have hTmeas : MeasurableSet {ω | a < SQ f l N ω} :=
    measurableSet_lt measurable_const (measurable_SQ hadp l N)
  -- the main integral inequality
  have hmain : ∫ ω, AA f l a N ω ∂P ≤ 2 * l ^ 2 * (P {ω | a < SQ f l N ω}).toReal := by
    have hI : ∫ ω, AA f l a N ω ∂P = 2 * ∫ ω, H0 f l a N ω * H1 f l a N ω ∂P
        - ∫ ω, H1 f l a N ω ^ 2 ∂P - 2 * 0 := by
      have e0 : ∫ ω, AA f l a N ω ∂P = ∫ ω, (2 * (H0 f l a N ω * H1 f l a N ω) - H1 f l a N ω ^ 2
          - 2 * ∑ k ∈ Finset.Icc 1 (N + 1), Yk f l a k ω * dseq f k ω) ∂P :=
        integral_congr_ae (ae_of_all _ (fun ω => AA_identity f l a N ω))
      have e1 : ∫ ω, (2 * (H0 f l a N ω * H1 f l a N ω) - H1 f l a N ω ^ 2
          - 2 * ∑ k ∈ Finset.Icc 1 (N + 1), Yk f l a k ω * dseq f k ω) ∂P
          = (∫ ω, (2 * (H0 f l a N ω * H1 f l a N ω) - H1 f l a N ω ^ 2) ∂P)
            - ∫ ω, 2 * ∑ k ∈ Finset.Icc 1 (N + 1), Yk f l a k ω * dseq f k ω ∂P :=
        integral_sub ((hH0H1.const_mul 2).sub hH1sq) (hYsum.const_mul 2)
      have e2 : ∫ ω, (2 * (H0 f l a N ω * H1 f l a N ω) - H1 f l a N ω ^ 2) ∂P
          = (∫ ω, 2 * (H0 f l a N ω * H1 f l a N ω) ∂P) - ∫ ω, H1 f l a N ω ^ 2 ∂P :=
        integral_sub (hH0H1.const_mul 2) hH1sq
      rw [e0, e1, e2, integral_const_mul, integral_const_mul, hYint]
    have hsq : 0 ≤ ∫ ω, H1 f l a N ω ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg _)
    have hind : Integrable (fun ω => l ^ 2 * (SN f l a N).indicator (1 : Ω → ℝ) ω) P :=
      ((integrable_const (1 : ℝ)).indicator hSmeas).const_mul _
    have hcross : ∫ ω, H0 f l a N ω * H1 f l a N ω ∂P
        ≤ ∫ ω, ((l - FNU f l a N ω) * H0 f l a N ω + l ^ 2 * (SN f l a N).indicator 1 ω) ∂P := by
      apply integral_mono_ae hH0H1 (hFH.add hind)
      filter_upwards [hnn'] with ω hω
      exact H0_mul_H1_le f hl a N ω hω
    rw [integral_add hFH hind, hZint, zero_add, integral_const_mul, integral_indicator_one hSmeas]
      at hcross
    have hPle : (P (SN f l a N)).toReal ≤ (P {ω | a < SQ f l N ω}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (SN_subset f l a N))
    rw [hI]
    simp only [measureReal_def] at hcross
    have := mul_le_mul_of_nonneg_left hPle (by positivity : (0:ℝ) ≤ l ^ 2)
    nlinarith
  -- pass to the lower integral
  have hAAnn : 0 ≤ᵐ[P] AA f l a N := ae_of_all _ (fun ω => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc ∫⁻ ω, ENNReal.ofReal (SQ f l N ω - (a + l ^ 2)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (AA f l a N ω) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [hnn'] with ω hω
        exact ENNReal.ofReal_le_ofReal (SQ_sub_le_AA f hl ha N ω hω)
    _ = ENNReal.ofReal (∫ ω, AA f l a N ω ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hAA hAAnn).symm
    _ ≤ ENNReal.ofReal (2 * l ^ 2 * (P {ω | a < SQ f l N ω}).toReal) :=
        ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal (2 * l ^ 2) * P {ω | a < SQ f l N ω} := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ = ENNReal.ofReal (2 * l ^ 2) * P {ω | ENNReal.ofReal a < ENNReal.ofReal (SQ f l N ω)} := by
        congr 2
        ext ω
        simp only [Set.mem_setOf_eq]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).symm

/-- Tonelli: the tail integral as an expectation of a Lebesgue measure. -/
lemma tail_eq_volume [IsProbabilityMeasure P] (G : Ω → ℝ≥0∞) (hG : Measurable G) (c : ℝ) :
    ∫⁻ x in Set.Ioi c, P {ω | ENNReal.ofReal x < G ω}
      = ∫⁻ ω, volume ({x : ℝ | ENNReal.ofReal x < G ω} ∩ Set.Ioi c) ∂P := by
  set S : Set (ℝ × Ω) := {p | ENNReal.ofReal p.1 < G p.2} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_lt (measurable_fst.ennreal_ofReal) (hG.comp measurable_snd)
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi c)) (ν := P)
    (f := fun x ω => S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω))
    (measurable_const.indicator hS).aemeasurable
  have hl : ∀ x : ℝ, ∫⁻ ω, S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω) ∂P
      = P {ω | ENNReal.ofReal x < G ω} := by
    intro x
    have : (fun ω => S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω))
        = {ω | ENNReal.ofReal x < G ω}.indicator 1 := by
      ext ω
      simp [S, Set.indicator_apply]
    rw [this, lintegral_indicator_one (measurableSet_lt measurable_const hG)]
  have hr : ∀ ω : Ω, ∫⁻ x in Set.Ioi c, S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω)
      = volume ({x : ℝ | ENNReal.ofReal x < G ω} ∩ Set.Ioi c) := by
    intro ω
    have : (fun x => S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω))
        = {x : ℝ | ENNReal.ofReal x < G ω}.indicator 1 := by
      ext x
      simp [S, Set.indicator_apply]
    rw [this, lintegral_indicator_one (measurableSet_lt ENNReal.measurable_ofReal measurable_const),
      Measure.restrict_apply (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
  simp_rw [hl, hr] at hswap
  exact hswap

lemma volume_tail_le (g : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    volume ({x : ℝ | ENNReal.ofReal x < ENNReal.ofReal g} ∩ Set.Ioi c) ≤ ENNReal.ofReal (g - c) := by
  calc volume ({x : ℝ | ENNReal.ofReal x < ENNReal.ofReal g} ∩ Set.Ioi c)
      ≤ volume (Set.Ioo c g) := by
        apply measure_mono
        rintro x ⟨hx1, hx2⟩
        simp only [Set.mem_setOf_eq] at hx1
        have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt hc hx2)
        rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx0] at hx1
        exact ⟨hx2, hx1⟩
    _ = ENNReal.ofReal (g - c) := Real.volume_Ioo

/-- (18.5). -/
theorem eq_18_5_core {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)
    (l : ℝ) (hl : 0 < l) (a : ℝ) (ha : 0 < a) :
    ∫⁻ s in Set.Ioi (a + l ^ 2), P {ω | ENNReal.ofReal s < sqFnAt f (exitTime f l ω - 1) ω ^ 2}
      ≤ ENNReal.ofReal (2 * l ^ 2) * P {ω | ENNReal.ofReal a < sqFnAt f (exitTime f l ω - 1) ω ^ 2} := by
  have hadp := hf.submartingale.stronglyAdapted
  set GN : ℕ → Ω → ℝ≥0∞ := fun N ω => ENNReal.ofReal (SQ f l N ω) with hGNdef
  have hGN : ∀ N ω, sqFnAt f (tauN f l N ω - 1) ω ^ 2 = GN N ω := fun N ω => sqFnAt_tauN_sq f l N ω
  have hG : ∀ ω, sqFnAt f (exitTime f l ω - 1) ω ^ 2 = ⨆ N, GN N ω := fun ω => by
    rw [← iSup_sqFnAt_tauN]
    simp only [hGN]
  have hmono : ∀ ω, Monotone (fun N => GN N ω) := by
    intro ω N M h
    simp only
    rw [← hGN, ← hGN]
    exact pow_le_pow_left₀ bot_le (sqFnAt_mono f ω (tsub_le_tsub_right (tauN_mono f l ω h) 1)) 2
  have hGNmeas : ∀ N, Measurable (GN N) := fun N => (measurable_SQ hadp l N).ennreal_ofReal
  have hset : ∀ s : ℝ, {ω | ENNReal.ofReal s < sqFnAt f (exitTime f l ω - 1) ω ^ 2}
      = ⋃ N, {ω | ENNReal.ofReal s < GN N ω} := by
    intro s; ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, hG, lt_iSup_iff]
  have hPN : ∀ s : ℝ, P {ω | ENNReal.ofReal s < sqFnAt f (exitTime f l ω - 1) ω ^ 2}
      = ⨆ N, P {ω | ENNReal.ofReal s < GN N ω} := by
    intro s
    rw [hset]
    exact Monotone.measure_iUnion (fun N M h ω hω => lt_of_lt_of_le hω (hmono ω h))
  have hanti : ∀ N, Antitone (fun s : ℝ => P {ω | ENNReal.ofReal s < GN N ω}) := by
    intro N s t hst
    apply measure_mono
    intro ω hω
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hω
  have hc : 0 ≤ a + l ^ 2 := by positivity
  calc ∫⁻ s in Set.Ioi (a + l ^ 2), P {ω | ENNReal.ofReal s < sqFnAt f (exitTime f l ω - 1) ω ^ 2}
      = ∫⁻ s in Set.Ioi (a + l ^ 2), ⨆ N, P {ω | ENNReal.ofReal s < GN N ω} := by
        simp_rw [hPN]
    _ = ⨆ N, ∫⁻ s in Set.Ioi (a + l ^ 2), P {ω | ENNReal.ofReal s < GN N ω} := by
        rw [lintegral_iSup (fun N => (hanti N).measurable)]
        refine fun N M h s => ?_
        apply measure_mono
        intro ω hω
        exact lt_of_lt_of_le hω (hmono ω h)
    _ ≤ ENNReal.ofReal (2 * l ^ 2) * P {ω | ENNReal.ofReal a < sqFnAt f (exitTime f l ω - 1) ω ^ 2} := by
        refine iSup_le fun N => ?_
        calc ∫⁻ s in Set.Ioi (a + l ^ 2), P {ω | ENNReal.ofReal s < GN N ω}
            = ∫⁻ ω, volume ({x : ℝ | ENNReal.ofReal x < GN N ω} ∩ Set.Ioi (a + l ^ 2)) ∂P :=
              tail_eq_volume (GN N) (hGNmeas N) _
          _ ≤ ∫⁻ ω, ENNReal.ofReal (SQ f l N ω - (a + l ^ 2)) ∂P :=
              lintegral_mono fun ω => volume_tail_le (SQ f l N ω) hc
          _ ≤ ENNReal.ofReal (2 * l ^ 2) * P {ω | ENNReal.ofReal a < GN N ω} :=
              finite_bound_185 hf hnn hl ha N
          _ ≤ _ := by
              refine mul_le_mul' le_rfl (measure_mono ?_)
              intro ω hω
              simp only [Set.mem_setOf_eq] at hω ⊢
              rw [hG]
              exact lt_of_lt_of_le hω (le_iSup (fun N => GN N ω) N)

end E185

section L181

variable {g : Ω → ℝ≥0∞}

lemma tailm_antitone (P : Measure Ω) (g : Ω → ℝ≥0∞) :
    Antitone (fun x : ℝ => P {ω | ENNReal.ofReal x < g ω}) := by
  intro x y hxy
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at *
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hxy) hω

lemma tailm_measurable (P : Measure Ω) (g : Ω → ℝ≥0∞) :
    Measurable (fun x : ℝ => P {ω | ENNReal.ofReal x < g ω}) :=
  (tailm_antitone P g).measurable

lemma ae_ne_top_of_tail [IsProbabilityMeasure P] (g : Ω → ℝ≥0∞) (α : ℝ)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω}
        ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω}) :
    ∀ᵐ ω ∂P, g ω ≠ ⊤ := by
  have hsub : ∀ x : ℝ, {ω | g ω = ⊤} ⊆ {ω | ENNReal.ofReal x < g ω} := fun x ω hω => by
    simp only [Set.mem_setOf_eq] at *
    rw [hω]; exact ENNReal.ofReal_lt_top
  have hfin : ∫⁻ x in Set.Ioi (1:ℝ), P {ω | ENNReal.ofReal x < g ω} < ⊤ := by
    calc _ ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal 1 < g ω} := h184 1 one_pos
      _ ≤ ENNReal.ofReal α * 1 := by gcongr; exact prob_le_one
      _ < ⊤ := by simp
  by_contra hcon
  rw [ae_iff] at hcon
  simp only [ne_eq, not_not] at hcon
  have hpos : 0 < P {ω | g ω = ⊤} := pos_iff_ne_zero.mpr hcon
  have : ∫⁻ x in Set.Ioi (1:ℝ), P {ω | g ω = ⊤}
      ≤ ∫⁻ x in Set.Ioi (1:ℝ), P {ω | ENNReal.ofReal x < g ω} :=
    lintegral_mono (fun x => measure_mono (hsub x))
  rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top hpos.ne'] at this
  exact absurd (lt_of_le_of_lt this hfin) (lt_irrefl _)

lemma tail_int_zero_le [IsProbabilityMeasure P] (g : Ω → ℝ≥0∞) (α : ℝ)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω}
        ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω}) :
    ∫⁻ x in Set.Ioi (0:ℝ), P {ω | ENNReal.ofReal x < g ω} ≤ ENNReal.ofReal α := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε' : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 (ε:ℝ) ∪ Set.Ioi (ε:ℝ) :=
    (Set.Ioc_union_Ioi_eq_Ioi hε'.le).symm
  rw [hsplit]
  calc ∫⁻ x in Set.Ioc 0 (ε:ℝ) ∪ Set.Ioi (ε:ℝ), P {ω | ENNReal.ofReal x < g ω}
      ≤ (∫⁻ x in Set.Ioc 0 (ε:ℝ), P {ω | ENNReal.ofReal x < g ω})
          + ∫⁻ x in Set.Ioi (ε:ℝ), P {ω | ENNReal.ofReal x < g ω} := lintegral_union_le _ _ _
    _ ≤ (∫⁻ _ in Set.Ioc 0 (ε:ℝ), (1:ℝ≥0∞))
          + ENNReal.ofReal α * P {ω | ENNReal.ofReal (ε:ℝ) < g ω} := by
        gcongr
        · exact prob_le_one
        · exact h184 ε hε'
    _ ≤ ε + ENNReal.ofReal α := by
        rw [setLIntegral_const, Real.volume_Ioc]
        gcongr
        · simp
        · calc ENNReal.ofReal α * P {ω | ENNReal.ofReal (ε:ℝ) < g ω}
              ≤ ENNReal.ofReal α * 1 := by gcongr; exact prob_le_one
            _ = _ := mul_one _
    _ = ENNReal.ofReal α + ε := add_comm _ _

lemma hasDerivAt_exp_mul (t x : ℝ) :
    HasDerivAt (fun s => Real.exp (t * s)) (t * Real.exp (t * x)) x := by
  have h := ((hasDerivAt_id x).const_mul t).exp
  simpa [mul_comm] using h

lemma integral_t_exp (t r : ℝ) :
    ∫ s in (0:ℝ)..r, t * Real.exp (t * s) = Real.exp (t * r) - 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => Real.exp (t * s))
    (fun x _ => hasDerivAt_exp_mul t x)]
  · simp
  · exact (by fun_prop : Continuous fun s => t * Real.exp (t * s)).intervalIntegrable _ _

/-- (B1) -/
lemma ofReal_exp_sub_one_eq (t : ℝ) (ht : 0 < t) {y : ℝ} (hy : 0 < y) :
    ENNReal.ofReal (Real.exp (t * y) - 1)
      = ∫⁻ x in Set.Ioo 0 y, ENNReal.ofReal (t * Real.exp (t * x)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hy.le, integral_t_exp]
  · exact ((by fun_prop : Continuous fun s => t * Real.exp (t * s)).integrableOn_Icc).mono_set
      Set.Ioo_subset_Icc_self
  · exact ae_of_all _ (fun x => by positivity)

/-- (B2) the Tonelli swap. -/
lemma swap_bound [IsProbabilityMeasure P] (g : Ω → ℝ≥0∞) (α : ℝ) (hα : 0 < α)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω}
        ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω})
    (t : ℝ) (ht : 0 < t) (N : ℝ) :
    ∫⁻ y in Set.Ioo 0 N, P {ω | ENNReal.ofReal y < g ω} * ENNReal.ofReal (Real.exp (t * y) - 1)
      ≤ ENNReal.ofReal (α * t) *
        ∫⁻ x in Set.Ioo 0 N, ENNReal.ofReal (Real.exp (t * x)) * P {ω | ENNReal.ofReal x < g ω} := by
  set m : ℝ → ℝ≥0∞ := fun x => P {ω | ENNReal.ofReal x < g ω} with hm
  have hmm : Measurable m := tailm_measurable P g
  set G : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (t * Real.exp (t * x)) with hG
  have hGm : Measurable G := by fun_prop
  let H : ℝ → ℝ → ℝ≥0∞ := fun x y => if 0 < x ∧ x < y ∧ y < N then G x * m y else 0
  have hH : Measurable (Function.uncurry H) := by
    have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < N} :=
      (measurableSet_lt measurable_const measurable_fst).inter
        ((measurableSet_lt measurable_fst measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_const))
    exact Measurable.ite hS ((hGm.comp measurable_fst).mul (hmm.comp measurable_snd))
      measurable_const
  -- step 1: LHS = ∫⁻ y, ∫⁻ x, H x y
  have h1 : ∫⁻ y in Set.Ioo 0 N, m y * ENNReal.ofReal (Real.exp (t * y) - 1)
      = ∫⁻ y, ∫⁻ x, H x y := by
    rw [← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ Set.Ioo 0 N
    · rw [Set.indicator_of_mem hy, ofReal_exp_sub_one_eq t ht hy.1, ← lintegral_const_mul' _ _
        (measure_ne_top _ _), ← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ Set.Ioo 0 y
      · rw [Set.indicator_of_mem hx]
        simp only [H, hx.1, hx.2, hy.2, and_self, if_true]
        ring
      · rw [Set.indicator_of_notMem hx]
        simp only [H]
        rw [if_neg]
        rintro ⟨h0, hxy, -⟩
        exact hx ⟨h0, hxy⟩
    · rw [Set.indicator_of_notMem hy]
      symm
      calc ∫⁻ x, H x y = ∫⁻ _x, (0:ℝ≥0∞) := lintegral_congr (fun x => by
              simp only [H]
              rw [if_neg]
              rintro ⟨h0, hxy, hyN⟩
              exact hy ⟨h0.trans hxy, hyN⟩)
        _ = 0 := lintegral_zero
  -- step 2: swap
  have h2 : ∫⁻ y, ∫⁻ x, H x y = ∫⁻ x, ∫⁻ y, H x y :=
    (lintegral_lintegral_swap hH.aemeasurable).symm
  -- step 3: inner bound
  have h3 : ∀ x, ∫⁻ y, H x y ≤ (Set.Ioo 0 N).indicator (fun x => G x * (ENNReal.ofReal α * m x)) x := by
    intro x
    by_cases hx : x ∈ Set.Ioo 0 N
    · rw [Set.indicator_of_mem hx]
      have : ∫⁻ y, H x y = ∫⁻ y in Set.Ioo x N, G x * m y := by
        rw [← lintegral_indicator measurableSet_Ioo]
        apply lintegral_congr
        intro y
        by_cases hy : y ∈ Set.Ioo x N
        · rw [Set.indicator_of_mem hy]
          simp only [H, hx.1, hy.1, hy.2, and_self, if_true]
        · rw [Set.indicator_of_notMem hy]
          simp only [H]
          rw [if_neg]
          rintro ⟨-, hxy, hyN⟩
          exact hy ⟨hxy, hyN⟩
      rw [this, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      calc ∫⁻ y in Set.Ioo x N, m y ≤ ∫⁻ y in Set.Ioi x, m y :=
            lintegral_mono_set Set.Ioo_subset_Ioi_self
        _ ≤ ENNReal.ofReal α * m x := h184 x hx.1
    · rw [Set.indicator_of_notMem hx]
      apply le_of_eq
      calc ∫⁻ y, H x y = ∫⁻ _y, (0:ℝ≥0∞) := lintegral_congr (fun y => by
              simp only [H]
              rw [if_neg]
              rintro ⟨h0, hxy, hyN⟩
              exact hx ⟨h0, hxy.trans hyN⟩)
        _ = 0 := lintegral_zero
  rw [h1, h2]
  calc ∫⁻ x, ∫⁻ y, H x y
      ≤ ∫⁻ x, (Set.Ioo 0 N).indicator (fun x => G x * (ENNReal.ofReal α * m x)) x :=
        lintegral_mono h3
    _ = ∫⁻ x in Set.Ioo 0 N, G x * (ENNReal.ofReal α * m x) := lintegral_indicator measurableSet_Ioo _
    _ = ∫⁻ x in Set.Ioo 0 N, ENNReal.ofReal (α * t) * (ENNReal.ofReal (Real.exp (t * x)) * m x) := by
        apply lintegral_congr
        intro x
        simp only [G]
        rw [ENNReal.ofReal_mul ht.le, ENNReal.ofReal_mul hα.le]
        ring
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- (B) truncated bound. -/
lemma trunc_bound [IsProbabilityMeasure P] (g : Ω → ℝ≥0∞) (α : ℝ) (hα : 0 < α)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω}
        ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω})
    (t : ℝ) (ht : 0 < t) (htα : t < α⁻¹) (N : ℝ) :
    ∫⁻ x in Set.Ioo 0 N, ENNReal.ofReal (Real.exp (t * x)) * P {ω | ENNReal.ofReal x < g ω}
      ≤ ENNReal.ofReal (α / (1 - α * t)) := by
  set m : ℝ → ℝ≥0∞ := fun x => P {ω | ENNReal.ofReal x < g ω} with hm
  have hmm : Measurable m := tailm_measurable P g
  set J := ∫⁻ x in Set.Ioo 0 N, ENNReal.ofReal (Real.exp (t * x)) * m x with hJ
  have hαt : α * t < 1 := by
    have := mul_lt_mul_of_pos_right htα hα
    rwa [inv_mul_cancel₀ hα.ne', mul_comm] at this
  have hJfin : J < ⊤ := by
    calc J ≤ ∫⁻ _ in Set.Ioo 0 N, ENNReal.ofReal (Real.exp (t * N)) := by
          apply setLIntegral_mono measurable_const
          intro x hx
          calc ENNReal.ofReal (Real.exp (t * x)) * m x
              ≤ ENNReal.ofReal (Real.exp (t * N)) * 1 := by
                gcongr
                · exact hx.2.le
                · exact prob_le_one
            _ = _ := mul_one _
      _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Ioo]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hJle : J ≤ ENNReal.ofReal α + ENNReal.ofReal (α * t) * J := by
    have hsplit : ∀ x ∈ Set.Ioo (0:ℝ) N, ENNReal.ofReal (Real.exp (t * x)) * m x
        = m x + m x * ENNReal.ofReal (Real.exp (t * x) - 1) := by
      intro x hx
      have h1 : Real.exp (t * x) = 1 + (Real.exp (t * x) - 1) := by ring
      have h2 : 0 ≤ Real.exp (t * x) - 1 := by
        have : 1 ≤ Real.exp (t * x) := Real.one_le_exp (mul_nonneg ht.le hx.1.le)
        linarith
      rw [h1, ENNReal.ofReal_add zero_le_one h2, ENNReal.ofReal_one, add_mul, one_mul, mul_comm]
      congr 2
      ring
    calc J = ∫⁻ x in Set.Ioo 0 N, (m x + m x * ENNReal.ofReal (Real.exp (t * x) - 1)) :=
          setLIntegral_congr_fun measurableSet_Ioo hsplit
      _ = (∫⁻ x in Set.Ioo 0 N, m x)
            + ∫⁻ x in Set.Ioo 0 N, m x * ENNReal.ofReal (Real.exp (t * x) - 1) :=
          lintegral_add_left hmm _
      _ ≤ ENNReal.ofReal α + ENNReal.ofReal (α * t) * J := by
          gcongr
          · calc ∫⁻ x in Set.Ioo 0 N, m x ≤ ∫⁻ x in Set.Ioi 0, m x :=
                  lintegral_mono_set Set.Ioo_subset_Ioi_self
              _ ≤ ENNReal.ofReal α := tail_int_zero_le g α h184
          · exact swap_bound g α hα h184 t ht N
  -- solve in the reals
  have hR : J.toReal ≤ α + α * t * J.toReal := by
    have hfin2 : ENNReal.ofReal α + ENNReal.ofReal (α * t) * J ≠ ⊤ := by
      apply ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ?_⟩
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJfin.ne
    have := ENNReal.toReal_mono hfin2 hJle
    rwa [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJfin.ne),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le,
      ENNReal.toReal_ofReal (by positivity)] at this
  have hR2 : J.toReal ≤ α / (1 - α * t) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  calc J = ENNReal.ofReal J.toReal := (ENNReal.ofReal_toReal hJfin.ne).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hR2

/-- (C) untruncated bound. -/
lemma full_bound [IsProbabilityMeasure P] (g : Ω → ℝ≥0∞) (α : ℝ) (hα : 0 < α)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω}
        ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω})
    (t : ℝ) (ht : 0 < t) (htα : t < α⁻¹) :
    ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (Real.exp (t * x)) * P {ω | ENNReal.ofReal x < g ω}
      ≤ ENNReal.ofReal (α / (1 - α * t)) := by
  set h : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (t * x)) * P {ω | ENNReal.ofReal x < g ω}
    with hh
  have hhm : Measurable h := by
    apply Measurable.mul (by fun_prop) (tailm_measurable P g)
  have hpt : ∀ x, (Set.Ioi 0).indicator h x = ⨆ n : ℕ, (Set.Ioo 0 (n:ℝ)).indicator h x := by
    intro x
    apply le_antisymm
    · by_cases hx : x ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem hx]
        refine le_iSup_of_le (⌈x⌉₊ + 1) ?_
        rw [Set.indicator_of_mem]
        refine ⟨hx, ?_⟩
        push_cast
        linarith [Nat.le_ceil x]
      · rw [Set.indicator_of_notMem hx]; exact zero_le
    · apply iSup_le
      intro n
      exact Set.indicator_le_indicator_of_subset Set.Ioo_subset_Ioi_self (fun _ => by simp) x
  have hpt' : (Set.Ioi 0).indicator h = fun x => ⨆ n : ℕ, (Set.Ioo 0 (n:ℝ)).indicator h x :=
    funext hpt
  rw [← lintegral_indicator measurableSet_Ioi, hpt']
  rw [lintegral_iSup (fun n => hhm.indicator measurableSet_Ioo)]
  · apply iSup_le
    intro n
    rw [lintegral_indicator measurableSet_Ioo]
    exact trunc_bound g α hα h184 t ht htα n
  · intro a b hab x
    exact Set.indicator_le_indicator_of_subset
      (Set.Ioo_subset_Ioo_right (by exact_mod_cast hab)) (fun _ => by simp) x

/-- (A) layer cake for the exponential moment. -/
lemma exp_moment_eq [IsProbabilityMeasure P] (g : Ω → ℝ≥0∞) (hg : Measurable g)
    (hfin : ∀ᵐ ω ∂P, g ω ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (g ω).toReal)) ∂P
      = 1 + ∫⁻ x in Set.Ioi 0,
          P {ω | ENNReal.ofReal x < g ω} * ENNReal.ofReal (t * Real.exp (t * x)) := by
  have h1 : ∀ ω, ENNReal.ofReal (Real.exp (t * (g ω).toReal))
      = 1 + ENNReal.ofReal (∫ s in (0:ℝ)..(g ω).toReal, t * Real.exp (t * s)) := by
    intro ω
    rw [integral_t_exp]
    have h2 : 0 ≤ Real.exp (t * (g ω).toReal) - 1 := by
      have : 1 ≤ Real.exp (t * (g ω).toReal) := Real.one_le_exp (by positivity)
      linarith
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one h2]
    congr 1; ring
  simp_rw [h1]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  congr 1
  rw [lintegral_comp_eq_lintegral_meas_lt_mul P (f := fun ω => (g ω).toReal)
    (g := fun s => t * Real.exp (t * s)) (ae_of_all _ (fun ω => ENNReal.toReal_nonneg))
    hg.ennreal_toReal.aemeasurable
    (fun r _ => (by fun_prop : Continuous fun s => t * Real.exp (t * s)).intervalIntegrable _ _)
    (ae_of_all _ (fun s => by positivity))]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  beta_reduce
  congr 1
  apply measure_congr
  filter_upwards [hfin] with ω hω
  show (s < (g ω).toReal) = (ENNReal.ofReal s < g ω)
  rw [eq_iff_iff]
  exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hs) hω).symm

theorem lemma_18_1_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → ℝ≥0∞) (hg : Measurable g) (α : ℝ) (hα : 0 < α)
    (h184 : ∀ a : ℝ, 0 < a →
      ∫⁻ x in Set.Ioi a, P {ω | ENNReal.ofReal x < g ω}
        ≤ ENNReal.ofReal α * P {ω | ENNReal.ofReal a < g ω}) :
    (∀ᵐ ω ∂P, g ω ≠ ⊤) ∧
    ∀ t : ℝ, 0 < t → t < α⁻¹ →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (g ω).toReal)) ∂P
        ≤ ENNReal.ofReal (1 / (1 - α * t)) := by
  have hfin := ae_ne_top_of_tail g α h184
  refine ⟨hfin, ?_⟩
  intro t ht htα
  have hαt : α * t < 1 := by
    have := mul_lt_mul_of_pos_right htα hα
    rwa [inv_mul_cancel₀ hα.ne', mul_comm] at this
  rw [exp_moment_eq g hg hfin t ht]
  have hre : ∫⁻ x in Set.Ioi 0, P {ω | ENNReal.ofReal x < g ω} * ENNReal.ofReal (t * Real.exp (t * x))
      = ENNReal.ofReal t *
        ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (Real.exp (t * x)) * P {ω | ENNReal.ofReal x < g ω} := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul ht.le]
    ring
  rw [hre]
  calc 1 + ENNReal.ofReal t *
        ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (Real.exp (t * x)) * P {ω | ENNReal.ofReal x < g ω}
      ≤ 1 + ENNReal.ofReal t * ENNReal.ofReal (α / (1 - α * t)) := by
        gcongr
        exact full_bound g α hα h184 t ht htα
    _ = ENNReal.ofReal (1 + t * (α / (1 - α * t))) := by
        rw [ENNReal.ofReal_add zero_le_one (by
            have : 0 < 1 - α * t := by linarith
            positivity), ENNReal.ofReal_one, ENNReal.ofReal_mul ht.le]
    _ = ENNReal.ofReal (1 / (1 - α * t)) := by
        congr 1
        have : 1 - α * t ≠ 0 := by linarith
        rw [eq_div_iff this, add_mul, mul_assoc, div_mul_cancel₀ _ this]
        ring

end L181

/-! ### The tail condition (18.4) with `α = 3λ²` and Theorem 18.1 -/

section T181

theorem tail_integral_bound_core {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)
    (l : ℝ) (hl : 0 < l) :
    ∀ a : ℝ, 0 < a →
      ∫⁻ s in Set.Ioi a, P {ω | ENNReal.ofReal s < sqFnAt f (exitTime f l ω - 1) ω ^ 2}
        ≤ ENNReal.ofReal (3 * l ^ 2) * P {ω | ENNReal.ofReal a < sqFnAt f (exitTime f l ω - 1) ω ^ 2} := by
  intro a ha
  have hl2 : 0 < l ^ 2 := by positivity
  have hsplit : Set.Ioi a = Set.Ioc a (a + l ^ 2) ∪ Set.Ioi (a + l ^ 2) :=
    (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  rw [hsplit]
  calc ∫⁻ s in Set.Ioc a (a + l ^ 2) ∪ Set.Ioi (a + l ^ 2),
          P {ω | ENNReal.ofReal s < sqFnAt f (exitTime f l ω - 1) ω ^ 2}
      ≤ (∫⁻ s in Set.Ioc a (a + l ^ 2), P {ω | ENNReal.ofReal s < sqFnAt f (exitTime f l ω - 1) ω ^ 2})
          + ∫⁻ s in Set.Ioi (a + l ^ 2), P {ω | ENNReal.ofReal s < sqFnAt f (exitTime f l ω - 1) ω ^ 2} :=
        lintegral_union_le _ _ _
    _ ≤ (∫⁻ _ in Set.Ioc a (a + l ^ 2), P {ω | ENNReal.ofReal a < sqFnAt f (exitTime f l ω - 1) ω ^ 2})
          + ENNReal.ofReal (2 * l ^ 2) * P {ω | ENNReal.ofReal a < sqFnAt f (exitTime f l ω - 1) ω ^ 2} := by
        refine add_le_add ?_ (eq_18_5_core hf hnn l hl a ha)
        apply setLIntegral_mono measurable_const
        intro s hs
        apply measure_mono
        intro ω hω
        exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs.1.le) hω
    _ = ENNReal.ofReal (l ^ 2) * P {ω | ENNReal.ofReal a < sqFnAt f (exitTime f l ω - 1) ω ^ 2}
          + ENNReal.ofReal (2 * l ^ 2) * P {ω | ENNReal.ofReal a < sqFnAt f (exitTime f l ω - 1) ω ^ 2} := by
        rw [setLIntegral_const, Real.volume_Ioc, add_sub_cancel_left, mul_comm]
    _ = ENNReal.ofReal (3 * l ^ 2) * P {ω | ENNReal.ofReal a < sqFnAt f (exitTime f l ω - 1) ω ^ 2} := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring

lemma measurable_comp_enat' {F : ℕ∞ → Ω → ℝ≥0∞} (hF : ∀ k, Measurable (F k)) {t : Ω → ℕ∞}
    (ht : Measurable t) : Measurable fun ω => F (t ω) ω := by
  have h : Measurable fun p : Ω × ℕ∞ => F p.2 p.1 :=
    measurable_from_prod_countable_left (fun k => hF k)
  exact h.comp (measurable_id.prodMk ht)

lemma measurable_sqFnN' (hadp : StronglyAdapted ℱ f) (n : ℕ) : Measurable (sqFnN f n) := by
  unfold sqFnN
  exact (Finset.measurable_sum _ (fun k _ =>
    (measurable_dseq hadp k).pow_const 2)).sqrt.ennreal_ofReal

lemma measurable_sqFnAt (hadp : StronglyAdapted ℱ f) (m : ℕ∞) : Measurable (sqFnAt f m) := by
  induction m using ENat.recTopCoe with
  | top =>
    have : sqFnAt f ⊤ = sqFn f := by funext ω; exact sqFnAt_top f ω
    rw [this]
    exact Measurable.iSup (fun n => measurable_sqFnN' hadp n)
  | coe k =>
    have : sqFnAt f (k : ℕ∞) = sqFnN f k := by funext ω; exact sqFnAt_coe f k ω
    rw [this]
    exact measurable_sqFnN' hadp k

lemma measurable_sqFnAt_exit (hadp : StronglyAdapted ℱ f) (l : ℝ) :
    Measurable fun ω => sqFnAt f (exitTime f l ω - 1) ω :=
  measurable_comp_enat' (F := fun m ω => sqFnAt f m ω) (fun m => measurable_sqFnAt hadp m)
    ((measurable_from_top (f := fun x : ℕ∞ => x - 1)).comp (measurable_exitTime hadp l))

/-- Theorem 18.1. -/
theorem theorem_18_1_core {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n) (l : ℝ) (hl : 0 < l) :
    (∀ᵐ ω ∂P, sqFnAt f (exitTime f l ω - 1) ω ≠ ⊤) ∧
    ∀ t : ℝ, 0 < t → t < 1 / (3 * l ^ 2) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * ((sqFnAt f (exitTime f l ω - 1) ω).toReal) ^ 2)) ∂P
        ≤ ENNReal.ofReal (1 / (1 - 3 * t * l ^ 2)) := by
  have hadp := hf.submartingale.stronglyAdapted
  have hg : Measurable fun ω => sqFnAt f (exitTime f l ω - 1) ω ^ 2 :=
    (measurable_sqFnAt_exit hadp l).pow_const 2
  have hα : 0 < 3 * l ^ 2 := by positivity
  obtain ⟨h1, h2⟩ := lemma_18_1_core P (fun ω => sqFnAt f (exitTime f l ω - 1) ω ^ 2) hg
    (3 * l ^ 2) hα (tail_integral_bound_core hf hnn l hl)
  refine ⟨?_, ?_⟩
  · filter_upwards [h1] with ω hω
    intro h
    apply hω
    rw [h]
    exact ENNReal.top_pow (by norm_num)
  · intro t ht htl
    have h3 := h2 t ht (by rwa [one_div] at htl)
    have e1 : (fun ω => ENNReal.ofReal (Real.exp (t * ((sqFnAt f (exitTime f l ω - 1) ω).toReal) ^ 2)))
        = fun ω => ENNReal.ofReal (Real.exp (t * (sqFnAt f (exitTime f l ω - 1) ω ^ 2).toReal)) := by
      funext ω
      rw [ENNReal.toReal_pow]
    rw [e1]
    convert h3 using 3
    ring

end T181
end BurkholderDFI.NonnegExp

open BurkholderDFI.NonnegExp
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P) (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n) (l : ℝ) (hl : 0 < l) :
    (∀ᵐ ω ∂P, BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω ≠ ⊤) ∧
    ∀ t : ℝ, 0 < t → t < 1 / (3 * l ^ 2) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * ((BurkholderDFI.SquareFnLp.sqFnAt f (BurkholderDFI.SquareFnLp.exitTime f l ω - 1) ω).toReal) ^ 2)) ∂P
        ≤ ENNReal.ofReal (1 / (1 - 3 * t * l ^ 2)) := by
  exact theorem_18_1_core hf hnn l hl
