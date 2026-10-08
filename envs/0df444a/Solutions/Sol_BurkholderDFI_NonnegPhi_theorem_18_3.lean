-- Prove2me | solution 1 for BurkholderDFI.NonnegPhi.theorem_18_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:49:03.441695+00:00
-- url     : https://prove2.me/submissions/f056cdcd-5c2f-4922-8189-39ccf63e6530

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal


namespace BurkholderDFI.NonnegPhi
open BurkholderDFI.SquareFnLp

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}
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

lemma sqFnAt_tauN_sq (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) :
    sqFnAt f (tauN f l N ω - 1) ω ^ 2 = ENNReal.ofReal (SQ f l N ω) := by
  rw [tauN_sub_one, sqFnAt_coe, sqFnN, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rfl

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



/-! ### (18.5): the square function stopped before the exit time -/

/-- `S_n² = Σ_{k ≤ n} d_k²` as a real-valued process. -/
noncomputable def sqp (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.Icc 1 n, dseq f k ω ^ 2

lemma sqp_nonneg (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ sqp f n ω :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sqp_mono (f : ℕ → Ω → ℝ) (ω : Ω) : Monotone fun n => sqp f n ω := by
  intro n m h
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right h)
    (fun _ _ _ => sq_nonneg _)

lemma sqp_zero (f : ℕ → Ω → ℝ) (ω : Ω) : sqp f 0 ω = 0 := by simp [sqp]

lemma sqp_succ (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    sqp f (n + 1) ω = sqp f n ω + dseq f (n + 1) ω ^ 2 := by
  simp only [sqp]; rw [Finset.sum_Icc_succ_top (by omega)]

lemma gZ_sqp (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : gZ (sqp f) n ω = sqp f n ω := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gZ, sqp]
  · rw [gZ_pos _ hn]

lemma sqFnN_sq_eq (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    sqFnN f n ω ^ 2 = ENNReal.ofReal (sqp f n ω) := by
  rw [sqFnN, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rfl

lemma SQ_eq_sqp (f : ℕ → Ω → ℝ) (l : ℝ) (N : ℕ) (ω : Ω) :
    SQ f l N ω = sqp f (tN f l N ω - 1) ω := rfl

lemma Icc_one_eq_Ioc (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n := by
  ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

lemma stronglyMeasurable_dseq (hadp : StronglyAdapted ℱ f) {k : ℕ} (hk : 1 ≤ k) :
    StronglyMeasurable[ℱ k] (dseq f k) := by
  have e : dseq f k = fun ω => gZ f k ω - gZ f (k - 1) ω := funext (dseq_eq_gZ f hk)
  rw [e]
  refine StronglyMeasurable.sub ?_ ?_
  · rw [gZ_pos f hk]; exact hadp k
  · rcases Nat.eq_zero_or_pos (k - 1) with h0 | hpos
    · rw [h0, gZ_zero]; exact stronglyMeasurable_const
    · rw [gZ_pos f hpos]; exact (hadp (k - 1)).mono (ℱ.mono (Nat.sub_le k 1))

lemma stronglyAdapted_sqp (hadp : StronglyAdapted ℱ f) : StronglyAdapted ℱ (sqp f) := by
  intro n
  have : sqp f n = fun ω => ∑ k ∈ Finset.Icc 1 n, dseq f k ω ^ 2 := rfl
  rw [this]
  refine Measurable.stronglyMeasurable (Finset.measurable_sum (Finset.Icc 1 n) fun k hk => ?_)
  have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  exact ((stronglyMeasurable_dseq hadp hk1).mono (ℱ.mono hkn)).measurable.pow_const 2

/-! The hitting time `ν = inf {n : S_n² > a}` is `exitTime (sqp f) a`. -/

lemma nu_le_iff (f : ℕ → Ω → ℝ) {a : ℝ} (ha : 0 < a) (ω : Ω) (n : ℕ) :
    exitTime (sqp f) a ω ≤ n ↔ a < sqp f n ω := by
  rw [exitTime_le_iff]
  constructor
  · rintro ⟨k, _, hkn, hk⟩
    rw [abs_of_nonneg (sqp_nonneg f k ω)] at hk
    exact hk.trans_le (sqp_mono f ω hkn)
  · intro h
    refine ⟨n, ?_, le_rfl, ?_⟩
    · by_contra h0
      have : n = 0 := by omega
      subst this
      rw [sqp_zero] at h; linarith
    · rwa [abs_of_nonneg (sqp_nonneg f n ω)]

lemma sqp_le_of_lt_nu (f : ℕ → Ω → ℝ) {a : ℝ} (ha : 0 < a) (ω : Ω) {k : ℕ}
    (hk : (k : ℕ∞) < exitTime (sqp f) a ω) : sqp f k ω ≤ a := by
  have := abs_gZ_le_of_lt_exitTime (sqp f) ha ω hk
  rwa [gZ_sqp, abs_of_nonneg (sqp_nonneg _ _ _)] at this

lemma enat_lt_succ_iff (x : ℕ∞) (j : ℕ) : x < ((j + 1 : ℕ) : ℕ∞) ↔ x ≤ j := by
  induction x using ENat.recTopCoe with
  | top => simp
  | coe k => norm_cast; omega

lemma enat_le_sub_one_of_lt {x : ℕ∞} {j : ℕ} (h : (j : ℕ∞) < x) : (j : ℕ∞) ≤ x - 1 := by
  induction x using ENat.recTopCoe with
  | top => rw [top_sub_one]; exact le_top
  | coe m =>
    rw [coe_sub_one]
    norm_cast at h ⊢
    omega

lemma gZ_nonneg (f : ℕ → Ω → ℝ) (ω : Ω) (hnn : ∀ n, 1 ≤ n → 0 ≤ f n ω) (k : ℕ) :
    0 ≤ gZ f k ω := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [gZ]
  · rw [gZ_pos f hk]; exact hnn k hk

/-- `Σ_{ν < k ≤ τ_N − 1} d_k²`. -/
noncomputable def Qn (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (tN f l N ω - 1),
    if exitTime (sqp f) a ω < (k : ℕ∞) then dseq f k ω ^ 2 else 0

lemma Qn_nonneg (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) : 0 ≤ Qn f l a N ω :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

lemma tN_mono (f : ℕ → Ω → ℝ) (l : ℝ) (ω : Ω) {N M : ℕ} (h : N ≤ M) :
    tN f l N ω ≤ tN f l M ω := by
  have : tauN f l N ω ≤ tauN f l M ω := tauN_mono f l ω h
  rw [← coe_tN, ← coe_tN] at this
  exact_mod_cast this

lemma Qn_mono (f : ℕ → Ω → ℝ) (l a : ℝ) (ω : Ω) {N M : ℕ} (h : N ≤ M) :
    Qn f l a N ω ≤ Qn f l a M ω := by
  unfold Qn
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.sub_le_sub_right (tN_mono f l ω h) 1))
    (fun _ _ _ => by split_ifs <;> positivity)

lemma measurable_comp_pair {F : ℕ → ℕ∞ → Ω → ℝ} (hF : ∀ k x, Measurable (F k x))
    {t : Ω → ℕ} (ht : Measurable t) {ν : Ω → ℕ∞} (hν : Measurable ν) :
    Measurable fun ω => F (t ω) (ν ω) ω := by
  have h : Measurable fun p : Ω × (ℕ × ℕ∞) => F p.2.1 p.2.2 p.1 :=
    measurable_from_prod_countable_left (fun q => hF q.1 q.2)
  exact h.comp (measurable_id.prodMk (ht.prodMk hν))

lemma measurable_Qn (hadp : StronglyAdapted ℱ f) (l a : ℝ) (N : ℕ) :
    Measurable (Qn f l a N) := by
  refine measurable_comp_pair (F := fun t x ω => ∑ k ∈ Finset.Icc 1 (t - 1),
    if x < (k : ℕ∞) then dseq f k ω ^ 2 else 0) (fun t x => ?_) (measurable_tN hadp l N)
    (measurable_exitTime (stronglyAdapted_sqp hadp) a)
  refine Finset.measurable_sum _ fun k _ => ?_
  split_ifs
  · exact (measurable_dseq hadp k).pow_const 2
  · exact measurable_const

lemma sum_ite_lt_eq (g : ℕ → ℝ) (j m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, (if (j : ℕ∞) < (k : ℕ∞) then g k else 0) = ∑ k ∈ Finset.Ioc j m, g k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, Nat.cast_lt]
  omega

/-- The event `{ν < τ_N}`. -/
def Bset (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) : Set Ω :=
  {ω | exitTime (sqp f) a ω < tauN f l N ω}

lemma Bset_eq_compl (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) :
    Bset f l a N = {ω | tauN f l N ω ≤ exitTime (sqp f) a ω}ᶜ := by
  ext ω; simp [Bset, not_le]

lemma mem_Bset_iff (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) :
    ω ∈ Bset f l a N ↔ exitTime (sqp f) a ω < (tN f l N ω : ℕ∞) := by
  rw [coe_tN]; rfl

lemma measurableSet_Bset (hadp : StronglyAdapted ℱ f) (l a : ℝ) (N : ℕ) :
    MeasurableSet (Bset f l a N) := by
  have hτ := isStoppingTime_tauN hadp l N
  have hν := isStoppingTime_exitTime (stronglyAdapted_sqp hadp) a
  rw [Bset_eq_compl]
  exact hν.measurableSpace_le _ (IsStoppingTime.measurableSet_stopping_time_le hτ hν).compl

/-- On `{ν < τ_N}`, `ν` is a natural number `j` with `1 ≤ j < τ_N ≤ μ`. -/
lemma Bset_nat (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) {ω : Ω} (hω : ω ∈ Bset f l a N) :
    ∃ j : ℕ, exitTime (sqp f) a ω = j ∧ 1 ≤ j ∧ j < tN f l N ω ∧ (j : ℕ∞) < exitTime f l ω := by
  rw [mem_Bset_iff] at hω
  have hne : exitTime (sqp f) a ω ≠ ⊤ := (hω.trans_le le_top).ne
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hne
  refine ⟨j, hj.symm, ?_, ?_, ?_⟩
  · have := one_le_exitTime (sqp f) a ω
    rw [← hj] at this; exact_mod_cast this
  · rw [← hj] at hω; exact_mod_cast hω
  · rw [hj]; exact hω.trans_le (coe_tN_le_exit f l N ω)

/-- `g_ν` (read as `0` when `ν = ∞`). -/
noncomputable def gnu (f : ℕ → Ω → ℝ) (a : ℝ) (ω : Ω) : ℝ := gZ f (exitTime (sqp f) a ω).toNat ω

lemma measurable_gnu (hadp : StronglyAdapted ℱ f) (a : ℝ) : Measurable (gnu f a) :=
  measurable_comp_enat (F := fun x ω => gZ f x.toNat ω) (fun x => measurable_gZ hadp _)
    (measurable_exitTime (stronglyAdapted_sqp hadp) a)

lemma abs_gnu_le (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) (a : ℝ) (N : ℕ) {ω : Ω}
    (hω : ω ∈ Bset f l a N) : |gnu f a ω| ≤ l := by
  obtain ⟨j, hj, _, _, hjμ⟩ := Bset_nat f l a N hω
  unfold gnu
  rw [hj]
  simpa using abs_gZ_le_of_lt_exitTime f hl ω hjμ

/-- The boundary term `R_N`. -/
noncomputable def Rn (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (Bset f l a N).indicator (fun ω => 2 * G0 f l N ω * G1 f l N ω - G1 f l N ω ^ 2) ω
    + (Bset f l a N).indicator (fun ω => -(gnu f a ω ^ 2)) ω

/-- The predictable terms `1_{ν < k ≤ μ} f_{k-1} d_k`. -/
noncomputable def term2 (f : ℕ → Ω → ℝ) (l a : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if (k : ℕ∞) ≤ exitTime f l ω ∧ exitTime (sqp f) a ω < (k : ℕ∞) then gZ f (k - 1) ω * dseq f k ω
  else 0

lemma sum_term2_eq (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.Icc 1 (N + 1), term2 f l a k ω
      = ∑ k ∈ Finset.Icc 1 (tN f l N ω),
          (if exitTime (sqp f) a ω < (k : ℕ∞) then gZ f (k - 1) ω * dseq f k ω else 0) := by
  have hfilt : (Finset.Icc 1 (N + 1)).filter (fun k : ℕ => (k : ℕ∞) ≤ exitTime f l ω)
      = Finset.Icc 1 (tN f l N ω) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, (le_tN_iff f l N ω h2).mp h3⟩
    · rintro ⟨h1, h2⟩
      have h3 : k ≤ N + 1 := h2.trans (tN_le f l N ω)
      exact ⟨⟨h1, h3⟩, (le_tN_iff f l N ω h3).mpr h2⟩
  rw [← hfilt, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [term2, ite_and]

/-- The key pointwise identity `Q_N + 2 Σ_k term2_k = R_N`. -/
lemma Qn_identity (f : ℕ → Ω → ℝ) (l a : ℝ) (N : ℕ) (ω : Ω) :
    Qn f l a N ω + 2 * ∑ k ∈ Finset.Icc 1 (N + 1), term2 f l a k ω = Rn f l a N ω := by
  rw [sum_term2_eq]
  by_cases hB : ω ∈ Bset f l a N
  · obtain ⟨j, hj, hj1, hjt, _⟩ := Bset_nat f l a N hB
    set t := tN f l N ω with ht
    have ht1 : 1 ≤ t := one_le_tN f l N ω
    simp only [Rn, Set.indicator_of_mem hB, gnu, hj, ENat.toNat_natCast, Qn, ← ht]
    rw [sum_ite_lt_eq (fun k => dseq f k ω ^ 2), sum_ite_lt_eq (fun k => gZ f (k - 1) ω * dseq f k ω)]
    have hgt := gZ_sq_identity f ω t
    have hgj := gZ_sq_identity f ω j
    simp only [Icc_one_eq_Ioc] at hgt hgj
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le j) hjt.le,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le j) hjt.le] at hgt
    have hsplit : ∑ k ∈ Finset.Ioc j t, dseq f k ω ^ 2
        = ∑ k ∈ Finset.Ioc j (t - 1), dseq f k ω ^ 2 + dseq f t ω ^ 2 := by
      conv_lhs => rw [show t = (t - 1) + 1 by omega]
      rw [Finset.sum_Ioc_succ_top (by omega), Nat.sub_add_cancel ht1]
    have hd : dseq f t ω = gZ f t ω - gZ f (t - 1) ω := dseq_eq_gZ f ht1 ω
    simp only [G0, G1, ← ht]
    rw [hsplit, hd] at hgt
    linear_combination -hgt + hgj
  · simp only [Rn, Set.indicator_of_notMem hB]
    rw [mem_Bset_iff, not_lt] at hB
    have h1 : Qn f l a N ω = 0 := by
      unfold Qn
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [if_neg]
      intro h
      have hk' : k ≤ tN f l N ω := by have := (Finset.mem_Icc.mp hk).2; omega
      exact absurd (h.trans_le (by exact_mod_cast hk')) (not_lt.mpr hB)
    have h2 : ∑ k ∈ Finset.Icc 1 (tN f l N ω),
        (if exitTime (sqp f) a ω < (k : ℕ∞) then gZ f (k - 1) ω * dseq f k ω else 0) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [if_neg]
      intro h
      have hk' : k ≤ tN f l N ω := (Finset.mem_Icc.mp hk).2
      exact absurd (h.trans_le (by exact_mod_cast hk')) (not_lt.mpr hB)
    rw [h1, h2]; ring

lemma Rn_le (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) (a : ℝ) (N : ℕ) (ω : Ω)
    (hnn : ∀ n, 1 ≤ n → 0 ≤ f n ω) :
    Rn f l a N ω ≤ 2 * l * (Bset f l a N).indicator (G0 f l N) ω := by
  unfold Rn
  by_cases hB : ω ∈ Bset f l a N
  · simp only [Set.indicator_of_mem hB]
    have hG1 : G1 f l N ω ≤ l := (abs_le.mp (abs_G1_le f hl N ω)).2
    have hG0 : 0 ≤ G0 f l N ω := gZ_nonneg f ω hnn _
    nlinarith [mul_le_mul_of_nonneg_left hG1 hG0, sq_nonneg (G1 f l N ω), sq_nonneg (gnu f a ω)]
  · simp [Set.indicator_of_notMem hB]

lemma SQ_le_Qn (f : ℕ → Ω → ℝ) {l : ℝ} (hl : 0 < l) {a : ℝ} (ha : 0 < a) (N : ℕ) (ω : Ω)
    (hnn : ∀ n, 1 ≤ n → 0 ≤ f n ω) :
    SQ f l N ω ≤ a + l ^ 2 + Qn f l a N ω := by
  rw [SQ_eq_sqp]
  set m := tN f l N ω - 1 with hm
  have hmμ : (m : ℕ∞) < exitTime f l ω := tN_sub_one_lt_exit f l N ω
  by_cases h : exitTime (sqp f) a ω ≤ (m : ℕ∞)
  · have hne : exitTime (sqp f) a ω ≠ ⊤ := (h.trans_lt (WithTop.coe_lt_top m)).ne
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hne
    have hj1 : 1 ≤ j := by
      have := one_le_exitTime (sqp f) a ω
      rw [← hj] at this; exact_mod_cast this
    have hjm : j ≤ m := by rw [← hj] at h; exact_mod_cast h
    have hQ : Qn f l a N ω = ∑ k ∈ Finset.Ioc j m, dseq f k ω ^ 2 := by
      unfold Qn
      rw [← hm, ← hj, sum_ite_lt_eq (fun k => dseq f k ω ^ 2)]
    have hsplit : sqp f m ω = sqp f j ω + ∑ k ∈ Finset.Ioc j m, dseq f k ω ^ 2 := by
      simp only [sqp]
      rw [Icc_one_eq_Ioc, Icc_one_eq_Ioc, Finset.sum_Ioc_consecutive _ (Nat.zero_le j) hjm]
    have hjsucc : sqp f j ω = sqp f (j - 1) ω + dseq f j ω ^ 2 := by
      have := sqp_succ f (j - 1) ω
      rwa [Nat.sub_add_cancel hj1] at this
    have hprev : sqp f (j - 1) ω ≤ a := by
      refine sqp_le_of_lt_nu f ha ω ?_
      rw [← hj]; exact_mod_cast (Nat.sub_lt (by omega) one_pos)
    have hd : dseq f j ω = gZ f j ω - gZ f (j - 1) ω := dseq_eq_gZ f hj1 ω
    have hjμ : (j : ℕ∞) < exitTime f l ω := lt_of_le_of_lt (by exact_mod_cast hjm) hmμ
    have hj1μ : ((j - 1 : ℕ) : ℕ∞) < exitTime f l ω :=
      lt_of_le_of_lt (by exact_mod_cast (Nat.sub_le j 1)) hjμ
    have hx : |gZ f j ω| ≤ l := abs_gZ_le_of_lt_exitTime f hl ω hjμ
    have hy : |gZ f (j - 1) ω| ≤ l := abs_gZ_le_of_lt_exitTime f hl ω hj1μ
    have hx0 : 0 ≤ gZ f j ω := gZ_nonneg f ω hnn j
    have hy0 : 0 ≤ gZ f (j - 1) ω := gZ_nonneg f ω hnn (j - 1)
    have hx1 := (abs_le.mp hx).2
    have hy1 := (abs_le.mp hy).2
    have hdsq : dseq f j ω ^ 2 ≤ l ^ 2 := by
      rw [hd]
      nlinarith [mul_nonneg (by linarith : 0 ≤ l - gZ f j ω + gZ f (j - 1) ω)
        (by linarith : 0 ≤ l + gZ f j ω - gZ f (j - 1) ω)]
    rw [hsplit, hQ]
    linarith
  · push_neg at h
    have := sqp_le_of_lt_nu f ha ω h
    have := Qn_nonneg f l a N ω
    nlinarith [sq_nonneg l]

/-! ### The predictable terms have zero expectation -/

lemma term2_facts [IsProbabilityMeasure P] (hf : Martingale f ℱ P) {l : ℝ} (hl : 0 < l)
    (a : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (term2 f l a k) P ∧ ∫ ω, term2 f l a k ω ∂P = 0 := by
  have hadp := hf.stronglyAdapted
  have hμ := isStoppingTime_exitTime hadp l
  have hν := isStoppingTime_exitTime (stronglyAdapted_sqp hadp) a
  rcases Nat.exists_eq_add_of_le' hk with ⟨m, rfl⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : term2 f l a (0 + 1) = 0 := by
      funext ω
      simp only [term2]
      rw [if_neg]
      · rfl
      · rintro ⟨_, h⟩
        exact absurd (one_le_exitTime (sqp f) a ω) (not_le.mpr (by simpa using h))
    rw [h0]
    exact ⟨integrable_zero _ _ _, by simp⟩
  set j := m with hj
  have hjk : j ≤ j + 1 := Nat.le_succ j
  set S : Set Ω := {ω | ((j + 1 : ℕ) : ℕ∞) ≤ exitTime f l ω ∧
    exitTime (sqp f) a ω < ((j + 1 : ℕ) : ℕ∞)} with hSdef
  have hS : MeasurableSet[ℱ j] S := by
    have : S = {ω | exitTime f l ω ≤ (j : ℕ∞)}ᶜ ∩ {ω | exitTime (sqp f) a ω ≤ (j : ℕ∞)} := by
      ext ω
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_le,
        enat_lt_succ_iff]
      rw [Nat.cast_succ, ENat.add_one_le_iff (ENat.coe_ne_top j)]
    rw [this]
    exact (hμ j).compl.inter (hν j)
  set h : Ω → ℝ := S.indicator (f j) with hhdef
  have hh : StronglyMeasurable[ℱ j] h := (hadp j).indicator hS
  have hh' : AEStronglyMeasurable h P := (hh.mono (ℱ.le j)).aestronglyMeasurable
  have hbound : ∀ ω, ‖h ω‖ ≤ l := by
    intro ω
    simp only [hhdef, Real.norm_eq_abs]
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have hlt : (j : ℕ∞) < exitTime f l ω := by
        have := hω.1
        simp only [Nat.cast_succ] at this
        exact (ENat.add_one_le_iff (ENat.coe_ne_top j)).mp this
      have := abs_gZ_le_of_lt_exitTime f hl ω hlt
      rwa [gZ_pos f hm] at this
    · rw [Set.indicator_of_notMem hω]; simp [hl.le]
  have hterm : term2 f l a (j + 1) = fun ω => h ω * f (j + 1) ω - h ω * f j ω := by
    funext ω
    simp only [term2, Nat.add_sub_cancel, hhdef]
    by_cases hω : ω ∈ S
    · have hω' : ((j + 1 : ℕ) : ℕ∞) ≤ exitTime f l ω ∧
          exitTime (sqp f) a ω < ((j + 1 : ℕ) : ℕ∞) := hω
      rw [if_pos hω', Set.indicator_of_mem hω, dseq_eq_gZ f (by omega)]
      simp only [Nat.add_sub_cancel, gZ_pos f hm, gZ_pos f (Nat.succ_pos j), Nat.succ_eq_add_one,
        add_comm 1 j]
      ring
    · have hω' : ¬ (((j + 1 : ℕ) : ℕ∞) ≤ exitTime f l ω ∧
          exitTime (sqp f) a ω < ((j + 1 : ℕ) : ℕ∞)) := hω
      rw [if_neg hω', Set.indicator_of_notMem hω]; ring
  have hint1 : Integrable (fun ω => h ω * f (j + 1) ω) P :=
    (hf.integrable (j + 1)).bdd_mul hh' (Eventually.of_forall hbound)
  have hint2 : Integrable (fun ω => h ω * f j ω) P :=
    (hf.integrable j).bdd_mul hh' (Eventually.of_forall hbound)
  have hint3 : Integrable (fun ω => h ω * (P[f (j + 1) | ℱ j]) ω) P :=
    integrable_condExp.bdd_mul hh' (Eventually.of_forall hbound)
  have hintT : Integrable (term2 f l a (j + 1)) P := by
    rw [hterm]; exact hint1.sub hint2
  have hce : P[fun ω => h ω * f (j + 1) ω | ℱ j] =ᵐ[P] fun ω => h ω * (P[f (j + 1) | ℱ j]) ω :=
    condExp_mul_of_stronglyMeasurable_left hh hint1 (hf.integrable (j + 1))
  have hI1 : ∫ ω, h ω * f (j + 1) ω ∂P = ∫ ω, h ω * (P[f (j + 1) | ℱ j]) ω ∂P := by
    rw [← integral_condExp (ℱ.le j)]
    exact integral_congr_ae hce
  have hI : ∫ ω, term2 f l a (j + 1) ω ∂P
      = ∫ ω, h ω * ((P[f (j + 1) | ℱ j]) ω - f j ω) ∂P := by
    rw [hterm, integral_sub hint1 hint2, hI1, ← integral_sub hint3 hint2]
    congr 1; funext ω; ring
  refine ⟨hintT, ?_⟩
  rw [hI]
  have h1 : P[f (j + 1) | ℱ j] =ᵐ[P] f j := hf.condExp_ae_eq hjk
  have : (fun ω => h ω * ((P[f (j + 1) | ℱ j]) ω - f j ω)) =ᵐ[P] fun _ => 0 := by
    filter_upwards [h1] with ω h1
    simp [h1]
  rw [integral_congr_ae this]; simp

/-! ### Optional sampling: `∫_{ν < τ_N} f_{τ_N} = ∫_{ν < τ_N} f_ν ≤ λ P(ν < τ_N)` -/

lemma setIntegral_G0_le [IsProbabilityMeasure P] (hf : Martingale f ℱ P) {l : ℝ} (hl : 0 < l)
    (a : ℝ) (N : ℕ) :
    ∫ ω in Bset f l a N, G0 f l N ω ∂P ≤ l * (P (Bset f l a N)).toReal := by
  have hadp := hf.stronglyAdapted
  have hτ := isStoppingTime_tauN hadp l N
  have hν := isStoppingTime_exitTime (stronglyAdapted_sqp hadp) a
  set σ : Ω → ℕ∞ := fun ω => min (tauN f l N ω) (exitTime (sqp f) a ω) with hσdef
  have hσ : IsStoppingTime ℱ σ := hτ.min hν
  have hσle : σ ≤ tauN f l N := fun ω => min_le_left _ _
  have hτle : ∀ ω, tauN f l N ω ≤ ((N + 1 : ℕ) : ℕ∞) := fun ω => min_le_right _ _
  have hBσ : MeasurableSet[hσ.measurableSpace] (Bset f l a N) := by
    rw [Bset_eq_compl]
    exact (IsStoppingTime.measurableSet_stopping_time_le_min hτ hν).compl
  have hBm : MeasurableSet (Bset f l a N) := hσ.measurableSpace_le _ hBσ
  have hint : Integrable (stoppedValue f (tauN f l N)) P :=
    hf.submartingale.integrable_stoppedValue hτ hτle
  have hintσ : Integrable (stoppedValue f σ) P :=
    hf.submartingale.integrable_stoppedValue hσ (fun ω => (hσle ω).trans (hτle ω))
  have hcond : stoppedValue f σ =ᵐ[P] P[stoppedValue f (tauN f l N) | hσ.measurableSpace] :=
    hf.stoppedValue_ae_eq_condExp_of_le hτ hσ hσle hτle
  calc ∫ ω in Bset f l a N, G0 f l N ω ∂P
      = ∫ ω in Bset f l a N, stoppedValue f (tauN f l N) ω ∂P := by rw [G0_eq_stoppedValue]
    _ = ∫ ω in Bset f l a N, (P[stoppedValue f (tauN f l N) | hσ.measurableSpace]) ω ∂P :=
        (setIntegral_condExp hσ.measurableSpace_le hint hBσ).symm
    _ = ∫ ω in Bset f l a N, stoppedValue f σ ω ∂P := by
        refine setIntegral_congr_ae hBm ?_
        filter_upwards [hcond] with ω h _
        exact h.symm
    _ ≤ ∫ _ in Bset f l a N, l ∂P := by
        refine setIntegral_mono_on hintσ.integrableOn (integrableOn_const (by simp)) hBm ?_
        intro ω hω
        obtain ⟨j, hj, hj1, hjt, hjμ⟩ := Bset_nat f l a N hω
        have hσω : σ ω = (j : ℕ∞) := by
          simp only [hσdef]
          rw [min_eq_right hω.le, hj]
        simp only [stoppedValue, hσω]
        have : ((j : ℕ∞)).untopA = j := rfl
        rw [this]
        have := abs_gZ_le_of_lt_exitTime f hl ω hjμ
        rw [gZ_pos f hj1] at this
        exact (abs_le.mp this).2
    _ = l * (P (Bset f l a N)).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
        rfl

/-! ### The finite-`N` estimate -/

lemma integral_Qn_le [IsProbabilityMeasure P] (hf : Martingale f ℱ P)
    (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n) {l : ℝ} (hl : 0 < l) (a : ℝ) (N : ℕ) :
    Integrable (Qn f l a N) P ∧
      ∫ ω, Qn f l a N ω ∂P ≤ 2 * l ^ 2 * (P (Bset f l a N)).toReal := by
  have hadp := hf.stronglyAdapted
  have hBm : MeasurableSet (Bset f l a N) := measurableSet_Bset hadp l a N
  have hnn' : ∀ᵐ ω ∂P, ∀ n, 1 ≤ n → 0 ≤ f n ω := by
    rw [ae_all_iff]
    intro n
    by_cases hn : 1 ≤ n
    · filter_upwards [hnn n hn] with ω h _
      exact h
    · exact Eventually.of_forall fun ω h => absurd h hn
  -- integrability of the pieces of `R_N`
  have hG1m : AEStronglyMeasurable (G1 f l N) P := (measurable_G1 hadp l N).aestronglyMeasurable
  have hG1b : ∀ᵐ ω ∂P, ‖G1 f l N ω‖ ≤ l :=
    Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_G1_le f hl N ω
  have hG0 : Integrable (G0 f l N) P := integrable_G0 hf.submartingale l N
  have hprod : Integrable (fun ω => 2 * G0 f l N ω * G1 f l N ω) P := by
    have := (hG0.bdd_mul hG1m hG1b).const_mul 2
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only; ring
  have hG1sq : Integrable (fun ω => G1 f l N ω ^ 2) P := by
    refine memLp_one_iff_integrable.mp (MemLp.of_bound (hG1m.pow 2) (l ^ 2) ?_)
    filter_upwards [hG1b] with ω hω
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by rwa [Real.norm_eq_abs] at hω) 2
  have hR1 : Integrable ((Bset f l a N).indicator
      (fun ω => 2 * G0 f l N ω * G1 f l N ω - G1 f l N ω ^ 2)) P :=
    (hprod.sub hG1sq).indicator hBm
  have hR2 : Integrable ((Bset f l a N).indicator (fun ω => -(gnu f a ω ^ 2))) P := by
    refine memLp_one_iff_integrable.mp (MemLp.of_bound ?_ (l ^ 2) ?_)
    · exact (((measurable_gnu hadp a).pow_const 2).neg.indicator hBm).aestronglyMeasurable
    · refine Eventually.of_forall fun ω => ?_
      by_cases hω : ω ∈ Bset f l a N
      · rw [Set.indicator_of_mem hω, norm_neg, Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_gnu_le f hl a N hω) 2
      · rw [Set.indicator_of_notMem hω]; simp [sq_nonneg]
  have hRint : Integrable (Rn f l a N) P := hR1.add hR2
  have hterm : ∀ k ∈ Finset.Icc 1 (N + 1), Integrable (term2 f l a k) P := fun k hk =>
    (term2_facts hf hl a (Finset.mem_Icc.mp hk).1).1
  have hsum : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 (N + 1), term2 f l a k ω) P :=
    integrable_finsetSum _ hterm
  have hQeq : Qn f l a N = fun ω => Rn f l a N ω
      - 2 * ∑ k ∈ Finset.Icc 1 (N + 1), term2 f l a k ω := by
    funext ω; have := Qn_identity f l a N ω; linarith
  have hQint : Integrable (Qn f l a N) P := by
    rw [hQeq]; exact hRint.sub (hsum.const_mul 2)
  refine ⟨hQint, ?_⟩
  have hsum0 : ∫ ω, ∑ k ∈ Finset.Icc 1 (N + 1), term2 f l a k ω ∂P = 0 := by
    rw [integral_finsetSum _ hterm]
    exact Finset.sum_eq_zero fun k hk => (term2_facts hf hl a (Finset.mem_Icc.mp hk).1).2
  have hind : Integrable ((Bset f l a N).indicator (G0 f l N)) P := hG0.indicator hBm
  have hQR : ∫ ω, Qn f l a N ω ∂P = ∫ ω, Rn f l a N ω ∂P := by
    rw [hQeq, integral_sub hRint (hsum.const_mul 2), integral_const_mul, hsum0]
    ring
  calc ∫ ω, Qn f l a N ω ∂P = ∫ ω, Rn f l a N ω ∂P := hQR
    _ ≤ ∫ ω, 2 * l * (Bset f l a N).indicator (G0 f l N) ω ∂P := by
        refine integral_mono_ae hRint (hind.const_mul _) ?_
        filter_upwards [hnn'] with ω hω
        exact Rn_le f hl a N ω hω
    _ = 2 * l * ∫ ω in Bset f l a N, G0 f l N ω ∂P := by
        rw [integral_const_mul, integral_indicator hBm]
    _ ≤ 2 * l * (l * (P (Bset f l a N)).toReal) := by
        gcongr
        exact setIntegral_G0_le hf hl a N
    _ = 2 * l ^ 2 * (P (Bset f l a N)).toReal := by ring

/-! ### Tonelli for the tail integral -/

lemma tail_tonelli (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℝ≥0∞) (hT : Measurable T)
    (c : ℝ) :
    ∫⁻ x in Set.Ioi c, P {ω | ENNReal.ofReal x < T ω}
      = ∫⁻ ω, volume ({x : ℝ | ENNReal.ofReal x < T ω} ∩ Set.Ioi c) ∂P := by
  set S : Set (ℝ × Ω) := {p | ENNReal.ofReal p.1 < T p.2} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_lt (measurable_fst.ennreal_ofReal) (hT.comp measurable_snd)
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Set.Ioi c)) (ν := P)
    (f := fun x ω => S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω))
    (measurable_const.indicator hS).aemeasurable
  have hl : ∀ x : ℝ, ∫⁻ ω, S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω) ∂P
      = P {ω | ENNReal.ofReal x < T ω} := by
    intro x
    have : (fun ω => S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω))
        = {ω | ENNReal.ofReal x < T ω}.indicator 1 := by
      ext ω
      simp [S, Set.indicator_apply]
    rw [this, lintegral_indicator_one (measurableSet_lt measurable_const hT)]
  have hr : ∀ ω : Ω, ∫⁻ x in Set.Ioi c, S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω)
      = volume ({x : ℝ | ENNReal.ofReal x < T ω} ∩ Set.Ioi c) := by
    intro ω
    have : (fun x => S.indicator (1 : ℝ × Ω → ℝ≥0∞) (x, ω))
        = {x : ℝ | ENNReal.ofReal x < T ω}.indicator 1 := by
      ext x
      simp [S, Set.indicator_apply]
    rw [this, lintegral_indicator_one (measurableSet_lt ENNReal.measurable_ofReal measurable_const),
      Measure.restrict_apply (measurableSet_lt ENNReal.measurable_ofReal measurable_const)]
  simp_rw [hl, hr] at hswap
  exact hswap

lemma volume_set_le (a : ℝ) (ha : 0 ≤ a) (c : ℝ≥0∞) :
    volume ({x : ℝ | ENNReal.ofReal x < ENNReal.ofReal a + c} ∩ Set.Ioi a) ≤ c := by
  by_cases hc : c = ⊤
  · rw [hc]; exact le_top
  · calc volume ({x : ℝ | ENNReal.ofReal x < ENNReal.ofReal a + c} ∩ Set.Ioi a)
        ≤ volume (Set.Ioo a (a + c.toReal)) := by
          apply measure_mono
          rintro x ⟨hx1, hx2⟩
          refine ⟨hx2, ?_⟩
          simp only [Set.mem_setOf_eq] at hx1
          have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt ha hx2)
          rw [← ENNReal.ofReal_toReal hc, ← ENNReal.ofReal_add ha ENNReal.toReal_nonneg,
            ENNReal.ofReal_lt_ofReal_iff_of_nonneg hx0] at hx1
          exact hx1
      _ = c := by rw [Real.volume_Ioo, add_sub_cancel_left, ENNReal.ofReal_toReal hc]

/-! ### (18.5) -/

theorem eq_18_5_core [IsProbabilityMeasure P] (hf : Martingale f ℱ P)
    (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n) (l : ℝ) (hl : 0 < l) (a : ℝ) (ha : 0 < a) :
    ∫⁻ s in Set.Ioi (a + l ^ 2), P {ω | ENNReal.ofReal s < sqFnAt f (exitTime f l ω - 1) ω ^ 2}
      ≤ ENNReal.ofReal (2 * l ^ 2)
        * P {ω | ENNReal.ofReal a < sqFnAt f (exitTime f l ω - 1) ω ^ 2} := by
  have hadp := hf.stronglyAdapted
  set T : Ω → ℝ≥0∞ := fun ω => sqFnAt f (exitTime f l ω - 1) ω ^ 2 with hTdef
  have hTsup : ∀ ω, T ω = ⨆ N, ENNReal.ofReal (SQ f l N ω) := by
    intro ω
    simp only [hTdef]
    rw [← iSup_sqFnAt_tauN f l ω]
    congr 1; funext N; exact sqFnAt_tauN_sq f l N ω
  have hTm : Measurable T := by
    have : T = fun ω => ⨆ N, ENNReal.ofReal (SQ f l N ω) := funext hTsup
    rw [this]
    exact Measurable.iSup fun N => ENNReal.measurable_ofReal.comp (measurable_SQ hadp l N)
  have hnn' : ∀ᵐ ω ∂P, ∀ n, 1 ≤ n → 0 ≤ f n ω := by
    rw [ae_all_iff]
    intro n
    by_cases hn : 1 ≤ n
    · filter_upwards [hnn n hn] with ω h _
      exact h
    · exact Eventually.of_forall fun ω h => absurd h hn
  have hc0 : 0 ≤ a + l ^ 2 := by positivity
  -- `B_N ⊆ {a < T}`
  have hBsub : ∀ N, Bset f l a N ⊆ {ω | ENNReal.ofReal a < T ω} := by
    intro N ω hω
    obtain ⟨j, hj, hj1, _, hjμ⟩ := Bset_nat f l a N hω
    have hνj : exitTime (sqp f) a ω ≤ j := hj.le
    rw [nu_le_iff f ha] at hνj
    simp only [Set.mem_setOf_eq, hTdef]
    calc ENNReal.ofReal a < ENNReal.ofReal (sqp f j ω) :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).mpr hνj
      _ = sqFnAt f (j : ℕ∞) ω ^ 2 := by rw [sqFnAt_coe, sqFnN_sq_eq]
      _ ≤ sqFnAt f (exitTime f l ω - 1) ω ^ 2 :=
          pow_le_pow_left₀ bot_le (sqFnAt_mono f ω (enat_le_sub_one_of_lt hjμ)) 2
  -- the pointwise bound on the volume
  have hvol : ∀ᵐ ω ∂P, volume ({x : ℝ | ENNReal.ofReal x < T ω} ∩ Set.Ioi (a + l ^ 2))
      ≤ ⨆ N, ENNReal.ofReal (Qn f l a N ω) := by
    filter_upwards [hnn'] with ω hω
    have hT : T ω ≤ ENNReal.ofReal (a + l ^ 2) + ⨆ N, ENNReal.ofReal (Qn f l a N ω) := by
      rw [hTsup, ENNReal.add_iSup]
      refine iSup_mono fun N => ?_
      rw [← ENNReal.ofReal_add hc0 (Qn_nonneg f l a N ω)]
      exact ENNReal.ofReal_le_ofReal (SQ_le_Qn f hl ha N ω hω)
    refine le_trans (measure_mono ?_) (volume_set_le (a + l ^ 2) hc0 _)
    rintro x ⟨hx1, hx2⟩
    exact ⟨lt_of_lt_of_le hx1 hT, hx2⟩
  have hQm : ∀ N, Measurable fun ω => ENNReal.ofReal (Qn f l a N ω) := fun N =>
    ENNReal.measurable_ofReal.comp (measurable_Qn hadp l a N)
  have hQmono : Monotone fun N ω => ENNReal.ofReal (Qn f l a N ω) := fun N M h ω =>
    ENNReal.ofReal_le_ofReal (Qn_mono f l a ω h)
  calc ∫⁻ s in Set.Ioi (a + l ^ 2), P {ω | ENNReal.ofReal s < T ω}
      = ∫⁻ ω, volume ({x : ℝ | ENNReal.ofReal x < T ω} ∩ Set.Ioi (a + l ^ 2)) ∂P :=
        tail_tonelli P T hTm _
    _ ≤ ∫⁻ ω, ⨆ N, ENNReal.ofReal (Qn f l a N ω) ∂P := lintegral_mono_ae hvol
    _ = ⨆ N, ∫⁻ ω, ENNReal.ofReal (Qn f l a N ω) ∂P := lintegral_iSup hQm hQmono
    _ ≤ ENNReal.ofReal (2 * l ^ 2) * P {ω | ENNReal.ofReal a < T ω} := by
        refine iSup_le fun N => ?_
        obtain ⟨hQint, hQle⟩ := integral_Qn_le hf hnn hl a N
        rw [← ofReal_integral_eq_lintegral_ofReal hQint
          (Eventually.of_forall (Qn_nonneg f l a N))]
        calc ENNReal.ofReal (∫ ω, Qn f l a N ω ∂P)
            ≤ ENNReal.ofReal (2 * l ^ 2 * (P (Bset f l a N)).toReal) :=
              ENNReal.ofReal_le_ofReal hQle
          _ = ENNReal.ofReal (2 * l ^ 2) * P (Bset f l a N) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal (measure_ne_top _ _)]
          _ ≤ ENNReal.ofReal (2 * l ^ 2) * P {ω | ENNReal.ofReal a < T ω} := by
              gcongr
              exact hBsub N

/-! ### stopped_inclusion -/

lemma si_abs_le_of_maxFn_le (f : ℕ → Ω → ℝ) (ω : Ω) {c : ℝ} (hc : 0 ≤ c)
    (h : maxFn f ω ≤ ENNReal.ofReal c) {n : ℕ} (hn : 1 ≤ n) : |f n ω| ≤ c := by
  have h1 : ENNReal.ofReal |f n ω| ≤ maxFnN f n ω := by
    unfold maxFnN
    exact le_iSup₂ (f := fun k (_ : k ∈ Finset.Icc 1 n) => ENNReal.ofReal |f k ω|) n
      (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
  have h2 : maxFnN f n ω ≤ maxFn f ω := le_iSup (fun n => maxFnN f n ω) n
  have := (h1.trans h2).trans h
  rwa [ENNReal.ofReal_le_ofReal_iff hc] at this

lemma si_exitTime_eq_top (f : ℕ → Ω → ℝ) (ω : Ω) {c : ℝ}
    (h : ∀ n, 1 ≤ n → |f n ω| ≤ c) : exitTime f c ω = ⊤ := by
  unfold exitTime
  rw [iInf_eq_top]
  intro n
  rw [iInf_eq_top]
  rintro ⟨hn, hlt⟩
  exact absurd (h n hn) (not_le.mpr hlt)

theorem stopped_inclusion_core (P : Measure Ω) (f : ℕ → Ω → ℝ)
    (β δ l : ℝ) (hδ : 0 < δ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < sqFn f ω ∧ maxFn f ω ≤ ENNReal.ofReal (δ * l)}
      ≤ P {ω | ENNReal.ofReal (β * l) < sqFnAt f (exitTime f (δ * l) ω - 1) ω} := by
  apply measure_mono
  intro ω ⟨h1, h2⟩
  simp only [Set.mem_setOf_eq]
  have htop : exitTime f (δ * l) ω = ⊤ :=
    si_exitTime_eq_top f ω (fun n hn => si_abs_le_of_maxFn_le f ω (by positivity) h2 hn)
  rw [htop, top_sub_one]
  simpa [sqFnAt] using h1

/-! ### Theorem 18.2 -/

lemma sqFnAt_le_sqFn (f : ℕ → Ω → ℝ) (ω : Ω) (x : ℕ∞) : sqFnAt f x ω ≤ sqFn f ω := by
  have : sqFnAt f x ω ≤ sqFnAt f ⊤ ω := sqFnAt_mono f ω le_top
  rwa [sqFnAt_top] at this

lemma set_lt_sq_eq (Y : Ω → ℝ≥0∞) {c : ℝ} (hc : 0 ≤ c) :
    {ω | ENNReal.ofReal c < Y ω} = {ω | ENNReal.ofReal (c ^ 2) < Y ω ^ 2} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [ENNReal.ofReal_pow hc, ENNReal.pow_lt_pow_left_iff (by norm_num)]

/-- The Chebyshev-type step: `(t − c) P(T > t) ≤ ∫_c^∞ P(T > s) ds` for `c < t`. -/
lemma markov_tail (P : Measure Ω) (T : Ω → ℝ≥0∞) {c t : ℝ} (hct : c < t) :
    ENNReal.ofReal (t - c) * P {ω | ENNReal.ofReal t < T ω}
      ≤ ∫⁻ s in Set.Ioi c, P {ω | ENNReal.ofReal s < T ω} := by
  calc ENNReal.ofReal (t - c) * P {ω | ENNReal.ofReal t < T ω}
      = ∫⁻ _ in Set.Ioo c t, P {ω | ENNReal.ofReal t < T ω} := by
        rw [setLIntegral_const, Real.volume_Ioo, mul_comm]
    _ ≤ ∫⁻ s in Set.Ioo c t, P {ω | ENNReal.ofReal s < T ω} := by
        refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_setOf_eq] at hω ⊢
        exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs.2.le) hω
    _ ≤ ∫⁻ s in Set.Ioi c, P {ω | ENNReal.ofReal s < T ω} :=
        lintegral_mono_set Set.Ioo_subset_Ioi_self

theorem theorem_18_2_core [IsProbabilityMeasure P] (hf : Martingale f ℱ P)
    (hnn : ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n)
    (β δ : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hδβ : δ < Real.sqrt (β ^ 2 - 1))
    (l : ℝ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < sqFn f ω ∧ maxFn f ω ≤ ENNReal.ofReal (δ * l)}
      ≤ ENNReal.ofReal (2 * δ ^ 2 / (β ^ 2 - δ ^ 2 - 1)) * P {ω | ENNReal.ofReal l < sqFn f ω} := by
  have hβ0 : 0 < β := by linarith
  have hδ2 : δ ^ 2 < β ^ 2 - 1 := by
    have h1 : 0 < β ^ 2 - 1 := by nlinarith
    have := Real.sq_sqrt h1.le
    nlinarith [Real.sqrt_nonneg (β ^ 2 - 1)]
  have hden : 0 < β ^ 2 - δ ^ 2 - 1 := by linarith
  set T : Ω → ℝ≥0∞ := fun ω => sqFnAt f (exitTime f (δ * l) ω - 1) ω ^ 2 with hTdef
  set K : ℝ := 2 * δ ^ 2 / (β ^ 2 - δ ^ 2 - 1) with hK
  have hK0 : 0 < K := by positivity
  set c : ℝ := l ^ 2 + (δ * l) ^ 2 with hc
  set t : ℝ := (β * l) ^ 2 with ht
  have hct : c < t := by
    simp only [hc, ht]
    nlinarith [sq_nonneg l, mul_pos hl hl]
  have h185 := eq_18_5_core hf hnn (δ * l) (by positivity) (l ^ 2) (by positivity)
  have hmark := markov_tail P T hct
  have hcomb : ENNReal.ofReal (t - c) * P {ω | ENNReal.ofReal t < T ω}
      ≤ ENNReal.ofReal (2 * (δ * l) ^ 2) * P {ω | ENNReal.ofReal (l ^ 2) < T ω} :=
    hmark.trans h185
  have htc : t - c = l ^ 2 * (β ^ 2 - δ ^ 2 - 1) := by simp only [hc, ht]; ring
  have htc0 : 0 < t - c := by linarith
  have hdiv : ENNReal.ofReal K = ENNReal.ofReal (2 * (δ * l) ^ 2) / ENNReal.ofReal (t - c) := by
    rw [← ENNReal.ofReal_div_of_pos htc0]
    congr 1
    rw [htc, hK, div_eq_div_iff hden.ne' (by positivity)]
    ring
  have hmain : P {ω | ENNReal.ofReal t < T ω}
      ≤ ENNReal.ofReal K * P {ω | ENNReal.ofReal (l ^ 2) < T ω} := by
    rw [hdiv, div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
      ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr htc0).ne')
        (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hcomb
  calc P {ω | ENNReal.ofReal (β * l) < sqFn f ω ∧ maxFn f ω ≤ ENNReal.ofReal (δ * l)}
      ≤ P {ω | ENNReal.ofReal (β * l) < sqFnAt f (exitTime f (δ * l) ω - 1) ω} :=
        stopped_inclusion_core P f β δ l hδ hl
    _ = P {ω | ENNReal.ofReal t < T ω} := by
        rw [set_lt_sq_eq _ (by positivity)]
    _ ≤ ENNReal.ofReal K * P {ω | ENNReal.ofReal (l ^ 2) < T ω} := hmain
    _ ≤ ENNReal.ofReal K * P {ω | ENNReal.ofReal l < sqFn f ω} := by
        refine mul_le_mul_right (measure_mono (μ := P) ?_) _
        rw [set_lt_sq_eq (fun ω => sqFn f ω) hl.le]
        intro ω hω
        simp only [Set.mem_setOf_eq, hTdef] at hω ⊢
        exact lt_of_lt_of_le hω (pow_le_pow_left₀ bot_le (sqFnAt_le_sqFn f ω _) 2)

open BurkholderDFI.SquareFnLp

/-! ### Finiteness of `Φ` on finite arguments -/

lemma isPhi_ne_top {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) {x : ℝ≥0∞}
    (hx : x ≠ ⊤) : Φ x ≠ ⊤ := by
  have h0 : Tendsto Φ (𝓝 0) (𝓝 0) := by
    have := hΦ.cont.tendsto 0
    rwa [hΦ.zero] at this
  rw [ENNReal.tendsto_nhds_zero] at h0
  have h1 := h0 1 one_pos
  rw [ENNReal.nhds_zero_basis.eventually_iff] at h1
  obtain ⟨δ, hδ, hδ'⟩ := h1
  obtain ⟨d, hd0, hdδ⟩ := exists_between hδ
  have hΦd : Φ d ≤ 1 := hδ' hdδ
  have hdtop : d ≠ ⊤ := (hdδ.trans_le le_top).ne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top hx hd0.ne').ne
  have hxle : x ≤ 2 ^ n * d := by
    calc x = x / d * d := (ENNReal.div_mul_cancel hd0.ne' hdtop).symm
      _ ≤ (n : ℝ≥0∞) * d := mul_le_mul_left hn.le _
      _ ≤ 2 ^ n * d := by
        gcongr
        exact_mod_cast n.lt_two_pow_self.le
  have key : ∀ k : ℕ, Φ (2 ^ k * d) ≤ (c : ℝ≥0∞) ^ k * Φ d := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc Φ (2 ^ (k + 1) * d) = Φ (2 * (2 ^ k * d)) := by ring_nf
        _ ≤ c * Φ (2 ^ k * d) := hΦ.growth _
        _ ≤ c * ((c : ℝ≥0∞) ^ k * Φ d) := mul_le_mul_right ih _
        _ = (c : ℝ≥0∞) ^ (k + 1) * Φ d := by ring
  refine ne_top_of_le_ne_top ?_ ((hΦ.mono hxle).trans (key n))
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    (ne_top_of_le_ne_top ENNReal.one_ne_top hΦd)

/-! ### Pointwise scaling inequalities extend from positive reals to `[0, ∞]` -/

lemma scale_le {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) {a : ℝ} (ha : 0 < a) {k : ℝ≥0}
    (h : ∀ l : ℝ, 0 < l → Φ (ENNReal.ofReal (a * l)) ≤ k * Φ (ENNReal.ofReal l)) (x : ℝ≥0∞) :
    Φ (ENNReal.ofReal a * x) ≤ k * Φ x := by
  rcases eq_or_ne x ⊤ with hx | hx
  · subst hx
    rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 ha).ne']
    have h1 : Tendsto (fun n : ℕ => Φ (ENNReal.ofReal a * n)) atTop (𝓝 (Φ ⊤)) := by
      have : Tendsto (fun n : ℕ => ENNReal.ofReal a * (n : ℝ≥0∞)) atTop (𝓝 (ENNReal.ofReal a * ⊤)) :=
        ENNReal.Tendsto.const_mul ENNReal.tendsto_nat_nhds_top (Or.inl ENNReal.top_ne_zero)
      rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 ha).ne'] at this
      exact (hΦ.cont.tendsto _).comp this
    have h2 : Tendsto (fun n : ℕ => (k : ℝ≥0∞) * Φ n) atTop (𝓝 (k * Φ ⊤)) :=
      ENNReal.Tendsto.const_mul ((hΦ.cont.tendsto _).comp ENNReal.tendsto_nat_nhds_top)
        (Or.inr ENNReal.coe_ne_top)
    refine le_of_tendsto_of_tendsto' h1 h2 fun n => ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hΦ.zero]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have := h n hn'
      rwa [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_natCast] at this
  rcases eq_or_ne x 0 with hx0 | hx0
  · subst hx0; simp [hΦ.zero]
  have hxr : x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx).symm
  have hpos : 0 < x.toReal := ENNReal.toReal_pos hx0 hx
  rw [hxr, ← ENNReal.ofReal_mul ha.le]
  exact h _ hpos

/-! ### Layer-cake formula for `[0, ∞]`-valued functions -/

lemma layer_cake {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ ω, F ω ∂P = ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | ENNReal.ofReal t < F ω} := by
  by_cases hae : ∀ᵐ ω ∂P, F ω ≠ ⊤
  · have h1 : ∫⁻ ω, F ω ∂P = ∫⁻ ω, ENNReal.ofReal (F ω).toReal ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with ω hω
      rw [ENNReal.ofReal_toReal hω]
    rw [h1, lintegral_eq_lintegral_meas_lt P (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      hF.ennreal_toReal.aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    refine measure_congr ?_
    filter_upwards [hae] with ω hω
    change (t < (F ω).toReal) = (ENNReal.ofReal t < F ω)
    rw [eq_iff_iff, ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) hω]
  · have hS : MeasurableSet {ω | F ω = ⊤} := hF (measurableSet_singleton ⊤)
    have hpos : P {ω | F ω = ⊤} ≠ 0 := by
      intro h0
      apply hae
      rw [ae_iff]
      simpa using h0
    have hL : ∫⁻ ω, F ω ∂P = ⊤ := by
      refine eq_top_iff.2 ?_
      calc (⊤ : ℝ≥0∞) = ∫⁻ ω, {ω | F ω = ⊤}.indicator (fun _ => (⊤ : ℝ≥0∞)) ω ∂P := by
            rw [lintegral_indicator_const hS, ENNReal.top_mul hpos]
        _ ≤ ∫⁻ ω, F ω ∂P := by
            refine lintegral_mono fun ω => ?_
            by_cases hω : F ω = ⊤
            · simp [hω]
            · simp [Set.indicator, hω]
    have hR : ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | ENNReal.ofReal t < F ω} = ⊤ := by
      refine eq_top_iff.2 ?_
      calc (⊤ : ℝ≥0∞) = ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | F ω = ⊤} := by
            rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top hpos]
        _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), P {ω | ENNReal.ofReal t < F ω} := by
            refine lintegral_mono fun t => ?_
            refine measure_mono fun ω hω => ?_
            simp only [Set.mem_ofPred_eq] at hω ⊢
            rw [hω]; exact ENNReal.ofReal_lt_top
    rw [hL, hR]

/-! ### The generalized inverse of `Φ` -/

lemma phi_lt_iff {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) (s : ℝ≥0∞) (x : ℝ≥0∞) :
    s < Φ x ↔ sSup {y | Φ y ≤ s} < x := by
  set S := {y | Φ y ≤ s} with hS
  have hSne : S.Nonempty := ⟨0, by simp [hS, hΦ.zero]⟩
  have hSc : IsClosed S := isClosed_Iic.preimage hΦ.cont
  have hmem : sSup S ∈ S := hSc.sSup_mem hSne
  constructor
  · intro h
    exact hΦ.mono.reflect_lt (lt_of_le_of_lt hmem h)
  · intro h
    by_contra h'
    push Not at h'
    exact (not_le.2 h) (le_sSup (show x ∈ S from h'))

lemma inv_ne_zero {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) {s : ℝ≥0∞} (hs : 0 < s) :
    sSup {y | Φ y ≤ s} ≠ 0 := by
  intro h0
  have h0' : Tendsto Φ (𝓝 0) (𝓝 0) := by
    have := hΦ.cont.tendsto 0
    rwa [hΦ.zero] at this
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ≥0∞), Φ x < s :=
    (h0'.eventually_lt_const hs).filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hx1, hx2⟩ := (hev.and self_mem_nhdsWithin).exists
  have : s < Φ x := by
    rw [phi_lt_iff hΦ, h0]
    exact hx2
  exact absurd hx1 (not_lt.2 this.le)

/-- `ofReal l < ofReal b⁻¹ * x ↔ ofReal (b * l) < x` for `b > 0`. -/
lemma lt_inv_mul_iff {b l : ℝ} (hb : 0 < b) (x : ℝ≥0∞) :
    ENNReal.ofReal l < ENNReal.ofReal b⁻¹ * x ↔ ENNReal.ofReal (b * l) < x := by
  rw [ENNReal.ofReal_inv_of_pos hb, ← ENNReal.div_eq_inv_mul,
    ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.2 hb).ne') (Or.inl ENNReal.ofReal_ne_top),
    ENNReal.ofReal_mul hb.le, mul_comm]

lemma measurable_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → ℝ≥0∞) :
    Measurable fun t : ℝ => P {ω | ENNReal.ofReal t < F ω} :=
  Antitone.measurable fun s t hst => measure_mono fun ω hω =>
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst) hω

/-! ### The main estimate at fixed truncation level -/

lemma good_lambda_trunc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : IsPhi Φ c)
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (β δ ε : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hε : 0 < ε)
    (h71 : ∀ l : ℝ, 0 < l →
      P {ω | ENNReal.ofReal (β * l) < g ω ∧ f ω ≤ ENNReal.ofReal (δ * l)}
        ≤ ENNReal.ofReal ε * P {ω | ENNReal.ofReal l < g ω})
    (N : ℕ) :
    ∫⁻ ω, Φ (ENNReal.ofReal β⁻¹ * min (g ω) N) ∂P
      ≤ ENNReal.ofReal ε * ∫⁻ ω, Φ (min (g ω) N) ∂P
        + ∫⁻ ω, Φ (ENNReal.ofReal δ⁻¹ * f ω) ∂P := by
  have hΦm : Measurable Φ := hΦ.cont.measurable
  have hgN : Measurable fun ω => min (g ω) (N : ℝ≥0∞) := hg.min measurable_const
  have hβ0 : 0 < β := by linarith
  rw [layer_cake P (fun ω => Φ (ENNReal.ofReal β⁻¹ * min (g ω) N))
      (hΦm.comp (measurable_const.mul hgN)),
    layer_cake P (fun ω => Φ (min (g ω) N)) (hΦm.comp hgN),
    layer_cake P (fun ω => Φ (ENNReal.ofReal δ⁻¹ * f ω)) (hΦm.comp (measurable_const.mul hf)),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left']
  · refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ≥0∞) < ENNReal.ofReal t := ENNReal.ofReal_pos.2 ht
    set a := sSup {y | Φ y ≤ ENNReal.ofReal t} with ha
    have hiff := phi_lt_iff hΦ (ENNReal.ofReal t)
    simp only [← ha] at hiff
    have ha0 : a ≠ 0 := inv_ne_zero hΦ ht'
    simp only [hiff]
    rcases eq_or_ne a ⊤ with hatop | hatop
    · have : {ω | a < ENNReal.ofReal β⁻¹ * min (g ω) N} = ∅ := by
        ext ω; simp [hatop]
      rw [this, measure_empty]; exact zero_le'
    set l := a.toReal with hl
    have hal : a = ENNReal.ofReal l := (ENNReal.ofReal_toReal hatop).symm
    have hlpos : 0 < l := ENNReal.toReal_pos ha0 hatop
    rw [hal]
    simp only [lt_inv_mul_iff hβ0, lt_inv_mul_iff hδ]
    have hsub : {ω | ENNReal.ofReal (β * l) < min (g ω) N} ⊆
        {ω | ENNReal.ofReal (β * l) < min (g ω) N ∧ f ω ≤ ENNReal.ofReal (δ * l)} ∪
        {ω | ENNReal.ofReal (δ * l) < f ω} := by
      intro ω hω
      by_cases hfω : f ω ≤ ENNReal.ofReal (δ * l)
      · exact Or.inl ⟨hω, hfω⟩
      · exact Or.inr (not_le.1 hfω)
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    gcongr
    by_cases hN : ENNReal.ofReal (β * l) < N
    · have e1 : {ω | ENNReal.ofReal (β * l) < min (g ω) N ∧ f ω ≤ ENNReal.ofReal (δ * l)} =
          {ω | ENNReal.ofReal (β * l) < g ω ∧ f ω ≤ ENNReal.ofReal (δ * l)} := by
        ext ω; simp [hN]
      have hlN : ENNReal.ofReal l < N := by
        refine lt_of_lt_of_le ?_ hN.le
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        nlinarith
      have e2 : {ω | ENNReal.ofReal l < min (g ω) N} = {ω | ENNReal.ofReal l < g ω} := by
        ext ω; simp [hlN]
      rw [e1, e2]
      exact h71 l hlpos
    · have e1 : {ω | ENNReal.ofReal (β * l) < min (g ω) N ∧ f ω ≤ ENNReal.ofReal (δ * l)} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h _
        exact hN (lt_of_lt_of_le h (min_le_right _ _))
      rw [e1, measure_empty]; exact zero_le'
  · exact (measurable_const.mul (measurable_tail P _)).aemeasurable


/-! ### Arithmetic -/

lemma key_arith (I J : ℝ≥0∞) (γ η : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (hγε : (γ : ℝ) * ε < 1)
    (hI : I ≠ ⊤) (h : I ≤ γ * (ENNReal.ofReal ε * I + η * J)) :
    I ≤ ENNReal.ofReal (γ * η / (1 - γ * ε)) * J := by
  have h1 : (0 : ℝ) < 1 - γ * ε := by linarith
  by_cases hJ : J = ⊤
  · subst hJ
    by_cases hγη : (γ : ℝ) * η = 0
    · rcases mul_eq_zero.1 hγη with hγ | hη
      · have hγ' : γ = 0 := by exact_mod_cast hγ
        subst hγ'
        simp at h
        simp [h]
      · have hη' : η = 0 := by exact_mod_cast hη
        subst hη'
        simp only [ENNReal.coe_zero, zero_mul, add_zero] at h
        have hreal : I.toReal ≤ γ * (ε * I.toReal) := by
          have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI)) h
          rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
            ENNReal.toReal_ofReal hε.le] at this
        have hI0 : I.toReal = 0 := by
          have hnn : 0 ≤ I.toReal := ENNReal.toReal_nonneg
          nlinarith
        rw [ENNReal.toReal_eq_zero_iff] at hI0
        rcases hI0 with hI0 | hI0
        · simp [hI0]
        · exact absurd hI0 hI
    · have hpos : 0 < (γ : ℝ) * η / (1 - γ * ε) := by
        have : 0 < (γ : ℝ) * η := lt_of_le_of_ne (by positivity) (Ne.symm hγη)
        positivity
      rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
      exact le_top
  · have hreal : I.toReal ≤ γ * (ε * I.toReal + η * J.toReal) := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI,
          ENNReal.mul_ne_top ENNReal.coe_ne_top hJ⟩)) h
      rwa [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI)
        (ENNReal.mul_ne_top ENNReal.coe_ne_top hJ), ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.coe_toReal, ENNReal.coe_toReal, ENNReal.toReal_ofReal hε.le] at this
    have hfin : I.toReal ≤ γ * η / (1 - γ * ε) * J.toReal := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h1]
      nlinarith
    calc I = ENNReal.ofReal I.toReal := (ENNReal.ofReal_toReal hI).symm
      _ ≤ ENNReal.ofReal (γ * η / (1 - γ * ε) * J.toReal) := ENNReal.ofReal_le_ofReal hfin
      _ = ENNReal.ofReal (γ * η / (1 - γ * ε)) * ENNReal.ofReal J.toReal := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (γ * η / (1 - γ * ε)) * J := by rw [ENNReal.ofReal_toReal hJ]

/-! ### Lemma 7.1 -/

theorem lemma_7_1_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (c : ℝ≥0) (hΦ : BurkholderDFI.SquareFnLp.IsPhi Φ c)
    (f g : Ω → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (β δ ε : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hε : 0 < ε)
    (h71 : ∀ l : ℝ, 0 < l →
      P {ω | ENNReal.ofReal (β * l) < g ω ∧ f ω ≤ ENNReal.ofReal (δ * l)}
        ≤ ENNReal.ofReal ε * P {ω | ENNReal.ofReal l < g ω})
    (γ η : ℝ≥0)
    (h72 : ∀ l : ℝ, 0 < l →
      Φ (ENNReal.ofReal (β * l)) ≤ γ * Φ (ENNReal.ofReal l) ∧
      Φ (ENNReal.ofReal (δ⁻¹ * l)) ≤ η * Φ (ENNReal.ofReal l))
    (hγε : (γ : ℝ) * ε < 1) :
    ∫⁻ ω, Φ (g ω) ∂P ≤ ENNReal.ofReal (γ * η / (1 - γ * ε)) * ∫⁻ ω, Φ (f ω) ∂P := by
  have hΦm : Measurable Φ := hΦ.cont.measurable
  have hβ0 : 0 < β := by linarith
  -- the truncated estimate
  have hN : ∀ N : ℕ, ∫⁻ ω, Φ (min (g ω) N) ∂P
      ≤ ENNReal.ofReal (γ * η / (1 - γ * ε)) * ∫⁻ ω, Φ (f ω) ∂P := by
    intro N
    have hgN : Measurable fun ω => min (g ω) (N : ℝ≥0∞) := hg.min measurable_const
    have hfin : ∫⁻ ω, Φ (min (g ω) N) ∂P ≠ ⊤ := by
      refine ne_top_of_le_ne_top (isPhi_ne_top hΦ (ENNReal.natCast_ne_top N)) ?_
      calc ∫⁻ ω, Φ (min (g ω) N) ∂P ≤ ∫⁻ _, Φ N ∂P :=
            lintegral_mono fun ω => hΦ.mono (min_le_right _ _)
        _ = Φ N := by simp
    refine key_arith _ _ γ η ε hε hγε hfin ?_
    calc ∫⁻ ω, Φ (min (g ω) N) ∂P
        ≤ ∫⁻ ω, γ * Φ (ENNReal.ofReal β⁻¹ * min (g ω) N) ∂P := by
          refine lintegral_mono fun ω => ?_
          have := scale_le hΦ hβ0 (fun l hl => (h72 l hl).1) (ENNReal.ofReal β⁻¹ * min (g ω) N)
          rwa [← mul_assoc, ← ENNReal.ofReal_mul hβ0.le, mul_inv_cancel₀ hβ0.ne',
            ENNReal.ofReal_one, one_mul] at this
      _ = γ * ∫⁻ ω, Φ (ENNReal.ofReal β⁻¹ * min (g ω) N) ∂P :=
          lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ ≤ γ * (ENNReal.ofReal ε * ∫⁻ ω, Φ (min (g ω) N) ∂P
            + ∫⁻ ω, Φ (ENNReal.ofReal δ⁻¹ * f ω) ∂P) := by
          gcongr
          exact good_lambda_trunc P Φ c hΦ f g hf hg β δ ε hβ hδ hε h71 N
      _ ≤ γ * (ENNReal.ofReal ε * ∫⁻ ω, Φ (min (g ω) N) ∂P + η * ∫⁻ ω, Φ (f ω) ∂P) := by
          gcongr
          rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
          exact lintegral_mono fun ω =>
            scale_le hΦ (inv_pos.2 hδ) (fun l hl => (h72 l hl).2) (f ω)
  -- pass to the limit `N → ∞`
  have hlim : Tendsto (fun N : ℕ => ∫⁻ ω, Φ (min (g ω) N) ∂P) atTop (𝓝 (∫⁻ ω, Φ (g ω) ∂P)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun N => (hΦm.comp (hg.min measurable_const)).aemeasurable)
      (Eventually.of_forall fun ω N M hNM => hΦ.mono (min_le_min_left _ (by exact_mod_cast hNM)))
      (Eventually.of_forall fun ω => ?_)
    have : Tendsto (fun N : ℕ => min (g ω) (N : ℝ≥0∞)) atTop (𝓝 (min (g ω) ⊤)) :=
      tendsto_const_nhds.min ENNReal.tendsto_nat_nhds_top
    rw [min_eq_left le_top] at this
    exact (hΦ.cont.tendsto _).comp this
  exact le_of_tendsto' hlim hN


/-! ### Theorem 18.3 -/

lemma measurable_sqFn_of (hadp : StronglyAdapted ℱ f) : Measurable (sqFn f) := by
  refine Measurable.iSup fun n => ?_
  unfold sqFnN
  exact (Finset.measurable_sum _ fun k _ =>
    (measurable_dseq hadp k).pow_const 2).sqrt.ennreal_ofReal

lemma measurable_maxFn_of (hadp : StronglyAdapted ℱ f) : Measurable (maxFn f) := by
  refine Measurable.iSup fun n => ?_
  unfold maxFnN
  refine Measurable.iSup fun k => ?_
  refine Measurable.iSup fun hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have : Measurable (f k) := by
    have := measurable_gZ hadp k
    rwa [gZ_pos f hk1] at this
  exact this.abs.ennreal_ofReal

lemma phi_two_pow_le {Φ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0} (hΦ : IsPhi Φ c) (k : ℕ) (x : ℝ≥0∞) :
    Φ (2 ^ k * x) ≤ (c : ℝ≥0∞) ^ k * Φ x := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc Φ (2 ^ (k + 1) * x) = Φ (2 * (2 ^ k * x)) := by ring_nf
      _ ≤ c * Φ (2 ^ k * x) := hΦ.growth _
      _ ≤ c * ((c : ℝ≥0∞) ^ k * Φ x) := mul_le_mul_right ih _
      _ = (c : ℝ≥0∞) ^ (k + 1) * Φ x := by ring

theorem theorem_18_3_core (c : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P → (∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n) →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, IsPhi Φ c →
          ∫⁻ ω, Φ (sqFn f ω) ∂P ≤ (C : ℝ≥0∞) * ∫⁻ ω, Φ (maxFn f ω) ∂P := by
  -- the parameters
  set m : ℕ := ⌈(c : ℝ)⌉₊ + 1 with hm
  set δ : ℝ := (2 : ℝ)⁻¹ ^ m with hδdef
  have hδ : 0 < δ := by positivity
  have hδle : δ ≤ 2⁻¹ := by
    rw [hδdef]
    calc (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 2⁻¹ := pow_one _
  have hδβ : δ < Real.sqrt ((2 : ℝ) ^ 2 - 1) := by
    have : (1 : ℝ) < Real.sqrt ((2 : ℝ) ^ 2 - 1) := by
      rw [show ((2 : ℝ) ^ 2 - 1) = 3 by norm_num]
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    linarith
  have hδsq : δ ^ 2 = 1 / (4 : ℝ) ^ m := by
    rw [hδdef, ← pow_mul, mul_comm, pow_mul, show ((2 : ℝ)⁻¹ ^ 2) = 1 / 4 by norm_num,
      one_div_pow]
  have h4m : 1 + (m : ℝ) * 3 ≤ (4 : ℝ) ^ m := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 3 by norm_num) m
    norm_num at this
    linarith
  have hcm : (c : ℝ) + 1 ≤ m := by
    rw [hm]; push_cast
    linarith [Nat.le_ceil (c : ℝ)]
  set ε : ℝ := 2 * δ ^ 2 / (2 ^ 2 - δ ^ 2 - 1) with hε
  have hden : 0 < (2 : ℝ) ^ 2 - δ ^ 2 - 1 := by nlinarith
  have hε0 : 0 < ε := by positivity
  have hγε : (c : ℝ) * ε < 1 := by
    rw [hε, mul_div_assoc', div_lt_one hden]
    have h4pos : (0 : ℝ) < 4 ^ m := by positivity
    have hkey : δ ^ 2 * (2 * c + 1) < 3 := by
      rw [hδsq, one_div, inv_mul_lt_iff₀ h4pos]
      nlinarith
    nlinarith
  -- the constant
  set η : ℝ≥0 := c ^ m with hη
  set Cr : ℝ := (c : ℝ) * η / (1 - c * ε) with hCr
  refine ⟨Real.toNNReal Cr + 1, by positivity, ?_⟩
  intro Ω mΩ P hP ℱ f hf hnn Φ hΦ
  have hadp := hf.stronglyAdapted
  have hsq : Measurable (sqFn f) := measurable_sqFn_of hadp
  have hmax : Measurable (maxFn f) := measurable_maxFn_of hadp
  have h71 : ∀ l : ℝ, 0 < l →
      P {ω | ENNReal.ofReal (2 * l) < sqFn f ω ∧ maxFn f ω ≤ ENNReal.ofReal (δ * l)}
        ≤ ENNReal.ofReal ε * P {ω | ENNReal.ofReal l < sqFn f ω} := fun l hl =>
    theorem_18_2_core hf hnn 2 δ (by norm_num) hδ hδβ l hl
  have h72 : ∀ l : ℝ, 0 < l →
      Φ (ENNReal.ofReal (2 * l)) ≤ c * Φ (ENNReal.ofReal l) ∧
      Φ (ENNReal.ofReal (δ⁻¹ * l)) ≤ η * Φ (ENNReal.ofReal l) := by
    intro l hl
    constructor
    · rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      exact hΦ.growth _
    · have hδinv : δ⁻¹ = (2 : ℝ) ^ m := by rw [hδdef, inv_pow, inv_inv]
      rw [hδinv, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat, hη, ENNReal.coe_pow]
      exact phi_two_pow_le hΦ m _
  have hmain := lemma_7_1_core P Φ c hΦ (maxFn f) (sqFn f) hmax hsq 2 δ ε (by norm_num) hδ hε0
    h71 c η h72 hγε
  refine hmain.trans ?_
  have hC : ((Real.toNNReal Cr + 1 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal Cr + 1 := by
    rw [ENNReal.coe_add, ENNReal.coe_one]; rfl
  rw [hC]
  exact mul_le_mul_left le_self_add _

end BurkholderDFI.NonnegPhi

open BurkholderDFI.NonnegPhi


theorem solution (c : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ), Martingale f ℱ P → (∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n) →
        ∀ Φ : ℝ≥0∞ → ℝ≥0∞, BurkholderDFI.SquareFnLp.IsPhi Φ c →
          ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.sqFn f ω) ∂P ≤ (C : ℝ≥0∞) * ∫⁻ ω, Φ (BurkholderDFI.SquareFnLp.maxFn f ω) ∂P := by
  exact theorem_18_3_core c
