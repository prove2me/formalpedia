-- Prove2me | solution 1 for BurkholderDFI.CondSquare.eq_21_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:10:00.141744+00:00
-- url     : https://prove2.me/submissions/823dc1d0-2e63-4f0f-b0bd-291801a619cc

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal


namespace BurkholderDFI.CondSquare

open BurkholderDFI.SquareFnLp

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℕ mΩ}
  {g : ℕ → Ω → ℝ} {f : ℕ → Ω → ℝ}

/-- `((x ^ (1/p)) ^ p = x`. -/
lemma rpow_one_div_rpow (x : ℝ≥0∞) {p : ℝ} (hp : p ≠ 0) : (x ^ (1 / p)) ^ p = x := by
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp, ENNReal.rpow_one]

/-- Hölder step: from `l * m ≤ a` and `a ≤ b^(1/p) m^(1/q)` deduce `l^p m ≤ b`. -/
lemma holder_step {p q : ℝ} (hpq : p.HolderConjugate q) {l : ℝ} (hl : 0 < l)
    {a b m : ℝ≥0∞} (hm : m ≠ ⊤) (h1 : ENNReal.ofReal l * m ≤ a)
    (h2 : a ≤ b ^ (1 / p) * m ^ (1 / q)) :
    ENNReal.ofReal (l ^ p) * m ≤ b := by
  rcases eq_or_ne m 0 with hm0 | hm0
  · simp [hm0]
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hpq' : 1 / q * p = p - 1 := by
    have h := hpq.inv_add_inv_eq_one
    field_simp
    field_simp at h
    linarith
  have h3 : (ENNReal.ofReal l * m) ^ p ≤ (b ^ (1 / p) * m ^ (1 / q)) ^ p :=
    ENNReal.rpow_le_rpow (h1.trans h2) hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
    rpow_one_div_rpow _ hp0.ne', ← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_nonneg hl.le hp0.le,
    hpq'] at h3
  have hsplit : m ^ p = m * m ^ (p - 1) := by
    conv_lhs => rw [show p = 1 + (p - 1) by ring]
    rw [ENNReal.rpow_add _ _ hm0 hm, ENNReal.rpow_one]
  rw [hsplit, ← mul_assoc] at h3
  have hp1 : 0 ≤ p - 1 := by linarith [hpq.lt]
  refine (ENNReal.mul_le_mul_iff_left ?_ (ENNReal.rpow_ne_top_of_nonneg hp1 hm)).1 h3
  intro h0
  rw [ENNReal.rpow_eq_zero_iff] at h0
  rcases h0 with ⟨h, _⟩ | ⟨h, _⟩
  · exact hm0 h
  · exact hm h

/-- Doob's inequality in `L^p` form at a fixed time, for a nonnegative submartingale. -/
lemma doob_fixed [IsProbabilityMeasure P] (hg : Submartingale g ℱ P) (hnn : 0 ≤ g)
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) (n : ℕ) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < maxFnN g n ω}
      ≤ ∫⁻ ω, ENNReal.ofReal (g n ω) ^ p ∂P := by
  set ε : ℝ≥0 := Real.toNNReal l with hε
  have hεl : (ε : ℝ) = l := Real.coe_toNNReal _ hl.le
  have hεl' : (ε : ℝ≥0∞) = ENNReal.ofReal l := rfl
  set A := {ω | (ε : ℝ) ≤
    (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => g k ω} with hA
  have hsub : {ω | ENNReal.ofReal l < maxFnN g n ω} ⊆ A := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, maxFnN, lt_iSup_iff] at hω
    obtain ⟨k, hk, hlt⟩ := hω
    have hk' : k ∈ Finset.range (n + 1) := by
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_range]; omega
    have hnn' : 0 ≤ g k ω := hnn k ω
    have hlt' : l < g k ω := by
      have := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
      rwa [abs_of_nonneg hnn'] at this
    simp only [hA, Set.mem_ofPred_eq, hεl]
    exact hlt'.le.trans (Finset.le_sup' (fun k => g k ω) hk')
  have hmax := maximal_ineq hg hnn (ε := ε) n
  rw [← hA, ofReal_integral_eq_lintegral_ofReal (hg.integrable n).integrableOn
    (Eventually.of_forall fun ω => hnn n ω), hεl'] at hmax
  have hb : ∫⁻ ω in A, ENNReal.ofReal (g n ω) ^ p ∂P ≤ ∫⁻ ω, ENNReal.ofReal (g n ω) ^ p ∂P :=
    setLIntegral_le_lintegral _ _
  refine le_trans ?_ hb
  have hmono : P {ω | ENNReal.ofReal l < maxFnN g n ω} ≤ P A := measure_mono hsub
  refine le_trans (mul_le_mul' le_rfl hmono) ?_
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · subst hp1
    simpa using hmax
  · have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp1
    have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (g n ω)) (P.restrict A) :=
      ((hg.stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl).ennreal_ofReal.aemeasurable
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (P.restrict A) hpq hmeas
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul,
      Measure.restrict_apply_univ] at hH
    exact holder_step hpq hl (measure_ne_top P A) hmax hH

/-- The maximal set is the increasing union of the finite-time maximal sets. -/
lemma measure_maxFn_eq_iSup (P : Measure Ω) (g : ℕ → Ω → ℝ) (l : ℝ) :
    P {ω | ENNReal.ofReal l < maxFn g ω} = ⨆ n, P {ω | ENNReal.ofReal l < maxFnN g n ω} := by
  have hU : {ω | ENNReal.ofReal l < maxFn g ω} = ⋃ n, {ω | ENNReal.ofReal l < maxFnN g n ω} := by
    ext ω; simp [maxFn, lt_iSup_iff]
  rw [hU]
  refine Monotone.measure_iUnion fun n m hnm ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine lt_of_lt_of_le hω ?_
  simp only [maxFnN]
  exact biSup_mono fun k hk => by
    simp only [Finset.mem_Icc] at hk ⊢; omega

/-- (1.5) for a nonnegative submartingale `g` (nonnegative everywhere). -/
lemma eq_1_5_nonneg [IsProbabilityMeasure P] (hg : Submartingale g ℱ P) (hnn : 0 ≤ g)
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < maxFn g ω} ≤ pNorm P p g ^ p := by
  rw [measure_maxFn_eq_iSup, ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have : {ω | ENNReal.ofReal l < maxFnN g 0 ω} = ∅ := by
      ext ω; simp [maxFnN]
    rw [this, measure_empty, mul_zero]; exact zero_le
  refine (doob_fixed hg hnn p hp l hl n).trans ?_
  have hp0 : 0 ≤ p := by linarith
  have h1 : ∫⁻ ω, ENNReal.ofReal (g n ω) ^ p ∂P
      = lpNormE P p (fun ω => ENNReal.ofReal |g n ω|) ^ p := by
    simp only [lpNormE]
    rw [rpow_one_div_rpow _ (by linarith)]
    congr 1
    funext ω
    rw [abs_of_nonneg (hnn n ω)]
  rw [h1]
  refine ENNReal.rpow_le_rpow ?_ hp0
  exact le_iSup₂ (f := fun n (_ : n ∈ Set.Ici (1 : ℕ)) =>
    lpNormE P p (fun ω => ENNReal.ofReal |g n ω|)) n hn

/-- (1.5). -/
theorem eq_1_5_core [IsProbabilityMeasure P] {f : ℕ → Ω → ℝ}
    (hf : Martingale f ℱ P ∨ (Submartingale f ℱ P ∧ ∀ n, 1 ≤ n → 0 ≤ᵐ[P] f n))
    (p : ℝ) (hp : 1 ≤ p) (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ p) * P {ω | ENNReal.ofReal l < maxFn f ω} ≤ pNorm P p f ^ p := by
  rcases hf with hf | ⟨hf, hnn⟩
  · -- martingale case: `|f|` is a nonnegative submartingale
    have hsub : Submartingale (f⁺ + (-f)⁺) ℱ P :=
      hf.submartingale.pos.add hf.neg.submartingale.pos
    have heq : (f⁺ + (-f)⁺) = fun n ω => |f n ω| := by
      funext n ω
      simp only [Pi.add_apply, Pi.posPart_apply, Pi.neg_apply]
      rw [posPart_neg, posPart_add_negPart]
    rw [heq] at hsub
    have hnn : (0 : ℕ → Ω → ℝ) ≤ fun n ω => |f n ω| := fun n ω => abs_nonneg _
    have h := eq_1_5_nonneg hsub hnn p hp l hl
    have e1 : maxFn (fun n ω => |f n ω|) = maxFn f := by
      funext ω; simp [maxFn, maxFnN, abs_abs]
    have e2 : pNorm P p (fun n ω => |f n ω|) = pNorm P p f := by
      simp [pNorm, abs_abs]
    rwa [e1, e2] at h
  · -- nonnegative submartingale case: `f⁺` is a nonnegative submartingale a.e. equal to `f`
    have hsub : Submartingale (f⁺) ℱ P := hf.pos
    have hnn' : (0 : ℕ → Ω → ℝ) ≤ f⁺ := fun n ω => by
      simp only [Pi.posPart_apply, Pi.zero_apply]
      exact posPart_nonneg _
    have h := eq_1_5_nonneg hsub hnn' p hp l hl
    have hae : ∀ᵐ ω ∂P, ∀ n, 1 ≤ n → |(f⁺) n ω| = |f n ω| := by
      rw [ae_all_iff]
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · filter_upwards [hnn n hn] with ω hω
        intro _
        simp only [Pi.posPart_apply]
        rw [posPart_eq_self.2 hω]
    have e1 : P {ω | ENNReal.ofReal l < maxFn (f⁺) ω} = P {ω | ENNReal.ofReal l < maxFn f ω} := by
      refine measure_congr ?_
      filter_upwards [hae] with ω hω
      have : maxFn (f⁺) ω = maxFn f ω := by
        simp only [maxFn, maxFnN]
        refine iSup_congr fun n => iSup_congr fun k => iSup_congr fun hk => ?_
        simp only [Finset.mem_Icc] at hk
        rw [hω k hk.1]
      change (ENNReal.ofReal l < maxFn (f⁺) ω) = (ENNReal.ofReal l < maxFn f ω)
      rw [this]
    have e2 : pNorm P p (f⁺) = pNorm P p f := by
      simp only [pNorm]
      refine iSup_congr fun n => iSup_congr fun hn => ?_
      simp only [lpNormE]
      congr 1
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with ω hω
      rw [hω n hn]
    rwa [e1, e2] at h


/-! ### Measurability of the maximal function -/

lemma measurable_maxFnN_filt (hf : Martingale f ℱ P) (k : ℕ) : Measurable[ℱ k] (maxFnN f k) := by
  unfold maxFnN
  refine Measurable.iSup fun n => Measurable.iSup fun hn => ?_
  have hnk : n ≤ k := (Finset.mem_Icc.1 hn).2
  exact (continuous_abs.measurable.comp
    ((hf.stronglyMeasurable n).measurable.mono (ℱ.mono hnk) le_rfl)).ennreal_ofReal

lemma measurable_maxFnN (hf : Martingale f ℱ P) (k : ℕ) : Measurable (maxFnN f k) :=
  (measurable_maxFnN_filt hf k).mono (ℱ.le k) le_rfl

lemma measurable_maxFn (hf : Martingale f ℱ P) : Measurable (maxFn f) :=
  Measurable.iSup fun k => measurable_maxFnN hf k

/-! ### The conditional square function summands -/

/-- `Z_{j+1} = E(d_{j+1}^2 | 𝒜_j)`. -/
noncomputable def Zc (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (j : ℕ) : Ω → ℝ≥0∞ :=
  condLExp (ℱ j) P (fun x => ENNReal.ofReal (dseq f (j + 1) x ^ 2))

lemma measurable_Zc_filt (j : ℕ) : Measurable[ℱ j] (Zc ℱ P f j) :=
  measurable_condLExp _ _ _

lemma measurable_Zc (j : ℕ) : Measurable (Zc ℱ P f j) :=
  measurable_condLExp' _ _ _

lemma condSqFn_eq (ω : Ω) : condSqFn ℱ P f ω = (∑' k, Zc ℱ P f k ω) ^ (1 / 2 : ℝ) := rfl

/-! ### The stopping sets and the transform -/

/-- `{μ ≤ k}`: the maximal function up to time `k` exceeds `l`. -/
def Mset (f : ℕ → Ω → ℝ) (l : ℝ) (k : ℕ) : Set Ω := {ω | ENNReal.ofReal l < maxFnN f k ω}

/-- `{s_{k+1} ≤ δλ}` in squared form: the first `k+1` conditional summands sum to at most `c`. -/
def Sset (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (c : ℝ≥0∞) (k : ℕ) : Set Ω :=
  {ω | ∑ j ∈ Finset.range (k + 1), Zc ℱ P f j ω ≤ c}

def Aset (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (l : ℝ) (c : ℝ≥0∞) (k : ℕ) :
    Set Ω := Mset f l k ∩ Sset ℱ P f c k

lemma measurableSet_Mset (hf : Martingale f ℱ P) (l : ℝ) (k : ℕ) :
    MeasurableSet[ℱ k] (Mset f l k) :=
  measurableSet_lt measurable_const (measurable_maxFnN_filt hf k)

lemma measurableSet_Sset (c : ℝ≥0∞) (k : ℕ) : MeasurableSet[ℱ k] (Sset ℱ P f c k) := by
  refine measurableSet_le ?_ measurable_const
  refine Finset.measurable_sum _ fun j hj => ?_
  have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
  exact (measurable_Zc_filt j).mono (ℱ.mono hjk) le_rfl

lemma measurableSet_Aset (hf : Martingale f ℱ P) (l : ℝ) (c : ℝ≥0∞) (k : ℕ) :
    MeasurableSet[ℱ k] (Aset ℱ P f l c k) :=
  (measurableSet_Mset hf l k).inter (measurableSet_Sset c k)

lemma Mset_zero (f : ℕ → Ω → ℝ) (l : ℝ) : Mset f l 0 = ∅ := by
  ext ω; simp [Mset, maxFnN]

/-- The difference `D_k = f_{k+1} - f_k`. -/
def Dk (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ := f (k + 1) ω - f k ω

lemma Dk_eq_dseq (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : Dk f (k + 1) ω = dseq f (k + 2) ω := by
  simp [Dk, dseq]

/-- The transform increments `h_k = 1_{A_k} D_k`. -/
noncomputable def hk (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (l : ℝ) (c : ℝ≥0∞)
    (k : ℕ) : Ω → ℝ := (Aset ℱ P f l c k).indicator (Dk f k)

/-- The transform `g_n = Σ_{k<n} h_k`. -/
noncomputable def gtr (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (l : ℝ) (c : ℝ≥0∞)
    (n : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.range n, hk ℱ P f l c k ω

/-- The indicator weights. -/
noncomputable def xi (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (l : ℝ) (c : ℝ≥0∞)
    (k : ℕ) : Ω → ℝ := (Aset ℱ P f l c k).indicator (fun _ => (1 : ℝ))

lemma gtr_eq (l : ℝ) (c : ℝ≥0∞) :
    gtr ℱ P f l c = fun n => ∑ k ∈ Finset.range n, xi ℱ P f l c k * (f (k + 1) - f k) := by
  funext n ω
  simp only [gtr, hk, xi, Finset.sum_apply, Pi.mul_apply, Pi.sub_apply, Set.indicator, Dk]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

lemma gtr_martingale [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) (c : ℝ≥0∞) :
    Martingale (gtr ℱ P f l c) ℱ P := by
  have hξ : StronglyAdapted ℱ (xi ℱ P f l c) := fun k =>
    stronglyMeasurable_const.indicator (measurableSet_Aset hf l c k)
  have hbdd : ∀ n ω, xi ℱ P f l c n ω ≤ 1 := fun n ω => by
    simp only [xi, Set.indicator]; split_ifs <;> norm_num
  have hnn : ∀ n ω, 0 ≤ xi ℱ P f l c n ω := fun n ω => by
    simp only [xi, Set.indicator]; split_ifs <;> norm_num
  have h1 := hf.submartingale.sum_mul_sub hξ hbdd hnn
  have h2 := hf.neg.submartingale.sum_mul_sub hξ hbdd hnn
  rw [gtr_eq, martingale_iff]
  refine ⟨?_, h1⟩
  have := h2.neg
  convert this using 1
  funext n ω
  simp only [Pi.neg_apply, Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### Integrability and the conditional second moments -/

lemma integrable_hk [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) (c : ℝ≥0∞) (k : ℕ) :
    Integrable (hk ℱ P f l c k) P :=
  ((hf.integrable (k + 1)).sub (hf.integrable k)).indicator (ℱ.le k _ (measurableSet_Aset hf l c k))

lemma hk_sq (l : ℝ) (c : ℝ≥0∞) (k : ℕ) (ω : Ω) :
    ENNReal.ofReal (hk ℱ P f l c k ω ^ 2)
      = (Aset ℱ P f l c k).indicator (fun ω => ENNReal.ofReal (Dk f k ω ^ 2)) ω := by
  simp only [hk, Set.indicator]
  split_ifs <;> simp

/-- The key identity: `E[h_k^2] = ∫_{A_k} Z_{k+1}`. -/
lemma lintegral_hk_sq [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) (c : ℝ≥0∞) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (hk ℱ P f l c k ω ^ 2) ∂P
      = ∫⁻ ω, (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω ∂P := by
  simp_rw [hk_sq]
  rw [lintegral_indicator (ℱ.le k _ (measurableSet_Aset hf l c k)),
    lintegral_indicator (ℱ.le k _ (measurableSet_Aset hf l c k))]
  rcases k with _ | k
  · have : Aset ℱ P f l c 0 = ∅ := by
      simp [Aset, Mset_zero]
    simp [this]
  · simp_rw [Dk_eq_dseq]
    rw [Zc, setLIntegral_condLExp (ℱ.le (k + 1)) P _ (measurableSet_Aset hf l c (k + 1))]

/-- On `A_k`, `Z_{k+1} ≤ c`. -/
lemma indicator_Zc_le (l : ℝ) (c : ℝ≥0∞) (k : ℕ) (ω : Ω) :
    (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω ≤ c := by
  simp only [Set.indicator]
  split_ifs with h
  · refine le_trans ?_ h.2
    exact Finset.single_le_sum (f := fun j => Zc ℱ P f j ω) (fun _ _ => zero_le)
      (Finset.self_mem_range_succ k)
  · exact zero_le

lemma integrable_hk_sq [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (k : ℕ) : Integrable (fun ω => hk ℱ P f l c k ω ^ 2) P := by
  refine ⟨((integrable_hk hf l c k).aestronglyMeasurable.mul
    (integrable_hk hf l c k).aestronglyMeasurable).congr (Eventually.of_forall fun ω => by
      simp [sq]), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _),
    lintegral_hk_sq hf l c k]
  calc ∫⁻ ω, (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω ∂P ≤ ∫⁻ _, c ∂P :=
        lintegral_mono fun ω => indicator_Zc_le l c k ω
    _ = c := by simp
    _ < ⊤ := hc.lt_top

lemma integrable_mul_of_sq {a b : Ω → ℝ} (ha : AEStronglyMeasurable a P)
    (hb : AEStronglyMeasurable b P) (ha2 : Integrable (fun ω => a ω ^ 2) P)
    (hb2 : Integrable (fun ω => b ω ^ 2) P) : Integrable (fun ω => a ω * b ω) P := by
  refine Integrable.mono' ((ha2.add hb2).div_const 2) (ha.mul hb)
    (Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|a ω| - |b ω|), sq_abs (a ω), sq_abs (b ω), abs_nonneg (a ω),
    abs_nonneg (b ω)]

lemma stronglyMeasurable_hk_filt (hf : Martingale f ℱ P) (l : ℝ) (c : ℝ≥0∞) (k : ℕ) :
    StronglyMeasurable[ℱ (k + 1)] (hk ℱ P f l c k) := by
  refine StronglyMeasurable.indicator ?_ ((ℱ.mono (Nat.le_succ k)) _ (measurableSet_Aset hf l c k))
  exact (hf.stronglyMeasurable (k + 1)).sub
    ((hf.stronglyMeasurable k).mono (ℱ.mono (Nat.le_succ k)))

lemma condExp_Dk [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (k : ℕ) :
    P[Dk f k | ℱ k] =ᵐ[P] 0 := by
  have h1 : P[Dk f k | ℱ k] =ᵐ[P] P[f (k + 1) | ℱ k] - P[f k | ℱ k] :=
    condExp_sub (hf.integrable (k + 1)) (hf.integrable k) _
  have h2 : P[f (k + 1) | ℱ k] =ᵐ[P] f k := hf.condExp_ae_eq (Nat.le_succ k)
  have h3 : P[f k | ℱ k] = f k :=
    condExp_of_stronglyMeasurable (ℱ.le k) (hf.stronglyMeasurable k) (hf.integrable k)
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [hω1, Pi.sub_apply, hω2, h3, Pi.zero_apply, sub_self]

/-- Orthogonality of the increments. -/
lemma integral_hk_mul [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) {c : ℝ≥0∞}
    (hc : c ≠ ⊤) {j k : ℕ} (hjk : j < k) :
    ∫ ω, hk ℱ P f l c j ω * hk ℱ P f l c k ω ∂P = 0 := by
  set Y : Ω → ℝ := fun ω => hk ℱ P f l c j ω * (Aset ℱ P f l c k).indicator (fun _ => (1 : ℝ)) ω
    with hY
  have hYm : StronglyMeasurable[ℱ k] Y :=
    ((stronglyMeasurable_hk_filt hf l c j).mono (ℱ.mono hjk)).mul
      (stronglyMeasurable_const.indicator (measurableSet_Aset hf l c k))
  have heq : (fun ω => hk ℱ P f l c j ω * hk ℱ P f l c k ω) = Y * Dk f k := by
    funext ω
    simp only [hY, Pi.mul_apply, hk, Set.indicator]
    split_ifs <;> simp
  have hint : Integrable (Y * Dk f k) P := by
    rw [← heq]
    exact integrable_mul_of_sq (integrable_hk hf l c j).aestronglyMeasurable
      (integrable_hk hf l c k).aestronglyMeasurable (integrable_hk_sq hf l hc j)
      (integrable_hk_sq hf l hc k)
  have hD : Integrable (Dk f k) P := (hf.integrable (k + 1)).sub (hf.integrable k)
  rw [heq, ← integral_condExp (ℱ.le k)]
  have h1 := condExp_mul_of_stronglyMeasurable_left hYm hint hD
  have h2 := condExp_Dk hf k
  have h3 : P[Y * Dk f k | ℱ k] =ᵐ[P] 0 := by
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [hω1, Pi.mul_apply, hω2, Pi.zero_apply, mul_zero]
  rw [integral_congr_ae h3]
  simp

/-- `E[g_n^2] = Σ_{k<n} E[h_k^2]`. -/
lemma integral_gtr_sq [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (n : ℕ) :
    ∫ ω, gtr ℱ P f l c n ω ^ 2 ∂P = ∑ k ∈ Finset.range n, ∫ ω, hk ℱ P f l c k ω ^ 2 ∂P := by
  have hprod : ∀ j k, Integrable (fun ω => hk ℱ P f l c j ω * hk ℱ P f l c k ω) P := fun j k =>
    integrable_mul_of_sq (integrable_hk hf l c j).aestronglyMeasurable
      (integrable_hk hf l c k).aestronglyMeasurable (integrable_hk_sq hf l hc j)
      (integrable_hk_sq hf l hc k)
  have hexp : ∀ ω, gtr ℱ P f l c n ω ^ 2
      = ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, hk ℱ P f l c j ω * hk ℱ P f l c k ω := by
    intro ω
    simp only [gtr, sq, Finset.sum_mul_sum]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hprod j k]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ fun k _ => hprod j k]
  have : ∀ k ∈ Finset.range n, ∫ ω, hk ℱ P f l c j ω * hk ℱ P f l c k ω ∂P
      = if j = k then ∫ ω, hk ℱ P f l c j ω ^ 2 ∂P else 0 := by
    intro k _
    rcases lt_trichotomy j k with h | h | h
    · rw [if_neg h.ne, integral_hk_mul hf l hc h]
    · subst h; simp [sq]
    · rw [if_neg h.ne', ← integral_hk_mul hf l hc h]
      congr 1; funext ω; ring
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hj]

lemma integrable_gtr_sq [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (n : ℕ) : Integrable (fun ω => gtr ℱ P f l c n ω ^ 2) P := by
  have hprod : ∀ j k, Integrable (fun ω => hk ℱ P f l c j ω * hk ℱ P f l c k ω) P := fun j k =>
    integrable_mul_of_sq (integrable_hk hf l c j).aestronglyMeasurable
      (integrable_hk hf l c k).aestronglyMeasurable (integrable_hk_sq hf l hc j)
      (integrable_hk_sq hf l hc k)
  have hexp : (fun ω => gtr ℱ P f l c n ω ^ 2)
      = fun ω => ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
          hk ℱ P f l c j ω * hk ℱ P f l c k ω := by
    funext ω
    simp only [gtr, sq, Finset.sum_mul_sum]
  rw [hexp]
  exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hprod j k

/-- Pointwise bound on the stopped conditional sum. -/
lemma sum_indicator_Zc_le (l : ℝ) (c : ℝ≥0∞) (n : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range n, (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω
      ≤ {ω | ENNReal.ofReal l < maxFn f ω}.indicator (fun _ => c) ω := by
  classical
  set K := (Finset.range n).filter (fun k => ω ∈ Aset ℱ P f l c k) with hK
  have hsum : ∑ k ∈ Finset.range n, (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω
      = ∑ k ∈ K, Zc ℱ P f k ω := by
    rw [hK, Finset.sum_filter]
    rfl
  rw [hsum]
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe, Finset.sum_empty]; exact zero_le
  set m := K.max' hKne with hm
  have hmK : m ∈ K := Finset.max'_mem K hKne
  have hmA : ω ∈ Aset ℱ P f l c m := (Finset.mem_filter.1 hmK).2
  have hsub : K ⊆ Finset.range (m + 1) := fun k hk => by
    simp only [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_max' K k hk
  calc ∑ k ∈ K, Zc ℱ P f k ω ≤ ∑ k ∈ Finset.range (m + 1), Zc ℱ P f k ω :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => zero_le
    _ ≤ c := hmA.2
    _ = {ω | ENNReal.ofReal l < maxFn f ω}.indicator (fun _ => c) ω := by
        rw [Set.indicator_of_mem]
        show ENNReal.ofReal l < maxFn f ω
        exact lt_of_lt_of_le hmA.1 (le_iSup (fun n => maxFnN f n ω) m)

/-- The `L²` bound on the transform: `E g_n^2 ≤ c P(f^* > λ)`. -/
lemma lintegral_gtr_sq_le [IsProbabilityMeasure P] (hf : Martingale f ℱ P) (l : ℝ) {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (gtr ℱ P f l c n ω ^ 2) ∂P
      ≤ c * P {ω | ENNReal.ofReal l < maxFn f ω} := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gtr_sq hf l hc n)
    (Eventually.of_forall fun ω => sq_nonneg _), integral_gtr_sq hf l hc n,
    ENNReal.ofReal_sum_of_nonneg fun k _ => integral_nonneg fun ω => sq_nonneg _]
  have h1 : ∀ k, ENNReal.ofReal (∫ ω, hk ℱ P f l c k ω ^ 2 ∂P)
      = ∫⁻ ω, (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω ∂P := fun k => by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_hk_sq hf l hc k)
      (Eventually.of_forall fun ω => sq_nonneg _), lintegral_hk_sq hf l c k]
  simp_rw [h1]
  rw [← lintegral_finsetSum _ fun k _ =>
    (measurable_Zc k).indicator (ℱ.le k _ (measurableSet_Aset hf l c k))]
  calc ∫⁻ ω, ∑ k ∈ Finset.range n, (Aset ℱ P f l c k).indicator (Zc ℱ P f k) ω ∂P
      ≤ ∫⁻ ω, {ω | ENNReal.ofReal l < maxFn f ω}.indicator (fun _ => c) ω ∂P :=
        lintegral_mono fun ω => sum_indicator_Zc_le l c n ω
    _ = c * P {ω | ENNReal.ofReal l < maxFn f ω} :=
        lintegral_indicator_const (measurableSet_lt measurable_const (measurable_maxFn hf)) c


/-! ### The event inclusion -/

lemma event_subset (f : ℕ → Ω → ℝ) (β δ l : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hδβ : δ < β - 1)
    (hl : 0 < l) :
    {ω | ENNReal.ofReal (β * l) < maxFn f ω ∧
        max (condSqFn ℱ P f ω) (maxFn (dseq f) ω) ≤ ENNReal.ofReal (δ * l)}
      ⊆ {ω | ENNReal.ofReal ((β - δ - 1) * l)
          < maxFn (gtr ℱ P f l (ENNReal.ofReal (δ * l) ^ 2)) ω} := by
  classical
  intro ω hω
  obtain ⟨h1, h2⟩ := hω
  set c := ENNReal.ofReal (δ * l) ^ 2 with hc
  have hs : ∀ k, ω ∈ Sset ℱ P f c k := by
    intro k
    have hcs : condSqFn ℱ P f ω ≤ ENNReal.ofReal (δ * l) := le_trans (le_max_left _ _) h2
    rw [condSqFn_eq] at hcs
    have : ∑' k, Zc ℱ P f k ω ≤ c := by
      have := ENNReal.rpow_le_rpow hcs (by norm_num : (0 : ℝ) ≤ 2)
      rwa [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
        ENNReal.rpow_two] at this
    exact le_trans (ENNReal.sum_le_tsum _) this
  have hd : ∀ k, 1 ≤ k → |dseq f k ω| ≤ δ * l := by
    intro k hk
    have hdm : maxFn (dseq f) ω ≤ ENNReal.ofReal (δ * l) := le_trans (le_max_right _ _) h2
    have : ENNReal.ofReal |dseq f k ω| ≤ maxFn (dseq f) ω := by
      refine le_trans ?_ (le_iSup (fun n => maxFnN (dseq f) n ω) k)
      exact le_iSup₂ (f := fun n (_ : n ∈ Finset.Icc 1 k) => ENNReal.ofReal |dseq f n ω|) k
        (Finset.mem_Icc.2 ⟨hk, le_rfl⟩)
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (this.trans hdm)
  obtain ⟨N, hN1, hN⟩ : ∃ N, 1 ≤ N ∧ β * l < |f N ω| := by
    simp only [maxFn, maxFnN, lt_iSup_iff] at h1
    obtain ⟨n, k, hk, hlt⟩ := h1
    exact ⟨k, (Finset.mem_Icc.1 hk).1, (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1⟩
  have hlN : l < |f N ω| := by nlinarith
  have hex : ∃ n, 1 ≤ n ∧ l < |f n ω| := ⟨N, hN1, hlN⟩
  obtain ⟨m, hm1, hmin⟩ : ∃ m, (1 ≤ m ∧ l < |f m ω|) ∧ ∀ n, n < m → ¬ (1 ≤ n ∧ l < |f n ω|) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun n hn => Nat.find_min hex hn⟩
  have hmN : m ≤ N := by
    by_contra h
    exact hmin N (not_le.1 h) ⟨hN1, hlN⟩
  have hM : ∀ k, ω ∈ Mset f l k ↔ m ≤ k := by
    intro k
    constructor
    · intro hk
      simp only [Mset, Set.mem_setOf_eq, maxFnN, lt_iSup_iff] at hk
      obtain ⟨n, hn, hlt⟩ := hk
      by_contra hcon
      push Not at hcon
      have hn1 := Finset.mem_Icc.1 hn
      exact hmin n (by omega) ⟨hn1.1, (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1⟩
    · intro hk
      show ENNReal.ofReal l < maxFnN f k ω
      refine lt_of_lt_of_le ?_ (le_iSup₂ (f := fun n (_ : n ∈ Finset.Icc 1 k) =>
        ENNReal.ofReal |f n ω|) m (Finset.mem_Icc.2 ⟨hm1.1, hk⟩))
      exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hm1.2, by linarith [hm1.2]⟩
  have hA : ∀ k, ω ∈ Aset ℱ P f l c k ↔ m ≤ k := fun k => by
    simp only [Aset, Set.mem_inter_iff, hM, hs, and_true]
  have hg : gtr ℱ P f l c N ω = f N ω - f m ω := by
    simp only [gtr, hk, Set.indicator]
    have : ∀ k, (if ω ∈ Aset ℱ P f l c k then Dk f k ω else 0)
        = if m ≤ k then Dk f k ω else 0 := fun k => by simp only [hA]
    simp_rw [this]
    rw [← Finset.sum_filter]
    have hfil : (Finset.range N).filter (fun k => m ≤ k) = Finset.Ico m N := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hfil, Finset.sum_Ico_eq_sub _ hmN]
    simp only [Dk]
    rw [Finset.sum_range_sub (fun k => f k ω), Finset.sum_range_sub (fun k => f k ω)]
    ring
  have hfm : |f m ω| ≤ (1 + δ) * l := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rcases Nat.eq_zero_or_pos m' with hm' | hm'
    · subst hm'
      have := hd 1 le_rfl
      simp only [dseq, one_ne_zero, if_false, if_true] at this
      nlinarith
    · have h1 := hd (m' + 1) (by omega)
      have h2 : |f m' ω| ≤ l := by
        by_contra hcon
        exact hmin m' (Nat.lt_succ_self m') ⟨hm', not_le.1 hcon⟩
      have hd' : dseq f (m' + 1) ω = f (m' + 1) ω - f m' ω := by
        simp only [dseq, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        rw [if_neg (by omega)]
      rw [hd'] at h1
      calc |f (m' + 1) ω| = |f m' ω + (f (m' + 1) ω - f m' ω)| := by ring_nf
        _ ≤ |f m' ω| + |f (m' + 1) ω - f m' ω| := abs_add_le _ _
        _ ≤ l + δ * l := add_le_add h2 h1
        _ = (1 + δ) * l := by ring
  have hgN : (β - δ - 1) * l < |gtr ℱ P f l c N ω| := by
    rw [hg]
    have := abs_sub_abs_le_abs_sub (f N ω) (f m ω)
    nlinarith
  show ENNReal.ofReal ((β - δ - 1) * l) < maxFn (gtr ℱ P f l c) ω
  refine lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hgN, ?_⟩) ?_
  · have : 0 < β - δ - 1 := by linarith
    exact lt_trans (mul_pos this hl) hgN
  · refine le_trans ?_ (le_iSup (fun n => maxFnN (gtr ℱ P f l c) n ω) N)
    exact le_iSup₂ (f := fun n (_ : n ∈ Finset.Icc 1 N) => ENNReal.ofReal |gtr ℱ P f l c n ω|) N
      (Finset.mem_Icc.2 ⟨hN1, le_rfl⟩)

/-! ### (21.2) -/

theorem eq_21_2_core [IsProbabilityMeasure P] (hf : Martingale f ℱ P)
    (β δ : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hδβ : δ < β - 1) (l : ℝ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < maxFn f ω ∧
          max (condSqFn ℱ P f ω) (maxFn (dseq f) ω) ≤ ENNReal.ofReal (δ * l)}
      ≤ ENNReal.ofReal (δ ^ 2 / (β - δ - 1) ^ 2) * P {ω | ENNReal.ofReal l < maxFn f ω} := by
  set c := ENNReal.ofReal (δ * l) ^ 2 with hc
  have hcT : c ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  set κ := (β - δ - 1) * l with hκ
  have hκ0 : 0 < κ := mul_pos (by linarith) hl
  have hmart := gtr_martingale hf l c
  have h15 := eq_1_5_core (Or.inl hmart) 2 one_le_two κ hκ0
  have hsub := event_subset (ℱ := ℱ) (P := P) f β δ l hβ hδ hδβ hl
  have hnorm : pNorm P 2 (gtr ℱ P f l c) ^ (2 : ℝ)
      ≤ c * P {ω | ENNReal.ofReal l < maxFn f ω} := by
    have hle : pNorm P 2 (gtr ℱ P f l c)
        ≤ (c * P {ω | ENNReal.ofReal l < maxFn f ω}) ^ (1 / 2 : ℝ) := by
      refine iSup₂_le fun n _ => ?_
      simp only [lpNormE]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      have : ∀ ω, ENNReal.ofReal |gtr ℱ P f l c n ω| ^ (2 : ℝ)
          = ENNReal.ofReal (gtr ℱ P f l c n ω ^ 2) := fun ω => by
        rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]
      simp_rw [this]
      exact lintegral_gtr_sq_le hf l hcT n
    calc pNorm P 2 (gtr ℱ P f l c) ^ (2 : ℝ)
        ≤ ((c * P {ω | ENNReal.ofReal l < maxFn f ω}) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hle (by norm_num)
      _ = c * P {ω | ENNReal.ofReal l < maxFn f ω} := rpow_one_div_rpow _ two_ne_zero
  have hκ2 : ENNReal.ofReal (κ ^ (2 : ℝ)) ≠ 0 := by
    rw [Real.rpow_two]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hκ2T : ENNReal.ofReal (κ ^ (2 : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc P {ω | ENNReal.ofReal (β * l) < maxFn f ω ∧
          max (condSqFn ℱ P f ω) (maxFn (dseq f) ω) ≤ ENNReal.ofReal (δ * l)}
      ≤ P {ω | ENNReal.ofReal κ < maxFn (gtr ℱ P f l c) ω} := measure_mono hsub
    _ ≤ (c * P {ω | ENNReal.ofReal l < maxFn f ω}) / ENNReal.ofReal (κ ^ (2 : ℝ)) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hκ2) (Or.inl hκ2T), mul_comm]
        exact h15.trans hnorm
    _ = ENNReal.ofReal (δ ^ 2 / (β - δ - 1) ^ 2) * P {ω | ENNReal.ofReal l < maxFn f ω} := by
        rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv, hc, Real.rpow_two,
          ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 2
        have : β - δ - 1 ≠ 0 := by intro h; linarith
        rw [hκ]
        field_simp

end BurkholderDFI.CondSquare

open BurkholderDFI.CondSquare


theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ P)
    (β δ : ℝ) (hβ : 1 < β) (hδ : 0 < δ) (hδβ : δ < β - 1) (l : ℝ) (hl : 0 < l) :
    P {ω | ENNReal.ofReal (β * l) < BurkholderDFI.SquareFnLp.maxFn f ω ∧
          max (BurkholderDFI.SquareFnLp.condSqFn ℱ P f ω) (BurkholderDFI.SquareFnLp.maxFn (BurkholderDFI.SquareFnLp.dseq f) ω) ≤ ENNReal.ofReal (δ * l)}
      ≤ ENNReal.ofReal (δ ^ 2 / (β - δ - 1) ^ 2) * P {ω | ENNReal.ofReal l < BurkholderDFI.SquareFnLp.maxFn f ω} := by
  exact eq_21_2_core hf β δ hβ hδ hδβ l hl
