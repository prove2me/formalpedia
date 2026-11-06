-- Prove2me | solution 1 for FastFashion.Approx.eq_2_optional_sampling
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:39:23.058128+00:00
-- url     : https://prove2.me/submissions/8bc8b556-1738-4e4e-892f-214af85529a2

import Mathlib
import Definitions.Def_FastFashion_Structure_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace FFEq2


open FastFashion.Structure

/-- the truncation map `x ↦ x ∧ T` from `WithTop ℝ` to `ℝ` -/
noncomputable def trunc (T : ℝ) : WithTop ℝ → ℝ
  | ⊤ => T
  | (t : ℝ) => min t T

lemma stopMin_eq {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (T : ℝ) (ω : Ω) :
    stopMin N A q T ω = trunc T (tauMin N A q ω) := by
  unfold stopMin trunc
  rfl

lemma trunc_mono (T : ℝ) {x y : WithTop ℝ} (h : x ≤ y) : trunc T x ≤ trunc T y := by
  induction y using WithTop.recTopCoe with
  | top =>
    induction x using WithTop.recTopCoe with
    | top => exact le_rfl
    | coe a => exact min_le_right _ _
  | coe b =>
    induction x using WithTop.recTopCoe with
    | top => exact absurd h (by simp)
    | coe a =>
      have : a ≤ b := WithTop.coe_le_coe.mp h
      exact min_le_min_right _ this

lemma trunc_nonneg {T : ℝ} (hT : 0 ≤ T) {x : WithTop ℝ} (h : 0 ≤ x) : 0 ≤ trunc T x := by
  induction x using WithTop.recTopCoe with
  | top => exact hT
  | coe a =>
    have : (0:ℝ) ≤ a := by exact_mod_cast h
    exact le_min this hT

lemma trunc_le {T : ℝ} (x : WithTop ℝ) : trunc T x ≤ T := by
  induction x using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe a => exact min_le_right _ _

lemma stockoutTime_nonneg {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (s : S) (q : S → ℕ) (ω : Ω) :
    0 ≤ stockoutTime N s q ω := by
  classical
  unfold stockoutTime
  split_ifs with h
  · have : (0:ℝ) ≤ sInf {t : ℝ | 0 ≤ t ∧ N s t ω = q s} :=
      Real.sInf_nonneg (fun x hx => hx.1)
    exact_mod_cast this
  · exact le_top

lemma tauMin_nonneg {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (ω : Ω) :
    0 ≤ tauMin N A q ω := by
  unfold tauMin
  exact Finset.le_inf (fun s _ => stockoutTime_nonneg N s q ω)

/-- right-continuity of an `ℕ`-valued path: locally constant on the right -/
lemma rc_const {f : ℝ → ℕ} {t : ℝ} (h : ContinuousWithinAt f (Set.Ici t) t) :
    ∃ δ > 0, ∀ u, t ≤ u → u < t + δ → f u = f t := by
  have h1 : ∀ᶠ u in nhdsWithin t (Set.Ici t), f u = f t := by
    have := h.eventually (isOpen_discrete {f t} |>.mem_nhds rfl)
    exact this
  rcases (mem_nhdsGE_iff_exists_Ico_subset.mp h1) with ⟨u, hu, hsub⟩
  refine ⟨u - t, by linarith [hu.out], fun v hv1 hv2 => hsub ⟨hv1, by linarith⟩⟩

variable {S Ω : Type*} [MeasurableSpace Ω] {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} {P : Measure Ω}

/-- the path hits every level below a reached value -/
lemma hit (hN : IsPoissonFamily lam N P) (s : S) (ω : Ω) (k : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hk : k ≤ N s c ω) : ∃ u, 0 ≤ u ∧ u ≤ c ∧ N s u ω = k := by
  set B : Set ℝ := {t | 0 ≤ t ∧ k ≤ N s t ω} with hB
  have hBne : B.Nonempty := ⟨c, hc, hk⟩
  have hBbdd : BddBelow B := ⟨0, fun x hx => hx.1⟩
  set ts := sInf B with hts
  have h0 : 0 ≤ ts := le_csInf hBne (fun x hx => hx.1)
  have hc' : ts ≤ c := csInf_le hBbdd ⟨hc, hk⟩
  have hge : k ≤ N s ts ω := by
    by_contra hlt
    push Not at hlt
    obtain ⟨δ, hδ, hconst⟩ := rc_const (hN.rightContinuous s ω ts h0)
    obtain ⟨b, hbB, hb⟩ := exists_lt_of_csInf_lt hBne (show sInf B < ts + δ by linarith)
    have hbts : ts ≤ b := csInf_le hBbdd hbB
    have := hconst b hbts hb
    have := hbB.2
    omega
  refine ⟨ts, h0, hc', le_antisymm ?_ hge⟩
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h, hN.zero]; exact Nat.zero_le _
  · obtain ⟨u, hu, hj⟩ := hN.unitJumps s ω ts h
    set m := max u 0
    have hm : m < ts := max_lt hu h
    set v := (m + ts) / 2
    have hv1 : u < v := by
      have := le_max_left u 0; simp only [v]; linarith
    have hv2 : v < ts := by simp only [v]; linarith
    have hv0 : 0 ≤ v := by
      have := le_max_right u 0; simp only [v]; linarith
    have hvB : v ∉ B := fun hvB => by
      have := csInf_le hBbdd hvB
      linarith
    have hNv : N s v ω < k := by
      by_contra hh; push Not at hh; exact hvB ⟨hv0, hh⟩
    have := hj v hv1 hv2
    omega

lemma stockout_le_iff (hN : IsPoissonFamily lam N P) (s : S) (q : S → ℕ) (ω : Ω) (c : ℝ)
    (hc : 0 ≤ c) : stockoutTime N s q ω ≤ (c : WithTop ℝ) ↔ q s ≤ N s c ω := by
  classical
  set A : Set ℝ := {t : ℝ | 0 ≤ t ∧ N s t ω = q s} with hA
  have hAbdd : BddBelow A := ⟨0, fun x hx => hx.1⟩
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨δ, hδ, hconst⟩ := rc_const (hN.rightContinuous s ω c hc)
    unfold stockoutTime at h
    by_cases hne : A.Nonempty
    · rw [if_pos hne] at h
      have h' : sInf A ≤ c := by exact_mod_cast h
      have hlow : c + δ ≤ sInf A := by
        refine le_csInf hne (fun t ht => ?_)
        by_contra htlt
        push Not at htlt
        rcases le_or_gt t c with htc | htc
        · have := hN.mono s ω ht.1 htc
          have := ht.2
          omega
        · have := hconst t htc.le htlt
          have := ht.2
          omega
      linarith
    · rw [if_neg hne] at h
      exact absurd h (by simp)
  · intro h
    obtain ⟨u, hu0, huc, hu⟩ := hit hN s ω (q s) c hc h
    have hne : A.Nonempty := ⟨u, hu0, hu⟩
    unfold stockoutTime
    rw [if_pos hne]
    have : sInf A ≤ c := (csInf_le hAbdd ⟨hu0, hu⟩).trans huc
    exact_mod_cast this

lemma lt_trunc_iff {T c : ℝ} (hc : c < T) (x : WithTop ℝ) :
    c < trunc T x ↔ ¬ x ≤ (c : WithTop ℝ) := by
  induction x using WithTop.recTopCoe with
  | top => simp [trunc, hc]
  | coe a =>
    simp only [trunc, WithTop.coe_le_coe, not_le, lt_min_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩

lemma measurable_stopMin_single (hN : IsPoissonFamily lam N P) (s : S) (q : S → ℕ) (T : ℝ)
    (hT : 0 < T) : Measurable (fun ω => stopMin N {s} q T ω) := by
  classical
  refine measurable_of_Ioi (fun c => ?_)
  have hfe : ∀ ω, stopMin N {s} q T ω = trunc T (stockoutTime N s q ω) := by
    intro ω; rw [stopMin_eq]; simp [tauMin]
  rcases lt_or_ge c 0 with hc0 | hc0
  · convert MeasurableSet.univ
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
    rw [hfe]
    exact lt_of_lt_of_le hc0 (trunc_nonneg hT.le (stockoutTime_nonneg N s q ω))
  rcases lt_or_ge c T with hcT | hcT
  · have : (fun ω => stopMin N {s} q T ω) ⁻¹' Set.Ioi c = {ω | N s c ω < q s} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_ofPred_eq]
      rw [hfe, lt_trunc_iff hcT, stockout_le_iff hN s q ω c hc0, not_le]
    rw [this]
    exact measurableSet_lt (hN.measurable s c hc0) measurable_const
  · convert MeasurableSet.empty
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_lt]
    exact (hfe ω ▸ trunc_le _).trans hcT


section Poisson
variable {S Ω : Type*} [MeasurableSpace Ω] {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} {P : Measure Ω}

lemma poisson_mean (r : ℝ≥0) :
    HasSum (fun n : ℕ => (Real.exp (-r) * r ^ n / (n.factorial : ℝ)) • (n : ℝ)) (r : ℝ) := by
  rw [← hasSum_nat_add_iff' 1]
  have h := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have hf : (fun n : ℕ => (Real.exp (-r) * r ^ (n + 1) / ((n + 1).factorial : ℝ)) • ((n + 1 : ℕ) : ℝ))
      = fun n : ℕ => (r : ℝ) * (Real.exp (-r) * r ^ n / (n.factorial : ℝ)) := by
    funext n
    rw [smul_eq_mul, Nat.factorial_succ]
    push_cast
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, smul_zero, sub_zero]
  rw [hf]
  simpa using h

lemma measurable_nat_sub {f g : Ω → ℕ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => f ω - g ω) :=
  (measurable_of_countable (fun p : ℕ × ℕ => p.1 - p.2)).comp (hf.prodMk hg)

lemma incr_integral [IsProbabilityMeasure P] (hN : FastFashion.Structure.IsPoissonFamily lam N P)
    (s : S) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hl : 0 ≤ lam s) :
    Integrable (fun ω => ((N s v ω - N s u ω : ℕ) : ℝ)) P ∧
      ∫ ω, ((N s v ω - N s u ω : ℕ) : ℝ) ∂P = lam s * (v - u) := by
  have hY : Measurable (fun ω => N s v ω - N s u ω) :=
    measurable_nat_sub (hN.measurable s v (hu.trans huv)) (hN.measurable s u hu)
  have hmap := hN.incrementLaw s u v hu huv
  set r : ℝ≥0 := (lam s * (v - u)).toNNReal with hr
  have hrr : (r : ℝ) = lam s * (v - u) := Real.coe_toNNReal _ (mul_nonneg hl (by linarith))
  have hcast : AEStronglyMeasurable (fun n : ℕ => (n : ℝ)) (P.map (fun ω => N s v ω - N s u ω)) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hintPo : Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]
    have := (poisson_mean r).summable
    refine this.congr (fun n => ?_)
    simp [smul_eq_mul]
  constructor
  · have := (integrable_map_measure hcast hY.aemeasurable).1 (by rw [hmap]; exact hintPo)
    exact this
  · rw [← integral_map hY.aemeasurable hcast, hmap, integral_poissonMeasure, ← hrr]
    exact (poisson_mean r).tsum_eq

end Poisson

section Indep
variable {S Ω : Type*} [MeasurableSpace Ω] {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} {P : Measure Ω}

/-- the event `{τ_A > u}` (for `u < T`): every size of `A` is still in stock at time `u` -/
def stockEv (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (u : ℝ) : Set Ω :=
  {ω | ∀ s' ∈ A, N s' u ω < q s'}

lemma measurableSet_stockEv (hN : FastFashion.Structure.IsPoissonFamily lam N P)
    (A : Finset S) (q : S → ℕ) {u : ℝ} (hu : 0 ≤ u) : MeasurableSet (stockEv N A q u) := by
  have : stockEv N A q u = ⋂ s' ∈ A, {ω | N s' u ω < q s'} := by
    ext ω; simp [stockEv]
  rw [this]
  exact Finset.measurableSet_biInter A (fun s' _ =>
    measurableSet_lt (hN.measurable s' u hu) measurable_const)

lemma integral_incr_single [IsProbabilityMeasure P]
    (hN : FastFashion.Structure.IsPoissonFamily lam N P)
    (s : S) (hl : 0 ≤ lam s) (k : ℕ) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    ∫ ω, ({ω | N s u ω < k}.indicator (fun _ => (1:ℝ)) ω) * ((N s v ω - N s u ω : ℕ) : ℝ) ∂P =
      P.real {ω | N s u ω < k} * (lam s * (v - u)) := by
  obtain ⟨hXi, hXe⟩ := incr_integral hN s hu huv.le hl
  rcases eq_or_lt_of_le hu with h0 | hpos
  · subst h0
    by_cases hk : 0 < k
    · have : {ω | N s 0 ω < k} = Set.univ := by
        ext ω; simp [hN.zero, hk]
      rw [this]
      simp only [Set.indicator_univ, one_mul, probReal_univ]
      simpa using hXe
    · have : {ω | N s 0 ω < k} = ∅ := by
        ext ω; simp [hN.zero]; omega
      rw [this]
      simp
  · have hinc := hN.indepIncrements s 2 ![0, u, v] le_rfl (by
      intro i; fin_cases i <;> simp [hpos, huv])
    have hind := hinc.indepFun (show (0 : Fin 2) ≠ 1 by decide)
    simp only [Matrix.cons_val, Fin.succ_zero_eq_one, Fin.castSucc_zero, Fin.succ_one_eq_two,
      Fin.castSucc_one] at hind
    have hind2 := hind.comp (φ := fun n : ℕ => if n < k then (1:ℝ) else 0) (ψ := fun n : ℕ => (n : ℝ))
      (measurable_of_countable _) (measurable_of_countable _)
    have hfun : (fun ω => ({ω | N s u ω < k}.indicator (fun _ => (1:ℝ)) ω) *
        ((N s v ω - N s u ω : ℕ) : ℝ)) =
        ((fun n : ℕ => if n < k then (1:ℝ) else 0) ∘ (fun ω => N s u ω - N s 0 ω)) *
          ((fun n : ℕ => (n : ℝ)) ∘ (fun ω => N s v ω - N s u ω)) := by
      funext ω
      simp [Set.indicator, hN.zero]
    rw [hfun, hind2.integral_mul_eq_mul_integral]
    · congr 1
      · rw [← integral_indicator_one (measurableSet_lt (hN.measurable s u hu) measurable_const)]
        congr 1
        funext ω
        simp [Set.indicator, hN.zero]
    · exact ((measurable_of_countable _).comp
        (measurable_nat_sub (hN.measurable s u hu) (hN.measurable s 0 le_rfl))).aestronglyMeasurable
    · exact ((measurable_of_countable _).comp
        (measurable_nat_sub (hN.measurable s v (hu.trans huv.le)) (hN.measurable s u hu))).aestronglyMeasurable

/-- the σ-algebra generated by the process of size `i` -/
noncomputable def procSigma {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (i : S) : MeasurableSpace Ω :=
  ⨆ (t : ℝ) (_ : 0 ≤ t), MeasurableSpace.comap (N i t) inferInstance

/-- the σ-algebra generated by the processes with sizes in `I` -/
noncomputable def sigOn {S Ω : Type*} (N : S → ℝ → Ω → ℕ) (I : Set S) : MeasurableSpace Ω :=
  ⨆ i ∈ I, procSigma N i

lemma key_indep [IsProbabilityMeasure P] [DecidableEq S]
    (hN : FastFashion.Structure.IsPoissonFamily lam N P)
    (A : Finset S) (q : S → ℕ) (s : S) (hs : s ∈ A) (hl : 0 ≤ lam s) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u < v) :
    ∫ ω, ((stockEv N A q u).indicator (fun _ => (1:ℝ)) ω) * ((N s v ω - N s u ω : ℕ) : ℝ) ∂P =
      P.real (stockEv N A q u) * (lam s * (v - u)) := by
  classical
  have hle : ∀ i, procSigma N i ≤ ‹MeasurableSpace Ω› := fun i =>
    iSup₂_le (fun t ht => (hN.measurable i t ht).comap_le)
  have hmeasF : ∀ i (t : ℝ), 0 ≤ t → Measurable[procSigma N i] (N i t) := fun i t ht =>
    Measurable.of_comap_le (le_iSup₂ (f := fun (t : ℝ) (_ : 0 ≤ t) =>
      MeasurableSpace.comap (N i t) inferInstance) t ht)
  have hind : Indep (sigOn N ({s} : Set S)) (sigOn N ({s}ᶜ : Set S)) P :=
    indep_iSup_of_disjoint hle hN.indepSizes disjoint_compl_right
  have hF1 : procSigma N s ≤ sigOn N ({s} : Set S) :=
    le_iSup₂ (f := fun i (_ : i ∈ ({s} : Set S)) => procSigma N i) s rfl
  have hF2 : ∀ i, i ≠ s → procSigma N i ≤ sigOn N ({s}ᶜ : Set S) := fun i hi =>
    le_iSup₂ (f := fun i (_ : i ∈ ({s}ᶜ : Set S)) => procSigma N i) i hi
  set E1 : Set Ω := {ω | N s u ω < q s}
  set E2 : Set Ω := stockEv N (A.erase s) q u
  have hE : stockEv N A q u = E1 ∩ E2 := by
    ext ω
    simp only [stockEv, E1, E2, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_erase]
    constructor
    · intro h; exact ⟨h s hs, fun s' hs' => h s' hs'.2⟩
    · rintro ⟨h1, h2⟩ s' hs'
      by_cases hss : s' = s
      · subst hss; exact h1
      · exact h2 s' ⟨hss, hs'⟩
  -- measurability of the pieces
  have hE1m : MeasurableSet[sigOn N ({s} : Set S)] E1 :=
    hF1 _ (measurableSet_lt (hmeasF s u hu) measurable_const)
  have hE2m : MeasurableSet[sigOn N ({s}ᶜ : Set S)] E2 := by
    have : E2 = ⋂ s' ∈ A.erase s, {ω | N s' u ω < q s'} := by
      ext ω; simp [E2, stockEv]
    rw [this]
    refine Finset.measurableSet_biInter _ (fun s' hs' => ?_)
    exact hF2 s' (Finset.ne_of_mem_erase hs') _
      (measurableSet_lt (hmeasF s' u hu) measurable_const)
  set X : Ω → ℝ := fun ω => ((N s v ω - N s u ω : ℕ) : ℝ)
  set f1 : Ω → ℝ := fun ω => E1.indicator (fun _ => (1:ℝ)) ω * X ω
  set f2 : Ω → ℝ := E2.indicator (fun _ => (1:ℝ))
  have hf1m : Measurable[sigOn N ({s} : Set S)] f1 := by
    refine Measurable.mul ?_ ?_
    · exact measurable_const.indicator hE1m
    · have : Measurable[procSigma N s] X :=
        (measurable_of_countable (fun p : ℕ × ℕ => ((p.1 - p.2 : ℕ) : ℝ))).comp
          ((hmeasF s v (hu.trans huv.le)).prodMk (hmeasF s u hu))
      exact this.mono hF1 le_rfl
  have hf2m : Measurable[sigOn N ({s}ᶜ : Set S)] f2 := measurable_const.indicator hE2m
  have hindf : f1 ⟂ᵢ[P] f2 := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left (indep_of_indep_of_le_right hind hf2m.comap_le) hf1m.comap_le
  have hfun : (fun ω => ((stockEv N A q u).indicator (fun _ => (1:ℝ)) ω) * X ω) = f1 * f2 := by
    funext ω
    simp only [Pi.mul_apply, f1, f2, hE]
    by_cases h1 : ω ∈ E1 <;> by_cases h2 : ω ∈ E2 <;> simp [Set.indicator, h1, h2]
  have hG1 : sigOn N ({s} : Set S) ≤ ‹MeasurableSpace Ω› := iSup₂_le (fun i _ => hle i)
  have hG2 : sigOn N ({s}ᶜ : Set S) ≤ ‹MeasurableSpace Ω› := iSup₂_le (fun i _ => hle i)
  rw [show (fun ω => ((stockEv N A q u).indicator (fun _ => (1:ℝ)) ω) *
      ((N s v ω - N s u ω : ℕ) : ℝ)) = f1 * f2 from hfun,
    hindf.integral_mul_eq_mul_integral (hf1m.mono hG1 le_rfl).aestronglyMeasurable
      (hf2m.mono hG2 le_rfl).aestronglyMeasurable]
  have h1 : ∫ ω, f1 ω ∂P = P.real E1 * (lam s * (v - u)) :=
    integral_incr_single hN s hl (q s) hu huv
  have h2 : ∫ ω, f2 ω ∂P = P.real E2 := integral_indicator_one (hG2 _ hE2m)
  have hprod : P.real (E1 ∩ E2) = P.real E1 * P.real E2 := by
    have := (Indep_iff _ _ P).1 hind E1 E2 hE1m hE2m
    simp only [measureReal_def, this, ENNReal.toReal_mul]
  rw [h1, h2, hE, hprod]
  ring

end Indep

section Grid
open FastFashion.Structure Filter Topology
variable {S Ω : Type*} [MeasurableSpace Ω] {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} {P : Measure Ω}

lemma tauMin_le_iff (A : Finset S) (hA : A.Nonempty) (q : S → ℕ) (ω : Ω) (c : WithTop ℝ) :
    tauMin N A q ω ≤ c ↔ ∃ s' ∈ A, stockoutTime N s' q ω ≤ c := by
  unfold tauMin
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image A (fun s' => stockoutTime N s' q ω) hA
  have heq : A.inf (fun s' => stockoutTime N s' q ω) = stockoutTime N x q ω :=
    le_antisymm (Finset.inf_le hx) (Finset.le_inf hmin)
  constructor
  · intro h; exact ⟨x, hx, heq ▸ h⟩
  · rintro ⟨s', hs', h⟩; exact (Finset.inf_le hs').trans h

lemma lt_stopMin_iff (hN : IsPoissonFamily lam N P) (A : Finset S) (hA : A.Nonempty)
    (q : S → ℕ) (T : ℝ) (ω : Ω) {c : ℝ} (hc0 : 0 ≤ c) (hcT : c < T) :
    c < stopMin N A q T ω ↔ ω ∈ stockEv N A q c := by
  rw [stopMin_eq, lt_trunc_iff hcT, tauMin_le_iff A hA]
  simp only [stockEv, Set.mem_ofPred_eq, not_exists, not_and]
  refine forall₂_congr (fun s' _ => ?_)
  rw [stockout_le_iff hN s' q ω c hc0, not_le]

lemma stopMin_nonneg (A : Finset S) (q : S → ℕ) {T : ℝ} (hT : 0 < T) (ω : Ω) :
    0 ≤ stopMin N A q T ω := by
  rw [stopMin_eq]; exact trunc_nonneg hT.le (tauMin_nonneg N A q ω)

lemma stopMin_le (A : Finset S) (q : S → ℕ) (T : ℝ) (ω : Ω) : stopMin N A q T ω ≤ T := by
  rw [stopMin_eq]; exact trunc_le _

/-- the grid-index of the first grid point `≥ σ` -/
noncomputable def gidx (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (T : ℝ) (M : ℕ)
    (ω : Ω) : ℕ :=
  ⌈stopMin N A q T ω / (T / M)⌉₊

lemma gidx_le (A : Finset S) (q : S → ℕ) {T : ℝ} (hT : 0 < T) {M : ℕ} (hM : 0 < M) (ω : Ω) :
    gidx N A q T M ω ≤ M := by
  unfold gidx
  rw [Nat.ceil_le]
  have hd : 0 < T / M := div_pos hT (by exact_mod_cast hM)
  rw [div_le_iff₀ hd]
  have : (M : ℝ) * (T / M) = T := by field_simp
  rw [this]; exact stopMin_le A q T ω

lemma lt_gidx_iff (A : Finset S) (q : S → ℕ) {T : ℝ} (hT : 0 < T) {M : ℕ} (hM : 0 < M) (ω : Ω)
    (k : ℕ) : k < gidx N A q T M ω ↔ (k : ℝ) * (T / M) < stopMin N A q T ω := by
  unfold gidx
  have hd : 0 < T / M := div_pos hT (by exact_mod_cast hM)
  rw [Nat.lt_ceil, lt_div_iff₀ hd]

lemma gidx_bounds (A : Finset S) (q : S → ℕ) {T : ℝ} (hT : 0 < T) {M : ℕ} (hM : 0 < M) (ω : Ω) :
    stopMin N A q T ω ≤ (gidx N A q T M ω : ℝ) * (T / M) ∧
      (gidx N A q T M ω : ℝ) * (T / M) < stopMin N A q T ω + T / M := by
  have hd : 0 < T / M := div_pos hT (by exact_mod_cast hM)
  have h0 := stopMin_nonneg (N := N) A q hT ω
  unfold gidx
  constructor
  · have := Nat.le_ceil (stopMin N A q T ω / (T / M))
    rw [div_le_iff₀ hd] at this; exact this
  · have := Nat.ceil_lt_add_one (R := ℝ) (div_nonneg h0 hd.le)
    have h2 := mul_lt_mul_of_pos_right this hd
    rwa [add_mul, div_mul_cancel₀ _ hd.ne', one_mul] at h2

end Grid

section Key
open FastFashion.Structure Filter Topology
variable {S Ω : Type*} [MeasurableSpace Ω] {lam : S → ℝ} {N : S → ℝ → Ω → ℕ} {P : Measure Ω}

lemma indicator_grid (hN : IsPoissonFamily lam N P) (A : Finset S) (hA : A.Nonempty) (q : S → ℕ)
    {T : ℝ} (hT : 0 < T) {M : ℕ} (hM : 0 < M) (ω : Ω) {k : ℕ} (hk : k < M) :
    (stockEv N A q ((k : ℝ) * (T / M))).indicator (fun _ => (1:ℝ)) ω =
      if k < gidx N A q T M ω then 1 else 0 := by
  have hd : 0 < T / M := div_pos hT (by exact_mod_cast hM)
  have hk0 : 0 ≤ (k : ℝ) * (T / M) := by positivity
  have hkT : (k : ℝ) * (T / M) < T := by
    have : (k : ℝ) < M := by exact_mod_cast hk
    calc (k : ℝ) * (T / M) < M * (T / M) := mul_lt_mul_of_pos_right this hd
      _ = T := by field_simp
  have hiff : ω ∈ stockEv N A q ((k : ℝ) * (T / M)) ↔ k < gidx N A q T M ω := by
    rw [lt_gidx_iff A q hT hM ω k, lt_stopMin_iff hN A hA q T ω hk0 hkT]
  by_cases h : k < gidx N A q T M ω
  · rw [Set.indicator_of_mem (hiff.2 h), if_pos h]
  · rw [Set.indicator_of_notMem (fun hh => h (hiff.1 hh)), if_neg h]

lemma sum_split_ite (M g : ℕ) (hg : g ≤ M) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.range M, (if k < g then (1:ℝ) else 0) * f k = ∑ k ∈ Finset.range g, f k := by
  rw [← Finset.sum_range_add_sum_Ico _ hg]
  have h1 : ∑ k ∈ Finset.range g, (if k < g then (1:ℝ) else 0) * f k = ∑ k ∈ Finset.range g, f k :=
    Finset.sum_congr rfl (fun k hk => by rw [if_pos (Finset.mem_range.mp hk), one_mul])
  have h2 : ∑ k ∈ Finset.Ico g M, (if k < g then (1:ℝ) else 0) * f k = 0 :=
    Finset.sum_eq_zero (fun k hk => by
      rw [if_neg (not_lt.mpr (Finset.mem_Ico.mp hk).1), zero_mul])
  rw [h1, h2, add_zero]

/-- grid approximation of `N_s(σ)` -/
noncomputable def Dgrid (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (T : ℝ) (s : S) (M : ℕ)
    (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range M, (stockEv N A q ((k : ℝ) * (T / M))).indicator (fun _ => (1:ℝ)) ω *
    ((N s (((k + 1 : ℕ) : ℝ) * (T / M)) ω - N s ((k : ℝ) * (T / M)) ω : ℕ) : ℝ)

/-- grid approximation of `σ` -/
noncomputable def Sgrid (N : S → ℝ → Ω → ℕ) (A : Finset S) (q : S → ℕ) (T : ℝ) (M : ℕ)
    (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range M, (stockEv N A q ((k : ℝ) * (T / M))).indicator (fun _ => (1:ℝ)) ω * (T / M)

lemma Dgrid_eq (hN : IsPoissonFamily lam N P) (A : Finset S) (hA : A.Nonempty) (q : S → ℕ)
    {T : ℝ} (hT : 0 < T) (s : S) {M : ℕ} (hM : 0 < M) (ω : Ω) :
    Dgrid N A q T s M ω = (N s ((gidx N A q T M ω : ℝ) * (T / M)) ω : ℝ) := by
  have hd : 0 < T / M := div_pos hT (by exact_mod_cast hM)
  unfold Dgrid
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [indicator_grid hN A hA q hT hM ω (Finset.mem_range.mp hk)]),
    sum_split_ite M _ (gidx_le A q hT hM ω)]
  have hcast : ∀ k : ℕ, ((N s (((k + 1 : ℕ) : ℝ) * (T / M)) ω - N s ((k : ℝ) * (T / M)) ω : ℕ) : ℝ)
      = (N s (((k + 1 : ℕ) : ℝ) * (T / M)) ω : ℝ) - (N s ((k : ℝ) * (T / M)) ω : ℝ) := by
    intro k
    rw [Nat.cast_sub]
    exact hN.mono s ω (by positivity) (mul_le_mul_of_nonneg_right (by push_cast; linarith) hd.le)
  rw [Finset.sum_congr rfl (fun k _ => hcast k),
    Finset.sum_range_sub (fun i : ℕ => (N s ((i : ℝ) * (T / M)) ω : ℝ))]
  simp [hN.zero]

lemma Sgrid_eq (hN : IsPoissonFamily lam N P) (A : Finset S) (hA : A.Nonempty) (q : S → ℕ)
    {T : ℝ} (hT : 0 < T) {M : ℕ} (hM : 0 < M) (ω : Ω) :
    Sgrid N A q T M ω = (gidx N A q T M ω : ℝ) * (T / M) := by
  unfold Sgrid
  rw [Finset.sum_congr rfl (fun k hk => by
    rw [indicator_grid hN A hA q hT hM ω (Finset.mem_range.mp hk)]),
    sum_split_ite M _ (gidx_le A q hT hM ω)]
  simp

lemma ind_mul_eq {E : Set Ω} (f : Ω → ℝ) :
    (fun ω => E.indicator (fun _ => (1:ℝ)) ω * f ω) = E.indicator f := by
  funext ω; by_cases h : ω ∈ E <;> simp [h]

lemma integral_grid [IsProbabilityMeasure P] [DecidableEq S] (hN : IsPoissonFamily lam N P)
    (hlam : ∀ s, 0 < lam s) (A : Finset S) (q : S → ℕ)
    {T : ℝ} (hT : 0 < T) (s : S) (hs : s ∈ A) {M : ℕ} (hM : 0 < M) :
    ∫ ω, Dgrid N A q T s M ω ∂P = lam s * ∫ ω, Sgrid N A q T M ω ∂P := by
  have hd : 0 < T / M := div_pos hT (by exact_mod_cast hM)
  have hk0 : ∀ k : ℕ, 0 ≤ (k : ℝ) * (T / M) := fun k => by positivity
  have hlt : ∀ k : ℕ, (k : ℝ) * (T / M) < ((k + 1 : ℕ) : ℝ) * (T / M) := fun k =>
    mul_lt_mul_of_pos_right (by push_cast; linarith) hd
  have hEm : ∀ k : ℕ, MeasurableSet (stockEv N A q ((k : ℝ) * (T / M))) := fun k =>
    measurableSet_stockEv hN A q (hk0 k)
  unfold Dgrid Sgrid
  rw [integral_finsetSum _ (fun k _ => by
      rw [ind_mul_eq]
      exact (incr_integral hN s (hk0 k) (hlt k).le (hlam s).le).1.indicator (hEm k)),
    integral_finsetSum _ (fun k _ => by
      rw [ind_mul_eq]
      exact (integrable_const _).indicator (hEm k))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [key_indep hN A q s hs (hlam s).le (hk0 k) (hlt k), integral_mul_const]
  rw [show (fun _ : Ω => (1:ℝ)) = (1 : Ω → ℝ) from rfl, integral_indicator_one (hEm k)]
  push_cast
  ring

lemma measurable_Dgrid (hN : IsPoissonFamily lam N P) (A : Finset S) (q : S → ℕ)
    {T : ℝ} (hT : 0 < T) (s : S) (M : ℕ) : Measurable (Dgrid N A q T s M) := by
  have hk0 : ∀ k : ℕ, 0 ≤ (k : ℝ) * (T / M) := fun k => by positivity
  unfold Dgrid
  refine Finset.measurable_sum _ (fun k _ => ?_)
  refine (measurable_const.indicator (measurableSet_stockEv hN A q (hk0 k))).mul ?_
  exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (measurable_nat_sub (hN.measurable s _ (hk0 (k + 1))) (hN.measurable s _ (hk0 k)))

lemma measurable_Sgrid (hN : IsPoissonFamily lam N P) (A : Finset S) (q : S → ℕ)
    {T : ℝ} (hT : 0 < T) (M : ℕ) : Measurable (Sgrid N A q T M) := by
  have hk0 : ∀ k : ℕ, 0 ≤ (k : ℝ) * (T / M) := fun k => by positivity
  unfold Sgrid
  refine Finset.measurable_sum _ (fun k _ => ?_)
  exact (measurable_const.indicator (measurableSet_stockEv hN A q (hk0 k))).mul measurable_const

lemma key [IsProbabilityMeasure P] [DecidableEq S] (hN : IsPoissonFamily lam N P)
    (hlam : ∀ s, 0 < lam s) (A : Finset S) (q : S → ℕ) {T : ℝ} (hT : 0 < T) (s : S)
    (hs : s ∈ A) :
    Integrable (fun ω => (N s (stopMin N A q T ω) ω : ℝ)) P ∧
      ∫ ω, (N s (stopMin N A q T ω) ω : ℝ) ∂P = lam s * hA N P T A q := by
  have hA : A.Nonempty := ⟨s, hs⟩
  have hM : ∀ n : ℕ, 0 < n + 1 := fun n => Nat.succ_pos n
  -- the dominating variable `N_s(T)`
  have hNT : Integrable (fun ω => (N s T ω : ℝ)) P := by
    have := (incr_integral hN s le_rfl hT.le (hlam s).le).1
    simpa [hN.zero] using this
  have hmesh : Tendsto (fun n : ℕ => T / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 1)
  have hgT : ∀ (n : ℕ) ω, (gidx N A q T (n + 1) ω : ℝ) * (T / ((n + 1 : ℕ) : ℝ)) ≤ T := by
    intro n ω
    have h1 : (gidx N A q T (n + 1) ω : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast gidx_le A q hT (hM n) ω
    have hd : 0 < T / ((n + 1 : ℕ) : ℝ) := div_pos hT (by positivity)
    calc (gidx N A q T (n + 1) ω : ℝ) * (T / ((n + 1 : ℕ) : ℝ))
        ≤ ((n + 1 : ℕ) : ℝ) * (T / ((n + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_right h1 hd.le
      _ = T := by field_simp
  have hg0 : ∀ (n : ℕ) ω, 0 ≤ (gidx N A q T (n + 1) ω : ℝ) * (T / ((n + 1 : ℕ) : ℝ)) :=
    fun n ω => by positivity
  -- pointwise limit of the grid approximation of `N_s(σ)`
  have hlimD : ∀ ω, Tendsto (fun n : ℕ => Dgrid N A q T s (n + 1) ω) atTop
      (𝓝 (N s (stopMin N A q T ω) ω : ℝ)) := by
    intro ω
    obtain ⟨δ, hδ, hconst⟩ := rc_const (hN.rightContinuous s ω _ (stopMin_nonneg A q hT ω))
    have hev : ∀ᶠ n : ℕ in atTop, T / ((n + 1 : ℕ) : ℝ) < δ := (hmesh.eventually (gt_mem_nhds hδ))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    rw [Dgrid_eq hN A hA q hT s (hM n) ω]
    obtain ⟨hb1, hb2⟩ := gidx_bounds (N := N) A q hT (hM n) ω
    rw [hconst _ hb1 (by linarith)]
  -- pointwise limit of the grid approximation of `σ`
  have hlimS : ∀ ω, Tendsto (fun n : ℕ => Sgrid N A q T (n + 1) ω) atTop
      (𝓝 (stopMin N A q T ω)) := by
    intro ω
    have hup : Tendsto (fun n : ℕ => stopMin N A q T ω + T / ((n + 1 : ℕ) : ℝ)) atTop
        (𝓝 (stopMin N A q T ω)) := by
      simpa using (tendsto_const_nhds (x := stopMin N A q T ω)).add hmesh
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_) (fun n => ?_)
    · rw [Sgrid_eq hN A hA q hT (hM n) ω]; exact (gidx_bounds A q hT (hM n) ω).1
    · rw [Sgrid_eq hN A hA q hT (hM n) ω]; exact (gidx_bounds A q hT (hM n) ω).2.le
  have hboundD : ∀ n : ℕ, ∀ᵐ ω ∂P, ‖Dgrid N A q T s (n + 1) ω‖ ≤ (N s T ω : ℝ) := by
    intro n
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Dgrid_eq hN A hA q hT s (hM n) ω, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact_mod_cast hN.mono s ω (hg0 n ω) (hgT n ω)
  have hboundS : ∀ n : ℕ, ∀ᵐ ω ∂P, ‖Sgrid N A q T (n + 1) ω‖ ≤ T := by
    intro n
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Sgrid_eq hN A hA q hT (hM n) ω, Real.norm_eq_abs, abs_of_nonneg (hg0 n ω)]
    exact hgT n ω
  have hTD := tendsto_integral_of_dominated_convergence _
    (fun n => (measurable_Dgrid hN A q hT s (n + 1)).aestronglyMeasurable) hNT hboundD
    (Filter.Eventually.of_forall hlimD)
  have hTS := tendsto_integral_of_dominated_convergence _
    (fun n => (measurable_Sgrid hN A q hT (n + 1)).aestronglyMeasurable) (integrable_const T) hboundS
    (Filter.Eventually.of_forall hlimS)
  have hTS' := hTS.const_mul (lam s)
  have heq : (fun n : ℕ => ∫ ω, Dgrid N A q T s (n + 1) ω ∂P) =
      fun n => lam s * ∫ ω, Sgrid N A q T (n + 1) ω ∂P := by
    funext n; exact integral_grid hN hlam A q hT s hs (hM n)
  rw [heq] at hTD
  refine ⟨?_, tendsto_nhds_unique hTD hTS'⟩
  have haesm : AEStronglyMeasurable (fun ω => (N s (stopMin N A q T ω) ω : ℝ)) P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (measurable_Dgrid hN A q hT s (n + 1)).aestronglyMeasurable)
      (Filter.Eventually.of_forall hlimD)
  refine hNT.mono' haesm (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact_mod_cast hN.mono s ω (stopMin_nonneg A q hT ω) (stopMin_le A q T ω)

end Key

end FFEq2

open FFEq2 in
theorem solution {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ)
    (hN : FastFashion.Structure.IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (T : ℝ) (hT : 0 < T)
    (Sp : Finset S) (q : S → ℕ) :
    FastFashion.Structure.expectedSales N P Sp T q =
      (∑ s ∈ Sp, lam s) * FastFashion.Structure.hA N P T Sp q + ∑ s ∈ Spᶜ, lam s * FastFashion.Structure.hA N P T (insert s Sp) q := by
  unfold FastFashion.Structure.expectedSales FastFashion.Structure.sales
  push_cast
  have h1 : ∀ s ∈ Sp, Integrable (fun ω =>
      (N s (FastFashion.Structure.stopMin N Sp q T ω) ω : ℝ)) P :=
    fun s hs => (key hN hlam Sp q hT s hs).1
  have h2 : ∀ s ∈ Spᶜ, Integrable (fun ω =>
      (N s (FastFashion.Structure.stopMin N (insert s Sp) q T ω) ω : ℝ)) P :=
    fun s _ => (key hN hlam (insert s Sp) q hT s (Finset.mem_insert_self s Sp)).1
  rw [integral_add (integrable_finset_sum _ h1) (integrable_finset_sum _ h2),
    integral_finsetSum _ h1, integral_finsetSum _ h2, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl (fun s hs => (key hN hlam Sp q hT s hs).2)
  · exact Finset.sum_congr rfl (fun s _ =>
      (key hN hlam (insert s Sp) q hT s (Finset.mem_insert_self s Sp)).2)
