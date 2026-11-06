-- Prove2me | solution 1 for FastFashion.Approx.eq_3_min_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:22:38.477583+00:00
-- url     : https://prove2.me/submissions/011d47fb-9824-4f87-986b-ebd0204e4848

import Mathlib
import Definitions.Def_FastFashion_Structure_Model

open MeasureTheory ProbabilityTheory

namespace FFEq3

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

end FFEq3

open FFEq3 in
theorem solution {S Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ)
    (hN : FastFashion.Structure.IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (T : ℝ) (hT : 0 < T)
    (D : Finset S) (hD : D.Nonempty) (q : S → ℕ) :
    FastFashion.Structure.hA N P T D q ≤ D.inf' hD (fun s => FastFashion.Structure.hA N P T {s} q) := by
  classical
  refine Finset.le_inf' _ _ (fun s hs => ?_)
  unfold FastFashion.Structure.hA
  have hint : Integrable (fun ω => FastFashion.Structure.stopMin N {s} q T ω) P := by
    refine Integrable.of_bound (measurable_stopMin_single hN s q T hT).aestronglyMeasurable T
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [stopMin_eq, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [trunc_nonneg hT.le (tauMin_nonneg N {s} q ω)], trunc_le _⟩
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => ?_)) hint
    (Filter.Eventually.of_forall (fun ω => ?_))
  · simp only [Pi.zero_apply]
    rw [stopMin_eq]
    exact trunc_nonneg hT.le (tauMin_nonneg N D q ω)
  · rw [stopMin_eq, stopMin_eq]
    apply trunc_mono
    unfold FastFashion.Structure.tauMin
    rw [Finset.inf_singleton]
    exact Finset.inf_le hs
