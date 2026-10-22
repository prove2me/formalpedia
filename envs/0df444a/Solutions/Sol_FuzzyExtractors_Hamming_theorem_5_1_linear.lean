-- Prove2me | solution 1 for FuzzyExtractors.Hamming.theorem_5_1_linear
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:08:33.822502+00:00
-- url     : https://prove2.me/submissions/3ecd4cdd-8200-4a9f-9c4a-86f28106c6db

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
set_option autoImplicit false
open FuzzyExtractors.Hamming
open scoped ENNReal

lemma ss_withSketchAux_apply {M S ι : Type} (SS : M → PMF S) (WI : PMF (M × ι))
    (w : M) (s : S) (i : ι) :
    withSketchAux SS WI (w, (s, i)) = WI (w, i) * SS w s := by
  unfold withSketchAux
  rw [PMF.bind_apply, tsum_eq_single (w, i)]
  · rw [PMF.map_apply, tsum_eq_single s]
    · simp
    · intro s' hs'
      have : ¬ ((w, (s, i)) = (w, (s', i))) := by
        intro h
        have h' : s = s' := by simpa using h
        exact hs' h'.symm
      simp [this]
  · intro p hp
    rw [PMF.map_apply]
    have : ∀ s', ¬ ((w, (s, i)) = (p.1, (s', p.2))) := by
      intro s' h
      apply hp
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1.symm h.2.2.symm
    simp [this]

theorem ss_lemma31 {M S : Type} (dis : M → M → ℕ) (t : ℕ)
    (SS : M → PMF S) (Rec : M → S → PMF M) (hcorr : SketchCorrect dis t SS Rec) (lam : ℝ)
    (hrange : ∃ T : Finset S, (T.card : ℝ) ≤ (2 : ℝ) ^ lam ∧ ∀ w, (SS w).support ⊆ (T : Set S)) :
    ∀ m : ℝ, IsAvgSecureSketch dis m (m - lam) t SS Rec := by
  intro m
  refine ⟨hcorr, ?_⟩
  intro ι WI hm
  obtain ⟨T, hTcard, hT⟩ := hrange
  classical
  set A : ℝ≥0∞ := ∑' i : ι, ⨆ w : M, WI (w, i) with hA
  set A' : ℝ≥0∞ := ∑' x : S × ι, ⨆ w : M, withSketchAux SS WI (w, x) with hA'
  have hAeq : avgMinEntropy WI = -Real.logb 2 A.toReal := rfl
  have hA'eq : avgMinEntropy (withSketchAux SS WI) = -Real.logb 2 A'.toReal := rfl
  -- A ≤ 1
  have hA1 : A ≤ 1 := by
    calc A ≤ ∑' i : ι, ∑' w : M, WI (w, i) := by
          refine ENNReal.tsum_le_tsum fun i => iSup_le fun w => ?_
          exact ENNReal.le_tsum (f := fun w => WI (w, i)) w
      _ = ∑' p : M × ι, WI p := by
          rw [ENNReal.tsum_comm]
          exact (ENNReal.tsum_prod (f := fun w i => WI (w, i))).symm
      _ = 1 := WI.tsum_coe
  obtain ⟨⟨w0, i0⟩, hp0⟩ := WI.support_nonempty
  have hp0' : WI (w0, i0) ≠ 0 := hp0
  obtain ⟨s0, hs0⟩ := (SS w0).support_nonempty
  have hs0' : SS w0 s0 ≠ 0 := hs0
  have hApos : 0 < A := by
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr hp0') ?_
    refine le_trans (le_iSup (fun w => WI (w, i0)) w0) ?_
    exact ENNReal.le_tsum i0
  have hA'pos : 0 < A' := by
    have : withSketchAux SS WI (w0, (s0, i0)) ≠ 0 := by
      rw [ss_withSketchAux_apply]; exact mul_ne_zero hp0' hs0'
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr this) ?_
    refine le_trans (le_iSup (fun w => withSketchAux SS WI (w, (s0, i0))) w0) ?_
    exact ENNReal.le_tsum (f := fun x : S × ι => ⨆ w : M, withSketchAux SS WI (w, x)) (s0, i0)
  -- main bound
  have hbound : A' ≤ (T.card : ℝ≥0∞) * A := by
    have h1 : A' = ∑' s : S, ∑' i : ι, ⨆ w : M, WI (w, i) * SS w s := by
      rw [hA']
      refine Eq.trans (ENNReal.tsum_prod (f := fun s i => ⨆ w : M, withSketchAux SS WI (w, (s, i)))) ?_
      refine tsum_congr fun s => tsum_congr fun i => ?_
      simp_rw [ss_withSketchAux_apply]
    rw [h1]
    have h2 : ∀ s i, (⨆ w : M, WI (w, i) * SS w s) ≤ (if s ∈ T then 1 else 0) * ⨆ w : M, WI (w, i) := by
      intro s i
      refine iSup_le fun w => ?_
      by_cases hs : s ∈ T
      · simp only [hs, if_true, one_mul]
        calc WI (w, i) * SS w s ≤ WI (w, i) * 1 :=
              mul_le_mul' le_rfl (PMF.coe_le_one _ _)
          _ ≤ _ := by rw [mul_one]; exact le_iSup (fun w => WI (w, i)) w
      · have : SS w s = 0 := by
          by_contra h
          exact hs (hT w ((PMF.mem_support_iff _ _).mpr h))
        simp [hs, this]
    calc ∑' s : S, ∑' i : ι, ⨆ w : M, WI (w, i) * SS w s
        ≤ ∑' s : S, ∑' i : ι, (if s ∈ T then 1 else 0) * ⨆ w : M, WI (w, i) :=
          ENNReal.tsum_le_tsum fun s => ENNReal.tsum_le_tsum fun i => h2 s i
      _ = ∑' s : S, (if s ∈ T then 1 else 0) * A := by
          refine tsum_congr fun s => ?_
          rw [ENNReal.tsum_mul_left]
      _ = (T.card : ℝ≥0∞) * A := by
          rw [ENNReal.tsum_mul_right]
          congr 1
          rw [tsum_eq_sum (s := T)]
          · simp
          · intro s hs; simp [hs]
  -- pass to reals
  have hAne : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hA1
  have hAreal_pos : 0 < A.toReal := ENNReal.toReal_pos hApos.ne' hAne
  have hA'ne : A' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hAne) hbound
  have hA'real_pos : 0 < A'.toReal := ENNReal.toReal_pos hA'pos.ne' hA'ne
  have hreal : A'.toReal ≤ (T.card : ℝ) * A.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hAne) hbound
    simpa using this
  rw [hAeq] at hm
  have hAle : A.toReal ≤ (2:ℝ) ^ (-m) := by
    have : Real.logb 2 A.toReal ≤ -m := by linarith
    exact (Real.logb_le_iff_le_rpow (by norm_num) hAreal_pos).mp this
  have hfin : A'.toReal ≤ (2:ℝ) ^ (lam - m) := by
    calc A'.toReal ≤ (T.card : ℝ) * A.toReal := hreal
      _ ≤ (2:ℝ) ^ lam * (2:ℝ) ^ (-m) :=
          mul_le_mul hTcard hAle hAreal_pos.le (by positivity)
      _ = (2:ℝ) ^ (lam - m) := by
          rw [← Real.rpow_add (by norm_num)]; ring_nf
  have : Real.logb 2 A'.toReal ≤ lam - m :=
    (Real.logb_le_iff_le_rpow (by norm_num) hA'real_pos).mpr hfin
  rw [hA'eq]
  linarith


lemma ss_hn_sub {n : ℕ} {F : Type} [AddCommGroup F] [DecidableEq F] (x y : Fin n → F) :
    hammingNorm (x - y) ≤ hammingNorm x + hammingNorm y := by
  have h1 : hammingNorm (x - y) = hammingDist y x := by
    rw [hammingDist_eq_hammingNorm, neg_add_eq_sub]
  rw [h1]
  have := hammingDist_triangle y 0 x
  rw [hammingDist_zero_right, hammingDist_zero_left] at this
  omega

lemma ss_hn_dist {n : ℕ} {F : Type} [AddCommGroup F] [DecidableEq F] (w w' : Fin n → F) :
    hammingNorm (w' - w) = hammingDist w w' := by
  rw [hammingDist_eq_hammingNorm, neg_add_eq_sub]

theorem solution {F : Type} [Field F] [Fintype F] [DecidableEq F] {n k t : ℕ}
    (C : Submodule F (Fin n → F)) (hk : Module.finrank F C = k)
    (syn : (Fin n → F) →ₗ[F] (Fin (n - k) → F)) (hsyn : LinearMap.ker syn = C)
    (hdist : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → 2 * t + 1 ≤ hammingDist c c') :
    ∀ m : ℝ, IsAvgSecureSketch hammingDist m
      (m - ((n : ℝ) - k) * Real.logb 2 (Fintype.card F)) t
      (syndromeSS syn) (syndromeRec syn t) := by
  have hkn : k ≤ n := by
    rw [← hk]
    calc Module.finrank F C ≤ Module.finrank F (Fin n → F) := Submodule.finrank_le C
      _ = n := by simp
  -- correctness
  have hcorr : SketchCorrect hammingDist t (syndromeSS syn) (syndromeRec syn t) := by
    intro w w' hww s hs
    have hs' : s = syn w := by simpa [syndromeSS] using hs
    subst hs'
    unfold syndromeRec
    have hex : ∃ e : Fin n → F, hammingNorm e ≤ t ∧ syn e = syn w' - syn w :=
      ⟨w' - w, by
        rw [ss_hn_dist]; exact hww, by simp⟩
    rw [dif_pos hex]
    obtain ⟨he1, he2⟩ := hex.choose_spec
    set e := hex.choose with he
    have hd : e - (w' - w) ∈ C := by
      rw [← hsyn, LinearMap.mem_ker, map_sub, he2]; simp
    have hzero : e - (w' - w) = 0 := by
      by_contra hne
      have h0 : (0 : Fin n → F) ∈ C := C.zero_mem
      have h1 := hdist _ hd 0 h0 hne
      have h2 : hammingDist (e - (w' - w)) 0 ≤ 2 * t := by
        have htri := hammingDist_triangle (e - (w' - w)) 0 0
        calc hammingDist (e - (w' - w)) 0 = hammingNorm (e - (w' - w)) :=
              hammingDist_zero_right _
          _ ≤ hammingNorm e + hammingNorm (w' - w) := ss_hn_sub _ _
          _ ≤ t + t := by
              have : hammingNorm (w' - w) ≤ t := by
                rw [ss_hn_dist]; exact hww
              omega
          _ = 2 * t := by ring
      omega
    have : e = w' - w := sub_eq_zero.mp hzero
    rw [this]
    simp
  intro m
  have hrange : ∃ T : Finset (Fin (n - k) → F),
      (T.card : ℝ) ≤ (2 : ℝ) ^ (((n : ℝ) - k) * Real.logb 2 (Fintype.card F)) ∧
        ∀ w, (syndromeSS syn w).support ⊆ (T : Set (Fin (n - k) → F)) := by
    refine ⟨Finset.univ, ?_, fun w => by intro x _; simp⟩
    have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
    have hnk : ((n : ℝ) - k) = ((n - k : ℕ) : ℝ) := by rw [Nat.cast_sub hkn]
    rw [hnk, mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hq,
      Real.rpow_natCast]
    simp
  exact ss_lemma31 hammingDist t (syndromeSS syn) (syndromeRec syn t) hcorr _ hrange m
