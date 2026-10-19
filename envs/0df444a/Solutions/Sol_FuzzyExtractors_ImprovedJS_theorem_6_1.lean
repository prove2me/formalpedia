-- Prove2me | solution 1 for FuzzyExtractors.ImprovedJS.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T09:47:38.838987+00:00
-- url     : https://prove2.me/submissions/95bc223d-01e2-4db4-904a-2fac4cc557c9

-- Licensed under Apache 2.0. Complete improved Juels–Sudan secure sketch.
import Mathlib
import Definitions.Def_FuzzyExtractors_ImprovedJS_Basic


open Polynomial
open FuzzyExtractors.ImprovedJS

namespace SecureSketchProof

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]

omit [DecidableEq 𝔽] in
 theorem charPoly_monic (w : Finset 𝔽) : (charPoly w).Monic :=
  monic_prod_X_sub_C id w

omit [DecidableEq 𝔽] in
 theorem charPoly_natDegree (w : Finset 𝔽) : (charPoly w).natDegree = w.card := by
  exact natDegree_finsetProd_X_sub_C_eq_card w id

 theorem charPoly_roots (w : Finset 𝔽) : (charPoly w).roots.toFinset = w := by
  simp only [charPoly, roots_prod_X_sub_C, Finset.val_toFinset]

omit [DecidableEq 𝔽] in
 theorem charPoly_eval_zero {w : Finset 𝔽} {x : 𝔽} (hx : x ∈ w) :
    (charPoly w).eval x = 0 := by
  have hr : x ∈ (charPoly w).roots := by
    simpa only [charPoly, roots_prod_X_sub_C, Finset.mem_val] using hx
  exact isRoot_of_mem_roots hr

omit [DecidableEq 𝔽] in
 theorem charPoly_coeff_top {s : ℕ} (w : SDifS 𝔽 s) : (charPoly w.1).coeff s = 1 := by
  have hd : (charPoly w.1).natDegree = s := (charPoly_natDegree w.1).trans w.2
  simpa only [hd] using (charPoly_monic w.1).coeff_natDegree

omit [DecidableEq 𝔽] in
 theorem charPoly_coeff_above {s : ℕ} (w : SDifS 𝔽 s) {d : ℕ} (hd : s < d) :
    (charPoly w.1).coeff d = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  simpa only [charPoly_natDegree, w.2] using hd

end SecureSketchProof


open Polynomial
open FuzzyExtractors.ImprovedJS

namespace SecureSketchProof

variable {𝔽 : Type} [Field 𝔽]

 theorem high_coeff_top {s t : ℕ} (hts : t ≤ s) (c : Fin t → 𝔽) :
    (pHigh s t c).coeff s = 1 := by
  simp only [pHigh, coeff_add, finsetSum_coeff, coeff_X_pow,
    coeff_C_mul_X_pow]
  have hz : ∀ i : Fin t, s ≠ s - 1 - i.val := by
    intro i
    have := i.isLt
    omega
  simp [hz]

 theorem high_coeff_below {s t d : ℕ} (hts : t ≤ s) (hd : d < s)
    (hlo : s - t ≤ d) (c : Fin t → 𝔽) :
    (pHigh s t c).coeff d = c ⟨s - 1 - d, by omega⟩ := by
  let i : Fin t := ⟨s - 1 - d, by omega⟩
  have hi : s - 1 - i.val = d := by dsimp [i]; omega
  simp only [pHigh, coeff_add, finsetSum_coeff, coeff_X_pow, if_neg (ne_of_lt hd),
    zero_add, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp only [hi, ite_true]
    rfl
  · intro j _ hji
    have hne : d ≠ s - 1 - j.val := by
      intro he
      apply hji
      apply Fin.ext
      have := j.isLt
      dsimp [i]
      omega
    simp only [if_neg hne]
  · simp

 theorem high_coeff_above {s t d : ℕ} (hd : s < d)
    (c : Fin t → 𝔽) : (pHigh s t c).coeff d = 0 := by
  simp only [pHigh, coeff_add, finsetSum_coeff, coeff_X_pow, if_neg (ne_of_gt hd),
    zero_add, coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro i _
  have hne : d ≠ s - 1 - i.val := by omega
  simp only [if_neg hne]

 theorem low_degree {s t : ℕ} (hts : t ≤ s) (w : SDifS 𝔽 s) :
    (pHigh s t (sketchCoeffs s t w.1) - charPoly w.1).degree < (s - t : ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro d hd
  rw [coeff_sub]
  rcases lt_trichotomy d s with hlt | heq | hgt
  · rw [high_coeff_below hts hlt hd]
    simp only [sketchCoeffs]
    have he : s - 1 - (s - 1 - d) = d := by omega
    rw [he, sub_self]
  · subst d
    rw [high_coeff_top hts, charPoly_coeff_top, sub_self]
  · rw [high_coeff_above hgt, charPoly_coeff_above w hgt, sub_self]

end SecureSketchProof


namespace SecureSketchProof

variable {α : Type*} [DecidableEq α]

 theorem distance_inter_bound {w w' : Finset α} {s t : ℕ}
    (hw : w.card = s) (hw' : w'.card = s)
    (hd : (symmDiff w w').card ≤ t) : 2 * s - t ≤ 2 * (w ∩ w').card := by
  have hdis : Disjoint (w \ w') (w' \ w) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have hcard : (symmDiff w w').card = (w \ w').card + (w' \ w).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdis]
  have h1 := Finset.card_sdiff_add_card_inter w w'
  have h2 := Finset.card_sdiff_add_card_inter w' w
  rw [Finset.inter_comm w' w] at h2
  omega

 theorem agreement_inter_bound {A B W : Finset α} {s t : ℕ}
    (hW : W.card = s) (hA : A ⊆ W) (hB : B ⊆ W)
    (ha : 2 * s - t ≤ 2 * A.card) (hb : 2 * s - t ≤ 2 * B.card)
    (hts : t ≤ s) : s - t ≤ (A ∩ B).card := by
  have hu : (A ∪ B).card ≤ s := by
    rw [← hW]
    exact Finset.card_le_card (Finset.union_subset hA hB)
  have hh := Finset.card_inter_add_card_union A B
  omega

end SecureSketchProof


open Polynomial
open FuzzyExtractors.ImprovedJS

namespace SecureSketchProof

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]

 theorem step3_unique {s t : ℕ} (hts : t ≤ s) (c : Fin t → 𝔽)
    (w' : SDifS 𝔽 s) {P Q : 𝔽[X]}
    (hP : Step3Cond s t c w'.1 P) (hQ : Step3Cond s t c w'.1 Q) : P = Q := by
  let A := w'.1.filter fun x => P.eval x = (pHigh s t c).eval x
  let B := w'.1.filter fun x => Q.eval x = (pHigh s t c).eval x
  have hc : s - t ≤ (A ∩ B).card :=
    agreement_inter_bound w'.2 (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      hP.2 hQ.2 hts
  have hd : (P - Q).degree < (s - t : ℕ) :=
    lt_of_le_of_lt (degree_sub_le P Q) (max_lt hP.1 hQ.1)
  by_contra hne
  have hpq : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hr : (A ∩ B).val ⊆ (P - Q).roots := by
    intro x hx
    have hx' : x ∈ A ∩ B := hx
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp hx'
    apply (mem_roots hpq).mpr
    change (P - Q).eval x = 0
    rw [eval_sub, (Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2, sub_self]
  have hb := card_le_degree_of_subset_roots hr
  have hn : (P - Q).natDegree < s - t := by
    rw [degree_eq_natDegree hpq] at hd
    exact_mod_cast hd
  omega

 theorem low_candidate {s t : ℕ} (hts : t ≤ s) (w w' : SDifS 𝔽 s)
    (hd : sdifDist w w' ≤ t) :
    Step3Cond s t (sketchCoeffs s t w.1) w'.1
      (pHigh s t (sketchCoeffs s t w.1) - charPoly w.1) := by
  refine ⟨low_degree hts w, ?_⟩
  have hc := distance_inter_bound w.2 w'.2 hd
  have hs : w.1 ∩ w'.1 ⊆ w'.1.filter (fun x =>
      (pHigh s t (sketchCoeffs s t w.1) - charPoly w.1).eval x =
        (pHigh s t (sketchCoeffs s t w.1)).eval x) := by
    intro x hx
    obtain ⟨hxw, hxw'⟩ := Finset.mem_inter.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨hxw', ?_⟩
    rw [eval_sub, charPoly_eval_zero hxw, sub_zero]
  exact hc.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hs))

end SecureSketchProof


open Polynomial
open FuzzyExtractors.ImprovedJS

namespace SecureSketchProof

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽]

 theorem recover_correct {s t : ℕ} (hts : t ≤ s) (w w' : SDifS 𝔽 s)
    (hd : sdifDist w w' ≤ t) :
    recover s t w' (sketchCoeffs s t w.1) = PMF.pure w := by
  classical
  have hex : ∃ P, Step3Cond s t (sketchCoeffs s t w.1) w'.1 P :=
    ⟨_, low_candidate hts w w' hd⟩
  have heq : Classical.choose hex =
      pHigh s t (sketchCoeffs s t w.1) - charPoly w.1 :=
    step3_unique hts _ w' (Classical.choose_spec hex) (low_candidate hts w w' hd)
  have hp : pHigh s t (sketchCoeffs s t w.1) - Classical.choose hex = charPoly w.1 := by
    rw [heq, sub_sub_cancel]
  have hr : (pHigh s t (sketchCoeffs s t w.1) - Classical.choose hex).roots.toFinset = w.1 := by
    rw [hp, charPoly_roots]
  have hc : (pHigh s t (sketchCoeffs s t w.1) - Classical.choose hex).roots.toFinset.card = s :=
    (congrArg Finset.card hr).trans w.2
  simp only [recover, dif_pos hex, dif_pos hc]
  congr 1
  exact Subtype.ext hr

 theorem sketch_correct (s t : ℕ) (hts : t ≤ s) :
    FuzzyExtractors.Hamming.SketchCorrect (sdifDist (𝓤 := 𝔽) (s := s)) t
      (sketch s t) (recover s t) := by
  intro w w' hd c hc
  have heq : c = sketchCoeffs s t w.1 := by
    simpa only [sketch, PMF.support_pure, Set.mem_singleton_iff] using hc
  subst c
  exact recover_correct hts w w' hd

end SecureSketchProof


open scoped ENNReal

namespace SecureSketchProof

noncomputable def guessingMass {A I : Type*} (W : PMF (A × I)) : ℝ≥0∞ :=
  ∑' i, ⨆ a, W (a, i)

theorem guessingMass_le_one {A I : Type*} (W : PMF (A × I)) :
    guessingMass W ≤ 1 := by
  calc
    guessingMass W ≤ ∑' i, ∑' a, W (a, i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact iSup_le fun a => ENNReal.le_tsum a
    _ = ∑' p : A × I, W p := by rw [ENNReal.tsum_comm, ENNReal.tsum_prod']
    _ = 1 := W.tsum_coe

theorem guessingMass_pos {A I : Type*} (W : PMF (A × I)) :
    0 < guessingMass W := by
  obtain ⟨⟨a, i⟩, h⟩ := W.support_nonempty
  have hp : 0 < W (a, i) := (W.apply_pos_iff _).2 h
  exact hp.trans_le ((le_iSup (fun a => W (a, i)) a).trans (ENNReal.le_tsum i))

theorem guessingMass_ne_top {A I : Type*} (W : PMF (A × I)) :
    guessingMass W ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (guessingMass_le_one W)

theorem guessingMass_toReal_pos {A I : Type*} (W : PMF (A × I)) :
    0 < (guessingMass W).toReal :=
  ENNReal.toReal_pos (ne_of_gt (guessingMass_pos W)) (guessingMass_ne_top W)

end SecureSketchProof


open scoped ENNReal
open FuzzyExtractors.Hamming

namespace SecureSketchProof

variable {A S I : Type}
open Classical

theorem disclosure_apply (σ : A → S) (W : PMF (A × I)) (a : A) (s : S) (i : I) :
    withSketchAux (fun a => PMF.pure (σ a)) W (a, (s, i)) =
      if s = σ a then W (a, i) else 0 := by
  classical
  simp only [withSketchAux, PMF.pure_map, PMF.bind_apply, PMF.pure_apply]
  rw [tsum_eq_single (a, i)]
  · simp
  · intro p hp
    have h : (a, (s, i)) ≠ (p.1, (σ p.1, p.2)) := by
      intro he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg (fun z : A × (S × I) => z.2.2) he
      exact hp (Prod.ext h1.symm h2.symm)
    simp [h]

theorem guessingMass_disclosure_le [Fintype S] (σ : A → S) (W : PMF (A × I)) :
    guessingMass (withSketchAux (fun a => PMF.pure (σ a)) W) ≤
      (Fintype.card S : ℝ≥0∞) * guessingMass W := by
  classical
  unfold guessingMass
  rw [ENNReal.tsum_prod']
  calc
    (∑' s : S, ∑' i : I, ⨆ a : A,
      withSketchAux (fun a => PMF.pure (σ a)) W (a, (s, i))) ≤
        ∑' _s : S, ∑' i : I, ⨆ a : A, W (a, i) := by
      apply ENNReal.tsum_le_tsum
      intro s
      apply ENNReal.tsum_le_tsum
      intro i
      apply iSup_le
      intro a
      rw [disclosure_apply]
      split_ifs
      · exact le_iSup (fun a => W (a, i)) a
      · exact bot_le
    _ = _ := by simp [tsum_fintype, nsmul_eq_mul]

end SecureSketchProof


open scoped ENNReal
open FuzzyExtractors.Hamming

namespace SecureSketchProof

theorem avgMinEntropy_disclosure {A S I : Type} [Fintype S] [Nonempty S]
    (σ : A → S) (W : PMF (A × I)) :
    avgMinEntropy W - Real.logb 2 (Fintype.card S) ≤
      avgMinEntropy (withSketchAux (fun a => PMF.pure (σ a)) W) := by
  have hc : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hw := guessingMass_toReal_pos W
  have hv := guessingMass_toReal_pos (withSketchAux (fun a => PMF.pure (σ a)) W)
  have hbound := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) (guessingMass_ne_top W))
    (guessingMass_disclosure_le σ W)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hbound
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hv hbound
  rw [Real.logb_mul (ne_of_gt hc) (ne_of_gt hw)] at hlog
  change -Real.logb 2 (guessingMass W).toReal - Real.logb 2 (Fintype.card S) ≤
    -Real.logb 2 (guessingMass (withSketchAux (fun a => PMF.pure (σ a)) W)).toReal
  linarith

theorem sketch_entropy_bound {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (s t : ℕ) (m : ℝ) (I : Type)
    (W : PMF (FuzzyExtractors.ImprovedJS.SDifS 𝔽 s × I))
    (hm : m ≤ avgMinEntropy W) :
    m - t * Real.logb 2 (Fintype.card 𝔽) ≤
      avgMinEntropy (withSketchAux (FuzzyExtractors.ImprovedJS.sketch s t) W) := by
  have h := avgMinEntropy_disclosure
    (fun w : FuzzyExtractors.ImprovedJS.SDifS 𝔽 s =>
      FuzzyExtractors.ImprovedJS.sketchCoeffs s t w.1) W
  have hc : (Fintype.card (Fin t → 𝔽) : ℝ) = (Fintype.card 𝔽 : ℝ) ^ t := by
    simp
  rw [hc, Real.logb_pow] at h
  exact (sub_le_sub_right hm _).trans h

end SecureSketchProof


namespace SecureSketchProof
open FuzzyExtractors.ImprovedJS

theorem full_secure_sketch {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (s t : ℕ) (hts : t ≤ s) (m : ℝ) :
    FuzzyExtractors.Hamming.IsAvgSecureSketch (sdifDist (𝓤 := 𝔽) (s := s)) m
      (m - t * Real.logb 2 (Fintype.card 𝔽)) t (sketch s t) (recover s t) := by
  constructor
  · exact sketch_correct s t hts
  · intro I W hm
    exact sketch_entropy_bound s t m I W hm

end SecureSketchProof


open FuzzyExtractors.ImprovedJS

namespace FuzzyExtractors.ImprovedJS

/-- Theorem 6.1 (Analysis of Improved JS), p. 22: over a finite field 𝔽 with n elements and for
t ≤ s, Construction 5 is an average-case (SDif_s(𝔽), m, m − t log n, t)-secure sketch, for every m. -/
theorem theorem_6_1 {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (s t : ℕ) (hts : t ≤ s)
    (m : ℝ) :
    FuzzyExtractors.Hamming.IsAvgSecureSketch (sdifDist (𝓤 := 𝔽) (s := s)) m
      (m - t * Real.logb 2 (Fintype.card 𝔽)) t (sketch s t) (recover s t) := by
  exact SecureSketchProof.full_secure_sketch s t hts m

end FuzzyExtractors.ImprovedJS

open FuzzyExtractors.ImprovedJS

theorem solution {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (s t : ℕ) (hts : t ≤ s)
    (m : ℝ) :
    FuzzyExtractors.Hamming.IsAvgSecureSketch (sdifDist (𝓤 := 𝔽) (s := s)) m
      (m - t * Real.logb 2 (Fintype.card 𝔽)) t (sketch s t) (recover s t) := FuzzyExtractors.ImprovedJS.theorem_6_1 s t hts m
