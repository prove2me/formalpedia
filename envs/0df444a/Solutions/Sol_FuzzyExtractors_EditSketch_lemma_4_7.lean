-- Prove2me | solution 1 for FuzzyExtractors.EditSketch.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:28:11.081457+00:00
-- url     : https://prove2.me/submissions/0edcb329-d5aa-408b-8c62-038808a3c915

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic


open FuzzyExtractors.EditSketch FuzzyExtractors.Hamming

theorem embedding_correct {M₁ M₂ G S : Type} (dis₁ : M₁ → M₁ → ℕ)
    (dis₂ : M₂ → M₂ → ℕ) (t₁ t₂ : ℕ) (lam : ℝ) (f : M₁ → M₂) (g : M₁ → G)
    (SS : M₂ → PMF S) (Rec : M₂ → S → PMF M₂)
    (hf : IsEmbeddingWithRecovery dis₁ dis₂ t₁ t₂ lam f g)
    (hc : SketchCorrect dis₂ t₂ SS Rec) :
    SketchCorrect dis₁ t₁ (embedSketch f g SS) (embedRec f g Rec) := by
  classical
  intro w w' hd sr hsr
  obtain ⟨s, hs, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hsr
  change (s, g w) = sr at he
  subst sr
  have hr := hc (f w) (f w') (hf.1 w w' hd) s hs
  unfold embedRec
  rw [hr, PMF.pure_map]
  have hex : ∃ a, f a = f w ∧ g a = g w := ⟨w,rfl,rfl⟩
  simp only [dif_pos hex]
  congr 1
  apply hf.2.2
  exact Prod.ext hex.choose_spec.1 hex.choose_spec.2



open scoped ENNReal
open Classical

namespace Paper40

noncomputable def guess {A I : Type} (P : PMF (A × I)) : ℝ≥0∞ :=
  ∑' i, ⨆ a, P (a,i)

noncomputable def reveal {A B G I : Type} (f : A → B) (g : A → G) (P : PMF (A × I)) :
    PMF (B × (G × I)) := P.map fun p => (f p.1,(g p.1,p.2))

theorem reveal_apply {A B G I : Type} (f : A → B) (g : A → G)
    (hinj : Function.Injective fun a => (f a,g a)) (P : PMF (A × I))
    (b : B) (r : G) (i : I) :
    reveal f g P (b,(r,i)) =
      if h : ∃ a, f a = b ∧ g a = r then P (h.choose,i) else 0 := by
  classical
  unfold reveal
  rw [PMF.map_apply]
  split
  next h =>
    rw [tsum_eq_single (h.choose,i)]
    · simp [h.choose_spec.1,h.choose_spec.2]
    · intro p hp
      split_ifs with he
      · have he' : f p.1 = b ∧ g p.1 = r ∧ p.2 = i := by
          simpa [Prod.mk.injEq, eq_comm, and_assoc] using he
        have ha : p.1 = h.choose := hinj (Prod.ext
          (he'.1.trans h.choose_spec.1.symm) (he'.2.1.trans h.choose_spec.2.symm))
        exact (hp (Prod.ext ha he'.2.2)).elim
      · rfl
  next h =>
    apply ENNReal.tsum_eq_zero.mpr
    intro p
    split_ifs with he
    · apply (h ?_).elim
      have he' : f p.1 = b ∧ g p.1 = r ∧ p.2 = i := by
        simpa [Prod.mk.injEq, eq_comm, and_assoc] using he
      exact ⟨p.1,he'.1,he'.2.1⟩
    · rfl

theorem reveal_guess_le {A B G I : Type} (f : A → B) (g : A → G)
    (hinj : Function.Injective fun a => (f a,g a)) (T : Finset G)
    (hT : ∀ a, g a ∈ T) (P : PMF (A × I)) :
    guess (reveal f g P) ≤ T.card * guess P := by
  classical
  have hbound (r : G) (i : I) :
      (⨆ b, reveal f g P (b,(r,i))) ≤
        if r ∈ T then ⨆ a, P (a,i) else 0 := by
    apply iSup_le
    intro b
    rw [reveal_apply f g hinj]
    split
    next h =>
      have hr : r ∈ T := h.choose_spec.2 ▸ hT h.choose
      simp only [hr,if_true]
      exact le_iSup (fun a => P (a,i)) h.choose
    next h => exact zero_le
  unfold guess
  change (∑' p : G × I, ⨆ b, reveal f g P (b,(p.1,p.2))) ≤ _
  rw [ENNReal.tsum_prod (f := fun r i => ⨆ b, reveal f g P (b,(r,i)))]
  calc
    (∑' r, ∑' i, ⨆ b, reveal f g P (b,(r,i))) ≤
        ∑' r, ∑' i, if r ∈ T then ⨆ a, P (a,i) else 0 :=
      ENNReal.tsum_le_tsum fun r => ENNReal.tsum_le_tsum (hbound r)
    _ = T.card * ∑' i, ⨆ a, P (a,i) := by
      have he (r : G) : (∑' i, if r ∈ T then ⨆ a, P (a,i) else 0) =
          if r ∈ T then ∑' i, ⨆ a, P (a,i) else 0 := by
        by_cases hr : r ∈ T <;> simp [hr]
      simp_rw [he]
      rw [tsum_eq_sum (s := T)]
      · simp
      · intro r hr; simp [hr]

end Paper40


open scoped ENNReal
open FuzzyExtractors.Hamming
namespace Paper40

theorem guess_le_one {A I : Type} (P : PMF (A × I)) : guess P ≤ 1 := by
  calc
    guess P ≤ ∑' i, ∑' a, P (a,i) := ENNReal.tsum_le_tsum fun i =>
      iSup_le fun a => ENNReal.le_tsum a
    _ = 1 := by rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod', P.tsum_coe]

theorem guess_pos {A I : Type} (P : PMF (A × I)) : 0 < guess P := by
  obtain ⟨⟨a,i⟩,h⟩ := P.support_nonempty
  exact (pos_iff_ne_zero.mpr h).trans_le
    ((le_iSup (fun a => P (a,i)) a).trans (ENNReal.le_tsum i))

theorem entropy_iff {A I : Type} (P : PMF (A × I)) (m : ℝ) :
    m ≤ avgMinEntropy P ↔ guess P ≤ ENNReal.ofReal ((2 : ℝ)^(-m)) := by
  have hf : guess P ≠ ∞ := ne_of_lt (lt_of_le_of_lt (guess_le_one P) ENNReal.one_lt_top)
  have hp : 0 < (guess P).toReal := ENNReal.toReal_pos (ne_of_gt (guess_pos P)) hf
  have he : m ≤ avgMinEntropy P ↔ Real.logb 2 (guess P).toReal ≤ -m := by
    unfold avgMinEntropy guess
    constructor <;> intro h <;> linarith
  rw [he, Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hp]
  constructor
  · intro h
    simpa [ENNReal.ofReal_toReal hf] using ENNReal.ofReal_le_ofReal h
  · intro h
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
      (ENNReal.toReal_ofReal (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)))

theorem entropy_reveal {A B G I : Type} (f : A → B) (g : A → G)
    (hinj : Function.Injective fun a => (f a,g a)) (T : Finset G)
    (hT : ∀ a, g a ∈ T) (lam m : ℝ) (hcard : (T.card : ℝ) ≤ (2 : ℝ)^lam)
    (P : PMF (A × I)) (hm : m ≤ avgMinEntropy P) :
    m-lam ≤ avgMinEntropy (reveal f g P) := by
  apply (entropy_iff _ _).mpr
  calc
    guess (reveal f g P) ≤ T.card * guess P := reveal_guess_le f g hinj T hT P
    _ ≤ ENNReal.ofReal ((2 : ℝ)^lam) * ENNReal.ofReal ((2 : ℝ)^(-m)) := by
      apply mul_le_mul'
      · simpa using ENNReal.ofReal_le_ofReal hcard
      · exact (entropy_iff P m).mp hm
    _ = ENNReal.ofReal ((2 : ℝ)^(-(m-lam))) := by
      rw [← ENNReal.ofReal_mul (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

end Paper40


open scoped ENNReal
open Classical
open FuzzyExtractors.EditSketch FuzzyExtractors.Hamming

namespace Paper40

theorem reveal_image {A B G I : Type} (f : A → B) (g : A → G)
    (hinj : Function.Injective fun a => (f a,g a)) (P : PMF (A × I))
    (a : A) (i : I) : reveal f g P (f a,(g a,i)) = P (a,i) := by
  rw [reveal_apply f g hinj]
  split
  next h =>
    congr 1
    congr 1
    exact hinj (Prod.ext h.choose_spec.1 h.choose_spec.2)
  next h => exact (h ⟨a,rfl,rfl⟩).elim

theorem sketchAux_apply {A S I : Type} (SS : A → PMF S) (P : PMF (A × I))
    (a : A) (s : S) (i : I) :
    withSketchAux SS P (a,(s,i)) = P (a,i) * SS a s := by
  unfold withSketchAux
  rw [PMF.bind_apply]
  have hm (p : A × I) : ((SS p.1).map fun s => (p.1,(s,p.2))) (a,(s,i)) =
      if p = (a,i) then SS a s else 0 := by
    by_cases hp : p = (a,i)
    · subst p; simp [PMF.map_apply]
    · have hp' : ¬ (a = p.1 ∧ i = p.2) := by
        intro h; apply hp; exact Prod.ext h.1.symm h.2.symm
      simp only [PMF.map_apply, Prod.mk.injEq]
      have hx : ∀ x, (if a = p.1 ∧ s = x ∧ i = p.2 then SS p.1 x else 0) = 0 := by
        intro x; split_ifs with h
        · exact (hp' ⟨h.1,h.2.2⟩).elim
        · rfl
      simp [hx,hp]
  simp_rw [hm]
  rw [tsum_eq_single (a,i)]
  · simp
  · intro p hp; simp [hp]

theorem embedSketch_apply {A B G S : Type} (f : A → B) (g : A → G)
    (SS : B → PMF S) (a : A) (s : S) (r : G) :
    embedSketch f g SS a (s,r) = if r = g a then SS (f a) s else 0 := by
  unfold embedSketch
  by_cases hr : r = g a
  · subst r; simp [PMF.map_apply]
  · simp [PMF.map_apply, Prod.mk.injEq, hr]

theorem embed_output_guess {A B G S I : Type} (f : A → B) (g : A → G)
    (hinj : Function.Injective fun a => (f a,g a)) (SS : B → PMF S) (P : PMF (A × I)) :
    guess (withSketchAux (embedSketch f g SS) P) ≤
      guess (withSketchAux SS (reveal f g P)) := by
  have hb (s : S) (r : G) (i : I) :
      (⨆ a, withSketchAux (embedSketch f g SS) P (a,((s,r),i))) ≤
        ⨆ b, withSketchAux SS (reveal f g P) (b,(s,(r,i))) := by
    apply iSup_le
    intro a
    rw [sketchAux_apply,embedSketch_apply]
    by_cases hr : r = g a
    · subst r
      simp only [if_true]
      have he : withSketchAux SS (reveal f g P) (f a,(s,(g a,i))) =
          P (a,i)*SS (f a) s := by rw [sketchAux_apply,reveal_image f g hinj]
      rw [← he]
      exact le_iSup (fun b : B => withSketchAux SS (reveal f g P) (b,(s,(g a,i)))) (f a)
    · simp [hr]
  unfold guess
  simp only [ENNReal.tsum_prod']
  apply ENNReal.tsum_le_tsum
  intro s
  apply ENNReal.tsum_le_tsum
  intro r
  exact ENNReal.tsum_le_tsum (hb s r)

end Paper40


open FuzzyExtractors.EditSketch FuzzyExtractors.Hamming Paper40

theorem solution {M₁ M₂ G S : Type} (dis₁ : M₁ → M₁ → ℕ) (dis₂ : M₂ → M₂ → ℕ)
    (t₁ t₂ : ℕ) (lam m₁ m₂' : ℝ) (f : M₁ → M₂) (g : M₁ → G)
    (SS : M₂ → PMF S) (Rec : M₂ → S → PMF M₂)
    (hf : IsEmbeddingWithRecovery dis₁ dis₂ t₁ t₂ lam f g)
    (hSS : FuzzyExtractors.Hamming.IsAvgSecureSketch dis₂ (m₁ - lam) m₂' t₂ SS Rec) :
    FuzzyExtractors.Hamming.IsAvgSecureSketch dis₁ m₁ m₂' t₁ (embedSketch f g SS) (embedRec f g Rec) := by
  refine ⟨embedding_correct dis₁ dis₂ t₁ t₂ lam f g SS Rec hf hSS.1, ?_⟩
  intro I WI hm
  obtain ⟨T,hcard,hT⟩ := hf.2.1
  have hi := entropy_reveal f g hf.2.2 T hT lam m₁ hcard WI hm
  have ho := hSS.2 (G × I) (reveal f g WI) hi
  apply (entropy_iff _ _).mpr
  exact (embed_output_guess f g hf.2.2 SS WI).trans ((entropy_iff _ _).mp ho)


#print axioms solution
