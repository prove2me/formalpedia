-- Prove2me | solution 1 for FracTruthSched.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:44:54.54422+00:00
-- url     : https://prove2.me/submissions/52a88e20-5c66-42d5-aaf2-163eb6a39c1f

import Mathlib
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_IsGraphInput
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_IsClassSymmetric
import Definitions.Def_FracTruthSched_rootStarInput
import Definitions.Def_FracTruthSched_classSet
import Definitions.Def_FracTruthSched_IsAdditiveOn
import Definitions.Def_FracTruthSched_IsSymmetricOn
import Theorems.Thm_FracTruthSched_lemma_2b
import Theorems.Thm_FracTruthSched_lemma_4

section
set_option autoImplicit false

namespace FracTruthSched.Dev.L5
open FracTruthSched

variable {n ℓ : ℕ}

/-- the star input with root values `a` and opposing values `s` -/
def I (i : Fin n) (a s : CoreTask n ℓ → ℝ) : Fin n → CoreTask n ℓ → ℝ :=
  fun u e => if e.isLeft ∧ incident i e ∧ incident u e then (if u = i then a e else s e) else 0

noncomputable def W (M : FracMech n (CoreTask n ℓ)) (i : Fin n) (a s : CoreTask n ℓ → ℝ) : ℝ :=
  disutility M (I i a s) i

lemma I_graph (i : Fin n) (a s : CoreTask n ℓ → ℝ) (ha : ∀ d, 0 ≤ a d) (hs : ∀ d, 0 ≤ s d) :
    IsGraphInput (I i a s) := by
  intro u e
  constructor
  · unfold I
    split_ifs
    · exact ha _
    · exact hs _
    · exact le_refl _
  · intro h
    unfold I
    rw [if_neg (fun hc => h hc.2.2)]

lemma sum_diff (a b y : CoreTask n ℓ → ℝ) (e : CoreTask n ℓ) (h : ∀ k, k ≠ e → b k = a k) :
    ∑ k, b k * y k - ∑ k, a k * y k = (b e - a e) * y e := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single e]
  · ring
  · intro k _ hk; rw [h k hk]; ring
  · simp

lemma sandwich (M : FracMech n (CoreTask n ℓ)) (htruth : IsTruthfulOn IsGraphInput M)
    (j : Fin n) (t : Fin n → CoreTask n ℓ → ℝ) (b : CoreTask n ℓ → ℝ) (e : CoreTask n ℓ)
    (ht : IsGraphInput t) (ht2 : IsGraphInput (Function.update t j b))
    (hb : ∀ k, k ≠ e → b k = t j k) :
    (b e - t j e) * M.x (Function.update t j b) j e ≤
      disutility M (Function.update t j b) j - disutility M t j ∧
    disutility M (Function.update t j b) j - disutility M t j ≤
      (b e - t j e) * M.x t j e := by
  have h1 := htruth t ht j b ht2
  have e2 : Function.update (Function.update t j b) j (t j) = t := by
    rw [Function.update_idem, Function.update_eq_self]
  have h2 := htruth (Function.update t j b) ht2 j (t j) (by rw [e2]; exact ht)
  rw [e2] at h2
  have e3 : Function.update t j b j = b := by simp
  rw [e3] at h2
  have e4 : Function.update (Function.update t j b) j 0 = Function.update t j 0 := by
    rw [Function.update_idem]
  have s1 := sum_diff (t j) b (M.x (Function.update t j b) j) e hb
  have s2 := sum_diff (t j) b (M.x t j) e hb
  unfold disutility
  rw [e3, e4]
  constructor <;> linarith

lemma I_update (i : Fin n) (a b s : CoreTask n ℓ → ℝ) :
    I i b s = Function.update (I i a s) i (I i b s i) := by
  funext u e
  by_cases hu : u = i
  · subst hu; simp
  · rw [Function.update_of_ne hu]
    unfold I
    simp [hu]

lemma step_lip (M : FracMech n (CoreTask n ℓ)) (hfeas : IsFeasibleOn IsGraphInput M)
    (htruth : IsTruthfulOn IsGraphInput M) (i : Fin n) (a b s : CoreTask n ℓ → ℝ)
    (e : CoreTask n ℓ) (ha : ∀ d, 0 ≤ a d) (hb : ∀ d, 0 ≤ b d) (hs : ∀ d, 0 ≤ s d)
    (hab : ∀ d, d ≠ e → b d = a d) :
    |W M i b s - W M i a s| ≤ |b e - a e| := by
  have hga := I_graph i a s ha hs
  have hgb := I_graph i b s hb hs
  have hsw := sandwich M htruth i (I i a s) (I i b s i) e hga
    (by rw [← I_update i a b s]; exact hgb)
    (by
      intro k hk
      unfold I
      simp only [and_self, if_true]
      by_cases hc : k.isLeft ∧ incident i k
      · simp [hc, hab k hk]
      · simp [hc])
  rw [← I_update i a b s] at hsw
  have hx1 := hfeas _ hga
  have hx2 := hfeas _ hgb
  set d := I i b s i e - I i a s i e with hd
  have hdd : |d| ≤ |b e - a e| := by
    rw [hd]
    unfold I
    simp only [and_self, if_true]
    by_cases hc : e.isLeft ∧ incident i e
    · simp [hc]
    · simp [hc]
  have h1 : |d * M.x (I i a s) i e| ≤ |d| := by
    rw [abs_mul, abs_of_nonneg (hx1.1 i e).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (hx1.1 i e).2
  have h2 : |d * M.x (I i b s) i e| ≤ |d| := by
    rw [abs_mul, abs_of_nonneg (hx2.1 i e).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (hx2.1 i e).2
  have := abs_le.mp h1
  have := abs_le.mp h2
  unfold W
  rw [abs_le]
  constructor <;> nlinarith [hsw.1, hsw.2, abs_le.mp h1, abs_le.mp h2]

lemma lip_a (M : FracMech n (CoreTask n ℓ)) (hfeas : IsFeasibleOn IsGraphInput M)
    (htruth : IsTruthfulOn IsGraphInput M) (i : Fin n) (a b s : CoreTask n ℓ → ℝ)
    (ha : ∀ d, 0 ≤ a d) (hb : ∀ d, 0 ≤ b d) (hs : ∀ d, 0 ≤ s d) (δ : ℝ)
    (hab : ∀ d, |b d - a d| ≤ δ) :
    |W M i b s - W M i a s| ≤ Fintype.card (CoreTask n ℓ) * δ := by
  classical
  have key : ∀ T : Finset (CoreTask n ℓ),
      |W M i (fun d => if d ∈ T then b d else a d) s - W M i a s| ≤ T.card * δ := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert e T he ih =>
      have hc : ∀ T' : Finset (CoreTask n ℓ), ∀ d, 0 ≤ (fun d => if d ∈ T' then b d else a d) d := by
        intro T' d; simp only; split_ifs
        · exact hb d
        · exact ha d
      have hstep := step_lip M hfeas htruth i (fun d => if d ∈ T then b d else a d)
        (fun d => if d ∈ insert e T then b d else a d) s e (hc T) (hc _) hs (by
          intro d hd
          simp [Finset.mem_insert, hd])
      have : |(fun d => if d ∈ insert e T then b d else a d) e -
          (fun d => if d ∈ T then b d else a d) e| ≤ δ := by
        simp [he, hab e]
      rw [Finset.card_insert_of_notMem he]
      push_cast
      have := abs_sub_le (W M i (fun d => if d ∈ insert e T then b d else a d) s)
        (W M i (fun d => if d ∈ T then b d else a d) s) (W M i a s)
      nlinarith [abs_le.mp ih]
  have := key Finset.univ
  simpa using this

structure Hyp (M : FracMech n (CoreTask n ℓ)) : Prop where
  hℓ : 2 ≤ ℓ
  feas : IsFeasibleOn IsGraphInput M
  truth : IsTruthfulOn IsGraphInput M
  el : IsEligible M
  zti : HasZeroTypeIrrelevance M

lemma mono_s (M : FracMech n (CoreTask n ℓ)) (H : Hyp M) (i : Fin n) (a s s' : CoreTask n ℓ → ℝ)
    (ha : ∀ d, 0 ≤ a d) (hs : ∀ d, 0 ≤ s d) (hs' : ∀ d, 0 ≤ s' d) (hle : ∀ d, s d ≤ s' d) :
    W M i a s ≤ W M i a s' := by
  refine FracTruthSched.lemma_4 H.hℓ M H.feas H.truth H.el H.zti i (I i a s) (I i a s')
    (I_graph i a s ha hs) (I_graph i a s' ha hs') ?_ ?_
  · rintro u e (rfl | h)
    · simp [I]
    · unfold I
      rw [if_neg (fun hc => h ⟨hc.1, hc.2.1⟩), if_neg (fun hc => h ⟨hc.1, hc.2.1⟩)]
  · intro u e
    unfold I
    split_ifs
    · exact le_refl _
    · exact hle e
    · exact le_refl _

def ratv (q : CoreTask n ℓ → ℚ) : CoreTask n ℓ → ℝ := fun d => (q d : ℝ)

noncomputable def fz (M : FracMech n (CoreTask n ℓ)) (i : Fin n) (q : CoreTask n ℓ → ℚ) (z : ℝ) : ℝ :=
  W M i (ratv q) (fun _ => max z 0)

lemma fz_mono (M : FracMech n (CoreTask n ℓ)) (H : Hyp M) (i : Fin n) (q : CoreTask n ℓ → ℚ)
    (hq : ∀ d, 0 ≤ q d) : Monotone (fz M i q) := by
  intro z z' hz
  exact mono_s M H i _ _ _ (fun d => by simpa [ratv] using hq d) (fun _ => le_max_right _ _)
    (fun _ => le_max_right _ _) (fun _ => max_le_max hz le_rfl)

lemma exists_lam (M : FracMech n (CoreTask n ℓ)) (H : Hyp M) (i : Fin n) (ε : ℝ) (hε : 0 < ε) :
    ∃ lam ∈ Set.Ioo (1:ℝ) (1 + ε), ∀ q : CoreTask n ℓ → ℚ, (∀ d, 0 ≤ q d) →
      ContinuousAt (fz M i q) lam := by
  have hcount : (⋃ q : CoreTask n ℓ → ℚ,
      {z | (∀ d, 0 ≤ q d) ∧ ¬ ContinuousAt (fz M i q) z}).Countable := by
    refine Set.countable_iUnion (fun q => ?_)
    by_cases hq : ∀ d, 0 ≤ q d
    · exact (fz_mono M H i q hq).countable_not_continuousAt.mono (fun z hz => hz.2)
    · exact Set.countable_empty.mono (fun z hz => absurd hz.1 hq)
  by_contra hcon
  push Not at hcon
  have hsub : Set.Ioo (1:ℝ) (1 + ε) ⊆ ⋃ q : CoreTask n ℓ → ℚ,
      {z | (∀ d, 0 ≤ q d) ∧ ¬ ContinuousAt (fz M i q) z} := by
    intro z hz
    obtain ⟨q, hq, hnc⟩ := hcon z hz
    exact Set.mem_iUnion.2 ⟨q, hq, hnc⟩
  have h0 := MeasureTheory.measure_mono_null hsub (hcount.measure_zero MeasureTheory.volume)
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  linarith

lemma cont_at (M : FracMech n (CoreTask n ℓ)) (H : Hyp M) (i : Fin n) (lam : ℝ) (hlam : 0 < lam)
    (hc : ∀ q : CoreTask n ℓ → ℚ, (∀ d, 0 ≤ q d) → ContinuousAt (fz M i q) lam)
    (q : CoreTask n ℓ → ℚ) (hq : ∀ d, 0 ≤ q d) (ε' : ℝ) (hε' : 0 < ε') :
    ∃ η > 0, ∀ s : CoreTask n ℓ → ℝ, (∀ d, 0 ≤ s d) → (∀ d, |s d - lam| ≤ η) →
      |W M i (ratv q) s - W M i (ratv q) (fun _ => lam)| < ε' := by
  obtain ⟨η0, hη0, h⟩ := Metric.continuousAt_iff.mp (hc q hq) ε' hε'
  refine ⟨min (η0 / 2) (lam / 2), by positivity, ?_⟩
  intro s hs hsl
  set η := min (η0 / 2) (lam / 2) with hη
  have hη1 : η ≤ η0 / 2 := min_le_left _ _
  have hη2 : η ≤ lam / 2 := min_le_right _ _
  have hηpos : 0 < η := by positivity
  have hq0 : ∀ d, 0 ≤ ratv q d := fun d => by simpa [ratv] using hq d
  have hfl : fz M i q lam = W M i (ratv q) (fun _ => lam) := by
    simp [fz, max_eq_left hlam.le]
  have hlo := mono_s M H i (ratv q) (fun _ => max (lam - η) 0) s hq0 (fun _ => le_max_right _ _) hs
    (fun d => max_le (by have := abs_le.mp (hsl d); linarith) (hs d))
  have hhi := mono_s M H i (ratv q) s (fun _ => max (lam + η) 0) hq0 hs (fun _ => le_max_right _ _)
    (fun d => le_trans (by have := abs_le.mp (hsl d); linarith) (le_max_left _ _))
  have h1 := h (x := lam - η) (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  have h2 := h (x := lam + η) (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
  rw [Real.dist_eq, abs_lt] at h1 h2
  change W M i (ratv q) (fun _ => max (lam - η) 0) ≤ _ at hlo
  change _ ≤ W M i (ratv q) (fun _ => max (lam + η) 0) at hhi
  simp only [fz] at h1 h2 hfl
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma ae_dense (P : ℝ × ℝ → Prop)
    (h : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ))), P s)
    (lam η : ℝ) (hlam : 0 < lam) (hη : 0 < η) :
    ∃ s : ℝ × ℝ, 0 < s.1 ∧ 0 < s.2 ∧ |s.1 - lam| < η ∧ |s.2 - lam| < η ∧ P s := by
  rw [MeasureTheory.ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)] at h
  by_contra hno
  push Not at hno
  set U : Set (ℝ × ℝ) := Set.Ioo (max 0 (lam - η)) (lam + η) ×ˢ Set.Ioo (max 0 (lam - η)) (lam + η)
    with hU
  have hUo : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hne : U.Nonempty := ⟨(lam, lam), by
    exact ⟨⟨max_lt hlam (by linarith), by linarith⟩, max_lt hlam (by linarith), by linarith⟩⟩
  have hpos := hUo.measure_pos MeasureTheory.volume hne
  have hz := MeasureTheory.ae_iff.mp h
  have hsub : U ⊆ {a | ¬ (a ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ) → P a)} := by
    intro s hs
    simp only [hU, Set.mem_prod, Set.mem_Ioo, max_lt_iff] at hs
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, ⟨h4, h5⟩, h6⟩ := hs
    show ¬ (_ → _)
    intro hcon
    refine hno s h1 h4 ?_ ?_ (hcon ⟨h1, h4⟩) <;> rw [abs_lt] <;> constructor <;> linarith
  have := MeasureTheory.measure_mono_null hsub hz
  exact absurd this hpos.ne'

section Geometry

variable {i j : Fin n} {e f : CoreTask n ℓ}

lemma mem_class (h : e ∈ classSet i j) : e.isLeft ∧ incident i e ∧ incident j e := by
  simpa [classSet] using h

lemma endpoints (a b : Fin n) (hi : i = a ∨ i = b) (hj : j = a ∨ j = b) (hji : j ≠ i) :
    (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  rcases hi with h | h <;> rcases hj with h' | h'
  · exact absurd (h'.trans h.symm) hji
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact absurd (h'.trans h.symm) hji

lemma class_incident (hji : j ≠ i) (he : e ∈ classSet i j) (u : Fin n) :
    incident u e ↔ u = i ∨ u = j := by
  obtain ⟨hl, hi, hj⟩ := mem_class he
  rcases e with ⟨⟨⟨a, b⟩, hab⟩, k⟩ | k
  · simp only [incident] at hi hj ⊢
    rcases endpoints a b hi hj hji with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; tauto
    · subst h1; subst h2; tauto
  · simp at hl

lemma class_pair (hji : j ≠ i) (he : e ∈ classSet i j) (hf : f ∈ classSet i j) (hef : e ≠ f) :
    ∃ (p : {p : Fin n × Fin n // p.1 < p.2}) (k₁ k₂ : Fin ℓ), k₁ ≠ k₂ ∧
      ((i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1)) ∧
      e = Sum.inl (p, k₁) ∧ f = Sum.inl (p, k₂) := by
  obtain ⟨hl, hi, hj⟩ := mem_class he
  obtain ⟨hl', hi', hj'⟩ := mem_class hf
  rcases e with ⟨⟨⟨a, b⟩, hab⟩, k⟩ | k
  · rcases f with ⟨⟨⟨a', b'⟩, hab'⟩, k'⟩ | k'
    · simp only [incident] at hi hj hi' hj'
      have e1 := endpoints a b hi hj hji
      have e2 := endpoints a' b' hi' hj' hji
      have hpp : a = a' ∧ b = b' := by
        rcases e1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases e2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact ⟨h1.symm.trans h3, h2.symm.trans h4⟩
        · exfalso
          simp only at hab hab'
          rw [← h1, ← h2] at hab
          rw [← h3, ← h4] at hab'
          exact lt_asymm hab hab'
        · exfalso
          simp only at hab hab'
          rw [← h1, ← h2] at hab
          rw [← h3, ← h4] at hab'
          exact lt_asymm hab hab'
        · exact ⟨h2.symm.trans h4, h1.symm.trans h3⟩
      obtain ⟨rfl, rfl⟩ := hpp
      have hk : k ≠ k' := by
        rintro rfl
        exact hef rfl
      exact ⟨⟨(a, b), hab⟩, k, k', hk, e1, rfl, rfl⟩
    · simp at hl'
  · simp at hl

end Geometry

section Slice

variable {i j : Fin n} {e f : CoreTask n ℓ}

lemma slice_input (hji : j ≠ i) (he : e ∈ classSet i j) (hf : f ∈ classSet i j) (hef : e ≠ f)
    (a s : CoreTask n ℓ → ℝ) (t s' : ℝ × ℝ) :
    pairSliceInput (I i a s) i j e f t s' =
      I i (Function.update (Function.update a e t.1) f t.2)
        (Function.update (Function.update s e s'.1) f s'.2) := by
  obtain ⟨hle, hie, hje⟩ := mem_class he
  obtain ⟨hlf, hif, hjf⟩ := mem_class hf
  have hce := class_incident hji he
  have hcf := class_incident hji hf
  funext u g
  unfold pairSliceInput I
  by_cases hge : g = e
  · subst hge
    by_cases hu : u = i
    · subst hu; simp [hle, hie, hef]
    · by_cases hu2 : u = j
      · subst hu2; simp [hle, hie, hje, hef, hu]
      · simp [hu, hu2, hce, hef]
  · by_cases hgf : g = f
    · subst hgf
      by_cases hu : u = i
      · subst hu; simp [hlf, hif, hef.symm]
      · by_cases hu2 : u = j
        · subst hu2; simp [hlf, hif, hjf, hu, hef.symm]
        · simp [hu, hu2, hcf]
    · simp [hge, hgf]

lemma slice_dis (M : FracMech n (CoreTask n ℓ)) (hji : j ≠ i) (he : e ∈ classSet i j)
    (hf : f ∈ classSet i j) (hef : e ≠ f) (a s : CoreTask n ℓ → ℝ) (t s' : ℝ × ℝ) :
    pairSliceDisutility M (I i a s) i j e f t s' =
      W M i (Function.update (Function.update a e t.1) f t.2)
        (Function.update (Function.update s e s'.1) f s'.2) -
      W M i (Function.update (Function.update a e 0) f 0)
        (Function.update (Function.update s e s'.1) f s'.2) := by
  unfold pairSliceDisutility W
  rw [slice_input hji he hf hef, slice_input hji he hf hef]
  rfl

end Slice

noncomputable def PW (M : FracMech n (CoreTask n ℓ)) (i : Fin n) (lam : ℝ)
    (c : CoreTask n ℓ → ℝ) (e f : CoreTask n ℓ) (u v : ℝ) (s : ℝ × ℝ) : ℝ :=
  W M i (Function.update (Function.update c e u) f v)
    (Function.update (Function.update (fun _ => lam) e s.1) f s.2)

noncomputable def Pl (M : FracMech n (CoreTask n ℓ)) (i : Fin n) (lam : ℝ)
    (c : CoreTask n ℓ → ℝ) (e f : CoreTask n ℓ) (u v : ℝ) : ℝ :=
  W M i (Function.update (Function.update c e u) f v) (fun _ => lam)

/-- the rectangle difference at opposing pair `s` -/
def RDs (M : FracMech n (CoreTask n ℓ)) (i : Fin n) (lam : ℝ)
    (c : CoreTask n ℓ → ℝ) (e f : CoreTask n ℓ) (u v : ℝ) (s : ℝ × ℝ) : Prop :=
  PW M i lam c e f u v s - PW M i lam c e f u 0 s - PW M i lam c e f 0 v s +
    PW M i lam c e f 0 0 s = 0

lemma ae_rd1 (M : FracMech n (CoreTask n ℓ)) (H : Hyp M) (i j : Fin n) (hji : j ≠ i)
    (e f : CoreTask n ℓ) (he : e ∈ classSet i j) (hf : f ∈ classSet i j) (hef : e ≠ f)
    (lam : ℝ) (hlam : 0 ≤ lam) (c : CoreTask n ℓ → ℝ) (hc : ∀ d, 0 ≤ c d) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ))),
      ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → RDs M i lam c e f u v s := by
  obtain ⟨p, k₁, k₂, hk, hij, rfl, rfl⟩ := class_pair hji he hf hef
  have h2b := FracTruthSched.lemma_2b H.hℓ M H.feas H.truth H.el H.zti p k₁ k₂ hk i j hij
    (I i c (fun _ => lam)) (I_graph i c _ hc (fun _ => hlam))
  filter_upwards [h2b] with s hs u v hu hv
  have := hs u v hu hv
  simp only [slice_dis M hji he hf hef] at this
  unfold RDs PW
  linarith

lemma ae_rd (M : FracMech n (CoreTask n ℓ)) (H : Hyp M) (i : Fin n) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ))),
      ∀ (j : Fin n) (e f : CoreTask n ℓ) (c' : CoreTask n ℓ → ℚ),
        (j ≠ i ∧ e ∈ classSet i j ∧ f ∈ classSet i j ∧ e ≠ f ∧ ∀ d, 0 ≤ c' d) →
        ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → RDs M i lam (ratv c') e f u v s := by
  refine MeasureTheory.ae_all_iff.2 (fun j => MeasureTheory.ae_all_iff.2 (fun e =>
    MeasureTheory.ae_all_iff.2 (fun f => MeasureTheory.ae_all_iff.2 (fun c' => ?_))))
  by_cases h : j ≠ i ∧ e ∈ classSet i j ∧ f ∈ classSet i j ∧ e ≠ f ∧ ∀ d, 0 ≤ c' d
  · obtain ⟨hji, he, hf, hef, hc'⟩ := h
    filter_upwards [ae_rd1 M H i j hji e f he hf hef lam hlam (ratv c')
      (fun d => by simpa [ratv] using hc' d)] with s hs _ u v hu hv
    exact hs u v hu hv
  · exact Filter.Eventually.of_forall (fun s hh => absurd hh h)

lemma ratv_upd2 (c' : CoreTask n ℓ → ℚ) (e f : CoreTask n ℓ) (a b : ℚ) :
    ratv (Function.update (Function.update c' e a) f b) =
      Function.update (Function.update (ratv c') e (a : ℝ)) f (b : ℝ) := by
  funext d
  simp only [ratv, Function.update_apply]
  split_ifs <;> simp

lemma rd_lam (M : FracMech n (CoreTask n ℓ)) (H : Hyp M) (i : Fin n) (lam : ℝ) (hlam : 0 < lam)
    (hc : ∀ q : CoreTask n ℓ → ℚ, (∀ d, 0 ≤ q d) → ContinuousAt (fz M i q) lam)
    (hae : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ))),
      ∀ (j : Fin n) (e f : CoreTask n ℓ) (c' : CoreTask n ℓ → ℚ),
        (j ≠ i ∧ e ∈ classSet i j ∧ f ∈ classSet i j ∧ e ≠ f ∧ ∀ d, 0 ≤ c' d) →
        ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → RDs M i lam (ratv c') e f u v s)
    (j : Fin n) (hji : j ≠ i) (e f : CoreTask n ℓ) (he : e ∈ classSet i j) (hf : f ∈ classSet i j)
    (hef : e ≠ f) (c' : CoreTask n ℓ → ℚ) (hc' : ∀ d, 0 ≤ c' d) (qu qv : ℚ) (hu : 0 ≤ qu)
    (hv : 0 ≤ qv) :
    Pl M i lam (ratv c') e f qu qv - Pl M i lam (ratv c') e f qu 0 -
      Pl M i lam (ratv c') e f 0 qv + Pl M i lam (ratv c') e f 0 0 = 0 := by
  by_contra hX
  set X := Pl M i lam (ratv c') e f qu qv - Pl M i lam (ratv c') e f qu 0 -
      Pl M i lam (ratv c') e f 0 qv + Pl M i lam (ratv c') e f 0 0 with hXdef
  have hε' : 0 < |X| / 5 := by have := abs_pos.2 hX; positivity
  set ε' := |X| / 5 with hε'def
  have cont4 : ∀ (u v : ℚ), 0 ≤ u → 0 ≤ v → ∃ η > 0, ∀ s : CoreTask n ℓ → ℝ, (∀ d, 0 ≤ s d) →
      (∀ d, |s d - lam| ≤ η) →
      |W M i (Function.update (Function.update (ratv c') e (u:ℝ)) f (v:ℝ)) s -
        Pl M i lam (ratv c') e f u v| < ε' := by
    intro u v hu hv
    obtain ⟨η, hη, h⟩ := cont_at M H i lam hlam hc (Function.update (Function.update c' e u) f v)
      (fun d => by
        simp only [Function.update_apply]
        split_ifs
        · exact hv
        · exact hu
        · exact hc' d) ε' hε'
    rw [ratv_upd2] at h
    exact ⟨η, hη, h⟩
  obtain ⟨η1, hη1, h1⟩ := cont4 qu qv hu hv
  obtain ⟨η2, hη2, h2⟩ := cont4 qu 0 hu le_rfl
  obtain ⟨η3, hη3, h3⟩ := cont4 0 qv le_rfl hv
  obtain ⟨η4, hη4, h4⟩ := cont4 0 0 le_rfl le_rfl
  simp only [Rat.cast_zero] at h2 h3 h4
  set η := min (min η1 η2) (min η3 η4) with hη
  have hηpos : 0 < η := lt_min (lt_min hη1 hη2) (lt_min hη3 hη4)
  obtain ⟨σ, hσ1, hσ2, hσ3, hσ4, hσP⟩ := ae_dense _ hae lam η hlam hηpos
  have hRD := hσP j e f c' ⟨hji, he, hf, hef, hc'⟩ qu qv (by exact_mod_cast hu)
    (by exact_mod_cast hv)
  set S : CoreTask n ℓ → ℝ := Function.update (Function.update (fun _ => lam) e σ.1) f σ.2 with hS
  have hSn : ∀ d, 0 ≤ S d := by
    intro d
    simp only [hS, Function.update_apply]
    split_ifs <;> linarith
  have hSc : ∀ d, |S d - lam| ≤ η := by
    intro d
    simp only [hS, Function.update_apply]
    split_ifs
    · exact hσ4.le
    · exact hσ3.le
    · simp [hηpos.le]
  have hmin1 : η ≤ η1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hmin2 : η ≤ η2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hmin3 : η ≤ η3 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hmin4 : η ≤ η4 := le_trans (min_le_right _ _) (min_le_right _ _)
  have b1 := h1 S hSn (fun d => le_trans (hSc d) hmin1)
  have b2 := h2 S hSn (fun d => le_trans (hSc d) hmin2)
  have b3 := h3 S hSn (fun d => le_trans (hSc d) hmin3)
  have b4 := h4 S hSn (fun d => le_trans (hSc d) hmin4)
  unfold RDs PW at hRD
  rw [abs_lt] at b1 b2 b3 b4
  have hXabs : |X| < |X| := by
    rw [abs_lt]
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, abs_nonneg X]
  exact lt_irrefl _ hXabs

section Telescope

variable {X : Type*} [DecidableEq X]

def mix (S T : Finset X) (a : X → ℝ) : X → ℝ := fun d => if d ∈ S ∧ d ∉ T then 0 else a d

lemma mix_insert (S T : Finset X) (a : X → ℝ) (f : X) :
    mix S (insert f T) a = Function.update (mix S T a) f (a f) := by
  funext d
  by_cases hd : d = f
  · subst hd; simp [mix]
  · simp [mix, hd, Function.update_apply]

lemma telescope (V : (X → ℝ) → ℝ) (S : Finset X) (a : X → ℝ)
    (hRD : ∀ T ⊆ S, ∀ e ∈ S, ∀ f ∈ S, e ≠ f → e ∉ T → f ∉ T →
      V (Function.update (Function.update (mix S T a) e (a e)) f (a f)) -
        V (Function.update (mix S T a) e (a e)) - V (Function.update (mix S T a) f (a f)) +
        V (mix S T a) = 0) :
    V a - V (fun d => if d ∈ S then 0 else a d) =
      ∑ e ∈ S, (V (Function.update (fun d => if d ∈ S then 0 else a d) e (a e)) -
        V (fun d => if d ∈ S then 0 else a d)) := by
  have h0 : (fun d => if d ∈ S then 0 else a d) = mix S ∅ a := by
    funext d; simp [mix]
  have hS : mix S S a = a := by funext d; simp [mix]
  have hB : ∀ T ⊆ S, ∀ e ∈ S, e ∉ T →
      V (Function.update (mix S T a) e (a e)) - V (mix S T a) =
        V (Function.update (mix S ∅ a) e (a e)) - V (mix S ∅ a) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _ e _ _; rfl
    | insert f T hf ih =>
      intro hsub e he heT
      have hfS : f ∈ S := hsub (Finset.mem_insert_self _ _)
      have hTS : T ⊆ S := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hef : e ≠ f := fun h => heT (h ▸ Finset.mem_insert_self _ _)
      have heT' : e ∉ T := fun h => heT (Finset.mem_insert_of_mem h)
      have := ih hTS e he heT'
      have hr := hRD T hTS e he f hfS hef heT' hf
      rw [mix_insert, Function.update_comm hef.symm]
      linarith
  have hA : ∀ T ⊆ S, V (mix S T a) - V (mix S ∅ a) =
      ∑ e ∈ T, (V (Function.update (mix S ∅ a) e (a e)) - V (mix S ∅ a)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert e T he ih =>
      intro hsub
      have heS : e ∈ S := hsub (Finset.mem_insert_self _ _)
      have hTS : T ⊆ S := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      rw [Finset.sum_insert he, ← ih hTS, mix_insert, ← hB T hTS e heS he]
      ring
  rw [h0]
  have := hA S subset_rfl
  rw [hS] at this
  exact this

end Telescope

structure Good (M : FracMech n (CoreTask n ℓ)) (i : Fin n) (lam : ℝ) : Prop where
  pos : 0 < lam
  cont : ∀ q : CoreTask n ℓ → ℚ, (∀ d, 0 ≤ q d) → ContinuousAt (fz M i q) lam
  ae : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ))),
      ∀ (j : Fin n) (e f : CoreTask n ℓ) (c' : CoreTask n ℓ → ℚ),
        (j ≠ i ∧ e ∈ classSet i j ∧ f ∈ classSet i j ∧ e ≠ f ∧ ∀ d, 0 ≤ c' d) →
        ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → RDs M i lam (ratv c') e f u v s

lemma rd_V (M : FracMech n (CoreTask n ℓ)) (H : Hyp M) (i : Fin n) (lam : ℝ)
    (G : Good M i lam) (j : Fin n) (hji : j ≠ i) (e f : CoreTask n ℓ)
    (he : e ∈ classSet i j) (hf : f ∈ classSet i j) (hef : e ≠ f) (q : CoreTask n ℓ → ℚ)
    (hq : ∀ d, 0 ≤ q d) (hqe : q e = 0) (hqf : q f = 0) (u v : ℚ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    W M i (Function.update (Function.update (ratv q) e (u:ℝ)) f (v:ℝ)) (fun _ => lam) -
      W M i (Function.update (ratv q) e (u:ℝ)) (fun _ => lam) -
      W M i (Function.update (ratv q) f (v:ℝ)) (fun _ => lam) +
      W M i (ratv q) (fun _ => lam) = 0 := by
  have h := rd_lam M H i lam G.pos G.cont G.ae j hji e f he hf hef q hq u v hu hv
  unfold Pl at h
  have e1 : Function.update (Function.update (ratv q) e (u:ℝ)) f 0 =
      Function.update (ratv q) e (u:ℝ) := by
    rw [Function.update_eq_self_iff]
    simp [Function.update_of_ne hef.symm, ratv, hqf]
  have e2 : Function.update (Function.update (ratv q) e 0) f (v:ℝ) =
      Function.update (ratv q) f (v:ℝ) := by
    have : Function.update (ratv q) e 0 = ratv q := by
      rw [Function.update_eq_self_iff]
      simp [ratv, hqe]
    rw [this]
  have e3 : Function.update (Function.update (ratv q) e 0) f 0 = ratv q := by
    rw [Function.update_eq_self_iff.2 (show (0:ℝ) = Function.update (ratv q) e 0 f by
      simp [Function.update_of_ne hef.symm, ratv, hqf])]
    rw [Function.update_eq_self_iff]
    simp [ratv, hqe]
  rw [e1, e2, e3] at h
  exact h

lemma additive_rat (M : FracMech n (CoreTask n ℓ)) (H : Hyp M) (i : Fin n) (lam : ℝ)
    (G : Good M i lam) (j : Fin n) (hji : j ≠ i) (q : CoreTask n ℓ → ℚ) (hq : ∀ d, 0 ≤ q d) :
    W M i (ratv q) (fun _ => lam) -
      W M i (fun d => if d ∈ classSet i j then 0 else ratv q d) (fun _ => lam) =
    ∑ e ∈ classSet i j, (W M i (Function.update
        (fun d => if d ∈ classSet i j then 0 else ratv q d) e (ratv q e)) (fun _ => lam) -
      W M i (fun d => if d ∈ classSet i j then 0 else ratv q d) (fun _ => lam)) := by
  refine telescope (fun a => W M i a (fun _ => lam)) (classSet i j) (ratv q) ?_
  intro T hT e he f hf hef heT hfT
  have hmix : mix (classSet i j) T (ratv q) =
      ratv (fun d => if d ∈ classSet i j ∧ d ∉ T then 0 else q d) := by
    funext d
    simp only [mix, ratv]
    split_ifs <;> simp
  rw [hmix]
  exact rd_V M H i lam G j hji e f he hf hef _
    (fun d => by beta_reduce; split_ifs <;> simp [hq d]) (by simp [he, heT]) (by simp [hf, hfT])
    (q e) (q f) (hq e) (hq f)

noncomputable def Phi (M : FracMech n (CoreTask n ℓ)) (i : Fin n) (lam : ℝ) (S : Finset (CoreTask n ℓ))
    (a : CoreTask n ℓ → ℝ) : ℝ :=
  W M i a (fun _ => lam) - W M i (fun d => if d ∈ S then 0 else a d) (fun _ => lam) -
    ∑ e ∈ S, (W M i (Function.update (fun d => if d ∈ S then 0 else a d) e (a e)) (fun _ => lam) -
      W M i (fun d => if d ∈ S then 0 else a d) (fun _ => lam))

lemma phi_lip (M : FracMech n (CoreTask n ℓ)) (H : Hyp M) (i : Fin n) (lam : ℝ) (hlam : 0 ≤ lam)
    (S : Finset (CoreTask n ℓ)) (a b : CoreTask n ℓ → ℝ) (ha : ∀ d, 0 ≤ a d) (hb : ∀ d, 0 ≤ b d)
    (δ : ℝ) (hδ : 0 ≤ δ) (hab : ∀ d, |b d - a d| ≤ δ) :
    |Phi M i lam S b - Phi M i lam S a| ≤
      (2 * Fintype.card (CoreTask n ℓ) + 2 * Fintype.card (CoreTask n ℓ) *
        Fintype.card (CoreTask n ℓ)) * δ := by
  classical
  set K : ℝ := (Fintype.card (CoreTask n ℓ) : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hs : ∀ d : CoreTask n ℓ, 0 ≤ (fun _ : CoreTask n ℓ => lam) d := fun _ => hlam
  have a0n : ∀ x : CoreTask n ℓ → ℝ, (∀ d, 0 ≤ x d) → ∀ d, 0 ≤ (fun d => if d ∈ S then 0 else x d) d := by
    intro x hx d; beta_reduce; split_ifs
    · exact le_rfl
    · exact hx d
  have a0d : ∀ d, |(fun d => if d ∈ S then 0 else b d) d - (fun d => if d ∈ S then 0 else a d) d| ≤ δ := by
    intro d; beta_reduce; split_ifs
    · simpa using hδ
    · exact hab d
  have upn : ∀ (x : CoreTask n ℓ → ℝ), (∀ d, 0 ≤ x d) → ∀ e, 0 ≤ x e →
      ∀ d, 0 ≤ Function.update (fun d => if d ∈ S then 0 else x d) e (x e) d := by
    intro x hx e hxe d
    rw [Function.update_apply]; split_ifs
    · exact hxe
    · exact le_rfl
    · exact hx d
  have l := fun x y hx hy hxy => lip_a M H.feas H.truth i x y (fun _ => lam) hx hy hs δ hxy
  have h1 := l a b ha hb hab
  have h2 := l _ _ (a0n a ha) (a0n b hb) a0d
  have h3 : ∀ e ∈ S, |(W M i (Function.update (fun d => if d ∈ S then 0 else b d) e (b e))
        (fun _ => lam) - W M i (fun d => if d ∈ S then 0 else b d) (fun _ => lam)) -
      (W M i (Function.update (fun d => if d ∈ S then 0 else a d) e (a e)) (fun _ => lam) -
        W M i (fun d => if d ∈ S then 0 else a d) (fun _ => lam))| ≤ 2 * K * δ := by
    intro e _
    have := l (Function.update (fun d => if d ∈ S then 0 else a d) e (a e))
      (Function.update (fun d => if d ∈ S then 0 else b d) e (b e)) (upn a ha e (ha e))
      (upn b hb e (hb e)) (by
        intro d
        simp only [Function.update_apply]
        split_ifs
        · exact hab e
        · simpa using hδ
        · exact hab d)
    rw [abs_le] at this h2 ⊢
    constructor <;> nlinarith [this.1, this.2, h2.1, h2.2]
  have h4 : |∑ e ∈ S, ((W M i (Function.update (fun d => if d ∈ S then 0 else b d) e (b e))
        (fun _ => lam) - W M i (fun d => if d ∈ S then 0 else b d) (fun _ => lam)) -
      (W M i (Function.update (fun d => if d ∈ S then 0 else a d) e (a e)) (fun _ => lam) -
        W M i (fun d => if d ∈ S then 0 else a d) (fun _ => lam)))| ≤ K * (2 * K * δ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ h3) ?_
    rw [nsmul_eq_mul]
    have hcard : (S.card : ℝ) ≤ K := by
      rw [hK]; exact_mod_cast Finset.card_le_univ S
    have : 0 ≤ 2 * K * δ := by positivity
    exact mul_le_mul_of_nonneg_right hcard this
  rw [Finset.sum_sub_distrib] at h4
  unfold Phi
  rw [abs_le] at h1 h2 h4 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h4.1, h4.2]

lemma zero_of_approx (Φ C : ℝ) (hC : 0 ≤ C) (h : ∀ δ > 0, |Φ| ≤ C * δ) : Φ = 0 := by
  by_contra hne
  have hp : 0 < |Φ| := abs_pos.2 hne
  have hδ : 0 < |Φ| / (2 * (C + 1)) := by positivity
  have := h _ hδ
  have h2 : C * (|Φ| / (2 * (C + 1))) < |Φ| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

lemma additive_real (M : FracMech n (CoreTask n ℓ)) (H : Hyp M) (i : Fin n) (lam : ℝ)
    (G : Good M i lam) (j : Fin n) (hji : j ≠ i) (a : CoreTask n ℓ → ℝ) (ha : ∀ d, 0 ≤ a d) :
    Phi M i lam (classSet i j) a = 0 := by
  apply zero_of_approx _ (2 * Fintype.card (CoreTask n ℓ) + 2 * Fintype.card (CoreTask n ℓ) *
        Fintype.card (CoreTask n ℓ)) (by positivity)
  intro δ hδ
  have hex : ∀ d, ∃ r : ℚ, a d < r ∧ (r:ℝ) < a d + δ := fun d =>
    exists_rat_btwn (lt_add_of_pos_right _ hδ)
  choose q hq1 hq2 using hex
  have hqn : ∀ d, 0 ≤ q d := fun d => by
    have := lt_of_le_of_lt (ha d) (hq1 d)
    exact_mod_cast this.le
  have hrat : Phi M i lam (classSet i j) (ratv q) = 0 := by
    unfold Phi
    rw [additive_rat M H i lam G j hji q hqn]
    ring
  have := phi_lip M H i lam G.pos.le (classSet i j) a (ratv q) ha (fun d => by
    simpa [ratv] using hqn d) δ hδ.le (fun d => by
      rw [abs_le]; simp only [ratv]; constructor <;> linarith [hq1 d, hq2 d])
  rw [hrat] at this
  simpa [abs_sub_comm] using this


section Sym

variable {i j : Fin n}

lemma perm_mem (S : Finset (CoreTask n ℓ)) (σ : Equiv.Perm (CoreTask n ℓ))
    (hσ : ∀ e, e ∉ S → σ e = e) (e : CoreTask n ℓ) (he : e ∈ S) : σ e ∈ S := by
  by_contra h
  have h1 := hσ _ h
  have h2 : σ e = e := σ.injective h1
  exact h (by rw [h2]; exact he)

lemma classPerm (hji : j ≠ i) (σ : Equiv.Perm (CoreTask n ℓ))
    (hσ : ∀ e, e ∉ classSet i j → σ e = e) : IsClassPerm σ := by
  constructor
  · intro p k
    by_cases hm : (Sum.inl (p, k) : CoreTask n ℓ) ∈ classSet i j
    · have hm' := perm_mem _ σ hσ _ hm
      by_cases hs : σ (Sum.inl (p, k)) = Sum.inl (p, k)
      · exact ⟨k, hs⟩
      · obtain ⟨p', k1, k2, _, _, h1, h2⟩ := class_pair hji hm hm' (Ne.symm hs)
        have h3 : p = p' := (Prod.mk.inj (Sum.inl.inj h1)).1
        subst h3
        exact ⟨k2, h2⟩
    · exact ⟨k, hσ _ hm⟩
  · intro k
    exact hσ _ (by simp [classSet])

lemma relabel_root (hji : j ≠ i) (σ : Equiv.Perm (CoreTask n ℓ))
    (hσ : ∀ e, e ∉ classSet i j → σ e = e) (lam : ℝ) (a : CoreTask n ℓ → ℝ) :
    relabel σ (rootStarInput i lam a) = rootStarInput i lam (a ∘ σ) := by
  funext u e
  unfold relabel rootStarInput
  by_cases he : e ∈ classSet i j
  · have hm := perm_mem _ σ hσ _ he
    obtain ⟨hl, hi, _⟩ := mem_class he
    obtain ⟨hl', hi', _⟩ := mem_class hm
    have c1 := class_incident hji he u
    have c2 := class_incident hji hm u
    simp [hl, hi, hl', hi', c1, c2]
  · simp only [hσ e he, Function.comp]

lemma sym_all (M : FracMech n (CoreTask n ℓ)) (hsym : IsClassSymmetric M) (lam : ℝ)
    (hlam : 0 ≤ lam) (hji : j ≠ i) :
    IsSymmetricOn (fun a => disutility M (rootStarInput i lam a) i) (classSet i j) := by
  intro σ hσ a ha
  have ht : IsGraphInput (rootStarInput i lam a) := I_graph i a (fun _ => lam) ha (fun _ => hlam)
  have := (hsym σ (classPerm hji σ hσ) _ ht).2 i
  rw [relabel_root hji σ hσ lam a] at this
  exact this

lemma add_all (M : FracMech n (CoreTask n ℓ)) (H : Hyp M) (lam : ℝ) (G : Good M i lam)
    (hji : j ≠ i) :
    IsAdditiveOn (fun a => disutility M (rootStarInput i lam a) i) (classSet i j) := by
  intro a ha
  have h := additive_real M H i lam G j hji a ha
  unfold Phi at h
  change W M i a (fun _ => lam) -
      W M i (fun d => if d ∈ classSet i j then 0 else a d) (fun _ => lam) =
    ∑ e ∈ classSet i j, (W M i (Function.update
        (fun d => if d ∈ classSet i j then 0 else a d) e (a e)) (fun _ => lam) -
      W M i (fun d => if d ∈ classSet i j then 0 else a d) (fun _ => lam))
  linarith

end Sym

end FracTruthSched.Dev.L5

namespace FracTruthSched

/-- **Lemma 5 (common leaf value)** -/
theorem chk_lemma_5 {n ℓ : ℕ} (hℓ : 2 ≤ ℓ) (M : FracMech n (CoreTask n ℓ))
    (hfeas : IsFeasibleOn IsGraphInput M) (htruth : IsTruthfulOn IsGraphInput M)
    (hel : IsEligible M) (hzti : HasZeroTypeIrrelevance M) (hsym : IsClassSymmetric M)
    (i : Fin n) (ε : ℝ) (hε : 0 < ε) :
    ∃ lam ∈ Set.Ioo 1 (1 + ε), ∀ j, j ≠ i →
      IsAdditiveOn (fun a => disutility M (rootStarInput i lam a) i) (classSet i j) ∧
        IsSymmetricOn (fun a => disutility M (rootStarInput i lam a) i) (classSet i j) := by
  have H : Dev.L5.Hyp M := ⟨hℓ, hfeas, htruth, hel, hzti⟩
  obtain ⟨lam, hlam, hcont⟩ := Dev.L5.exists_lam M H i ε hε
  have hpos : 0 < lam := by linarith [hlam.1]
  have G : Dev.L5.Good M i lam := ⟨hpos, hcont, Dev.L5.ae_rd M H i lam hpos.le⟩
  exact ⟨lam, hlam, fun j hji => ⟨Dev.L5.add_all M H lam G hji,
    Dev.L5.sym_all M hsym lam hpos.le hji⟩⟩

end FracTruthSched
end

theorem solution : type_of% @FracTruthSched.chk_lemma_5 := @FracTruthSched.chk_lemma_5
