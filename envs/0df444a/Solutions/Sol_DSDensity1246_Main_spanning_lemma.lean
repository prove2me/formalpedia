-- Prove2me | solution 1 for DSDensity1246.Main.spanning_lemma
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:20:38.420191+00:00
-- url     : https://prove2.me/submissions/5df17d6b-70a0-4117-adb2-8dece1eb64d6

import Mathlib
import Definitions.Def_DSDensity1246_Main_dsModel
import Definitions.Def_DSDensity1246_Main_monomials

section
set_option autoImplicit false

namespace DSDensity1246.Dev.Spanning

open DSDensity1246.Main
open scoped Classical

def mono {k n : ℕ} (α : Fin n → ℕ) : (Fin n → Fin k) → ℝ :=
  fun w => ∏ i : Fin n, realLabel (w i) ^ (α i)

def PS (k n ℓ : ℕ) (T : Finset (Fin n)) (s : ℕ) : Submodule ℝ ((Fin n → Fin k) → ℝ) :=
  Submodule.span ℝ {f | ∃ α : Fin n → ℕ, (∀ i, α i < k) ∧ (∀ i, i ∉ T → α i = 0) ∧
    (Finset.univ.filter (fun i => ℓ ≤ α i)).card ≤ s ∧ f = mono α}

def Loc {k n : ℕ} (T : Finset (Fin n)) (g : (Fin n → Fin k) → ℝ) : Prop :=
  ∀ w w' : Fin n → Fin k, (∀ i ∈ T, w i = w' i) → g w = g w'

def Agr {k n : ℕ} (T : Finset (Fin n)) (w h : Fin n → Fin k) : Prop := ∀ j ∈ T, w j = h j

def Nb {k n : ℕ} (T : Finset (Fin n)) (i : Fin n) (f g : Fin n → Fin k) : Prop :=
  g i ≠ f i ∧ ∀ j ∈ T, j ≠ i → g j = f j

noncomputable def cnt {k n : ℕ} (F : Finset (Fin n → Fin k)) (T : Finset (Fin n)) (i : Fin n)
    (f : Fin n → Fin k) : ℕ :=
  ((F.filter (Nb T i f)).image (fun g => g i)).card

def Shat {k n : ℕ} (ℓ : ℕ) (A : Finset (Fin n → Fin k)) (U : Finset (Fin n)) : Prop :=
  ∃ F : Finset (Fin n → Fin k), F.Nonempty ∧ (∀ f ∈ F, ∃ a ∈ A, Agr U a f) ∧
    ∀ f ∈ F, ∀ i ∈ U, ℓ ≤ cnt F U i f

def Good {k n : ℕ} (ℓ s : ℕ) (A : Finset (Fin n → Fin k)) (T : Finset (Fin n)) : Prop :=
  ∀ U ⊆ T, s < U.card → ¬ Shat ℓ A U

lemma Good.mono_set {k n ℓ s : ℕ} {A B : Finset (Fin n → Fin k)} {T : Finset (Fin n)}
    (h : Good ℓ s A T) (hB : B ⊆ A) : Good ℓ s B T := by
  intro U hU hc ⟨F, hne, hF, hc'⟩
  exact h U hU hc ⟨F, hne, fun f hf => by
    obtain ⟨a, ha, h2⟩ := hF f hf
    exact ⟨a, hB ha, h2⟩, hc'⟩

lemma Good.mono_T {k n ℓ s : ℕ} {A : Finset (Fin n → Fin k)} {T T' : Finset (Fin n)}
    (h : Good ℓ s A T) (hT : T' ⊆ T) : Good ℓ s A T' :=
  fun U hU => h U (hU.trans hT)

lemma PS_mono {k n ℓ s s' : ℕ} {T T' : Finset (Fin n)} (hT : T ⊆ T') (hs : s ≤ s') :
    PS k n ℓ T s ≤ PS k n ℓ T' s' := by
  apply Submodule.span_mono
  rintro f ⟨α, h1, h2, h3, h4⟩
  exact ⟨α, h1, fun i hi => h2 i (fun h => hi (hT h)), h3.trans hs, h4⟩

lemma PS_loc {k n ℓ s : ℕ} {T : Finset (Fin n)} {p : (Fin n → Fin k) → ℝ}
    (hp : p ∈ PS k n ℓ T s) : Loc T p := by
  induction hp using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α, h1, h2, h3, rfl⟩ := hf
    intro w w' hw
    unfold mono
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ T
    · rw [hw i hi]
    · rw [h2 i hi]; simp
  | zero => intro w w' _; rfl
  | add x y _ _ hx hy => intro w w' hw; simp [hx w w' hw, hy w w' hw]
  | smul a x _ hx => intro w w' hw; simp [hx w w' hw]

lemma mono_mul {k n : ℕ} (α : Fin n → ℕ) (i : Fin n) (hi : α i = 0) (e : ℕ) :
    (fun w : Fin n → Fin k => mono α w * realLabel (w i) ^ e) = mono (Function.update α i e) := by
  funext w
  unfold mono
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => realLabel (w j) ^ (Function.update α i e j))
      (Finset.mem_univ i)]
  have : ∏ j ∈ Finset.univ.erase i, realLabel (w j) ^ (Function.update α i e j)
      = ∏ j ∈ Finset.univ.erase i, realLabel (w j) ^ (α j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this, hi]
  simp [mul_comm]

lemma PS_mulX {k n ℓ s' s'' : ℕ} {T' T'' : Finset (Fin n)} (hT : T' ⊆ T'') (i : Fin n)
    (hi' : i ∉ T') (hi : i ∈ T'') (e : ℕ) (he : e < k)
    (hs : s' + (if ℓ ≤ e then 1 else 0) ≤ s'')
    {p : (Fin n → Fin k) → ℝ} (hp : p ∈ PS k n ℓ T' s') :
    (fun w => p w * realLabel (w i) ^ e) ∈ PS k n ℓ T'' s'' := by
  induction hp using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α, h1, h2, h3, rfl⟩ := hf
    have hαi : α i = 0 := h2 i hi'
    rw [mono_mul α i hαi e]
    apply Submodule.subset_span
    refine ⟨Function.update α i e, ?_, ?_, ?_, rfl⟩
    · intro j
      by_cases hj : j = i
      · subst hj; simpa using he
      · rw [Function.update_of_ne hj]; exact h1 j
    · intro j hj
      have hji : j ≠ i := fun h => hj (h ▸ hi)
      rw [Function.update_of_ne hji]
      exact h2 j (fun h => hj (hT h))
    · by_cases hle : ℓ ≤ e
      · rw [if_pos hle] at hs
        calc _ ≤ (insert i (Finset.univ.filter (fun j => ℓ ≤ α j))).card := by
              apply Finset.card_le_card
              intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              by_cases hji : j = i
              · simp [hji]
              · rw [Function.update_of_ne hji] at hj
                simp [hj]
          _ ≤ _ := Finset.card_insert_le _ _
          _ ≤ s'' := by omega
      · rw [if_neg hle] at hs
        calc _ ≤ (Finset.univ.filter (fun j => ℓ ≤ α j)).card := by
              apply Finset.card_le_card
              intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
              by_cases hji : j = i
              · subst hji; simp at hj; omega
              · rwa [Function.update_of_ne hji] at hj
          _ ≤ s'' := by omega
  | zero =>
    have : (fun w : Fin n → Fin k => (0 : (Fin n → Fin k) → ℝ) w * realLabel (w i) ^ e) = 0 := by
      funext w; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun w => (x w + y w) * realLabel (w i) ^ e) =
        (fun w => x w * realLabel (w i) ^ e) + (fun w => y w * realLabel (w i) ^ e) := by
      funext w; simp [add_mul]
    simp only [Pi.add_apply] 
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : (fun w => (a • x) w * realLabel (w i) ^ e) =
        a • (fun w => x w * realLabel (w i) ^ e) := by
      funext w; simp [mul_assoc]
    rw [this]; exact Submodule.smul_mem _ _ hx

lemma PS_mulPoly {k n ℓ s' s'' : ℕ} {T' T'' : Finset (Fin n)} (hT : T' ⊆ T'') (i : Fin n)
    (hi' : i ∉ T') (hi : i ∈ T'') (q : Polynomial ℝ) (d : ℕ) (hq : q.natDegree ≤ d) (hd : d < k)
    (hs : s' + (if ℓ ≤ d then 1 else 0) ≤ s'')
    {p : (Fin n → Fin k) → ℝ} (hp : p ∈ PS k n ℓ T' s') :
    (fun w => p w * q.eval (realLabel (w i))) ∈ PS k n ℓ T'' s'' := by
  have : (fun w : Fin n → Fin k => p w * q.eval (realLabel (w i))) =
      ∑ e ∈ Finset.range (d + 1), q.coeff e • (fun w : Fin n → Fin k => p w * realLabel (w i) ^ e) := by
    funext w
    rw [Polynomial.eval_eq_sum_range' (n := d + 1) (by omega)]
    simp [Finset.mul_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro e _; ring
  rw [this]
  apply Submodule.sum_mem
  intro e he
  have he' : e ≤ d := by simpa [Nat.lt_succ_iff] using he
  apply Submodule.smul_mem
  apply PS_mulX hT i hi' hi e (by omega) _ hp
  have : (if ℓ ≤ e then 1 else 0) ≤ (if ℓ ≤ d then 1 else 0) := by
    split_ifs <;> omega
  omega

lemma PS_one {k n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hk : ∀ i : Fin n, 0 < k) (T : Finset (Fin n)) (s : ℕ) :
    (fun _ : Fin n → Fin k => (1 : ℝ)) ∈ PS k n ℓ T s := by
  apply Submodule.subset_span
  refine ⟨fun _ => 0, fun i => hk i, fun _ _ => rfl, ?_, ?_⟩
  · simp [show ℓ ≠ 0 by omega]
  · funext w; simp [mono]

lemma PS_prod {k n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hk : ∀ i : Fin n, 0 < k) (q : Fin n → Polynomial ℝ)
    (hq : ∀ i, (q i).natDegree < k) (T : Finset (Fin n)) :
    (fun w : Fin n → Fin k => ∏ i ∈ T, (q i).eval (realLabel (w i))) ∈ PS k n ℓ T T.card := by
  induction T using Finset.induction_on with
  | empty =>
    simpa using PS_one (k := k) (n := n) (ℓ := ℓ) hℓ hk ∅ 0
  | insert a T ha ih =>
    have hk0 : 0 < k := by
      by_cases hn : Nonempty (Fin n)
      · obtain ⟨i⟩ := hn; exact hk i
      · exact absurd ⟨a⟩ hn
    have := PS_mulPoly (ℓ := ℓ) (s'' := (insert a T).card) (Finset.subset_insert a T) a ha
      (Finset.mem_insert_self a T) (q a) (k - 1) (by have := hq a; omega) (by omega)
      (by rw [Finset.card_insert_of_notMem ha]; split_ifs <;> omega) ih
    convert this using 2 with w
    rw [Finset.prod_insert ha, mul_comm]

noncomputable def Lq {k n : ℕ} (h : Fin n → Fin k) (i : Fin n) : Polynomial ℝ :=
  Polynomial.C ((∏ j ∈ Finset.univ.erase (h i), (realLabel (h i) - realLabel j))⁻¹) *
    ∏ j ∈ Finset.univ.erase (h i), (Polynomial.X - Polynomial.C (realLabel j))

lemma realLabel_inj {k : ℕ} {a b : Fin k} (h : realLabel a = realLabel b) : a = b := by
  unfold realLabel at h
  apply Fin.ext
  have : (a.val : ℝ) = b.val := by linarith
  exact_mod_cast this

lemma Lq_natDegree {k n : ℕ} (h : Fin n → Fin k) (i : Fin n) : (Lq h i).natDegree < k := by
  unfold Lq
  have h1 : (∏ j ∈ Finset.univ.erase (h i), (Polynomial.X - Polynomial.C (realLabel j))).natDegree
      = (Finset.univ.erase (h i)).card :=
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card _ _
  have h2 := Polynomial.natDegree_C_mul_le ((∏ j ∈ Finset.univ.erase (h i),
    (realLabel (h i) - realLabel j))⁻¹) (∏ j ∈ Finset.univ.erase (h i),
      (Polynomial.X - Polynomial.C (realLabel j)))
  have h3 : (Finset.univ.erase (h i)).card < k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    have := (h i).pos
    simp; omega
  omega

lemma Lq_eval {k n : ℕ} (h w : Fin n → Fin k) (i : Fin n) :
    (Lq h i).eval (realLabel (w i)) = if w i = h i then 1 else 0 := by
  unfold Lq
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X]
  split_ifs with hw
  · rw [hw]
    have : (∏ j ∈ Finset.univ.erase (h i), (realLabel (h i) - realLabel j)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j hj
      have := Finset.ne_of_mem_erase hj
      intro h0
      exact this (realLabel_inj (by linarith)).symm
    simp [this]
  · have hz : ∏ j ∈ Finset.univ.erase (h i), (realLabel (w i) - realLabel j) = 0 :=
      Finset.prod_eq_zero (i := w i) (Finset.mem_erase.2 ⟨hw, Finset.mem_univ _⟩) (sub_self _)
    rw [hz]; simp

lemma Lq_prod {k n : ℕ} (T : Finset (Fin n)) (h w : Fin n → Fin k) :
    ∏ i ∈ T, (Lq h i).eval (realLabel (w i)) = if Agr T w h then 1 else 0 := by
  simp_rw [Lq_eval]
  by_cases hA : Agr T w h
  · rw [if_pos hA]; exact Finset.prod_eq_one (fun i hi => if_pos (hA i hi))
  · rw [if_neg hA]
    obtain ⟨i, hi, hne⟩ : ∃ i ∈ T, w i ≠ h i := by
      by_contra hc; push_neg at hc; exact hA hc
    exact Finset.prod_eq_zero hi (if_neg hne)

lemma Q_base {k n ℓ s : ℕ} (hℓ : 1 ≤ ℓ) (hk : ∀ i : Fin n, 0 < k) (T : Finset (Fin n))
    (hT : T.card ≤ s) (h : Fin n → Fin k) :
    ∃ Q ∈ PS k n ℓ T s, ∀ w, Q w = if Agr T w h then 1 else 0 := by
  refine ⟨_, PS_mono (le_refl T) hT (PS_prod hℓ hk (Lq h) (Lq_natDegree h) T), ?_⟩
  intro w
  exact Lq_prod T h w

lemma Q_step {k n ℓ s : ℕ} (hℓ : 1 ≤ ℓ) (hk : ∀ i : Fin n, 0 < k) (T : Finset (Fin n))
    (A : Finset (Fin n → Fin k)) (h1 : Fin n → Fin k) (i : Fin n) (hi : i ∈ T)
    (hc : cnt A T i h1 < ℓ) (P1 : (Fin n → Fin k) → ℝ) (hP1 : P1 ∈ PS k n ℓ (T.erase i) s)
    (hv : ∀ w ∈ A, P1 w = if Agr (T.erase i) w h1 then 1 else 0) (hh1 : h1 ∈ A) :
    ∃ Q ∈ PS k n ℓ T s, ∀ w ∈ A, (Agr T w h1 → Q w = 1) ∧ (¬ Agr T w h1 → Q w = 0) := by
  set S : Finset (Fin k) := (A.filter (Nb T i h1)).image (fun g => g i) with hS
  have hSc : S.card < ℓ := hc
  have hh1S : h1 i ∉ S := by
    intro hm
    obtain ⟨g, hg, hgi⟩ := Finset.mem_image.1 hm
    exact (Finset.mem_filter.1 hg).2.1 hgi
  have hSk : S.card < k := by
    have : S ⊆ Finset.univ.erase (h1 i) := fun v hv =>
      Finset.mem_erase.2 ⟨fun h => hh1S (h ▸ hv), Finset.mem_univ _⟩
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)] at this
    have := (h1 i).pos
    simp at *; omega
  let q : Polynomial ℝ := Polynomial.C ((∏ v ∈ S, (realLabel (h1 i) - realLabel v))⁻¹) *
    ∏ v ∈ S, (Polynomial.X - Polynomial.C (realLabel v))
  have hqdeg : q.natDegree ≤ S.card := by
    show (Polynomial.C ((∏ v ∈ S, (realLabel (h1 i) - realLabel v))⁻¹) *
      ∏ v ∈ S, (Polynomial.X - Polynomial.C (realLabel v))).natDegree ≤ S.card
    have h1' : (∏ v ∈ S, (Polynomial.X - Polynomial.C (realLabel v))).natDegree = S.card :=
      Polynomial.natDegree_finsetProd_X_sub_C_eq_card _ _
    have h2 := Polynomial.natDegree_C_mul_le ((∏ v ∈ S, (realLabel (h1 i) - realLabel v))⁻¹)
      (∏ v ∈ S, (Polynomial.X - Polynomial.C (realLabel v)))
    omega
  have hne : (∏ v ∈ S, (realLabel (h1 i) - realLabel v)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro v hv h0
    exact hh1S (by rw [realLabel_inj (by linarith : realLabel (h1 i) = realLabel v)]; exact hv)
  have hqe : ∀ x : Fin k, q.eval (realLabel x) =
      (∏ v ∈ S, (realLabel (h1 i) - realLabel v))⁻¹ * ∏ v ∈ S, (realLabel x - realLabel v) := by
    intro x
    simp [q, Polynomial.eval_prod]
  have hmem : (fun w => P1 w * q.eval (realLabel (w i))) ∈ PS k n ℓ T s :=
    PS_mulPoly (Finset.erase_subset i T) i (Finset.notMem_erase i T) hi q S.card hqdeg hSk
      (by rw [if_neg (by omega)]; omega) hP1
  refine ⟨_, hmem, ?_⟩
  intro w hw
  constructor
  · intro hag
    have hP : Agr (T.erase i) w h1 := fun j hj => hag j (Finset.mem_of_mem_erase hj)
    rw [hv w hw, if_pos hP, hqe, hag i hi]
    simp [hne]
  · intro hag
    by_cases hr : Agr (T.erase i) w h1
    · have hwi : w i ≠ h1 i := by
        intro he
        apply hag
        intro j hj
        by_cases hji : j = i
        · rw [hji]; exact he
        · exact hr j (Finset.mem_erase.2 ⟨hji, hj⟩)
      have hwS : w i ∈ S := Finset.mem_image.2 ⟨w, Finset.mem_filter.2 ⟨hw, hwi, fun j hj hji =>
        hr j (Finset.mem_erase.2 ⟨hji, hj⟩)⟩, rfl⟩
      have hz : ∏ v ∈ S, (realLabel (w i) - realLabel v) = 0 :=
        Finset.prod_eq_zero hwS (sub_self _)
      rw [hqe, hz]; simp
    · rw [hv w hw, if_neg hr]; simp

lemma peel {k n ℓ s : ℕ} (T : Finset (Fin n))
    (hQ : ∀ A : Finset (Fin n → Fin k), A.Nonempty → Good ℓ s A T →
      ∃ h1 ∈ A, ∃ Q ∈ PS k n ℓ T s, ∀ w ∈ A, (Agr T w h1 → Q w = 1) ∧ (¬ Agr T w h1 → Q w = 0))
    (g : (Fin n → Fin k) → ℝ) (hg : Loc T g) :
    ∀ A : Finset (Fin n → Fin k), Good ℓ s A T →
      ∃ p ∈ PS k n ℓ T s, ∀ w ∈ A, p w = g w := by
  intro A
  induction A using Finset.strongInduction with
  | H A ih =>
  intro hA
  by_cases hne : A.Nonempty
  · obtain ⟨h1, hh1, Q, hQm, hQv⟩ := hQ A hne hA
    have hsub : A.filter (fun w => ¬ Agr T w h1) ⊂ A :=
      Finset.filter_ssubset.2 ⟨h1, hh1, by simp [Agr]⟩
    obtain ⟨p', hp'm, hp'v⟩ := ih _ hsub (hA.mono_set hsub.subset)
    refine ⟨p' + (g h1 - p' h1) • Q, Submodule.add_mem _ hp'm (Submodule.smul_mem _ _ hQm), ?_⟩
    intro w hw
    by_cases hag : Agr T w h1
    · have e1 := (hQv w hw).1 hag
      have e2 := PS_loc hp'm w h1 hag
      have e3 := hg w h1 hag
      simp [e1, e2, e3]
    · have hw' : w ∈ A.filter (fun w => ¬ Agr T w h1) := Finset.mem_filter.2 ⟨hw, hag⟩
      simp [(hQv w hw).2 hag, hp'v w hw']
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    intro w hw
    exact absurd ⟨w, hw⟩ hne

theorem claim {k n ℓ s : ℕ} (hℓ : 1 ≤ ℓ) (hk : ∀ i : Fin n, 0 < k) :
    ∀ m : ℕ, ∀ T : Finset (Fin n), T.card = m → ∀ g : (Fin n → Fin k) → ℝ, Loc T g →
      ∀ A : Finset (Fin n → Fin k), Good ℓ s A T →
        ∃ p ∈ PS k n ℓ T s, ∀ w ∈ A, p w = g w := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro T hT g hg
  apply peel T _ g hg
  intro A hne hA
  obtain ⟨h0, hh0⟩ := hne
  by_cases hsm : T.card ≤ s
  · obtain ⟨Q, hQ, hQv⟩ := Q_base hℓ hk T hsm h0
    exact ⟨h0, hh0, Q, hQ, fun w _ => ⟨fun h => by rw [hQv, if_pos h],
      fun h => by rw [hQv, if_neg h]⟩⟩
  · push_neg at hsm
    have : ∃ h1 ∈ A, ∃ i ∈ T, cnt A T i h1 < ℓ := by
      by_contra hc
      push_neg at hc
      exact hA T (Finset.Subset.refl _) hsm
        ⟨A, ⟨h0, hh0⟩, fun f hf => ⟨f, hf, fun _ _ => rfl⟩, fun f hf i hi => hc f hf i hi⟩
    obtain ⟨h1, hh1, i, hi, hc⟩ := this
    have hlt : (T.erase i).card < m := by
      rw [Finset.card_erase_of_mem hi]
      have : 0 < T.card := Finset.card_pos.2 ⟨i, hi⟩
      omega
    have hloc : Loc (T.erase i) (fun w : Fin n → Fin k => if Agr (T.erase i) w h1 then (1 : ℝ) else 0) := by
      intro w w' hw
      have : Agr (T.erase i) w h1 ↔ Agr (T.erase i) w' h1 :=
        ⟨fun h j hj => (hw j hj).symm.trans (h j hj), fun h j hj => (hw j hj).trans (h j hj)⟩
      simp only [this]
    obtain ⟨P1, hP1, hv⟩ := ih _ hlt (T.erase i) rfl _ hloc A
      (hA.mono_T (Finset.erase_subset i T))
    obtain ⟨Q, hQ, hQv⟩ := Q_step hℓ hk T A h1 i hi hc P1 hP1 hv hh1
    exact ⟨h1, hh1, Q, hQ, hQv⟩

lemma good_univ {k n ℓ s : ℕ} (W : Set (Fin n → Fin k)) (hs : listDSDim ℓ W ≤ (s : ℕ∞)) :
    Good ℓ s (Finset.univ.filter (fun w => w ∈ W)) Finset.univ := by
  intro U _ hU hsh
  obtain ⟨F, hne, hF, hc⟩ := hsh
  let S : Fin U.card → Fin n := fun j => U.orderEmbOfFin rfl j
  have hSU : ∀ j, S j ∈ U := fun j => Finset.orderEmbOfFin_mem U rfl j
  have hSinj : Function.Injective S := (U.orderEmbOfFin rfl).injective
  have hsh : ListDSShatters ℓ W S := by
    refine ⟨F.image (fun f => f ∘ S), ?_, ?_⟩
    · intro f' hf'
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hf')
      obtain ⟨a, ha, hag⟩ := hF f hf
      exact ⟨a, (Finset.mem_filter.1 ha).2, funext fun j => hag (S j) (hSU j)⟩
    · unfold IsListDSWitness
      refine ⟨hne.image _, ?_⟩
      intro f' hf' j
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hf'
      have h1 := hc f hf (S j) (hSU j)
      unfold cnt at h1
      refine h1.trans ?_
      set X := F.filter (Nb U (S j) f)
      have e : X.image (fun g => g (S j)) = (X.image (fun g => g ∘ S)).image (fun g' => g' j) := by
        rw [Finset.image_image]; rfl
      rw [e]
      refine (Finset.card_image_le).trans (Finset.card_le_card ?_)
      intro g' hg'
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hg'
      have hg2 := Finset.mem_filter.1 hg
      obtain ⟨hgF, hgn1, hgn2⟩ := And.intro hg2.1 hg2.2
      refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨g, hgF, rfl⟩, fun h => hgn1 h.symm, ?_⟩
      intro j' hj'
      exact hgn2 (S j') (hSU j') (fun h => hj' (hSinj h)) |>.symm
  have : ((U.card : ℕ) : ℕ∞) ≤ listDSDim ℓ W :=
    le_iSup_of_le U.card (le_iSup_of_le S (le_iSup_of_le hsh le_rfl))
  have := this.trans hs
  have := Nat.cast_le.1 this
  omega

end DSDensity1246.Dev.Spanning

namespace DSDensity1246.Main

open DSDensity1246.Dev.Spanning

/-- Lemma 2.1 (Spanning Lemma [HMMS26]), p. 8, at full list-size generality. -/
theorem chk_spanning_lemma (k n ℓ s : ℕ) (W : Set (Fin n → Fin k))
    (hℓ : 1 ≤ ℓ) (hs : listDSDim ℓ W ≤ (s : ℕ∞)) :
    Submodule.span ℝ (monomials ℓ s W) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  by_cases hW : W = ∅
  · subst hW
    have : f = 0 := by
      funext x
      exact absurd x.2 (Set.notMem_empty _)
    rw [this]; exact Submodule.zero_mem _
  obtain ⟨w0, hw0⟩ := Set.nonempty_iff_ne_empty.2 hW
  have hk : ∀ i : Fin n, 0 < k := fun i => (w0 i).pos
  let g : (Fin n → Fin k) → ℝ := fun w => if h : w ∈ W then f ⟨w, h⟩ else 0
  have hg : Loc Finset.univ g := by
    intro w w' hw
    have : w = w' := funext fun i => hw i (Finset.mem_univ i)
    rw [this]
  obtain ⟨p, hp, hpv⟩ := claim (s := s) hℓ hk _ Finset.univ rfl g hg _ (good_univ W hs)
  have hmem : (LinearMap.funLeft ℝ ℝ (Subtype.val : W → (Fin n → Fin k))) p ∈
      Submodule.span ℝ (monomials ℓ s W) := by
    have hle : PS k n ℓ Finset.univ s ≤
        (Submodule.span ℝ (monomials ℓ s W)).comap
          (LinearMap.funLeft ℝ ℝ (Subtype.val : W → (Fin n → Fin k))) := by
      apply Submodule.span_le.2
      rintro f ⟨α, h1, _, h3, rfl⟩
      apply Submodule.subset_span
      exact ⟨α, h1, h3, by funext w; rfl⟩
    exact hle hp
  convert hmem using 1
  funext ⟨w, hw⟩
  have := hpv w (by simp [hw])
  simp only [LinearMap.funLeft_apply, this, g, dif_pos hw]

end DSDensity1246.Main

end

theorem solution : type_of% @DSDensity1246.Main.chk_spanning_lemma := @DSDensity1246.Main.chk_spanning_lemma
