-- Prove2me | solution 1 for FracTruthSched.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:30:25.622716+00:00
-- url     : https://prove2.me/submissions/1fe08806-d1e4-40fb-8db9-02f2b3594717

import Mathlib
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_IsGraphInput
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_disutility

section
set_option autoImplicit false

namespace FracTruthSched.Dev.L4
open FracTruthSched

variable {n ℓ : ℕ}

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

lemma riemann (T : ℝ) (hT : 0 ≤ T) (V V' x x' : ℝ → ℝ)
    (hV : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → V b - V a ≤ (b - a) * x a)
    (hV' : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → (b - a) * x' b ≤ V' b - V' a)
    (hxx : ∀ a, 0 ≤ a → a ≤ T → x a ≤ x' a) :
    V T - V 0 ≤ V' T - V' 0 := by
  have key : ∀ N : ℕ, 0 < N → ∀ m : ℕ, m ≤ N →
      (V (m * (T / N)) - V' (m * (T / N))) - (V 0 - V' 0) ≤
        (x' 0 - x' (m * (T / N))) * (T / N) := by
    intro N hN m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      have hNpos : (0:ℝ) < N := by exact_mod_cast hN
      have hδ0 : 0 ≤ T / (N:ℝ) := div_nonneg hT hNpos.le
      have hmN : ((m:ℝ) + 1) ≤ N := by exact_mod_cast hm
      have hNδ : (N:ℝ) * (T / N) = T := by field_simp
      have h1 : (m:ℝ) * (T / N) ≤ ((m+1:ℕ):ℝ) * (T / N) := by push_cast; nlinarith
      have h2 : ((m+1:ℕ):ℝ) * (T / N) ≤ T := by
        have := mul_le_mul_of_nonneg_right hmN hδ0
        rw [hNδ] at this; push_cast; linarith
      have h0 : 0 ≤ (m:ℝ) * (T / N) := by positivity
      have hd : ((m+1:ℕ):ℝ) * (T / N) - m * (T / N) = T / N := by push_cast; ring
      have a1 := hV (m * (T / N)) (((m+1:ℕ):ℝ) * (T / N)) h0 h1 h2
      have a2 := hV' (m * (T / N)) (((m+1:ℕ):ℝ) * (T / N)) h0 h1 h2
      have a3 := hxx (m * (T / N)) h0 (le_trans h1 h2)
      have a4 := mul_le_mul_of_nonneg_right a3 hδ0
      rw [hd] at a1 a2
      nlinarith
  by_contra hcon
  push Not at hcon
  have hDpos : 0 < (V T - V 0) - (V' T - V' 0) := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (((x' 0 - x' T) * T) / ((V T - V 0) - (V' T - V' 0)))
  have hMpos : (0:ℝ) < ((N+1:ℕ):ℝ) := by positivity
  have k := key (N+1) (by omega) (N+1) le_rfl
  have hT' : ((N+1:ℕ):ℝ) * (T / ((N+1:ℕ):ℝ)) = T := by field_simp
  rw [hT'] at k
  have e : (x' 0 - x' T) * (T / ((N+1:ℕ):ℝ)) = ((x' 0 - x' T) * T) / ((N+1:ℕ):ℝ) := by ring
  rw [e, le_div_iff₀ hMpos] at k
  rw [div_lt_iff₀ hDpos] at hN
  have : (N:ℝ) < ((N+1:ℕ):ℝ) := by push_cast; linarith
  nlinarith

lemma gi_update {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t) (i : Fin n)
    (b : CoreTask n ℓ → ℝ) (hb : ∀ g, 0 ≤ b g ∧ (¬ incident i g → b g = 0)) :
    IsGraphInput (Function.update t i b) := by
  intro u g
  by_cases hu : u = i
  · subst hu; simpa using hb g
  · rw [Function.update_of_ne hu]; exact ht u g

lemma inc_three {a b c : Fin n} {e : CoreTask n ℓ} (he : e.isLeft = true)
    (ha : incident a e) (hb : incident b e) (hc : incident c e)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  rcases e with ⟨q, k⟩ | k
  · simp only [incident] at ha hb hc
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
      first
      | exact hab (ha.trans hb.symm)
      | exact hac (ha.trans hc.symm)
      | exact hbc (hb.trans hc.symm)
  · simp at he

lemma sum_two (M : FracMech n (CoreTask n ℓ)) (hel : IsEligible M)
    {Y : Fin n → CoreTask n ℓ → ℝ} (hY : IsGraphInput Y) (i u0 : Fin n) (hne : i ≠ u0)
    (e0 : CoreTask n ℓ) (hL : e0.isLeft = true) (hi : incident i e0) (hu : incident u0 e0) :
    ∑ w, M.x Y w e0 = M.x Y i e0 + M.x Y u0 e0 := by
  rw [← Finset.sum_subset (Finset.subset_univ {i, u0}), Finset.sum_pair hne]
  intro w _ hw
  apply hel Y hY w e0
  intro hwi
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  exact inc_three hL hi hu hwi hne (Ne.symm hw.1) (Ne.symm hw.2)

lemma cross_mono (M : FracMech n (CoreTask n ℓ)) (hfeas : IsFeasibleOn IsGraphInput M)
    (htruth : IsTruthfulOn IsGraphInput M) (hel : IsEligible M)
    {X X2 : Fin n → CoreTask n ℓ → ℝ} (hX : IsGraphInput X) (hX2 : IsGraphInput X2)
    (i u0 : Fin n) (hne : i ≠ u0) (e0 : CoreTask n ℓ) (hL : e0.isLeft = true)
    (hi : incident i e0) (hag : ∀ u f, (u, f) ≠ (u0, e0) → X u f = X2 u f)
    (hle : X u0 e0 ≤ X2 u0 e0) : M.x X i e0 ≤ M.x X2 i e0 := by
  rcases hle.eq_or_lt with h | h
  · have : X = X2 := by
      funext u f
      by_cases hh : (u, f) = (u0, e0)
      · simp only [Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh; exact h
      · exact hag u f hh
    rw [this]
  · have hinc : incident u0 e0 := by
      by_contra hn
      have := (hX2 u0 e0).2 hn
      linarith [(hX u0 e0).1]
    have hX2eq : Function.update X u0 (X2 u0) = X2 := by
      funext u f
      by_cases hu : u = u0
      · subst hu; simp
      · rw [Function.update_of_ne hu]
        exact hag u f (fun hh => hu (Prod.mk.inj hh).1)
    have hs := sandwich M htruth u0 X (X2 u0) e0 hX (by rw [hX2eq]; exact hX2)
      (fun k hk => (hag u0 k (fun hh => hk (Prod.mk.inj hh).2)).symm)
    rw [hX2eq] at hs
    have hmono : M.x X2 u0 e0 ≤ M.x X u0 e0 := by
      have : (X2 u0 e0 - X u0 e0) * M.x X2 u0 e0 ≤ (X2 u0 e0 - X u0 e0) * M.x X u0 e0 :=
        hs.1.trans hs.2
      exact le_of_mul_le_mul_left this (by linarith)
    have s1 := (hfeas X hX).2 e0
    have s2 := (hfeas X2 hX2).2 e0
    rw [sum_two M hel hX i u0 hne e0 hL hi hinc] at s1
    rw [sum_two M hel hX2 i u0 hne e0 hL hi hinc] at s2
    linarith

lemma path_sandwich (M : FracMech n (CoreTask n ℓ)) (htruth : IsTruthfulOn IsGraphInput M)
    (i : Fin n) (t : Fin n → CoreTask n ℓ → ℝ) (A : ℝ → CoreTask n ℓ → ℝ) (f : CoreTask n ℓ)
    (hAdef : ∀ θ g, g ≠ f → A θ g = A 0 g) (hAf : ∀ θ, A θ f = θ)
    (hgi : ∀ θ, 0 ≤ θ → IsGraphInput (Function.update t i (A θ))) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    (b - a) * M.x (Function.update t i (A b)) i f ≤
        disutility M (Function.update t i (A b)) i - disutility M (Function.update t i (A a)) i ∧
    disutility M (Function.update t i (A b)) i - disutility M (Function.update t i (A a)) i ≤
        (b - a) * M.x (Function.update t i (A a)) i f := by
  have hs := sandwich M htruth i (Function.update t i (A a)) (A b) f (hgi a ha)
    (by rw [Function.update_idem]; exact hgi b (ha.trans hab))
    (fun k hk => by simp [hAdef b k hk, hAdef a k hk])
  rw [Function.update_idem] at hs
  simpa [hAf] using hs

lemma dis_zero (M : FracMech n (CoreTask n ℓ)) (t : Fin n → CoreTask n ℓ → ℝ) (i : Fin n) :
    disutility M (Function.update t i 0) i = 0 := by
  unfold disutility; simp


lemma single_step (M : FracMech n (CoreTask n ℓ)) (hfeas : IsFeasibleOn IsGraphInput M)
    (htruth : IsTruthfulOn IsGraphInput M) (hel : IsEligible M) (hzti : HasZeroTypeIrrelevance M)
    (i u0 : Fin n) (hne : u0 ≠ i) (e0 : CoreTask n ℓ) (hL : e0.isLeft = true)
    (hi : incident i e0) (t t2 : Fin n → CoreTask n ℓ → ℝ)
    (ht : IsGraphInput t) (ht2 : IsGraphInput t2)
    (hag : ∀ u f, (u, f) ≠ (u0, e0) → t u f = t2 u f) (hle : t u0 e0 ≤ t2 u0 e0) :
    disutility M t i ≤ disutility M t2 i := by
  have hrow : t2 i = t i := funext fun f =>
    (hag i f (fun h => hne (Prod.mk.inj h).1.symm)).symm
  let rowS : Finset (CoreTask n ℓ) → CoreTask n ℓ → ℝ := fun S f => if f ∈ S then t i f else 0
  have rowS_ok : ∀ S g, 0 ≤ rowS S g ∧ (¬ incident i g → rowS S g = 0) := by
    intro S g
    by_cases hg : g ∈ S
    · simp only [rowS, hg, if_true]; exact ⟨(ht i g).1, (ht i g).2⟩
    · simp [rowS, hg]
  have C : ∀ S : Finset (CoreTask n ℓ), e0 ∉ S →
      disutility M (Function.update t i (rowS S)) i =
        disutility M (Function.update t2 i (rowS S)) i := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      have : rowS ∅ = 0 := by funext g; simp [rowS]
      rw [this, dis_zero, dis_zero]
    | insert f S hf ih =>
      intro he0
      have hfe : f ≠ e0 := fun h => he0 (h ▸ Finset.mem_insert_self _ _)
      have he0S : e0 ∉ S := fun h => he0 (Finset.mem_insert_of_mem h)
      have ihS := ih he0S
      by_cases hr : t i f = 0
      · have : rowS (insert f S) = rowS S := by
          funext g
          by_cases hg : g = f
          · subst hg; simp [rowS, hr]
          · simp [rowS, hg]
        rw [this]; exact ihS
      · have hrpos : 0 < t i f := lt_of_le_of_ne (ht i f).1 (Ne.symm hr)
        have hfi : incident i f := by
          by_contra hn; exact hr ((ht i f).2 hn)
        let A : ℝ → CoreTask n ℓ → ℝ := fun θ => Function.update (rowS S) f θ
        have hAdef : ∀ θ g, g ≠ f → A θ g = A 0 g := by
          intro θ g hg; simp [A, Function.update_of_ne hg]
        have hAf : ∀ θ, A θ f = θ := by intro θ; simp [A]
        have hA : ∀ θ, 0 ≤ θ → ∀ g, 0 ≤ A θ g ∧ (¬ incident i g → A θ g = 0) := by
          intro θ h0 g
          by_cases hg : g = f
          · subst hg; exact ⟨by simpa [A] using h0, fun h => absurd hfi h⟩
          · simp only [A, Function.update_of_ne hg]; exact rowS_ok S g
        have hgi1 : ∀ θ, 0 ≤ θ → IsGraphInput (Function.update t i (A θ)) :=
          fun θ h0 => gi_update ht i _ (hA θ h0)
        have hgi2 : ∀ θ, 0 ≤ θ → IsGraphInput (Function.update t2 i (A θ)) :=
          fun θ h0 => gi_update ht2 i _ (hA θ h0)
        have hz : ∀ θ, A θ e0 = 0 := by
          intro θ; simp [A, Function.update_of_ne (Ne.symm hfe), rowS, he0S]
        have hxeq : ∀ θ, 0 ≤ θ → M.x (Function.update t i (A θ)) i f =
            M.x (Function.update t2 i (A θ)) i f := by
          intro θ h0
          refine hzti _ _ (hgi1 θ h0) (hgi2 θ h0) e0 hL ?_ ⟨i, hi, by simp [hz]⟩
            ⟨i, hi, by simp [hz]⟩ i f hfe
          intro u g hg
          by_cases hu : u = i
          · subst hu; simp
          · rw [Function.update_of_ne hu, Function.update_of_ne hu]
            exact hag u g (fun h => hg (Prod.mk.inj h).2)
        have hrf : (0:ℝ) ≤ t i f := hrpos.le
        have ineq : ∀ (t₁ t₂ : Fin n → CoreTask n ℓ → ℝ),
            (∀ θ, 0 ≤ θ → IsGraphInput (Function.update t₁ i (A θ))) →
            (∀ θ, 0 ≤ θ → IsGraphInput (Function.update t₂ i (A θ))) →
            (∀ θ, 0 ≤ θ → θ ≤ t i f → M.x (Function.update t₁ i (A θ)) i f =
              M.x (Function.update t₂ i (A θ)) i f) →
            disutility M (Function.update t₁ i (A (t i f))) i -
                disutility M (Function.update t₁ i (A 0)) i ≤
              disutility M (Function.update t₂ i (A (t i f))) i -
                disutility M (Function.update t₂ i (A 0)) i := by
          intro t₁ t₂ g1 g2 hx
          refine riemann (t i f) hrf
            (fun θ => disutility M (Function.update t₁ i (A θ)) i)
            (fun θ => disutility M (Function.update t₂ i (A θ)) i)
            (fun θ => M.x (Function.update t₁ i (A θ)) i f)
            (fun θ => M.x (Function.update t₂ i (A θ)) i f) ?_ ?_ ?_
          · intro a b ha hab _
            exact (path_sandwich M htruth i t₁ A f hAdef hAf g1 ha hab).2
          · intro a b ha hab _
            exact (path_sandwich M htruth i t₂ A f hAdef hAf g2 ha hab).1
          · intro a ha hb; exact (hx a ha hb).le
        have i1 := ineq t t2 hgi1 hgi2 (fun θ h0 _ => hxeq θ h0)
        have i2 := ineq t2 t hgi2 hgi1 (fun θ h0 _ => (hxeq θ h0).symm)
        have eA0 : A 0 = rowS S := by
          funext g
          by_cases hg : g = f
          · subst hg; simp [A, rowS, hf]
          · simp [A, Function.update_of_ne hg]
        have eA1 : A (t i f) = rowS (insert f S) := by
          funext g
          by_cases hg : g = f
          · subst hg; simp [A, rowS]
          · simp [A, Function.update_of_ne hg, rowS, hg]
        rw [eA0, eA1] at i1 i2
        linarith
  -- last coordinate
  let S0 : Finset (CoreTask n ℓ) := Finset.univ.erase e0
  have hS0 : e0 ∉ S0 := by simp [S0]
  let A : ℝ → CoreTask n ℓ → ℝ := fun θ => Function.update (rowS S0) e0 θ
  have hAdef : ∀ θ g, g ≠ e0 → A θ g = A 0 g := by
    intro θ g hg; simp [A, Function.update_of_ne hg]
  have hAf : ∀ θ, A θ e0 = θ := by intro θ; simp [A]
  have hA : ∀ θ, 0 ≤ θ → ∀ g, 0 ≤ A θ g ∧ (¬ incident i g → A θ g = 0) := by
    intro θ h0 g
    by_cases hg : g = e0
    · subst hg; exact ⟨by simpa [A] using h0, fun h => absurd hi h⟩
    · simp only [A, Function.update_of_ne hg]; exact rowS_ok S0 g
  have hgi1 : ∀ θ, 0 ≤ θ → IsGraphInput (Function.update t i (A θ)) :=
    fun θ h0 => gi_update ht i _ (hA θ h0)
  have hgi2 : ∀ θ, 0 ≤ θ → IsGraphInput (Function.update t2 i (A θ)) :=
    fun θ h0 => gi_update ht2 i _ (hA θ h0)
  have eA0 : A 0 = rowS S0 := by
    funext g
    by_cases hg : g = e0
    · subst hg; simp [A, rowS, hS0]
    · simp [A, Function.update_of_ne hg]
  have eA1 : A (t i e0) = t i := by
    funext g
    by_cases hg : g = e0
    · subst hg; simp [A]
    · simp [A, Function.update_of_ne hg, rowS, S0, hg]
  have hrf : (0:ℝ) ≤ t i e0 := (ht i e0).1
  have hmain := riemann (t i e0) hrf
    (fun θ => disutility M (Function.update t i (A θ)) i)
    (fun θ => disutility M (Function.update t2 i (A θ)) i)
    (fun θ => M.x (Function.update t i (A θ)) i e0)
    (fun θ => M.x (Function.update t2 i (A θ)) i e0)
    (fun a b ha hab _ => (path_sandwich M htruth i t A e0 hAdef hAf hgi1 ha hab).2)
    (fun a b ha hab _ => (path_sandwich M htruth i t2 A e0 hAdef hAf hgi2 ha hab).1)
    (fun a ha _ => by
      refine cross_mono M hfeas htruth hel (hgi1 a ha) (hgi2 a ha) i u0 hne.symm e0 hL hi ?_ ?_
      · intro u f huf
        by_cases hu : u = i
        · subst hu; simp
        · rw [Function.update_of_ne hu, Function.update_of_ne hu]; exact hag u f huf
      · rw [Function.update_of_ne hne, Function.update_of_ne hne]; exact hle)
  rw [eA0, eA1, C S0 hS0] at hmain
  rw [Function.update_eq_self, ← hrow, Function.update_eq_self] at hmain
  linarith

lemma chain (M : FracMech n (CoreTask n ℓ)) (hfeas : IsFeasibleOn IsGraphInput M)
    (htruth : IsTruthfulOn IsGraphInput M) (hel : IsEligible M) (hzti : HasZeroTypeIrrelevance M)
    (i : Fin n) (t t' : Fin n → CoreTask n ℓ → ℝ) (ht : IsGraphInput t) (ht' : IsGraphInput t')
    (hfix : ∀ u e, (u = i ∨ ¬ (e.isLeft ∧ incident i e)) → t u e = t' u e)
    (hle : ∀ u e, t u e ≤ t' u e) :
    disutility M t i ≤ disutility M t' i := by
  classical
  let D : Finset (Fin n × CoreTask n ℓ) := Finset.univ.filter (fun p => t p.1 p.2 ≠ t' p.1 p.2)
  let g : Finset (Fin n × CoreTask n ℓ) → Fin n → CoreTask n ℓ → ℝ :=
    fun S u e => if (u, e) ∈ S then t' u e else t u e
  have hg : ∀ S, IsGraphInput (g S) := by
    intro S u e
    by_cases h : (u, e) ∈ S
    · simp only [g, h, if_true]; exact ht' u e
    · simp only [g, h, if_false]; exact ht u e
  have hD : ∀ p ∈ D, p.1 ≠ i ∧ p.2.isLeft = true ∧ incident i p.2 := by
    intro p hp
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_contra hcon
    apply hp
    apply hfix
    by_cases h1 : p.1 = i
    · exact Or.inl h1
    · exact Or.inr (fun h => hcon ⟨h1, h.1, h.2⟩)
  have step : ∀ S : Finset (Fin n × CoreTask n ℓ), S ⊆ D →
      disutility M t i ≤ disutility M (g S) i := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      have : g ∅ = t := by funext u e; simp [g]
      rw [this]
    | insert p S hp ih =>
      intro hsub
      have ih' := ih (subset_trans (Finset.subset_insert _ _) hsub)
      refine ih'.trans ?_
      obtain ⟨u0, e0⟩ := p
      obtain ⟨h1, h2, h3⟩ := hD (u0, e0) (hsub (Finset.mem_insert_self _ _))
      refine single_step M hfeas htruth hel hzti i u0 h1 e0 h2 h3 (g S) (g (insert (u0, e0) S))
        (hg S) (hg _) ?_ ?_
      · intro u f huf
        simp [g, Finset.mem_insert, huf]
      · simp [g, hp]; exact hle _ _
  have gD : g D = t' := by
    funext u e
    by_cases h : (u, e) ∈ D
    · simp [g, h]
    · simp only [D, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at h
      simp [g, D, h]
  have := step D (Finset.Subset.refl _)
  rwa [gD] at this

end FracTruthSched.Dev.L4

namespace FracTruthSched

theorem chk_lemma_4 {n ℓ : ℕ} (hℓ : 2 ≤ ℓ) (M : FracMech n (CoreTask n ℓ))
    (hfeas : IsFeasibleOn IsGraphInput M) (htruth : IsTruthfulOn IsGraphInput M)
    (hel : IsEligible M) (hzti : HasZeroTypeIrrelevance M) (i : Fin n)
    (t t' : Fin n → CoreTask n ℓ → ℝ) (ht : IsGraphInput t) (ht' : IsGraphInput t')
    (hfix : ∀ u e, (u = i ∨ ¬ (e.isLeft ∧ incident i e)) → t u e = t' u e)
    (hle : ∀ u e, t u e ≤ t' u e) :
    disutility M t i ≤ disutility M t' i :=
  Dev.L4.chain M hfeas htruth hel hzti i t t' ht ht' hfix hle

end FracTruthSched
end

theorem solution : type_of% @FracTruthSched.chk_lemma_4 := @FracTruthSched.chk_lemma_4
