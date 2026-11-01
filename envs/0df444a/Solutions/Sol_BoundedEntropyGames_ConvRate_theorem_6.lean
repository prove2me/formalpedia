-- Prove2me | solution 1 for BoundedEntropyGames.ConvRate.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T13:12:43.383002+00:00
-- url     : https://prove2.me/submissions/cdcd2cea-dec0-4808-96ff-32095d6eea2c

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof
import Theorems.Thm_BoundedEntropyGames_ConvRate_lemma_16
import Theorems.Thm_BoundedEntropyGames_ConvRate_eq_31


open BoundedEntropyGames.ConvRate

/-! Part A: resampling identity for product measures. -/

theorem BGE6_sum_prod {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (w : ι → κ → ℝ) : ∑ f : ι → κ, ∏ i, w i (f i) = ∏ i, ∑ b, w i b := by
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset κ)), Fintype.piFinset_univ]

theorem BGE6_prod_extend {n N : ℕ} {Ω : Type*} (P : Fin n → Ω → ℝ) (e : Fin N → Fin n)
    (he : Function.Injective e) (z : Fin n → Ω) (u : Fin N → Ω) :
    ∏ t, P t (Function.extend e u z t) =
      (∏ l, P (e l) (u l)) * ∏ t ∈ (Finset.univ.image e)ᶜ, P t (z t) := by
  classical
  rw [← Finset.prod_mul_prod_compl (Finset.univ.image e), Finset.prod_image (fun x _ y _ h => he h)]
  congr 1
  · exact Finset.prod_congr rfl fun l _ => by rw [he.extend_apply]
  · refine Finset.prod_congr rfl fun t ht => ?_
    rw [Function.extend_apply']
    rintro ⟨l, rfl⟩
    simp at ht

theorem BGE6_prod_split {n N : ℕ} {Ω : Type*} (P : Fin n → Ω → ℝ) (e : Fin N → Fin n)
    (he : Function.Injective e) (z : Fin n → Ω) :
    ∏ t, P t (z t) = (∏ l, P (e l) (z (e l))) * ∏ t ∈ (Finset.univ.image e)ᶜ, P t (z t) := by
  classical
  rw [← Finset.prod_mul_prod_compl (Finset.univ.image e), Finset.prod_image (fun x _ y _ h => he h)]

theorem BGE6_resample {n N : ℕ} {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : Fin n → Ω → ℝ) (hP : ∀ t, ∑ ω, P t ω = 1) (e : Fin N → Fin n)
    (he : Function.Injective e) (F : (Fin n → Ω) → ℝ) :
    ∑ z, (∏ t, P t (z t)) * F z =
      ∑ z, (∏ t, P t (z t)) * ∑ u : Fin N → Ω, (∏ l, P (e l) (u l)) *
        F (Function.extend e u z) := by
  classical
  set W : (Fin n → Ω) → ℝ := fun z => ∏ t, P t (z t) with hW
  set We : (Fin N → Ω) → ℝ := fun u => ∏ l, P (e l) (u l) with hWe
  let Θ : (Fin n → Ω) × (Fin N → Ω) → (Fin n → Ω) × (Fin N → Ω) :=
    fun p => (Function.extend e p.2 p.1, p.1 ∘ e)
  have hext1 : ∀ (z : Fin n → Ω) (u : Fin N → Ω),
      Function.extend e (z ∘ e) (Function.extend e u z) = z := by
    intro z u
    funext t
    by_cases h : ∃ l, e l = t
    · obtain ⟨l, rfl⟩ := h
      rw [he.extend_apply]; rfl
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
  have hext2 : ∀ (z : Fin n → Ω) (u : Fin N → Ω), (Function.extend e u z) ∘ e = u := by
    intro z u; funext l; simp [he.extend_apply]
  have hΘ : Function.Involutive Θ := by
    intro p
    simp only [Θ, hext1, hext2]
  have hWe1 : ∑ u, We u = 1 := by
    simp only [hWe]
    rw [BGE6_sum_prod (fun l ω => P (e l) ω)]
    exact Finset.prod_eq_one fun l _ => hP (e l)
  set G : (Fin n → Ω) × (Fin N → Ω) → ℝ :=
    fun p => W p.1 * We p.2 * F (Function.extend e p.2 p.1) with hG
  have hRHS : ∑ z, W z * ∑ u, We u * F (Function.extend e u z) = ∑ p, G p := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [hG]; ring
  have hperm : ∑ p, G p = ∑ p, G (Θ p) :=
    (Fintype.sum_equiv (Function.Involutive.toPerm Θ hΘ) _ _ (fun p => rfl)).symm
  have hGΘ : ∀ p, G (Θ p) = W p.1 * We p.2 * F p.1 := by
    rintro ⟨z, u⟩
    simp only [hG, Θ, hext1]
    congr 1
    simp only [hW, hWe]
    rw [BGE6_prod_extend P e he z u, BGE6_prod_split P e he z]
    simp only [Function.comp]
    ring
  show ∑ z, W z * F z = ∑ z, W z * ∑ u, We u * F (Function.extend e u z)
  rw [hRHS, hperm]
  simp_rw [hGΘ]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  have : ∑ u, W z * We u * F z = W z * F z * ∑ u, We u := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
  simp only at this ⊢
  rw [this, hWe1, mul_one]

/-! Part B: plays against non-adaptive Alice strategies. -/

section game
variable {𝒜 ℬ 𝒳 𝒳' 𝒴 : Type*} {n : ℕ}

theorem BGE6_hist_eq (σ : AliceStrategy 𝒜 ℬ 𝒳 n) (σ' : AliceStrategy 𝒜 ℬ 𝒳' n)
    (τ : BobStrategy 𝒜 ℬ 𝒴 n) (xs : Fin n → 𝒳) (xs' : Fin n → 𝒳') (ys : Fin n → 𝒴) (K : ℕ)
    (h : ∀ k (hk : k + 1 ≤ n), k < K → ∀ hist,
      σ ⟨k, hk⟩ hist (fun j => xs ⟨j.1, lt_of_lt_of_le j.2 hk⟩) =
        σ' ⟨k, hk⟩ hist (fun j => xs' ⟨j.1, lt_of_lt_of_le j.2 hk⟩)) :
    ∀ k (hk : k ≤ n), k ≤ K → history σ τ xs ys k hk = history σ' τ xs' ys k hk := by
  intro k
  induction k with
  | zero => intro hk _; rfl
  | succ k ih =>
    intro hk hkK
    have ih' := ih (Nat.le_of_succ_le hk) (Nat.le_of_succ_le hkK)
    simp only [history]
    rw [ih', h k hk (Nat.lt_of_succ_le hkK)]

theorem BGE6_play_eq (σ : AliceStrategy 𝒜 ℬ 𝒳 n) (τ : BobStrategy 𝒜 ℬ 𝒴 n)
    (xs : Fin n → 𝒳) (ys : Fin n → 𝒴) (t : Fin n) :
    play σ τ xs ys t =
      (σ ⟨t.1, t.2⟩ (history σ τ xs ys t.1 (Nat.le_of_lt t.2))
          (fun j => xs ⟨j.1, lt_of_lt_of_le j.2 t.2⟩),
        τ ⟨t.1, t.2⟩ (history σ τ xs ys t.1 (Nat.le_of_lt t.2))
          (fun j => ys ⟨j.1, lt_of_lt_of_le j.2 t.2⟩)) := by
  unfold play
  simp only [history]
  rw [Fin.snoc_last]

/-- Alice strategy that plays a fixed action sequence. -/
def BGE6_fixA (a : Fin n → 𝒜) : AliceStrategy 𝒜 ℬ Unit n := fun t _ _ => a t

/-- Bob's response at stage `t` when Alice's actions are the fixed sequence `a`. -/
def BGE6_bob (τ : BobStrategy 𝒜 ℬ 𝒴 n) (a : Fin n → 𝒜) (ys : Fin n → 𝒴) (t : Fin n) : ℬ :=
  (play (BGE6_fixA (ℬ := ℬ) a) τ (fun _ => ()) ys t).2

theorem BGE6_play_split (σ : AliceStrategy 𝒜 ℬ 𝒳 n) (τ : BobStrategy 𝒜 ℬ 𝒴 n)
    (xs : Fin n → 𝒳) (ys : Fin n → 𝒴) (a : Fin n → 𝒜)
    (ha : ∀ k (hk : k + 1 ≤ n) hist,
      σ ⟨k, hk⟩ hist (fun j => xs ⟨j.1, lt_of_lt_of_le j.2 hk⟩) = a ⟨k, hk⟩) (t : Fin n) :
    play σ τ xs ys t = (a t, BGE6_bob τ a ys t) := by
  have hh := BGE6_hist_eq σ (BGE6_fixA (ℬ := ℬ) a) τ xs (fun _ => ()) ys n
    (fun k hk _ hist => by rw [ha k hk hist]; rfl)
  unfold BGE6_bob
  rw [BGE6_play_eq, BGE6_play_eq, hh t.1 (Nat.le_of_lt t.2) (Nat.le_of_lt t.2), ha]

theorem BGE6_bob_pred (τ : BobStrategy 𝒜 ℬ 𝒴 n) (a a' : Fin n → 𝒜) (ys : Fin n → 𝒴)
    (t : Fin n) (h : ∀ s : Fin n, s.1 < t.1 → a s = a' s) :
    BGE6_bob τ a ys t = BGE6_bob τ a' ys t := by
  have hh := BGE6_hist_eq (BGE6_fixA (ℬ := ℬ) a) (BGE6_fixA (ℬ := ℬ) a') τ (fun _ => ())
    (fun _ => ()) ys t.1 (fun k hk hkt hist => by
      simp only [BGE6_fixA]; exact h ⟨k, hk⟩ hkt)
  unfold BGE6_bob
  rw [BGE6_play_eq, BGE6_play_eq, hh t.1 (Nat.le_of_lt t.2) le_rfl]

end game


open BoundedEntropyGames.ConvRate

/-! Part C: the block strategy. -/

theorem BGE6_idx_lt {t N l : ℕ} (hN : 0 < N) (h1 : 1 ≤ t / N) (hl : l < N) :
    (t / N - 1) * N + l < t / N * N := by
  obtain ⟨q, hq⟩ : ∃ q, t / N = q + 1 := ⟨t / N - 1, by omega⟩
  rw [hq, Nat.add_sub_cancel, Nat.succ_mul]
  omega

theorem BGE6_idx_lt' {t N l : ℕ} (hN : 0 < N) (h1 : 1 ≤ t / N) (hl : l < N) :
    (t / N - 1) * N + l < t + 1 :=
  lt_of_lt_of_le (BGE6_idx_lt hN h1 hl) (Nat.lt_succ_of_le (Nat.div_mul_le_self t N)).le

section strat
variable {𝒜 ℬ 𝒳 𝒴 : Type*} {n : ℕ}

/-- Alice's actions as a function of the whole source sequence: in block `i` (`1 ≤ i < F`),
position `j`, play `φ(x-block i-1)_j`; otherwise `a0`. -/
def BGE6_alpha (N F : ℕ) (hN : 0 < N) (φ : (Fin N → 𝒳) → (Fin N → 𝒜)) (a0 : 𝒜)
    (xs : Fin n → 𝒳) (t : Fin n) : 𝒜 :=
  if h : 1 ≤ t.1 / N ∧ t.1 / N < F then
    φ (fun l : Fin N => xs ⟨(t.1 / N - 1) * N + l.1,
      lt_of_lt_of_le (BGE6_idx_lt' hN h.1 l.2) t.2⟩) ⟨t.1 % N, Nat.mod_lt _ hN⟩
  else a0

theorem BGE6_alpha_congr (N F : ℕ) (hN : 0 < N) (φ : (Fin N → 𝒳) → (Fin N → 𝒜)) (a0 : 𝒜)
    (xs xs' : Fin n → 𝒳) (t : Fin n) (h : ∀ r : Fin n, r.1 < t.1 / N * N → xs r = xs' r) :
    BGE6_alpha N F hN φ a0 xs t = BGE6_alpha N F hN φ a0 xs' t := by
  unfold BGE6_alpha
  split_ifs with h1
  · congr 1
    funext l
    exact h _ (BGE6_idx_lt hN h1.1 l.2)
  · rfl

theorem BGE6_alpha_block (N F : ℕ) (hN : 0 < N) (φ : (Fin N → 𝒳) → (Fin N → 𝒜)) (a0 : 𝒜)
    (xs : Fin n → 𝒳) (i : ℕ) (hi1 : 1 ≤ i) (hiF : i < F) (e : Fin N → Fin n)
    (he : ∀ l, (e l).1 = (i - 1) * N + l.1) (t : Fin n) (j : Fin N) (ht : t.1 = i * N + j.1) :
    BGE6_alpha N F hN φ a0 xs t = φ (xs ∘ e) j := by
  have hdiv : t.1 / N = i := by
    rw [ht, Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt j.2, zero_add]
  have hmod : t.1 % N = j.1 := by
    rw [ht, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]
  unfold BGE6_alpha
  rw [dif_pos (by rw [hdiv]; exact ⟨hi1, hiF⟩)]
  congr 1
  · funext l
    simp only [Function.comp]
    congr 1
    ext
    show (t.1 / N - 1) * N + l.1 = (e l).1
    rw [he, hdiv]
  · ext; exact hmod

/-- Alice's strategy: extend the observed prefix arbitrarily and apply `BGE6_alpha`. -/
def BGE6_sigma (N F : ℕ) (hN : 0 < N) (φ : (Fin N → 𝒳) → (Fin N → 𝒜)) (a0 : 𝒜) (x0 : 𝒳) :
    AliceStrategy 𝒜 ℬ 𝒳 n :=
  fun t _ pre => BGE6_alpha N F hN φ a0
    (fun r : Fin n => if h : r.1 < t.1 + 1 then pre ⟨r.1, h⟩ else x0) t

theorem BGE6_sigma_spec (N F : ℕ) (hN : 0 < N) (φ : (Fin N → 𝒳) → (Fin N → 𝒜)) (a0 : 𝒜)
    (x0 : 𝒳) (xs : Fin n → 𝒳) :
    ∀ k (hk : k + 1 ≤ n) hist,
      (BGE6_sigma (ℬ := ℬ) N F hN φ a0 x0) ⟨k, hk⟩ hist
        (fun j => xs ⟨j.1, lt_of_lt_of_le j.2 hk⟩) = BGE6_alpha N F hN φ a0 xs ⟨k, hk⟩ := by
  intro k hk hist
  unfold BGE6_sigma
  apply BGE6_alpha_congr
  intro r hr
  have : r.1 < k + 1 := lt_of_lt_of_le hr (le_trans (Nat.div_mul_le_self k N) (Nat.le_succ k))
  simp only [dif_pos this]

end strat


open BoundedEntropyGames.ConvRate

/-! Part D: the per-block bound. -/

theorem BGE6_U_le {𝒜 ℬ : Type*} [Fintype 𝒜] [Fintype ℬ] [Nonempty ℬ] (u : 𝒜 → ℬ → ℝ)
    (p : 𝒜 → ℝ) (b : ℬ) : U u p ≤ ∑ a, p a * u a b :=
  Finset.inf'_le _ (Finset.mem_univ b)

theorem BGE6_pred_prod {N : ℕ} {𝒜 ℬ : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Fintype ℬ]
    [Nonempty ℬ] (u : 𝒜 → ℬ → ℝ) (qs : Fin N → 𝒜 → ℝ) (hqs : ∀ j, IsPMF (qs j))
    (β : Fin N → (Fin N → 𝒜) → ℬ)
    (hβ : ∀ j c b, β j (Function.update c j b) = β j c) :
    ∑ j, U u (qs j) ≤ ∑ c : Fin N → 𝒜, (∏ k, qs k (c k)) * ∑ j, u (c j) (β j c) := by
  have hw1 : ∑ c : Fin N → 𝒜, ∏ k, qs k (c k) = 1 := by
    rw [BGE6_sum_prod (fun k a => qs k a)]
    exact Finset.prod_eq_one fun k _ => (hqs k).2
  have hw0 : ∀ c : Fin N → 𝒜, 0 ≤ ∏ k, qs k (c k) :=
    fun c => Finset.prod_nonneg fun k _ => (hqs k).1 _
  have swap : ∑ c : Fin N → 𝒜, (∏ k, qs k (c k)) * ∑ j, u (c j) (β j c) =
      ∑ j, ∑ c : Fin N → 𝒜, (∏ k, qs k (c k)) * u (c j) (β j c) := by
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
  rw [swap]
  refine Finset.sum_le_sum fun j _ => ?_
  -- resample coordinate j
  let e : Fin 1 → Fin N := fun _ => j
  have he : Function.Injective e := fun a b _ => Subsingleton.elim a b
  rw [BGE6_resample qs (fun k => (hqs k).2) e he (fun c => u (c j) (β j c))]
  have hext : ∀ (c : Fin N → 𝒜) (v : Fin 1 → 𝒜),
      Function.extend e v c = Function.update c j (v 0) := by
    intro c v
    funext s
    by_cases hs : s = j
    · subst hs
      rw [Function.update_self]
      exact he.extend_apply v c 0
    · rw [Function.update_of_ne hs, Function.extend_apply']
      rintro ⟨l, hl⟩; exact hs hl.symm
  have inner : ∀ c : Fin N → 𝒜, U u (qs j) ≤
      ∑ v : Fin 1 → 𝒜, (∏ l, qs (e l) (v l)) * u (Function.extend e v c j)
        (β j (Function.extend e v c)) := by
    intro c
    simp_rw [hext, Function.update_self, hβ, Fin.prod_univ_one]
    have : ∑ v : Fin 1 → 𝒜, qs (e 0) (v 0) * u (v 0) (β j c) = ∑ a, qs j a * u a (β j c) :=
      (Equiv.funUnique (Fin 1) 𝒜).sum_comp (fun a => qs j a * u a (β j c))
    rw [this]
    exact BGE6_U_le u (qs j) (β j c)
  calc U u (qs j) = ∑ c : Fin N → 𝒜, (∏ k, qs k (c k)) * U u (qs j) := by
        rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (inner c) (hw0 c)

theorem BGE6_couple {T : Type*} [Fintype T] (P1 P2 Ψ : T → ℝ) (C : ℝ)
    (hΨ : ∀ t, |Ψ t| ≤ C) : ∑ t, P2 t * Ψ t - 2 * C * tv P1 P2 ≤ ∑ t, P1 t * Ψ t := by
  have : ∑ t, P2 t * Ψ t - ∑ t, P1 t * Ψ t ≤ C * ∑ t, |P1 t - P2 t| := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    calc P2 t * Ψ t - P1 t * Ψ t = (P2 t - P1 t) * Ψ t := by ring
      _ ≤ |P2 t - P1 t| * |Ψ t| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ |P1 t - P2 t| * C := by
          rw [abs_sub_comm]; exact mul_le_mul_of_nonneg_left (hΨ t) (abs_nonneg _)
      _ = C * |P1 t - P2 t| := mul_comm _ _
  unfold tv
  linarith

theorem BGE6_ideal_sumU {𝒜 ℬ : Type*} [Fintype 𝒜] [Fintype ℬ] [Nonempty ℬ]
    (u : 𝒜 → ℬ → ℝ) (p₁ p₂ : 𝒜 → ℝ) (m N : ℕ) (hm : m ≤ N) :
    ∑ j : Fin N, U u (if j.1 < m then p₁ else p₂) = m * U u p₁ + ((N : ℝ) - m) * U u p₂ := by
  have e : ∀ j : Fin N, U u (if j.1 < m then p₁ else p₂) =
      if j.1 < m then U u p₁ else U u p₂ := fun j => by split_ifs <;> rfl
  simp_rw [e]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, Fin.card_filter_val_lt]
  have hc : (Finset.univ.filter (fun t : Fin N => ¬ (t : ℕ) < m)).card = N - m := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin N))) (fun t : Fin N => (t : ℕ) < m)
    rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin] at this
    omega
  rw [hc, min_eq_right hm, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub hm]


open BoundedEntropyGames.ConvRate

theorem BGE6_iid_sum {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (pXY : 𝒳 × 𝒴 → ℝ)
    (hp : IsPMF pXY) (n : ℕ) : ∑ z : Fin n → 𝒳 × 𝒴, ∏ t, pXY (z t) = 1 := by
  classical
  rw [BGE6_sum_prod (fun _ ω => pXY ω)]
  exact Finset.prod_eq_one fun _ _ => hp.2

theorem BGE6_iid_pair_sum {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (pXY : 𝒳 × 𝒴 → ℝ)
    (hp : IsPMF pXY) (N : ℕ) (G : (Fin N → 𝒳) → (Fin N → 𝒴) → ℝ) :
    ∑ v : Fin N → 𝒳 × 𝒴, (∏ l, pXY (v l)) * G (fun l => (v l).1) (fun l => (v l).2) =
      ∑ x' : Fin N → 𝒳, ∑ y' : Fin N → 𝒴, iidJoint pXY N (x', y') * G x' y' := by
  have := (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => 𝒳) (fun _ => 𝒴)).symm.sum_comp
    (fun v => (∏ l, pXY (v l)) * G (fun l => (v l).1) (fun l => (v l).2))
  rw [← this, Fintype.sum_prod_type]
  rfl

theorem BGE6_iid_pmf' {𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] (pXY : 𝒳 × 𝒴 → ℝ)
    (hp : IsPMF pXY) (N : ℕ) : IsPMF (iidJoint pXY N) := by
  refine ⟨fun z => Finset.prod_nonneg fun t _ => hp.1 _, ?_⟩
  have := BGE6_iid_pair_sum pXY hp N (fun _ _ => 1)
  simp only [mul_one] at this
  rw [Fintype.sum_prod_type, ← this]
  exact BGE6_iid_sum pXY hp N

theorem BGE6_block {𝒜 ℬ 𝒳 𝒴 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Fintype ℬ] [Nonempty ℬ]
    [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒴] [DecidableEq 𝒴] {n : ℕ}
    (u : 𝒜 → ℬ → ℝ) (M : ℝ) (hM : ∀ a b, |u a b| ≤ M)
    (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY)
    (N F : ℕ) (hN : 0 < N) (φ : (Fin N → 𝒳) → (Fin N → 𝒜)) (a0 : 𝒜)
    (τ : BobStrategy 𝒜 ℬ 𝒴 n)
    (p₁ p₂ : 𝒜 → ℝ) (h₁ : IsPMF p₁) (h₂ : IsPMF p₂) (m : ℕ) (hm : m ≤ N) (δ : ℝ)
    (hδ : tv (pfXY (iidJoint pXY N) φ)
      (fun z => idealBlock p₁ p₂ m N z.1 * marginalY (iidJoint pXY N) z.2) ≤ δ)
    (i : ℕ) (hi1 : 1 ≤ i) (hiF : i < F) (e sB : Fin N → Fin n)
    (he : ∀ l, (e l).1 = (i - 1) * N + l.1) (hsB : ∀ j, (sB j).1 = i * N + j.1) :
    (m : ℝ) * U u p₁ + ((N : ℝ) - m) * U u p₂ - 2 * N * M * δ ≤
      ∑ z : Fin n → 𝒳 × 𝒴, (∏ t, pXY (z t)) *
        ∑ j : Fin N, u (BGE6_alpha N F hN φ a0 (fun t => (z t).1) (sB j))
          (BGE6_bob τ (BGE6_alpha N F hN φ a0 (fun t => (z t).1)) (fun t => (z t).2) (sB j)) := by
  classical
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a0 (Classical.arbitrary ℬ))
  set B0 : ℝ := (m : ℝ) * U u p₁ + ((N : ℝ) - m) * U u p₂ with hB0
  set alpha := BGE6_alpha (n := n) N F hN φ a0 with halpha
  have he_inj : Function.Injective e := by
    intro l l' h
    have := congrArg Fin.val h
    rw [he, he] at this
    exact Fin.ext (by omega)
  set Fi : (Fin n → 𝒳 × 𝒴) → ℝ := fun z => ∑ j : Fin N, u (alpha (fun t => (z t).1) (sB j))
      (BGE6_bob τ (alpha (fun t => (z t).1)) (fun t => (z t).2) (sB j)) with hFi
  show B0 - 2 * N * M * δ ≤ ∑ z, (∏ t, pXY (z t)) * Fi z
  rw [BGE6_resample (fun _ => pXY) (fun _ => hp.2) e he_inj Fi]
  -- the bound for each fixed outer sample `z`
  suffices key : ∀ z : Fin n → 𝒳 × 𝒴, B0 - 2 * N * M * δ ≤
      ∑ v : Fin N → 𝒳 × 𝒴, (∏ l, pXY (v l)) * Fi (Function.extend e v z) by
    calc B0 - 2 * N * M * δ = ∑ z : Fin n → 𝒳 × 𝒴, (∏ t, pXY (z t)) * (B0 - 2 * N * M * δ) := by
          rw [← Finset.sum_mul, BGE6_iid_sum pXY hp n, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (key z)
          (Finset.prod_nonneg fun t _ => hp.1 _)
  intro z
  -- modified action sequence and Bob's sources
  let ã : (Fin N → 𝒜) → Fin n → 𝒜 := fun c s =>
    if h : i * N ≤ s.1 ∧ s.1 < i * N + N then c ⟨s.1 - i * N, by omega⟩
    else alpha (fun t => (z t).1) s
  let Yext : (Fin N → 𝒴) → Fin n → 𝒴 := fun y' => Function.extend e y' (fun t => (z t).2)
  let Ψ : (Fin N → 𝒜) → (Fin N → 𝒴) → ℝ := fun c y' =>
    ∑ j : Fin N, u (c j) (BGE6_bob τ (ã c) (Yext y') (sB j))
  -- Claim 1
  have claim1 : ∀ v : Fin N → 𝒳 × 𝒴, Fi (Function.extend e v z) =
      Ψ (φ (fun l => (v l).1)) (fun l => (v l).2) := by
    intro v
    set zz := Function.extend e v z with hzz
    have hxe : (fun t => (zz t).1) ∘ e = fun l => (v l).1 := by
      funext l; simp [hzz, he_inj.extend_apply]
    have hys : (fun t => (zz t).2) = Yext (fun l => (v l).2) := by
      funext t
      by_cases h : ∃ l, e l = t
      · obtain ⟨l, rfl⟩ := h
        simp [hzz, Yext, he_inj.extend_apply]
      · simp only [hzz, Yext, Function.extend_apply' _ _ _ h]
    have hblock : ∀ (t : Fin n) (j : Fin N), t.1 = i * N + j.1 →
        alpha (fun t => (zz t).1) t = φ (fun l => (v l).1) j := by
      intro t j ht
      rw [halpha, BGE6_alpha_block N F hN φ a0 _ i hi1 hiF e he t j ht, hxe]
    simp only [hFi, Ψ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hblock (sB j) j (hsB j), hys]
    congr 1
    apply BGE6_bob_pred
    intro s hs
    rw [hsB] at hs
    simp only [ã]
    by_cases hsi : i * N ≤ s.1
    · rw [dif_pos ⟨hsi, by omega⟩]
      exact hblock s ⟨s.1 - i * N, by omega⟩ (by simp; omega)
    · rw [dif_neg (fun h => hsi h.1)]
      rw [halpha]
      apply BGE6_alpha_congr
      intro r hr
      have hsN : s.1 / N < i := (Nat.div_lt_iff_lt_mul hN).mpr (by omega)
      have hle : s.1 / N * N ≤ (i - 1) * N := Nat.mul_le_mul_right _ (by omega)
      have hnot : ¬∃ l, e l = r := by
        rintro ⟨l, rfl⟩
        rw [he] at hr; omega
      simp only [hzz, Function.extend_apply' _ _ _ hnot]
  simp_rw [claim1]
  rw [BGE6_iid_pair_sum pXY hp N (fun x' y' => Ψ (φ x') y')]
  have hiid := BGE6_iid_pmf' pXY hp N
  -- Claim 3: push forward through φ
  set P1 : (Fin N → 𝒜) × (Fin N → 𝒴) → ℝ := pfXY (iidJoint pXY N) φ with hP1
  set P2 : (Fin N → 𝒜) × (Fin N → 𝒴) → ℝ :=
    fun z => idealBlock p₁ p₂ m N z.1 * marginalY (iidJoint pXY N) z.2 with hP2
  have claim3 : ∑ x' : Fin N → 𝒳, ∑ y' : Fin N → 𝒴, iidJoint pXY N (x', y') * Ψ (φ x') y' =
      ∑ q, P1 q * Ψ q.1 q.2 := by
    symm
    rw [Fintype.sum_prod_type]
    have h1 : ∀ (c : Fin N → 𝒜) (y' : Fin N → 𝒴), P1 (c, y') * Ψ c y' =
        ∑ x' : Fin N → 𝒳, if φ x' = c then iidJoint pXY N (x', y') * Ψ (φ x') y' else 0 := by
      intro c y'
      simp only [hP1, pfXY, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x' _ => ?_
      split_ifs with h
      · rw [h]
      · simp
    simp_rw [h1]
    calc ∑ c : Fin N → 𝒜, ∑ y' : Fin N → 𝒴, ∑ x' : Fin N → 𝒳,
          (if φ x' = c then iidJoint pXY N (x', y') * Ψ (φ x') y' else 0)
        = ∑ c : Fin N → 𝒜, ∑ x' : Fin N → 𝒳, ∑ y' : Fin N → 𝒴,
          (if φ x' = c then iidJoint pXY N (x', y') * Ψ (φ x') y' else 0) :=
          Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = ∑ x' : Fin N → 𝒳, ∑ c : Fin N → 𝒜, ∑ y' : Fin N → 𝒴,
          (if φ x' = c then iidJoint pXY N (x', y') * Ψ (φ x') y' else 0) := Finset.sum_comm
      _ = ∑ x' : Fin N → 𝒳, ∑ y' : Fin N → 𝒴, ∑ c : Fin N → 𝒜,
          (if φ x' = c then iidJoint pXY N (x', y') * Ψ (φ x') y' else 0) :=
          Finset.sum_congr rfl fun x' _ => Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y' _ => ?_
          rw [Finset.sum_ite_eq]
          simp
  rw [claim3]
  -- Claim 4: coupling
  have hΨ : ∀ q : (Fin N → 𝒜) × (Fin N → 𝒴), |Ψ q.1 q.2| ≤ N * M := by
    intro q
    simp only [Ψ]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ j : Fin N, |u (q.1 j) (BGE6_bob τ (ã q.1) (Yext q.2) (sB j))|
        ≤ ∑ j : Fin N, M := Finset.sum_le_sum fun j _ => hM _ _
      _ = N * M := by simp
  have hcoup := BGE6_couple P1 P2 (fun q => Ψ q.1 q.2) (N * M) hΨ
  -- Claim 5: the ideal law secures B0
  have claim5 : B0 ≤ ∑ q, P2 q * Ψ q.1 q.2 := by
    have hmY0 : ∀ y', 0 ≤ marginalY (iidJoint pXY N) y' :=
      fun y' => Finset.sum_nonneg fun x _ => hiid.1 _
    have hmY1 : ∑ y', marginalY (iidJoint pXY N) y' = 1 := by
      unfold marginalY
      rw [Finset.sum_comm, ← Fintype.sum_prod_type' (f := fun x y => iidJoint pXY N (x, y))]
      exact hiid.2
    have inner : ∀ y' : Fin N → 𝒴, B0 ≤ ∑ c : Fin N → 𝒜, idealBlock p₁ p₂ m N c * Ψ c y' := by
      intro y'
      have hpp := BGE6_pred_prod u (fun j : Fin N => if j.1 < m then p₁ else p₂)
        (fun j => by split_ifs; exact h₁; exact h₂)
        (fun j c => BGE6_bob τ (ã c) (Yext y') (sB j)) (by
          intro j c b
          apply BGE6_bob_pred
          intro s hs
          rw [hsB] at hs
          simp only [ã]
          split_ifs with h
          · rw [Function.update_of_ne]
            intro hc
            have := congrArg Fin.val hc
            simp at this
            omega
          · rfl)
      rw [BGE6_ideal_sumU u p₁ p₂ m N hm] at hpp
      refine le_trans hpp (le_of_eq ?_)
      refine Finset.sum_congr rfl fun c _ => ?_
      congr 1
      unfold idealBlock
      refine Finset.prod_congr rfl fun k _ => ?_
      split_ifs <;> rfl
    calc B0 = ∑ y' : Fin N → 𝒴, marginalY (iidJoint pXY N) y' * B0 := by
          rw [← Finset.sum_mul, hmY1, one_mul]
      _ ≤ ∑ y' : Fin N → 𝒴, marginalY (iidJoint pXY N) y' *
            ∑ c : Fin N → 𝒜, idealBlock p₁ p₂ m N c * Ψ c y' :=
          Finset.sum_le_sum fun y' _ => mul_le_mul_of_nonneg_left (inner y') (hmY0 y')
      _ = ∑ q, P2 q * Ψ q.1 q.2 := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          refine Finset.sum_congr rfl fun y' _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [hP2]; ring
  have hNM : 0 ≤ (N : ℝ) * M := mul_nonneg (Nat.cast_nonneg _) hM0
  have : 2 * (N * M) * tv P1 P2 ≤ 2 * N * M * δ := by
    have := mul_le_mul_of_nonneg_left hδ (by linarith : (0 : ℝ) ≤ 2 * (N * M))
    linarith
  linarith


open BoundedEntropyGames.ConvRate

theorem BGE6_payoff_z {𝒜 ℬ 𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] {n : ℕ}
    (u : 𝒜 → ℬ → ℝ) (pXY : 𝒳 × 𝒴 → ℝ) (σ : AliceStrategy 𝒜 ℬ 𝒳 n)
    (τ : BobStrategy 𝒜 ℬ 𝒴 n) :
    payoff u pXY σ τ = ∑ z : Fin n → 𝒳 × 𝒴, (∏ t, pXY (z t)) *
      ((1 / (n : ℝ)) * ∑ t, u (play σ τ (fun t => (z t).1) (fun t => (z t).2) t).1
        (play σ τ (fun t => (z t).1) (fun t => (z t).2) t).2) := by
  unfold payoff
  rw [← Fintype.sum_prod_type' (f := fun xs ys => (∏ t, pXY (xs t, ys t)) *
      ((1 / (n : ℝ)) * ∑ t, u (play σ τ xs ys t).1 (play σ τ xs ys t).2))]
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => 𝒳) (fun _ => 𝒴)).sum_comp]
  rfl

theorem BGE6_payoff_ge {𝒜 ℬ 𝒳 𝒴 : Type*} [Fintype 𝒳] [Fintype 𝒴] {n : ℕ}
    (u : 𝒜 → ℬ → ℝ) (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) (σ : AliceStrategy 𝒜 ℬ 𝒳 n)
    (τ : BobStrategy 𝒜 ℬ 𝒴 n) (hn : 1 ≤ n) (c : ℝ)
    (h : ∀ xs ys t, c ≤ u (play σ τ xs ys t).1 (play σ τ xs ys t).2) :
    c ≤ payoff u pXY σ τ := by
  rw [BGE6_payoff_z]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hin : ∀ z : Fin n → 𝒳 × 𝒴, c ≤ (1 / (n : ℝ)) * ∑ t, u (play σ τ (fun t => (z t).1)
      (fun t => (z t).2) t).1 (play σ τ (fun t => (z t).1) (fun t => (z t).2) t).2 := by
    intro z
    have : ∑ _t : Fin n, c ≤ ∑ t, u (play σ τ (fun t => (z t).1)
      (fun t => (z t).2) t).1 (play σ τ (fun t => (z t).1) (fun t => (z t).2) t).2 :=
      Finset.sum_le_sum fun t _ => h _ _ t
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hn']
    linarith
  calc c = ∑ z : Fin n → 𝒳 × 𝒴, (∏ t, pXY (z t)) * c := by
        rw [← Finset.sum_mul, BGE6_iid_sum pXY hp n, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hin z)
        (Finset.prod_nonneg fun t _ => hp.1 _)

theorem BGE6_sum_range_mul (E : ℕ → ℝ) (F N : ℕ) :
    ∑ k ∈ Finset.range (F * N), E k = ∑ i ∈ Finset.range F, ∑ j ∈ Finset.range N, E (i * N + j) := by
  induction F with
  | zero => simp
  | succ F ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem BGE6_strategy_payoff {𝒜 ℬ 𝒳 𝒴 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Fintype ℬ]
    [Nonempty ℬ] [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒴] [DecidableEq 𝒴] {n : ℕ}
    (u : 𝒜 → ℬ → ℝ) (M : ℝ) (hM : ∀ a b, |u a b| ≤ M)
    (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY)
    (N F : ℕ) (hN : 0 < N) (hF : 1 ≤ F) (hFN : F * N ≤ n)
    (φ : (Fin N → 𝒳) → (Fin N → 𝒜)) (a0 : 𝒜) (x0 : 𝒳)
    (τ : BobStrategy 𝒜 ℬ 𝒴 n)
    (p₁ p₂ : 𝒜 → ℝ) (h₁ : IsPMF p₁) (h₂ : IsPMF p₂) (m : ℕ) (hm : m ≤ N) (δ : ℝ)
    (hδ : tv (pfXY (iidJoint pXY N) φ)
      (fun z => idealBlock p₁ p₂ m N z.1 * marginalY (iidJoint pXY N) z.2) ≤ δ) :
    -(N : ℝ) * M + ((F : ℝ) - 1) * ((m : ℝ) * U u p₁ + ((N : ℝ) - m) * U u p₂ - 2 * N * M * δ)
        - ((n : ℝ) - F * N) * M ≤
      (n : ℝ) * payoff u pXY (BGE6_sigma (ℬ := ℬ) N F hN φ a0 x0) τ := by
  classical
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a0 (Classical.arbitrary ℬ))
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
    hFN
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  set alpha := BGE6_alpha (n := n) N F hN φ a0 with halpha
  set B : ℝ := (m : ℝ) * U u p₁ + ((N : ℝ) - m) * U u p₂ - 2 * N * M * δ with hB
  -- per-stage expected payoff
  set E : Fin n → ℝ := fun t => ∑ z : Fin n → 𝒳 × 𝒴, (∏ s, pXY (z s)) *
    u (alpha (fun s => (z s).1) t) (BGE6_bob τ (alpha (fun s => (z s).1)) (fun s => (z s).2) t)
    with hE
  have hpay : (n : ℝ) * payoff u pXY (BGE6_sigma (ℬ := ℬ) N F hN φ a0 x0) τ = ∑ t, E t := by
    rw [BGE6_payoff_z]
    have hplay : ∀ (z : Fin n → 𝒳 × 𝒴) (t : Fin n),
        play (BGE6_sigma (ℬ := ℬ) N F hN φ a0 x0) τ (fun t => (z t).1) (fun t => (z t).2) t =
          (alpha (fun s => (z s).1) t, BGE6_bob τ (alpha (fun s => (z s).1)) (fun s => (z s).2) t) :=
      fun z t => BGE6_play_split _ τ _ _ _ (BGE6_sigma_spec N F hN φ a0 x0 _) t
    simp_rw [hplay]
    rw [Finset.mul_sum]
    simp only [hE]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.mul_sum]
    field_simp
  have hEge : ∀ t, -M ≤ E t := by
    intro t
    calc -M = ∑ z : Fin n → 𝒳 × 𝒴, (∏ s, pXY (z s)) * (-M) := by
          rw [← Finset.sum_mul, BGE6_iid_sum pXY hp n, one_mul]
      _ ≤ E t := Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
          (neg_le_of_abs_le (hM _ _)) (Finset.prod_nonneg fun s _ => hp.1 _)
  set E' : ℕ → ℝ := fun k => if h : k < n then E ⟨k, h⟩ else 0 with hE'
  have hE'ge : ∀ k, -M ≤ E' k := by
    intro k; simp only [hE']; split_ifs
    · exact hEge _
    · linarith
  have hsum : ∑ t, E t = ∑ k ∈ Finset.range n, E' k := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [hE', t.2]
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hsplit : ∑ k ∈ Finset.range n, E' k =
      (∑ i ∈ Finset.range F', ∑ j ∈ Finset.range N, E' ((i + 1) * N + j)) +
        ∑ j ∈ Finset.range N, E' (0 * N + j) +
        ∑ k ∈ Finset.range (n - (F' + 1) * N), E' ((F' + 1) * N + k) := by
    conv_lhs => rw [show n = (F' + 1) * N + (n - (F' + 1) * N) by omega]
    rw [Finset.sum_range_add, BGE6_sum_range_mul, Finset.sum_range_succ']
  -- the blocks
  have hblock : ∀ i ∈ Finset.range F', B ≤ ∑ j ∈ Finset.range N, E' ((i + 1) * N + j) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hlt : ∀ j : Fin N, (i + 1) * N + j.1 < n := by
      intro j
      have : (i + 1) * N + j.1 < (i + 2) * N := by
        rw [show (i + 2) * N = (i + 1) * N + N by ring]; omega
      have : (i + 2) * N ≤ (F' + 1) * N := Nat.mul_le_mul_right _ (by omega)
      omega
    have hlt' : ∀ l : Fin N, i * N + l.1 < n := by
      intro l; have := hlt l; nlinarith
    let sB : Fin N → Fin n := fun j => ⟨(i + 1) * N + j.1, hlt j⟩
    let e : Fin N → Fin n := fun l => ⟨i * N + l.1, hlt' l⟩
    have hb := BGE6_block u M hM pXY hp N (F' + 1) hN φ a0 τ p₁ p₂ h₁ h₂ m hm δ hδ (i + 1)
      (by omega) (by omega) e sB (fun l => by simp [e]) (fun j => rfl)
    rw [← Fin.sum_univ_eq_sum_range (fun j => E' ((i + 1) * N + j))]
    have : ∀ j : Fin N, E' ((i + 1) * N + j.1) = E (sB j) := by
      intro j; simp [hE', hlt j, sB]
    simp_rw [this]
    simp only [hE]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    exact hb
  have h1 : (F' : ℝ) * B ≤ ∑ i ∈ Finset.range F', ∑ j ∈ Finset.range N, E' ((i + 1) * N + j) := by
    have := Finset.sum_le_sum hblock
    simpa [Finset.sum_const, Finset.card_range] using this
  have h2 : -(N : ℝ) * M ≤ ∑ j ∈ Finset.range N, E' (0 * N + j) := by
    have := Finset.sum_le_sum (s := Finset.range N) fun j _ => hE'ge (0 * N + j)
    simpa using this
  have h3 : -((n : ℝ) - (F' + 1 : ℕ) * N) * M ≤
      ∑ k ∈ Finset.range (n - (F' + 1) * N), E' ((F' + 1) * N + k) := by
    have := Finset.sum_le_sum (s := Finset.range (n - (F' + 1) * N))
      fun k _ => hE'ge ((F' + 1) * N + k)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    have hc : ((n - (F' + 1) * N : ℕ) : ℝ) = (n : ℝ) - (F' + 1 : ℕ) * N := by
      rw [Nat.cast_sub hFN, Nat.cast_mul]
    rw [hc] at this
    linarith
  rw [hpay, hsum, hsplit]
  have : ((F' + 1 : ℕ) : ℝ) - 1 = F' := by push_cast; ring
  rw [this]
  linarith


open BoundedEntropyGames.ConvRate

theorem BGE6_absle {𝒜 ℬ : Type*} [Fintype 𝒜] [Fintype ℬ] [Nonempty 𝒜] [Nonempty ℬ]
    (u : 𝒜 → ℬ → ℝ) (a : 𝒜) (b : ℬ) : |u a b| ≤ maxAbsPayoff u :=
  Finset.le_sup' (fun ab : 𝒜 × ℬ => |u ab.1 ab.2|) (Finset.mem_univ (a, b))

theorem BGE6_Jcav_le {𝒜 ℬ : Type*} [Fintype 𝒜] [Fintype ℬ] [Nonempty 𝒜] [Nonempty ℬ]
    (u : 𝒜 → ℬ → ℝ) (h : ℝ) : Jcav u h ≤ maxAbsPayoff u := by
  classical
  set M := maxAbsPayoff u
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _)
    (BGE6_absle u (Classical.arbitrary 𝒜) (Classical.arbitrary ℬ))
  have hU : ∀ p ∈ stdSimplex ℝ 𝒜, U u p ≤ M := by
    intro p hp
    refine le_trans (BGE6_U_le u p (Classical.arbitrary ℬ)) ?_
    calc ∑ a, p a * u a (Classical.arbitrary ℬ) ≤ ∑ a, p a * M :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
            (le_trans (le_abs_self _) (BGE6_absle u _ _)) (hp.1 a)
      _ = M := by rw [← Finset.sum_mul, hp.2, one_mul]
  have hJ : ∀ h', J u h' ≤ M := by
    intro h'
    unfold J
    apply Real.sSup_le _ hM0
    rintro _ ⟨p, hp, rfl⟩
    exact hU p hp.1
  unfold Jcav
  by_cases hb : BddBelow {c | ∃ g : ℝ → ℝ, ConcaveOn ℝ (Set.Ici 0) g ∧
      (∀ h' ≥ 0, J u h' ≤ g h') ∧ c = g h}
  · exact csInf_le hb ⟨fun _ => M, concaveOn_const _ (convex_Ici 0), fun h' _ => hJ h', rfl⟩
  · rw [Real.sInf_of_not_bddBelow hb]; exact hM0

theorem BGE6_U_single {𝒜 ℬ : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Fintype ℬ] [Nonempty ℬ]
    (u : 𝒜 → ℬ → ℝ) (a : 𝒜) (b : ℬ) : U u (Pi.single a (1 : ℝ)) ≤ u a b := by
  refine le_trans (BGE6_U_le u _ b) (le_of_eq ?_)
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [Pi.single_apply, hc]
  · simp

theorem BGE6_final_arith (n F N m : ℕ) (hF : 1 ≤ F) (hFn : F ≤ n) (hN : N = n / F)
    (M ΔU U1 U2 Jc r G δ pay : ℝ)
    (hM0 : 0 ≤ M) (hΔ : ΔU = |U1 - U2|) (hJc : Jc = r * U1 + (1 - r) * U2) (hJM : Jc ≤ M)
    (hG0 : 0 ≤ G) (hδ0 : 0 ≤ δ)
    (hm1 : (m : ℝ) ≤ N * (r - G)) (hm2 : (N : ℝ) * (r - G) < m + 1)
    (hpay : -(N : ℝ) * M + ((F : ℝ) - 1) * (m * U1 + ((N : ℝ) - m) * U2 - 2 * N * M * δ)
        - ((n : ℝ) - F * N) * M ≤ n * pay) :
    Jc - (2 * M + ΔU) * (1 / (n : ℝ) + 1 / (F : ℝ) + (F : ℝ) / n + G + δ) ≤ pay := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hFR : (1 : ℝ) ≤ F := by exact_mod_cast hF
  have hFpos : (0 : ℝ) < F := by linarith
  have hFN : (F : ℝ) * N ≤ n := by
    rw [hN]; exact_mod_cast Nat.mul_div_le n F
  have hrem : (n : ℝ) - F * N < F := by
    have h1 := Nat.div_add_mod n F
    have h2 := Nat.mod_lt n (show F > 0 by omega)
    rw [hN]
    have : (n : ℝ) = F * (n / F : ℕ) + (n % F : ℕ) := by exact_mod_cast h1.symm
    have h2' : ((n % F : ℕ) : ℝ) < F := by exact_mod_cast h2
    linarith
  have hNle : (N : ℝ) ≤ n / F := by rw [le_div_iff₀ hFpos]; linarith
  have hΔ0 : 0 ≤ ΔU := by rw [hΔ]; exact abs_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  -- (33): the per-block payoff is close to N·Jc
  have hB0 : (N : ℝ) * Jc - (G * N + 1) * ΔU ≤ m * U1 + ((N : ℝ) - m) * U2 := by
    have e : m * U1 + ((N : ℝ) - m) * U2 - N * Jc = ((m : ℝ) - r * N) * (U1 - U2) := by
      rw [hJc]; ring
    have habs : |(m : ℝ) - r * N| ≤ G * N + 1 := by
      rw [abs_le]; constructor <;> nlinarith
    have : -((G * N + 1) * ΔU) ≤ ((m : ℝ) - r * N) * (U1 - U2) := by
      have h1 := neg_abs_le (((m : ℝ) - r * N) * (U1 - U2))
      rw [abs_mul, ← hΔ] at h1
      have h2 : |(m : ℝ) - r * N| * ΔU ≤ (G * N + 1) * ΔU := mul_le_mul_of_nonneg_right habs hΔ0
      linarith
    linarith
  have hpay' : -(N : ℝ) * M + ((F : ℝ) - 1) * (N * Jc - (G * N + 1) * ΔU - 2 * N * M * δ)
      - ((n : ℝ) - F * N) * M ≤ n * pay := by
    have := mul_le_mul_of_nonneg_left hB0 (by linarith : (0 : ℝ) ≤ (F : ℝ) - 1)
    nlinarith
  -- bounds on the error contributions
  set R : ℝ := (n : ℝ) - ((F : ℝ) - 1) * N with hR
  have hR0 : 0 ≤ R := by rw [hR]; nlinarith
  have hRle : R ≤ F + n / F := by rw [hR]; linarith
  have k1 : R * Jc ≤ R * M := mul_le_mul_of_nonneg_left hJM hR0
  have k2 : R * M ≤ (F + n / F) * M := mul_le_mul_of_nonneg_right hRle hM0
  have hFN1 : ((F : ℝ) - 1) * N ≤ n := by nlinarith
  have k3 : ((F : ℝ) - 1) * N * (G * ΔU) ≤ n * (G * ΔU) :=
    mul_le_mul_of_nonneg_right hFN1 (mul_nonneg hG0 hΔ0)
  have k4 : ((F : ℝ) - 1) * ΔU ≤ F * ΔU := mul_le_mul_of_nonneg_right (by linarith) hΔ0
  have k5 : ((F : ℝ) - 1) * N * (M * δ) ≤ n * (M * δ) :=
    mul_le_mul_of_nonneg_right hFN1 (mul_nonneg hM0 hδ0)
  have k6 : 0 ≤ ΔU * (n / F) := mul_nonneg hΔ0 (div_nonneg hnR.le hFpos.le)
  have k7 : 0 ≤ ΔU * (n * δ) := mul_nonneg hΔ0 (mul_nonneg hnR.le hδ0)
  have k8 : 0 ≤ M * (n * G) := mul_nonneg hM0 (mul_nonneg hnR.le hG0)
  have main : (n : ℝ) * Jc - (2 * M + ΔU) * (1 + n / F + F + n * G + n * δ) ≤ n * pay := by
    have : (n : ℝ) * Jc - (2 * M + ΔU) * (1 + n / F + F + n * G + n * δ) ≤
        -(N : ℝ) * M + ((F : ℝ) - 1) * (N * Jc - (G * N + 1) * ΔU - 2 * N * M * δ)
          - ((n : ℝ) - F * N) * M := by
      have hRdef : (n : ℝ) = R + ((F : ℝ) - 1) * N := by rw [hR]; ring
      have hM2 : 0 ≤ 2 * M + ΔU := by linarith
      nlinarith
    linarith
  have hT : (n : ℝ) * ((2 * M + ΔU) * (1 / (n : ℝ) + 1 / (F : ℝ) + (F : ℝ) / n + G + δ)) =
      (2 * M + ΔU) * (1 + n / F + F + n * G + n * δ) := by
    field_simp
  have : (n : ℝ) * (Jc - (2 * M + ΔU) * (1 / (n : ℝ) + 1 / (F : ℝ) + (F : ℝ) / n + G + δ))
      ≤ n * pay := by
    rw [mul_sub, hT]; exact main
  exact le_of_mul_le_mul_left this hnR


open BoundedEntropyGames.ConvRate

/-- The constant strategy. -/
def BGE6_constA {𝒜 ℬ 𝒳 : Type*} (n : ℕ) (a : 𝒜) : AliceStrategy 𝒜 ℬ 𝒳 n := fun _ _ _ => a

theorem BGE6_div_bound (n F : ℕ) (hF : 1 ≤ F) : (n : ℝ) / F - 1 ≤ ((n / F : ℕ) : ℝ) := by
  have hFpos : (0 : ℝ) < F := by exact_mod_cast hF
  have h1 := Nat.div_add_mod n F
  have h2 := Nat.mod_lt n (show F > 0 by omega)
  have : (n : ℝ) = F * (n / F : ℕ) + (n % F : ℕ) := by exact_mod_cast h1.symm
  have h2' : ((n % F : ℕ) : ℝ) < F := by exact_mod_cast h2
  rw [sub_le_iff_le_add, div_le_iff₀ hFpos]
  nlinarith

theorem solution {𝒜 ℬ 𝒳 𝒴 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Nonempty 𝒜]
    [Fintype ℬ] [DecidableEq ℬ] [Nonempty ℬ] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype 𝒴] [DecidableEq 𝒴]
    (u : 𝒜 → ℬ → ℝ) (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) :
    ∃ r > (0 : ℝ), ∃ β > (0 : ℝ), ∃ γ ≥ (0 : ℝ), ∃ μ ≥ (0 : ℝ),
      ∀ (f : ℕ → ℕ) (g h : ℕ → ℝ), (∀ n, 1 ≤ f n) → (∀ n, 0 ≤ g n ∧ g n ≤ r) →
        (∀ n, 0 ≤ h n ∧ h n ≤ 1) →
        ∃ σ : (n : ℕ) → AliceStrategy 𝒜 ℬ 𝒳 n,
          ∀ (τ : (n : ℕ) → BobStrategy 𝒜 ℬ 𝒴 n) (n : ℕ), 1 ≤ n →
            Jcav u (condEntropy pXY) -
                μ * (1 / (n : ℝ) + 1 / (f n : ℝ) + (f n : ℝ) / n + g n +
                  (2 : ℝ) ^ (-(1 / 2) * ((n : ℝ) / f n - 1) * h n * (β * g n - γ * h n)))
              ≤ payoff u pXY (σ n) (τ n) := by
  classical
  set M := maxAbsPayoff u with hMdef
  have hM : ∀ a b, |u a b| ≤ M := BGE6_absle u
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (Classical.arbitrary 𝒜) (Classical.arbitrary ℬ))
  have hJM : Jcav u (condEntropy pXY) ≤ M := BGE6_Jcav_le u _
  obtain ⟨⟨x0, _⟩, -⟩ : ∃ z, 0 < pXY z := by
    by_contra hc
    push Not at hc
    have : ∑ t, pXY t ≤ 0 := Finset.sum_nonpos fun t _ => hc t
    linarith [hp.2]
  have a0 : 𝒜 := Classical.arbitrary 𝒜
  rcases lemma_16 u pXY hp with ⟨a, ha⟩ | ⟨r, hr, p₁, hp₁, p₂, hp₂, h18, h19, h20⟩
  · -- a pure action secures `J_cav(H(X|Y))`
    let σc : (n : ℕ) → AliceStrategy 𝒜 ℬ 𝒳 n := fun n _ _ _ => a
    refine ⟨1, one_pos, 1, one_pos, 0, le_rfl, 0, le_rfl, fun f g h _ _ _ =>
      ⟨σc, fun τ n hn => ?_⟩⟩
    rw [zero_mul, sub_zero]
    refine le_trans ha (BGE6_payoff_ge u pXY hp (σc n) (τ n) hn _ fun xs ys t => ?_)
    have e := BGE6_play_eq (σc n) (τ n) xs ys t
    rw [e]
    exact BGE6_U_single u a _
  · have hP₁ : IsPMF p₁ := ⟨hp₁.1, hp₁.2⟩
    have hP₂ : IsPMF p₂ := ⟨hp₂.1, hp₂.2⟩
    obtain ⟨γ, hγ, h31⟩ := eq_31 pXY hp r hr p₁ p₂ hP₁ hP₂ h19 h20
    set ΔU := |U u p₁ - U u p₂| with hΔ
    refine ⟨r, hr.1, shannon p₁ - shannon p₂, by linarith, γ, hγ, 2 * M + ΔU,
      by positivity, ?_⟩
    intro f g h hf hg hh
    choose φ hφ using h31
    refine ⟨fun n => if hc : f n ≤ n ∧ 0 < h n then
        BGE6_sigma (n / f n) (f n) (Nat.div_pos hc.1 (hf n))
          (φ n (f n) (hf n) hc.1 (g n) (Set.mem_Icc.mpr ⟨(hg n).1, (hg n).2⟩) (h n) (Set.mem_Ioc.mpr ⟨hc.2, (hh n).2⟩)
            (n / f n) (n / f n) le_rfl (BGE6_div_bound n (f n) (hf n))) a0 x0
      else BGE6_constA n a0, fun τ n hn => ?_⟩
    set T : ℝ := 1 / (n : ℝ) + 1 / (f n : ℝ) + (f n : ℝ) / n + g n +
      (2 : ℝ) ^ (-(1 / 2) * ((n : ℝ) / f n - 1) * h n *
        ((shannon p₁ - shannon p₂) * g n - γ * h n)) with hT
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hfR : (0 : ℝ) < f n := by exact_mod_cast hf n
    by_cases hc : f n ≤ n ∧ 0 < h n
    · dsimp only
      rw [dif_pos hc]
      set N := n / f n with hN
      set δ : ℝ := (2 : ℝ) ^ (-(1 / 2) * ((n : ℝ) / f n - 1) * h n *
        ((shannon p₁ - shannon p₂) * g n - γ * h n)) with hδ
      have hNpos : 0 < N := Nat.div_pos hc.1 (hf n)
      set m := ⌊(N : ℝ) * (r - g n)⌋₊ with hm
      have hrg : 0 ≤ r - g n := by linarith [(hg n).2]
      have hmN : m ≤ N := by
        apply Nat.floor_le_of_le
        have : r - g n ≤ 1 := by linarith [(hg n).1, hr.2]
        nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
      have hFN : f n * N ≤ n := by rw [hN, Nat.mul_comm]; exact Nat.div_mul_le_self n (f n)
      have hpay := BGE6_strategy_payoff (ℬ := ℬ) u M hM pXY hp N (f n) hNpos (hf n) hFN
        (φ n (f n) (hf n) hc.1 (g n) (Set.mem_Icc.mpr ⟨(hg n).1, (hg n).2⟩) (h n) (Set.mem_Ioc.mpr ⟨hc.2, (hh n).2⟩)
          N N le_rfl (BGE6_div_bound n (f n) (hf n))) a0 x0 (τ n) p₁ p₂ hP₁ hP₂ m hmN δ
        (hφ n (f n) (hf n) hc.1 (g n) (Set.mem_Icc.mpr ⟨(hg n).1, (hg n).2⟩) (h n) (Set.mem_Ioc.mpr ⟨hc.2, (hh n).2⟩)
          N N le_rfl (BGE6_div_bound n (f n) (hf n)))
      have hm1 : (m : ℝ) ≤ N * (r - g n) :=
        Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) hrg)
      have hm2 : (N : ℝ) * (r - g n) < m + 1 := Nat.lt_floor_add_one _
      exact BGE6_final_arith n (f n) N m (hf n) hc.1 rfl M ΔU (U u p₁) (U u p₂)
        (Jcav u (condEntropy pXY)) r (g n) δ _ hM0 rfl h18.symm hJM (hg n).1
        (Real.rpow_nonneg (by norm_num) _) hm1 hm2 hpay
    · -- trivial regime: the error term is at least 1
      dsimp only
      rw [dif_neg hc]
      have hpay := BGE6_payoff_ge u pXY hp (BGE6_constA (ℬ := ℬ) (𝒳 := 𝒳) n a0) (τ n) hn
        (-M) (fun xs ys t => neg_le_of_abs_le (hM _ _))
      have hT1 : 1 ≤ T := by
        have h2pos : 0 < (2 : ℝ) ^ (-(1 / 2) * ((n : ℝ) / f n - 1) * h n *
            ((shannon p₁ - shannon p₂) * g n - γ * h n)) := Real.rpow_pos_of_pos (by norm_num) _
        have h1n : 0 < 1 / (n : ℝ) := by positivity
        have h1f : 0 < 1 / (f n : ℝ) := by positivity
        have hfn0 : 0 ≤ (f n : ℝ) / n := by positivity
        have hg0 := (hg n).1
        rcases not_and_or.mp hc with hlt | hh0
        · have : (1 : ℝ) ≤ (f n : ℝ) / n := by
            rw [le_div_iff₀ hnR, one_mul]; push Not at hlt; exact_mod_cast hlt.le
          rw [hT]; linarith
        · have : h n = 0 := le_antisymm (not_lt.mp hh0) (hh n).1
          have : (2 : ℝ) ^ (-(1 / 2) * ((n : ℝ) / f n - 1) * h n *
              ((shannon p₁ - shannon p₂) * g n - γ * h n)) = 1 := by
            rw [this]; simp
          rw [hT, this]; linarith
      have hμ : 2 * M ≤ (2 * M + ΔU) * T := by
        have hΔ0 : 0 ≤ ΔU := abs_nonneg _
        nlinarith
      show Jcav u (condEntropy pXY) - (2 * M + ΔU) * T ≤ _
      linarith
