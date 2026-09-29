-- Prove2me | solution 1 for CompetitivePaging.LowerBound.no_competitive_below_harmonic_n_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:17:15.961272+00:00
-- url     : https://prove2.me/submissions/dd12ef92-2db0-488b-9a21-633dc7dd7a3a

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized



namespace CompetitivePaging.LowerBound

open KServer MeasureTheory Classical

section
variable {k : ℕ} {M : Type} [MetricSpace M]

lemma nch_cost_snoc (B : OnlineAlgorithm k M) (σ : List M) (x : M) :
    B.cost (σ ++ [x]) = B.cost σ + moveCost (B.conf σ) (B.conf (σ ++ [x])) := by
  unfold OnlineAlgorithm.cost
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length le_rfl, List.take_length,
      List.take_of_length_le (by simp)]

lemma nch_moveCost_nonneg (C C' : Config k M) : 0 ≤ moveCost C C' :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

lemma nch_cost_nonneg (B : OnlineAlgorithm k M) (σ : List M) : 0 ≤ B.cost σ :=
  Finset.sum_nonneg fun _ _ => nch_moveCost_nonneg _ _

noncomputable def nq (A : RandomizedAlgorithm k M) (σ : List M) (x : M) : ENNReal :=
  ∫⁻ ω, min 1 (ENNReal.ofReal (moveCost ((A.alg ω).conf σ) ((A.alg ω).conf (σ ++ [x])))) ∂A.μ

lemma nq_le_one (A : RandomizedAlgorithm k M) (σ : List M) (x : M) : nq A σ x ≤ 1 := by
  haveI := A.prob
  calc nq A σ x ≤ ∫⁻ _, 1 ∂A.μ := lintegral_mono fun _ => min_le_left _ _
    _ = 1 := by simp

lemma nch_exp_snoc (A : RandomizedAlgorithm k M) (σ : List M) (x : M) :
    A.expCost σ + nq A σ x ≤ A.expCost (σ ++ [x]) := by
  unfold RandomizedAlgorithm.expCost nq
  have : ∀ ω, ENNReal.ofReal ((A.alg ω).cost (σ ++ [x])) = ENNReal.ofReal ((A.alg ω).cost σ)
      + ENNReal.ofReal (moveCost ((A.alg ω).conf σ) ((A.alg ω).conf (σ ++ [x]))) := by
    intro ω
    rw [nch_cost_snoc, ENNReal.ofReal_add (nch_cost_nonneg _ _) (nch_moveCost_nonneg _ _)]
  simp_rw [this]
  rw [lintegral_add_left (A.meas σ).ennreal_ofReal]
  exact add_le_add le_rfl (lintegral_mono fun ω => min_le_right _ _)

noncomputable def qr (A : RandomizedAlgorithm k M) (σ : List M) (x : M) : ℝ := (nq A σ x).toReal

lemma qr_nonneg (A : RandomizedAlgorithm k M) (σ : List M) (x : M) : 0 ≤ qr A σ x :=
  ENNReal.toReal_nonneg

lemma nch_exp_snoc_real (A : RandomizedAlgorithm k M) (σ : List M) (x : M) :
    A.expCost σ + ENNReal.ofReal (qr A σ x) ≤ A.expCost (σ ++ [x]) := by
  unfold qr
  rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (nq_le_one A σ x))]
  exact nch_exp_snoc A σ x

lemma nch_sum_ge (A : RandomizedAlgorithm k M) (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (D : Finset M) (hD : D.card = k + 1) (σ : List M) :
    1 ≤ ∑ x ∈ D, nq A σ x := by
  letI := A.ms
  haveI := A.prob
  unfold nq
  have hmeas : ∀ x ∈ D, Measurable (fun ω => min 1 (ENNReal.ofReal
      (moveCost ((A.alg ω).conf σ) ((A.alg ω).conf (σ ++ [x]))))) := by
    intro x _
    have e : (fun ω => moveCost ((A.alg ω).conf σ) ((A.alg ω).conf (σ ++ [x])))
        = fun ω => (A.alg ω).cost (σ ++ [x]) - (A.alg ω).cost σ := by
      funext ω; rw [nch_cost_snoc]; ring
    have hm : Measurable (fun ω => moveCost ((A.alg ω).conf σ) ((A.alg ω).conf (σ ++ [x]))) := by
      rw [e]; exact (A.meas _).sub (A.meas _)
    exact measurable_const.min hm.ennreal_ofReal
  rw [← lintegral_finsetSum D hmeas]
  calc (1:ENNReal) = ∫⁻ _, 1 ∂A.μ := by simp
    _ ≤ _ := lintegral_mono fun ω => ?_
  obtain ⟨d, hdD, hdn⟩ : ∃ d ∈ D, d ∉ Set.range ((A.alg ω).conf σ) := by
    by_contra h
    push_neg at h
    have hsub : D ⊆ Finset.univ.image ((A.alg ω).conf σ) := by
      intro d hd'
      obtain ⟨j, hj⟩ := h d hd'
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := (A.alg ω).conf σ)
    simp at h2; omega
  refine le_trans ?_ (Finset.single_le_sum (f := fun x => min 1 (ENNReal.ofReal
    (moveCost ((A.alg ω).conf σ) ((A.alg ω).conf (σ ++ [x]))))) (fun _ _ => bot_le) hdD)
  obtain ⟨j, hj⟩ := (A.alg ω).serves σ d
  have h1 : 1 ≤ moveCost ((A.alg ω).conf σ) ((A.alg ω).conf (σ ++ [d])) := by
    have hne : (A.alg ω).conf σ j ≠ d := fun h => hdn ⟨j, h⟩
    calc (1:ℝ) = dist ((A.alg ω).conf σ j) ((A.alg ω).conf (σ ++ [d]) j) := by
          rw [hj, hd _ _ hne]
      _ ≤ _ := Finset.single_le_sum (f := fun i => dist ((A.alg ω).conf σ i)
          ((A.alg ω).conf (σ ++ [d]) i)) (fun _ _ => dist_nonneg) (Finset.mem_univ j)
  simp only
  rw [le_min_iff]
  exact ⟨le_rfl, by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1⟩

lemma nch_sum_ge_real (A : RandomizedAlgorithm k M) (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (D : Finset M) (hD : D.card = k + 1) (σ : List M) :
    1 ≤ ∑ x ∈ D, qr A σ x := by
  unfold qr
  rw [← ENNReal.toReal_sum (fun x _ => ne_top_of_le_ne_top ENNReal.one_ne_top (nq_le_one A σ x))]
  have hfin : ∑ x ∈ D, nq A σ x ≠ ⊤ :=
    ENNReal.sum_ne_top.2 (fun x _ => ne_top_of_le_ne_top ENNReal.one_ne_top (nq_le_one A σ x))
  have := ENNReal.toReal_mono hfin (nch_sum_ge A hd D hD σ)
  simpa using this

lemma nch_sub (A : RandomizedAlgorithm k M) (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (D : Finset M) (hD : D.card = k + 1) (Mk : Finset M) (hMk : Mk ⊆ D) (hMne : Mk.Nonempty)
    (hU : (D \ Mk).Nonempty) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ K : ℕ, ∀ σ : List M, ∃ τ₀ : List M, ∃ x : M, (∀ y ∈ τ₀, y ∈ Mk) ∧ x ∈ D \ Mk ∧
      A.expCost σ + ENNReal.ofReal (min ((1 - δ) / (D \ Mk).card) (K * δ / Mk.card))
        ≤ A.expCost (σ ++ τ₀ ++ [x]) := by
  have hUc : (0:ℝ) < (D \ Mk).card := by exact_mod_cast hU.card_pos
  have hMc : (0:ℝ) < Mk.card := by exact_mod_cast hMne.card_pos
  intro K
  induction K with
  | zero =>
    intro σ
    obtain ⟨x, hx⟩ := hU
    refine ⟨[], x, by simp, hx, ?_⟩
    have : min ((1-δ)/(D\Mk).card) (((0:ℕ):ℝ)*δ/Mk.card) ≤ 0 := min_le_of_right_le (by simp)
    rw [ENNReal.ofReal_of_nonpos this, add_zero]
    simpa using le_trans le_self_add (nch_exp_snoc_real A σ x)
  | succ K ih =>
    intro σ
    by_cases hs : ∑ y ∈ Mk, qr A σ y < δ
    · have htot := nch_sum_ge_real A hd D hD σ
      have hsplit := Finset.sum_sdiff hMk (f := qr A σ)
      obtain ⟨x, hx, hxq⟩ : ∃ x ∈ D \ Mk, (1-δ)/(D\Mk).card ≤ qr A σ x := by
        apply Finset.exists_le_of_sum_le hU
        rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hUc.ne']
        linarith
      refine ⟨[], x, by simp, hx, ?_⟩
      calc _ ≤ A.expCost σ + ENNReal.ofReal (qr A σ x) := by
            gcongr; exact min_le_of_left_le hxq
        _ ≤ _ := by simpa using nch_exp_snoc_real A σ x
    · push_neg at hs
      obtain ⟨m, hm, hmq⟩ : ∃ m ∈ Mk, δ / Mk.card ≤ qr A σ m := by
        apply Finset.exists_le_of_sum_le hMne
        rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hMc.ne']
        linarith
      obtain ⟨τ₀, x, h1, h2, h3⟩ := ih (σ ++ [m])
      refine ⟨m :: τ₀, x, ?_, h2, ?_⟩
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hm
        · exact h1 y hy
      · have e : σ ++ m :: τ₀ ++ [x] = σ ++ [m] ++ τ₀ ++ [x] := by simp
        rw [e]
        refine le_trans ?_ (le_trans (add_le_add (nch_exp_snoc_real A σ m) le_rfl) h3)
        have hmin0 : 0 ≤ min ((1-δ)/(D\Mk).card) (K*δ/Mk.card) :=
          le_min (div_nonneg (by linarith) hUc.le) (div_nonneg (by positivity) hMc.le)
        rw [add_assoc, ← ENNReal.ofReal_add (qr_nonneg A σ m) hmin0]
        gcongr
        have hK : (((K+1 : ℕ)):ℝ) * δ / Mk.card = K * δ / Mk.card + δ / Mk.card := by
          push_cast; ring
        rw [hK]
        rcases min_cases ((1-δ)/(D\Mk).card) (K*δ/Mk.card) with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; linarith [min_le_left ((1-δ)/(D\Mk).card) (K*δ/Mk.card + δ/Mk.card),
            qr_nonneg A σ m]
        · rw [h]; linarith [min_le_right ((1-δ)/(D\Mk).card) (K*δ/Mk.card + δ/Mk.card)]

lemma nch_sub' (A : RandomizedAlgorithm k M) (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (D : Finset M) (hD : D.card = k + 1) (Mk : Finset M) (hMk : Mk ⊆ D) (hMne : Mk.Nonempty)
    (hU : (D \ Mk).Nonempty) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (σ : List M) :
    ∃ τ₀ : List M, ∃ x : M, (∀ y ∈ τ₀, y ∈ Mk) ∧ x ∈ D \ Mk ∧
      A.expCost σ + ENNReal.ofReal ((1 - δ) / (D \ Mk).card) ≤ A.expCost (σ ++ τ₀ ++ [x]) := by
  have hMc : (0:ℝ) < Mk.card := by exact_mod_cast hMne.card_pos
  set a := (1 - δ) / ((D \ Mk).card : ℝ)
  obtain ⟨τ₀, x, h1, h2, h3⟩ := nch_sub A hd D hD Mk hMk hMne hU δ hδ hδ1
    ⌈a * Mk.card / δ⌉₊ σ
  refine ⟨τ₀, x, h1, h2, ?_⟩
  have : min a (⌈a * Mk.card / δ⌉₊ * δ / Mk.card) = a := by
    apply min_eq_left
    rw [le_div_iff₀ hMc]
    have := Nat.le_ceil (a * Mk.card / δ)
    rw [div_le_iff₀ hδ] at this
    linarith
  rwa [this] at h3

lemma nch_phase (A : RandomizedAlgorithm k M) (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (D : Finset M) (hD : D.card = k + 1) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ s : ℕ, ∀ Mk : Finset M, Mk ⊆ D → Mk.Nonempty → (D \ Mk).card = s + 1 →
    ∀ σ : List M, ∃ τ : List M, ∃ v : M, v ∈ D ∧ v ∉ Mk ∧ (∀ y ∈ τ, y ∈ D ∧ y ≠ v) ∧
      A.expCost σ + ENNReal.ofReal ((1 - δ) * ∑ i ∈ Finset.range (s + 1), (1:ℝ) / (i + 1))
        ≤ A.expCost (σ ++ τ ++ [v]) := by
  intro s
  induction s with
  | zero =>
    intro Mk hMk hMne hc σ
    have hU : (D \ Mk).Nonempty := by rw [← Finset.card_pos, hc]; omega
    obtain ⟨τ₀, x, h1, h2, h3⟩ := nch_sub' A hd D hD Mk hMk hMne hU δ hδ hδ1 σ
    rw [Finset.mem_sdiff] at h2
    refine ⟨τ₀, x, h2.1, h2.2, fun y hy => ⟨hMk (h1 y hy), fun h => h2.2 (h ▸ h1 y hy)⟩, ?_⟩
    rw [hc] at h3
    simpa using h3
  | succ s ih =>
    intro Mk hMk hMne hc σ
    have hU : (D \ Mk).Nonempty := by rw [← Finset.card_pos, hc]; omega
    obtain ⟨τ₀, x, h1, h2, h3⟩ := nch_sub' A hd D hD Mk hMk hMne hU δ hδ hδ1 σ
    have h2' := Finset.mem_sdiff.1 h2
    have hc' : (D \ insert x Mk).card = s + 1 := by
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem h2, hc]; rfl
    obtain ⟨τ', v, g1, g2, g3, g4⟩ := ih (insert x Mk) (Finset.insert_subset h2'.1 hMk)
      (Finset.insert_nonempty _ _) hc' (σ ++ τ₀ ++ [x])
    rw [Finset.mem_insert, not_or] at g2
    refine ⟨τ₀ ++ [x] ++ τ', v, g1, g2.2, ?_, ?_⟩
    · intro y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with (hy | rfl) | hy
      · exact ⟨hMk (h1 y hy), fun h => g2.2 (h ▸ h1 y hy)⟩
      · exact ⟨h2'.1, fun h => g2.1 h.symm⟩
      · exact g3 y hy
    · have e : σ ++ (τ₀ ++ [x] ++ τ') ++ [v] = σ ++ τ₀ ++ [x] ++ τ' ++ [v] := by simp
      rw [e]
      refine le_trans ?_ (le_trans (add_le_add h3 le_rfl) g4)
      have hn1 : (0:ℝ) ≤ (1 - δ) / ((D \ Mk).card : ℝ) := div_nonneg (by linarith) (by positivity)
      have hn2 : (0:ℝ) ≤ (1 - δ) * ∑ i ∈ Finset.range (s + 1), (1:ℝ) / (i + 1) :=
        mul_nonneg (by linarith) (Finset.sum_nonneg fun i _ => by positivity)
      rw [add_assoc (A.expCost σ), ← ENNReal.ofReal_add hn1 hn2, hc, Finset.sum_range_succ (n := s + 1)]
      apply le_of_eq; congr 2; push_cast; ring

/-! Offline schedules. -/

def Reach (C₀ : Config k M) (σ : List M) (C : Config k M) (c : ℝ) : Prop :=
  ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧ S σ.length = C ∧
    ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) ≤ c

lemma reach_nil (C₀ : Config k M) : Reach C₀ [] C₀ 0 :=
  ⟨fun _ => C₀, ⟨rfl, fun j => j.elim0⟩, rfl, by simp⟩

lemma reach_mono {C₀ : Config k M} {σ : List M} {C : Config k M} {c c' : ℝ}
    (h : Reach C₀ σ C c) (hc : c ≤ c') : Reach C₀ σ C c' := by
  obtain ⟨S, h1, h2, h3⟩ := h
  exact ⟨S, h1, h2, h3.trans hc⟩

lemma reach_snoc {C₀ : Config k M} {σ : List M} {C : Config k M} {c : ℝ}
    (h : Reach C₀ σ C c) (x : M) (C' : Config k M) (hx : x ∈ Set.range C') :
    Reach C₀ (σ ++ [x]) C' (c + moveCost C C') := by
  obtain ⟨S, ⟨hS0, hS⟩, hSl, hc⟩ := h
  refine ⟨fun j => if j ≤ σ.length then S j else C', ⟨by simpa using hS0, ?_⟩, ?_, ?_⟩
  · intro j
    have hj := j.2
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjl : (j:ℕ) < σ.length
    · obtain ⟨i, hi⟩ := hS ⟨j, hjl⟩
      refine ⟨i, ?_⟩
      simp only [show (j:ℕ) + 1 ≤ σ.length from hjl, if_true]
      rw [hi]
      simp [List.getElem_append_left hjl]
    · have hjeq : (j:ℕ) = σ.length := by omega
      obtain ⟨i, hi⟩ := hx
      refine ⟨i, ?_⟩
      simp [hjeq, hi]
  · simp
  · rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
    have e : ∑ j ∈ Finset.range σ.length,
        moveCost (if j ≤ σ.length then S j else C') (if j + 1 ≤ σ.length then S (j+1) else C')
        = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j+1)) :=
      Finset.sum_congr rfl fun j hj => by
        rw [Finset.mem_range] at hj
        rw [if_pos (by omega), if_pos (by omega)]
    simp only at e ⊢
    rw [e]
    simp only [le_rfl, if_true, show ¬ (σ.length + 1 ≤ σ.length) by omega, if_false, hSl]
    linarith

lemma moveCost_self (C : Config k M) : moveCost C C = 0 := by simp [moveCost]

lemma reach_stay {C₀ : Config k M} {C : Config k M} {c : ℝ} :
    ∀ (τ σ : List M), Reach C₀ σ C c → (∀ y ∈ τ, y ∈ Set.range C) → Reach C₀ (σ ++ τ) C c := by
  intro τ
  induction τ with
  | nil => intro σ h _; simpa using h
  | cons y τ ih =>
    intro σ h hy
    have h1 := reach_snoc h y C (hy y (by simp))
    rw [moveCost_self, add_zero] at h1
    have := ih (σ ++ [y]) h1 (fun z hz => hy z (by simp [hz]))
    simpa using this

lemma offline_le {C₀ : Config k M} {σ : List M} {C : Config k M} {c : ℝ}
    (h : Reach C₀ σ C c) : offlineCost C₀ σ ≤ c := by
  obtain ⟨S, h1, _, h3⟩ := h
  refine le_trans (csInf_le ⟨0, ?_⟩ ⟨S, h1, rfl⟩) h3
  rintro _ ⟨S', _, rfl⟩
  exact Finset.sum_nonneg fun _ _ => nch_moveCost_nonneg _ _

lemma offline_nonneg (C₀ : Config k M) (σ : List M) : 0 ≤ offlineCost C₀ σ := by
  apply Real.sInf_nonneg
  rintro _ ⟨S', _, rfl⟩
  exact Finset.sum_nonneg fun _ _ => nch_moveCost_nonneg _ _

lemma dist_le_one' (hd : ∀ x y : M, x ≠ y → dist x y = 1) (x y : M) : dist x y ≤ 1 := by
  by_cases h : x = y
  · simp [h]
  · rw [hd x y h]

lemma moveCost_le_k (hd : ∀ x y : M, x ≠ y → dist x y = 1) (C C' : Config k M) :
    moveCost C C' ≤ k := by
  unfold moveCost
  calc ∑ i, dist (C i) (C' i) ≤ ∑ _i : Fin k, (1:ℝ) :=
        Finset.sum_le_sum fun i _ => dist_le_one' hd _ _
    _ = k := by simp

lemma moveCost_update (hd : ∀ x y : M, x ≠ y → dist x y = 1) (C : Config k M) (i₀ : Fin k)
    (v : M) : moveCost C (Function.update C i₀ v) ≤ 1 := by
  unfold moveCost
  rw [Finset.sum_eq_single i₀]
  · simpa using dist_le_one' hd (C i₀) v
  · intro b _ hb; simp [Function.update_of_ne hb]
  · simp

end

theorem nch_core (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) (M : Type)
    [MetricSpace M] (e : Fin n ≃ M) (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (A : KServer.RandomizedAlgorithm k M) (C₀ : KServer.Config k M) (c : ℝ)
    (hc : c < (harmonic k : ℝ)) :
    ¬ A.IsCompetitiveFrom C₀ c := by
  rintro ⟨-, a, ha⟩
  let D : Finset M := Finset.univ.map ⟨fun j : Fin (k+1) => e (Fin.castLE hkn j),
    fun i j h => Fin.castLE_injective hkn (e.injective h)⟩
  have hD : D.card = k + 1 := by simp [D]
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 1 := ⟨k - 1, by omega⟩
  set H : ℝ := ∑ i ∈ Finset.range (s + 1), (1:ℝ) / (i + 1) with hHdef
  have hH : (harmonic (s+1) : ℝ) = H := by
    rw [hHdef, harmonic]; push_cast; simp [one_div]
  rw [hH] at hc
  have hHpos : 0 < H := by
    rw [hHdef, Finset.sum_range_succ']; simp only [CharP.cast_eq_zero, zero_add, div_one]
    have := Finset.sum_nonneg (s := Finset.range s) (f := fun i : ℕ => (1:ℝ) / ((i + 1 : ℕ) + 1))
      (fun i _ => by positivity)
    push_cast at this ⊢; linarith
  set c' := max c 0 with hc'
  have hc'H : c' < H := max_lt hc hHpos
  have hc'0 : 0 ≤ c' := le_max_right _ _
  set δ := (H - c') / (2 * H) with hδdef
  have hδ : 0 < δ := div_pos (by linarith) (by linarith)
  have hδ1 : δ < 1 := by rw [div_lt_one (by linarith)]; linarith
  set g := (1 - δ) * H with hg
  have hgc : c' < g := by
    rw [hg, hδdef]; field_simp; nlinarith
  have hg0 : 0 ≤ g := by linarith
  -- covering configuration
  have cover : ∀ v ∈ D, ∃ C : Config (s+1) M, ∀ y ∈ D, y ≠ v → y ∈ Set.range C := by
    intro v hv
    have hcard : (D.erase v).card = s + 1 := by rw [Finset.card_erase_of_mem hv, hD]; rfl
    let f := (D.erase v).equivFin.symm
    refine ⟨fun i => (f (Fin.cast hcard.symm i)).1, fun y hy hyv => ?_⟩
    obtain ⟨i, hi⟩ := f.surjective ⟨y, Finset.mem_erase.2 ⟨hyv, hy⟩⟩
    exact ⟨Fin.cast hcard i, by simp [hi]⟩
  have hDne : D.Nonempty := by rw [← Finset.card_pos, hD]; omega
  obtain ⟨d0, hd0⟩ := hDne
  have hsing : ∀ v ∈ D, ({v} : Finset M) ⊆ D ∧ ({v} : Finset M).Nonempty ∧
      (D \ {v}).card = s + 1 := fun v hv =>
    ⟨by simpa using hv, by simp, by
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hv, hD]; rfl⟩
  have iter : ∀ P : ℕ, ∃ σ : List M, ∃ v : M, ∃ C : Config (s+1) M, v ∈ D ∧
      (∀ y ∈ D, y ≠ v → y ∈ Set.range C) ∧
      Reach C₀ σ C (((s+1 : ℕ) : ℝ) + ((P:ℝ) + 1)) ∧
      ENNReal.ofReal (((P:ℝ) + 1) * g) ≤ A.expCost (σ ++ [v]) := by
    intro P
    induction P with
    | zero =>
      obtain ⟨Mk1, Mk2, Mk3⟩ := hsing d0 hd0
      obtain ⟨τ, v, h1, h2, h3, h4⟩ := nch_phase A hd D hD δ hδ hδ1 s {d0} Mk1 Mk2 Mk3 [d0]
      obtain ⟨C, hC⟩ := cover v h1
      have hv : v ≠ d0 := by simpa using h2
      refine ⟨d0 :: τ, v, C, h1, hC, ?_, ?_⟩
      · have r1 := reach_snoc (reach_nil C₀) d0 C (hC d0 hd0 (Ne.symm hv))
        have r2 := reach_stay τ _ r1 (fun y hy => hC y (h3 y hy).1 (h3 y hy).2)
        refine reach_mono (by simpa using r2) ?_
        have := moveCost_le_k hd C₀ C
        push_cast at this ⊢; linarith
      · have e : [d0] ++ τ ++ [v] = d0 :: τ ++ [v] := by simp
        rw [e] at h4
        refine le_trans (le_of_eq ?_) (le_trans le_add_self h4)
        congr 1; rw [hg]; push_cast; ring
    | succ P ih =>
      obtain ⟨σ, v, C, hv, hC, hR, hE⟩ := ih
      obtain ⟨Mk1, Mk2, Mk3⟩ := hsing v hv
      obtain ⟨τ, w, h1, h2, h3, h4⟩ :=
        nch_phase A hd D hD δ hδ hδ1 s {v} Mk1 Mk2 Mk3 (σ ++ [v])
      have hwv : w ≠ v := by simpa using h2
      obtain ⟨i₀, hi₀⟩ := hC w h1 hwv
      have hC' : ∀ y ∈ D, y ≠ w → y ∈ Set.range (Function.update C i₀ v) := by
        intro y hy hyw
        by_cases hyv : y = v
        · exact ⟨i₀, by simp [hyv]⟩
        · obtain ⟨i, hi⟩ := hC y hy hyv
          have : i ≠ i₀ := by rintro rfl; exact hyw (hi.symm.trans hi₀)
          exact ⟨i, by simp [Function.update_of_ne this, hi]⟩
      refine ⟨σ ++ v :: τ, w, Function.update C i₀ v, h1, hC', ?_, ?_⟩
      · have r1 := reach_snoc hR v (Function.update C i₀ v) (hC' v hv (Ne.symm hwv))
        have r2 := reach_stay τ _ r1 (fun y hy => hC' y (h3 y hy).1 (h3 y hy).2)
        refine reach_mono (by simpa using r2) ?_
        have := moveCost_update hd C i₀ v
        push_cast; linarith
      · have e : σ ++ [v] ++ τ ++ [w] = σ ++ v :: τ ++ [w] := by simp
        rw [e] at h4
        refine le_trans ?_ (le_trans (add_le_add hE le_rfl) h4)
        rw [← ENNReal.ofReal_add (by positivity) (by rw [← hg]; exact hg0)]
        apply le_of_eq; congr 1; rw [← hg]; push_cast; ring
  obtain ⟨P, hP⟩ := exists_nat_gt ((c' * (((s+1:ℕ):ℝ) + 1) + a) / (g - c'))
  obtain ⟨σ, v, C, hv, hC, hR, hE⟩ := iter P
  have hR' := reach_snoc hR v (Function.update C ⟨0, by omega⟩ v) ⟨⟨0, by omega⟩, by simp⟩
  have hoff := offline_le (reach_mono hR' (add_le_add le_rfl (moveCost_update hd C _ v)))
  have hoff0 := offline_nonneg C₀ (σ ++ [v])
  have h := hE.trans (ha (σ ++ [v]))
  rw [ENNReal.ofReal_le_ofReal_iff'] at h
  have hcc : c * offlineCost C₀ (σ ++ [v]) ≤ c' * (((s+1:ℕ):ℝ) + ((P:ℝ) + 1) + 1) :=
    calc c * offlineCost C₀ (σ ++ [v]) ≤ c' * offlineCost C₀ (σ ++ [v]) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hoff0
      _ ≤ _ := mul_le_mul_of_nonneg_left hoff hc'0
  have hgc' : 0 < g - c' := by linarith
  rw [div_lt_iff₀ hgc'] at hP
  rcases h with h | h
  · nlinarith
  · have : (0:ℝ) < ((P:ℝ) + 1) * g := by
      have : (0:ℝ) < g := by linarith
      positivity
    linarith

end CompetitivePaging.LowerBound

open CompetitivePaging.LowerBound


theorem solution (n : ℕ) (hn : 2 ≤ n) (M : Type) [MetricSpace M]
    (e : Fin n ≃ M) (hd : ∀ x y : M, x ≠ y → dist x y = 1)
    (A : KServer.RandomizedAlgorithm (n - 1) M) (C₀ : KServer.Config (n - 1) M) (c : ℝ)
    (hc : c < (harmonic (n - 1) : ℝ)) :
    ¬ A.IsCompetitiveFrom C₀ c := by
  exact nch_core n (n - 1) (by omega) (by omega) M e hd A C₀ c hc
