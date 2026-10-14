-- Prove2me | solution 1 for GTWSched.MaxDisc.normalize_after
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:42:07.89817+00:00
-- url     : https://prove2.me/submissions/aa27656a-ac60-494f-8b1f-28fc13a014d8

import Mathlib
import Definitions.Def_GTWSched_MaxDisc_Model



namespace GTWSched.MaxDisc

noncomputable def swapT {N : ℕ} (l : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (a b : Fin N) (p : Fin N) : ℝ :=
  if p = a then s (σ a) else if p = b then s (σ b) + (l (σ b) - l (σ a))
  else if a < p ∧ p < b then s (σ p) + (l (σ b) - l (σ a)) else s (σ p)

noncomputable def swapS {N : ℕ} (l : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (a b : Fin N) (i : Fin N) : ℝ :=
  swapT l σ s a b (Equiv.swap a b (σ.symm i))

lemma swapS_apply {N : ℕ} (l : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (a b : Fin N) (p : Fin N) :
    swapS l σ s a b (σ (Equiv.swap a b p)) = swapT l σ s a b p := by
  simp [swapS]

theorem swap_exch {N : ℕ} (r d l : Fin N → ℝ) (hl : ∀ i, 0 ≤ l i)
    (σ : Fin N ≃ Fin N) (s : Fin N → ℝ) (hF : Feasible r d l σ s) (a b : Fin N) (hab : a < b)
    (hd : d (σ b) ≤ d (σ a)) (hR1 : r (σ b) ≤ s (σ a))
    (hmid : ∀ p, a < p → p < b →
      r (σ p) ≤ s (σ p) + (l (σ b) - l (σ a)) ∧
      s (σ p) + (l (σ b) - l (σ a)) + l (σ p) ≤ d (σ p)) :
    Feasible r d l ((Equiv.swap a b).trans σ) (swapS l σ s a b) ∧
    makespan l (swapS l σ s a b) ≤ makespan l s := by
  obtain ⟨hO, hRD⟩ := hF
  have hne : a ≠ b := ne_of_lt hab
  have hbna : b ≠ a := ne_of_gt hab
  -- values of T and lengths by zone
  have Ta : swapT l σ s a b a = s (σ a) := by simp [swapT]
  have Tb : swapT l σ s a b b = s (σ b) + (l (σ b) - l (σ a)) := by simp [swapT, hbna]
  have Tm : ∀ p, a < p → p < b → swapT l σ s a b p = s (σ p) + (l (σ b) - l (σ a)) := by
    intro p h1 h2
    have : p ≠ a := ne_of_gt h1
    have : p ≠ b := ne_of_lt h2
    simp [swapT, *]
  have To : ∀ p, p < a ∨ b < p → swapT l σ s a b p = s (σ p) := by
    intro p h
    have h1 : p ≠ a := by rcases h with h | h <;> [exact ne_of_lt h; exact ne_of_gt (hab.trans h)]
    have h2 : p ≠ b := by rcases h with h | h <;> [exact ne_of_lt (h.trans hab); exact ne_of_gt h]
    have h3 : ¬ (a < p ∧ p < b) := by
      rintro ⟨x, y⟩; rcases h with h | h
      · exact absurd x (not_lt.mpr h.le)
      · exact absurd y (not_lt.mpr h.le)
    simp [swapT, h1, h2, h3]
  have Sa : σ (Equiv.swap a b a) = σ b := by simp
  have Sb : σ (Equiv.swap a b b) = σ a := by simp
  have Sx : ∀ p, p ≠ a → p ≠ b → σ (Equiv.swap a b p) = σ p := by
    intro p h1 h2; rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hOs := hO
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p q hpq
    simp only [Equiv.trans_apply]
    rw [swapS_apply, swapS_apply]
    rcases lt_trichotomy p a with hp | hp | hp
    · have hpa : p ≠ a := ne_of_lt hp
      have hpb : p ≠ b := ne_of_lt (hp.trans hab)
      rw [Sx p hpa hpb, To p (Or.inl hp)]
      rcases lt_trichotomy q a with hq | hq | hq
      · rw [To q (Or.inl hq)]
        exact hO p q hpq
      · subst hq; rw [Ta]; exact hO p _ hpq
      · rcases lt_trichotomy q b with hq' | hq' | hq'
        · rw [Tm q hq hq']
          have := hO p a hp
          have := hO a q hq
          have := hl (σ a); have := hl (σ b)
          linarith
        · obtain rfl : b = q := hq'.symm; rw [Tb]
          have := hO p a hp
          have := hO a _ hq
          have := hl (σ a); have := hl (σ b)
          linarith
        · rw [To q (Or.inr hq')]
          exact hO p q hpq
    · obtain rfl : a = p := hp.symm
      rw [Ta, Sa]
      rcases lt_trichotomy q b with hq' | hq' | hq'
      · rw [Tm q hpq hq']
        have := hO _ q hpq
        have := hl (σ a); have := hl (σ b)
        linarith
      · obtain rfl : b = q := hq'.symm; rw [Tb]
        have := hO _ _ hpq
        have := hl (σ a); have := hl (σ b)
        linarith
      · rw [To q (Or.inr hq')]
        have := hO a b hab
        have := hO _ _ hq'
        have := hl (σ a); have := hl (σ b)
        linarith
    · rcases lt_trichotomy p b with hp' | hp' | hp'
      · have hpa : p ≠ a := ne_of_gt hp
        have hpb : p ≠ b := ne_of_lt hp'
        rw [Sx p hpa hpb, Tm p hp hp']
        rcases lt_trichotomy q b with hq' | hq' | hq'
        · rw [Tm q (hp.trans hpq) hq']
          have := hO p q hpq
          linarith
        · obtain rfl : b = q := hq'.symm; rw [Tb]
          have := hO p _ hpq
          linarith
        · rw [To q (Or.inr hq')]
          have := hO p b hp'
          have := hO b q hq'
          have := hl (σ a); have := hl (σ b)
          linarith
      · obtain rfl : b = p := hp'.symm
        rw [Tb, Sb]
        have hq' : b < q := hpq
        rw [To q (Or.inr hq')]
        have := hO _ _ hq'
        linarith
      · have hpa : p ≠ a := ne_of_gt (hab.trans hp')
        have hpb : p ≠ b := ne_of_gt hp'
        rw [Sx p hpa hpb, To p (Or.inr hp')]
        have hqa : q ≠ a := ne_of_gt (hab.trans (hp'.trans hpq))
        have hqb : q ≠ b := ne_of_gt (hp'.trans hpq)
        rw [To q (Or.inr (hp'.trans hpq))]
        exact hO p q hpq
  · intro i
    obtain ⟨p, rfl⟩ : ∃ p, ((Equiv.swap a b).trans σ) p = i :=
      ⟨((Equiv.swap a b).trans σ).symm i, by simp⟩
    simp only [Equiv.trans_apply]
    rw [swapS_apply]
    rcases lt_trichotomy p a with hp | hp | hp
    · rw [Sx p (ne_of_lt hp) (ne_of_lt (hp.trans hab)), To p (Or.inl hp)]
      exact hRD _
    · obtain rfl : a = p := hp.symm
      rw [Sa, Ta]
      have := hO a b hab
      have := hRD (σ b)
      have := hl (σ a)
      constructor <;> linarith
    · rcases lt_trichotomy p b with hp' | hp' | hp'
      · rw [Sx p (ne_of_gt hp) (ne_of_lt hp'), Tm p hp hp']
        obtain ⟨h1, h2⟩ := hmid p hp hp'
        exact ⟨h1, h2⟩
      · obtain rfl : b = p := hp'.symm
        rw [Sb, Tb]
        have := hO a b hab
        have := hRD (σ a)
        have := hRD (σ b)
        have := hl (σ a); have := hl (σ b)
        constructor <;> linarith
      · rw [Sx p (ne_of_gt (hab.trans hp')) (ne_of_gt hp'), To p (Or.inr hp')]
        exact hRD _
  · have hM : ∀ j, s j + l j ≤ makespan l s := fun j =>
      le_ciSup (f := fun j => s j + l j) (Set.finite_range _).bddAbove j
    haveI : Nonempty (Fin N) := ⟨a⟩
    unfold makespan at *
    apply ciSup_le
    intro i
    obtain ⟨p, rfl⟩ : ∃ p, ((Equiv.swap a b).trans σ) p = i :=
      ⟨((Equiv.swap a b).trans σ).symm i, by simp⟩
    simp only [Equiv.trans_apply]
    rw [swapS_apply]
    have hb := hM (σ b)
    rcases lt_trichotomy p a with hp | hp | hp
    · rw [Sx p (ne_of_lt hp) (ne_of_lt (hp.trans hab)), To p (Or.inl hp)]
      have := hO p b (hp.trans hab)
      have := hl (σ b)
      linarith
    · obtain rfl : a = p := hp.symm
      rw [Sa, Ta]
      have := hO a b hab
      have := hl (σ a)
      linarith
    · rcases lt_trichotomy p b with hp' | hp' | hp'
      · rw [Sx p (ne_of_gt hp) (ne_of_lt hp'), Tm p hp hp']
        have := hO p b hp'
        have := hl (σ a)
        linarith
      · obtain rfl : b = p := hp'.symm
        rw [Sb, Tb]
        linarith
      · rw [Sx p (ne_of_gt (hab.trans hp')) (ne_of_gt hp'), To p (Or.inr hp')]
        exact hM _


lemma continuous_makespan {N : ℕ} [Nonempty (Fin N)] (l : Fin N → ℝ) :
    Continuous (fun s : Fin N → ℝ => makespan l s) := by
  have : (fun s : Fin N → ℝ => makespan l s) = fun s => Finset.univ.sup' Finset.univ_nonempty (fun i => s i + l i) := by
    ext s
    unfold makespan
    rw [Finset.sup'_univ_eq_ciSup]
  rw [this]
  exact Continuous.finset_sup'_apply (f := fun (i : Fin N) (s : Fin N → ℝ) => s i + l i) Finset.univ_nonempty
    (fun i _ => by fun_prop)

lemma feasible_compact {N : ℕ} (r d l : Fin N → ℝ) (hl : ∀ i, 0 ≤ l i) (σ : Fin N ≃ Fin N) :
    IsCompact {s : Fin N → ℝ | Feasible r d l σ s} := by
  have hsub : {s : Fin N → ℝ | Feasible r d l σ s} ⊆ Set.pi Set.univ (fun i => Set.Icc (r i) (d i)) := by
    intro s hs i _
    obtain ⟨_, h⟩ := hs
    have h1 := h i
    have h2 := hl i
    exact ⟨h1.1, by linarith [h1.2]⟩
  have hclosed : IsClosed {s : Fin N → ℝ | Feasible r d l σ s} := by
    have : {s : Fin N → ℝ | Feasible r d l σ s} =
        (⋂ p, ⋂ q, ⋂ (_ : p < q), {s : Fin N → ℝ | s (σ p) + l (σ p) ≤ s (σ q)}) ∩
        ⋂ i, ({s : Fin N → ℝ | r i ≤ s i} ∩ {s : Fin N → ℝ | s i + l i ≤ d i}) := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Feasible, Ordered]
    rw [this]
    refine IsClosed.inter ?_ ?_
    · refine isClosed_iInter fun p => isClosed_iInter fun q => isClosed_iInter fun _ => ?_
      exact isClosed_le (by fun_prop) (by fun_prop)
    · refine isClosed_iInter fun i => IsClosed.inter ?_ ?_
      · exact isClosed_le (by fun_prop) (by fun_prop)
      · exact isClosed_le (by fun_prop) (by fun_prop)
  exact IsCompact.of_isClosed_subset (isCompact_univ_pi fun i => isCompact_Icc) hclosed hsub

theorem exists_optimum {N : ℕ} (r d l : Fin N → ℝ) (hl : ∀ i, 0 ≤ l i) [Nonempty (Fin N)]
    (hfeas : ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ), Feasible r d l σ s) :
    ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ), Optimum r d l σ s := by
  set M : Set ℝ := ⋃ σ : Fin N ≃ Fin N, (fun s => makespan l s) '' {s : Fin N → ℝ | Feasible r d l σ s} with hM
  have hcomp : IsCompact M := by
    apply isCompact_iUnion
    intro σ
    exact (feasible_compact r d l hl σ).image (continuous_makespan l)
  obtain ⟨σ0, s0, h0⟩ := hfeas
  have hne : M.Nonempty := ⟨makespan l s0, Set.mem_iUnion.mpr ⟨σ0, s0, h0, rfl⟩⟩
  obtain ⟨m, hm, hmin⟩ := hcomp.exists_isLeast hne
  obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp hm
  obtain ⟨s, hs, rfl⟩ := hσ
  refine ⟨σ, s, hs, ?_⟩
  intro σ' s' hs'
  exact hmin (Set.mem_iUnion.mpr ⟨σ', s', hs', rfl⟩)


theorem rle_core {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (n : Fin N) (hn : ∀ i, d i ≤ d n) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (hS : Feasible r d l σ s) :
    ∀ i, σ.symm n < σ.symm i → r i ≤ s n + l n := by
  intro i _
  obtain ⟨_, hF⟩ := hS
  have hn1 := hF n
  have hn2 := hn i
  have hr0 := hr n
  have hli := hl i
  have hln := hl n
  have hi := hr i
  rcases hsf i with h | ⟨h0, h1⟩
  · rcases hsf n with h' | ⟨h0', h1'⟩
    · linarith [hn1.1, hn1.2]
    · linarith [hn1.1, hn1.2]
  · linarith [hn1.1]

theorem rtp_core {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (n : Fin N) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (hS : Feasible r d l σ s) (hrtp : ReleaseTimeProperty r σ s n) :
    ∀ i, i ≠ n → (σ.symm i < σ.symm n ↔ d i ≤ s n + α) := by
  intro i hin
  obtain ⟨hO, hF⟩ := hS
  have hne : σ.symm i ≠ σ.symm n := fun h => hin (σ.symm.injective h)
  constructor
  · intro h
    have h1 := hO _ _ h
    simp only [Equiv.apply_symm_apply] at h1
    have := hF i
    have := hr i
    have := hl i
    rcases hsf i with h | ⟨h0, h1'⟩ <;> linarith [(hF i).1]
  · intro h
    by_contra hc
    have hgt : σ.symm n < σ.symm i := lt_of_le_of_ne (not_lt.mp hc) (Ne.symm hne)
    have := hrtp i hgt
    have := hl i
    have := hr n
    have := (hF n).1
    rcases hsf i with h' | ⟨h0, h1'⟩ <;> linarith


lemma phi_swap {N : ℕ} (w f : Fin N → ℝ) (σ : Fin N ≃ Fin N) (u v : Fin N) (huv : u ≠ v) :
    ∑ p, w p * f (σ (Equiv.swap u v p)) - ∑ p, w p * f (σ p) =
      (w v - w u) * (f (σ u) - f (σ v)) := by
  have h1 : ∑ p, w p * f (σ (Equiv.swap u v p)) = ∑ q, w (Equiv.swap u v q) * f (σ q) := by
    rw [← Equiv.sum_comp (Equiv.swap u v) (fun q => w (Equiv.swap u v q) * f (σ q))]
    simp
  rw [h1, ← Finset.sum_sub_distrib]
  have : ∀ q, w (Equiv.swap u v q) * f (σ q) - w q * f (σ q) = (w (Equiv.swap u v q) - w q) * f (σ q) := by
    intro q; ring
  simp_rw [this]
  rw [Fintype.sum_eq_add u v huv]
  · simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  · intro x hx
    rw [Equiv.swap_apply_of_ne_of_ne hx.1 hx.2]
    ring



lemma rel_le_rn {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i)
    (hsf : SpecialForm r d l α) (n : Fin N) (hn : ∀ i, d i ≤ d n) :
    ∀ i, r i ≤ r n + l n := by
  intro i
  have hn1 := hn i
  have hr0 := hr n
  have hli := hl i
  have hln := hl n
  have hi := hr i
  rcases hsf i with h | ⟨h0, h1⟩
  · rcases hsf n with h' | ⟨h0', h1'⟩
    · linarith
    · linarith
  · linarith

theorem compaction {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (n : Fin N) (hn : ∀ i, d i ≤ d n) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (hF : Feasible r d l σ s) :
    ∃ s' : Fin N → ℝ, Feasible r d l σ s' ∧ (∀ i, s' i ≤ s i) ∧
      (∀ i, σ.symm i < σ.symm n → s' i = s i) ∧
      s' n = max (r n) (⨆ i : {i : Fin N // σ.symm i < σ.symm n}, s' i + l i) ∧
      (∀ p q : Fin N, σ.symm n ≤ p → q.val = p.val + 1 → s' (σ q) = s' (σ p) + l (σ p)) := by
  classical
  obtain ⟨hO, hRD⟩ := hF
  set a : Fin N := σ.symm n with ha
  have hσa : σ a = n := by simp [ha]
  have hRn := rel_le_rn r d l α hr hl hsf n hn
  let m0 : ℝ := ⨆ i : {i : Fin N // σ.symm i < a}, s i.1 + l i.1
  let sn : ℝ := max (r n) m0
  let L : ℕ → ℝ := fun j => if h : j < N then l (σ ⟨j, h⟩) else 0
  have hL0 : ∀ j, 0 ≤ L j := by
    intro j; simp only [L]; split_ifs
    · exact hl _
    · exact le_rfl
  have hLq : ∀ q : Fin N, L q.val = l (σ q) := by
    intro q; simp [L, q.isLt]
  let T : Fin N → ℝ := fun q => sn + ∑ j ∈ Finset.Ico a.val q.val, L j
  let s' : Fin N → ℝ := fun i => if σ.symm i < a then s i else T (σ.symm i)
  have hm0le : ∀ p : Fin N, p < a → s (σ p) + l (σ p) ≤ m0 := by
    intro p hp
    exact le_ciSup (f := fun i : {i : Fin N // σ.symm i < a} => s i.1 + l i.1)
      (Set.finite_range _).bddAbove ⟨σ p, by simpa using hp⟩
  have hm0s : m0 ≤ s n := by
    apply Real.iSup_le
    · intro i
      have := hO (σ.symm i.1) a i.2
      simpa [hσa] using this
    · exact (hr n).trans (hRD n).1
  have hsn_le : sn ≤ s n := max_le (hRD n).1 hm0s
  have hsum0 : ∀ q : Fin N, 0 ≤ ∑ j ∈ Finset.Ico a.val q.val, L j :=
    fun q => Finset.sum_nonneg (fun j _ => hL0 j)
  have hsn_ge : r n ≤ sn := le_max_left _ _
  have hTge : ∀ q : Fin N, sn ≤ T q := fun q => by simp only [T]; linarith [hsum0 q]
  have hTa : T a = sn := by simp [T]
  have hTsucc : ∀ p q : Fin N, a ≤ p → q.val = p.val + 1 → T q = T p + l (σ p) := by
    intro p q hp hq
    simp only [T]
    rw [hq, Finset.sum_Ico_succ_top (by exact hp), hLq]
    ring
  have hTdom : ∀ k : ℕ, ∀ hk : k < N, a.val ≤ k → T ⟨k, hk⟩ ≤ s (σ ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk hak
      have : a = ⟨0, hk⟩ := Fin.ext (by show a.val = 0; omega)
      rw [← this, hTa, hσa]; exact hsn_le
    | succ k ih =>
      intro hk hak
      rcases Nat.eq_or_lt_of_le hak with h | h
      · have : a = ⟨k+1, hk⟩ := Fin.ext (by show a.val = k + 1; omega)
        rw [← this, hTa, hσa]; exact hsn_le
      · have hk' : k < N := by omega
        have h1 := ih hk' (by omega)
        rw [hTsucc ⟨k, hk'⟩ ⟨k+1, hk⟩ (by rw [Fin.le_def]; show a.val ≤ k; omega) (by simp)]
        have h2 := hO ⟨k, hk'⟩ ⟨k+1, hk⟩ (by simp [Fin.lt_def])
        linarith
  have hs'pre : ∀ p : Fin N, p < a → s' (σ p) = s (σ p) := by
    intro p hp; simp [s', hp]
  have hs'post : ∀ p : Fin N, a ≤ p → s' (σ p) = T p := by
    intro p hp; simp [s', not_lt.mpr hp]
  refine ⟨s', ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro p q hpq
    rcases lt_or_ge p a with hp | hp
    · rcases lt_or_ge q a with hq | hq
      · rw [hs'pre p hp, hs'pre q hq]; exact hO p q hpq
      · rw [hs'pre p hp, hs'post q hq]
        have := hm0le p hp
        have := hTge q
        have : m0 ≤ sn := le_max_right _ _
        linarith
    · rw [hs'post p hp, hs'post q (hp.trans hpq.le)]
      have : T q = T p + (∑ j ∈ Finset.Ico p.val q.val, L j) := by
        simp only [T]
        rw [add_assoc, Finset.sum_Ico_consecutive _ hp (Fin.lt_def.mp hpq).le]
      rw [this]
      have : L p.val ≤ ∑ j ∈ Finset.Ico p.val q.val, L j := by
        apply Finset.single_le_sum (f := L) (fun j _ => hL0 j)
        simp [Finset.mem_Ico, Fin.lt_def.mp hpq]
      rw [hLq] at this
      linarith
  · intro i
    obtain ⟨p, rfl⟩ := σ.surjective i
    rcases lt_or_ge p a with hp | hp
    · rw [hs'pre p hp]; exact hRD _
    · rw [hs'post p hp]
      rcases eq_or_lt_of_le hp with h | h
      · rw [← h, hTa, hσa]; exact ⟨hsn_ge, by linarith [hsn_le, (hRD n).2]⟩
      · constructor
        · have h1 := hRn (σ p)
          have h2 : T p ≥ sn + l n := by
            have := hTsucc a ⟨a.val + 1, by omega⟩ le_rfl rfl
            have hmono : T ⟨a.val + 1, by omega⟩ ≤ T p := by
              simp only [T]
              have : ∑ j ∈ Finset.Ico a.val (a.val + 1), L j ≤ ∑ j ∈ Finset.Ico a.val p.val, L j := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro j hj; simp only [Finset.mem_Ico] at hj ⊢
                  have := Fin.lt_def.mp h; omega
                · intro j _ _; exact hL0 j
              linarith
            rw [hσa] at this
            linarith
          linarith
        · have := hTdom p.val p.isLt (by exact hp)
          have h3 := (hRD (σ p)).2
          have h4 : T p ≤ s (σ p) := by simpa using this
          linarith
  · intro i
    rcases lt_or_ge (σ.symm i) a with hp | hp
    · simp [s', hp]
    · have h := hTdom (σ.symm i).val (σ.symm i).isLt hp
      simp only [s', not_lt.mpr hp, if_false]
      simpa using h
  · intro i hi
    simp [s', hi]
  · have hsn' : s' n = sn := by
      have : s' (σ a) = T a := hs'post a le_rfl
      rw [hσa, hTa] at this; exact this
    rw [hsn']
    have : (⨆ i : {i : Fin N // σ.symm i < σ.symm n}, s' i + l i) = m0 := by
      apply iSup_congr
      intro i
      have h2 : σ.symm i.1 < a := i.2
      have : s' i.1 = s i.1 := by simp [s', h2]
      rw [this]
    rw [this]
  · intro p q hp hq
    rw [hs'post p hp, hs'post q (by rw [Fin.le_def]; have := Fin.le_def.mp hp; omega)]
    exact hTsucc p q hp hq


lemma swapT_out {N : ℕ} (l : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (a b p : Fin N) (hab : a < b) (h : p < a ∨ b < p) : swapT l σ s a b p = s (σ p) := by
  have h1 : p ≠ a := by rcases h with h | h <;> [exact ne_of_lt h; exact ne_of_gt (hab.trans h)]
  have h2 : p ≠ b := by rcases h with h | h <;> [exact ne_of_lt (h.trans hab); exact ne_of_gt h]
  have h3 : ¬ (a < p ∧ p < b) := by
    rintro ⟨x, y⟩; rcases h with h | h
    · exact absurd x (not_lt.mpr h.le)
    · exact absurd y (not_lt.mpr h.le)
  simp [swapT, h1, h2, h3]

lemma swapS_out {N : ℕ} (l : Fin N → ℝ) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (a b i : Fin N) (hab : a < b) (h : σ.symm i < a ∨ b < σ.symm i) :
    swapS l σ s a b i = s i := by
  have h1 : σ.symm i ≠ a := by rcases h with h | h <;> [exact ne_of_lt h; exact ne_of_gt (hab.trans h)]
  have h2 : σ.symm i ≠ b := by rcases h with h | h <;> [exact ne_of_lt (h.trans hab); exact ne_of_gt h]
  unfold swapS
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2, swapT_out l σ s a b _ hab h]
  simp

theorem sort_tail {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (hd : Monotone d) (n : Fin N) (hnlast : n.val + 1 = N)
    (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (hopt : Optimum r d l σ s) (hrtp : ReleaseTimeProperty r σ s n) :
    ∃ (σ' : Fin N ≃ Fin N) (s' : Fin N → ℝ),
      Optimum r d l σ' s' ∧ ReleaseTimeProperty r σ' s' n ∧ σ'.symm n = σ.symm n ∧
      (∀ p : Fin N, p < σ.symm n → σ' p = σ p ∧ s' (σ p) = s (σ p)) ∧ s' n = s n ∧
      (∀ p q : Fin N, σ.symm n < p → p < q → σ' p < σ' q) := by
  classical
  have hn : ∀ i, d i ≤ d n := fun i => hd (Fin.le_def.mpr (by have := i.isLt; omega))
  set a : Fin N := σ.symm n with ha
  let C : Set (Fin N ≃ Fin N) := {σ' | ∃ s', Optimum r d l σ' s' ∧ ReleaseTimeProperty r σ' s' n ∧
    σ'.symm n = a ∧ (∀ p : Fin N, p < a → σ' p = σ p ∧ s' (σ p) = s (σ p)) ∧ s' n = s n}
  have hCne : C.Nonempty := ⟨σ, s, hopt, hrtp, rfl, fun p _ => ⟨rfl, rfl⟩, rfl⟩
  let w : Fin N → ℝ := fun p => if a < p then (p.val : ℝ) else 0
  let Φ : (Fin N ≃ Fin N) → ℝ := fun σ' => ∑ p, w p * ((σ' p).val : ℝ)
  obtain ⟨σ2, ⟨s2, hopt2, hrtp2, hpos2, hpre2, hsn2⟩, hσ2max⟩ :=
    Set.exists_max_image C Φ (Set.toFinite _) hCne
  have hσa : σ2 a = n := by rw [← hpos2]; simp
  obtain ⟨hO, hRD⟩ := hopt2.1
  have hadj : ∀ u v : Fin N, v.val = u.val + 1 → a < u → σ2 u < σ2 v := by
    intro u v huv hau
    by_contra hnot
    have huv' : u < v := by rw [Fin.lt_def]; omega
    have hlt : σ2 v < σ2 u := by
      have hne : σ2 u ≠ σ2 v := fun h => (ne_of_lt huv') (σ2.injective h)
      exact lt_of_le_of_ne (not_lt.mp hnot) (Ne.symm hne)
    have hR1 : r (σ2 v) ≤ s2 (σ2 u) := by
      have h1 := rle_core r d l α hα hr hl hsf n hn σ2 s2 hopt2.1 (σ2 v)
        (by simpa [hpos2] using hau.trans huv')
      have h2 := hO a u hau
      rw [hσa] at h2
      linarith
    have hmid : ∀ p, u < p → p < v →
        r (σ2 p) ≤ s2 (σ2 p) + (l (σ2 v) - l (σ2 u)) ∧
        s2 (σ2 p) + (l (σ2 v) - l (σ2 u)) + l (σ2 p) ≤ d (σ2 p) := by
      intro p h1 h2
      exfalso
      rw [Fin.lt_def] at h1 h2
      omega
    obtain ⟨hF', hmk⟩ := swap_exch r d l hl σ2 s2 hopt2.1 u v huv' (hd hlt.le) hR1 hmid
    have hopt' : Optimum r d l ((Equiv.swap u v).trans σ2) (swapS l σ2 s2 u v) :=
      ⟨hF', fun σ'' s'' hF'' => hmk.trans (hopt2.2 σ'' s'' hF'')⟩
    have hau' : a ≠ u := ne_of_lt hau
    have hav' : a ≠ v := ne_of_lt (hau.trans huv')
    have hpos' : ((Equiv.swap u v).trans σ2).symm n = a := by
      have : ((Equiv.swap u v).trans σ2).symm n = Equiv.swap u v (σ2.symm n) := by
        simp only [Equiv.symm_trans_apply, Equiv.symm_swap]
      rw [this, hpos2]
      exact Equiv.swap_apply_of_ne_of_ne hau' hav'
    have hsn' : swapS l σ2 s2 u v n = s2 n := by
      apply swapS_out l σ2 s2 u v n huv'
      left; rw [hpos2]; exact hau
    have hmem : (Equiv.swap u v).trans σ2 ∈ C := by
      refine ⟨swapS l σ2 s2 u v, hopt', ?_, hpos', ?_, ?_⟩
      · intro i hi
        have hi' : a < ((Equiv.swap u v).trans σ2).symm i := by rw [hpos'] at hi; exact hi
        have hx : a < σ2.symm i := by
          by_contra hc
          push_neg at hc
          have h1 : σ2.symm i ≠ u := fun h => by rw [h] at hc; exact absurd hau (not_lt.mpr hc)
          have h2 : σ2.symm i ≠ v := fun h => by rw [h] at hc; exact absurd (hau.trans huv') (not_lt.mpr hc)
          have : ((Equiv.swap u v).trans σ2).symm i = σ2.symm i := by
            simp only [Equiv.symm_trans_apply, Equiv.symm_swap]
            exact Equiv.swap_apply_of_ne_of_ne h1 h2
          rw [this] at hi'
          exact absurd hi' (not_lt.mpr hc)
        rw [hsn']
        exact hrtp2 i (by rw [hpos2]; exact hx)
      · intro p hp
        have hpu : p ≠ u := ne_of_lt (hp.trans hau)
        have hpv : p ≠ v := ne_of_lt (hp.trans (hau.trans huv'))
        obtain ⟨h1, h2⟩ := hpre2 p hp
        refine ⟨?_, ?_⟩
        · simp only [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hpu hpv]; exact h1
        · rw [← h1, swapS_out l σ2 s2 u v (σ2 p) huv' (Or.inl (by simpa using hp.trans hau)), h1]
          exact h2
      · rw [hsn']; exact hsn2
    have hle := hσ2max _ hmem
    have hphi := phi_swap w (fun x : Fin N => (x.val : ℝ)) σ2 u v (ne_of_lt huv')
    have hwu : w u = (u.val : ℝ) := by simp [w, hau.trans_le le_rfl]
    have hwv : w v = (u.val : ℝ) + 1 := by
      have : a < v := hau.trans huv'
      simp only [w, if_pos this]; rw [huv]; push_cast; ring
    have hΦ : Φ ((Equiv.swap u v).trans σ2) = ∑ p, w p * ((σ2 (Equiv.swap u v p)).val : ℝ) := rfl
    have hΦ2 : Φ σ2 = ∑ p, w p * ((σ2 p).val : ℝ) := rfl
    rw [hΦ, hΦ2] at hle
    rw [hwu, hwv] at hphi
    have hv : (σ2 v).val < (σ2 u).val := hlt
    have hv' : ((σ2 v).val : ℝ) + 1 ≤ ((σ2 u).val : ℝ) := by exact_mod_cast hv
    nlinarith
  have hsorted : ∀ k : ℕ, ∀ u v : Fin N, v.val = u.val + k + 1 → a < u → σ2 u < σ2 v := by
    intro k
    induction k with
    | zero => intro u v h hau; exact hadj u v (by omega) hau
    | succ k ih =>
      intro u v h hau
      have hw : u.val + k + 1 < N := by have := v.isLt; omega
      have h1 := ih u ⟨u.val + k + 1, hw⟩ (by simp) hau
      have h2 := hadj ⟨u.val + k + 1, hw⟩ v (by simp; omega) (by
        rw [Fin.lt_def] at hau ⊢; simp; omega)
      exact h1.trans h2
  refine ⟨σ2, s2, hopt2, hrtp2, by rw [hpos2], hpre2, hsn2, ?_⟩
  intro p q hap hpq
  exact hsorted (q.val - p.val - 1) p q (by rw [Fin.lt_def] at hpq; omega) hap

theorem normalize_core {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (hd : Monotone d) (n : Fin N) (hnlast : n.val + 1 = N)
    (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (hopt : Optimum r d l σ s) (hrtp : ReleaseTimeProperty r σ s n) :
    ∃ (σ' : Fin N ≃ Fin N) (s' : Fin N → ℝ),
      Optimum r d l σ' s' ∧ ReleaseTimeProperty r σ' s' n ∧
      σ'.symm n = σ.symm n ∧
      (∀ p : Fin N, p < σ.symm n → σ' p = σ p ∧ s' (σ p) = s (σ p)) ∧
      s' n ≤ s n ∧
      s' n = max (r n) (⨆ i : {i : Fin N // σ'.symm i < σ'.symm n}, s' i + l i) ∧
      (∀ p q : Fin N, σ'.symm n < p → p < q → σ' p < σ' q) ∧
      (∀ p q : Fin N, σ'.symm n ≤ p → q.val = p.val + 1 →
        s' (σ' q) = s' (σ' p) + l (σ' p)) := by
  classical
  have hn : ∀ i, d i ≤ d n := fun i => hd (Fin.le_def.mpr (by have := i.isLt; omega))
  obtain ⟨σ2, s2, hopt2, hrtp2, hpos2, hpre2, hsn2, hsort⟩ :=
    sort_tail r d l α hα hr hl hsf hd n hnlast σ s hopt hrtp
  obtain ⟨s', hF', hle, hsame, h5, h7⟩ := compaction r d l α hr hl hsf n hn σ2 s2 hopt2.1
  haveI : Nonempty (Fin N) := ⟨n⟩
  have hmk : makespan l s' ≤ makespan l s2 := by
    unfold makespan
    exact ciSup_mono (Set.finite_range _).bddAbove (fun i => by linarith [hle i])
  refine ⟨σ2, s', ⟨hF', fun σ'' s'' hF'' => hmk.trans (hopt2.2 σ'' s'' hF'')⟩, ?_, hpos2, ?_, ?_, h5, ?_, h7⟩
  · intro i hi
    exact (hle n).trans_lt (hrtp2 i hi)
  · intro p hp
    obtain ⟨h1, h2⟩ := hpre2 p hp
    refine ⟨h1, ?_⟩
    rw [← h1, hsame (σ2 p) (by simpa [hpos2] using hp), ← h1] at *
    exact h2
  · rw [← hsn2]; exact hle n
  · rw [hpos2]; exact hsort

end GTWSched.MaxDisc

open GTWSched.MaxDisc


theorem solution {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (hd : Monotone d) (n : Fin N) (hnlast : n.val + 1 = N)
    (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (hopt : Optimum r d l σ s) (hrtp : ReleaseTimeProperty r σ s n) :
    ∃ (σ' : Fin N ≃ Fin N) (s' : Fin N → ℝ),
      Optimum r d l σ' s' ∧ ReleaseTimeProperty r σ' s' n ∧
      σ'.symm n = σ.symm n ∧
      (∀ p : Fin N, p < σ.symm n → σ' p = σ p ∧ s' (σ p) = s (σ p)) ∧
      s' n ≤ s n ∧
      s' n = max (r n) (⨆ i : {i : Fin N // σ'.symm i < σ'.symm n}, s' i.1 + l i.1) ∧
      (∀ p q : Fin N, σ'.symm n < p → p < q → σ' p < σ' q) ∧
      (∀ p q : Fin N, σ'.symm n ≤ p → q.val = p.val + 1 →
        s' (σ' q) = s' (σ' p) + l (σ' p)) := by
  exact normalize_core r d l α hα hr hl hsf hd n hnlast σ s hopt hrtp
