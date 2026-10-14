-- Prove2me | solution 1 for GTWSched.MaxDisc.corollary_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:46:33.516471+00:00
-- url     : https://prove2.me/submissions/a3ed8b15-4017-4537-9d12-e7e060b05f0c

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

theorem thm4_core {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (n : Fin N) (hn : ∀ i, d i ≤ d n)
    (hfeas : ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ), Feasible r d l σ s) :
    ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ),
      Optimum r d l σ s ∧ ReleaseTimeProperty r σ s n := by
  classical
  haveI : Nonempty (Fin N) := ⟨n⟩
  obtain ⟨σ0, s0, h0⟩ := exists_optimum r d l hl hfeas
  have F1 : ∀ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ), Feasible r d l σ s → d n ≤ s n + l n + α := by
    intro σ s hF
    have h1 := (hF.2 n).1
    have h2 := hr n
    rcases hsf n with h | ⟨h0, h1'⟩ <;> linarith
  have F3 : ∀ i, d i ≤ r i + l i + α := by
    intro i
    rcases hsf i with h | ⟨h0, h1⟩ <;> linarith
  let U : Set (Fin N ≃ Fin N) := {σ | ∃ s, Optimum r d l σ s}
  have hUne : U.Nonempty := ⟨σ0, s0, h0⟩
  obtain ⟨σ1, hσ1U, hσ1max⟩ := Set.exists_max_image U (fun σ => (σ.symm n).val) (Set.toFinite _) hUne
  obtain ⟨P, hP⟩ : ∃ P, P = (σ1.symm n).val := ⟨_, rfl⟩
  let U2 : Set (Fin N ≃ Fin N) := {σ | σ ∈ U ∧ (σ.symm n).val = P}
  let w : Fin N → ℝ := fun p => if P < p.val then (p.val : ℝ) else 0
  let Φ : (Fin N ≃ Fin N) → ℝ := fun σ => ∑ p, w p * d (σ p)
  obtain ⟨σ2, ⟨⟨s2, hopt2⟩, hP2⟩, hσ2max⟩ :=
    Set.exists_max_image U2 Φ (Set.toFinite _) ⟨σ1, hσ1U, hP.symm⟩
  refine ⟨σ2, s2, hopt2, ?_⟩
  obtain ⟨hO, hRD⟩ := hopt2.1
  set a : Fin N := σ2.symm n with ha
  have hσa : σ2 a = n := by simp [ha]
  have hsn : s2 n = s2 (σ2 a) := by rw [hσa]
  -- optimum-ness of exchanged schedule
  have hopt_swap : ∀ u v : Fin N, ∀ (hab : u < v), d (σ2 v) ≤ d (σ2 u) → r (σ2 v) ≤ s2 (σ2 u) →
      (∀ p, u < p → p < v →
        r (σ2 p) ≤ s2 (σ2 p) + (l (σ2 v) - l (σ2 u)) ∧
        s2 (σ2 p) + (l (σ2 v) - l (σ2 u)) + l (σ2 p) ≤ d (σ2 p)) →
      ∃ s', Optimum r d l ((Equiv.swap u v).trans σ2) s' := by
    intro u v huv hd hR1 hmid
    obtain ⟨hF', hmk⟩ := swap_exch r d l hl σ2 s2 hopt2.1 u v huv hd hR1 hmid
    exact ⟨_, hF', fun σ'' s'' hF'' => hmk.trans (hopt2.2 σ'' s'' hF'')⟩
  -- sortedness of the tail, adjacent version
  have hadj : ∀ u v : Fin N, v.val = u.val + 1 → a < u → d (σ2 u) ≤ d (σ2 v) := by
    intro u v huv hau
    by_contra hlt
    push_neg at hlt
    have huv' : u < v := by rw [Fin.lt_def]; omega
    have hR1 : r (σ2 v) ≤ s2 (σ2 u) := by
      have h1 := rle_core r d l α hα hr hl hsf n hn σ2 s2 hopt2.1 (σ2 v)
        (by simpa using hau.trans huv')
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
    obtain ⟨s', hs'⟩ := hopt_swap u v huv' hlt.le hR1 hmid
    have hmem : (Equiv.swap u v).trans σ2 ∈ U2 := by
      refine ⟨⟨s', hs'⟩, ?_⟩
      have hau' : a ≠ u := ne_of_lt hau
      have hav' : a ≠ v := ne_of_lt (hau.trans huv')
      have : ((Equiv.swap u v).trans σ2).symm n = a := by
        simp only [Equiv.symm_trans_apply, Equiv.symm_swap]
        exact Equiv.swap_apply_of_ne_of_ne hau' hav'
      rw [this]; exact hP2
    have hle := hσ2max _ hmem
    have hphi := phi_swap w d σ2 u v (ne_of_lt huv')
    have hwu : w u = (u.val : ℝ) := by
      have : P < u.val := by rw [← hP2]; exact hau
      simp [w, this]
    have hwv : w v = (u.val : ℝ) + 1 := by
      have : P < v.val := by rw [← hP2]; exact hau.trans huv'
      simp only [w, if_pos this]; rw [huv]; push_cast; ring
    have hΦ : Φ ((Equiv.swap u v).trans σ2) = ∑ p, w p * d (σ2 (Equiv.swap u v p)) := rfl
    have hΦ2 : Φ σ2 = ∑ p, w p * d (σ2 p) := rfl
    rw [hΦ, hΦ2] at hle
    rw [hwu, hwv] at hphi
    nlinarith
  -- general sortedness
  have hsorted : ∀ k : ℕ, ∀ u v : Fin N, v.val = u.val + k → a < u → d (σ2 u) ≤ d (σ2 v) := by
    intro k
    induction k with
    | zero =>
      intro u v h _
      have : u = v := Fin.ext (by omega)
      rw [this]
    | succ k ih =>
      intro u v h hau
      have hw : u.val + k < N := by have := v.isLt; omega
      have h1 := ih u ⟨u.val + k, hw⟩ (by simp) hau
      have h2 := hadj ⟨u.val + k, hw⟩ v (by simp; omega) (by
        rw [Fin.lt_def] at hau ⊢; simp; omega)
      exact h1.trans h2
  have hsorted' : ∀ u v : Fin N, a < u → u < v → d (σ2 u) ≤ d (σ2 v) := by
    intro u v hau huv
    exact hsorted (v.val - u.val) u v (by rw [Fin.lt_def] at huv; omega) hau
  -- violator step
  by_contra hnot
  have hex : ∃ i, a < σ2.symm i ∧ r i ≤ s2 n := by
    unfold ReleaseTimeProperty at hnot
    push_neg at hnot
    exact hnot
  obtain ⟨i0, hi0, hri0⟩ := hex
  let V : Finset (Fin N) := Finset.univ.filter (fun p => a < p ∧ r (σ2 p) ≤ s2 n)
  have hVne : V.Nonempty := ⟨σ2.symm i0, by simp [V, hi0, hri0]⟩
  obtain ⟨q, hqV, hqmin⟩ := Finset.exists_min_image V (fun p => p) hVne
  simp only [V, Finset.mem_filter, Finset.mem_univ, true_and] at hqV
  obtain ⟨haq, hrq⟩ := hqV
  have hnonviol : ∀ p, a < p → p < q → s2 n < r (σ2 p) := by
    intro p hap hpq
    by_contra hc
    push_neg at hc
    have : p ∈ V := by simp [V, hap, hc]
    exact absurd (hqmin p this) (not_le.mpr hpq)
  have hd : d (σ2 q) ≤ d (σ2 a) := by rw [hσa]; exact hn _
  have hR1 : r (σ2 q) ≤ s2 (σ2 a) := by rw [hσa]; exact hrq
  have hmid : ∀ p, a < p → p < q →
      r (σ2 p) ≤ s2 (σ2 p) + (l (σ2 q) - l (σ2 a)) ∧
      s2 (σ2 p) + (l (σ2 q) - l (σ2 a)) + l (σ2 p) ≤ d (σ2 p) := by
    intro p hap hpq
    have hv := hnonviol p hap hpq
    have hdxy := hsorted' p q hap hpq
    have hsp := hO a p hap
    have hsq := hO p q hpq
    rw [hσa] at hsp ⊢
    have hFn := F1 σ2 s2 hopt2.1
    have hy := (hRD (σ2 q)).2
    have hx := hRD (σ2 p)
    have hyF := F3 (σ2 q)
    have hdy := hn (σ2 q)
    have hr0 := hr n
    have hsn0 := (hRD n).1
    have hlx := hl (σ2 p)
    have hly := hl (σ2 q)
    have hln := hl n
    have hspec : d (σ2 p) = r (σ2 p) + l (σ2 p) + α := by
      rcases hsf (σ2 p) with h | ⟨h0, h1⟩
      · linarith
      · exfalso; linarith
    constructor <;> nlinarith
  obtain ⟨s', hs'⟩ := hopt_swap a q haq hd hR1 hmid
  have hmemU : (Equiv.swap a q).trans σ2 ∈ U := ⟨s', hs'⟩
  have hle := hσ1max _ hmemU
  have : ((Equiv.swap a q).trans σ2).symm n = q := by
    simp [Equiv.symm_trans_apply, ha]
  rw [this] at hle
  have : a.val = P := hP2
  have hq : a.val < q.val := haq
  omega


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

lemma exists_opt_sub (j : ℕ) (r' d' l' : Fin j → ℝ) (hl' : ∀ i, 0 ≤ l' i)
    (hfeas' : ∃ (σ : Fin j ≃ Fin j) (s : Fin j → ℝ), Feasible r' d' l' σ s) :
    ∃ (σ : Fin j ≃ Fin j) (s : Fin j → ℝ), Optimum r' d' l' σ s := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine ⟨Equiv.refl _, fun i => i.elim0, ⟨fun p q _ => p.elim0, fun i => i.elim0⟩,
      fun σ' s' _ => ?_⟩
    simp [makespan]
  · haveI : Nonempty (Fin j) := ⟨⟨0, hj⟩⟩
    exact exists_optimum r' d' l' hl' hfeas'

lemma fpc_eq {N : ℕ} (l s : Fin N → ℝ) (j : ℕ) (hj : j ≤ N) (s'' : Fin j → ℝ)
    (h : ∀ x : Fin j, s (Fin.castLE hj x) = s'' x) :
    firstPartCompletion l s j = makespan (fun x => l (Fin.castLE hj x)) s'' := by
  unfold firstPartCompletion makespan
  let e : Fin j ≃ {i : Fin N // i.val < j} :=
    ⟨fun x => ⟨Fin.castLE hj x, by simp⟩, fun y => ⟨y.1.val, y.2⟩,
      fun x => by simp, fun y => by ext; simp⟩
  rw [← Equiv.iSup_comp e]
  apply iSup_congr
  intro x
  simp only [e, Equiv.coe_fn_mk]
  rw [h x]

lemma downset_facts {N : ℕ} (d : Fin N → ℝ) (hd : Monotone d) (n : Fin N) (hnlast : n.val + 1 = N)
    (σ : Fin N ≃ Fin N) (β : ℝ)
    (hsplit : ∀ i, i ≠ n → (σ.symm i < σ.symm n ↔ d i ≤ β)) :
    (∀ i, σ.symm i < σ.symm n → i.val < (σ.symm n).val) ∧
    (∀ i, i.val < (σ.symm n).val → σ.symm i < σ.symm n) := by
  classical
  set a : Fin N := σ.symm n with ha
  let B : Finset (Fin N) := Finset.univ.filter (fun i => σ.symm i < a)
  have hBcard : B.card = a.val := by
    have : B.card = (Finset.univ.filter (fun p : Fin N => p < a)).card :=
      Finset.card_equiv σ.symm (fun i => by simp [B])
    rw [this]
    have : Finset.univ.filter (fun p : Fin N => p < a) = Finset.Iio a := by ext; simp
    rw [this]; simp
  have hnB : ∀ i ∈ B, i ≠ n := by
    intro i hi hin
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [hin] at hi
    exact lt_irrefl _ hi
  have hdown : ∀ i ∈ B, ∀ i', i' ≤ i → i' ∈ B := by
    intro i hi i' hii'
    have hin := hnB i hi
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have h1 := (hsplit i hin).mp hi
    have hi_lt : i < n := by
      rw [Fin.lt_def]
      have := i.isLt
      have hne : i.val ≠ n.val := fun h => hin (Fin.ext h)
      omega
    have hne' : i' ≠ n := ne_of_lt (lt_of_le_of_lt hii' hi_lt)
    exact (hsplit i' hne').mpr ((hd hii').trans h1)
  have C1 : ∀ i, σ.symm i < a → i.val < a.val := by
    intro i0 hi0
    by_contra hc
    push_neg at hc
    have hsub : Finset.Iic i0 ⊆ B := by
      intro x hx
      exact hdown i0 (by simp [B, hi0]) x (Finset.mem_Iic.mp hx)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic, hBcard] at this
    omega
  refine ⟨C1, ?_⟩
  have hsub : B ⊆ Finset.Iio a := by
    intro x hx
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_Iio, Fin.lt_def]
    exact C1 x hx
  have hcard : (Finset.Iio a).card ≤ B.card := by rw [Fin.card_Iio, hBcard]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  intro i hi
  have : i ∈ Finset.Iio a := by simp [Fin.lt_def, hi]
  rw [← heq] at this
  simpa [B] using this

lemma after_order_fact {N : ℕ} (σ : Fin N ≃ Fin N) (n : Fin N) (hnlast : n.val + 1 = N)
    (j : ℕ) (hj : j < N) (hpos : (σ.symm n).val = j)
    (hge : ∀ p : Fin N, j ≤ p.val → j ≤ (σ p).val)
    (hsort : ∀ p q : Fin N, σ.symm n < p → p < q → σ p < σ q) :
    ∀ p : Fin N, j < p.val → (σ p).val + 1 = p.val := by
  have LB : ∀ k, j + 1 ≤ k → ∀ hk : k < N, k - 1 ≤ (σ ⟨k, hk⟩).val := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro hk'
      have := hge ⟨j + 1, hk'⟩ (by simp)
      simpa using this
    | succ k hk ih =>
      intro hk'
      have h1 := ih (by omega)
      have h2 := hsort ⟨k, by omega⟩ ⟨k + 1, hk'⟩
        (by rw [Fin.lt_def]; simp; omega) (by simp [Fin.lt_def])
      have h3 : (σ ⟨k, by omega⟩).val < (σ ⟨k + 1, hk'⟩).val := h2
      simp only [Nat.add_sub_cancel]
      omega
  have UB : ∀ m k, N - 1 - k = m → j < k → ∀ hk : k < N, (σ ⟨k, hk⟩).val ≤ k - 1 := by
    intro m
    induction m with
    | zero =>
      intro k hkm hjk hk
      have hk' : k = N - 1 := by omega
      have hne : σ ⟨k, hk⟩ ≠ n := by
        intro h
        have : σ.symm n = ⟨k, hk⟩ := by rw [← h]; simp
        rw [this] at hpos
        simp at hpos
        omega
      have : (σ ⟨k, hk⟩).val ≠ n.val := fun h => hne (Fin.ext h)
      have := (σ ⟨k, hk⟩).isLt
      omega
    | succ m ih =>
      intro k hkm hjk hk
      have hk1 : k + 1 < N := by omega
      have h1 := ih (k + 1) (by omega) (by omega) hk1
      have h2 := hsort ⟨k, hk⟩ ⟨k + 1, hk1⟩
        (by rw [Fin.lt_def]; simp; omega) (by simp [Fin.lt_def])
      have h3 : (σ ⟨k, hk⟩).val < (σ ⟨k + 1, hk1⟩).val := h2
      simp only [Nat.add_sub_cancel] at h1
      omega
  intro p hp
  have h1 := LB p.val (by omega) p.isLt
  have h2 := UB (N - 1 - p.val) p.val rfl hp p.isLt
  have : (σ ⟨p.val, p.isLt⟩) = σ p := by simp
  rw [this] at h1 h2
  omega


theorem cor2_core {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (hd : Monotone d) (n : Fin N) (hnlast : n.val + 1 = N)
    (hfeas : ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ), Feasible r d l σ s) :
    ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ) (j : ℕ),
      Optimum r d l σ s ∧ StandardForm r d l σ s j ∧ ReleaseTimeProperty r σ s n := by
  classical
  haveI : Nonempty (Fin N) := ⟨n⟩
  have hn : ∀ i, d i ≤ d n := fun i => hd (Fin.le_def.mpr (by have := i.isLt; omega))
  obtain ⟨σ0, s0, hopt0, hrtp0⟩ := thm4_core r d l α hα hr hl hsf n hn hfeas
  obtain ⟨σ1, s1, hopt1, hrtp1, hpos1, hpre1, hle1, h5, hsort1, h7⟩ :=
    normalize_core r d l α hα hr hl hsf hd n hnlast σ0 s0 hopt0 hrtp0
  have hsplit := rtp_core r d l α hα hr hl hsf n σ1 s1 hopt1.1 hrtp1
  obtain ⟨C1, C2⟩ := downset_facts d hd n hnlast σ1 (s1 n + α) hsplit
  obtain ⟨hO1, hRD1⟩ := hopt1.1
  set a : Fin N := σ1.symm n with ha
  obtain ⟨j, hj⟩ : ∃ j, j = a.val := ⟨_, rfl⟩
  have hjN : j < N := by rw [hj]; exact a.isLt
  have hjle : j ≤ N := hjN.le
  have hσ1a : σ1 a = n := by simp [ha]
  have hge : ∀ p : Fin N, j ≤ p.val → j ≤ (σ1 p).val := by
    intro p hp
    by_contra hc
    push_neg at hc
    have h1 := C2 (σ1 p) (by rw [← hj]; exact hc)
    simp only [Equiv.symm_apply_apply] at h1
    rw [Fin.lt_def] at h1
    omega
  have hfirst : ∀ p : Fin N, p.val < j → (σ1 p).val < j := by
    intro p hp
    have := C1 (σ1 p) (by simp only [Equiv.symm_apply_apply]; rw [Fin.lt_def]; omega)
    omega
  have hnj : j ≤ n.val := by omega
  -- the first part as a sub-instance
  let r' : Fin j → ℝ := fun x => r (Fin.castLE hjle x)
  let d' : Fin j → ℝ := fun x => d (Fin.castLE hjle x)
  let l' : Fin j → ℝ := fun x => l (Fin.castLE hjle x)
  let fR : Fin j → Fin j := fun x => ⟨(σ1 (Fin.castLE hjle x)).val, hfirst _ (by simp)⟩
  have hfRinj : Function.Injective fR := by
    intro x y hxy
    have h1 : (σ1 (Fin.castLE hjle x)).val = (σ1 (Fin.castLE hjle y)).val := by
      have := congrArg Fin.val hxy
      exact this
    have h2 := σ1.injective (Fin.ext h1)
    exact Fin.castLE_injective hjle h2
  let σR : Fin j ≃ Fin j := Equiv.ofBijective fR (Finite.injective_iff_bijective.mp hfRinj)
  let sR : Fin j → ℝ := fun x => s1 (Fin.castLE hjle x)
  have hσR : ∀ x, Fin.castLE hjle (σR x) = σ1 (Fin.castLE hjle x) := fun x => Fin.ext rfl
  have feasR : Feasible r' d' l' σR sR := by
    refine ⟨fun p q hpq => ?_, fun i => hRD1 _⟩
    show s1 (Fin.castLE hjle (σR p)) + l (Fin.castLE hjle (σR p)) ≤ s1 (Fin.castLE hjle (σR q))
    rw [hσR, hσR]
    exact hO1 _ _ hpq
  obtain ⟨σ'', s'', hopt''⟩ := exists_opt_sub j r' d' l' (fun i => hl _) ⟨σR, sR, feasR⟩
  have hmk'' : makespan l' s'' ≤ makespan l' sR := hopt''.2 σR sR feasR
  have hfpc1 : firstPartCompletion l s1 j = makespan l' sR := fpc_eq l s1 j hjle sR (fun x => rfl)
  have hfpc_le : firstPartCompletion l s1 j ≤ s1 n := by
    unfold firstPartCompletion
    apply Real.iSup_le
    · intro i
      have h1 := hO1 (σ1.symm i.1) a (C2 i.1 (by rw [← hj]; exact i.2))
      simp only [Equiv.apply_symm_apply, hσ1a] at h1
      exact h1
    · exact (hr n).trans (hRD1 n).1
  have hmk''n : makespan l' s'' ≤ s1 n := by
    calc makespan l' s'' ≤ makespan l' sR := hmk''
      _ = firstPartCompletion l s1 j := hfpc1.symm
      _ ≤ s1 n := hfpc_le
  have hfin'' : ∀ x : Fin j, s'' x + l' x ≤ makespan l' s'' := fun x =>
    le_ciSup (f := fun x => s'' x + l' x) (Set.finite_range _).bddAbove x
  -- the new order
  let fM : Fin N → Fin N := fun p =>
    if h : p.val < j then Fin.castLE hjle (σ'' ⟨p.val, h⟩) else σ1 p
  have hfM_lt : ∀ p (h : p.val < j), fM p = Fin.castLE hjle (σ'' ⟨p.val, h⟩) := by
    intro p h; simp [fM, h]
  have hfM_ge : ∀ p, j ≤ p.val → fM p = σ1 p := by
    intro p h; simp [fM, not_lt.mpr h]
  have hfMinj : Function.Injective fM := by
    intro p q hpq
    by_cases hp : p.val < j <;> by_cases hq : q.val < j
    · rw [hfM_lt p hp, hfM_lt q hq] at hpq
      have h1 := σ''.injective (Fin.castLE_injective hjle hpq)
      exact Fin.ext (by simpa using congrArg Fin.val h1)
    · exfalso
      rw [hfM_lt p hp, hfM_ge q (not_lt.mp hq)] at hpq
      have h1 := hge q (not_lt.mp hq)
      rw [← hpq] at h1
      have := (σ'' ⟨p.val, hp⟩).isLt
      simp at h1
      omega
    · exfalso
      rw [hfM_ge p (not_lt.mp hp), hfM_lt q hq] at hpq
      have h1 := hge p (not_lt.mp hp)
      rw [hpq] at h1
      have := (σ'' ⟨q.val, hq⟩).isLt
      simp at h1
      omega
    · rw [hfM_ge p (not_lt.mp hp), hfM_ge q (not_lt.mp hq)] at hpq
      exact σ1.injective hpq
  let σM : Fin N ≃ Fin N := Equiv.ofBijective fM (Finite.injective_iff_bijective.mp hfMinj)
  have hσM_lt : ∀ p (h : p.val < j), σM p = Fin.castLE hjle (σ'' ⟨p.val, h⟩) := hfM_lt
  have hσM_ge : ∀ p, j ≤ p.val → σM p = σ1 p := hfM_ge
  have hσMval_lt : ∀ p : Fin N, p.val < j → (σM p).val < j := by
    intro p h; rw [hσM_lt p h]; simp
  have hσMval_ge : ∀ p : Fin N, j ≤ p.val → j ≤ (σM p).val := by
    intro p h; rw [hσM_ge p h]; exact hge p h
  have hσMa : σM a = n := by rw [hσM_ge a (by omega), hσ1a]
  have hposM : σM.symm n = a := by rw [Equiv.symm_apply_eq]; exact hσMa.symm
  have hsymm_lt : ∀ i : Fin N, i.val < j → σM.symm i < a := by
    intro i hi
    by_contra hc
    push_neg at hc
    have h1 := hσMval_ge (σM.symm i) (by rw [Fin.le_def] at hc; omega)
    simp at h1
    omega
  have hsymm_lt' : ∀ i : Fin N, σM.symm i < a → i.val < j := by
    intro i hi
    have h1 := hσMval_lt (σM.symm i) (by rw [Fin.lt_def] at hi; omega)
    simpa using h1
  -- the new times
  let sM : Fin N → ℝ := fun i => if h : i.val < j then s'' ⟨i.val, h⟩ else s1 i
  have hsM_lt : ∀ x : Fin j, sM (Fin.castLE hjle x) = s'' x := by
    intro x; simp [sM]
  have hsM_ge : ∀ i : Fin N, j ≤ i.val → sM i = s1 i := by
    intro i h; simp [sM, not_lt.mpr h]
  have hs1n : s1 n ≤ s1 (σ1 a) := by rw [hσ1a]
  have feasM : Feasible r d l σM sM := by
    refine ⟨fun p q hpq => ?_, fun i => ?_⟩
    · by_cases hp : p.val < j
      · have hx := σM p
        by_cases hq : q.val < j
        · rw [hσM_lt p hp, hσM_lt q hq, hsM_lt, hsM_lt]
          exact hopt''.1.1 ⟨p.val, hp⟩ ⟨q.val, hq⟩ hpq
        · rw [hσM_lt p hp, hsM_lt, hσM_ge q (not_lt.mp hq),
            hsM_ge _ (hge q (not_lt.mp hq))]
          have h1 := hfin'' (σ'' ⟨p.val, hp⟩)
          have h2 : s1 n ≤ s1 (σ1 q) := by
            rcases eq_or_lt_of_le (show a ≤ q by rw [Fin.le_def]; omega) with h | h
            · rw [← h, hσ1a]
            · have := hO1 a q h
              rw [hσ1a] at this
              linarith [hl n]
          show s'' (σ'' ⟨p.val, hp⟩) + l' (σ'' ⟨p.val, hp⟩) ≤ _
          linarith
      · have hq : ¬ q.val < j := by rw [Fin.lt_def] at hpq; omega
        rw [hσM_ge p (not_lt.mp hp), hσM_ge q (not_lt.mp hq),
          hsM_ge _ (hge p (not_lt.mp hp)), hsM_ge _ (hge q (not_lt.mp hq))]
        exact hO1 p q hpq
    · by_cases hi : i.val < j
      · have h1 := hopt''.1.2 ⟨i.val, hi⟩
        have : Fin.castLE hjle ⟨i.val, hi⟩ = i := Fin.ext rfl
        rw [show sM i = s'' ⟨i.val, hi⟩ by rw [← hsM_lt]; rw [this]]
        have e1 : r' ⟨i.val, hi⟩ = r i := by simp only [r']; rw [this]
        have e2 : d' ⟨i.val, hi⟩ = d i := by simp only [d']; rw [this]
        have e3 : l' ⟨i.val, hi⟩ = l i := by simp only [l']; rw [this]
        rw [e1, e2, e3] at h1
        exact h1
      · rw [hsM_ge i (not_lt.mp hi)]
        exact hRD1 i
  have hmkM : makespan l sM ≤ makespan l s1 := by
    unfold makespan
    apply ciSup_le
    intro i
    by_cases hi : i.val < j
    · have : Fin.castLE hjle ⟨i.val, hi⟩ = i := Fin.ext rfl
      have h1 := hfin'' ⟨i.val, hi⟩
      have e3 : l' ⟨i.val, hi⟩ = l i := by simp only [l']; rw [this]
      rw [e3, ← hsM_lt ⟨i.val, hi⟩, this] at h1
      have h2 : s1 n + l n ≤ ⨆ i, s1 i + l i :=
        le_ciSup (f := fun i => s1 i + l i) (Set.finite_range _).bddAbove n
      have h3 : makespan l' s'' ≤ s1 n := hmk''n
      linarith [hl n]
    · rw [hsM_ge i (not_lt.mp hi)]
      exact le_ciSup (f := fun i => s1 i + l i) (Set.finite_range _).bddAbove i
  have hoptM : Optimum r d l σM sM :=
    ⟨feasM, fun σ' s' hF' => hmkM.trans (hopt1.2 σ' s' hF')⟩
  have hrtpM : ReleaseTimeProperty r σM sM n := by
    intro i hi
    rw [hposM] at hi
    have hq : j ≤ (σM.symm i).val := by rw [Fin.lt_def] at hi; omega
    have hi' : σM (σM.symm i) = i := by simp
    rw [hσM_ge _ hq] at hi'
    have hs1 : σ1.symm i = σM.symm i := by
      rw [Equiv.symm_apply_eq]; exact hi'.symm
    have := hrtp1 i (by rw [hs1]; exact hi)
    rw [hsM_ge n hnj]
    exact this
  obtain ⟨sf, hFf, hlef, hsamef, h5f, h7f⟩ := compaction r d l α hr hl hsf n hn σM sM hoptM.1
  have hmkf : makespan l sf ≤ makespan l sM := by
    unfold makespan
    exact ciSup_mono (Set.finite_range _).bddAbove (fun i => by linarith [hlef i])
  have hoptf : Optimum r d l σM sf :=
    ⟨hFf, fun σ' s' hF' => hmkf.trans (hoptM.2 σ' s' hF')⟩
  have hrtpf : ReleaseTimeProperty r σM sf n := fun i hi =>
    (hlef n).trans_lt (hrtpM i hi)
  have hsf_lt : ∀ x : Fin j, sf (Fin.castLE hjle x) = s'' x := by
    intro x
    rw [hsamef _ (by rw [hposM]; exact hsymm_lt _ (by simp)), hsM_lt]
  have hfpcf : firstPartCompletion l sf j = makespan l' s'' := fpc_eq l sf j hjle s'' hsf_lt
  refine ⟨σM, sf, j, hoptf, ?_, hrtpf⟩
  refine ⟨hjN, hσMval_lt, ⟨fun p q hpq _ => hFf.1 p q hpq, fun i _ => hFf.2 i, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro σ' s' hF'
    rw [hfpcf]
    exact hopt''.2 σ' s' hF'
  · intro p hp
    have : p = a := Fin.ext (by omega)
    rw [this, hσMa]; exact hnlast
  · intro p hp
    have : p = a := Fin.ext (by omega)
    rw [this, hσMa]
    rw [h5f, hposM]
    congr 1
    unfold firstPartCompletion
    exact Equiv.iSup_congr (Equiv.subtypeEquivRight (fun i => ⟨hsymm_lt' i, hsymm_lt i⟩)) (fun x => rfl)
  · apply after_order_fact σM n hnlast j hjN (by rw [hposM]; exact hj.symm) hσMval_ge
    intro p q hp hpq
    rw [hposM] at hp
    have hp' : j ≤ p.val := by rw [Fin.lt_def] at hp; omega
    have hq' : j ≤ q.val := by rw [Fin.lt_def] at hpq; omega
    rw [hσM_ge p hp', hσM_ge q hq']
    exact hsort1 p q hp hpq
  · intro p q hp hq
    exact h7f p q (by rw [hposM, Fin.le_def]; omega) hq

end GTWSched.MaxDisc

open GTWSched.MaxDisc


theorem solution {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (hd : Monotone d) (n : Fin N) (hnlast : n.val + 1 = N)
    (hfeas : ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ), Feasible r d l σ s) :
    ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ) (j : ℕ),
      Optimum r d l σ s ∧ StandardForm r d l σ s j ∧ ReleaseTimeProperty r σ s n := by
  exact cor2_core r d l α hα hr hl hsf hd n hnlast hfeas
