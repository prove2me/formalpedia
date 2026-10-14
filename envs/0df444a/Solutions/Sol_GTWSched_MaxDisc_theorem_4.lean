-- Prove2me | solution 1 for GTWSched.MaxDisc.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:36:14.156531+00:00
-- url     : https://prove2.me/submissions/4b827b91-134b-4909-a444-47f77da70ff3

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

end GTWSched.MaxDisc

open GTWSched.MaxDisc


theorem solution {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (n : Fin N) (hn : ∀ i, d i ≤ d n)
    (hfeas : ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ), Feasible r d l σ s) :
    ∃ (σ : Fin N ≃ Fin N) (s : Fin N → ℝ),
      Optimum r d l σ s ∧ ReleaseTimeProperty r σ s n := by
  exact thm4_core r d l α hα hr hl hsf n hn hfeas
