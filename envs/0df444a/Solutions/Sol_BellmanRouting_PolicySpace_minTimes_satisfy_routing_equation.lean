-- Prove2me | solution 1 for BellmanRouting.PolicySpace.minTimes_satisfy_routing_equation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T19:24:48.794207+00:00
-- url     : https://prove2.me/submissions/793f8e28-4faa-451f-897f-3492fee576fa

import Mathlib
import Definitions.Def_BellmanRouting_PolicySpace_Routing

open BellmanRouting.PolicySpace

namespace RouteAux

variable {n : ℕ}

theorem isRoute_cons {i j : Fin (n + 1)} {l : List (Fin (n + 1))} :
    IsRoute i (j :: l) ↔ i ≠ j ∧ IsRoute j l := Iff.rfl

theorem routeTime_cons (t : Fin (n + 1) → Fin (n + 1) → ℝ) (i j : Fin (n + 1))
    (l : List (Fin (n + 1))) : routeTime t i (j :: l) = t i j + routeTime t j l := rfl

theorem minStep_last (t : Fin (n + 1) → Fin (n + 1) → ℝ) (F : Fin (n + 1) → ℝ) :
    minStep t F (Fin.last n) = 0 := by simp [minStep]

theorem minStep_of_ne (t : Fin (n + 1) → Fin (n + 1) → ℝ) (F : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (h : i ≠ Fin.last n) :
    minStep t F i = (Finset.univ.erase i).inf' (erase_nonempty h) (fun j => t i j + F j) := by
  simp [minStep, h]

theorem routeTime_nonneg (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    ∀ (l : List (Fin (n + 1))) (i : Fin (n + 1)), IsRoute i l → 0 ≤ routeTime t i l := by
  intro l
  induction l with
  | nil => intro i _; simp [routeTime]
  | cons j l ih =>
    intro i h
    rw [routeTime_cons]
    have := ht i j h.1
    have := ih j h.2
    linarith

/-- positive-time routes: a route through `c` has time at least the rest of the route. -/
theorem route_split (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    ∀ (a : List (Fin (n + 1))) (j c : Fin (n + 1)) (b : List (Fin (n + 1))),
      IsRoute j (a ++ c :: b) → IsRoute c b ∧ routeTime t c b ≤ routeTime t j (a ++ c :: b) := by
  intro a
  induction a with
  | nil =>
    intro j c b h
    refine ⟨h.2, ?_⟩
    rw [List.nil_append, routeTime_cons]
    have := ht j c h.1
    linarith
  | cons x a ih =>
    intro j c b h
    rw [List.cons_append] at h ⊢
    obtain ⟨h1, h2⟩ := h
    obtain ⟨r1, r2⟩ := ih x c b h2
    refine ⟨r1, ?_⟩
    rw [routeTime_cons]
    have := ht j x h1
    linarith

/-- every route can be replaced by a simple route that is not slower. -/
theorem exists_simple (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    ∀ (l : List (Fin (n + 1))) (i : Fin (n + 1)), IsRoute i l →
      ∃ l', IsRoute i l' ∧ (i :: l').Nodup ∧ routeTime t i l' ≤ routeTime t i l := by
  intro l
  induction l with
  | nil =>
    intro i h
    exact ⟨[], h, by simp, le_rfl⟩
  | cons j l ih =>
    intro i h
    obtain ⟨hij, hjl⟩ := h
    obtain ⟨l1, r1, nd1, tm1⟩ := ih j hjl
    have hnn := routeTime_nonneg t ht l j hjl
    by_cases hi : i ∈ l1
    · obtain ⟨a, b, hab⟩ := List.append_of_mem hi
      subst hab
      obtain ⟨r2, tm2⟩ := route_split t ht a j i b r1
      refine ⟨b, r2, ?_, ?_⟩
      · have hsub : (i :: b).Sublist (j :: (a ++ i :: b)) := by
          exact List.Sublist.cons _ (List.sublist_append_right a (i :: b))
        exact nd1.sublist hsub
      · have := ht i j hij
        rw [routeTime_cons]
        linarith
    · refine ⟨j :: l1, ⟨hij, r1⟩, ?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨?_, nd1⟩
        intro hm
        rcases List.mem_cons.mp hm with h | h
        · exact hij h
        · exact hi h
      · rw [routeTime_cons, routeTime_cons]
        linarith

theorem simple_length_le (i : Fin (n + 1)) (l : List (Fin (n + 1))) (h : (i :: l).Nodup) :
    l.length ≤ n := by
  have := h.length_le_card
  simp at this
  omega

end RouteAux

namespace RouteAux

variable {n : ℕ}

theorem approx_zero_last (t : Fin (n + 1) → Fin (n + 1) → ℝ) : approx t 0 (Fin.last n) = 0 := by
  simp [approx]

theorem approx_zero_ne (t : Fin (n + 1) → Fin (n + 1) → ℝ) {i : Fin (n + 1)}
    (h : i ≠ Fin.last n) : approx t 0 i = t i (Fin.last n) := by
  simp [approx, h]

theorem approx_succ (t : Fin (n + 1) → Fin (n + 1) → ℝ) (k : ℕ) :
    approx t (k + 1) = minStep t (approx t k) := rfl

theorem approx_within (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    ∀ k i, IsMinTimeWithin t k i (approx t k i) := by
  intro k
  induction k with
  | zero =>
    intro i
    by_cases hi : i = Fin.last n
    · subst hi
      rw [approx_zero_last]
      refine ⟨⟨[], rfl, by simp, rfl⟩, ?_⟩
      intro l hl _
      exact routeTime_nonneg t ht l _ hl
    · rw [approx_zero_ne t hi]
      refine ⟨⟨[Fin.last n], ⟨hi, rfl⟩, by simp, by simp [routeTime]⟩, ?_⟩
      intro l hl hlen
      match l, hl, hlen with
      | [], hl, _ => exact absurd hl hi
      | [j], hl, _ =>
        obtain ⟨hij, hj⟩ := hl
        have hj' : j = Fin.last n := hj
        subst hj'
        simp [routeTime]
      | j :: j' :: l, _, hlen => simp at hlen
  | succ k ih =>
    intro i
    by_cases hi : i = Fin.last n
    · subst hi
      have : approx t (k + 1) (Fin.last n) = 0 := by rw [approx_succ]; exact minStep_last t _
      rw [this]
      refine ⟨⟨[], rfl, by simp, rfl⟩, ?_⟩
      intro l hl _
      exact routeTime_nonneg t ht l _ hl
    · have hv : approx t (k + 1) i = (Finset.univ.erase i).inf' (erase_nonempty hi)
          (fun j => t i j + approx t k j) := by rw [approx_succ]; exact minStep_of_ne t _ hi
      rw [hv]
      constructor
      · obtain ⟨j0, hj0, heq⟩ := Finset.exists_mem_eq_inf' (erase_nonempty hi)
          (fun j => t i j + approx t k j)
        obtain ⟨⟨l0, hl0, hlen0, htm0⟩, _⟩ := ih j0
        have hne : i ≠ j0 := (Finset.mem_erase.mp hj0).1.symm
        refine ⟨j0 :: l0, ⟨hne, hl0⟩, by simp; omega, ?_⟩
        rw [routeTime_cons, htm0, heq]
      · intro l hl hlen
        match l, hl, hlen with
        | [], hl, _ => exact absurd hl hi
        | j :: l', hl, hlen =>
          obtain ⟨hij, hj⟩ := hl
          have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
          have h1 := Finset.inf'_le (fun j => t i j + approx t k j) hmem
          obtain ⟨_, hmin⟩ := ih j
          have h2 := hmin l' hj (by simp at hlen; omega)
          rw [routeTime_cons]
          linarith

theorem approx_succ_le' (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    ∀ k i, approx t (k + 1) i ≤ approx t k i := by
  intro k i
  obtain ⟨⟨l, hl, hlen, htm⟩, _⟩ := approx_within t ht k i
  obtain ⟨_, hmin⟩ := approx_within t ht (k + 1) i
  have := hmin l hl (by omega)
  rw [htm] at this
  exact this

theorem isMinTime_unique (t : Fin (n + 1) → Fin (n + 1) → ℝ) {i : Fin (n + 1)} {v w : ℝ}
    (hv : IsMinTime t i v) (hw : IsMinTime t i w) : v = w := by
  obtain ⟨⟨l, hl, hlt⟩, hvm⟩ := hv
  obtain ⟨⟨l', hl', hlt'⟩, hwm⟩ := hw
  have h1 := hvm l' hl'
  have h2 := hwm l hl
  linarith

theorem approx_isMinTime (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    ∀ k, n ≤ k → ∀ i, IsMinTime t i (approx t k i) := by
  intro k hk i
  obtain ⟨⟨l, hl, hlen, htm⟩, hmin⟩ := approx_within t ht k i
  refine ⟨⟨l, hl, htm⟩, ?_⟩
  intro l0 hl0
  obtain ⟨l', hl', nd, htl⟩ := exists_simple t ht l0 i hl0
  have := hmin l' hl' (by have := simple_length_le i l' nd; omega)
  linarith

theorem approx_eq_of_ge (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j)
    {k m : ℕ} (hk : n ≤ k) (hm : n ≤ m) : approx t k = approx t m := by
  funext i
  exact isMinTime_unique t (approx_isMinTime t ht k hk i) (approx_isMinTime t ht m hm i)

theorem approx_isSolution (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    IsRoutingSolution t (approx t n) := by
  intro i
  have h : approx t n = approx t (n + 1) := approx_eq_of_ge t ht le_rfl (Nat.le_succ n)
  have h2 : approx t (n + 1) i = minStep t (approx t n) i := rfl
  rw [← h2, ← h]

end RouteAux

namespace RouteAux

variable {n : ℕ}

theorem sol_last {t : Fin (n + 1) → Fin (n + 1) → ℝ} {F : Fin (n + 1) → ℝ}
    (hF : IsRoutingSolution t F) : F (Fin.last n) = 0 := by
  rw [hF (Fin.last n), minStep_last]

theorem sol_le_route (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j)
    {F : Fin (n + 1) → ℝ} (hF : IsRoutingSolution t F) :
    ∀ (l : List (Fin (n + 1))) (i : Fin (n + 1)), IsRoute i l → F i ≤ routeTime t i l := by
  intro l
  induction l with
  | nil =>
    intro i h
    have : i = Fin.last n := h
    subst this
    simp [sol_last hF, routeTime]
  | cons j l ih =>
    intro i h
    obtain ⟨hij, hj⟩ := h
    by_cases hi : i = Fin.last n
    · subst hi
      rw [sol_last hF]
      exact routeTime_nonneg t ht _ _ ⟨hij, hj⟩
    · have hmem : j ∈ Finset.univ.erase i :=
        Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
      have h1 := Finset.inf'_le (fun j => t i j + F j) hmem
      have h2 := ih j hj
      have h3 : F i = (Finset.univ.erase i).inf' (erase_nonempty hi) (fun j => t i j + F j) := by
        rw [hF i, minStep_of_ne t F hi]
      rw [routeTime_cons]
      linarith

theorem sol_le_unique (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j)
    {F G : Fin (n + 1) → ℝ} (hF : IsRoutingSolution t F) (hG : IsRoutingSolution t G)
    (hFG : ∀ i, F i ≤ G i) : F = G := by
  by_contra hne
  have hex : ∃ i, F i < G i := by
    by_contra hall
    push Not at hall
    exact hne (funext fun i => le_antisymm (hFG i) (hall i))
  obtain ⟨i0, hi0⟩ := hex
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (n + 1)))
    (fun i => G i - F i) ⟨i0, Finset.mem_univ _⟩
  set δ := G m - F m with hδ
  have hδpos : 0 < δ := by
    have := hm i0 (Finset.mem_univ _)
    linarith
  set M := Finset.univ.filter (fun i => G i - F i = δ) with hM
  have hMne : M.Nonempty := ⟨m, by simp [hM, hδ]⟩
  obtain ⟨x, hxM, hxmin⟩ := Finset.exists_min_image M F hMne
  have hxδ : G x - F x = δ := (Finset.mem_filter.mp hxM).2
  have hxD : x ≠ Fin.last n := by
    intro h
    subst h
    rw [sol_last hF, sol_last hG] at hxδ
    linarith
  have hFx : F x = (Finset.univ.erase x).inf' (erase_nonempty hxD) (fun j => t x j + F j) := by
    rw [hF x, minStep_of_ne t F hxD]
  have hGx : G x = (Finset.univ.erase x).inf' (erase_nonempty hxD) (fun j => t x j + G j) := by
    rw [hG x, minStep_of_ne t G hxD]
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' (erase_nonempty hxD) (fun j => t x j + F j)
  have hxj : x ≠ j := (Finset.mem_erase.mp hj).1.symm
  have hGle : G x ≤ t x j + G j := by
    rw [hGx]; exact Finset.inf'_le (fun j => t x j + G j) hj
  have hFj : F x = t x j + F j := by rw [hFx]; exact hjeq
  have hjM : j ∈ M := by
    have h1 : G j - F j ≤ δ := hm j (Finset.mem_univ _)
    have h2 : δ ≤ G j - F j := by linarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_antisymm h1 h2⟩
  have h3 := hxmin j hjM
  have := ht x j hxj
  linarith

theorem sol_eq_approx (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j)
    {F : Fin (n + 1) → ℝ} (hF : IsRoutingSolution t F) : F = approx t n := by
  have hS := approx_isSolution t ht
  have hle : ∀ i, F i ≤ approx t n i := by
    intro i
    obtain ⟨⟨l, hl, htm⟩, _⟩ := approx_isMinTime t ht n le_rfl i
    rw [← htm]
    exact sol_le_route t ht hF l i hl
  exact sol_le_unique t ht hF hS hle

theorem routing_unique (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j)
    {F G : Fin (n + 1) → ℝ} (hF : IsRoutingSolution t F) (hG : IsRoutingSolution t G) : F = G := by
  rw [sol_eq_approx t ht hF, sol_eq_approx t ht hG]

theorem minTime_isSolution (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j)
    (f : Fin (n + 1) → ℝ) (hf : ∀ i, IsMinTime t i (f i)) : IsRoutingSolution t f := by
  have : f = approx t n := funext fun i => isMinTime_unique t (hf i) (approx_isMinTime t ht n le_rfl i)
  rw [this]
  exact approx_isSolution t ht

/-! Section 7. -/

theorem minStep_mono (t : Fin (n + 1) → Fin (n + 1) → ℝ) {F G : Fin (n + 1) → ℝ}
    (h : ∀ i, F i ≤ G i) : ∀ i, minStep t F i ≤ minStep t G i := by
  intro i
  by_cases hi : i = Fin.last n
  · subst hi; simp [minStep_last]
  · rw [minStep_of_ne t F hi, minStep_of_ne t G hi]
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' (erase_nonempty hi) (fun j => t i j + G j)
    rw [hjeq]
    calc _ ≤ t i j + F j := Finset.inf'_le (fun j => t i j + F j) hj
      _ ≤ t i j + G j := by linarith [h j]

theorem approxUp_zero_last (t : Fin (n + 1) → Fin (n + 1) → ℝ) :
    approxUp t 0 (Fin.last n) = 0 := by simp [approxUp]

theorem approxUp_zero_ne (t : Fin (n + 1) → Fin (n + 1) → ℝ) {i : Fin (n + 1)}
    (h : i ≠ Fin.last n) : approxUp t 0 i = (Finset.univ.erase i).inf' (erase_nonempty h)
      (fun j => t i j) := by simp [approxUp, h]

theorem approxUp_succ (t : Fin (n + 1) → Fin (n + 1) → ℝ) (k : ℕ) :
    approxUp t (k + 1) = minStep t (approxUp t k) := rfl

theorem approxUp_zero_nonneg (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j)
    (i : Fin (n + 1)) : 0 ≤ approxUp t 0 i := by
  by_cases hi : i = Fin.last n
  · subst hi; simp [approxUp_zero_last]
  · rw [approxUp_zero_ne t hi]
    apply Finset.le_inf'
    intro j hj
    exact (ht i j (Finset.mem_erase.mp hj).1.symm).le

theorem approxUp_zero_le_step (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j)
    {F : Fin (n + 1) → ℝ} (hF : ∀ i, 0 ≤ F i) : ∀ i, approxUp t 0 i ≤ minStep t F i := by
  intro i
  by_cases hi : i = Fin.last n
  · subst hi; simp [approxUp_zero_last, minStep_last]
  · rw [approxUp_zero_ne t hi, minStep_of_ne t F hi]
    apply Finset.le_inf'
    intro j hj
    calc (Finset.univ.erase i).inf' (erase_nonempty hi) (fun j => t i j)
        ≤ t i j := Finset.inf'_le (fun j => t i j) hj
      _ ≤ t i j + F j := by linarith [hF j]

theorem approxUp_nonneg_step (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    ∀ k i, approxUp t k i ≤ approxUp t (k + 1) i := by
  intro k
  induction k with
  | zero =>
    intro i
    rw [approxUp_succ]
    exact approxUp_zero_le_step t ht (approxUp_zero_nonneg t ht) i
  | succ k ih =>
    intro i
    rw [approxUp_succ t (k + 1)]
    exact minStep_mono t ih i

theorem approxUp_le_sol (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j)
    {f : Fin (n + 1) → ℝ} (hf : IsRoutingSolution t f) : ∀ k i, approxUp t k i ≤ f i := by
  have hfnn : ∀ i, 0 ≤ f i := by
    intro i
    obtain ⟨⟨l, hl, htm⟩, _⟩ := approx_isMinTime t ht n le_rfl i
    rw [sol_eq_approx t ht hf, ← htm]
    exact routeTime_nonneg t ht l i hl
  intro k
  induction k with
  | zero =>
    intro i
    have := approxUp_zero_le_step t ht hfnn i
    rw [← hf i] at this
    exact this
  | succ k ih =>
    intro i
    rw [approxUp_succ]
    calc minStep t (approxUp t k) i ≤ minStep t f i := minStep_mono t ih i
      _ = f i := (hf i).symm

theorem exists_tau (hn : 1 ≤ n) (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ i j, i ≠ j → τ ≤ t i j := by
  let P : Finset (Fin (n + 1) × Fin (n + 1)) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  have hP : P.Nonempty := by
    refine ⟨(Fin.last n, ⟨0, by omega⟩), ?_⟩
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  refine ⟨P.inf' hP (fun p => t p.1 p.2), ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro p hp
    exact ht _ _ (Finset.mem_filter.mp hp).2
  · intro i j hij
    exact Finset.inf'_le (fun p : Fin (n + 1) × Fin (n + 1) => t p.1 p.2)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hij⟩)

theorem approxUp_lower (hn : 1 ≤ n) (t : Fin (n + 1) → Fin (n + 1) → ℝ)
    (ht : ∀ i j, i ≠ j → 0 < t i j) {f : Fin (n + 1) → ℝ} (hf : IsRoutingSolution t f)
    {τ : ℝ} (hτ : ∀ i j, i ≠ j → τ ≤ t i j) :
    ∀ (k : ℕ) (i : Fin (n + 1)), min (f i) (((k : ℝ) + 1) * τ) ≤ approxUp t k i := by
  have hfl := sol_last hf
  intro k
  induction k with
  | zero =>
    intro i
    by_cases hi : i = Fin.last n
    · subst hi; simp [approxUp_zero_last, hfl]
    · rw [approxUp_zero_ne t hi]
      refine le_trans (min_le_right _ _) ?_
      simp only [Nat.cast_zero, zero_add, one_mul]
      apply Finset.le_inf'
      intro j hj
      exact hτ i j (Finset.mem_erase.mp hj).1.symm
  | succ k ih =>
    intro i
    by_cases hi : i = Fin.last n
    · subst hi; simp [approxUp_succ, minStep_last, hfl]
    · rw [approxUp_succ, minStep_of_ne t _ hi]
      apply Finset.le_inf'
      intro j hj
      have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
      have hfi : f i ≤ t i j + f j := by
        rw [hf i, minStep_of_ne t f hi]
        exact Finset.inf'_le (fun j => t i j + f j) hj
      calc min (f i) (((↑(k + 1) : ℝ) + 1) * τ)
          ≤ min (t i j + f j) (t i j + ((k : ℝ) + 1) * τ) := by
            refine le_min (min_le_of_left_le hfi) (min_le_of_right_le ?_)
            have := hτ i j hij
            push_cast
            nlinarith
        _ = t i j + min (f j) (((k : ℝ) + 1) * τ) := min_add_add_left _ _ _
        _ ≤ t i j + approxUp t k j := by linarith [ih j]

theorem approxUp_eventually (hn : 1 ≤ n) (t : Fin (n + 1) → Fin (n + 1) → ℝ)
    (ht : ∀ i j, i ≠ j → 0 < t i j) {f : Fin (n + 1) → ℝ} (hf : IsRoutingSolution t f) :
    ∃ K : ℕ, ∀ k, K ≤ k → approxUp t k = f := by
  obtain ⟨τ, hτpos, hτ⟩ := exists_tau hn t ht
  have hK : ∀ i, ∃ K : ℕ, f i ≤ (K : ℝ) * τ := fun i => by
    obtain ⟨K, hK⟩ := exists_nat_gt (f i / τ)
    exact ⟨K, by rw [div_lt_iff₀ hτpos] at hK; linarith⟩
  choose Ki hKi using hK
  refine ⟨∑ i, Ki i, ?_⟩
  set K := ∑ i, Ki i with hKdef
  have hfK : ∀ i, f i ≤ ((K : ℝ) + 1) * τ := by
    intro i
    have h1 : Ki i ≤ K := Finset.single_le_sum (f := Ki) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : (Ki i : ℝ) ≤ K := by exact_mod_cast h1
    nlinarith [hKi i]
  have hlow : ∀ i, f i ≤ approxUp t K i := by
    intro i
    have := approxUp_lower hn t ht hf hτ K i
    rwa [min_eq_left (hfK i)] at this
  have hmono : Monotone (fun k => approxUp t k) := by
    apply monotone_nat_of_le_succ
    intro k i
    exact approxUp_nonneg_step t ht k i
  intro k hk
  funext i
  apply le_antisymm (approxUp_le_sol t ht hf k i)
  exact le_trans (hlow i) (hmono hk i)

end RouteAux

theorem solution {n : ℕ} (hn : 1 ≤ n)
    (t : Fin (n + 1) → Fin (n + 1) → ℝ) (ht : ∀ i j, i ≠ j → 0 < t i j) :
    (∀ i, ∃ v, IsMinTime t i v) ∧
      ∀ f : Fin (n + 1) → ℝ, (∀ i, IsMinTime t i (f i)) → IsRoutingSolution t f :=
  ⟨fun i => ⟨approx t n i, RouteAux.approx_isMinTime t ht n le_rfl i⟩,
    fun f hf => RouteAux.minTime_isSolution t ht f hf⟩
