-- Prove2me | solution 1 for ClarkeWright64.Savings.link_saving
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:24:23.253611+00:00
-- url     : https://prove2.me/submissions/a965c82c-39e3-453f-9fe6-f2fe27053932

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure



namespace ClarkeWright64.Savings

open Classical

variable {M n : ℕ}

lemma mem_customers {j : Fin (M + 1)} : j ∈ customers M ↔ j ≠ 0 := by
  simp [customers]

lemma customers_nodup : (customers M).Nodup := by
  unfold customers
  exact (List.nodup_finRange _).filter _

lemma isAllocation_init : IsAllocation (init M) := by
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [init, List.mem_map] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    have := mem_customers.1 hj
    simp [this, Ne.symm this]
  · have : ∀ l : List (Fin (M + 1)), (l.map (fun j => [j])).flatten = l := by
      intro l; induction l with
      | nil => rfl
      | cons a l ih => simp [ih]
    simp [init, this]

lemma nodup_flatten_disj {α : Type*} : ∀ (s : List (List α)), s.flatten.Nodup →
    ∀ {r1 r2 : List α} {y : α}, r1 ∈ s → r2 ∈ s → y ∈ r1 → y ∈ r2 → r1 = r2
  | [], _, _, _, _, h1, _, _, _ => by simp at h1
  | r :: s, h, r1, r2, y, h1, h2, hy1, hy2 => by
    simp only [List.flatten_cons, List.nodup_append] at h
    obtain ⟨_, h', hd⟩ := h
    rcases List.mem_cons.1 h1 with rfl | h1' <;> rcases List.mem_cons.1 h2 with rfl | h2'
    · rfl
    · exact (hd _ hy1 _ (List.mem_flatten.2 ⟨r2, h2', hy2⟩) rfl).elim
    · exact (hd _ hy2 _ (List.mem_flatten.2 ⟨r1, h1', hy1⟩) rfl).elim
    · exact nodup_flatten_disj s h' h1' h2' hy1 hy2

lemma nodup_of_flat {α : Type*} : ∀ (s : List (List α)), (∀ r ∈ s, r ≠ []) → s.flatten.Nodup → s.Nodup
  | [], _, _ => List.nodup_nil
  | r :: s, hne, h => by
    simp only [List.flatten_cons, List.nodup_append] at h
    obtain ⟨_, h', hd⟩ := h
    refine List.nodup_cons.2 ⟨?_, nodup_of_flat s (fun r hr => hne r (List.mem_cons_of_mem _ hr)) h'⟩
    intro hr
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil r (hne r (List.mem_cons_self))
    exact hd _ ha _ (List.mem_flatten.2 ⟨r, hr, ha⟩) rfl

lemma IsAllocation.nodup_flat {s : State M} (hs : IsAllocation s) : s.flatten.Nodup :=
  hs.2.nodup_iff.2 customers_nodup

lemma IsAllocation.nodup {s : State M} (hs : IsAllocation s) : s.Nodup :=
  nodup_of_flat s (fun r hr => (hs.1 r hr).1) hs.nodup_flat

lemma IsAllocation.exists_run {s : State M} (hs : IsAllocation s) {y : Fin (M + 1)} (hy : y ≠ 0) :
    ∃ R ∈ s, y ∈ R ∧ s.find? (fun r => decide (y ∈ r)) = some R := by
  have : y ∈ s.flatten := hs.2.mem_iff.2 (mem_customers.2 hy)
  obtain ⟨R0, hR0, hyR0⟩ := List.mem_flatten.1 this
  cases h : s.find? (fun r => decide (y ∈ r)) with
  | none =>
    have := List.find?_eq_none.1 h R0 hR0
    simp [hyR0] at this
  | some R =>
    have h1 := List.find?_some h
    have h2 := List.mem_of_find?_eq_some h
    simp at h1
    exact ⟨R, h2, h1, rfl⟩

lemma countP_unique {α : Type*} (p : α → Bool) : ∀ (s : List α), s.Nodup → ∀ {R : α}, R ∈ s →
    (∀ r ∈ s, p r = true → r = R) → s.countP p = if p R then 1 else 0
  | [], _, R, hR, _ => by simp at hR
  | a :: s, hnd, R, hR, h => by
    rw [List.nodup_cons] at hnd
    by_cases haR : a = R
    · subst haR
      have : s.countP p = 0 := by
        rw [List.countP_eq_zero]
        intro r hr hpr
        exact hnd.1 (h r (List.mem_cons_of_mem _ hr) hpr ▸ hr)
      simp [List.countP_cons, this]
    · have hpa : p a = false := by
        by_contra hc
        exact haR (h a List.mem_cons_self (by simpa using hc))
      have hRs : R ∈ s := by
        rcases List.mem_cons.1 hR with h' | h'
        · exact absurd h'.symm haR
        · exact h'
      rw [List.countP_cons, countP_unique p s hnd.2 hRs (fun r hr => h r (List.mem_cons_of_mem _ hr))]
      simp [hpa]

lemma t_endpoint {s : State M} (hs : IsAllocation s) {R : List (Fin (M + 1))} (hR : R ∈ s)
    {y : Fin (M + 1)} (hy : y ∈ R) (hy0 : y ≠ 0) :
    t s y 0 = (if R.head? = some y then 1 else 0) + (if R.getLast? = some y then 1 else 0) := by
  have h1 : s.countP (fun r => decide (r.head? = some y)) =
      if R.head? = some y then 1 else 0 := by
    rw [countP_unique _ s hs.nodup hR]
    · simp
    · intro r hr hp
      have : y ∈ r := by
        have := of_decide_eq_true hp
        exact List.mem_of_mem_head? this
      exact nodup_flatten_disj s hs.nodup_flat hr hR this hy
  have h2 : s.countP (fun r => decide (r.getLast? = some y)) =
      if R.getLast? = some y then 1 else 0 := by
    rw [countP_unique _ s hs.nodup hR]
    · simp
    · intro r hr hp
      have : y ∈ r := by
        have := of_decide_eq_true hp
        exact List.mem_of_getLast? this
      exact nodup_flatten_disj s hs.nodup_flat hr hR this hy
  simp only [t, hy0, if_false, if_true]
  simp [h1, h2]

lemma endpoint_of_pos {s : State M} (hs : IsAllocation s) {R : List (Fin (M + 1))} (hR : R ∈ s)
    {y : Fin (M + 1)} (hy : y ∈ R) (hy0 : y ≠ 0) (hpos : 0 < t s y 0) :
    R.head? = some y ∨ R.getLast? = some y := by
  rw [t_endpoint hs hR hy hy0] at hpos
  by_contra hc
  push_neg at hc
  rw [if_neg hc.1, if_neg hc.2] at hpos
  simp at hpos

lemma link_struct (I : Instance M n) {s : State M} (hs : IsAllocation s) {y z : Fin (M + 1)}
    (hadm : Admissible I s y z) :
    ∃ (R R' : List (Fin (M + 1))) (rest : State M),
      R ∈ s ∧ R' ∈ s ∧ y ∈ R ∧ z ∈ R' ∧ y ∉ R' ∧ z ∉ R ∧ s.Perm (R :: R' :: rest) ∧
      rest = s.filter (fun r => decide (y ∉ r ∧ z ∉ r)) ∧
      (∀ r ∈ rest, y ∉ r ∧ z ∉ r) ∧
      link s y z = rest ++ [orientEnd R y ++ orientStart R' z] ∧
      Q I s y = I.runLoad R ∧ Q I s z = I.runLoad R' ∧
      (R.head? = some y ∨ R.getLast? = some y) ∧ (R'.head? = some z ∨ R'.getLast? = some z) := by
  obtain ⟨hy0, hz0, hyz, hty, htz, hnot, _⟩ := hadm
  obtain ⟨R, hR, hyR, hRf⟩ := hs.exists_run hy0
  obtain ⟨R', hR', hzR', hR'f⟩ := hs.exists_run hz0
  have hzR : z ∉ R := fun h => hnot ⟨R, hR, hyR, h⟩
  have hyR' : y ∉ R' := fun h => hnot ⟨R', hR', h, hzR'⟩
  have hne : R ≠ R' := fun h => hzR (h ▸ hzR')
  refine ⟨R, R', s.filter (fun r => decide (y ∉ r ∧ z ∉ r)), hR, hR', hyR, hzR', hyR', hzR, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := List.filter_append_perm (fun r => decide (y ∉ r ∧ z ∉ r)) s
    have h2 : (s.filter (fun r => !decide (y ∉ r ∧ z ∉ r))).Perm [R, R'] := by
      rw [List.perm_ext_iff_of_nodup ((hs.nodup).filter _) (by simp [hne])]
      intro a
      rw [List.mem_filter]
      constructor
      · rintro ⟨ha, hh⟩
        have hh : y ∈ a ∨ z ∈ a := by simpa using hh
        by_cases hy : y ∈ a
        · exact List.mem_cons.2 (Or.inl (nodup_flatten_disj s hs.nodup_flat ha hR hy hyR))
        · have hz : z ∈ a := hh.resolve_left hy
          exact List.mem_cons.2 (Or.inr (List.mem_singleton.2
            (nodup_flatten_disj s hs.nodup_flat ha hR' hz hzR')))
      · intro ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact ⟨hR, by simpa using Or.inl hyR⟩
        · rw [List.mem_singleton] at ha
          subst ha
          exact ⟨hR', by simpa using Or.inr hzR'⟩
    have h3 := (h1.symm.trans ((List.Perm.refl _).append h2.symm.symm))
    exact (h3.trans (List.perm_append_comm))
  · intro r hr
    have := (List.mem_filter.1 hr).2
    simpa using this
  · simp [link, hRf, hR'f]
  · simp [Q, hRf]
  · simp [Q, hR'f]
  · exact endpoint_of_pos hs hR hyR hy0 hty
  · exact endpoint_of_pos hs hR' hzR' hz0 htz

/-! ### orientation -/

lemma orientEnd_perm (R : List (Fin (M + 1))) (y : Fin (M + 1)) : (orientEnd R y).Perm R := by
  unfold orientEnd; split_ifs
  · exact List.Perm.refl _
  · exact List.reverse_perm R

lemma orientStart_perm (R : List (Fin (M + 1))) (y : Fin (M + 1)) : (orientStart R y).Perm R := by
  unfold orientStart; split_ifs
  · exact List.Perm.refl _
  · exact List.reverse_perm R

lemma orientEnd_last {R : List (Fin (M + 1))} {y : Fin (M + 1)}
    (h : R.head? = some y ∨ R.getLast? = some y) : (orientEnd R y).getLast? = some y := by
  unfold orientEnd; split_ifs with h1
  · exact h1
  · rw [List.getLast?_reverse]; tauto

lemma orientStart_head {R : List (Fin (M + 1))} {y : Fin (M + 1)}
    (h : R.head? = some y ∨ R.getLast? = some y) : (orientStart R y).head? = some y := by
  unfold orientStart; split_ifs with h1
  · exact h1
  · rw [List.head?_reverse]; tauto

lemma orientEnd_ne_nil {R : List (Fin (M + 1))} (h : R ≠ []) (y : Fin (M + 1)) :
    orientEnd R y ≠ [] := by
  intro h'
  have := (orientEnd_perm R y).symm
  rw [h'] at this
  exact h (List.perm_nil.1 this)

lemma orientStart_ne_nil {R : List (Fin (M + 1))} (h : R ≠ []) (y : Fin (M + 1)) :
    orientStart R y ≠ [] := by
  intro h'
  have := (orientStart_perm R y).symm
  rw [h'] at this
  exact h (List.perm_nil.1 this)

lemma t_perm {s s' : State M} (h : s.Perm s') (y z : Fin (M + 1)) : t s y z = t s' y z := by
  unfold t
  simp only [List.Perm.countP_eq _ h, h.mem_iff]

lemma isAllocation_link (I : Instance M n) {s : State M} (hs : IsAllocation s) {y z : Fin (M + 1)}
    (hadm : Admissible I s y z) : IsAllocation (link s y z) := by
  obtain ⟨R, R', rest, hR, hR', hyR, hzR', hyR', hzR, hperm, hrest, hrest2, hlink, -, -, -, -⟩ :=
    link_struct I hs hadm
  rw [hlink]
  have hNperm : (orientEnd R y ++ orientStart R' z).Perm (R ++ R') :=
    (orientEnd_perm R y).append (orientStart_perm R' z)
  refine ⟨?_, ?_⟩
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · have : r ∈ s := by rw [hrest] at hr; exact (List.mem_filter.1 hr).1
      exact hs.1 r this
    · rw [List.mem_singleton] at hr
      subst hr
      refine ⟨?_, ?_⟩
      · intro hc
        exact orientEnd_ne_nil (hs.1 R hR).1 y (List.append_eq_nil_iff.1 hc).1
      · intro h0
        rcases List.mem_append.1 h0 with h0 | h0
        · exact (hs.1 R hR).2 ((orientEnd_perm R y).mem_iff.1 h0)
        · exact (hs.1 R' hR').2 ((orientStart_perm R' z).mem_iff.1 h0)
  · have h1 := (hperm.flatten).symm.trans hs.2
    simp only [List.flatten_cons] at h1
    refine List.Perm.trans ?_ h1
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
    have e1 : List.Perm (rest.flatten ++ (orientEnd R y ++ orientStart R' z)) (rest.flatten ++ (R ++ R')) :=
      List.Perm.append_left _ hNperm
    have e2 : List.Perm (rest.flatten ++ (R ++ R')) ((R ++ R') ++ rest.flatten) := List.perm_append_comm
    rw [List.append_assoc] at e2
    exact e1.trans e2

lemma reachable_alloc (I : Instance M n) {s : State M} (hs : Reachable I s) : IsAllocation s := by
  induction hs with
  | refl => exact isAllocation_init
  | tail _ hstep ih =>
    obtain ⟨y, z, hadm, -, rfl⟩ := hstep
    exact isAllocation_link I ih hadm

/-! ### route costs -/

/-- open path length of a list -/
def wl (c : Fin (M + 1) → Fin (M + 1) → ℝ) : List (Fin (M + 1)) → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: l => c a b + wl c (b :: l)

lemma wl_snoc (c : Fin (M + 1) → Fin (M + 1) → ℝ) (x : Fin (M + 1)) :
    ∀ (X : List (Fin (M + 1))) (a : Fin (M + 1)),
      wl c (a :: (X ++ [x])) = wl c (a :: X) + c (X.getLastD a) x
  | [], a => by simp [wl]
  | b :: X', a => by
    have := wl_snoc c x X' b
    simp only [List.cons_append, wl, List.getLastD_cons] at this ⊢
    rw [this]; ring

lemma wl_append (c : Fin (M + 1) → Fin (M + 1) → ℝ) (y : Fin (M + 1)) (Y : List (Fin (M + 1))) :
    ∀ (X : List (Fin (M + 1))) (x : Fin (M + 1)),
      wl c (x :: X ++ y :: Y) = wl c (x :: X) + c (X.getLastD x) y + wl c (y :: Y)
  | [], x => by simp [wl]
  | b :: X', x => by
    have := wl_append c y Y X' b
    simp only [List.cons_append, wl, List.getLastD_cons] at this ⊢
    rw [this]; ring

lemma wl_reverse (c : Fin (M + 1) → Fin (M + 1) → ℝ) (hc : ∀ i j, c i j = c j i) :
    ∀ (L : List (Fin (M + 1))), wl c L.reverse = wl c L
  | [] => rfl
  | [a] => rfl
  | a :: b :: l => by
    have ih := wl_reverse c hc (b :: l)
    rw [List.reverse_cons]
    obtain ⟨e, Xs, hX⟩ : ∃ e Xs, (b :: l).reverse = e :: Xs := by
      cases h : (b :: l).reverse with
      | nil => simp at h
      | cons e Xs => exact ⟨e, Xs, rfl⟩
    rw [hX] at ih ⊢
    have h1 := wl_snoc c a Xs e
    show wl c (e :: (Xs ++ [a])) = _
    rw [h1, ih]
    have h2 : Xs.getLastD e = b := by
      have : (e :: Xs).getLast? = some b := by
        rw [← hX, List.getLast?_reverse]; rfl
      rw [List.getLast?_cons] at this
      rw [List.getLastD_eq_getLast?]; exact Option.some.inj this
    rw [h2, wl, hc a b]; ring

lemma zw_sum (c : Fin (M + 1) → Fin (M + 1) → ℝ) :
    ∀ (l : List (Fin (M + 1))) (a : Fin (M + 1)),
      (List.zipWith c (a :: l) (l ++ [0])).sum = wl c (a :: l) + c (l.getLastD a) 0
  | [], a => by simp [wl]
  | b :: l', a => by
    have := zw_sum c l' b
    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons, wl, List.getLastD_cons] at this ⊢
    rw [this]; ring

lemma routeCost_eq (c : Fin (M + 1) → Fin (M + 1) → ℝ) {L : List (Fin (M + 1))} (hL : L ≠ []) :
    SupplyChainTheory.routeCost c L = c 0 (L.headD 0) + wl c L + c (L.getLastD 0) 0 := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hL
  unfold SupplyChainTheory.routeCost SupplyChainTheory.closedLength
  have hrot : (0 :: a :: l : List (Fin (M + 1))).rotate 1 = (a :: l) ++ [0] := by
    simpa using List.rotate_cons_succ (l := a :: l) (a := (0 : Fin (M + 1))) (n := 0)
  rw [hrot]
  have := zw_sum c (a :: l) 0
  simp only [List.cons_append] at this ⊢
  rw [this]
  simp [wl]

lemma routeCost_reverse (c : Fin (M + 1) → Fin (M + 1) → ℝ) (hc : ∀ i j, c i j = c j i)
    (L : List (Fin (M + 1))) :
    SupplyChainTheory.routeCost c L.reverse = SupplyChainTheory.routeCost c L := by
  by_cases hL : L = []
  · subst hL; rfl
  have hL' : L.reverse ≠ [] := by simpa using hL
  rw [routeCost_eq c hL, routeCost_eq c hL', wl_reverse c hc]
  have h1 : L.reverse.headD 0 = L.getLastD 0 := by
    simp [List.headD_eq_head?_getD, List.getLastD_eq_getLast?, List.head?_reverse]
  have h2 : L.reverse.getLastD 0 = L.headD 0 := by
    simp [List.headD_eq_head?_getD, List.getLastD_eq_getLast?, List.getLast?_reverse]
  rw [h1, h2, hc 0 (L.getLastD 0), hc (L.headD 0) 0]
  ring

lemma routeCost_orientEnd (c : Fin (M + 1) → Fin (M + 1) → ℝ) (hc : ∀ i j, c i j = c j i)
    (R : List (Fin (M + 1))) (y : Fin (M + 1)) :
    SupplyChainTheory.routeCost c (orientEnd R y) = SupplyChainTheory.routeCost c R := by
  unfold orientEnd; split_ifs
  · rfl
  · exact routeCost_reverse c hc R

lemma routeCost_orientStart (c : Fin (M + 1) → Fin (M + 1) → ℝ) (hc : ∀ i j, c i j = c j i)
    (R : List (Fin (M + 1))) (y : Fin (M + 1)) :
    SupplyChainTheory.routeCost c (orientStart R y) = SupplyChainTheory.routeCost c R := by
  unfold orientStart; split_ifs
  · rfl
  · exact routeCost_reverse c hc R

lemma routeCost_join (c : Fin (M + 1) → Fin (M + 1) → ℝ) {X Y : List (Fin (M + 1))}
    (hX : X ≠ []) (hY : Y ≠ []) {y z : Fin (M + 1)} (hy : X.getLast? = some y)
    (hz : Y.head? = some z) :
    SupplyChainTheory.routeCost c (X ++ Y) = SupplyChainTheory.routeCost c X +
      SupplyChainTheory.routeCost c Y - c y 0 - c 0 z + c y z := by
  obtain ⟨a, X0, rfl⟩ := List.exists_cons_of_ne_nil hX
  obtain ⟨b, Y0, rfl⟩ := List.exists_cons_of_ne_nil hY
  have hz' : b = z := by simpa using hz
  subst hz'
  have hy' : X0.getLastD a = y := by
    rw [List.getLastD_eq_getLast?]
    rw [List.getLast?_cons] at hy
    exact Option.some.inj hy
  have hXY : (a :: X0 ++ b :: Y0) ≠ [] := by simp
  rw [routeCost_eq c hXY, routeCost_eq c hX, routeCost_eq c hY, wl_append c b Y0 X0 a, hy']
  have e1 : (a :: X0 ++ b :: Y0).headD 0 = a := by simp
  have e2 : (a :: X0 ++ b :: Y0).getLastD 0 = (b :: Y0).getLastD 0 := by
    show ((a :: X0) ++ (b :: Y0)).getLastD 0 = _
    rw [List.getLastD_eq_getLast?, List.getLast?_append, List.getLastD_eq_getLast?]
    simp [List.getLast?_cons]
  have e3 : (a :: X0).getLastD 0 = y := by
    rw [List.getLastD_cons]; exact hy'
  rw [e1, e2, e3]
  simp
  ring

theorem link_saving_core (I : Instance M n) (hsymm : ∀ i j, I.d i j = I.d j i)
    (s : State M) (hs : Reachable I s) (y z : Fin (M + 1)) (hyz : Admissible I s y z) :
    I.mileage (link s y z) = I.mileage s - I.saving y z := by
  have hs' := reachable_alloc I hs
  obtain ⟨R, R', rest, hR, hR', hyR, hzR', hyR', hzR, hperm, hrest, hrest2, hlink, -, -, hRe, hR'e⟩ :=
    link_struct I hs' hyz
  have hRne := (hs'.1 R hR).1
  have hR'ne := (hs'.1 R' hR').1
  have hm1 : I.mileage s = SupplyChainTheory.routeCost I.d R + SupplyChainTheory.routeCost I.d R' +
      (rest.map (SupplyChainTheory.routeCost I.d)).sum := by
    unfold Instance.mileage
    rw [(hperm.map _).sum_eq]
    simp only [List.map_cons, List.sum_cons]
    ring
  have hm2 : I.mileage (link s y z) = (rest.map (SupplyChainTheory.routeCost I.d)).sum +
      SupplyChainTheory.routeCost I.d (orientEnd R y ++ orientStart R' z) := by
    unfold Instance.mileage
    rw [hlink]
    simp
  rw [hm1] at *
  rw [hm2, routeCost_join I.d (orientEnd_ne_nil hRne y) (orientStart_ne_nil hR'ne z)
    (orientEnd_last hRe) (orientStart_head hR'e), routeCost_orientEnd _ hsymm,
    routeCost_orientStart _ hsymm, Instance.saving, hsymm y 0]
  ring

end ClarkeWright64.Savings

open ClarkeWright64.Savings


theorem solution {M n : ℕ} (I : Instance M n) (hsymm : ∀ i j, I.d i j = I.d j i)
    (s : State M) (hs : Reachable I s) (y z : Fin (M + 1)) (hyz : Admissible I s y z) :
    I.mileage (link s y z) = I.mileage s - I.saving y z := by
  exact link_saving_core I hsymm s hs y z hyz
