-- Prove2me | solution 1 for ClarkeWright64.Savings.tsp_case
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:45:35.214576+00:00
-- url     : https://prove2.me/submissions/a648f1ab-6bc5-48e4-bfc6-0ddddb4cc570

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

theorem infix_pair_append {α : Type*} (u v : α) : ∀ (A B : List α),
    [u, v] <:+: A ++ B ↔ [u, v] <:+: A ∨ [u, v] <:+: B ∨ (A.getLast? = some u ∧ B.head? = some v)
  | [], B => by simp
  | [a], B => by
    cases B with
    | nil => simp [List.infix_cons_iff]
    | cons b B' =>
      simp [List.infix_cons_iff, List.cons_prefix_cons]
      have : (a = u ∧ b = v) ↔ (u = a ∧ v = b) := by
        constructor <;> (rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩)
      rw [this]; tauto
  | a :: a' :: A, B => by
    have ih := infix_pair_append u v (a' :: A) B
    simp only [List.cons_append, List.infix_cons_iff] at ih ⊢
    rw [ih]
    simp [List.cons_prefix_cons, List.getLast?_cons]
    tauto

/-! ### adjacency -/

def adj (s : State M) (u v : Fin (M + 1)) : Prop := ∃ r ∈ s, [u, v] <:+: r ∨ [v, u] <:+: r

lemma t_adj {s : State M} {u v : Fin (M + 1)} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    t s u v = if adj s u v then 1 else 0 := by
  unfold t adj
  rw [if_neg huv, if_neg hv, if_neg hu]
  by_cases h : ∃ r ∈ s, [u, v] <:+: r ∨ [v, u] <:+: r <;> simp [h]

lemma pair_rev {α : Type*} (u v : α) (R : List α) : [u, v] <:+: R.reverse ↔ [v, u] <:+: R := by
  have : [u, v] = [v, u].reverse := rfl
  rw [this, List.reverse_infix]

lemma pair_orientEnd (R : List (Fin (M + 1))) (a u v : Fin (M + 1)) :
    ([u, v] <:+: orientEnd R a ∨ [v, u] <:+: orientEnd R a) ↔ ([u, v] <:+: R ∨ [v, u] <:+: R) := by
  unfold orientEnd; split_ifs
  · exact Iff.rfl
  · rw [pair_rev, pair_rev]; tauto

lemma pair_orientStart (R : List (Fin (M + 1))) (a u v : Fin (M + 1)) :
    ([u, v] <:+: orientStart R a ∨ [v, u] <:+: orientStart R a) ↔ ([u, v] <:+: R ∨ [v, u] <:+: R) := by
  unfold orientStart; split_ifs
  · exact Iff.rfl
  · rw [pair_rev, pair_rev]; tauto

lemma prop_aux (p1 p2 q1 q2 r1 r2 s1 s2 e1 e2 e3 e4 : Prop)
    (hX : (p1 ∨ p2) ↔ (r1 ∨ r2)) (hY : (q1 ∨ q2) ↔ (s1 ∨ s2)) :
    ((p1 ∨ q1 ∨ (e1 ∧ e2)) ∨ (p2 ∨ q2 ∨ (e4 ∧ e3))) ↔
      ((r1 ∨ r2) ∨ (s1 ∨ s2) ∨ (e1 ∧ e2) ∨ (e3 ∧ e4)) := by
  tauto

lemma prop_aux2 (x p q r s : Prop) : (x ∨ (p ∨ q ∨ r ∨ s)) ↔ ((x ∨ p ∨ q) ∨ r ∨ s) := by
  tauto

lemma adj_link (I : Instance M n) {s : State M} (hs : IsAllocation s) {a b : Fin (M + 1)}
    (hadm : Admissible I s a b) (u v : Fin (M + 1)) :
    adj (link s a b) u v ↔ adj s u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  obtain ⟨R, R', rest, hR, hR', hyR, hzR', hyR', hzR, hperm, hrest, hrest2, hlink, -, -, hRe, hR'e⟩ :=
    link_struct I hs hadm
  have hX := orientEnd_last hRe
  have hY := orientStart_head hR'e
  have e1 : (u = a) ↔ ((orientEnd R a).getLast? = some u) := by
    rw [hX]; simp [eq_comm]
  have e2 : (v = b) ↔ ((orientStart R' b).head? = some v) := by
    rw [hY]; simp [eq_comm]
  have e3 : (u = b) ↔ ((orientStart R' b).head? = some u) := by
    rw [hY]; simp [eq_comm]
  have e4 : (v = a) ↔ ((orientEnd R a).getLast? = some v) := by
    rw [hX]; simp [eq_comm]
  have hP : ∀ r : List (Fin (M + 1)), ([u, v] <:+: r ∨ [v, u] <:+: r) → True := fun _ _ => trivial
  have hN : ([u, v] <:+: orientEnd R a ++ orientStart R' b ∨ [v, u] <:+: orientEnd R a ++ orientStart R' b) ↔
      (([u, v] <:+: R ∨ [v, u] <:+: R) ∨ ([u, v] <:+: R' ∨ [v, u] <:+: R') ∨
        (u = a ∧ v = b) ∨ (u = b ∧ v = a)) := by
    have hX' := pair_orientEnd R a u v
    have hY' := pair_orientStart R' b u v
    rw [infix_pair_append u v, infix_pair_append v u, ← e1, ← e2, ← e3, ← e4]
    exact prop_aux _ _ _ _ _ _ _ _ _ _ _ _ hX' hY'
  have hs1 : adj s u v ↔ adj rest u v ∨ ([u, v] <:+: R ∨ [v, u] <:+: R) ∨ ([u, v] <:+: R' ∨ [v, u] <:+: R') := by
    unfold adj
    constructor
    · rintro ⟨r, hr, h⟩
      rcases List.mem_cons.1 (hperm.subset hr) with rfl | hr
      · exact Or.inr (Or.inl h)
      · rcases List.mem_cons.1 hr with rfl | hr
        · exact Or.inr (Or.inr h)
        · exact Or.inl ⟨r, hr, h⟩
    · rintro (⟨r, hr, h⟩ | h | h)
      · exact ⟨r, hperm.symm.subset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)), h⟩
      · exact ⟨R, hR, h⟩
      · exact ⟨R', hR', h⟩
  have hs2 : adj (link s a b) u v ↔ adj rest u v ∨
      ([u, v] <:+: orientEnd R a ++ orientStart R' b ∨ [v, u] <:+: orientEnd R a ++ orientStart R' b) := by
    rw [hlink]
    unfold adj
    constructor
    · rintro ⟨r, hr, h⟩
      rcases List.mem_append.1 hr with hr | hr
      · exact Or.inl ⟨r, hr, h⟩
      · rw [List.mem_singleton] at hr
        subst hr; exact Or.inr h
    · rintro (⟨r, hr, h⟩ | h)
      · exact ⟨r, List.mem_append_left _ hr, h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), h⟩
  rw [hs2, hs1, hN]
  exact prop_aux2 _ _ _ _ _

lemma orientEnd_head {R : List (Fin (M + 1))} (a : Fin (M + 1)) :
    (orientEnd R a).head? = R.head? ∨ (orientEnd R a).head? = R.getLast? := by
  unfold orientEnd; split_ifs
  · exact Or.inl rfl
  · rw [List.head?_reverse]; exact Or.inr rfl

lemma orientStart_last {R : List (Fin (M + 1))} (a : Fin (M + 1)) :
    (orientStart R a).getLast? = R.head? ∨ (orientStart R a).getLast? = R.getLast? := by
  unfold orientStart; split_ifs
  · exact Or.inr rfl
  · rw [List.getLast?_reverse]; exact Or.inl rfl

lemma t_link_le (I : Instance M n) {s : State M} (hs : IsAllocation s) {a b : Fin (M + 1)}
    (hadm : Admissible I s a b) {y : Fin (M + 1)} (hy0 : y ≠ 0) :
    t (link s a b) y 0 ≤ t s y 0 := by
  obtain ⟨R, R', rest, hR, hR', hyR, hzR', hyR', hzR, hperm, hrest, hrest2, hlink, -, -, hRe, hR'e⟩ :=
    link_struct I hs hadm
  have hRne := (hs.1 R hR).1
  have hR'ne := (hs.1 R' hR').1
  rw [t_perm hperm y 0, hlink]
  have hXne := orientEnd_ne_nil hRne a
  have hYne := orientStart_ne_nil hR'ne b
  have h1 : (orientEnd R a ++ orientStart R' b).head? = (orientEnd R a).head? := by
    obtain ⟨x, X0, hx⟩ := List.exists_cons_of_ne_nil hXne
    rw [hx]; rfl
  have h2 : (orientEnd R a ++ orientStart R' b).getLast? = (orientStart R' b).getLast? := by
    obtain ⟨x, X0, hx⟩ := List.exists_cons_of_ne_nil hYne
    rw [List.getLast?_append, hx]
    simp [List.getLast?_cons]
  have h3 := orientEnd_head (R := R) a
  have h4 := orientStart_last (R := R') b
  simp only [t, if_neg hy0, if_true, List.countP_append, List.countP_cons, List.countP_nil,
    decide_eq_true_eq, h1, h2]
  by_cases c1 : (orientEnd R a).head? = some y
  · by_cases c2 : (orientStart R' b).getLast? = some y
    · simp only [c1, c2, if_true]
      rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;> rw [h3] at c1 <;> rw [h4] at c2 <;> simp [c1, c2] <;> omega
    · simp only [c1, c2, if_true, if_false]
      rcases h3 with h3 | h3 <;> rw [h3] at c1 <;> simp [c1] <;> omega
  · by_cases c2 : (orientStart R' b).getLast? = some y
    · simp only [c1, c2, if_true, if_false]
      rcases h4 with h4 | h4 <;> rw [h4] at c2 <;> simp [c2] <;> omega
    · simp only [c1, c2, if_false]
      omega

lemma reachable_step (I : Instance M n) {s s' : State M} (hs : Reachable I s) (h : Step I s s') :
    Reachable I s' := Relation.ReflTransGen.tail hs h

lemma t_mono_reach (I : Instance M n) {s s'' : State M} (hs : Reachable I s)
    (h : Relation.ReflTransGen (Step I) s s'') {y : Fin (M + 1)} (hy : y ≠ 0) :
    t s'' y 0 ≤ t s y 0 := by
  induction h with
  | refl => exact le_rfl
  | tail hss' hstep ih =>
    rename_i s1 s2
    have hr : Reachable I s1 := Relation.ReflTransGen.trans hs hss'
    obtain ⟨a, b, hadm, -, rfl⟩ := hstep
    exact (t_link_le I (reachable_alloc I hr) hadm hy).trans ih

theorem interior_core {M n : ℕ} (I : Instance M n) (s s' : State M)
    (hs : Reachable I s) (hstep : Step I s s') :
    (∀ y z : Fin (M + 1), y ≠ 0 → z ≠ 0 → t s y z = 1 → t s' y z = 1) ∧
    (∀ y : Fin (M + 1), y ≠ 0 → t s' y 0 ≤ t s y 0) ∧
    (∀ y : Fin (M + 1), y ≠ 0 → t s y 0 = 0 →
      ∀ s'' : State M, Relation.ReflTransGen (Step I) s s'' →
        ∀ z : Fin (M + 1), ¬ Admissible I s'' y z ∧ ¬ Admissible I s'' z y) := by
  have hal := reachable_alloc I hs
  obtain ⟨a, b, hadm, -, rfl⟩ := hstep
  refine ⟨?_, ?_, ?_⟩
  · intro y z hy hz h
    have hyz : y ≠ z := by
      rintro rfl
      simp [t] at h
    rw [t_adj hy hz hyz] at h
    have hadj : adj s y z := by
      by_contra hc
      rw [if_neg hc] at h
      exact absurd h (by norm_num)
    rw [t_adj hy hz hyz, if_pos ((adj_link I hal hadm y z).2 (Or.inl hadj))]
  · intro y hy
    exact t_link_le I hal hadm hy
  · intro y hy ht s'' hss z
    have h1 : t s'' y 0 ≤ t s y 0 := t_mono_reach I hs hss hy
    have h2 : ¬ 0 < t s'' y 0 := by omega
    exact ⟨fun h => h2 h.2.2.2.1, fun h => h2 h.2.2.2.2.1⟩

lemma adj_iff_run {s : State M} (hs : IsAllocation s) {R : List (Fin (M + 1))} (hR : R ∈ s)
    {y z : Fin (M + 1)} (hy : y ∈ R) : adj s y z ↔ ([y, z] <:+: R ∨ [z, y] <:+: R) := by
  constructor
  · rintro ⟨r, hr, h⟩
    have : y ∈ r := by
      rcases h with h | h
      · exact h.subset (by simp)
      · exact h.subset (by simp)
    rwa [nodup_flatten_disj s hs.nodup_flat hr hR this hy] at h
  · intro h; exact ⟨R, hR, h⟩

lemma pair_char {α : Type*} (A B : List α) (y z : α) (hA : y ∉ A) (hB : y ∉ B) :
    [y, z] <:+: A ++ y :: B ↔ B.head? = some z := by
  rw [infix_pair_append]
  have h1 : ¬ [y, z] <:+: A := fun h => hA (h.subset (by simp))
  have h2 : ¬ A.getLast? = some y := fun h => hA (List.mem_of_getLast? h)
  have h3 : [y, z] <:+: y :: B ↔ B.head? = some z := by
    rw [List.infix_cons_iff]
    have : ¬ [y, z] <:+: B := fun h => hB (h.subset (by simp))
    simp only [this, or_false]
    cases B with
    | nil => simp
    | cons b B' => simp [List.cons_prefix_cons, eq_comm]
  simp [h1, h2, h3]

lemma pair_char' {α : Type*} (A B : List α) (y z : α) (hA : y ∉ A) (hB : y ∉ B) :
    [z, y] <:+: A ++ y :: B ↔ A.getLast? = some z := by
  rw [infix_pair_append]
  have h1 : ¬ [z, y] <:+: A := fun h => hA (h.subset (by simp))
  have h3 : ¬ [z, y] <:+: y :: B := by
    rw [List.infix_cons_iff]
    have : ¬ [z, y] <:+: B := fun h => hB (h.subset (by simp))
    simp only [this, or_false]
    intro h
    rcases h with ⟨t, ht⟩
    simp at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact hB (by simp)
  simp [h1, h3]

lemma sum_t_eq_two {s : State M} (hs : IsAllocation s) {y : Fin (M + 1)} (hy0 : y ≠ 0) :
    ∑ z ∈ Finset.univ.erase y, t s y z = 2 := by
  obtain ⟨R, hR, hyR, -⟩ := hs.exists_run hy0
  obtain ⟨A, B, hRAB⟩ := List.append_of_mem hyR
  have hnd : R.Nodup := (List.nodup_flatten.1 hs.nodup_flat).1 R hR
  have h0 : (0 : Fin (M + 1)) ∉ R := (hs.1 R hR).2
  rw [hRAB] at hnd h0
  rw [List.nodup_append] at hnd
  obtain ⟨-, hnd2, hdisj⟩ := hnd
  rw [List.nodup_cons] at hnd2
  have hyA : y ∉ A := fun h => hdisj _ h _ (List.mem_cons_self) rfl
  have hyB : y ∉ B := hnd2.1
  have h0A : (0 : Fin (M + 1)) ∉ A := fun h => h0 (List.mem_append_left _ h)
  have h0B : (0 : Fin (M + 1)) ∉ B := fun h => h0 (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hmem0 : (0 : Fin (M + 1)) ∈ Finset.univ.erase y := by simp [Ne.symm hy0]
  rw [← Finset.add_sum_erase _ _ hmem0]
  have hty : t s y 0 = (if A = [] then 1 else 0) + (if B = [] then 1 else 0) := by
    have hh : ((A ++ y :: B).head? = some y) ↔ A = [] := by
      cases A with
      | nil => simp
      | cons a A' =>
        simp only [List.cons_append, List.head?_cons, Option.some.injEq]
        constructor
        · intro h; exact absurd (h ▸ List.mem_cons_self) hyA
        · intro h; cases h
    have hl : ((A ++ y :: B).getLast? = some y) ↔ B = [] := by
      cases B with
      | nil => simp
      | cons b B' =>
        constructor
        · intro h
          have h' : (b :: B').getLast? = some y := by
            simpa [List.getLast?_append, List.getLast?_cons_cons] using h
          exact absurd (List.mem_of_getLast? h') hyB
        · intro h; cases h
    rw [t_endpoint hs hR hyR hy0, hRAB]
    simp only [hh, hl]
  have e : ∀ z ∈ (Finset.univ.erase y).erase 0, t s y z =
      if (B.head? = some z ∨ A.getLast? = some z) then 1 else 0 := by
    intro z hz
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hz
    obtain ⟨hz0, hzy⟩ := hz
    have hiff : adj s y z ↔ (B.head? = some z ∨ A.getLast? = some z) := by
      rw [adj_iff_run hs hR hyR, hRAB, pair_char A B y z hyA hyB, pair_char' A B y z hyA hyB]
    rw [t_adj hy0 hz0 (Ne.symm hzy)]
    exact if_congr hiff rfl rfl
  rw [Finset.sum_congr rfl e, ← Finset.card_filter, hty]
  have hSmem : ∀ w, w ∈ A ∨ w ∈ B → w ∈ (Finset.univ.erase y).erase 0 := by
    intro w hw
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rcases hw with hw | hw
    · exact ⟨fun h => h0A (h ▸ hw), fun h => hyA (h ▸ hw)⟩
    · exact ⟨fun h => h0B (h ▸ hw), fun h => hyB (h ▸ hw)⟩
  rcases List.eq_nil_or_concat A with rfl | ⟨A', a, rfl⟩ <;> rcases B with _ | ⟨b, B'⟩ <;> simp only [List.concat_eq_append] at *
  · simp
  · have : ((Finset.univ.erase y).erase 0).filter (fun z => (b :: B').head? = some z ∨ ([] : List (Fin (M + 1))).getLast? = some z) = {b} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h | h⟩
        · simp at h; exact h.symm
        · simp at h
      · intro hz; rw [hz]
        exact ⟨hSmem b (Or.inr (by simp)), Or.inl (by simp)⟩
    rw [this]; simp
  · have : ((Finset.univ.erase y).erase 0).filter (fun z => ([] : List (Fin (M + 1))).head? = some z ∨ (A' ++ [a]).getLast? = some z) = {a} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h | h⟩
        · simp at h
        · simp at h; exact h.symm
      · intro hz; rw [hz]
        exact ⟨hSmem a (Or.inl (by simp)), Or.inr (by simp)⟩
    rw [this]; simp
  · have hab : a ≠ b := by
      rintro rfl
      exact hdisj a (by simp) a (by simp) rfl
    have : ((Finset.univ.erase y).erase 0).filter (fun z => (b :: B').head? = some z ∨ (A' ++ [a]).getLast? = some z) = {a, b} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h | h⟩
        · simp at h; exact Or.inr h.symm
        · simp at h; exact Or.inl h.symm
      · rintro (hz | hz)
        · rw [hz]; exact ⟨hSmem a (Or.inl (by simp)), Or.inr (by simp)⟩
        · rw [hz]; exact ⟨hSmem b (Or.inr (by simp)), Or.inl (by simp)⟩
    rw [this, Finset.card_pair hab]; simp

theorem relation_A_core {M n : ℕ} (I : Instance M n) :
    (∀ y : Fin (M + 1), y ≠ 0 → t (init M) y 0 = 2) ∧
    ∀ s : State M, Reachable I s →
      ∀ y : Fin (M + 1), y ≠ 0 → ∑ z ∈ Finset.univ.erase y, t s y z = 2 := by
  refine ⟨?_, ?_⟩
  · intro y hy
    have hR : [y] ∈ init M := by
      simp only [init, List.mem_map]
      exact ⟨y, mem_customers.2 hy, rfl⟩
    rw [t_endpoint isAllocation_init hR (by simp) hy]
    simp
  · intro s hs y hy
    exact sum_t_eq_two (reachable_alloc I hs) hy

lemma sum_Ioi_update (x : Fin (n + 1) → ℕ∞) (j i : Fin (n + 1)) (hij : i < j) (hx : 1 ≤ x j) :
    ∑ k ∈ Finset.Ioi i, x k = ∑ k ∈ Finset.Ioi i, Function.update x j (x j - 1) k + 1 := by
  have hj : j ∈ Finset.Ioi i := Finset.mem_Ioi.2 hij
  have h1 := Finset.sum_update_of_mem hj x (x j)
  have h2 := Finset.sum_update_of_mem hj x (x j - 1)
  rw [Function.update_eq_self] at h1
  rw [h1, h2, add_right_comm, tsub_add_cancel_of_le hx]

lemma sum_Ioi_update' (x : Fin (n + 1) → ℕ∞) (j i : Fin (n + 1)) (hij : j ≤ i) (v : ℕ∞) :
    ∑ k ∈ Finset.Ioi i, Function.update x j v k = ∑ k ∈ Finset.Ioi i, x k := by
  apply Finset.sum_congr rfl
  intro k hk
  have : k ≠ j := by
    intro h; subst h
    exact absurd (Finset.mem_Ioi.1 hk) (not_lt.2 hij)
  exact Function.update_of_ne this _ _

theorem fleet_aux : ∀ (k : ℕ) (I : Instance M n), Monotone I.C → I.x 0 = ⊤ →
    ∀ L : Multiset ℝ, Multiset.card L = k → I.TableIIOK L → I.FleetFeasible L := by
  intro k
  induction k with
  | zero =>
    intro I hC hx L hL hT
    rw [Multiset.card_eq_zero] at hL
    subst hL
    refine ⟨0, by simp, by simp, ?_⟩
    intro i; simp
  | succ k ih =>
    intro I hC hx L hL hT
    have hLne : L ≠ 0 := by
      intro h; subst h; simp at hL
    obtain ⟨l, hlL, hlmax⟩ : ∃ l ∈ L, ∀ l' ∈ L, l' ≤ l := by
      have hne : L.toFinset.Nonempty := by
        rw [Multiset.toFinset_nonempty]; exact hLne
      obtain ⟨l, hl, hmax⟩ := L.toFinset.exists_max_image id hne
      exact ⟨l, Multiset.mem_toFinset.1 hl, fun l' hl' => hmax l' (Multiset.mem_toFinset.2 hl')⟩
    obtain ⟨L', rfl⟩ := Multiset.exists_cons_of_mem hlL
    -- find the class j
    obtain ⟨j, hjC, hjx⟩ : ∃ j : Fin (n + 1), l ≤ I.C j ∧ 1 ≤ I.x j := by
      by_cases hex : ∃ i, I.C i < l
      · obtain ⟨i, hi, himax⟩ : ∃ i ∈ Finset.univ.filter (fun i => I.C i < l), ∀ i' ∈ Finset.univ.filter (fun i => I.C i < l), i' ≤ i := by
          have : (Finset.univ.filter (fun i => I.C i < l)).Nonempty := by
            obtain ⟨i, hi⟩ := hex; exact ⟨i, by simp [hi]⟩
          exact ⟨_, Finset.max'_mem _ this, fun i' hi' => Finset.le_max' _ i' hi'⟩
        by_contra hno
        push Not at hno
        have hs : ∑ k ∈ Finset.Ioi i, I.x k = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hk' := Finset.mem_Ioi.1 hk
          have hlk : l ≤ I.C k := by
            by_contra h
            push Not at h
            exact absurd (himax k (by simp [h])) (not_le.2 hk')
          have := hno k hlk
          simpa using this
        have h1 := hT i
        rw [hs] at h1
        have h2 : 1 ≤ (Multiset.filter (fun l' => I.C i < l') (l ::ₘ L')).card := by
          exact Multiset.card_pos_iff_exists_mem.2
            ⟨l, Multiset.mem_filter.2 ⟨Multiset.mem_cons_self _ _, by simpa using hi⟩⟩
        have h3 : ((1 : ℕ) : ℕ∞) ≤ ((Multiset.filter (fun l' => I.C i < l') (l ::ₘ L')).card : ℕ∞) := by
          exact_mod_cast h2
        have := h3.trans h1
        simp at this
      · push Not at hex
        exact ⟨0, hex 0 |> fun h => h, by rw [hx]; exact le_top⟩
    let x' : Fin (n + 1) → ℕ∞ := Function.update I.x j (I.x j - 1)
    let I' : Instance M n := { I with x := x' }
    have hx' : I'.x 0 = ⊤ := by
      show Function.update I.x j (I.x j - 1) 0 = ⊤
      by_cases hj0 : j = 0
      · subst hj0
        rw [Function.update_self, hx]; rfl
      · rw [Function.update_of_ne (Ne.symm hj0), hx]
    have hT' : I'.TableIIOK L' := by
      intro i
      show ((L'.filter (fun l' => I.C i < l')).card : ℕ∞) ≤ ∑ k ∈ Finset.Ioi i, x' k
      have hTi := hT i
      rcases le_or_gt j i with hij | hij
      · have hlle : ¬ I.C i < l := not_lt.2 (hjC.trans (hC hij))
        rw [Multiset.filter_cons_of_neg _ hlle] at hTi
        rw [sum_Ioi_update' I.x j i hij] 
        exact hTi
      · have hTi' := hTi
        rw [sum_Ioi_update I.x j i hij hjx] at hTi'
        by_cases hli : I.C i < l
        · rw [Multiset.filter_cons_of_pos _ hli, Multiset.card_cons] at hTi'
          push_cast at hTi'
          exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 hTi'
        · have : L'.filter (fun l' => I.C i < l') = 0 := by
            rw [Multiset.filter_eq_nil]
            intro a ha hlt
            exact hli (lt_of_lt_of_le hlt (hlmax a (Multiset.mem_cons_of_mem ha)) |> fun h => by
              exact lt_of_lt_of_le hlt (hlmax a (Multiset.mem_cons_of_mem ha)))
          rw [this]; simp
    have hC' : Monotone I'.C := hC
    have hcard : Multiset.card L' = k := by
      rw [Multiset.card_cons] at hL; omega
    obtain ⟨κ', h1, h2, h3⟩ := ih I' hC' hx' L' hcard hT'
    refine ⟨(l, j) ::ₘ κ', ?_, ?_, ?_⟩
    · simp [h1]
    · intro p hp
      rcases Multiset.mem_cons.1 hp with rfl | hp
      · exact hjC
      · exact h2 p hp
    · intro i
      by_cases hij : j = i
      · subst hij
        rw [Multiset.filter_cons_of_pos (p := fun p : ℝ × Fin (n + 1) => p.2 = j) (a := (l, j)) (s := κ') rfl, Multiset.card_cons]
        have := h3 j
        change ((Multiset.filter (fun p => p.2 = j) κ').card : ℕ∞) ≤ Function.update I.x j (I.x j - 1) j at this
        rw [Function.update_self] at this
        push_cast
        calc ((Multiset.filter (fun p => p.2 = j) κ').card : ℕ∞) + 1 ≤ (I.x j - 1) + 1 := by gcongr
          _ = I.x j := tsub_add_cancel_of_le hjx
      · rw [Multiset.filter_cons_of_neg _ (by simpa using hij)]
        have := h3 i
        change ((Multiset.filter (fun p => p.2 = i) κ').card : ℕ∞) ≤ Function.update I.x j (I.x j - 1) i at this
        rwa [Function.update_of_ne (Ne.symm hij)] at this


lemma runLoad_orientEnd (I : Instance M n) (R : List (Fin (M + 1))) (y : Fin (M + 1)) :
    I.runLoad (orientEnd R y) = I.runLoad R := by
  unfold Instance.runLoad
  exact ((orientEnd_perm R y).map I.q).sum_eq

lemma runLoad_orientStart (I : Instance M n) (R : List (Fin (M + 1))) (y : Fin (M + 1)) :
    I.runLoad (orientStart R y) = I.runLoad R := by
  unfold Instance.runLoad
  exact ((orientStart_perm R y).map I.q).sum_eq

lemma tableII_reach (I : Instance M n) (hinit : I.TableIIOK ↑((init M).map I.runLoad))
    {s : State M} (hs : Reachable I s) : I.TableIIOK ↑(s.map I.runLoad) := by
  induction hs with
  | refl => exact hinit
  | tail hr hstep ih =>
    rename_i s1 s2
    obtain ⟨a, b, hadm, -, rfl⟩ := hstep
    obtain ⟨R, R', rest, hR, hR', hyR, hzR', hyR', hzR, hperm, hrest, hrest2, hlink, hQ1, hQ2, hRe, hR'e⟩ :=
      link_struct I (reachable_alloc I hr) hadm
    have : (↑((link s1 a b).map I.runLoad) : Multiset ℝ) = amendedLoads I s1 a b := by
      rw [hlink]
      unfold amendedLoads
      rw [← hrest]
      congr 1
      simp only [List.map_append, List.map_cons, List.map_nil]
      congr 2
      have e3 : I.runLoad (orientEnd R a ++ orientStart R' b) =
          I.runLoad (orientEnd R a) + I.runLoad (orientStart R' b) := by
        unfold Instance.runLoad; simp [List.map_append]
      rw [e3, runLoad_orientEnd, runLoad_orientStart, hQ1, hQ2]
    rw [this]
    exact hadm.2.2.2.2.2.2

theorem reachable_feasible_core {M n : ℕ} (I : Instance M n) (hC : StrictMono I.C)
    (hx : I.x 0 = ⊤) (hinit : I.TableIIOK ↑((init M).map I.runLoad))
    (s : State M) (hs : Reachable I s) :
    IsAllocation s ∧ I.FleetFeasible ↑(s.map I.runLoad) :=
  ⟨reachable_alloc I hs, fleet_aux _ I hC.monotone hx _ rfl (tableII_reach I hinit hs)⟩

lemma length_step (I : Instance M n) {s s' : State M} (hs : Reachable I s) (h : Step I s s') :
    s'.length < s.length := by
  obtain ⟨a, b, hadm, -, rfl⟩ := h
  obtain ⟨R, R', rest, -, -, -, -, -, -, hperm, -, -, hlink, -⟩ :=
    link_struct I (reachable_alloc I hs) hadm
  rw [hlink, hperm.length_eq]
  simp

lemma acc_aux (I : Instance M n) : ∀ k : ℕ, ∀ s : State M, s.length = k → Reachable I s →
    Acc (fun s' s => Step I s s') s := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hk hs
    constructor
    intro s' hstep
    exact ih s'.length (hk ▸ length_step I hs hstep) s' rfl (reachable_step I hs hstep)

lemma exists_step (I : Instance M n) (s : State M) (h : ¬ Terminal I s) : ∃ s', Step I s s' := by
  unfold Terminal at h
  push Not at h
  obtain ⟨y, z, hyz⟩ := h
  have hne : (Finset.univ.filter (fun p : Fin (M + 1) × Fin (M + 1) => Admissible I s p.1 p.2)).Nonempty :=
    ⟨(y, z), by simpa using hyz⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image _ (fun p : Fin (M + 1) × Fin (M + 1) => I.saving p.1 p.2) hne
  refine ⟨link s p.1 p.2, p.1, p.2, by simpa using hp, ?_, rfl⟩
  intro y' z' h'
  exact hmax (y', z') (by simpa using h')

/-! ### mileage invariant -/

lemma adj_symm (s : State M) (u v : Fin (M + 1)) : adj s u v ↔ adj s v u := by
  unfold adj; simp only [or_comm]

lemma mileage_init (I : Instance M n) (hsymm : ∀ i j, I.d i j = I.d j i) :
    I.mileage (init M) = ∑ j ∈ Finset.univ.erase (0 : Fin (M + 1)), 2 * I.d 0 j := by
  unfold Instance.mileage init
  rw [List.map_map]
  have h1 : ∀ j : Fin (M + 1), (SupplyChainTheory.routeCost I.d ∘ fun j => [j]) j = 2 * I.d 0 j := by
    intro j
    simp only [Function.comp]
    rw [routeCost_eq I.d (by simp)]
    simp [wl, hsymm j 0]
    ring
  rw [List.map_congr_left (fun j _ => h1 j)]
  have h2 : (customers M).toFinset = Finset.univ.erase 0 := by
    ext j; simp [mem_customers]
  rw [← h2, List.sum_toFinset _ customers_nodup]

lemma pset_link (I : Instance M n) {s : State M} (hs : IsAllocation s) {a b : Fin (M + 1)}
    (hadm : Admissible I s a b) {q1 q2 : Fin (M + 1)} (hq0 : q1 ≠ 0) (hq : q1 < q2)
    (hab : (q1 = a ∧ q2 = b) ∨ (q1 = b ∧ q2 = a)) :
    (Finset.univ ×ˢ Finset.univ).filter
        (fun p : Fin (M + 1) × Fin (M + 1) => p.1 ≠ 0 ∧ p.1 < p.2 ∧ t (link s a b) p.1 p.2 = 1) =
      insert (q1, q2) ((Finset.univ ×ˢ Finset.univ).filter
        (fun p : Fin (M + 1) × Fin (M + 1) => p.1 ≠ 0 ∧ p.1 < p.2 ∧ t s p.1 p.2 = 1)) ∧
    (q1, q2) ∉ (Finset.univ ×ˢ Finset.univ).filter
        (fun p : Fin (M + 1) × Fin (M + 1) => p.1 ≠ 0 ∧ p.1 < p.2 ∧ t s p.1 p.2 = 1) := by
  have hq20 : q2 ≠ 0 := by
    intro h; subst h; exact absurd hq (by simp)
  refine ⟨?_, ?_⟩
  · ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_insert,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hu, huv, ht⟩
      have hv : v ≠ 0 := by
        intro h; subst h; exact absurd huv (by simp)
      rw [t_adj hu hv (ne_of_lt huv)] at ht
      have hadj : adj (link s a b) u v := by
        by_contra hc; rw [if_neg hc] at ht; exact absurd ht (by norm_num)
      rcases (adj_link I hs hadm u v).1 hadj with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right
        refine ⟨hu, huv, ?_⟩
        rw [t_adj hu hv (ne_of_lt huv), if_pos h]
      · left
        rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1.symm, h2.symm⟩
        · subst h1; subst h2; exact absurd hq (lt_asymm huv)
      · left
        rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1; subst h2; exact absurd hq (lt_asymm huv)
        · exact ⟨h1.symm, h2.symm⟩
    · rintro (⟨rfl, rfl⟩ | ⟨hu, huv, ht⟩)
      · refine ⟨hq0, hq, ?_⟩
        rw [t_adj hq0 hq20 (ne_of_lt hq), if_pos ((adj_link I hs hadm _ _).2 ?_)]
        rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
        · exact Or.inr (Or.inr ⟨h1, h2⟩)
      · have hv : v ≠ 0 := by
          intro h; subst h; exact absurd huv (by simp)
        refine ⟨hu, huv, ?_⟩
        rw [t_adj hu hv (ne_of_lt huv)] at ht ⊢
        have hadj : adj s u v := by
          by_contra hc; rw [if_neg hc] at ht; exact absurd ht (by norm_num)
        rw [if_pos ((adj_link I hs hadm u v).2 (Or.inl hadj))]
  · intro hmem
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hmem
    obtain ⟨-, -, ht⟩ := hmem
    rw [t_adj hq0 hq20 (ne_of_lt hq)] at ht
    have hadj : adj s q1 q2 := by
      by_contra hc; rw [if_neg hc] at ht; exact absurd ht (by norm_num)
    obtain ⟨r, hr, h⟩ := hadj
    have h1 : q1 ∈ r ∧ q2 ∈ r := by
      rcases h with h | h
      · exact ⟨h.subset (by simp), h.subset (by simp)⟩
      · exact ⟨h.subset (by simp), h.subset (by simp)⟩
    apply hadm.2.2.2.2.2.1
    refine ⟨r, hr, ?_⟩
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1
    · exact ⟨h1.2, h1.1⟩

theorem savings_procedure_correct_aux (I : Instance M n) (hsymm : ∀ i j, I.d i j = I.d j i)
    {s : State M} (hs : Reachable I s) :
    I.mileage s = ∑ j ∈ Finset.univ.erase (0 : Fin (M + 1)), 2 * I.d 0 j -
        ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter
            (fun p : Fin (M + 1) × Fin (M + 1) => p.1 ≠ 0 ∧ p.1 < p.2 ∧ t s p.1 p.2 = 1),
          I.saving p.1 p.2 := by
  induction hs with
  | refl =>
    rw [mileage_init I hsymm]
    have : (Finset.univ ×ˢ Finset.univ).filter
            (fun p : Fin (M + 1) × Fin (M + 1) => p.1 ≠ 0 ∧ p.1 < p.2 ∧ t (init M) p.1 p.2 = 1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro ⟨u, v⟩ -
      simp only
      rintro ⟨hu, huv, ht⟩
      have hv : v ≠ 0 := by
        intro h; subst h; exact absurd huv (by simp)
      rw [t_adj hu hv (ne_of_lt huv)] at ht
      have hadj : adj (init M) u v := by
        by_contra hc; rw [if_neg hc] at ht; exact absurd ht (by norm_num)
      obtain ⟨r, hr, h⟩ := hadj
      simp only [init, List.mem_map] at hr
      obtain ⟨j, -, rfl⟩ := hr
      rcases h with h | h <;> simpa using h.length_le
    rw [this]; simp
  | tail hr hstep ih =>
    rename_i s1 s2
    obtain ⟨a, b, hadm, -, rfl⟩ := hstep
    have hal := reachable_alloc I hr
    have hab : a ≠ b := hadm.2.2.1
    rw [link_saving_core I hsymm s1 hr a b hadm, ih]
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · obtain ⟨h1, h2⟩ := pset_link I hal hadm (q1 := a) (q2 := b) hadm.1 hlt (Or.inl ⟨rfl, rfl⟩)
      rw [h1, Finset.sum_insert h2]
      ring
    · obtain ⟨h1, h2⟩ := pset_link I hal hadm (q1 := b) (q2 := a) hadm.2.1 hlt (Or.inr ⟨rfl, rfl⟩)
      rw [h1, Finset.sum_insert h2]
      have : I.saving b a = I.saving a b := by
        unfold Instance.saving; rw [hsymm a b]; ring
      simp only [this]
      ring

theorem main_core {M n : ℕ} (I : Instance M n)
    (hsymm : ∀ i j, I.d i j = I.d j i) (hC : StrictMono I.C) (hx : I.x 0 = ⊤)
    (hinit : I.TableIIOK ↑((init M).map I.runLoad)) :
    Acc (fun s' s => Step I s s') (init M) ∧
    (∀ s : State M, Reachable I s → ¬ Terminal I s → ∃ s', Step I s s') ∧
    (∀ s : State M, Reachable I s → Terminal I s →
      IsAllocation s ∧ I.FleetFeasible ↑(s.map I.runLoad)) ∧
    (∀ s : State M, Reachable I s → Terminal I s →
      ∀ y : Fin (M + 1), y ≠ 0 → ∑ z ∈ Finset.univ.erase y, t s y z = 2) ∧
    (∀ s : State M, Reachable I s → Terminal I s →
      I.mileage s = ∑ j ∈ Finset.univ.erase (0 : Fin (M + 1)), 2 * I.d 0 j -
        ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter
            (fun p : Fin (M + 1) × Fin (M + 1) => p.1 ≠ 0 ∧ p.1 < p.2 ∧ t s p.1 p.2 = 1),
          I.saving p.1 p.2) :=
  ⟨acc_aux I _ (init M) rfl Relation.ReflTransGen.refl,
   fun s _ hnt => exists_step I s hnt,
   fun s hs _ => reachable_feasible_core I hC hx hinit s hs,
   fun s hs _ y hy => (relation_A_core I).2 s hs y hy,
   fun s hs _ => savings_procedure_correct_aux I hsymm hs⟩

/-! ### TSP case -/

lemma wl_nonneg (c : Fin (M + 1) → Fin (M + 1) → ℝ) (hc : ∀ i j, 0 ≤ c i j) :
    ∀ L : List (Fin (M + 1)), 0 ≤ wl c L
  | [] => le_rfl
  | [_] => le_rfl
  | a :: b :: l => by
    have := wl_nonneg c hc (b :: l)
    simp only [wl]
    linarith [hc a b]

lemma routeCost_nil (c : Fin (M + 1) → Fin (M + 1) → ℝ) :
    SupplyChainTheory.routeCost c [] = c 0 0 := by
  unfold SupplyChainTheory.routeCost SupplyChainTheory.closedLength
  simp

lemma routeCost_nonneg (c : Fin (M + 1) → Fin (M + 1) → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (L : List (Fin (M + 1))) : 0 ≤ SupplyChainTheory.routeCost c L := by
  by_cases hL : L = []
  · subst hL; rw [routeCost_nil]; exact hc _ _
  · rw [routeCost_eq c hL]
    have := wl_nonneg c hc L
    linarith [hc 0 (L.headD 0), hc (L.getLastD 0) 0]

lemma routeCost_append_le (c : Fin (M + 1) → Fin (M + 1) → ℝ)
    (hd : SupplyChainTheory.VRPMetric c) (X Y : List (Fin (M + 1))) :
    SupplyChainTheory.routeCost c (X ++ Y) ≤
      SupplyChainTheory.routeCost c X + SupplyChainTheory.routeCost c Y := by
  by_cases hX : X = []
  · subst hX
    rw [List.nil_append, routeCost_nil, hd.refl]; linarith
  by_cases hY : Y = []
  · subst hY
    rw [List.append_nil, routeCost_nil, hd.refl]; linarith
  have hy : X.getLast? = some (X.getLastD 0) := by
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hX
    simp [List.getLastD_eq_getLast?, List.getLast?_cons]
  have hz : Y.head? = some (Y.headD 0) := by
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hY
    simp
  rw [routeCost_join c hX hY hy hz]
  have := hd.triangle (X.getLastD 0) (Y.headD 0) 0
  linarith

lemma routeCost_flatten_le (c : Fin (M + 1) → Fin (M + 1) → ℝ)
    (hd : SupplyChainTheory.VRPMetric c) :
    ∀ s : List (List (Fin (M + 1))),
      SupplyChainTheory.routeCost c s.flatten ≤ (s.map (SupplyChainTheory.routeCost c)).sum
  | [] => by simp [routeCost_nil, hd.refl]
  | r :: s => by
    have := routeCost_flatten_le c hd s
    have h2 := routeCost_append_le c hd r s.flatten
    simp only [List.flatten_cons, List.map_cons, List.sum_cons]
    linarith

theorem tsp_case_core {M n : ℕ} (I : Instance M n) (hd : SupplyChainTheory.VRPMetric I.d)
    (hcap : ∑ j ∈ Finset.univ.erase (0 : Fin (M + 1)), I.q j ≤ I.C (Fin.last n))
    (htruck : 1 ≤ I.x (Fin.last n)) :
    optMileage I = SupplyChainTheory.tspOpt I.d := by
  unfold optMileage SupplyChainTheory.tspOpt
  have hnn := hd.nonneg
  have hT0 : {z | ∃ L, SupplyChainTheory.IsCustomerTour L ∧
      z = SupplyChainTheory.routeCost I.d L}.Nonempty :=
    ⟨_, customers M, ⟨customers_nodup, by simp [mem_customers], fun v hv => mem_customers.2 hv⟩, rfl⟩
  have hTA : ∀ t ∈ {z | ∃ L, SupplyChainTheory.IsCustomerTour L ∧
      z = SupplyChainTheory.routeCost I.d L}, ∃ a ∈ {m | ∃ s : State M, IsAllocation s ∧
        I.FleetFeasible ↑(s.map I.runLoad) ∧ m = I.mileage s}, a ≤ t := by
    rintro t ⟨L, ⟨hnd, h0, hall⟩, rfl⟩
    by_cases hL : L = []
    · subst hL
      refine ⟨0, ⟨[], ⟨by simp, ?_⟩, ⟨0, by simp, by simp, by simp⟩, by simp [Instance.mileage]⟩,
        routeCost_nonneg _ hnn _⟩
      have : customers M = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro j hj
        exact List.not_mem_nil (hall j (mem_customers.1 hj))
      rw [this]; simp
    · have hLset : L.toFinset = Finset.univ.erase 0 := by
        ext v
        simp only [List.mem_toFinset, Finset.mem_erase, Finset.mem_univ, and_true]
        exact ⟨fun h hv => h0 (hv ▸ h), hall v⟩
      refine ⟨I.mileage [L], ⟨[L], ⟨?_, ?_⟩, ?_, rfl⟩, ?_⟩
      · intro r hr
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨hL, h0⟩
      · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
        rw [List.perm_ext_iff_of_nodup hnd customers_nodup]
        intro v
        rw [mem_customers]
        exact ⟨fun h hv => h0 (hv ▸ h), hall v⟩
      · refine ⟨{(I.runLoad L, Fin.last n)}, by simp, ?_, ?_⟩
        · intro p hp
          rw [Multiset.mem_singleton] at hp; subst hp
          show I.runLoad L ≤ I.C (Fin.last n)
          unfold Instance.runLoad
          rw [← List.sum_toFinset I.q hnd, hLset]
          exact hcap
        · intro i
          by_cases hi : i = Fin.last n
          · subst hi
            rw [Multiset.filter_singleton, if_pos rfl]
            simpa using htruck
          · have : Multiset.filter (fun p : ℝ × Fin (n + 1) => p.2 = i) {(I.runLoad L, Fin.last n)} = 0 := by
              rw [Multiset.filter_singleton, if_neg (by simpa [eq_comm] using hi)]
              exact Multiset.empty_eq_zero
            simp [this]
      · simp [Instance.mileage]
  have hAT : ∀ a ∈ {m | ∃ s : State M, IsAllocation s ∧ I.FleetFeasible ↑(s.map I.runLoad) ∧
      m = I.mileage s}, ∃ t ∈ {z | ∃ L, SupplyChainTheory.IsCustomerTour L ∧
        z = SupplyChainTheory.routeCost I.d L}, t ≤ a := by
    rintro a ⟨s, hal, -, rfl⟩
    refine ⟨SupplyChainTheory.routeCost I.d s.flatten, ⟨s.flatten, ⟨hal.nodup_flat, ?_, ?_⟩, rfl⟩, ?_⟩
    · intro h
      obtain ⟨r, hr, h'⟩ := List.mem_flatten.1 h
      exact (hal.1 r hr).2 h'
    · intro v hv
      exact hal.2.mem_iff.2 (mem_customers.2 hv)
    · exact routeCost_flatten_le I.d hd s
  have hbA : BddBelow {m | ∃ s : State M, IsAllocation s ∧ I.FleetFeasible ↑(s.map I.runLoad) ∧
      m = I.mileage s} := by
    refine ⟨0, ?_⟩
    rintro a ⟨s, -, -, rfl⟩
    unfold Instance.mileage
    apply List.sum_nonneg
    intro x hx
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
    exact routeCost_nonneg _ hnn _
  have hbT : BddBelow {z | ∃ L, SupplyChainTheory.IsCustomerTour L ∧
      z = SupplyChainTheory.routeCost I.d L} := by
    refine ⟨0, ?_⟩
    rintro z ⟨L, -, rfl⟩
    exact routeCost_nonneg _ hnn _
  have hAne : {m | ∃ s : State M, IsAllocation s ∧ I.FleetFeasible ↑(s.map I.runLoad) ∧
      m = I.mileage s}.Nonempty := by
    obtain ⟨t, ht⟩ := hT0
    obtain ⟨a, ha, -⟩ := hTA t ht
    exact ⟨a, ha⟩
  apply le_antisymm
  · exact le_csInf hT0 (fun t ht => by
      obtain ⟨a, ha, hle⟩ := hTA t ht
      exact (csInf_le hbA ha).trans hle)
  · exact le_csInf hAne (fun a ha => by
      obtain ⟨t, ht, hle⟩ := hAT a ha
      exact (csInf_le hbT ht).trans hle)

end ClarkeWright64.Savings

open ClarkeWright64.Savings


theorem solution {M n : ℕ} (I : Instance M n) (hd : SupplyChainTheory.VRPMetric I.d)
    (hcap : ∑ j ∈ Finset.univ.erase (0 : Fin (M + 1)), I.q j ≤ I.C (Fin.last n))
    (htruck : 1 ≤ I.x (Fin.last n)) :
    optMileage I = SupplyChainTheory.tspOpt I.d := by
  exact tsp_case_core I hd hcap htruck
