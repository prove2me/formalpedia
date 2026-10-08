-- Prove2me | solution 1 for BCMPNetworks.Core.independent_balance_imp_global_balance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:04:17.101022+00:00
-- url     : https://prove2.me/submissions/59b8a07b-3ee1-439f-bcb8-61ce5304b2f7

import Mathlib
import Definitions.Def_BCMPNetworks_Core_Network
import Definitions.Def_BCMPNetworks_Core_Dynamics
import Definitions.Def_BCMPNetworks_Core_IndependentBalance

set_option autoImplicit false

namespace BCMPNetworks.Core.P4b

open BCMPNetworks.Core

lemma sum_ind {n c : ℕ} (hc : c < n) :
    ∑ k : Fin n, (if k.val = c then (1:ℕ) else 0) = 1 := by
  have h : ∀ k : Fin n, (k.val = c ↔ k = ⟨c, hc⟩) := fun k => by
    constructor
    · intro h; exact Fin.ext h
    · intro h; subst h; rfl
  simp only [h]
  simp

lemma sum_shift {n : ℕ} (f g : Fin n → ℕ) (a b : ℕ) (ha : a < n) (hb : b < n)
    (h : ∀ k : Fin n, g k + (if k.val = a then 1 else 0) = f k + (if k.val = b then 1 else 0)) :
    ∑ k, g k = ∑ k, f k := by
  have := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => h k)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ind ha, sum_ind hb] at this
  omega

lemma sum_dec {n : ℕ} (f g : Fin n → ℕ) (a : ℕ) (ha : a < n)
    (h : ∀ k : Fin n, g k + (if k.val = a then 1 else 0) = f k) : ∑ k, g k + 1 = ∑ k, f k := by
  have := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => h k)
  rw [Finset.sum_add_distrib, sum_ind ha] at this
  omega

lemma sum_count_list {R : ℕ} (l : List (Fin R)) : ∑ r, l.count r = l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, ih, List.length_cons]
    simp

lemma sum_countP_list {R : ℕ} {u : Fin R → ℕ+} (l : List (Σ r : Fin R, Fin (u r))) :
    ∑ r, l.countP (fun x => decide (x.1 = r)) = l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.countP_cons, Finset.sum_add_distrib, ih, List.length_cons]
    simp

variable {R : ℕ} {u : Fin R → ℕ+}

lemma finite_total_le (n : ℕ) : {y : LocalState R u | y.total ≤ n}.Finite := by
  have h1 := (List.finite_length_le (Fin R) n).image (LocalState.fcfs (u := u))
  have h2 := (Set.Finite.pi (ι := Fin R)
      (t := fun r => Set.pi Set.univ (fun _ : Fin (u r) => Set.Iic n))
      (fun r => Set.Finite.pi (fun _ => Set.finite_Iic n))).image (LocalState.stages (u := u))
  have h3 := (List.finite_length_le (Σ r : Fin R, Fin (u r)) n).image (LocalState.lcfs (u := u))
  refine ((h1.union h2).union h3).subset ?_
  intro y hy
  simp only [Set.mem_setOf_eq, LocalState.total, LocalState.count] at hy
  cases y with
  | fcfs l =>
    left; left
    refine ⟨l, ?_, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [← sum_count_list l]; simpa [LocalState.count] using hy
  | stages v =>
    left; right
    refine ⟨v, ?_, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies]
    intro r k
    simp only [LocalState.count] at hy
    have e1 : v r k ≤ ∑ k', v r k' :=
      Finset.single_le_sum (f := fun k' => v r k') (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have e2 : ∑ k', v r k' ≤ ∑ r', ∑ k', v r' k' :=
      Finset.single_le_sum (f := fun r' => ∑ k', v r' k') (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ r)
    omega
  | lcfs l =>
    right
    refine ⟨l, ?_, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [← sum_countP_list l]; simpa [LocalState.count] using hy

lemma count_enter (x : LocalState R u) (s r : Fin R) :
    (x.enter s).count r = x.count r + if r = s then 1 else 0 := by
  cases x with
  | fcfs l =>
    simp only [LocalState.enter, LocalState.count, List.count_append, List.count_singleton]
    by_cases h : r = s
    · subst h; simp
    · simp [h, Ne.symm h]
  | stages v =>
    simp only [LocalState.enter, LocalState.count]
    by_cases h : r = s
    · subst h
      rw [if_pos rfl]
      symm
      apply sum_dec _ _ 0 (u r).pos
      intro k
      by_cases hk : k.val = 0
      · rw [if_pos hk, if_pos ⟨rfl, hk⟩]
      · rw [if_neg hk, if_neg (fun hh => hk hh.2)]; rfl
    · simp [h]
  | lcfs l =>
    simp only [LocalState.enter, LocalState.count, List.countP_cons]
    by_cases h : r = s
    · subst h; simp
    · simp [h, Ne.symm h]

lemma fits_enter {t : CenterType} {x : LocalState R u} (h : x.Fits t) (s : Fin R) :
    (x.enter s).Fits t := by
  cases t <;> cases x <;> simp_all [LocalState.Fits, LocalState.enter]

lemma fits_fcfs {t : CenterType} {l l' : List (Fin R)} (h : (LocalState.fcfs l : LocalState R u).Fits t) :
    (LocalState.fcfs l' : LocalState R u).Fits t := by
  cases t <;> simp_all [LocalState.Fits]

lemma fits_stages {t : CenterType} {v v' : (r : Fin R) → Fin (u r) → ℕ}
    (h : (LocalState.stages v : LocalState R u).Fits t) :
    (LocalState.stages v' : LocalState R u).Fits t := by
  cases t <;> simp_all [LocalState.Fits]

lemma fits_lcfs {t : CenterType} {l l' : List (Σ r : Fin R, Fin (u r))}
    (h : (LocalState.lcfs l : LocalState R u).Fits t) :
    (LocalState.lcfs l' : LocalState R u).Fits t := by
  cases t <;> simp_all [LocalState.Fits]

variable {N m : ℕ} (net : Network N R m)

def AF (S : net.Config) : Prop := ∀ i, (S i).Fits (net.type i)

def Eff (S T : net.Config) : Prop :=
  ∃ src dst : Option (Fin N × Fin R),
    (∀ i' r', (T i').count r' + (if src = some (i', r') then 1 else 0) =
      (S i').count r' + (if dst = some (i', r') then 1 else 0)) ∧
    (∀ k, net.IsClosedChain k →
      (src.map (fun p => net.chain p.1 p.2) = some k ↔
        dst.map (fun p => net.chain p.1 p.2) = some k))

lemma af_update {S : net.Config} (h : AF net S) (i : Fin N) {y : LocalState R (net.u i)}
    (hy : y.Fits (net.type i)) : AF net (Function.update S i y) := by
  intro i'
  rcases eq_or_ne i' i with rfl | hi
  · rw [Function.update_self]; exact hy
  · rw [Function.update_of_ne hi]; exact h i'

lemma af_routeTo {T0 : net.Config} (h : AF net T0) (d : Option (Fin N × Fin R)) :
    AF net (net.routeTo T0 d) := by
  cases d with
  | none => exact h
  | some p =>
    obtain ⟨j, s⟩ := p
    exact af_update net h j (fits_enter (h j) s)

lemma count_routeTo (T0 : net.Config) (d : Option (Fin N × Fin R)) (i' : Fin N) (r' : Fin R) :
    (net.routeTo T0 d i').count r' = (T0 i').count r' + if d = some (i', r') then 1 else 0 := by
  cases d with
  | none => simp [Network.routeTo]
  | some p =>
    obtain ⟨j, s⟩ := p
    simp only [Network.routeTo, Network.enterAt]
    rcases eq_or_ne i' j with rfl | hi
    · rw [Function.update_self, count_enter]
      by_cases hs : r' = s
      · subst hs; simp
      · simp [hs, Ne.symm hs]
    · rw [Function.update_of_ne hi]; simp [Ne.symm hi]

lemma eff_none {S T : net.Config} (h : ∀ i' r', (T i').count r' = (S i').count r') :
    Eff net S T := ⟨none, none, by simp [h], by simp⟩

lemma eff_depart (hv : net.IsValid) {S T0 : net.Config} {i : Fin N} {r : Fin R}
    {d : Option (Fin N × Fin R)}
    (hc : ∀ i' r', (T0 i').count r' + (if some (i, r) = some (i', r') then 1 else 0) =
      (S i').count r')
    (hp : net.routeProb i r d ≠ 0) : Eff net S (net.routeTo T0 d) := by
  refine ⟨some (i, r), d, ?_, ?_⟩
  · intro i' r'
    rw [count_routeTo, ← hc i' r']
    ring
  · intro k hk
    cases d with
    | none =>
      simp only [Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq, iff_false]
      intro hck
      apply hp
      simp only [Network.routeProb]
      rw [hv.P_row_closed i r (by rw [hck]; exact hk)]
      ring
    | some p =>
      obtain ⟨j, s⟩ := p
      simp only [Network.routeProb] at hp
      simp only [Option.map_some, Option.some.injEq]
      rw [hv.P_chain i r j s hp]

lemma chainPop_eq {S T : net.Config} (h : Eff net S T) (k : Fin m) (hk : net.IsClosedChain k) :
    net.chainPop T k = net.chainPop S k := by
  obtain ⟨src, dst, hc, hch⟩ := h
  have key : ∀ o : Option (Fin N × Fin R),
      (∑ i, ∑ r, if net.chain i r = k then (if o = some (i, r) then 1 else 0) else 0) =
        if o.map (fun p => net.chain p.1 p.2) = some k then 1 else 0 := by
    intro o
    cases o with
    | none => simp
    | some p =>
      obtain ⟨a, b⟩ := p
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · by_cases hab : net.chain a b = k <;> simp [hab]
        · intro r _ hr; simp [Ne.symm hr]
        · simp
      · intro i _ hi
        apply Finset.sum_eq_zero; intro r _; simp [Ne.symm hi]
      · simp
  have hsum : net.chainPop T k + (if src.map (fun p => net.chain p.1 p.2) = some k then 1 else 0) =
      net.chainPop S k + (if dst.map (fun p => net.chain p.1 p.2) = some k then 1 else 0) := by
    rw [← key src, ← key dst]
    unfold Network.chainPop
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _
    have := hc i r
    split_ifs at this ⊢ <;> omega
  have hiff := hch k hk
  by_cases h1 : src.map (fun p => net.chain p.1 p.2) = some k
  · have h2 := hiff.mp h1
    rw [if_pos h1, if_pos h2] at hsum; omega
  · have h2 : ¬ dst.map (fun p => net.chain p.1 p.2) = some k := fun h => h1 (hiff.mpr h)
    rw [if_neg h1, if_neg h2] at hsum; omega

lemma total_le {S T : net.Config} (h : Eff net S T) (i' : Fin N) :
    (S i').total ≤ (T i').total + 1 := by
  obtain ⟨src, dst, hc, -⟩ := h
  have hb : ∑ r', (if src = some (i', r') then 1 else 0) ≤ 1 := by
    cases src with
    | none => simp
    | some p =>
      obtain ⟨a, b⟩ := p
      simp only [Option.some.injEq, Prod.mk.injEq]
      by_cases ha : a = i'
      · subst ha; simp
      · simp [ha]
  unfold LocalState.total
  have : ∑ r', (S i').count r' ≤
      ∑ r', ((T i').count r' + if src = some (i', r') then 1 else 0) :=
    Finset.sum_le_sum (fun r' _ => by have := hc i' r'; split_ifs at this ⊢ <;> omega)
  rw [Finset.sum_add_distrib] at this
  omega

lemma v_ne_of_stageRate {i : Fin N} {r : Fin R} {l : Fin (net.u i r)}
    {v : (r : Fin R) → Fin (net.u i r) → ℕ} {n : ℕ}
    (h : net.stageRate i r l v n ≠ 0) : v r l ≠ 0 := by
  intro hv; apply h; unfold Network.stageRate; split <;> simp [hv]

lemma step (hv : net.IsValid) (S : net.Config) (hS : AF net S) (ev : Network.Event N R net.u)
    (hr : net.evRate S ev ≠ 0) :
    AF net (net.evTarget S ev) ∧ Eff net S (net.evTarget S ev) := by
  cases ev with
  | arrive j s =>
    refine ⟨af_routeTo net hS (some (j, s)), none, some (j, s), ?_, ?_⟩
    · intro i' r'
      have := count_routeTo net S (some (j, s)) i' r'
      simp only [Network.routeTo] at this
      simp only [Network.evTarget]
      rw [this]; simp
    · intro k hk
      simp only [Option.map_none, Option.map_some, reduceCtorEq, false_iff, Option.some.injEq]
      intro hck
      apply hr
      have hq := hk j s hck
      simp only [Network.evRate, Network.arrivalRate]
      split <;> simp [hq]
  | fcfsDone i d =>
    simp only [Network.evRate] at hr
    simp only [Network.evTarget]
    rcases hSi : S i with l | v | l
    · rcases l with _ | ⟨r, rest⟩
      · simp [hSi] at hr
      · simp only [hSi] at hr ⊢
        have hfi : (LocalState.fcfs (r :: rest) : LocalState R (net.u i)).Fits (net.type i) := by
          have := hS i; rwa [hSi] at this
        refine ⟨af_routeTo net (af_update net hS i (fits_fcfs hfi)) d, ?_⟩
        apply eff_depart net hv _ (right_ne_zero_of_mul hr)
        intro i' r'
        rcases eq_or_ne i' i with rfl | hi
        · rw [Function.update_self, hSi]
          simp only [LocalState.count, List.count_cons, Option.some.injEq, Prod.mk.injEq, true_and]
          by_cases h : r = r' <;> simp [h]
        · rw [Function.update_of_ne hi]; simp [Ne.symm hi]
    · simp [hSi] at hr
    · simp [hSi] at hr
  | stageNext i r l =>
    simp only [Network.evRate] at hr
    simp only [Network.evTarget]
    rcases hSi : S i with l' | v | l'
    · simp [hSi] at hr
    · simp only [hSi] at hr ⊢
      have hfi : (LocalState.stages v : LocalState R (net.u i)).Fits (net.type i) := by
        have := hS i; rwa [hSi] at this
      have hv0 : v r l ≠ 0 := v_ne_of_stageRate net (left_ne_zero_of_mul hr)
      have hv' : ∀ k : Fin (net.u i r), k.val = l.val → v r k ≠ 0 := fun k hk => by
        have : k = l := Fin.ext hk
        subst this; exact hv0
      split_ifs with h
      · refine ⟨af_update net hS i (fits_stages hfi), eff_none net ?_⟩
        intro i' r'
        rcases eq_or_ne i' i with rfl | hi
        · rw [Function.update_self, hSi]
          simp only [LocalState.count]
          rcases eq_or_ne r' r with rfl | hr'
          · apply sum_shift _ _ l.val (l.val + 1) l.isLt h
            intro k
            by_cases hk : k.val = l.val
            · rw [if_pos ⟨rfl, hk⟩, if_pos hk, if_neg (by omega)]
              have := hv' k hk
              omega
            · by_cases hk2 : k.val = l.val + 1
              · rw [if_neg (fun hh => hk hh.2), if_pos ⟨rfl, hk2⟩, if_neg hk, if_pos hk2]
              · rw [if_neg (fun hh => hk hh.2), if_neg (fun hh => hk2 hh.2), if_neg hk, if_neg hk2]
          · simp [hr']
        · rw [Function.update_of_ne hi]
      · exact ⟨hS, eff_none net (fun _ _ => rfl)⟩
    · simp [hSi] at hr
  | stageDone i r l d =>
    simp only [Network.evRate] at hr
    simp only [Network.evTarget]
    rcases hSi : S i with l' | v | l'
    · simp [hSi] at hr
    · simp only [hSi] at hr ⊢
      have hfi : (LocalState.stages v : LocalState R (net.u i)).Fits (net.type i) := by
        have := hS i; rwa [hSi] at this
      have hv0 : v r l ≠ 0 :=
        v_ne_of_stageRate net (left_ne_zero_of_mul (left_ne_zero_of_mul hr))
      have hv' : ∀ k : Fin (net.u i r), k.val = l.val → v r k ≠ 0 := fun k hk => by
        have : k = l := Fin.ext hk
        subst this; exact hv0
      refine ⟨af_routeTo net (af_update net hS i (fits_stages hfi)) d, ?_⟩
      apply eff_depart net hv _ (right_ne_zero_of_mul hr)
      intro i' r'
      rcases eq_or_ne i' i with rfl | hi
      · rw [Function.update_self, hSi]
        simp only [LocalState.count]
        rcases eq_or_ne r' r with rfl | hr'
        · rw [if_pos rfl]
          apply sum_dec _ _ l.val l.isLt
          intro k
          by_cases hk : k.val = l.val
          · rw [if_pos ⟨rfl, hk⟩, if_pos hk]
            have := hv' k hk
            omega
          · rw [if_neg (fun hh => hk hh.2), if_neg hk]; rfl
        · have : ¬ (some (i', r) = some (i', r')) := by
            simp only [Option.some.injEq, Prod.mk.injEq, true_and]; exact Ne.symm hr'
          rw [if_neg this]
          simp [hr']
      · rw [Function.update_of_ne hi]; simp [Ne.symm hi]
    · simp [hSi] at hr
  | lcfsNext i =>
    simp only [Network.evRate] at hr
    simp only [Network.evTarget]
    rcases hSi : S i with l | v | l
    · simp [hSi] at hr
    · simp [hSi] at hr
    · rcases l with _ | ⟨⟨r0, l0⟩, rest⟩
      · simp [hSi] at hr
      · simp only [hSi] at hr ⊢
        have hfi : (LocalState.lcfs (⟨r0, l0⟩ :: rest) : LocalState R (net.u i)).Fits
            (net.type i) := by
          have := hS i; rwa [hSi] at this
        split_ifs with h
        · refine ⟨af_update net hS i (fits_lcfs hfi), eff_none net ?_⟩
          intro i' r'
          rcases eq_or_ne i' i with rfl | hi
          · rw [Function.update_self, hSi]
            simp [LocalState.count, List.countP_cons]
          · rw [Function.update_of_ne hi]
        · exact ⟨hS, eff_none net (fun _ _ => rfl)⟩
  | lcfsDone i d =>
    simp only [Network.evRate] at hr
    simp only [Network.evTarget]
    rcases hSi : S i with l | v | l
    · simp [hSi] at hr
    · simp [hSi] at hr
    · rcases l with _ | ⟨⟨r0, l0⟩, rest⟩
      · simp [hSi] at hr
      · simp only [hSi] at hr ⊢
        have hfi : (LocalState.lcfs (⟨r0, l0⟩ :: rest) : LocalState R (net.u i)).Fits
            (net.type i) := by
          have := hS i; rwa [hSi] at this
        refine ⟨af_routeTo net (af_update net hS i (fits_lcfs hfi)) d, ?_⟩
        apply eff_depart net hv _ (right_ne_zero_of_mul hr)
        intro i' r'
        rcases eq_or_ne i' i with rfl | hi
        · rw [Function.update_self, hSi]
          simp only [LocalState.count, List.countP_cons, Option.some.injEq, Prod.mk.injEq,
            true_and]
          by_cases h : r0 = r' <;> simp [h]
        · rw [Function.update_of_ne hi]; simp [Ne.symm hi]

lemma feas_target (hv : net.IsValid) (S : net.State) (ev : Network.Event N R net.u)
    (hr : net.evRate S.1 ev ≠ 0) : net.Feasible (net.evTarget S.1 ev) := by
  have hS : net.Feasible S.1 := S.2
  obtain ⟨hf, hK⟩ := hS
  obtain ⟨hf', he⟩ := step net hv S.1 hf ev hr
  refine ⟨hf', fun k hk => ?_⟩
  rw [chainPop_eq net he k hk]
  exact hK k hk

lemma pred_finite (hv : net.IsValid) (S : net.State) :
    {S' : net.State | ∃ ev, net.evTarget S'.1 ev = S.1 ∧ net.evRate S'.1 ev ≠ 0}.Finite := by
  have hF : (Set.pi Set.univ
      (fun i => {y : LocalState R (net.u i) | y.total ≤ (S.1 i).total + 1})).Finite :=
    Set.Finite.pi (fun i => finite_total_le _)
  refine (hF.preimage Subtype.val_injective.injOn).subset ?_
  rintro S' ⟨ev, ht, hr⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, true_implies]
  intro i
  have hS' : net.Feasible S'.1 := S'.2
  obtain ⟨_, he⟩ := step net hv S'.1 hS'.1 ev hr
  have := total_le net he i
  rw [ht] at this
  exact this

theorem main (hv : net.IsValid) (π : net.State → ℝ) (hπ : net.IndependentBalance π) :
    GlobalBalance π net.rate := by
  classical
  intro S
  have hout : ∑' S', net.rate S S' = ∑ ev, net.evRate S.1 ev := by
    have hs : ∀ ev, HasSum (fun S' : net.State =>
        if net.evTarget S.1 ev = S'.1 then net.evRate S.1 ev else 0) (net.evRate S.1 ev) := by
      intro ev
      by_cases hr : net.evRate S.1 ev = 0
      · simp only [hr, ite_self]; exact hasSum_zero
      · let T : net.State := ⟨_, feas_target net hv S ev hr⟩
        convert hasSum_single T (fun S' hS' => ?_) using 1
        · simp [T]
        · rw [if_neg]; intro h; apply hS'; exact Subtype.ext h.symm
    have := hasSum_sum (s := Finset.univ) (fun ev _ => hs ev)
    unfold Network.rate
    exact this.tsum_eq
  have hPf := pred_finite net hv S
  set Pf := hPf.toFinset with hPfdef
  have hsupp : ∀ S' ∉ Pf, ∀ ev,
      (if net.evTarget S'.1 ev = S.1 then net.evRate S'.1 ev else 0) = 0 := by
    intro S' hS' ev
    split_ifs with h
    · by_contra hne; exact hS' (hPf.mem_toFinset.mpr ⟨ev, h, hne⟩)
    · rfl
  have hin : ∑' S', π S' * net.rate S' S = ∑ S' ∈ Pf, π S' * net.rate S' S := by
    apply tsum_eq_sum; intro S' hS'
    unfold Network.rate
    rw [Finset.sum_eq_zero (fun ev _ => hsupp S' hS' ev), mul_zero]
  let Ls : Finset (Label N R m) :=
    (Pf ×ˢ Finset.univ).image (fun p => net.enterLabel p.1.1 p.2) ∪
      Finset.univ.image (net.leaveLabel S.1)
  have hIB : ∀ L, π S * ∑ ev, (if net.leaveLabel S.1 ev = L then net.evRate S.1 ev else 0) =
      ∑ S' ∈ Pf, π S' * ∑ ev, (if net.evTarget S'.1 ev = S.1 ∧ net.enterLabel S'.1 ev = L
        then net.evRate S'.1 ev else 0) := by
    intro L
    rw [hπ S L]
    apply tsum_eq_sum; intro S' hS'
    rw [Finset.sum_eq_zero, mul_zero]; intro ev _
    split_ifs with h
    · have := hsupp S' hS' ev; rw [if_pos h.1] at this; exact this
    · rfl
  rw [hout, hin]
  calc π S * ∑ ev, net.evRate S.1 ev
      = ∑ L ∈ Ls, π S * ∑ ev, (if net.leaveLabel S.1 ev = L then net.evRate S.1 ev else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl; intro ev _
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_univ ev)))]
    _ = ∑ L ∈ Ls, ∑ S' ∈ Pf, π S' * ∑ ev, (if net.evTarget S'.1 ev = S.1 ∧
          net.enterLabel S'.1 ev = L then net.evRate S'.1 ev else 0) :=
        Finset.sum_congr rfl (fun L _ => hIB L)
    _ = ∑ S' ∈ Pf, π S' * net.rate S' S := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro S' hS'
        rw [← Finset.mul_sum]; congr 1
        unfold Network.rate
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro ev _
        by_cases h : net.evTarget S'.1 ev = S.1
        · rw [if_pos h]
          simp only [h, true_and]
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨(S', ev), Finset.mem_product.mpr ⟨hS', Finset.mem_univ _⟩, rfl⟩))]
        · rw [if_neg h]; apply Finset.sum_eq_zero; intro L _
          rw [if_neg (fun hh => h hh.1)]

end BCMPNetworks.Core.P4b

open BCMPNetworks.Core in
theorem solution {N R m : ℕ} (net : Network N R m)
    (hnet : net.IsValid) (π : net.State → ℝ) (hπ : net.IndependentBalance π) :
    GlobalBalance π net.rate := by
  exact BCMPNetworks.Core.P4b.main net hnet π hπ
