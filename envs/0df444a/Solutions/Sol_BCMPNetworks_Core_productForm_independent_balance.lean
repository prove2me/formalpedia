-- Prove2me | solution 1 for BCMPNetworks.Core.productForm_independent_balance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:21:00.107524+00:00
-- url     : https://prove2.me/submissions/981e5848-b502-4fa3-8573-b77fc45f0575

import Mathlib
import Definitions.Def_BCMPNetworks_Core_Network
import Definitions.Def_BCMPNetworks_Core_Dynamics
import Definitions.Def_BCMPNetworks_Core_ProductForm
import Definitions.Def_BCMPNetworks_Core_IndependentBalance

set_option autoImplicit false

namespace BCMPNetworks.Core.P54b

open BCMPNetworks.Core

/-! ## Local state helpers -/

section Local

variable {R : ℕ} {u : Fin R → ℕ+}

/-- inverse of `enter` -/
def unenter : LocalState R u → Fin R → Option (LocalState R u)
  | .fcfs l, s => if l.getLast? = some s then some (.fcfs l.dropLast) else none
  | .stages v, s => if 0 < v s ⟨0, (u s).pos⟩ then
      some (.stages (fun r k => if r = s ∧ k.val = 0 then v r k - 1 else v r k)) else none
  | .lcfs [], _ => none
  | .lcfs (x :: rest), s => if x.1 = s ∧ x.2.val = 0 then some (.lcfs rest) else none

lemma enter_unenter (x : LocalState R u) (s : Fin R) : unenter (x.enter s) s = some x := by
  rcases x with l | v | l
  · simp [LocalState.enter, unenter]
  · simp only [LocalState.enter, unenter]
    rw [if_pos (by simp)]
    congr 2
    funext r k
    by_cases h : r = s ∧ k.val = 0
    · rw [if_pos h, if_pos h]; omega
    · rw [if_neg h, if_neg h]
  · simp [LocalState.enter, unenter]

lemma unenter_enter {x y : LocalState R u} {s : Fin R} (h : unenter y s = some x) :
    x.enter s = y := by
  rcases y with l | v | l
  · simp only [unenter] at h
    split_ifs at h with h1
    cases h
    simp only [LocalState.enter]
    rw [List.getLast?_eq_some_iff] at h1
    obtain ⟨ys, rfl⟩ := h1
    simp
  · simp only [unenter] at h
    split_ifs at h with h1
    cases h
    simp only [LocalState.enter]
    congr 1
    funext r k
    by_cases h : r = s ∧ k.val = 0
    · have h0 : 0 < v r k := by
        obtain ⟨rfl, hk⟩ := h
        have : k = ⟨0, (u r).pos⟩ := Fin.ext hk
        subst this; exact h1
      rw [if_pos h, if_pos h]; omega
    · rw [if_neg h, if_neg h]
  · rcases l with _ | ⟨x, rest⟩
    · simp [unenter] at h
    · simp only [unenter] at h
      split_ifs at h with h1
      cases h
      obtain ⟨r, k⟩ := x
      obtain ⟨h1, h2⟩ := h1
      simp only at h1 h2
      subst h1
      have : k = ⟨0, (u r).pos⟩ := Fin.ext h2
      subst this
      rfl

lemma unenter_eq_some_iff {x y : LocalState R u} {s : Fin R} :
    unenter y s = some x ↔ x.enter s = y := by
  constructor
  · exact unenter_enter
  · rintro rfl; exact enter_unenter x s

/-- shape of a local state -/
def kind : LocalState R u → Fin 3
  | .fcfs _ => 0
  | .stages _ => 1
  | .lcfs _ => 2

lemma fits_of_kind {t : CenterType} {x y : LocalState R u} (hk : kind x = kind y)
    (hx : x.Fits t) : y.Fits t := by
  rcases x with l | v | l <;> rcases y with l' | v' | l' <;> cases t <;>
    simp_all [kind, LocalState.Fits]

lemma kind_enter (x : LocalState R u) (s : Fin R) : kind (x.enter s) = kind x := by
  rcases x with l | v | l <;> rfl

lemma kind_unenter {x y : LocalState R u} {s : Fin R} (h : unenter y s = some x) :
    kind x = kind y := by
  rw [← unenter_enter h, kind_enter]

lemma sum_ite_val {n : ℕ} (c : ℕ) (hc : c < n) :
    ∑ k : Fin n, (if k.val = c then (1:ℕ) else 0) = 1 := by
  have h : ∀ k : Fin n, (k.val = c ↔ k = ⟨c, hc⟩) := fun k => by
    constructor
    · intro h; exact Fin.ext h
    · intro h; subst h; rfl
  simp only [h]
  simp

lemma count_enter (x : LocalState R u) (s r : Fin R) :
    (x.enter s).count r = x.count r + if r = s then 1 else 0 := by
  rcases x with l | v | l
  · simp only [LocalState.enter, LocalState.count, List.count_append]
    by_cases h : r = s
    · subst h; simp
    · simp [h, List.count_singleton]; intro h'; exact h h'.symm
  · simp only [LocalState.enter, LocalState.count]
    by_cases h : r = s
    · subst h
      simp only [true_and, if_true]
      rw [← sum_ite_val 0 (u r).pos, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    · simp [h]
  · simp only [LocalState.enter, LocalState.count, List.countP_cons]
    by_cases h : r = s
    · subst h; simp
    · have h' : ¬ s = r := fun h' => h h'.symm
      simp [h, h']

end Local

/-! ## Event sum -/

variable {N R m : ℕ} (net : Network N R m)

lemma ev_sum (g : Network.Event N R net.u → ℝ) :
    ∑ ev, g ev = ∑ j : Fin N, ∑ s : Fin R, g (.arrive j s)
      + ∑ i : Fin N, ∑ d : Option (Fin N × Fin R), g (.fcfsDone i d)
      + ∑ i : Fin N, ∑ r : Fin R, ∑ l : Fin (net.u i r), g (.stageNext i r l)
      + ∑ i : Fin N, ∑ r : Fin R, ∑ l : Fin (net.u i r), ∑ d : Option (Fin N × Fin R),
          g (.stageDone i r l d)
      + ∑ i : Fin N, g (.lcfsNext i)
      + ∑ i : Fin N, ∑ d : Option (Fin N × Fin R), g (.lcfsDone i d) := by
  classical
  let E : ((Fin N × Fin R) ⊕ (Fin N × Option (Fin N × Fin R)) ⊕
      (Σ i : Fin N, Σ r : Fin R, Fin (net.u i r)) ⊕
      ((Σ i : Fin N, Σ r : Fin R, Fin (net.u i r)) × Option (Fin N × Fin R)) ⊕
      Fin N ⊕ (Fin N × Option (Fin N × Fin R))) ≃ Network.Event N R net.u :=
    { toFun := fun
        | .inl (j, s) => .arrive j s
        | .inr (.inl (i, d)) => .fcfsDone i d
        | .inr (.inr (.inl ⟨i, r, l⟩)) => .stageNext i r l
        | .inr (.inr (.inr (.inl (⟨i, r, l⟩, d)))) => .stageDone i r l d
        | .inr (.inr (.inr (.inr (.inl i)))) => .lcfsNext i
        | .inr (.inr (.inr (.inr (.inr (i, d))))) => .lcfsDone i d
      invFun := fun
        | .arrive j s => .inl (j, s)
        | .fcfsDone i d => .inr (.inl (i, d))
        | .stageNext i r l => .inr (.inr (.inl ⟨i, r, l⟩))
        | .stageDone i r l d => .inr (.inr (.inr (.inl (⟨i, r, l⟩, d))))
        | .lcfsNext i => .inr (.inr (.inr (.inr (.inl i))))
        | .lcfsDone i d => .inr (.inr (.inr (.inr (.inr (i, d)))))
      left_inv := by
        intro x
        rcases x with ⟨j, s⟩ | ⟨i, d⟩ | ⟨i, r, l⟩ | ⟨⟨i, r, l⟩, d⟩ | i | ⟨i, d⟩ <;> rfl
      right_inv := by
        intro x
        cases x <;> rfl }
  rw [← Equiv.sum_comp E]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma, add_assoc]
  rfl

/-! ## HasSum over predecessor families -/

lemma hasSum_family {ι : Type*} [Fintype ι] (g : net.Config → ℝ) (T : ι → net.Config)
    (hinj : Function.Injective T)
    (hT : ∀ S' : net.State, g S'.1 ≠ 0 → ∃ p, S'.1 = T p)
    (hfeas : ∀ p, g (T p) ≠ 0 → net.Feasible (T p)) :
    HasSum (fun S' : net.State => g S'.1) (∑ p, g (T p)) := by
  classical
  have hfun : (fun S' : net.State => g S'.1) =
      fun S' => ∑ p, (if S'.1 = T p then g (T p) else 0) := by
    funext S'
    by_cases h : g S'.1 = 0
    · rw [h]; symm; apply Finset.sum_eq_zero; intro p _
      split_ifs with hp
      · rw [← hp, h]
      · rfl
    · obtain ⟨p0, hp0⟩ := hT S' h
      rw [Finset.sum_eq_single p0]
      · simp [hp0]
      · intro p _ hp; rw [if_neg]; intro h'; exact hp (hinj (h'.symm.trans hp0))
      · simp
  rw [hfun]
  apply hasSum_sum
  intro p _
  by_cases hp : net.Feasible (T p)
  · obtain ⟨S0, hS0⟩ : ∃ S0 : net.State, S0.1 = T p := ⟨⟨T p, hp⟩, rfl⟩
    have := hasSum_ite_eq S0 (g (T p))
    have heq : (fun S' : net.State => if S'.1 = T p then g (T p) else 0) =
        (fun b' => if b' = S0 then g (T p) else 0) := by
      funext S'
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (Subtype.ext (h1.trans hS0.symm)) h2
      · exact absurd (by rw [h2, hS0]) h1
      · rfl
    rw [heq]; exact this
  · have h0 : g (T p) = 0 := by by_contra h; exact hp (hfeas p h)
    simp only [h0, ite_self]
    exact hasSum_zero

lemma hasSum_zero_of (g : net.Config → ℝ) (h : ∀ S' : net.State, g S'.1 = 0) :
    HasSum (fun S' : net.State => g S'.1) 0 := by
  have : (fun S' : net.State => g S'.1) = fun _ => 0 := funext h
  rw [this]; exact hasSum_zero

lemma hasSum_one (g : net.Config → ℝ) (T : net.Config)
    (hT : ∀ S' : net.State, g S'.1 ≠ 0 → S'.1 = T)
    (hfeas : g T ≠ 0 → net.Feasible T) :
    HasSum (fun S' : net.State => g S'.1) (g T) := by
  have := hasSum_family net g (fun _ : Unit => T) (fun a b _ => rfl)
    (fun S' h => ⟨(), hT S' h⟩) (fun _ h => hfeas h)
  simpa using this

/-! ## Un-routing -/

def unroute (S : net.Config) : Option (Fin N × Fin R) → Option net.Config
  | none => some S
  | some (j, s) => (unenter (S j) s).map (fun y => Function.update S j y)

lemma routeTo_eq_iff (T S : net.Config) (d : Option (Fin N × Fin R)) :
    net.routeTo T d = S ↔ unroute net S d = some T := by
  rcases d with _ | ⟨j, s⟩
  · simp only [Network.routeTo, unroute, Option.some.injEq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  · simp only [Network.routeTo, unroute, Network.enterAt, Option.map_eq_some_iff]
    constructor
    · rintro rfl
      refine ⟨T j, ?_, ?_⟩
      · simp [enter_unenter]
      · simp
    · rintro ⟨y, hy, rfl⟩
      rw [unenter_eq_some_iff] at hy
      simp [hy]

lemma unroute_kind {S T : net.Config} {d : Option (Fin N × Fin R)}
    (h : unroute net S d = some T) (i : Fin N) : kind (T i) = kind (S i) := by
  rcases d with _ | ⟨j, s⟩
  · simp only [unroute, Option.some.injEq] at h; subst h; rfl
  · simp only [unroute, Option.map_eq_some_iff] at h
    obtain ⟨y, hy, rfl⟩ := h
    by_cases hij : i = j
    · subst hij; simp [kind_unenter hy]
    · simp [Function.update_of_ne hij]

/-! ## Populations -/

lemma chainPop_update (T : net.Config) (i0 : Fin N) (x : LocalState R (net.u i0)) (r0 : Fin R)
    (hc : ∀ r, x.count r = (T i0).count r + if r = r0 then 1 else 0) (k : Fin m) :
    net.chainPop (Function.update T i0 x) k = net.chainPop T k +
      if net.chain i0 r0 = k then 1 else 0 := by
  classical
  unfold Network.chainPop
  rw [Fintype.sum_eq_add_sum_compl i0, Fintype.sum_eq_add_sum_compl i0 (f := fun i => _)]
  have hrest : ∑ i ∈ ({i0}ᶜ : Finset (Fin N)), (∑ r, if net.chain i r = k then
      (Function.update T i0 x i).count r else 0) =
      ∑ i ∈ ({i0}ᶜ : Finset (Fin N)), (∑ r, if net.chain i r = k then (T i).count r else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    have : i ≠ i0 := by simpa using hi
    simp [Function.update_of_ne this]
  rw [hrest, Function.update_self]
  have h1 : ∀ r, (if net.chain i0 r = k then x.count r else 0) =
      (if net.chain i0 r = k then (T i0).count r else 0) +
        (if r = r0 then (if net.chain i0 r0 = k then 1 else 0) else 0) := by
    intro r; rw [hc r]
    by_cases h1 : r = r0
    · subst h1; split_ifs <;> simp
    · simp [h1]
  simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma totalPop_update (T : net.Config) (i0 : Fin N) (x : LocalState R (net.u i0)) (r0 : Fin R)
    (hc : ∀ r, x.count r = (T i0).count r + if r = r0 then 1 else 0) :
    net.totalPop (Function.update T i0 x) = net.totalPop T + 1 := by
  classical
  unfold Network.totalPop
  rw [Fintype.sum_eq_add_sum_compl i0, Fintype.sum_eq_add_sum_compl i0 (f := fun i => _)]
  have hrest : ∑ i ∈ ({i0}ᶜ : Finset (Fin N)), (Function.update T i0 x i).total =
      ∑ i ∈ ({i0}ᶜ : Finset (Fin N)), (T i).total := by
    apply Finset.sum_congr rfl
    intro i hi
    have : i ≠ i0 := by simpa using hi
    simp [Function.update_of_ne this]
  rw [hrest, Function.update_self]
  simp only [LocalState.total, hc, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  ring

/-! ## Product form on configurations, feasibility of predecessors -/

noncomputable def pc (e : Fin N → Fin R → ℝ) (T : net.Config) : ℝ :=
  net.d T * ∏ i, net.f e i (T i)

lemma chainPop_congr (T T' : net.Config) (h : ∀ i r, (T i).count r = (T' i).count r)
    (k : Fin m) : net.chainPop T k = net.chainPop T' k := by
  unfold Network.chainPop; simp only [h]

lemma count_update_same (T : net.Config) (i0 : Fin N) (x : LocalState R (net.u i0))
    (hc : ∀ r, x.count r = (T i0).count r) (i : Fin N) (r : Fin R) :
    (Function.update T i0 x i).count r = (T i).count r := by
  by_cases h : i = i0
  · subst h; simp [hc]
  · simp [Function.update_of_ne h]

lemma feasible_of (S : net.State) (T : net.Config) (hk : ∀ i, kind (T i) = kind (S.1 i))
    (hp : ∀ k, net.IsClosedChain k → net.chainPop T k = net.chainPop S.1 k) :
    net.Feasible T :=
  ⟨fun i => fits_of_kind (hk i).symm (S.2.1 i), fun k hk' => (hp k hk').trans (S.2.2 k hk')⟩

lemma routeProb_none_ne (hnet : net.IsValid) (i : Fin N) (r : Fin R)
    (h : net.routeProb i r none ≠ 0) : ¬ net.IsClosedChain (net.chain i r) := fun hc =>
  h (by simp [Network.routeProb, hnet.P_row_closed i r hc])

lemma routeProb_some_chain (hnet : net.IsValid) (i : Fin N) (r : Fin R) (j : Fin N) (s : Fin R)
    (h : net.routeProb i r (some (j, s)) ≠ 0) : net.chain i r = net.chain j s :=
  hnet.P_chain i r j s h

lemma feas_pred (hnet : net.IsValid) (S : net.State) (B : net.Config)
    (d : Option (Fin N × Fin R))
    (hB : unroute net S.1 d = some B) (i : Fin N) (x : LocalState R (net.u i)) (r0 : Fin R)
    (hk : kind x = kind (B i)) (hc : ∀ r, x.count r = (B i).count r + if r = r0 then 1 else 0)
    (hp : net.routeProb i r0 d ≠ 0) : net.Feasible (Function.update B i x) := by
  apply feasible_of net S
  · intro i'
    by_cases h : i' = i
    · subst h; rw [Function.update_self, hk, unroute_kind net hB]
    · rw [Function.update_of_ne h, unroute_kind net hB]
  · intro k hk'
    rw [chainPop_update net B i x r0 hc k]
    rcases d with _ | ⟨j, s⟩
    · simp only [unroute, Option.some.injEq] at hB
      subst hB
      have : net.chain i r0 ≠ k := by
        intro h; subst h; exact routeProb_none_ne net hnet i r0 hp hk'
      simp [this]
    · have hS : S.1 = net.routeTo B (some (j, s)) :=
        ((routeTo_eq_iff net B S.1 _).mpr hB).symm
      rw [hS]
      simp only [Network.routeTo, Network.enterAt]
      rw [chainPop_update net B j _ s (count_enter (B j) s) k,
        routeProb_some_chain net hnet i r0 j s hp]

lemma q_ne_open (j : Fin N) (s : Fin R) (h : net.q j s ≠ 0) :
    ¬ net.IsClosedChain (net.chain j s) := fun hc => h (hc j s rfl)

lemma arrivalRate_q (T : net.Config) (j : Fin N) (s : Fin R) (h : net.arrivalRate T j s ≠ 0) :
    net.q j s ≠ 0 := by
  intro hq; apply h; unfold Network.arrivalRate; split <;> simp [hq]

lemma feas_arrive (S : net.State) (B : net.Config) (j : Fin N) (s : Fin R)
    (hB : unroute net S.1 (some (j, s)) = some B) (hq : net.q j s ≠ 0) : net.Feasible B := by
  apply feasible_of net S
  · intro i'; exact unroute_kind net hB i'
  · intro k hk'
    have hS : S.1 = net.routeTo B (some (j, s)) := ((routeTo_eq_iff net B S.1 _).mpr hB).symm
    rw [hS]; simp only [Network.routeTo, Network.enterAt]
    rw [chainPop_update net B j _ s (count_enter (B j) s) k]
    have : net.chain j s ≠ k := by intro h; subst h; exact q_ne_open net j s hq hk'
    simp [this]

lemma feas_same (S : net.State) (i : Fin N) (x : LocalState R (net.u i))
    (hk : kind x = kind (S.1 i)) (hc : ∀ r, x.count r = (S.1 i).count r) :
    net.Feasible (Function.update S.1 i x) := by
  apply feasible_of net S
  · intro i'
    by_cases h : i' = i
    · subst h; simp [hk]
    · simp [Function.update_of_ne h]
  · intro k _; exact chainPop_congr net _ _ (count_update_same net S.1 i x hc) k

/-! ## Inflow, event by event -/

open Classical in
lemma in_arrive (e : Fin N → Fin R → ℝ) (S : net.State) (L : Label N R m) (j : Fin N)
    (s : Fin R) :
    HasSum (fun S' : net.State => pc net e S'.1 *
        (if net.evTarget S'.1 (.arrive j s) = S.1 ∧ net.enterLabel S'.1 (.arrive j s) = L
          then net.evRate S'.1 (.arrive j s) else 0))
      ((unroute net S.1 (some (j, s))).elim 0 (fun B =>
        pc net e B * (if net.entryLabel j s = L then net.arrivalRate B j s else 0))) := by
  set g : net.Config → ℝ := fun T => pc net e T * (if net.evTarget T (.arrive j s) = S.1 ∧
      net.enterLabel T (.arrive j s) = L then net.evRate T (.arrive j s) else 0) with hg
  have inv : ∀ T : net.Config, g T ≠ 0 → unroute net S.1 (some (j, s)) = some T := by
    intro T h
    have h1 : net.evTarget T (.arrive j s) = S.1 := by
      by_contra hc; apply h; simp [hg, hc]
    exact (routeTo_eq_iff net T S.1 _).mp h1
  rcases hB : unroute net S.1 (some (j, s)) with _ | B
  · simp only [Option.elim_none]
    apply hasSum_zero_of net g
    intro S'
    by_contra h
    have := inv _ h; rw [hB] at this; cases this
  · simp only [Option.elim_some]
    have := hasSum_one net g B ?_ ?_
    · convert this using 1
      have h1 : net.evTarget B (.arrive j s) = S.1 := (routeTo_eq_iff net B S.1 _).mpr hB
      simp only [hg, h1, true_and, Network.enterLabel, Network.evRate]
    · intro S' h
      have := inv _ h; rw [hB] at this; exact (Option.some.inj this).symm
    · intro h
      apply feas_arrive net S B j s hB
      apply arrivalRate_q net B j s
      intro h0; apply h
      simp [hg, Network.evRate, h0]

open Classical in
lemma in_fcfsDone (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (S : net.State)
    (L : Label N R m) (i : Fin N) (d : Option (Fin N × Fin R)) :
    HasSum (fun S' : net.State => pc net e S'.1 *
        (if net.evTarget S'.1 (.fcfsDone i d) = S.1 ∧ net.enterLabel S'.1 (.fcfsDone i d) = L
          then net.evRate S'.1 (.fcfsDone i d) else 0))
      ((unroute net S.1 d).elim 0 (fun B => match B i with
        | .fcfs rest => ∑ r : Fin R, pc net e (Function.update B i (.fcfs (r :: rest))) *
            (if net.destLabel i r d = L then net.μ i * net.routeProb i r d else 0)
        | _ => 0)) := by
  set g : net.Config → ℝ := fun T => pc net e T * (if net.evTarget T (.fcfsDone i d) = S.1 ∧
      net.enterLabel T (.fcfsDone i d) = L then net.evRate T (.fcfsDone i d) else 0) with hg
  have inv : ∀ T : net.Config, g T ≠ 0 → ∃ r rest, T i = .fcfs (r :: rest) ∧
      unroute net S.1 d = some (Function.update T i (.fcfs rest)) := by
    intro T h
    rcases hx : T i with l | v | l
    · rcases l with _ | ⟨r, rest⟩
      · exfalso; apply h; simp [hg, Network.evRate, hx]
      · refine ⟨r, rest, rfl, ?_⟩
        have h1 : net.evTarget T (.fcfsDone i d) = S.1 := by
          by_contra hc; apply h; simp [hg, hc]
        simp only [Network.evTarget, hx] at h1
        exact (routeTo_eq_iff net _ _ _).mp h1
    · exfalso; apply h; simp [hg, Network.evRate, hx]
    · exfalso; apply h; simp [hg, Network.evRate, hx]
  rcases hB : unroute net S.1 d with _ | B
  · simp only [Option.elim_none]
    apply hasSum_zero_of net g
    intro S'
    by_contra h
    obtain ⟨r, rest, -, h2⟩ := inv _ h
    rw [hB] at h2; cases h2
  · simp only [Option.elim_some]
    rcases hBi : B i with rest | v | l
    · have hinj : Function.Injective
          (fun r : Fin R => Function.update B i (LocalState.fcfs (r :: rest))) := by
        intro r1 r2 h
        have := congrFun h i
        simpa using this
      have := hasSum_family net g (fun r => Function.update B i (.fcfs (r :: rest))) hinj ?_ ?_
      · convert this using 1
        apply Finset.sum_congr rfl
        intro r _
        have h1 : net.evTarget (Function.update B i (.fcfs (r :: rest))) (.fcfsDone i d) = S.1 := by
          simp only [Network.evTarget, Function.update_self, Function.update_idem]
          rw [← hBi, Function.update_eq_self]
          exact (routeTo_eq_iff net _ _ _).mpr hB
        simp only [hg, h1, true_and, Network.enterLabel, Network.evRate, Function.update_self]
      · intro S' h
        obtain ⟨r, rest', hx, h2⟩ := inv _ h
        rw [hB] at h2
        have h3 := Option.some.inj h2
        have : rest' = rest := by
          have := congrFun h3 i
          rw [Function.update_self, hBi] at this
          injection this with h; exact h.symm
        subst this
        refine ⟨r, ?_⟩
        rw [h3, Function.update_idem, ← hx, Function.update_eq_self]
      · intro r h
        apply feas_pred net hnet S B d hB i _ r
        · rw [hBi]; rfl
        · intro r'; rw [hBi]; simp only [LocalState.count, List.count_cons]
          by_cases hr : r' = r
          · subst hr; simp
          · simp [hr, Ne.symm hr]
        · intro h0; apply h; simp [hg, Network.evRate, h0]
    all_goals
      apply hasSum_zero_of net g
      intro S'
      by_contra h
      obtain ⟨r, rest', -, h2⟩ := inv _ h
      rw [hB] at h2
      have := congrFun (Option.some.inj h2) i
      rw [Function.update_self, hBi] at this
      cases this

section Local2

variable {R : ℕ} {u : Fin R → ℕ+}

def addSt (v : (r : Fin R) → Fin (u r) → ℕ) (r : Fin R) (l : Fin (u r)) :
    (r : Fin R) → Fin (u r) → ℕ :=
  fun r' k => if r' = r ∧ k.val = l.val then v r' k + 1 else v r' k

def subSt (v : (r : Fin R) → Fin (u r) → ℕ) (r : Fin R) (l : Fin (u r)) :
    (r : Fin R) → Fin (u r) → ℕ :=
  fun r' k => if r' = r ∧ k.val = l.val then v r' k - 1 else v r' k

lemma at_of {v : (r : Fin R) → Fin (u r) → ℕ} {r r' : Fin R} {l : Fin (u r)} {k : Fin (u r')}
    (h : r' = r ∧ k.val = l.val) : v r' k = v r l := by
  obtain ⟨rfl, hk⟩ := h; rw [Fin.ext hk]

lemma addSt_subSt (v : (r : Fin R) → Fin (u r) → ℕ) (r : Fin R) (l : Fin (u r))
    (h : 0 < v r l) : addSt (subSt v r l) r l = v := by
  funext r' k
  simp only [addSt, subSt]
  by_cases hc : r' = r ∧ k.val = l.val
  · rw [if_pos hc, if_pos hc]; have := at_of (v := v) hc; omega
  · rw [if_neg hc, if_neg hc]

lemma subSt_addSt (v : (r : Fin R) → Fin (u r) → ℕ) (r : Fin R) (l : Fin (u r)) :
    subSt (addSt v r l) r l = v := by
  funext r' k
  simp only [addSt, subSt]
  by_cases hc : r' = r ∧ k.val = l.val
  · rw [if_pos hc, if_pos hc]; omega
  · rw [if_neg hc, if_neg hc]

lemma addSt_self (v : (r : Fin R) → Fin (u r) → ℕ) (r : Fin R) (l : Fin (u r)) :
    addSt v r l r l = v r l + 1 := by simp [addSt]

lemma addSt_ne (v : (r : Fin R) → Fin (u r) → ℕ) (r r' : Fin R) (l : Fin (u r)) (k : Fin (u r'))
    (h : ¬ (r' = r ∧ k.val = l.val)) : addSt v r l r' k = v r' k := by simp [addSt, h]

lemma sum_bump {n : ℕ} (f : Fin n → ℕ) (c : ℕ) (hc : c < n) :
    ∑ k : Fin n, (if k.val = c then f k + 1 else f k) = ∑ k, f k + 1 := by
  have : ∀ k : Fin n, (if k.val = c then f k + 1 else f k) = f k + (if k.val = c then 1 else 0) := by
    intro k; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_add_distrib, sum_ite_val c hc]

lemma count_addSt (v : (r : Fin R) → Fin (u r) → ℕ) (r : Fin R) (l : Fin (u r)) (r' : Fin R) :
    (LocalState.stages (u := u) (addSt v r l)).count r' =
      (LocalState.stages (u := u) v).count r' + if r' = r then 1 else 0 := by
  simp only [LocalState.count, addSt]
  by_cases h : r' = r
  · subst h
    simp only [true_and, if_true]
    exact sum_bump _ l.val l.isLt
  · simp [h]

lemma count_subSt (v : (r : Fin R) → Fin (u r) → ℕ) (r : Fin R) (l : Fin (u r)) (h : 0 < v r l)
    (r' : Fin R) :
    (LocalState.stages (u := u) v).count r' =
      (LocalState.stages (u := u) (subSt v r l)).count r' + if r' = r then 1 else 0 := by
  rw [← count_addSt, addSt_subSt v r l h]

def predFin {n : ℕ} (k : Fin n) : Fin n := ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩

end Local2

lemma stageRate_pos {i : Fin N} {r : Fin R} {l : Fin (net.u i r)}
    {v : (r : Fin R) → Fin (net.u i r) → ℕ} {n : ℕ} (h : net.stageRate i r l v n ≠ 0) :
    0 < v r l := by
  by_contra h0
  have h1 : v r l = 0 := by omega
  apply h; unfold Network.stageRate; split <;> simp [h1]

open Classical in
lemma in_stageDone (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (S : net.State)
    (L : Label N R m) (i : Fin N) (r : Fin R) (l : Fin (net.u i r))
    (d : Option (Fin N × Fin R)) :
    HasSum (fun S' : net.State => pc net e S'.1 *
        (if net.evTarget S'.1 (.stageDone i r l d) = S.1 ∧
            net.enterLabel S'.1 (.stageDone i r l d) = L
          then net.evRate S'.1 (.stageDone i r l d) else 0))
      ((unroute net S.1 d).elim 0 (fun B => match B i with
        | .stages w => pc net e (Function.update B i (.stages (addSt w r l))) *
            (if net.destLabel i r d = L then
              net.stageRate i r l (addSt w r l) (LocalState.stages (addSt w r l)).total *
                (1 - net.a i r l) * net.routeProb i r d else 0)
        | _ => 0)) := by
  set g : net.Config → ℝ := fun T => pc net e T *
      (if net.evTarget T (.stageDone i r l d) = S.1 ∧ net.enterLabel T (.stageDone i r l d) = L
        then net.evRate T (.stageDone i r l d) else 0) with hg
  have inv : ∀ T : net.Config, g T ≠ 0 → ∃ v, T i = .stages v ∧ 0 < v r l ∧
      unroute net S.1 d = some (Function.update T i (.stages (subSt v r l))) := by
    intro T h
    rcases hx : T i with l' | v | l'
    · exfalso; apply h; simp [hg, Network.evRate, hx]
    · refine ⟨v, rfl, ?_, ?_⟩
      · apply stageRate_pos net (n := (LocalState.stages (u := net.u i) v).total)
        intro h0; apply h; simp [hg, Network.evRate, hx, h0]
      · have h1 : net.evTarget T (.stageDone i r l d) = S.1 := by
          by_contra hc; apply h; simp [hg, hc]
        simp only [Network.evTarget, hx] at h1
        exact (routeTo_eq_iff net _ _ _).mp h1
    · exfalso; apply h; simp [hg, Network.evRate, hx]
  rcases hB : unroute net S.1 d with _ | B
  · simp only [Option.elim_none]
    apply hasSum_zero_of net g
    intro S'
    by_contra h
    obtain ⟨v, -, -, h2⟩ := inv _ h
    rw [hB] at h2; cases h2
  · simp only [Option.elim_some]
    rcases hBi : B i with rest | w | l'
    · apply hasSum_zero_of net g
      intro S'
      by_contra h
      obtain ⟨v, -, -, h2⟩ := inv _ h
      rw [hB] at h2
      have := congrFun (Option.some.inj h2) i
      rw [Function.update_self, hBi] at this
      cases this
    · have := hasSum_one net g (Function.update B i (.stages (addSt w r l))) ?_ ?_
      · convert this using 1
        have h1 : net.evTarget (Function.update B i (.stages (addSt w r l)))
            (.stageDone i r l d) = S.1 := by
          simp only [Network.evTarget, Function.update_self, Function.update_idem]
          have : subSt (addSt w r l) r l = w := subSt_addSt w r l
          unfold subSt at this
          rw [this, ← hBi, Function.update_eq_self]
          exact (routeTo_eq_iff net _ _ _).mpr hB
        simp only [hg, h1, true_and, Network.enterLabel, Network.evRate, Function.update_self]
      · intro S' h
        obtain ⟨v, hx, hv, h2⟩ := inv _ h
        rw [hB] at h2
        have h3 := Option.some.inj h2
        have : w = subSt v r l := by
          have := congrFun h3 i
          rw [Function.update_self, hBi] at this
          injection this
        subst this
        rw [h3, Function.update_idem, addSt_subSt v r l hv, ← hx, Function.update_eq_self]
      · intro h
        apply feas_pred net hnet S B d hB i _ r
        · rw [hBi]; rfl
        · intro r'; rw [hBi]; exact count_addSt w r l r'
        · intro h0; apply h; simp [hg, Network.evRate, h0]
    · apply hasSum_zero_of net g
      intro S'
      by_contra h
      obtain ⟨v, -, -, h2⟩ := inv _ h
      rw [hB] at h2
      have := congrFun (Option.some.inj h2) i
      rw [Function.update_self, hBi] at this
      cases this

open Classical in
lemma in_lcfsDone (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (S : net.State)
    (L : Label N R m) (i : Fin N) (d : Option (Fin N × Fin R)) :
    HasSum (fun S' : net.State => pc net e S'.1 *
        (if net.evTarget S'.1 (.lcfsDone i d) = S.1 ∧ net.enterLabel S'.1 (.lcfsDone i d) = L
          then net.evRate S'.1 (.lcfsDone i d) else 0))
      ((unroute net S.1 d).elim 0 (fun B => match B i with
        | .lcfs rest => ∑ x : (Σ r : Fin R, Fin (net.u i r)),
            pc net e (Function.update B i (.lcfs (x :: rest))) *
            (if net.destLabel i x.1 d = L then
              net.μs i x.1 x.2 * (1 - net.a i x.1 x.2) * net.routeProb i x.1 d else 0)
        | _ => 0)) := by
  set g : net.Config → ℝ := fun T => pc net e T * (if net.evTarget T (.lcfsDone i d) = S.1 ∧
      net.enterLabel T (.lcfsDone i d) = L then net.evRate T (.lcfsDone i d) else 0) with hg
  have inv : ∀ T : net.Config, g T ≠ 0 → ∃ x rest, T i = .lcfs (x :: rest) ∧
      unroute net S.1 d = some (Function.update T i (.lcfs rest)) := by
    intro T h
    rcases hx : T i with l | v | l
    · exfalso; apply h; simp [hg, Network.evRate, hx]
    · exfalso; apply h; simp [hg, Network.evRate, hx]
    · rcases l with _ | ⟨x, rest⟩
      · exfalso; apply h; simp [hg, Network.evRate, hx]
      · refine ⟨x, rest, rfl, ?_⟩
        have h1 : net.evTarget T (.lcfsDone i d) = S.1 := by
          by_contra hc; apply h; simp [hg, hc]
        simp only [Network.evTarget, hx] at h1
        exact (routeTo_eq_iff net _ _ _).mp h1
  rcases hB : unroute net S.1 d with _ | B
  · simp only [Option.elim_none]
    apply hasSum_zero_of net g
    intro S'
    by_contra h
    obtain ⟨x, rest, -, h2⟩ := inv _ h
    rw [hB] at h2; cases h2
  · simp only [Option.elim_some]
    rcases hBi : B i with l | v | rest
    rotate_left 2
    · have hinj : Function.Injective
          (fun x : (Σ r : Fin R, Fin (net.u i r)) =>
            Function.update B i (LocalState.lcfs (x :: rest))) := by
        intro x1 x2 h
        have := congrFun h i
        simpa using this
      have := hasSum_family net g
        (fun x => Function.update B i (.lcfs (x :: rest))) hinj ?_ ?_
      · convert this using 1
        apply Finset.sum_congr rfl
        intro x _
        have h1 : net.evTarget (Function.update B i (.lcfs (x :: rest))) (.lcfsDone i d)
            = S.1 := by
          simp only [Network.evTarget, Function.update_self, Function.update_idem]
          rw [← hBi, Function.update_eq_self]
          exact (routeTo_eq_iff net _ _ _).mpr hB
        simp only [hg, h1, true_and, Network.enterLabel, Network.evRate, Function.update_self]
      · intro S' h
        obtain ⟨x, rest', hx, h2⟩ := inv _ h
        rw [hB] at h2
        have h3 := Option.some.inj h2
        have : rest' = rest := by
          have := congrFun h3 i
          rw [Function.update_self, hBi] at this
          injection this with h; exact h.symm
        subst this
        refine ⟨x, ?_⟩
        rw [h3, Function.update_idem, ← hx, Function.update_eq_self]
      · intro x h
        apply feas_pred net hnet S B d hB i _ x.1
        · rw [hBi]; rfl
        · intro r'; rw [hBi]; simp only [LocalState.count, List.countP_cons]
          by_cases hr : r' = x.1
          · subst hr; simp
          · simp [hr, Ne.symm hr]
        · intro h0; apply h; simp [hg, Network.evRate, h0]
    all_goals
      apply hasSum_zero_of net g
      intro S'
      by_contra h
      obtain ⟨x, rest', -, h2⟩ := inv _ h
      rw [hB] at h2
      have := congrFun (Option.some.inj h2) i
      rw [Function.update_self, hBi] at this
      cases this

section Local3

variable {R : ℕ} {u : Fin R → ℕ+}

lemma mv_eq (v : (r : Fin R) → Fin (u r) → ℕ) (r : Fin R) (l : Fin (u r))
    (h : l.val + 1 < (u r : ℕ)) :
    (fun r' (k : Fin (u r')) => if r' = r ∧ k.val = l.val then v r' k - 1
      else if r' = r ∧ k.val = l.val + 1 then v r' k + 1 else v r' k) =
      addSt (subSt v r l) r ⟨l.val + 1, h⟩ := by
  funext r' k
  simp only [addSt, subSt]
  by_cases hr : r' = r
  · subst hr
    simp only [true_and]
    split_ifs <;> omega
  · simp [hr]

lemma sig_pred (y : Σ r : Fin R, Fin (u r)) (h : (predFin y.2).val + 1 < (u y.1 : ℕ))
    (hy : 0 < y.2.val) :
    (⟨y.1, ⟨(predFin y.2).val + 1, h⟩⟩ : Σ r : Fin R, Fin (u r)) = y := by
  obtain ⟨r, k⟩ := y
  exact Sigma.ext rfl (heq_of_eq (Fin.ext (by dsimp only at hy ⊢; simp only [predFin]; omega)))

end Local3

open Classical in
lemma in_stageNext (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (S : net.State)
    (L : Label N R m) (i : Fin N) (r : Fin R) (l : Fin (net.u i r)) :
    HasSum (fun S' : net.State => pc net e S'.1 *
        (if net.evTarget S'.1 (.stageNext i r l) = S.1 ∧
            net.enterLabel S'.1 (.stageNext i r l) = L
          then net.evRate S'.1 (.stageNext i r l) else 0))
      (match S.1 i with
        | .stages w => if h : l.val + 1 < (net.u i r : ℕ) then
            (if 0 < w r ⟨l.val + 1, h⟩ then
              pc net e (Function.update S.1 i (.stages (addSt (subSt w r ⟨l.val + 1, h⟩) r l))) *
                (if Label.stage i r (l.val + 1) = L then
                  net.stageRate i r l (addSt (subSt w r ⟨l.val + 1, h⟩) r l)
                    (LocalState.stages (addSt (subSt w r ⟨l.val + 1, h⟩) r l)).total *
                      net.a i r l
                 else 0)
             else 0)
          else 0
        | _ => 0) := by
  set g : net.Config → ℝ := fun T => pc net e T *
      (if net.evTarget T (.stageNext i r l) = S.1 ∧ net.enterLabel T (.stageNext i r l) = L
        then net.evRate T (.stageNext i r l) else 0) with hg
  have inv : ∀ T : net.Config, g T ≠ 0 → ∃ v, ∃ h : l.val + 1 < (net.u i r : ℕ),
      T i = .stages v ∧ 0 < v r l ∧
      S.1 = Function.update T i (.stages (addSt (subSt v r l) r ⟨l.val + 1, h⟩)) := by
    intro T hT
    rcases hx : T i with l' | v | l'
    · exfalso; apply hT; simp [hg, Network.evRate, hx]
    · have hv : 0 < v r l := by
        apply stageRate_pos net (n := (LocalState.stages (u := net.u i) v).total)
        intro h0; apply hT; simp [hg, Network.evRate, hx, h0]
      have h : l.val + 1 < (net.u i r : ℕ) := by
        by_contra hc
        have ha : net.a i r l = 0 := hnet.a_last i r l (by have := l.isLt; omega)
        apply hT; simp [hg, Network.evRate, hx, ha]
      refine ⟨v, h, rfl, hv, ?_⟩
      have h1 : net.evTarget T (.stageNext i r l) = S.1 := by
        by_contra hc; apply hT; simp [hg, hc]
      simp only [Network.evTarget, hx, if_pos h] at h1
      rw [← h1, mv_eq v r l h]
    · exfalso; apply hT; simp [hg, Network.evRate, hx]
  have hzero : (∀ T : net.Config, g T ≠ 0 → False) →
      HasSum (fun S' : net.State => g S'.1) 0 := fun H =>
    hasSum_zero_of net g (fun S' => by by_contra h; exact H _ h)
  rcases hSi : S.1 i with l' | w | l'
  · apply hzero; intro T hT
    obtain ⟨v, h, -, -, h2⟩ := inv T hT
    have := congrFun h2 i; rw [Function.update_self, hSi] at this; cases this
  · simp only []
    by_cases h : l.val + 1 < (net.u i r : ℕ)
    · rw [dif_pos h]
      by_cases hw : 0 < w r ⟨l.val + 1, h⟩
      · rw [if_pos hw]
        have := hasSum_one net g
          (Function.update S.1 i (.stages (addSt (subSt w r ⟨l.val + 1, h⟩) r l))) ?_ ?_
        · convert this using 1
          have h1 : net.evTarget (Function.update S.1 i
              (.stages (addSt (subSt w r ⟨l.val + 1, h⟩) r l))) (.stageNext i r l) = S.1 := by
            simp only [Network.evTarget, Function.update_self, Function.update_idem, if_pos h]
            rw [mv_eq _ r l h, subSt_addSt, addSt_subSt w r _ hw, ← hSi, Function.update_eq_self]
          simp only [hg, h1, true_and, Network.enterLabel, Network.evRate, Function.update_self]
        · intro S' hS'
          obtain ⟨v, h', hx, hv, h2⟩ := inv _ hS'
          have hw' : w = addSt (subSt v r l) r ⟨l.val + 1, h⟩ := by
            have := congrFun h2 i
            rw [Function.update_self, hSi] at this
            injection this
          subst hw'
          rw [subSt_addSt, addSt_subSt v r l hv, ← hx, h2, Function.update_idem,
            Function.update_eq_self]
        · intro _
          apply feas_same net S i
          · rw [hSi]; rfl
          · intro r'; rw [hSi]
            rw [count_addSt, count_subSt w r ⟨l.val + 1, h⟩ hw r']
      · rw [if_neg hw]
        apply hzero; intro T hT
        obtain ⟨v, h', -, hv, h2⟩ := inv T hT
        have := congrFun h2 i; rw [Function.update_self, hSi] at this
        injection this with hw'
        apply hw; rw [hw']
        simp [addSt]
    · rw [dif_neg h]
      apply hzero; intro T hT
      obtain ⟨v, h', -⟩ := inv T hT
      exact h h'
  · apply hzero; intro T hT
    obtain ⟨v, h, -, -, h2⟩ := inv T hT
    have := congrFun h2 i; rw [Function.update_self, hSi] at this; cases this

open Classical in
lemma in_lcfsNext (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (S : net.State)
    (L : Label N R m) (i : Fin N) :
    HasSum (fun S' : net.State => pc net e S'.1 *
        (if net.evTarget S'.1 (.lcfsNext i) = S.1 ∧ net.enterLabel S'.1 (.lcfsNext i) = L
          then net.evRate S'.1 (.lcfsNext i) else 0))
      (match S.1 i with
        | .lcfs (y :: rest) => if 0 < y.2.val then
            pc net e (Function.update S.1 i (.lcfs (⟨y.1, predFin y.2⟩ :: rest))) *
              (if Label.stage i y.1 y.2.val = L then
                net.μs i y.1 (predFin y.2) * net.a i y.1 (predFin y.2) else 0)
            else 0
        | _ => 0) := by
  set g : net.Config → ℝ := fun T => pc net e T *
      (if net.evTarget T (.lcfsNext i) = S.1 ∧ net.enterLabel T (.lcfsNext i) = L
        then net.evRate T (.lcfsNext i) else 0) with hg
  have inv : ∀ T : net.Config, g T ≠ 0 → ∃ x rest, ∃ h : x.2.val + 1 < (net.u i x.1 : ℕ),
      T i = .lcfs (x :: rest) ∧
      S.1 = Function.update T i (.lcfs (⟨x.1, ⟨x.2.val + 1, h⟩⟩ :: rest)) := by
    intro T hT
    rcases hx : T i with l' | v | l'
    · exfalso; apply hT; simp [hg, Network.evRate, hx]
    · exfalso; apply hT; simp [hg, Network.evRate, hx]
    · rcases l' with _ | ⟨x, rest⟩
      · exfalso; apply hT; simp [hg, Network.evRate, hx]
      · have h : x.2.val + 1 < (net.u i x.1 : ℕ) := by
          by_contra hc
          have ha : net.a i x.1 x.2 = 0 := hnet.a_last i x.1 x.2 (by have := x.2.isLt; omega)
          apply hT; simp [hg, Network.evRate, hx, ha]
        refine ⟨x, rest, h, rfl, ?_⟩
        have h1 : net.evTarget T (.lcfsNext i) = S.1 := by
          by_contra hc; apply hT; simp [hg, hc]
        simp only [Network.evTarget, hx, dif_pos h] at h1
        exact h1.symm
  have hzero : (∀ T : net.Config, g T ≠ 0 → False) →
      HasSum (fun S' : net.State => g S'.1) 0 := fun H =>
    hasSum_zero_of net g (fun S' => by by_contra h; exact H _ h)
  rcases hSi : S.1 i with l' | v | l'
  · apply hzero; intro T hT
    obtain ⟨x, rest, h, -, h2⟩ := inv T hT
    have := congrFun h2 i; rw [Function.update_self, hSi] at this; cases this
  · apply hzero; intro T hT
    obtain ⟨x, rest, h, -, h2⟩ := inv T hT
    have := congrFun h2 i; rw [Function.update_self, hSi] at this; cases this
  · rcases l' with _ | ⟨y, rest⟩
    · apply hzero; intro T hT
      obtain ⟨x, rest, h, -, h2⟩ := inv T hT
      have := congrFun h2 i; rw [Function.update_self, hSi] at this; cases this
    · simp only []
      by_cases hy : 0 < y.2.val
      · rw [if_pos hy]
        have hlt : (predFin y.2).val + 1 < (net.u i y.1 : ℕ) := by
          simp only [predFin]; have := y.2.isLt; omega
        have hv : (predFin y.2).val + 1 = y.2.val := by simp only [predFin]; omega
        have := hasSum_one net g
          (Function.update S.1 i (.lcfs (⟨y.1, predFin y.2⟩ :: rest))) ?_ ?_
        · convert this using 1
          have h1 : net.evTarget (Function.update S.1 i (.lcfs (⟨y.1, predFin y.2⟩ :: rest)))
              (.lcfsNext i) = S.1 := by
            simp only [Network.evTarget, Function.update_self, Function.update_idem]
            rw [dif_pos hlt, sig_pred y hlt hy, ← hSi, Function.update_eq_self]
          simp only [hg, h1, true_and, Network.enterLabel, Network.evRate, Function.update_self,
            hv]
        · intro S' hS'
          obtain ⟨⟨xr, xl⟩, rest', h, hx, h2⟩ := inv _ hS'
          have := congrFun h2 i
          rw [Function.update_self, hSi] at this
          injection this with h3
          injection h3 with h4 h5
          subst h4; subst h5
          dsimp only
          have hp : predFin (⟨xl.val + 1, h⟩ : Fin (net.u i xr)) = xl :=
            Fin.ext (by simp [predFin])
          rw [hp, h2, Function.update_idem, ← hx, Function.update_eq_self]
        · intro _
          apply feas_same net S i
          · rw [hSi]; rfl
          · intro r'; rw [hSi]
            simp [LocalState.count, List.countP_cons]
      · rw [if_neg hy]
        apply hzero; intro T hT
        obtain ⟨x, rest', h, -, h2⟩ := inv T hT
        have := congrFun h2 i; rw [Function.update_self, hSi] at this
        injection this with h3
        injection h3 with h4 h5
        subst h4
        exact hy (by simp)

/-! ## The factor d -/

noncomputable def lamF (T : net.Config) (c : Fin m) : ℝ :=
  match net.arrival with
  | .total lam => lam (net.totalPop T)
  | .perChain lam => lam c (net.chainPop T c)

lemma arrivalRate_eq (T : net.Config) (j : Fin N) (s : Fin R) :
    net.arrivalRate T j s = lamF net T (net.chain j s) * net.q j s := by
  unfold Network.arrivalRate lamF
  cases net.arrival <;> rfl

open Classical in
noncomputable def dAdd (T : net.Config) (c : Fin m) : ℝ :=
  if net.IsClosedNetwork then 1 else
  match net.arrival with
  | .total lam => ∏ n ∈ Finset.range (net.totalPop T + 1), lam n
  | .perChain lam =>
      ∏ k ∈ Finset.univ.filter (fun k => ¬ net.IsClosedChain k),
        ∏ n ∈ Finset.range (net.chainPop T k + if c = k then 1 else 0), lam k n

lemma d_eq_dAdd (B T : net.Config) (c : Fin m) (hM : net.totalPop T = net.totalPop B + 1)
    (hp : ∀ k, net.chainPop T k = net.chainPop B k + if c = k then 1 else 0) :
    net.d T = dAdd net B c := by
  unfold Network.d dAdd
  simp only [hM, hp]
  split_ifs
  · rfl
  · cases net.arrival <;> rfl

lemma dAdd_succ (T : net.Config) (c : Fin m) (hc : ¬ net.IsClosedChain c) :
    dAdd net T c = net.d T * lamF net T c := by
  classical
  have hnc : ¬ net.IsClosedNetwork := fun h => hc (h c)
  unfold Network.d dAdd lamF
  rw [if_neg hnc, if_neg hnc]
  cases net.arrival with
  | total lam => simp only [Finset.prod_range_succ]
  | perChain lam =>
    have h1 : ∀ k, ∏ n ∈ Finset.range (net.chainPop T k + if c = k then 1 else 0), lam k n =
        (∏ n ∈ Finset.range (net.chainPop T k), lam k n) *
          (if c = k then lam k (net.chainPop T k) else 1) := by
      intro k; split_ifs <;> simp [Finset.prod_range_succ]
    simp only [h1, Finset.prod_mul_distrib, Finset.prod_ite_eq]
    rw [if_pos (by simp [hc])]

lemma d_update_dAdd (B : net.Config) (i : Fin N) (x : LocalState R (net.u i)) (r0 : Fin R)
    (hc : ∀ r, x.count r = (B i).count r + if r = r0 then 1 else 0) :
    net.d (Function.update B i x) = dAdd net B (net.chain i r0) :=
  d_eq_dAdd net B _ _ (totalPop_update net B i x r0 hc) (chainPop_update net B i x r0 hc)

lemma d_enterAt (B : net.Config) (j : Fin N) (s : Fin R) :
    net.d (net.enterAt B j s) = dAdd net B (net.chain j s) :=
  d_update_dAdd net B j _ s (count_enter (B j) s)

lemma d_same (T : net.Config) (i : Fin N) (x : LocalState R (net.u i))
    (hc : ∀ r, x.count r = (T i).count r) : net.d (Function.update T i x) = net.d T := by
  have h1 : ∀ k, net.chainPop (Function.update T i x) k = net.chainPop T k :=
    chainPop_congr net _ _ (count_update_same net T i x hc)
  have h2 : net.totalPop (Function.update T i x) = net.totalPop T := by
    unfold Network.totalPop
    apply Finset.sum_congr rfl
    intro i' _
    simp only [LocalState.total, count_update_same net T i x hc]
  unfold Network.d
  simp only [h1, h2]

/-! ## Products of the f's -/

noncomputable def Fex (e : Fin N → Fin R → ℝ) (B : net.Config) (i0 : Fin N) : ℝ :=
  ∏ i ∈ ({i0}ᶜ : Finset (Fin N)), net.f e i (B i)

lemma F_update (e : Fin N → Fin R → ℝ) (B : net.Config) (i0 : Fin N)
    (x : LocalState R (net.u i0)) :
    ∏ i, net.f e i (Function.update B i0 x i) = net.f e i0 x * Fex net e B i0 := by
  rw [Fintype.prod_eq_mul_prod_compl i0, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have : i ≠ i0 := by simpa using hi
  rw [Function.update_of_ne this]

lemma F_self (e : Fin N → Fin R → ℝ) (B : net.Config) (i0 : Fin N) :
    ∏ i, net.f e i (B i) = net.f e i0 (B i0) * Fex net e B i0 := by
  rw [Fintype.prod_eq_mul_prod_compl i0]; rfl

lemma Fex_update (e : Fin N → Fin R → ℝ) (B : net.Config) (i0 : Fin N)
    (x : LocalState R (net.u i0)) : Fex net e (Function.update B i0 x) i0 = Fex net e B i0 := by
  unfold Fex
  apply Finset.prod_congr rfl
  intro i hi
  have : i ≠ i0 := by simpa using hi
  rw [Function.update_of_ne this]

lemma pc_update (e : Fin N → Fin R → ℝ) (B : net.Config) (i0 : Fin N)
    (x : LocalState R (net.u i0)) :
    pc net e (Function.update B i0 x) =
      net.d (Function.update B i0 x) * (net.f e i0 x * Fex net e B i0) := by
  unfold pc; rw [F_update]

/-! ## Local flux identities -/

lemma f_fcfs_cons (e : Fin N → Fin R → ℝ) (i : Fin N) (hμ : net.μ i ≠ 0) (r : Fin R)
    (rest : List (Fin R)) :
    net.f e i (.fcfs (r :: rest)) * net.μ i = e i r * net.f e i (.fcfs rest) := by
  simp only [Network.f, List.length_cons, List.map_cons, List.prod_cons, pow_succ]
  field_simp

lemma f_fcfs_concat (e : Fin N → Fin R → ℝ) (i : Fin N) (hμ : net.μ i ≠ 0) (l : List (Fin R))
    (s : Fin R) :
    net.f e i (.fcfs (l ++ [s])) * net.μ i = e i s * net.f e i (.fcfs l) := by
  simp only [Network.f, List.length_append, List.length_singleton, List.map_append,
    List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, pow_succ]
  field_simp

lemma f_lcfs_cons (e : Fin N → Fin R → ℝ) (i : Fin N) (r : Fin R) (l : Fin (net.u i r))
    (rest : List (Σ r : Fin R, Fin (net.u i r))) (hμ : net.μs i r l ≠ 0) :
    net.f e i (.lcfs (⟨r, l⟩ :: rest)) * net.μs i r l =
      net.f e i (.lcfs rest) * (e i r * net.A i r l) := by
  simp only [Network.f, List.map_cons, List.prod_cons]
  field_simp

section Local4

variable {R : ℕ} {u : Fin R → ℕ+}

lemma prod_ite_single (r : Fin R) (l : Fin (u r)) (c : ℝ) :
    ∏ r', ∏ k : Fin (u r'), (if r' = r ∧ k.val = l.val then c else 1) = c := by
  rw [Finset.prod_eq_single r]
  · rw [Finset.prod_eq_single l]
    · simp
    · intro k _ hk; rw [if_neg]; rintro ⟨-, h⟩; exact hk (Fin.ext h)
    · simp
  · intro r' _ hr; apply Finset.prod_eq_one; intro k _; rw [if_neg]; rintro ⟨h, -⟩; exact hr h
  · simp

lemma prod_addSt (X : (r : Fin R) → Fin (u r) → ℝ) (w : (r : Fin R) → Fin (u r) → ℕ)
    (r : Fin R) (l : Fin (u r)) :
    ∏ r', ∏ k, X r' k ^ (addSt w r l r' k) / ((addSt w r l r' k).factorial : ℝ) =
      (∏ r', ∏ k, X r' k ^ (w r' k) / ((w r' k).factorial : ℝ)) *
        (X r l / ((w r l : ℝ) + 1)) := by
  have pt : ∀ r' (k : Fin (u r')),
      X r' k ^ (addSt w r l r' k) / ((addSt w r l r' k).factorial : ℝ) =
      (X r' k ^ (w r' k) / ((w r' k).factorial : ℝ)) *
        (if r' = r ∧ k.val = l.val then X r l / ((w r l : ℝ) + 1) else 1) := by
    intro r' k
    by_cases h : r' = r ∧ k.val = l.val
    · rw [if_pos h]
      obtain ⟨rfl, hk⟩ := h
      have := Fin.ext hk; subst this
      rw [addSt_self, Nat.factorial_succ, pow_succ]
      push_cast
      have h1 : ((w r' k : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((w r' k).factorial : ℝ) ≠ 0 := by positivity
      field_simp
    · rw [if_neg h, addSt_ne w r r' l k h, mul_one]
  simp only [pt, Finset.prod_mul_distrib]
  rw [prod_ite_single r l]

lemma total_stages (v : (r : Fin R) → Fin (u r) → ℕ) :
    (LocalState.stages (u := u) v).total = ∑ r, ∑ k, v r k := rfl

lemma total_addSt (w : (r : Fin R) → Fin (u r) → ℕ) (r : Fin R) (l : Fin (u r)) :
    (LocalState.stages (u := u) (addSt w r l)).total = (LocalState.stages (u := u) w).total + 1 := by
  simp only [LocalState.total, count_addSt, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

end Local4

lemma f_stage_flux (e : Fin N → Fin R → ℝ) (i : Fin N) (ht : net.type i = .ps ∨ net.type i = .is)
    (w : (r : Fin R) → Fin (net.u i r) → ℕ) (r : Fin R) (l : Fin (net.u i r))
    (hμ : net.μs i r l ≠ 0) :
    net.f e i (.stages (addSt w r l)) *
      net.stageRate i r l (addSt w r l) (LocalState.stages (addSt w r l)).total =
      net.f e i (.stages w) * (e i r * net.A i r l) := by
  have hw : ((w r l : ℝ) + 1) ≠ 0 := by positivity
  rcases ht with ht | ht
  · have hsum : ∑ r', ∑ k, addSt w r l r' k = ∑ r', ∑ k, w r' k + 1 := by
      have := total_addSt w r l
      simpa only [total_stages] using this
    simp only [Network.f, Network.stageRate, ht]
    rw [prod_addSt, total_addSt, addSt_self]
    simp only [total_stages]
    rw [hsum, Nat.factorial_succ]
    push_cast
    have hn : ((∑ r, ∑ k, w r k : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  · simp only [Network.f, Network.stageRate, ht]
    rw [prod_addSt, addSt_self]
    push_cast
    field_simp

/-! ## Telescoping of the stage probabilities -/

lemma A_succ (i : Fin N) (r : Fin R) (l : Fin (net.u i r)) (h : l.val + 1 < (net.u i r : ℕ)) :
    net.A i r ⟨l.val + 1, h⟩ = net.A i r l * net.a i r l := by
  classical
  unfold Network.A
  have : (Finset.univ.filter fun j : Fin (net.u i r) => j < ⟨l.val + 1, h⟩) =
      insert l (Finset.univ.filter fun j => j < l) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.lt_def, Fin.ext_iff]
    omega
  rw [this, Finset.prod_insert (by simp), mul_comm]

lemma A_zero (i : Fin N) (r : Fin R) (h : 0 < (net.u i r : ℕ)) : net.A i r ⟨0, h⟩ = 1 := by
  unfold Network.A
  apply Finset.prod_eq_one
  intro j hj
  simp at hj

lemma sum_A (hnet : net.IsValid) (i : Fin N) (r : Fin R) :
    ∑ l : Fin (net.u i r), net.A i r l * (1 - net.a i r l) = 1 := by
  set n : ℕ := (net.u i r : ℕ) with hn
  have hpos : 0 < n := (net.u i r).pos
  let a' : ℕ → ℝ := fun t => if h : t < n then net.a i r ⟨t, h⟩ else 0
  let P : ℕ → ℝ := fun j => ∏ t ∈ Finset.range j, a' t
  have hA : ∀ (l : ℕ) (hl : l < n), net.A i r ⟨l, hl⟩ = P l := by
    intro l
    induction l with
    | zero => intro hl; rw [A_zero]; simp [P]
    | succ l ih =>
      intro hl
      have := A_succ net i r ⟨l, by omega⟩ hl
      simp only at this
      rw [this, ih (by omega)]
      simp only [P, Finset.prod_range_succ, a', dif_pos (show l < n by omega)]
  have hterm : ∀ l : Fin (net.u i r), net.A i r l * (1 - net.a i r l) = P l.val - P (l.val + 1) := by
    intro l
    have h1 := hA l.val l.isLt
    simp only [Fin.eta] at h1
    rw [h1]
    have ha : a' l.val = net.a i r l := by
      simp only [a', dif_pos (show l.val < n from l.isLt), Fin.eta]
    have hs : P (l.val + 1) = P l.val * a' l.val := Finset.prod_range_succ _ _
    rw [hs, ha]; ring
  rw [Finset.sum_congr rfl (fun l _ => hterm l)]
  rw [Fin.sum_univ_eq_sum_range (fun t => P t - P (t + 1)) n, Finset.sum_range_sub']
  have hP0 : P 0 = 1 := by simp [P]
  have hPn : P n = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr (show n - 1 < n by omega))
    simp only [a', dif_pos (show n - 1 < n by omega)]
    exact hnet.a_last i r _ (by simp only; omega)
  rw [hP0, hPn]; ring

/-! ## Departure flux from a configuration -/

section Local5

variable {R : ℕ} {u : Fin R → ℕ+}

lemma count_fcfs_cons (r : Fin R) (rest : List (Fin R)) (r' : Fin R) :
    (LocalState.fcfs (u := u) (r :: rest)).count r' =
      (LocalState.fcfs (u := u) rest).count r' + if r' = r then 1 else 0 := by
  simp only [LocalState.count, List.count_cons]
  by_cases hr : r' = r
  · subst hr; simp
  · simp [hr, Ne.symm hr]

lemma count_lcfs_cons (x : Σ r : Fin R, Fin (u r)) (rest : List (Σ r : Fin R, Fin (u r)))
    (r' : Fin R) :
    (LocalState.lcfs (u := u) (x :: rest)).count r' =
      (LocalState.lcfs (u := u) rest).count r' + if r' = x.1 then 1 else 0 := by
  simp only [LocalState.count, List.countP_cons]
  by_cases hr : r' = x.1
  · subst hr; simp
  · simp [hr, Ne.symm hr]

end Local5

noncomputable def FDB (e : Fin N → Fin R → ℝ) (L : Label N R m) (B : net.Config) (i : Fin N)
    (d : Option (Fin N × Fin R)) : ℝ :=
  match B i with
  | .fcfs rest => ∑ r : Fin R, pc net e (Function.update B i (.fcfs (r :: rest))) *
      (if net.destLabel i r d = L then net.μ i * net.routeProb i r d else 0)
  | _ => 0

noncomputable def SDB (e : Fin N → Fin R → ℝ) (L : Label N R m) (B : net.Config) (i : Fin N)
    (r : Fin R) (l : Fin (net.u i r)) (d : Option (Fin N × Fin R)) : ℝ :=
  match B i with
  | .stages w => pc net e (Function.update B i (.stages (addSt w r l))) *
      (if net.destLabel i r d = L then
        net.stageRate i r l (addSt w r l) (LocalState.stages (addSt w r l)).total *
          (1 - net.a i r l) * net.routeProb i r d else 0)
  | _ => 0

noncomputable def LDB (e : Fin N → Fin R → ℝ) (L : Label N R m) (B : net.Config) (i : Fin N)
    (d : Option (Fin N × Fin R)) : ℝ :=
  match B i with
  | .lcfs rest => ∑ x : (Σ r : Fin R, Fin (net.u i r)),
      pc net e (Function.update B i (.lcfs (x :: rest))) *
      (if net.destLabel i x.1 d = L then
        net.μs i x.1 x.2 * (1 - net.a i x.1 x.2) * net.routeProb i x.1 d else 0)
  | _ => 0

lemma depB (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (L : Label N R m) (B : net.Config)
    (i : Fin N) (hfit : (B i).Fits (net.type i)) (d : Option (Fin N × Fin R)) :
    FDB net e L B i d + ∑ r, ∑ l, SDB net e L B i r l d + LDB net e L B i d =
      (∑ r, if net.destLabel i r d = L then
          dAdd net B (net.chain i r) * (e i r * net.routeProb i r d) else 0) *
        (net.f e i (B i) * Fex net e B i) := by
  unfold FDB SDB LDB
  rcases hBi : B i with rest | w | rest
  · have ht : net.type i = .fcfs := by
      rw [hBi] at hfit; revert hfit; cases net.type i <;> simp [LocalState.Fits]
    have hμ : net.μ i ≠ 0 := (hnet.μ_pos i ht).ne'
    dsimp only
    simp only [Finset.sum_const_zero, add_zero, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [pc_update, d_update_dAdd net B i _ r (fun r' => by rw [hBi]; exact count_fcfs_cons r rest r')]
    split_ifs
    · have key := f_fcfs_cons net e i hμ r rest
      linear_combination (dAdd net B (net.chain i r) * Fex net e B i * net.routeProb i r d) * key
    · simp
  · have ht : net.type i ≠ .fcfs := by
      rw [hBi] at hfit; intro h; rw [h] at hfit; simp [LocalState.Fits] at hfit
    have ht' : net.type i = .ps ∨ net.type i = .is := by
      rw [hBi] at hfit; revert hfit; cases net.type i <;> simp [LocalState.Fits]
    dsimp only
    simp only [zero_add, add_zero, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs
    · have hterm : ∀ l : Fin (net.u i r),
          pc net e (Function.update B i (.stages (addSt w r l))) *
            (net.stageRate i r l (addSt w r l) (LocalState.stages (addSt w r l)).total *
              (1 - net.a i r l) * net.routeProb i r d) =
          (dAdd net B (net.chain i r) * Fex net e B i * net.routeProb i r d *
            net.f e i (.stages w) * e i r) * (net.A i r l * (1 - net.a i r l)) := by
        intro l
        rw [pc_update, d_update_dAdd net B i _ r
          (fun r' => by rw [hBi]; exact count_addSt w r l r')]
        have key := f_stage_flux net e i ht' w r l (hnet.μs_pos i r l ht).ne'
        linear_combination (dAdd net B (net.chain i r) * Fex net e B i *
          net.routeProb i r d * (1 - net.a i r l)) * key
      rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum, sum_A net hnet i r]
      ring
    · simp
  · have ht : net.type i ≠ .fcfs := by
      rw [hBi] at hfit; intro h; rw [h] at hfit; simp [LocalState.Fits] at hfit
    dsimp only
    simp only [Finset.sum_const_zero, zero_add, Finset.sum_mul]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs
    · have hterm : ∀ l : Fin (net.u i r),
          pc net e (Function.update B i (.lcfs (⟨r, l⟩ :: rest))) *
            (net.μs i r l * (1 - net.a i r l) * net.routeProb i r d) =
          (dAdd net B (net.chain i r) * Fex net e B i * net.routeProb i r d *
            net.f e i (.lcfs rest) * e i r) * (net.A i r l * (1 - net.a i r l)) := by
        intro l
        rw [pc_update, d_update_dAdd net B i _ r
          (fun r' => by rw [hBi]; exact count_lcfs_cons ⟨r, l⟩ rest r')]
        have key := f_lcfs_cons net e i r l rest (hnet.μs_pos i r l ht).ne'
        linear_combination (dAdd net B (net.chain i r) * Fex net e B i *
          net.routeProb i r d * (1 - net.a i r l)) * key
      rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum, sum_A net hnet i r]
      ring
    · simp

/-! ## Routing into a pair `(j, s)` -/

noncomputable def vArr (e : Fin N → Fin R → ℝ) (S : net.Config) (L : Label N R m) (j : Fin N)
    (s : Fin R) : ℝ :=
  (unroute net S (some (j, s))).elim 0 (fun B =>
    pc net e B * (if net.entryLabel j s = L then net.arrivalRate B j s else 0))

noncomputable def vDep (e : Fin N → Fin R → ℝ) (S : net.Config) (L : Label N R m) (i : Fin N)
    (d : Option (Fin N × Fin R)) : ℝ :=
  (unroute net S d).elim 0 (fun B =>
    FDB net e L B i d + ∑ r, ∑ l, SDB net e L B i r l d + LDB net e L B i d)

lemma route_in (hnet : net.IsValid) (e : Fin N → Fin R → ℝ)
    (htraffic : net.TrafficEquations e) (S : net.State) (L : Label N R m) (j : Fin N)
    (s : Fin R) :
    vArr net e S.1 L j s + ∑ i, vDep net e S.1 L i (some (j, s)) =
      if net.entryLabel j s = L then
        (unroute net S.1 (some (j, s))).elim 0 (fun B => net.d S.1 * (∏ i, net.f e i (B i)) * e j s)
      else 0 := by
  unfold vArr vDep
  rcases hB : unroute net S.1 (some (j, s)) with _ | B
  · simp
  · simp only [Option.elim_some]
    have hS : S.1 = net.enterAt B j s := ((routeTo_eq_iff net B S.1 _).mpr hB).symm
    have hfitB : ∀ i, (B i).Fits (net.type i) := fun i =>
      fits_of_kind (unroute_kind net hB i).symm (S.2.1 i)
    rw [Finset.sum_congr rfl (fun i _ => depB net hnet e L B i (hfitB i) (some (j, s)))]
    simp only [Network.destLabel]
    have hdS : net.d S.1 = dAdd net B (net.chain j s) := by rw [hS, d_enterAt]
    by_cases hc : net.entryLabel j s = L
    · simp only [hc, if_true]
      have h1 : ∀ i r, dAdd net B (net.chain i r) * (e i r * net.routeProb i r (some (j, s))) =
          net.d S.1 * (e i r * net.P i r j s) := by
        intro i r
        simp only [Network.routeProb]
        by_cases hP : net.P i r j s = 0
        · simp [hP]
        · rw [hnet.P_chain i r j s hP, hdS]
      simp only [h1]
      have h2 : pc net e B * net.arrivalRate B j s =
          net.d S.1 * (∏ i, net.f e i (B i)) * net.q j s := by
        rw [arrivalRate_eq]
        by_cases hq : net.q j s = 0
        · simp [hq]
        · rw [hdS, dAdd_succ net B _ (q_ne_open net j s hq)]
          unfold pc; ring
      rw [h2]
      have h3 : ∀ i, net.f e i (B i) * Fex net e B i = ∏ i', net.f e i' (B i') :=
        fun i => (F_self net e B i).symm
      simp only [h3, ← Finset.sum_mul, ← Finset.mul_sum]
      rw [← htraffic j s]
      ring
    · simp [hc]

/-! ## Assembling the right-hand side -/

noncomputable def vSN (e : Fin N → Fin R → ℝ) (S : net.Config) (L : Label N R m) (i : Fin N)
    (r : Fin R) (l : Fin (net.u i r)) : ℝ :=
  match S i with
  | .stages w => if h : l.val + 1 < (net.u i r : ℕ) then
      (if 0 < w r ⟨l.val + 1, h⟩ then
        pc net e (Function.update S i (.stages (addSt (subSt w r ⟨l.val + 1, h⟩) r l))) *
          (if Label.stage i r (l.val + 1) = L then
            net.stageRate i r l (addSt (subSt w r ⟨l.val + 1, h⟩) r l)
              (LocalState.stages (addSt (subSt w r ⟨l.val + 1, h⟩) r l)).total *
                net.a i r l
           else 0)
       else 0)
    else 0
  | _ => 0

noncomputable def vLN (e : Fin N → Fin R → ℝ) (S : net.Config) (L : Label N R m) (i : Fin N) :
    ℝ :=
  match S i with
  | .lcfs (y :: rest) => if 0 < y.2.val then
      pc net e (Function.update S i (.lcfs (⟨y.1, predFin y.2⟩ :: rest))) *
        (if Label.stage i y.1 y.2.val = L then
          net.μs i y.1 (predFin y.2) * net.a i y.1 (predFin y.2) else 0)
      else 0
  | _ => 0

noncomputable def vEv (e : Fin N → Fin R → ℝ) (S : net.Config) (L : Label N R m) :
    Network.Event N R net.u → ℝ
  | .arrive j s => vArr net e S L j s
  | .fcfsDone i d => (unroute net S d).elim 0 (fun B => FDB net e L B i d)
  | .stageNext i r l => vSN net e S L i r l
  | .stageDone i r l d => (unroute net S d).elim 0 (fun B => SDB net e L B i r l d)
  | .lcfsNext i => vLN net e S L i
  | .lcfsDone i d => (unroute net S d).elim 0 (fun B => LDB net e L B i d)

open Classical in
lemma rhs_hasSum (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (S : net.State)
    (L : Label N R m) :
    HasSum (fun S' : net.State => net.productForm e S' * ∑ ev : Network.Event N R net.u,
        (if net.evTarget S'.1 ev = S.1 ∧ net.enterLabel S'.1 ev = L
          then net.evRate S'.1 ev else 0))
      (∑ ev, vEv net e S.1 L ev) := by
  simp only [Finset.mul_sum]
  apply hasSum_sum
  intro ev _
  cases ev with
  | arrive j s => exact in_arrive net e S L j s
  | fcfsDone i d => exact in_fcfsDone net hnet e S L i d
  | stageNext i r l => exact in_stageNext net hnet e S L i r l
  | stageDone i r l d => exact in_stageDone net hnet e S L i r l d
  | lcfsNext i => exact in_lcfsNext net hnet e S L i
  | lcfsDone i d => exact in_lcfsDone net hnet e S L i d

noncomputable def RIN (e : Fin N → Fin R → ℝ) (S : net.Config) (L : Label N R m) : ℝ :=
  ∑ j, ∑ s, if net.entryLabel j s = L then
    (unroute net S (some (j, s))).elim 0 (fun B => net.d S * (∏ i, net.f e i (B i)) * e j s)
    else 0

noncomputable def DOUT (e : Fin N → Fin R → ℝ) (S : net.Config) (L : Label N R m) : ℝ :=
  ∑ i, (∑ r, if Label.outside (net.chain i r) = L then
      dAdd net S (net.chain i r) * (e i r * net.routeProb i r none) else 0) *
    (net.f e i (S i) * Fex net e S i)

lemma elim_sum {α ι : Type*} [Fintype ι] (o : Option α) (f : ι → α → ℝ) :
    ∑ x, o.elim 0 (f x) = o.elim 0 (fun a => ∑ x, f x a) := by
  cases o <;> simp

lemma rhs_val (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (htraffic : net.TrafficEquations e)
    (S : net.State) (L : Label N R m) :
    ∑ ev, vEv net e S.1 L ev = RIN net e S.1 L + DOUT net e S.1 L +
      ∑ i, ∑ r, ∑ l, vSN net e S.1 L i r l + ∑ i, vLN net e S.1 L i := by
  rw [ev_sum]
  simp only [vEv]
  have hdep : ∀ i d, vDep net e S.1 L i d =
      (unroute net S.1 d).elim 0 (fun B => FDB net e L B i d) +
      ∑ r, ∑ l, (unroute net S.1 d).elim 0 (fun B => SDB net e L B i r l d) +
      (unroute net S.1 d).elim 0 (fun B => LDB net e L B i d) := by
    intro i d
    unfold vDep
    cases unroute net S.1 d <;> simp
  have hD : ∑ i, ∑ d, (unroute net S.1 d).elim 0 (fun B => FDB net e L B i d) +
      ∑ i, ∑ r, ∑ l, ∑ d, (unroute net S.1 d).elim 0 (fun B => SDB net e L B i r l d) +
      ∑ i, ∑ d, (unroute net S.1 d).elim 0 (fun B => LDB net e L B i d) =
      ∑ i, vDep net e S.1 L i none + ∑ j, ∑ s, ∑ i, vDep net e S.1 L i (some (j, s)) := by
    have hSD : ∑ i, ∑ r, ∑ l, ∑ d, (unroute net S.1 d).elim 0 (fun B => SDB net e L B i r l d) =
        ∑ i, ∑ d, ∑ r, ∑ l, (unroute net S.1 d).elim 0 (fun B => SDB net e L B i r l d) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_congr rfl (fun r _ => Finset.sum_comm), Finset.sum_comm]
    rw [hSD, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have hc : ∀ i, ∑ d, (unroute net S.1 d).elim 0 (fun B => FDB net e L B i d) +
        ∑ d, ∑ r, ∑ l, (unroute net S.1 d).elim 0 (fun B => SDB net e L B i r l d) +
        ∑ d, (unroute net S.1 d).elim 0 (fun B => LDB net e L B i d) =
        vDep net e S.1 L i none + ∑ j, ∑ s, vDep net e S.1 L i (some (j, s)) := by
      intro i
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun d _ => (hdep i d).symm)]
      rw [Fintype.sum_option, Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
  have hR : ∑ j, ∑ s, vArr net e S.1 L j s + ∑ j, ∑ s, ∑ i, vDep net e S.1 L i (some (j, s)) =
      RIN net e S.1 L := by
    unfold RIN
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro s _
    exact route_in net hnet e htraffic S L j s
  have hO : ∑ i, vDep net e S.1 L i none = DOUT net e S.1 L := by
    unfold DOUT vDep
    apply Finset.sum_congr rfl; intro i _
    simp only [unroute, Option.elim_some]
    rw [depB net hnet e L S.1 i (S.2.1 i) none]
    rfl
  linarith [hD, hR, hO]

/-! ## The left-hand side -/

lemma sum_routeProb (i : Fin N) (r : Fin R) : ∑ d, net.routeProb i r d = 1 := by
  simp only [Fintype.sum_option, Fintype.sum_prod_type, Network.routeProb]
  ring

noncomputable def outC (S : net.Config) (i : Fin N) : ℝ :=
  match S i with
  | .fcfs (_ :: _) => net.μ i
  | _ => 0

noncomputable def outS (S : net.Config) (i : Fin N) (r : Fin R) (l : Fin (net.u i r)) : ℝ :=
  match S i with
  | .stages v => net.stageRate i r l v (LocalState.stages v).total
  | _ => 0

noncomputable def outL (S : net.Config) (L : Label N R m) (i : Fin N) : ℝ :=
  match S i with
  | .lcfs (x :: _) => if Label.stage i x.1 x.2.val = L then net.μs i x.1 x.2 else 0
  | _ => 0

noncomputable def OUT (S : net.Config) (L : Label N R m) : ℝ :=
  ∑ j, ∑ s, (if Label.outside (net.chain j s) = L then net.arrivalRate S j s else 0)
  + ∑ i, (if Label.center i = L then outC net S i else 0)
  + ∑ i, ∑ r, ∑ l : Fin (net.u i r), (if Label.stage i r l.val = L then outS net S i r l else 0)
  + ∑ i, outL net S L i

lemma if_label_eq {a b : Label N R m} (h : a = b) (L : Label N R m) (x : ℝ) :
    (if a = L then x else 0) = (if b = L then x else 0) := by rw [h]

lemma lhs_val (S : net.Config) (L : Label N R m) :
    ∑ ev : Network.Event N R net.u, (if net.leaveLabel S ev = L then net.evRate S ev else 0) =
      OUT net S L := by
  rw [ev_sum]
  unfold OUT
  have hF : ∀ i, ∑ d, (if net.leaveLabel S (.fcfsDone i d) = L then
      net.evRate S (.fcfsDone i d) else 0) = if Label.center i = L then outC net S i else 0 := by
    intro i
    rw [Finset.sum_congr rfl (fun d _ => if_label_eq
      (show net.leaveLabel S (.fcfsDone i d) = Label.center i from rfl) L _)]
    by_cases hc : Label.center i = L
    · simp only [hc, if_true]
      unfold outC
      simp only [Network.evRate]
      rcases S i with l | v | l
      · rcases l with _ | ⟨r, rest⟩
        · simp
        · dsimp only; rw [← Finset.mul_sum, sum_routeProb, mul_one]
      · simp
      · simp
    · simp [hc]
  have hS : ∀ i r l, (if net.leaveLabel S (.stageNext i r l) = L then
      net.evRate S (.stageNext i r l) else 0) +
      ∑ d, (if net.leaveLabel S (.stageDone i r l d) = L then
        net.evRate S (.stageDone i r l d) else 0) =
      if Label.stage i r l.val = L then outS net S i r l else 0 := by
    intro i r l
    rw [if_label_eq (show net.leaveLabel S (.stageNext i r l) = Label.stage i r l.val from rfl) L,
      Finset.sum_congr rfl (fun d _ => if_label_eq
        (show net.leaveLabel S (.stageDone i r l d) = Label.stage i r l.val from rfl) L _)]
    by_cases hc : Label.stage i r l.val = L
    · simp only [hc, if_true]
      unfold outS
      simp only [Network.evRate]
      rcases S i with l' | v | l'
      · simp
      · dsimp only; rw [← Finset.mul_sum, sum_routeProb]; ring
      · simp
    · simp [hc]
  have hL : ∀ i, (if net.leaveLabel S (.lcfsNext i) = L then net.evRate S (.lcfsNext i) else 0) +
      ∑ d, (if net.leaveLabel S (.lcfsDone i d) = L then net.evRate S (.lcfsDone i d) else 0) =
      outL net S L i := by
    intro i
    have h1 : net.leaveLabel S (.lcfsNext i) = (match S i with
        | .lcfs (x :: _) => Label.stage i x.1 x.2.val
        | _ => Label.center i) := rfl
    have h2 : ∀ d, net.leaveLabel S (.lcfsDone i d) = (match S i with
        | .lcfs (x :: _) => Label.stage i x.1 x.2.val
        | _ => Label.center i) := fun d => rfl
    rw [if_label_eq h1 L, Finset.sum_congr rfl (fun d _ => if_label_eq (h2 d) L _)]
    unfold outL
    simp only [Network.evRate]
    rcases S i with l' | v | l'
    · simp
    · simp
    · rcases l' with _ | ⟨x, rest⟩
      · simp
      · dsimp only
        split_ifs
        · rw [← Finset.mul_sum, sum_routeProb]; ring
        · simp
  simp only [hF]
  have e1 : ∑ i, ∑ r, ∑ l, (if net.leaveLabel S (.stageNext i r l) = L then
      net.evRate S (.stageNext i r l) else 0) +
      ∑ i, ∑ r, ∑ l, ∑ d, (if net.leaveLabel S (.stageDone i r l d) = L then
        net.evRate S (.stageDone i r l d) else 0) =
      ∑ i, ∑ r, ∑ l : Fin (net.u i r), (if Label.stage i r l.val = L then outS net S i r l
        else 0) := by
    simp only [← Finset.sum_add_distrib, hS]
  have e2 : ∑ i, (if net.leaveLabel S (.lcfsNext i) = L then net.evRate S (.lcfsNext i) else 0) +
      ∑ i, ∑ d, (if net.leaveLabel S (.lcfsDone i d) = L then net.evRate S (.lcfsDone i d) else 0) =
      ∑ i, outL net S L i := by
    simp only [← Finset.sum_add_distrib, hL]
  have e0 : ∑ j, ∑ s, (if net.leaveLabel S (.arrive j s) = L then net.evRate S (.arrive j s)
      else 0) = ∑ j, ∑ s, (if Label.outside (net.chain j s) = L then net.arrivalRate S j s
      else 0) := rfl
  linarith [e0, e1, e2]

/-! ## Per-label algebra: helpers -/

lemma vSN_zero (e : Fin N → Fin R → ℝ) (S : net.Config) (L : Label N R m) (i : Fin N)
    (r : Fin R) (l : Fin (net.u i r)) (h : ∀ n, Label.stage i r n ≠ L) :
    vSN net e S L i r l = 0 := by
  unfold vSN; split <;> simp [h]

lemma vLN_zero (e : Fin N → Fin R → ℝ) (S : net.Config) (L : Label N R m) (i : Fin N)
    (h : ∀ r n, Label.stage i r n ≠ L) : vLN net e S L i = 0 := by
  unfold vLN; split <;> simp [h]

lemma outL_zero (S : net.Config) (L : Label N R m) (i : Fin N)
    (h : ∀ r n, Label.stage i r n ≠ L) : outL net S L i = 0 := by
  unfold outL; split <;> simp [h]

lemma DOUT_zero (e : Fin N → Fin R → ℝ) (S : net.Config) (L : Label N R m)
    (h : ∀ k, Label.outside k ≠ L) : DOUT net e S L = 0 := by
  unfold DOUT; simp [h]

lemma unroute_some (S : net.Config) (j : Fin N) (s : Fin R) :
    unroute net S (some (j, s)) = (unenter (S j) s).map (fun y => Function.update S j y) := rfl

section Local7
variable {R : ℕ} {u : Fin R → ℕ+}

lemma unenter_stages (w : (r : Fin R) → Fin (u r) → ℕ) (s : Fin R) :
    unenter (LocalState.stages (u := u) w) s =
      if 0 < w s ⟨0, (u s).pos⟩ then some (.stages (subSt w s ⟨0, (u s).pos⟩)) else none := rfl

lemma unenter_lcfs_cons (x : Σ r : Fin R, Fin (u r)) (rest : List (Σ r : Fin R, Fin (u r)))
    (s : Fin R) :
    unenter (LocalState.lcfs (u := u) (x :: rest)) s =
      if x.1 = s ∧ x.2.val = 0 then some (.lcfs rest) else none := rfl

lemma unenter_lcfs_nil (s : Fin R) : unenter (LocalState.lcfs (u := u) []) s = none := rfl

lemma unenter_fcfs_concat (l : List (Fin R)) (s0 s : Fin R) :
    unenter (LocalState.fcfs (u := u) (l ++ [s0])) s = if s0 = s then some (.fcfs l) else none := by
  simp [unenter]

lemma unenter_fcfs_nil (s : Fin R) : unenter (LocalState.fcfs (u := u) []) s = none := by
  simp [unenter]

end Local7

lemma stageRate_zero {i : Fin N} {r : Fin R} {l : Fin (net.u i r)}
    {v : (r : Fin R) → Fin (net.u i r) → ℕ} {n : ℕ} (h : v r l = 0) :
    net.stageRate i r l v n = 0 := by
  unfold Network.stageRate; split <;> simp [h]

/-! ## Label: outside -/

lemma traffic_chain (hnet : net.IsValid) (e : Fin N → Fin R → ℝ)
    (htraffic : net.TrafficEquations e) (k : Fin m) :
    ∑ i, ∑ r, (if net.chain i r = k then e i r * (1 - ∑ j, ∑ s, net.P i r j s) else 0) =
      ∑ j, ∑ s, (if net.chain j s = k then net.q j s else 0) := by
  set χ : Fin N → Fin R → ℝ := fun i r => if net.chain i r = k then 1 else 0 with hχ
  have hP : ∀ i r j s, χ j s * net.P i r j s = χ i r * net.P i r j s := by
    intro i r j s
    by_cases h : net.P i r j s = 0
    · simp [h]
    · simp only [hχ, hnet.P_chain i r j s h]
  have lhs : ∀ i r, (if net.chain i r = k then e i r * (1 - ∑ j, ∑ s, net.P i r j s) else 0) =
      χ i r * e i r - ∑ j, ∑ s, χ j s * e i r * net.P i r j s := by
    intro i r
    have : ∑ j, ∑ s, χ j s * e i r * net.P i r j s = χ i r * e i r * ∑ j, ∑ s, net.P i r j s := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _
      linear_combination e i r * hP i r j s
    rw [this]; simp only [hχ]; split_ifs <;> ring
  have rhs : ∀ j s, (if net.chain j s = k then net.q j s else 0) =
      χ j s * e j s - ∑ i, ∑ r, χ j s * e i r * net.P i r j s := by
    intro j s
    rw [← htraffic j s]
    simp only [hχ]; split_ifs
    · simp only [one_mul]; ring
    · simp
  simp only [lhs, rhs, Finset.sum_sub_distrib]
  congr 1
  calc ∑ i, ∑ r, ∑ j, ∑ s, χ j s * e i r * net.P i r j s
      = ∑ i, ∑ j, ∑ r, ∑ s, χ j s * e i r * net.P i r j s :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ j, ∑ i, ∑ r, ∑ s, χ j s * e i r * net.P i r j s := Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ s, ∑ r, χ j s * e i r * net.P i r j s :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
    _ = ∑ j, ∑ s, ∑ i, ∑ r, χ j s * e i r * net.P i r j s :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_comm)

lemma ib_outside (hnet : net.IsValid) (e : Fin N → Fin R → ℝ)
    (htraffic : net.TrafficEquations e) (S : net.State) (k : Fin m) :
    pc net e S.1 * OUT net S.1 (.outside k) = RIN net e S.1 (.outside k) +
      DOUT net e S.1 (.outside k) + ∑ i, ∑ r, ∑ l, vSN net e S.1 (.outside k) i r l +
      ∑ i, vLN net e S.1 (.outside k) i := by
  have hRIN : RIN net e S.1 (.outside k) = 0 := by
    unfold RIN; apply Finset.sum_eq_zero; intro j _; apply Finset.sum_eq_zero; intro s _
    rw [if_neg]; unfold Network.entryLabel; split_ifs <;> simp
  have hSN : ∑ i, ∑ r, ∑ l, vSN net e S.1 (.outside k) i r l = 0 := by
    apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro r _
    apply Finset.sum_eq_zero; intro l _
    exact vSN_zero net e S.1 _ i r l (fun n => by simp)
  have hLN : ∑ i, vLN net e S.1 (.outside k) i = 0 := by
    apply Finset.sum_eq_zero; intro i _
    exact vLN_zero net e S.1 _ i (fun r n => by simp)
  have hOUT : OUT net S.1 (.outside k) =
      ∑ j, ∑ s, (if net.chain j s = k then lamF net S.1 k * net.q j s else 0) := by
    unfold OUT
    have h1 : ∀ i, outL net S.1 (.outside k) i = 0 := fun i =>
      outL_zero net S.1 _ i (fun r n => by simp)
    simp only [h1, Finset.sum_const_zero, add_zero]
    simp only [Label.outside.injEq, reduceCtorEq, if_false, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro s _
    split_ifs with h
    · rw [arrivalRate_eq, h]
    · rfl
  rw [hRIN, hSN, hLN, hOUT]
  unfold DOUT
  simp only [Label.outside.injEq, ← F_self net e S.1]
  rw [← Finset.sum_mul]
  by_cases hk : net.IsClosedChain k
  · have h1 : ∀ j s, (if net.chain j s = k then lamF net S.1 k * net.q j s else 0) = 0 := by
      intro j s; split_ifs with h
      · rw [hk j s h, mul_zero]
      · rfl
    have h2 : ∀ i r, (if net.chain i r = k then
        dAdd net S.1 (net.chain i r) * (e i r * net.routeProb i r none) else 0) = 0 := by
      intro i r; split_ifs with h
      · have hc : net.IsClosedChain (net.chain i r) := h ▸ hk
        have : net.routeProb i r none = 0 := by
          simp [Network.routeProb, hnet.P_row_closed i r hc]
        rw [this]; ring
      · rfl
    simp [h1, h2]
  · have hd := dAdd_succ net S.1 k hk
    have h2 : ∀ i r, (if net.chain i r = k then
        dAdd net S.1 (net.chain i r) * (e i r * net.routeProb i r none) else 0) =
        net.d S.1 * lamF net S.1 k *
          (if net.chain i r = k then e i r * (1 - ∑ j, ∑ s, net.P i r j s) else 0) := by
      intro i r; split_ifs with h
      · rw [h, hd]; simp only [Network.routeProb]; try ring
      · ring
    simp only [h2, ← Finset.mul_sum]
    rw [traffic_chain net hnet e htraffic k]
    have h1 : ∀ j s, (if net.chain j s = k then lamF net S.1 k * net.q j s else 0) =
        lamF net S.1 k * (if net.chain j s = k then net.q j s else 0) := by
      intro j s; split_ifs <;> ring
    simp only [h1, ← Finset.mul_sum]
    unfold pc; ring

/-! ## Label: center -/

lemma ib_center (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (S : net.State) (i0 : Fin N) :
    pc net e S.1 * OUT net S.1 (.center i0) = RIN net e S.1 (.center i0) +
      DOUT net e S.1 (.center i0) + ∑ i, ∑ r, ∑ l, vSN net e S.1 (.center i0) i r l +
      ∑ i, vLN net e S.1 (.center i0) i := by
  obtain ⟨T, hT⟩ := S
  dsimp only
  have hD : DOUT net e T (.center i0) = 0 := DOUT_zero net e T _ (fun k => by simp)
  have hSN : ∑ i, ∑ r, ∑ l, vSN net e T (.center i0) i r l = 0 := by
    apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro r _
    apply Finset.sum_eq_zero; intro l _
    exact vSN_zero net e T _ i r l (fun n => by simp)
  have hLN : ∑ i, vLN net e T (.center i0) i = 0 := by
    apply Finset.sum_eq_zero; intro i _
    exact vLN_zero net e T _ i (fun r n => by simp)
  have hOUT : OUT net T (.center i0) = outC net T i0 := by
    unfold OUT
    have h1 : ∀ i, outL net T (.center i0) i = 0 := fun i =>
      outL_zero net T _ i (fun r n => by simp)
    simp only [h1, Finset.sum_const_zero, add_zero]
    simp [Label.center.injEq]
  have hRIN : RIN net e T (.center i0) = if net.type i0 = .fcfs then
      ∑ s, (unroute net T (some (i0, s))).elim 0
        (fun B => net.d T * (∏ i, net.f e i (B i)) * e i0 s) else 0 := by
    unfold RIN
    rw [Finset.sum_eq_single i0]
    · split_ifs with ht
      · apply Finset.sum_congr rfl; intro s _
        rw [if_pos]; unfold Network.entryLabel; rw [if_pos ht]
      · apply Finset.sum_eq_zero; intro s _
        rw [if_neg]; unfold Network.entryLabel; rw [if_neg ht]; simp
    · intro j _ hj
      apply Finset.sum_eq_zero; intro s _
      rw [if_neg]; unfold Network.entryLabel; split_ifs <;> simp [hj]
    · simp
  rw [hD, hSN, hLN, hOUT, hRIN]
  have hfit := hT.1 i0
  rcases hSi : T i0 with l | w | l
  · have ht : net.type i0 = .fcfs := by
      rw [hSi] at hfit; revert hfit; cases net.type i0 <;> simp [LocalState.Fits]
    have hμ : net.μ i0 ≠ 0 := (hnet.μ_pos i0 ht).ne'
    rw [if_pos ht]
    simp only [unroute_some, hSi]
    rcases List.eq_nil_or_concat l with rfl | ⟨l', s0, rfl⟩
    · simp [outC, hSi, unenter_fcfs_nil]
    · try simp only [List.concat_eq_append] at hSi ⊢
      have hout : outC net T i0 = net.μ i0 := by
        unfold outC; rw [hSi]; cases l' <;> rfl
      rw [hout]
      simp only [unenter_fcfs_concat]
      rw [Finset.sum_eq_single s0]
      · simp only [if_true, Option.map_some, Option.elim_some]
        rw [F_update]
        unfold pc
        rw [F_self net e T i0, hSi]
        have key := f_fcfs_concat net e i0 hμ l' s0
        linear_combination (net.d T * Fex net e T i0) * key
      · intro s _ hs; rw [if_neg (Ne.symm hs)]; rfl
      · simp
  · have ht : net.type i0 ≠ .fcfs := by
      rw [hSi] at hfit; intro h; rw [h] at hfit; simp [LocalState.Fits] at hfit
    rw [if_neg ht]
    simp [outC, hSi]
  · have ht : net.type i0 ≠ .fcfs := by
      rw [hSi] at hfit; intro h; rw [h] at hfit; simp [LocalState.Fits] at hfit
    rw [if_neg ht]
    simp [outC, hSi]

/-! ## Label: stage -/

lemma ib_stage (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (S : net.State) (i0 : Fin N)
    (r0 : Fin R) (l0 : ℕ) :
    pc net e S.1 * OUT net S.1 (.stage i0 r0 l0) = RIN net e S.1 (.stage i0 r0 l0) +
      DOUT net e S.1 (.stage i0 r0 l0) + ∑ i, ∑ r, ∑ l, vSN net e S.1 (.stage i0 r0 l0) i r l +
      ∑ i, vLN net e S.1 (.stage i0 r0 l0) i := by
  obtain ⟨T, hT⟩ := S
  dsimp only
  have hD : DOUT net e T (.stage i0 r0 l0) = 0 := DOUT_zero net e T _ (fun k => by simp)
  have hSN : ∑ i, ∑ r, ∑ l, vSN net e T (.stage i0 r0 l0) i r l =
      ∑ l, vSN net e T (.stage i0 r0 l0) i0 r0 l := by
    rw [Finset.sum_eq_single i0]
    · rw [Finset.sum_eq_single r0]
      · intro r _ hr; apply Finset.sum_eq_zero; intro l _
        exact vSN_zero net e T _ i0 r l (fun n h => hr (by rw [Label.stage.injEq] at h; exact h.2.1))
      · simp
    · intro i _ hi; apply Finset.sum_eq_zero; intro r _; apply Finset.sum_eq_zero; intro l _
      exact vSN_zero net e T _ i r l (fun n h => hi (by rw [Label.stage.injEq] at h; exact h.1))
    · simp
  have hLN : ∑ i, vLN net e T (.stage i0 r0 l0) i = vLN net e T (.stage i0 r0 l0) i0 := by
    rw [Finset.sum_eq_single i0]
    · intro i _ hi
      exact vLN_zero net e T _ i (fun r n h => hi (by rw [Label.stage.injEq] at h; exact h.1))
    · simp
  have hOUT : OUT net T (.stage i0 r0 l0) =
      (∑ l : Fin (net.u i0 r0), if l.val = l0 then outS net T i0 r0 l else 0) +
        outL net T (.stage i0 r0 l0) i0 := by
    unfold OUT
    have h1 : ∑ j, ∑ s, (if Label.outside (net.chain j s) = Label.stage i0 r0 l0 then
        net.arrivalRate T j s else 0) = 0 := by simp
    have h2 : ∑ i, (if (Label.center i : Label N R m) = Label.stage i0 r0 l0 then
        outC net T i else 0) = 0 := by
      simp
    have h3 : ∑ i, ∑ r, ∑ l : Fin (net.u i r), (if (Label.stage i r l.val : Label N R m) =
        Label.stage i0 r0 l0
        then outS net T i r l else 0) =
        ∑ l : Fin (net.u i0 r0), if l.val = l0 then outS net T i0 r0 l else 0 := by
      rw [Finset.sum_eq_single i0]
      · rw [Finset.sum_eq_single r0]
        · apply Finset.sum_congr rfl; intro l _
          simp only [Label.stage.injEq, true_and]
        · intro r _ hr; apply Finset.sum_eq_zero; intro l _
          rw [if_neg]; rw [Label.stage.injEq]; exact fun h => hr h.2.1
        · simp
      · intro i _ hi; apply Finset.sum_eq_zero; intro r _; apply Finset.sum_eq_zero; intro l _
        rw [if_neg]; rw [Label.stage.injEq]; exact fun h => hi h.1
      · simp
    have h4 : ∑ i, outL net T (.stage i0 r0 l0) i = outL net T (.stage i0 r0 l0) i0 := by
      rw [Finset.sum_eq_single i0]
      · intro i _ hi
        exact outL_zero net T _ i (fun r n h => hi (by rw [Label.stage.injEq] at h; exact h.1))
      · simp
    rw [h1, h2, h3, h4]; ring
  have hRIN : RIN net e T (.stage i0 r0 l0) = if net.type i0 ≠ .fcfs ∧ l0 = 0 then
      (unroute net T (some (i0, r0))).elim 0
        (fun B => net.d T * (∏ i, net.f e i (B i)) * e i0 r0) else 0 := by
    unfold RIN
    rw [Finset.sum_eq_single i0]
    · rw [Finset.sum_eq_single r0]
      · unfold Network.entryLabel
        by_cases ht : net.type i0 = .fcfs
        · simp [ht]
        · simp only [ht, if_false, Label.stage.injEq, true_and, ne_eq, not_false_eq_true]
          by_cases h0 : l0 = 0
          · simp [h0]
          · rw [if_neg (Ne.symm h0), if_neg (by simp [h0])]
      · intro s _ hs; rw [if_neg]; unfold Network.entryLabel
        split_ifs
        · simp
        · rw [Label.stage.injEq]; exact fun h => hs h.2.1
      · simp
    · intro j _ hj; apply Finset.sum_eq_zero; intro s _
      rw [if_neg]; unfold Network.entryLabel
      split_ifs
      · simp
      · rw [Label.stage.injEq]; exact fun h => hj h.1
    · simp
  rw [hD, hSN, hLN, hOUT, hRIN]
  have hfit := hT.1 i0
  rcases hSi : T i0 with lst | w | lst
  · -- type 1 center: everything vanishes
    have ht : net.type i0 = .fcfs := by
      rw [hSi] at hfit; revert hfit; cases net.type i0 <;> simp [LocalState.Fits]
    have e1 : ∀ l, outS net T i0 r0 l = 0 := by intro l; simp only [outS, hSi]
    have e2 : outL net T (.stage i0 r0 l0) i0 = 0 := by simp only [outL, hSi]
    have e3 : ∀ l, vSN net e T (.stage i0 r0 l0) i0 r0 l = 0 := by
      intro l; simp only [vSN, hSi]
    have e4 : vLN net e T (.stage i0 r0 l0) i0 = 0 := by simp only [vLN, hSi]
    simp [e1, e2, e3, e4, ht]
  · -- types 2 and 3
    have ht : net.type i0 ≠ .fcfs := by
      rw [hSi] at hfit; intro h; rw [h] at hfit; simp [LocalState.Fits] at hfit
    have ht' : net.type i0 = .ps ∨ net.type i0 = .is := by
      rw [hSi] at hfit; revert hfit; cases net.type i0 <;> simp [LocalState.Fits]
    have e2 : outL net T (.stage i0 r0 l0) i0 = 0 := by simp only [outL, hSi]
    have e4 : vLN net e T (.stage i0 r0 l0) i0 = 0 := by simp only [vLN, hSi]
    have eS : ∀ l, outS net T i0 r0 l = net.stageRate i0 r0 l w (LocalState.stages w).total := by
      intro l; simp only [outS, hSi]
    rw [e2, e4, add_zero, add_zero]
    simp only [eS]
    have hpos : 0 < (net.u i0 r0 : ℕ) := (net.u i0 r0).pos
    rcases Nat.eq_zero_or_pos l0 with rfl | hl0
    · rw [if_pos ⟨ht, rfl⟩]
      have e3 : ∀ l, vSN net e T (.stage i0 r0 0) i0 r0 l = 0 := by
        intro l; simp [vSN, hSi]
      simp only [e3, Finset.sum_const_zero, add_zero]
      rw [Finset.sum_eq_single (⟨0, hpos⟩ : Fin (net.u i0 r0))]
      · simp only [if_true]
        simp only [unroute_some, hSi, unenter_stages]
        by_cases hw : 0 < w r0 ⟨0, hpos⟩
        · rw [if_pos hw]
          simp only [Option.map_some, Option.elim_some]
          rw [F_update]
          unfold pc
          rw [F_self net e T i0, hSi]
          have hwb : w = addSt (subSt w r0 ⟨0, hpos⟩) r0 ⟨0, hpos⟩ :=
            (addSt_subSt w r0 _ hw).symm
          have key := f_stage_flux net e i0 ht' (subSt w r0 ⟨0, hpos⟩) r0 ⟨0, hpos⟩
            (hnet.μs_pos i0 r0 _ ht).ne'
          rw [← hwb, A_zero] at key
          linear_combination (net.d T * Fex net e T i0) * key
        · rw [if_neg hw]
          rw [stageRate_zero net (by omega)]
          simp
      · intro l _ hl; rw [if_neg]; intro h; exact hl (Fin.ext h)
      · simp
    · rw [if_neg (by omega)]
      by_cases hlt : l0 < (net.u i0 r0 : ℕ)
      · have hl1 : (l0 - 1) + 1 < (net.u i0 r0 : ℕ) := by omega
        set l1 : Fin (net.u i0 r0) := ⟨l0 - 1, by omega⟩ with hl1def
        have hl1' : (⟨l1.val + 1, hl1⟩ : Fin (net.u i0 r0)) = ⟨l0, hlt⟩ := Fin.ext (by
          show l0 - 1 + 1 = l0; omega)
        rw [Finset.sum_eq_single (⟨l0, hlt⟩ : Fin (net.u i0 r0))]
        rotate_left
        · intro l _ hl; rw [if_neg]; intro h; exact hl (Fin.ext h)
        · simp
        rw [if_pos rfl]
        rw [Finset.sum_eq_single l1]
        rotate_left
        · intro l _ hl
          simp only [vSN, hSi, Label.stage.injEq, true_and]
          split_ifs with h1 h2 h3
          · exfalso; apply hl; apply Fin.ext; show _ = l0 - 1; omega
          · simp
          · rfl
          · rfl
        · simp
        simp only [vSN, hSi]
        rw [dif_pos hl1]
        simp only [hl1']
        by_cases hw : 0 < w r0 ⟨l0, hlt⟩
        · have hlab : (Label.stage i0 r0 (l1.val + 1) : Label N R m) = Label.stage i0 r0 l0 := by
            rw [Label.stage.injEq]; refine ⟨rfl, rfl, ?_⟩; show l0 - 1 + 1 = l0; omega
          rw [if_pos hw, if_pos hlab]
          set b := subSt w r0 ⟨l0, hlt⟩ with hb
          have hwb : w = addSt b r0 ⟨l0, hlt⟩ := (addSt_subSt w r0 _ hw).symm
          rw [pc_update]
          have hd : net.d (Function.update T i0 (.stages (addSt b r0 l1))) = net.d T := by
            apply d_same
            intro r'
            rw [hSi, count_addSt, count_subSt w r0 ⟨l0, hlt⟩ hw r']
          rw [hd]
          unfold pc
          rw [F_self net e T i0, hSi]
          have keyA := f_stage_flux net e i0 ht' b r0 l1 (hnet.μs_pos i0 r0 _ ht).ne'
          have keyB := f_stage_flux net e i0 ht' b r0 ⟨l0, hlt⟩ (hnet.μs_pos i0 r0 _ ht).ne'
          rw [← hwb] at keyB
          have hA := A_succ net i0 r0 l1 hl1
          rw [hl1'] at hA
          linear_combination (net.d T * Fex net e T i0) * keyB -
            (net.d T * Fex net e T i0 * net.a i0 r0 l1) * keyA +
            (net.d T * Fex net e T i0 * net.f e i0 (.stages b) * e i0 r0) * hA
        · rw [if_neg hw, stageRate_zero net (by omega)]
          simp
      · have z1 : ∑ l : Fin (net.u i0 r0), (if l.val = l0 then
            net.stageRate i0 r0 l w (LocalState.stages w).total else 0) = 0 := by
          apply Finset.sum_eq_zero; intro l _; rw [if_neg]; have := l.isLt; omega
        have z2 : ∑ l, vSN net e T (.stage i0 r0 l0) i0 r0 l = 0 := by
          apply Finset.sum_eq_zero; intro l _
          simp only [vSN, hSi, Label.stage.injEq, true_and]
          split_ifs with h1 h2 h3
          · exfalso; omega
          · simp
          · rfl
          · rfl
        rw [z1, z2]; simp
  · -- type 4
    have ht : net.type i0 ≠ .fcfs := by
      rw [hSi] at hfit; intro h; rw [h] at hfit; simp [LocalState.Fits] at hfit
    have e1 : ∀ l, outS net T i0 r0 l = 0 := by intro l; simp only [outS, hSi]
    have e3 : ∀ l, vSN net e T (.stage i0 r0 l0) i0 r0 l = 0 := by
      intro l; simp only [vSN, hSi]
    simp only [e1, e3, ite_self, Finset.sum_const_zero, zero_add, add_zero]
    rcases lst with _ | ⟨⟨xr, xl⟩, rest⟩
    · simp [outL, vLN, hSi, unroute_some, unenter_lcfs_nil]
    · simp only [outL, vLN, hSi, unroute_some, unenter_lcfs_cons]
      by_cases hm : xr = r0 ∧ xl.val = l0
      · obtain ⟨rfl, rfl⟩ := hm
        simp only [if_true]
        by_cases hz : xl.val = 0
        · have hA : net.A i0 xr xl = 1 := by
            rw [show xl = ⟨0, by omega⟩ from Fin.ext hz]; exact A_zero net i0 xr _
          simp only [hz, lt_self_iff_false, if_false, and_self, ht, ne_eq, not_false_eq_true,
            if_true, Option.map_some, Option.elim_some, add_zero]
          rw [F_update]
          unfold pc
          rw [F_self net e T i0, hSi]
          have key := f_lcfs_cons net e i0 xr xl rest (hnet.μs_pos i0 xr xl ht).ne'
          linear_combination (net.d T * Fex net e T i0) * key +
            (net.d T * Fex net e T i0 * net.f e i0 (.lcfs rest) * e i0 xr) * hA
        · have hpos : 0 < xl.val := by omega
          rw [if_neg (by tauto), if_pos hpos]
          simp only [zero_add]
          have hp1 : (predFin xl).val + 1 < (net.u i0 xr : ℕ) := by
            simp only [predFin]; have := xl.isLt; omega
          have hA := A_succ net i0 xr (predFin xl) hp1
          rw [show (⟨(predFin xl).val + 1, hp1⟩ : Fin (net.u i0 xr)) = xl from
            Fin.ext (by simp only [predFin]; omega)] at hA
          rw [pc_update]
          have hd : net.d (Function.update T i0
              (.lcfs (⟨xr, predFin xl⟩ :: rest))) = net.d T := by
            apply d_same
            intro r'
            rw [hSi, count_lcfs_cons, count_lcfs_cons]
          rw [hd]
          unfold pc
          rw [F_self net e T i0, hSi]
          have keyA := f_lcfs_cons net e i0 xr (predFin xl) rest (hnet.μs_pos i0 xr _ ht).ne'
          have keyB := f_lcfs_cons net e i0 xr xl rest (hnet.μs_pos i0 xr xl ht).ne'
          linear_combination (net.d T * Fex net e T i0) * keyB -
            (net.d T * Fex net e T i0 * net.a i0 xr (predFin xl)) * keyA +
            (net.d T * Fex net e T i0 * net.f e i0 (.lcfs rest) * e i0 xr) * hA
      · have hne : ¬ ((Label.stage i0 xr xl.val : Label N R m) = Label.stage i0 r0 l0) := by
          rw [Label.stage.injEq]; tauto
        have hE : ¬ (xr = r0 ∧ xl.val = 0 ∧ l0 = 0) := by
          rintro ⟨h1, h2, h3⟩; exact hm ⟨h1, by omega⟩
        rw [if_neg hne]
        simp only [if_neg hne, mul_zero, ite_self, add_zero]
        split_ifs with h1 h2
        · exfalso; exact hE ⟨h2.1, h2.2, h1.2⟩
        · simp
        · rfl

end BCMPNetworks.Core.P54b

open BCMPNetworks.Core in
theorem solution {N R m : ℕ} (net : Network N R m)
    (hnet : net.IsValid) (e : Fin N → Fin R → ℝ) (he : ∀ i r, 0 ≤ e i r)
    (htraffic : net.TrafficEquations e) :
    net.IndependentBalance (net.productForm e) := by
  intro S L
  rw [P54b.lhs_val net S.1 L, (P54b.rhs_hasSum net hnet e S L).tsum_eq,
    P54b.rhs_val net hnet e htraffic S L]
  cases L with
  | outside k => exact P54b.ib_outside net hnet e htraffic S k
  | center i => exact P54b.ib_center net hnet e S i
  | stage i r l => exact P54b.ib_stage net hnet e S i r l
