-- Prove2me | solution 1 for DistVerif.Simulation.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @rgmohan
-- created : 2026-10-27T06:36:58.905071+00:00
-- url     : https://prove2.me/submissions/540a2eaa-7b63-463f-821e-3d72830ce85a

import Mathlib
import Definitions.Def_DistVerif_Simulation_Network
import Definitions.Def_DistVerif_Simulation_Algorithm
import Theorems.Thm_DistVerif_Simulation_observation_3_3
import Theorems.Thm_DistVerif_Simulation_compl_R_subset_L
import Theorems.Thm_DistVerif_Simulation_cut_edges_le

open DistVerif.Simulation

/-! Proof of `DistVerif.Simulation.lemma_3_4` (Das Sarma et al., Lemma 3.4), as a reduction to
three proved milestones: `observation_3_3`, `compl_R_subset_L` and `cut_edges_le`.

`step_generic` is the one-round simulation step for arbitrary regions `Old ⊇ New` and a helper
region `Help ⊇ V \ Old`: if at most `n` edges enter `New` from outside `Old`, list them in `n`
slots, and let the update rule `g` be "pick any inputs consistent with what I know and the slot
messages, and report their round-`t` states on `New`". Observation 3.3 makes this choice-free
in effect: all consistent inputs give the same states. Bob's half uses
`(Old, New, Help) = (R_{t-1}, R_t, L_{t-1})`; Alice's uses `(L_{t-1}, L_t, R_{t-1})`. -/

namespace Lemma34Aux

/-- The one-round step, for any regions. -/
theorem step_generic {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s r : V) {B b : ℕ} (A : DetAlg V B b) (t : ℕ) (ht0 : 0 < t)
    (Old New Help : Finset V) (hsub : New ⊆ Old) (hhelp : Oldᶜ ⊆ Help) (n : ℕ)
    (hcard : (Finset.univ.filter fun q : V × V =>
        G.Adj q.1 q.2 ∧ q.1 ∉ Old ∧ q.2 ∈ New).card ≤ n) :
    ∃ e : Fin n → Option (V × V),
      ∃ g : (↥Old → A.State) → (Fin n → Msg B) → (↥New → A.State),
        (∀ i w u, e i = some (w, u) → w ∈ Help ∧ G.Adj w u) ∧
        ∀ x y : Fin b → Bool,
          (fun v : ↥New => A.exec G s r x y t v) =
            g (fun v : ↥Old => A.exec G s r x y (t - 1) v)
              (fun i => match e i with
                | some (w, u) => A.send w u (A.exec G s r x y (t - 1) w)
                | none => fun _ => false) := by
  classical
  -- The crossing edges, listed in a fixed order; slot `i` holds the `i`-th one (or nothing).
  set S := Finset.univ.filter fun q : V × V => G.Adj q.1 q.2 ∧ q.1 ∉ Old ∧ q.2 ∈ New with hS
  let e : Fin n → Option (V × V) := fun i => S.toList[(i : ℕ)]?
  -- What the simulator knows after round `t - 1`, and the slot messages, as functions of inputs.
  let old : (Fin b → Bool) → (Fin b → Bool) → (↥Old → A.State) :=
    fun x y v => A.exec G s r x y (t - 1) v
  let msgs : (Fin b → Bool) → (Fin b → Bool) → (Fin n → Msg B) := fun x y i =>
    match e i with
    | some (w, u) => A.send w u (A.exec G s r x y (t - 1) w)
    | none => fun _ => false
  let new : (Fin b → Bool) → (Fin b → Bool) → (↥New → A.State) :=
    fun x y v => A.exec G s r x y t v
  -- The update rule: any inputs consistent with `(c, m)` give the answer.
  let g : (↥Old → A.State) → (Fin n → Msg B) → (↥New → A.State) := fun c m =>
    if h : ∃ xy : (Fin b → Bool) × (Fin b → Bool), old xy.1 xy.2 = c ∧ msgs xy.1 xy.2 = m
    then new h.choose.1 h.choose.2
    else fun v => A.initO v
  -- Every crossing edge sits in some slot.
  have hslot : ∀ q ∈ S, ∃ i : Fin n, e i = some q := by
    intro q hq
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (Finset.mem_toList.mpr hq)
    have hlt : k < S.toList.length := (List.getElem?_eq_some_iff.mp hk).1
    rw [Finset.length_toList] at hlt
    exact ⟨⟨k, lt_of_lt_of_le hlt hcard⟩, hk⟩
  refine ⟨e, g, ?_, ?_⟩
  · -- Slot edges are crossing edges, so their tails lie outside `Old`, hence in `Help`.
    intro i w u hi
    have hmem : (w, u) ∈ S := Finset.mem_toList.mp (List.mem_of_getElem? hi)
    rw [hS, Finset.mem_filter] at hmem
    obtain ⟨-, hadj, hw, -⟩ := hmem
    exact ⟨hhelp (Finset.mem_compl.mpr hw), hadj⟩
  · intro x y
    have hex : ∃ xy : (Fin b → Bool) × (Fin b → Bool),
        old xy.1 xy.2 = old x y ∧ msgs xy.1 xy.2 = msgs x y := ⟨(x, y), rfl, rfl⟩
    show new x y = g (old x y) (msgs x y)
    simp only [g, dif_pos hex]
    obtain ⟨hc, hm⟩ := hex.choose_spec
    set x' := hex.choose.1
    set y' := hex.choose.2
    -- Observation 3.3 with `U = New`, `U' = Old`: the two runs agree on `New` after round `t`.
    have hobs := observation_3_3 G s r A (↑New : Set V) (↑Old : Set V)
      (Finset.coe_subset.mpr hsub) x y x' y' (t - 1)
      (fun v hv => (congrFun hc ⟨v, Finset.mem_coe.mp hv⟩).symm)
      (fun w u hw hu hadj => by
        have hq : (w, u) ∈ S := by
          rw [hS, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hadj, fun h => hw (Finset.mem_coe.mpr h),
            Finset.mem_coe.mp hu⟩
        obtain ⟨i, hi⟩ := hslot (w, u) hq
        have := congrFun hm i
        simp only [msgs, hi] at this
        exact this.symm)
    rw [Nat.sub_add_cancel ht0] at hobs
    funext v
    exact hobs v.1 (Finset.mem_coe.mpr v.2)

/-- `R_t ⊆ R_{t-1}` for `t ≥ 1`. -/
theorem R_mono (Γ d p t : ℕ) (ht0 : 0 < t) : R Γ d p t ⊆ R Γ d p (t - 1) := by
  intro v hv
  simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  rcases v with ⟨a, j⟩ | ⟨ℓ, k⟩
  · simp only [InRight] at hv ⊢; omega
  · simp only [InRight, if_neg (show t ≠ 0 by omega)] at hv ⊢
    obtain ⟨j, hj, hjk⟩ := hv
    by_cases h0 : t - 1 = 0
    · -- `R_0 = V \ {s}`; a node with a leaf `≥ 1` below it is not the leaf `s = u^p_0`.
      simp only [h0, if_true]
      rintro ⟨hl, hk⟩
      have h3 : d ^ (p - (ℓ : ℕ)) = 1 := by rw [hl, Nat.sub_self, pow_zero]
      rw [h3, Nat.div_one] at hjk
      omega
    · simp only [h0, if_false]
      exact ⟨j, by omega, hjk⟩

/-- `L_t ⊆ L_{t-1}` for `t ≥ 1`. -/
theorem L_mono (Γ d p t : ℕ) (ht0 : 0 < t) : L Γ d p t ⊆ L Γ d p (t - 1) := by
  intro v hv
  simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  rcases v with ⟨a, j⟩ | ⟨ℓ, k⟩
  · simp only [InLeft] at hv ⊢; omega
  · simp only [InLeft, if_neg (show t ≠ 0 by omega)] at hv ⊢
    obtain ⟨j, hj, hjk⟩ := hv
    by_cases h0 : t - 1 = 0
    · -- `L_0 = V \ {r}`; a node with a leaf `< d^p - 1` below it is not the leaf `r`.
      simp only [h0, if_true]
      rintro ⟨hl, hk⟩
      have h3 : d ^ (p - (ℓ : ℕ)) = 1 := by rw [hl, Nat.sub_self, pow_zero]
      rw [h3, Nat.div_one] at hjk
      omega
    · simp only [h0, if_false]
      exact ⟨j, by omega, hjk⟩

end Lemma34Aux

theorem solution (Γ d p B b : ℕ) (hdp : 0 < d ^ p) (A : DetAlg (Vtx Γ d p) B b)
    (t : ℕ) (ht0 : 0 < t) (ht : (t : ℝ) < ((d : ℝ) ^ p - 1) / 2) :
    (∃ eL : Fin (d * p) → Option (Vtx Γ d p × Vtx Γ d p),
      ∃ gL : (↥(L Γ d p (t - 1)) → A.State) → (Fin (d * p) → Msg B) → (↥(L Γ d p t) → A.State),
        (∀ i w u, eL i = some (w, u) → w ∈ R Γ d p (t - 1) ∧ (graph Γ d p).Adj w u) ∧
        ∀ x y : Fin b → Bool,
          (fun v : ↥(L Γ d p t) =>
              A.exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) x y t v) =
            gL (fun v : ↥(L Γ d p (t - 1)) =>
                  A.exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) x y (t - 1) v)
               (fun i => match eL i with
                 | some (w, u) => A.send w u
                     (A.exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) x y (t - 1) w)
                 | none => fun _ => false)) ∧
    (∃ eR : Fin (d * p) → Option (Vtx Γ d p × Vtx Γ d p),
      ∃ gR : (↥(R Γ d p (t - 1)) → A.State) → (Fin (d * p) → Msg B) → (↥(R Γ d p t) → A.State),
        (∀ i w u, eR i = some (w, u) → w ∈ L Γ d p (t - 1) ∧ (graph Γ d p).Adj w u) ∧
        ∀ x y : Fin b → Bool,
          (fun v : ↥(R Γ d p t) =>
              A.exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) x y t v) =
            gR (fun v : ↥(R Γ d p (t - 1)) =>
                  A.exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) x y (t - 1) v)
               (fun i => match eR i with
                 | some (w, u) => A.send w u
                     (A.exec (graph Γ d p) (sNode Γ d p hdp) (rNode Γ d p hdp) x y (t - 1) w)
                 | none => fun _ => false)) := by
  obtain ⟨hcR, hcL⟩ := compl_R_subset_L Γ d p t ht0 ht
  obtain ⟨hnR, hnL⟩ := cut_edges_le Γ d p t ht0 ht
  -- Alice's half: `(Old, New, Help) = (L_{t-1}, L_t, R_{t-1})`; Bob's: `(R_{t-1}, R_t, L_{t-1})`.
  -- The two `match` expressions are separately elaborated, so we rematch them slot by slot.
  obtain ⟨eL, gL, hL1, hL2⟩ := Lemma34Aux.step_generic (graph Γ d p) (sNode Γ d p hdp)
    (rNode Γ d p hdp) A t ht0 (L Γ d p (t - 1)) (L Γ d p t) (R Γ d p (t - 1))
    (Lemma34Aux.L_mono Γ d p t ht0) hcL (d * p) hnL
  obtain ⟨eR, gR, hR1, hR2⟩ := Lemma34Aux.step_generic (graph Γ d p) (sNode Γ d p hdp)
    (rNode Γ d p hdp) A t ht0 (R Γ d p (t - 1)) (R Γ d p t) (L Γ d p (t - 1))
    (Lemma34Aux.R_mono Γ d p t ht0) hcR (d * p) hnR
  refine ⟨⟨eL, gL, hL1, fun x y => ?_⟩, ⟨eR, gR, hR1, fun x y => ?_⟩⟩
  · rw [hL2 x y]; congr 1; funext i
    rcases eL i with _ | ⟨w, u⟩ <;> rfl
  · rw [hR2 x y]; congr 1; funext i
    rcases eR i with _ | ⟨w, u⟩ <;> rfl
