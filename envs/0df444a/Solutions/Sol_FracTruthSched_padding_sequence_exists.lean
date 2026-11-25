-- Prove2me | solution 1 for FracTruthSched.padding_sequence_exists
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-25T19:46:27.0434+00:00
-- url     : https://prove2.me/submissions/2d024a31-5e8e-48dc-9426-b2bd028496b3

import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_opt
import Definitions.Def_FracTruthSched_PaddingSequence
import Definitions.Def_FracTruthSched_relabel
import Definitions.Def_FracTruthSched_disutility

/-!
Construction (App. A.1 of Anastasiadis et al.), stage `K`, with `N = K + 1`:
* padded task type `T K = CoreTask ⊕ (Res K ⊕ Unit)`, where `Res K = Pair × Ty K × Fin (2N+2)` are
  reservoir slots; `Ty K = Bool × Fin (N+1) × Fin (N+1)` are zero types `(r,0)` / `(0,r)`,
  `r = a/(b+1)`. A count vector `κ : Pair × Ty K → ℕ` activates the first `κ(p,τ)` slots of type `τ`;
  inactive slots are all-zero tasks. The extra task has value `β = 1/N` on every machine; core
  non-incident entries get `H = N²`.
* base mechanism on `T K`: `R m` transported along `T K ≃ Fin m` (fixed `m`, independent of `κ`).
* symmetrize over the label-preserving permutations (edges stay in their class, loops fixed).
* `M K` = average over `κ ∈ [N, 2N]^d` of the symmetrized allocation on core tasks; payments minus
  the cost on fixed (non-core-incident) entries.
* load / eligibility: padded load ≤ ρ'·opt ≤ ρ'(C + β). unique zeros: `≥ N` reservoir copies
  identical to `e` (swap symmetry). zero-type irrelevance: a 3-cycle relabelling identifies
  `(t,κ)` with `(t', κ + 1_τ - 1_σ)`; shifting a box average by a unit vector costs `≤ 1/(N+1)`.
No platform theorems are imported; `hℓ` is not needed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FracTruthSched.FTSPE

open Finset

variable {n : ℕ}

/-! ### Transport along a task equivalence -/
section Transport
variable {τ σ : Type*} [Fintype τ] [Fintype σ]

def pre (E : τ ≃ σ) (s : Fin n → τ → ℝ) : Fin n → σ → ℝ := fun i k => s i (E.symm k)

def transport (E : τ ≃ σ) (X : FracMech n σ) : FracMech n τ where
  x s i a := X.x (pre E s) i (E a)
  P s i := X.P (pre E s) i

theorem pre_update (E : τ ≃ σ) (s : Fin n → τ → ℝ) (i : Fin n) (b : τ → ℝ) :
    pre E (Function.update s i b) = Function.update (pre E s) i (fun k => b (E.symm k)) := by
  funext j k
  rcases eq_or_ne j i with rfl | h
  · simp [pre]
  · simp [pre, Function.update_of_ne h]

theorem nonneg_pre (E : τ ≃ σ) {s : Fin n → τ → ℝ} (hs : Nonneg s) : Nonneg (pre E s) :=
  fun i k => hs i _

theorem transport_feasible (E : τ ≃ σ) {X : FracMech n σ} (h : IsFeasibleOn Nonneg X) :
    IsFeasibleOn Nonneg (transport E X) := by
  intro s hs
  obtain ⟨h1, h2⟩ := h _ (nonneg_pre E hs)
  exact ⟨fun i a => h1 i (E a), fun a => h2 (E a)⟩

theorem cost_transport (E : τ ≃ σ) (X : FracMech n σ) (r : τ → ℝ) (s : Fin n → τ → ℝ)
    (i : Fin n) :
    ∑ a, r a * (transport E X).x s i a = ∑ k, r (E.symm k) * X.x (pre E s) i k := by
  rw [← E.sum_comp]
  simp [transport]

theorem transport_truthful (E : τ ≃ σ) {X : FracMech n σ} (h : IsTruthfulOn Nonneg X) :
    IsTruthfulOn Nonneg (transport E X) := by
  intro s hs i b hb
  have hb' : Nonneg (Function.update (pre E s) i (fun k => b (E.symm k))) := by
    rw [← pre_update]; exact nonneg_pre E hb
  have key := h (pre E s) (nonneg_pre E hs) i _ hb'
  rw [cost_transport E X (s i), cost_transport E X (s i)]
  simp only [transport, pre_update]
  exact key

theorem transport_load [NeZero n] (E : τ ≃ σ) (X : FracMech n σ) (s : Fin n → τ → ℝ)
    (i : Fin n) : ∑ a, s i a * (transport E X).x s i a ≤ makespan X (pre E s) := by
  rw [cost_transport]
  exact Finset.le_sup' (fun i => ∑ j, pre E s i j * X.x (pre E s) i j) (Finset.mem_univ i)

end Transport

/-! ### Symmetrization over a finite group of task permutations -/
section Symm
variable {τ : Type*} [Fintype τ] [DecidableEq τ]

theorem relabel_update (π : Equiv.Perm τ) (s : Fin n → τ → ℝ) (i : Fin n) (b : τ → ℝ) :
    relabel π (Function.update s i b) = Function.update (relabel π s) i (fun a => b (π a)) := by
  funext j k
  rcases eq_or_ne j i with rfl | h
  · simp [relabel]
  · simp [relabel, Function.update_of_ne h]

theorem relabel_relabel (π γ : Equiv.Perm τ) (s : Fin n → τ → ℝ) :
    relabel π (relabel γ s) = relabel (γ * π) s := rfl

theorem nonneg_relabel (π : Equiv.Perm τ) {s : Fin n → τ → ℝ} (hs : Nonneg s) :
    Nonneg (relabel π s) := fun i a => hs i _

variable (G : Subgroup (Equiv.Perm τ)) [Fintype G]

noncomputable def symm (X : FracMech n τ) : FracMech n τ where
  x s i a := (1 / (Fintype.card G : ℝ)) * ∑ π : G, X.x (relabel π.1 s) i (π.1⁻¹ a)
  P s i := (1 / (Fintype.card G : ℝ)) * ∑ π : G, X.P (relabel π.1 s) i

theorem card_G_pos : (0 : ℝ) < Fintype.card G := by
  exact_mod_cast Fintype.card_pos

theorem cost_symm (X : FracMech n τ) (r : τ → ℝ) (s : Fin n → τ → ℝ) (i : Fin n) :
    ∑ a, r a * (symm G X).x s i a =
      (1 / (Fintype.card G : ℝ)) * ∑ π : G, ∑ a, r (π.1 a) * X.x (relabel π.1 s) i a := by
  simp only [symm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Equiv.sum_comp (π.1 : τ ≃ τ)]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp
  ring

theorem symm_feasible {X : FracMech n τ} (h : IsFeasibleOn Nonneg X) :
    IsFeasibleOn Nonneg (symm G X) := by
  intro s hs
  have hc := card_G_pos G
  have hX := fun π : G => h (relabel π.1 s) (nonneg_relabel _ hs)
  refine ⟨fun i a => ⟨?_, ?_⟩, fun a => ?_⟩
  · simp only [symm]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun π _ => ((hX π).1 i _).1)
  · simp only [symm]
    rw [div_mul_eq_mul_div, one_mul, div_le_one hc]
    calc ∑ π : G, X.x (relabel π.1 s) i (π.1⁻¹ a) ≤ ∑ _π : G, (1 : ℝ) :=
          Finset.sum_le_sum fun π _ => ((hX π).1 i _).2
      _ = Fintype.card G := by simp
  · simp only [symm]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [fun π : G => (hX π).2 (π.1⁻¹ a)]
    simp [hc.ne']

theorem symm_truthful {X : FracMech n τ} (h : IsTruthfulOn Nonneg X) :
    IsTruthfulOn Nonneg (symm G X) := by
  intro s hs i b hb
  rw [cost_symm, cost_symm]
  have hc := card_G_pos G
  simp only [symm]
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun π _ => ?_) (by positivity)
  have hb' : Nonneg (Function.update (relabel π.1 s) i (fun a => b (π.1 a))) := by
    rw [← relabel_update]; exact nonneg_relabel _ hb
  have key := h (relabel π.1 s) (nonneg_relabel _ hs) i _ hb'
  rw [relabel_update]
  exact key

theorem symm_equivariant (X : FracMech n τ) {γ : Equiv.Perm τ} (hγ : γ ∈ G)
    (s : Fin n → τ → ℝ) (i : Fin n) (a : τ) :
    (symm G X).x (relabel γ s) i a = (symm G X).x s i (γ a) ∧
      (symm G X).P (relabel γ s) i = (symm G X).P s i := by
  constructor
  · simp only [symm]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨γ, hγ⟩ : G)) _ _ fun π => ?_
    simp [relabel_relabel, Equiv.Perm.mul_apply, mul_inv_rev]
  · simp only [symm]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨γ, hγ⟩ : G)) _ _ fun π => ?_
    simp [relabel_relabel]

end Symm

/-! ### Generic bounds on `opt` -/
section OptBounds
variable [NeZero n] {τ τ' : Type*} [Fintype τ] [Fintype τ'] [DecidableEq τ] [DecidableEq τ']

theorem sched_comp (g : τ' ≃ τ) (s : Fin n → τ → ℝ) (σ : τ → Fin n) :
    schedMakespan (fun i k => s i (g k)) (fun k => σ (g k)) = schedMakespan s σ := by
  unfold schedMakespan
  congr 1
  funext i
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Equiv.sum_comp g (fun a => if σ a = i then s i a else 0)

theorem opt_comp_le (g : τ' ≃ τ) (s : Fin n → τ → ℝ) (σ : τ → Fin n) :
    opt (fun i k => s i (g k)) ≤ schedMakespan s σ := by
  rw [← sched_comp g s σ]
  exact Finset.inf'_le _ (Finset.mem_univ _)

theorem opt_pos_of (s : Fin n → τ → ℝ) (hs : Nonneg s) (a0 : τ) (β : ℝ) (hβ : 0 < β)
    (h0 : ∀ i, β ≤ s i a0) : 0 < opt s := by
  unfold opt
  rw [Finset.lt_inf'_iff]
  intro σ _
  unfold schedMakespan
  refine lt_of_lt_of_le hβ (le_trans (h0 (σ a0)) ?_)
  refine le_trans ?_ (Finset.le_sup' (fun i => ∑ j ∈ Finset.univ.filter (fun j => σ j = i), s i j)
    (Finset.mem_univ (σ a0)))
  exact Finset.single_le_sum (f := fun j => s (σ a0) j) (fun j _ => hs _ _)
    (by simp)

end OptBounds

def Valid (R : (m : ℕ) → FracMech n (Fin m)) (ρ' : ℝ) [NeZero n] : Prop :=
  ∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t → makespan (R m) t ≤ ρ' * opt t

/-! ### The padded instance -/
section Padding

abbrev Pair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Ty (K : ℕ) := Bool × Fin (K + 2) × Fin (K + 2)
abbrev Idx (n K : ℕ) := Pair n × Ty K
abbrev Res (n K : ℕ) := Idx n K × Fin (2 * K + 4)
abbrev T (n ℓ K : ℕ) := CoreTask n ℓ ⊕ (Res n K ⊕ Unit)

instance instDecEqT (n ℓ K : ℕ) : DecidableEq (T n ℓ K) :=
  @instDecidableEqSum _ _ inferInstance (@instDecidableEqSum _ _ inferInstance inferInstance)

variable {ℓ K : ℕ}

noncomputable def rval (τ : Ty K) : ℝ := (τ.2.1 : ℝ) / ((τ.2.2 : ℝ) + 1)
noncomputable def tyv1 (τ : Ty K) : ℝ := if τ.1 then rval τ else 0
noncomputable def tyv2 (τ : Ty K) : ℝ := if τ.1 then 0 else rval τ

noncomputable def Hc (K : ℕ) : ℝ := ((K : ℝ) + 1) ^ 2
noncomputable def βc (K : ℕ) : ℝ := 1 / ((K : ℝ) + 1)

theorem rval_nonneg (τ : Ty K) : 0 ≤ rval τ := by unfold rval; positivity
theorem tyv1_nonneg (τ : Ty K) : 0 ≤ tyv1 τ := by unfold tyv1; split_ifs <;> simp [rval_nonneg]
theorem tyv2_nonneg (τ : Ty K) : 0 ≤ tyv2 τ := by unfold tyv2; split_ifs <;> simp [rval_nonneg]
theorem Hc_pos (K : ℕ) : 0 < Hc K := by unfold Hc; positivity
theorem βc_pos (K : ℕ) : 0 < βc K := by unfold βc; positivity

noncomputable def slotVal (K : ℕ) (κ : Idx n K → ℕ) (i : Fin n) (c : Res n K) : ℝ :=
  if (c.2 : ℕ) < κ c.1 then
    (if i = c.1.1.1.1 then tyv1 c.1.2 else if i = c.1.1.1.2 then tyv2 c.1.2 else Hc K)
  else 0

noncomputable def rowmap (K : ℕ) (κ : Idx n K → ℕ) (i : Fin n) (r : CoreTask n ℓ → ℝ) :
    T n ℓ K → ℝ
  | .inl e => r e + if incident i e then 0 else Hc K
  | .inr (.inl c) => slotVal K κ i c
  | .inr (.inr _) => βc K

noncomputable def pad (K : ℕ) (κ : Idx n K → ℕ) (t : Fin n → CoreTask n ℓ → ℝ) :
    Fin n → T n ℓ K → ℝ := fun i => rowmap K κ i (t i)

theorem pad_update (κ : Idx n K → ℕ) (t : Fin n → CoreTask n ℓ → ℝ) (i : Fin n)
    (b : CoreTask n ℓ → ℝ) :
    pad K κ (Function.update t i b) = Function.update (pad K κ t) i (rowmap K κ i b) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp [pad]
  · simp [pad, Function.update_of_ne h]

theorem slotVal_nonneg (κ : Idx n K → ℕ) (i : Fin n) (c : Res n K) : 0 ≤ slotVal K κ i c := by
  unfold slotVal
  split_ifs <;> simp [tyv1_nonneg, tyv2_nonneg, (Hc_pos K).le]

theorem rowmap_nonneg (κ : Idx n K → ℕ) (i : Fin n) {r : CoreTask n ℓ → ℝ} (hr : ∀ e, 0 ≤ r e) :
    ∀ a, 0 ≤ rowmap K κ i r a
  | .inl e => by
      simp only [rowmap]; have := hr e; split_ifs <;> linarith [Hc_pos K]
  | .inr (.inl c) => slotVal_nonneg κ i c
  | .inr (.inr _) => (βc_pos K).le

theorem pad_nonneg (κ : Idx n K → ℕ) {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t) :
    Nonneg (pad K κ t) := fun i => rowmap_nonneg κ i (fun e => (ht i e).1)

/-- The label of a padded task: edges (core or reservoir) carry their machine pair,
every other task is labelled by itself. -/
def lab : T n ℓ K → Pair n ⊕ T n ℓ K
  | .inl (.inl q) => .inl q.1
  | .inl (.inr i) => .inr (.inl (.inr i))
  | .inr (.inl c) => .inl c.1.1
  | .inr (.inr u) => .inr (.inr (.inr u))

theorem lab_inr {a b : T n ℓ K} (h : lab b = .inr a) : b = a := by
  rcases b with (q | i) | (c | u) <;> simp [lab] at h ⊢ <;> exact h

def G (n ℓ K : ℕ) : Subgroup (Equiv.Perm (T n ℓ K)) where
  carrier := {γ | ∀ a, lab (γ a) = lab a}
  mul_mem' := by
    intro γ δ hγ hδ a
    simp only [Set.mem_ofPred_eq] at hγ hδ
    rw [Equiv.Perm.mul_apply, hγ, hδ]
  one_mem' := by intro a; rfl
  inv_mem' := by
    intro γ hγ a
    simp only [Set.mem_ofPred_eq] at hγ
    rw [← hγ (γ⁻¹ a)]
    simp

noncomputable instance (n ℓ K : ℕ) : Fintype (G n ℓ K) := Fintype.ofFinite _

theorem mem_G {γ : Equiv.Perm (T n ℓ K)} : γ ∈ G n ℓ K ↔ ∀ a, lab (γ a) = lab a := Iff.rfl

end Padding

/-! ### The padded symmetrized base mechanism -/
section Base
variable [NeZero n] (R : (m : ℕ) → FracMech n (Fin m)) {ℓ : ℕ}

noncomputable def Xs (ℓ K : ℕ) : FracMech n (T n ℓ K) :=
  symm (G n ℓ K) (transport (Fintype.equivFin (T n ℓ K)) (R (Fintype.card (T n ℓ K))))

theorem Xs_feasible (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (K : ℕ) :
    IsFeasibleOn Nonneg (Xs R ℓ K) :=
  symm_feasible _ (transport_feasible _ (hfeas _))

theorem Xs_truthful (htruth : ∀ m, IsTruthfulOn Nonneg (R m)) (K : ℕ) :
    IsTruthfulOn Nonneg (Xs R ℓ K) :=
  symm_truthful _ (transport_truthful _ (htruth _))

theorem Xs_equivariant (K : ℕ) {γ : Equiv.Perm (T n ℓ K)} (hγ : γ ∈ G n ℓ K)
    (s : Fin n → T n ℓ K → ℝ) (i : Fin n) (a : T n ℓ K) :
    (Xs R ℓ K).x (relabel γ s) i a = (Xs R ℓ K).x s i (γ a) ∧
      (Xs R ℓ K).P (relabel γ s) i = (Xs R ℓ K).P s i :=
  symm_equivariant _ _ hγ s i a

/-- Padded load of the symmetrized mechanism, given a uniform bound on `opt` of the relabelled
transported instances. -/
theorem Xs_load_of (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (K : ℕ) {ρ' : ℝ} (hρ' : Valid R ρ')
    (s : Fin n → T n ℓ K → ℝ) (hs : Nonneg s) (B : ℝ)
    (hB : ∀ π : G n ℓ K, 0 < opt (pre (Fintype.equivFin (T n ℓ K)) (relabel π.1 s)) ∧
      opt (pre (Fintype.equivFin (T n ℓ K)) (relabel π.1 s)) ≤ B) (i : Fin n) :
    ∑ a, s i a * (Xs R ℓ K).x s i a ≤ ρ' * B := by
  unfold Xs
  rw [cost_symm]
  have hc := card_G_pos (G n ℓ K)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hc]
  calc _ ≤ ∑ _π : G n ℓ K, ρ' * B := by
        refine Finset.sum_le_sum fun π _ => ?_
        set E := Fintype.equivFin (T n ℓ K)
        set s' := relabel π.1 s
        have h1 := transport_load E (R (Fintype.card (T n ℓ K))) s' i
        have h2 := hρ' _ (pre E s') (nonneg_pre E (nonneg_relabel _ hs)) (hB π).1
        have h0 : 0 ≤ ∑ a, s' i a * (transport E (R (Fintype.card (T n ℓ K)))).x s' i a :=
          Finset.sum_nonneg fun a _ => mul_nonneg (nonneg_relabel _ hs i a)
            (((transport_feasible E (hfeas _)) s' (nonneg_relabel _ hs)).1 i a).1
        have hρ0 : 0 ≤ ρ' := by
          by_contra hneg
          push Not at hneg
          have := mul_neg_of_neg_of_pos hneg (hB π).1
          linarith
        calc _ = ∑ a, s' i a * (transport E (R (Fintype.card (T n ℓ K)))).x s' i a := rfl
          _ ≤ ρ' * opt (pre E s') := h1.trans h2
          _ ≤ ρ' * B := mul_le_mul_of_nonneg_left (hB π).2 hρ0
    _ = ρ' * B * Fintype.card (G n ℓ K) := by simp [mul_comm]

end Base

/-! ### `opt` of the padded instance -/
section PadOpt
variable [NeZero n] {ℓ K : ℕ}

def σ0 (σs : CoreTask n ℓ → Fin n) : T n ℓ K → Fin n
  | .inl e => σs e
  | .inr (.inl c) => if c.1.2.1 then c.1.1.1.2 else c.1.1.1.1
  | .inr (.inr _) => 0

theorem sched_pad_le (κ : Idx n K → ℕ) {t : Fin n → CoreTask n ℓ → ℝ} (σs : CoreTask n ℓ → Fin n)
    (hσ : ∀ e, incident (σs e) e) :
    schedMakespan (pad K κ t) (σ0 σs) ≤ schedMakespan t σs + βc K := by
  unfold schedMakespan
  refine Finset.sup'_le _ _ fun i _ => ?_
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  have hcore : ∑ e, (if σ0 (K := K) σs (Sum.inl e) = i then pad K κ t i (Sum.inl e) else 0) =
      ∑ e ∈ Finset.univ.filter (fun e => σs e = i), t i e := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : σs e = i
    · subst h; simp [σ0, pad, rowmap, hσ e]
    · simp [σ0, h]
  have hslot : ∑ c, (if σ0 (ℓ := ℓ) σs (Sum.inr (Sum.inl c)) = i then
      pad K κ t i (Sum.inr (Sum.inl c)) else 0) = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases c with ⟨⟨p, b, a, d⟩, k⟩
    have hp := p.2
    cases b
    · by_cases h : p.1.1 = i
      · subst h; simp [σ0, pad, rowmap, slotVal, tyv1]
      · simp [σ0, h]
    · by_cases h : p.1.2 = i
      · subst h; simp [σ0, pad, rowmap, slotVal, tyv2, ne_of_gt hp]
      · simp [σ0, h]
  have hunit : ∑ u : Unit, (if σ0 (ℓ := ℓ) (K := K) σs (Sum.inr (Sum.inr u)) = i then
      pad K κ t i (Sum.inr (Sum.inr u)) else 0) ≤ βc K := by
    simp only [Finset.univ_unique, Finset.sum_singleton]
    split_ifs
    · simp [pad, rowmap]
    · exact (βc_pos K).le
  have hle : ∑ e ∈ Finset.univ.filter (fun e => σs e = i), t i e ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => ∑ j ∈ Finset.univ.filter (fun j => σs j = i), t i j) :=
    Finset.le_sup' (fun i => ∑ j ∈ Finset.univ.filter (fun j => σs j = i), t i j)
      (Finset.mem_univ i)
  rw [hcore, Fintype.sum_sum_type, hslot]
  linarith

theorem C_attained (t : Fin n → CoreTask n ℓ → ℝ) :
    ∃ σs : CoreTask n ℓ → Fin n, (∀ e, incident (σs e) e) ∧ C t = schedMakespan t σs := by
  unfold C
  generalize_proofs hne
  obtain ⟨σ, hσ, h⟩ := Finset.exists_mem_eq_inf' hne (fun σ => schedMakespan t σ)
  exact ⟨σ, (Finset.mem_filter.1 hσ).2, h⟩

theorem pad_opt (κ : Idx n K → ℕ) {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t)
    (π : Equiv.Perm (T n ℓ K)) :
    0 < opt (pre (Fintype.equivFin (T n ℓ K)) (relabel π (pad K κ t))) ∧
      opt (pre (Fintype.equivFin (T n ℓ K)) (relabel π (pad K κ t))) ≤ C t + βc K := by
  set g : Fin (Fintype.card (T n ℓ K)) ≃ T n ℓ K := (Fintype.equivFin (T n ℓ K)).symm.trans π
  have hdef : pre (Fintype.equivFin (T n ℓ K)) (relabel π (pad K κ t)) =
      fun i k => pad K κ t i (g k) := rfl
  rw [hdef]
  constructor
  · refine opt_pos_of _ (fun i k => pad_nonneg κ ht i _) (g.symm (Sum.inr (Sum.inr ())))
      (βc K) (βc_pos K) fun i => ?_
    simp [pad, rowmap]
  · obtain ⟨σs, hσ, hC⟩ := C_attained t
    rw [hC]
    exact (opt_comp_le g _ (σ0 σs)).trans (sched_pad_le κ σs hσ)

end PadOpt

section PadLoad
variable [NeZero n] (R : (m : ℕ) → FracMech n (Fin m)) {ℓ : ℕ}

theorem pad_load (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (K : ℕ) {ρ' : ℝ} (hρ' : Valid R ρ')
    (κ : Idx n K → ℕ) {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t) (i : Fin n) :
    ∑ a, pad K κ t i a * (Xs R ℓ K).x (pad K κ t) i a ≤ ρ' * (C t + βc K) :=
  Xs_load_of R hfeas K hρ' _ (pad_nonneg κ ht) _ (fun π => pad_opt κ ht π.1) i

end PadLoad

/-! ### Averages -/
section Avg
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem card_pos_real : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos

theorem avg_le (f : ι → ℝ) (c : ℝ) (h : ∀ k, f k ≤ c) :
    (1 / (Fintype.card ι : ℝ)) * ∑ k, f k ≤ c := by
  have hc := card_pos_real (ι := ι)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hc]
  calc ∑ k, f k ≤ ∑ _k : ι, c := Finset.sum_le_sum fun k _ => h k
    _ = c * Fintype.card ι := by simp [mul_comm]

theorem le_avg (f : ι → ℝ) (c : ℝ) (h : ∀ k, c ≤ f k) :
    c ≤ (1 / (Fintype.card ι : ℝ)) * ∑ k, f k := by
  have hc := card_pos_real (ι := ι)
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
  calc c * Fintype.card ι = ∑ _k : ι, c := by simp [mul_comm]
    _ ≤ ∑ k, f k := Finset.sum_le_sum fun k _ => h k

theorem avg_const (c : ℝ) : (1 / (Fintype.card ι : ℝ)) * ∑ _k : ι, c = c := by
  have hc := card_pos_real (ι := ι)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

end Avg

/-! ### The stage-`K` mechanism -/
section Stage
variable [NeZero n] (R : (m : ℕ) → FracMech n (Fin m)) {ℓ : ℕ}

abbrev Box (n K : ℕ) := Idx n K → Fin (K + 2)

def cnt {K : ℕ} (κ : Box n K) : Idx n K → ℕ := fun c => K + 1 + (κ c : ℕ)

def fixedW {K : ℕ} (i : Fin n) : T n ℓ K → ℝ
  | .inl e => if incident i e then 0 else 1
  | _ => 1

theorem fixedW_nonneg {K : ℕ} (i : Fin n) (a : T n ℓ K) : 0 ≤ fixedW i a := by
  rcases a with e | c
  · simp only [fixedW]; split_ifs <;> norm_num
  · simp [fixedW]

noncomputable def stageM (ℓ K : ℕ) : FracMech n (CoreTask n ℓ) where
  x t i e := (1 / (Fintype.card (Box n K) : ℝ)) *
    ∑ κ : Box n K, (Xs R ℓ K).x (pad K (cnt κ) t) i (.inl e)
  P t i := (1 / (Fintype.card (Box n K) : ℝ)) *
    ∑ κ : Box n K, ((Xs R ℓ K).P (pad K (cnt κ) t) i -
      ∑ a, fixedW i a * pad K (cnt κ) t i a * (Xs R ℓ K).x (pad K (cnt κ) t) i a)

variable {K : ℕ}

theorem sum_T (f : T n ℓ K → ℝ) : ∑ a, f a = ∑ e, f (.inl e) + ∑ c, f (.inr c) :=
  Fintype.sum_sum_type f

def Vanish (i : Fin n) (r : CoreTask n ℓ → ℝ) : Prop := ∀ e, ¬ incident i e → r e = 0

theorem key_split (κ : Idx n K → ℕ) (i : Fin n) {r : CoreTask n ℓ → ℝ} (hr : Vanish i r)
    (X : T n ℓ K → ℝ) :
    ∑ a, rowmap K κ i r a * X a =
      ∑ e, r e * X (.inl e) + ∑ a, fixedW i a * rowmap K κ i r a * X a := by
  rw [sum_T, sum_T, ← add_assoc]
  congr 1
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : incident i e
    · simp [rowmap, fixedW, h]
    · simp [rowmap, fixedW, h, hr e h]
  · simp [fixedW]

theorem fixed_indep (κ : Idx n K → ℕ) (i : Fin n) {r q : CoreTask n ℓ → ℝ} (hr : Vanish i r)
    (hq : Vanish i q) (X : T n ℓ K → ℝ) :
    ∑ a, fixedW i a * rowmap K κ i q a * X a = ∑ a, fixedW i a * rowmap K κ i r a * X a := by
  rw [sum_T, sum_T]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : incident i e
  · simp [fixedW, h]
  · simp [rowmap, fixedW, h, hr e h, hq e h]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rcases c with c | u <;> rfl

theorem gi_vanish {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t) (i : Fin n) :
    Vanish i (t i) := fun e h => (ht i e).2 h

theorem stage_cost (t : Fin n → CoreTask n ℓ → ℝ) (i : Fin n) (r : CoreTask n ℓ → ℝ) :
    ∑ e, r e * (stageM R ℓ K).x t i e = (1 / (Fintype.card (Box n K) : ℝ)) *
      ∑ κ : Box n K, ∑ e, r e * (Xs R ℓ K).x (pad K (cnt κ) t) i (.inl e) := by
  simp only [stageM, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem stage_feasible (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (K : ℕ) :
    IsFeasibleOn IsGraphInput (stageM R ℓ K) := by
  intro t ht
  have hX := fun κ : Box n K => Xs_feasible R hfeas K (pad K (cnt κ) t) (pad_nonneg _ ht)
  refine ⟨fun i e => ⟨le_avg _ _ fun κ => ((hX κ).1 i _).1,
    avg_le _ _ fun κ => ((hX κ).1 i _).2⟩, fun e => ?_⟩
  simp only [stageM]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [fun κ : Box n K => (hX κ).2 (.inl e)]
  exact avg_const 1

theorem stage_truthful (htruth : ∀ m, IsTruthfulOn Nonneg (R m)) (K : ℕ) :
    IsTruthfulOn IsGraphInput (stageM R ℓ K) := by
  intro t ht i b hb
  have hvb : Vanish i b := by
    intro e he
    have := (hb i e).2 he
    simpa using this
  rw [stage_cost, stage_cost]
  simp only [stageM]
  rw [← mul_sub, ← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun κ _ => ?_) (by positivity)
  set s := pad K (cnt κ) t
  have hs' : pad K (cnt κ) (Function.update t i b) = Function.update s i (rowmap K (cnt κ) i b) :=
    pad_update _ t i b
  have key := Xs_truthful R htruth K s (pad_nonneg _ ht) i (rowmap K (cnt κ) i b)
    (by rw [← hs']; exact pad_nonneg _ hb)
  rw [hs']
  have e1 := key_split (cnt κ) i (gi_vanish ht i)
    ((Xs R ℓ K).x (Function.update s i (rowmap K (cnt κ) i b)) i)
  have e2 := key_split (cnt κ) i (gi_vanish ht i) ((Xs R ℓ K).x s i)
  have e3 := fixed_indep (cnt κ) i (gi_vanish ht i) hvb
    ((Xs R ℓ K).x (Function.update s i (rowmap K (cnt κ) i b)) i)
  simp only [Function.update_self]
  have hsi : s i = rowmap K (cnt κ) i (t i) := rfl
  simp only [hsi] at key e2 ⊢
  rw [e3]
  linarith

theorem stage_load (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (K : ℕ) {ρ' : ℝ} (hρ' : Valid R ρ')
    {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t) (i : Fin n) :
    ∑ e, t i e * (stageM R ℓ K).x t i e ≤ ρ' * (C t + βc K) := by
  rw [stage_cost]
  refine avg_le _ _ fun κ => ?_
  have hX := Xs_feasible R hfeas K (pad K (cnt κ) t) (pad_nonneg _ ht)
  have e := key_split (cnt κ) i (gi_vanish ht i) ((Xs R ℓ K).x (pad K (cnt κ) t) i)
  have hF : 0 ≤ ∑ a, fixedW i a * rowmap K (cnt κ) i (t i) a * (Xs R ℓ K).x (pad K (cnt κ) t) i a :=
    Finset.sum_nonneg fun a _ => mul_nonneg (mul_nonneg (fixedW_nonneg i a)
      (pad_nonneg _ ht i a)) ((hX.1 i a).1)
  have hL := pad_load R hfeas K hρ' (cnt κ) ht i
  have hsi : pad K (cnt κ) t i = rowmap K (cnt κ) i (t i) := rfl
  rw [hsi] at hL
  linarith

theorem stage_elig (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (K : ℕ) {ρ : ℝ} (hρ : Valid R ρ)
    {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t) (i : Fin n) (e : CoreTask n ℓ)
    (he : ¬ incident i e) :
    (stageM R ℓ K).x t i e ≤ ρ * (C t + βc K) / Hc K := by
  refine avg_le _ _ fun κ => ?_
  have hX := Xs_feasible R hfeas K (pad K (cnt κ) t) (pad_nonneg _ ht)
  have hL := pad_load R hfeas K hρ (cnt κ) ht i
  have h1 : pad K (cnt κ) t i (.inl e) * (Xs R ℓ K).x (pad K (cnt κ) t) i (.inl e) ≤
      ∑ a, pad K (cnt κ) t i a * (Xs R ℓ K).x (pad K (cnt κ) t) i a :=
    Finset.single_le_sum (f := fun a => pad K (cnt κ) t i a * (Xs R ℓ K).x (pad K (cnt κ) t) i a)
      (fun a _ => mul_nonneg (pad_nonneg _ ht i a) (hX.1 i a).1) (Finset.mem_univ _)
  have h2 : pad K (cnt κ) t i (.inl e) = Hc K := by
    simp [pad, rowmap, he, (ht i e).2 he]
  rw [h2] at h1
  rw [le_div_iff₀ (Hc_pos K)]
  linarith

end Stage

/-! ### Class symmetry -/
section Symmetry
variable [NeZero n] (R : (m : ℕ) → FracMech n (Fin m)) {ℓ K : ℕ}

theorem incident_classPerm {γ : Equiv.Perm (CoreTask n ℓ)} (hγ : IsClassPerm γ) (j : Fin n)
    (e : CoreTask n ℓ) : incident j (γ e) ↔ incident j e := by
  rcases e with ⟨p, k⟩ | k
  · obtain ⟨k', hk'⟩ := hγ.1 p k
    rw [hk']; simp [incident]
  · rw [hγ.2 k]

def extT (K : ℕ) (γ : Equiv.Perm (CoreTask n ℓ)) : Equiv.Perm (T n ℓ K) :=
  Equiv.sumCongr γ (Equiv.refl _)

theorem extT_mem {γ : Equiv.Perm (CoreTask n ℓ)} (hγ : IsClassPerm γ) : extT K γ ∈ G n ℓ K := by
  rw [mem_G]
  rintro ((⟨p, k⟩ | i) | c)
  · obtain ⟨k', hk'⟩ := hγ.1 p k
    simp [extT, hk', lab]
  · simp [extT, hγ.2 i, lab]
  · simp [extT]

theorem relabel_pad {γ : Equiv.Perm (CoreTask n ℓ)} (hγ : IsClassPerm γ) (κ : Idx n K → ℕ)
    (t : Fin n → CoreTask n ℓ → ℝ) :
    relabel (extT K γ) (pad K κ t) = pad K κ (relabel γ t) := by
  funext i a
  rcases a with e | c
  · simp [relabel, extT, pad, rowmap, incident_classPerm hγ]
  · rcases c with c | u <;> rfl

theorem fixedW_ext {γ : Equiv.Perm (CoreTask n ℓ)} (hγ : IsClassPerm γ) (i : Fin n)
    (a : T n ℓ K) : fixedW i (extT K γ a) = fixedW i a := by
  rcases a with e | c
  · simp [extT, fixedW, incident_classPerm hγ]
  · simp [extT, fixedW]

theorem stage_x_relabel {γ : Equiv.Perm (CoreTask n ℓ)} (hγ : IsClassPerm γ)
    (t : Fin n → CoreTask n ℓ → ℝ) (i : Fin n) (e : CoreTask n ℓ) :
    (stageM R ℓ K).x (relabel γ t) i e = (stageM R ℓ K).x t i (γ e) := by
  simp only [stageM]
  congr 1
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [← relabel_pad hγ, (Xs_equivariant R K (extT_mem hγ) _ i _).1]
  rfl

theorem stage_P_relabel {γ : Equiv.Perm (CoreTask n ℓ)} (hγ : IsClassPerm γ)
    (t : Fin n → CoreTask n ℓ → ℝ) (i : Fin n) :
    (stageM R ℓ K).P (relabel γ t) i = (stageM R ℓ K).P t i := by
  simp only [stageM]
  congr 1
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [← relabel_pad hγ, (Xs_equivariant R K (extT_mem hγ) _ i (Sum.inr (Sum.inr ()))).2]
  congr 1
  rw [← Equiv.sum_comp (extT K γ)
    (fun a => fixedW i a * pad K (cnt κ) t i a * (Xs R ℓ K).x (pad K (cnt κ) t) i a)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [(Xs_equivariant R K (extT_mem hγ) _ i a).1, fixedW_ext hγ]
  rfl

theorem stage_symmetric (K : ℕ) : IsClassSymmetric (stageM R ℓ K) := by
  intro γ hγ t ht
  refine ⟨fun i e => stage_x_relabel R hγ t i e, fun i => ?_⟩
  unfold disutility
  have hu : Function.update (relabel γ t) i 0 = relabel γ (Function.update t i 0) := by
    rw [relabel_update]; rfl
  rw [hu, stage_P_relabel R hγ, stage_P_relabel R hγ]
  congr 2
  rw [← Equiv.sum_comp γ (fun e => t i e * (stageM R ℓ K).x t i e)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [stage_x_relabel R hγ]
  rfl

end Symmetry

/-! ### Zero types -/
section Types
variable {K : ℕ}

theorem rat_type (q : ℚ) (hq : 0 ≤ q) (b : Bool) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∃ τ : Ty K, rval τ = q ∧ τ.1 = b := by
  refine ⟨q.num.toNat + q.den, fun K hK => ⟨(b, ⟨q.num.toNat, by omega⟩, ⟨q.den - 1, by omega⟩),
    ?_, rfl⟩⟩
  have hnum : (0 : ℤ) ≤ q.num := Rat.num_nonneg.2 hq
  have hden : 1 ≤ q.den := q.den_pos
  simp only [rval]
  rw [Rat.cast_def]
  congr 1
  · have : ((q.num.toNat : ℤ) : ℝ) = (q.num : ℝ) := by rw [Int.toNat_of_nonneg hnum]
    exact_mod_cast this
  · rw [Nat.cast_sub hden]; simp

theorem zero_type (x1 x2 : ℝ) (h : x1 = 0 ∨ x2 = 0) (h1 : 0 ≤ x1) (h2 : 0 ≤ x2)
    (hr1 : ∃ q : ℚ, x1 = q) (hr2 : ∃ q : ℚ, x2 = q) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∃ τ : Ty K, tyv1 τ = x1 ∧ tyv2 τ = x2 := by
  rcases h with h | h
  · obtain ⟨q, rfl⟩ := hr2
    obtain ⟨K₀, hK₀⟩ := rat_type q (by exact_mod_cast h2) false
    refine ⟨K₀, fun K hK => ?_⟩
    obtain ⟨τ, hτ, hb⟩ := hK₀ K hK
    exact ⟨τ, by simp [tyv1, hb, h], by simp [tyv2, hb, hτ]⟩
  · obtain ⟨q, rfl⟩ := hr1
    obtain ⟨K₀, hK₀⟩ := rat_type q (by exact_mod_cast h1) true
    refine ⟨K₀, fun K hK => ?_⟩
    obtain ⟨τ, hτ, hb⟩ := hK₀ K hK
    exact ⟨τ, by simp [tyv1, hb, hτ], by simp [tyv2, hb, h]⟩

end Types

/-! ### Reservoir copies -/
section Copies
variable [NeZero n] {ℓ K : ℕ}

theorem slot_eq_core (κ : Idx n K → ℕ) {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t)
    (p : Pair n) (k0 : Fin ℓ) (τ : Ty K) (h1 : tyv1 τ = t p.1.1 (.inl (p, k0)))
    (h2 : tyv2 τ = t p.1.2 (.inl (p, k0))) (m : Fin (2 * K + 4)) (hm : (m : ℕ) < κ (p, τ))
    (u : Fin n) :
    pad K κ t u (.inr (.inl ((p, τ), m))) = pad K κ t u (.inl (.inl (p, k0))) := by
  simp only [pad, rowmap, slotVal, if_pos hm]
  by_cases hu1 : u = p.1.1
  · subst hu1; simp [incident, h1]
  · by_cases hu2 : u = p.1.2
    · subst hu2; simp [incident, h2, hu1]
    · have hni : ¬ incident u (Sum.inl (p, k0) : CoreTask n ℓ) := by
        simp [incident, hu1, hu2]
      simp [hu1, hu2, hni, (ht u _).2 hni]

theorem swap_mem_G {a b : T n ℓ K} (h : lab a = lab b) : Equiv.swap a b ∈ G n ℓ K := by
  rw [mem_G]
  intro x
  rcases eq_or_ne x a with rfl | hxa
  · simp [h]
  · rcases eq_or_ne x b with rfl | hxb
    · simp [h]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem relabel_swap_eq {s : Fin n → T n ℓ K → ℝ} {a b : T n ℓ K} (h : ∀ u, s u a = s u b) :
    relabel (Equiv.swap a b) s = s := by
  funext u x
  simp only [relabel]
  rcases eq_or_ne x a with rfl | hxa
  · simp [h]
  · rcases eq_or_ne x b with rfl | hxb
    · simp [h]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

theorem sum_range_ite (c0 : ℝ) (K : ℕ) :
    ∑ m : Fin (2 * K + 4), (if (m : ℕ) < K + 1 then c0 else 0) = (K + 1) * c0 := by
  rw [Fin.sum_univ_eq_sum_range (fun m => if m < K + 1 then c0 else 0) (2 * K + 4)]
  rw [show 2 * K + 4 = (K + 1) + (K + 3) by ring, Finset.sum_range_add]
  rw [Finset.sum_congr rfl (g := fun _ => c0) (fun m hm => if_pos (Finset.mem_range.1 hm))]
  rw [Finset.sum_congr rfl (g := fun _ => (0 : ℝ)) (fun m hm => if_neg (by omega))]
  simp

end Copies

/-! ### Unique zeros -/
section UZ
variable [NeZero n] (R : (m : ℕ) → FracMech n (Fin m)) {ℓ K : ℕ}

theorem stage_uz (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) {ρ : ℝ} (hρ : Valid R ρ)
    {t : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t) (p : Pair n) (k0 : Fin ℓ) (τ : Ty K)
    (h1 : tyv1 τ = t p.1.1 (.inl (p, k0))) (h2 : tyv2 τ = t p.1.2 (.inl (p, k0)))
    (j : Fin n) (hj : incident j (Sum.inl (p, k0) : CoreTask n ℓ))
    (htj : 0 < t j (.inl (p, k0))) :
    (stageM R ℓ K).x t j (.inl (p, k0)) ≤
      ρ * (C t + βc K) / (((K : ℝ) + 2) * t j (.inl (p, k0))) := by
  refine avg_le _ _ fun κ => ?_
  set s := pad K (cnt κ) t with hs
  set E : T n ℓ K := Sum.inl (Sum.inl (p, k0))
  set X := (Xs R ℓ K).x s j
  have hX := Xs_feasible R hfeas K s (pad_nonneg _ ht)
  have hsE : s j E = t j (.inl (p, k0)) := by simp [hs, E, pad, rowmap, hj]
  -- every active copy carries the same value and the same allocation as `E`
  have hcopy : ∀ m : Fin (2 * K + 4), (m : ℕ) < K + 1 →
      s j (.inr (.inl ((p, τ), m))) * X (.inr (.inl ((p, τ), m))) =
        t j (.inl (p, k0)) * X E := by
    intro m hm
    have hm' : (m : ℕ) < cnt κ (p, τ) := by simp only [cnt]; omega
    have hval := slot_eq_core (cnt κ) ht p k0 τ h1 h2 m hm'
    have hlab : lab E = lab (Sum.inr (Sum.inl ((p, τ), m)) : T n ℓ K) := rfl
    have hrel := relabel_swap_eq (s := s) (a := E) (b := .inr (.inl ((p, τ), m)))
      (fun u => (hval u).symm)
    have hx := (Xs_equivariant R K (swap_mem_G hlab) s j E).1
    rw [hrel, Equiv.swap_apply_left] at hx
    rw [show s j (.inr (.inl ((p, τ), m))) = s j E from hval j, hsE]
    show _ * (Xs R ℓ K).x s j _ = _ * (Xs R ℓ K).x s j E
    rw [← hx]
  have hF : ∀ a, 0 ≤ s j a * X a := fun a => mul_nonneg (pad_nonneg _ ht j a) (hX.1 j a).1
  have hlow : ((K : ℝ) + 2) * (t j (.inl (p, k0)) * X E) ≤ ∑ a, s j a * X a := by
    rw [sum_T]
    have hA : s j E * X E ≤ ∑ e, s j (.inl e) * X (.inl e) :=
      Finset.single_le_sum (f := fun e => s j (.inl e) * X (.inl e)) (fun e _ => hF _)
        (Finset.mem_univ (Sum.inl (p, k0)))
    have hB : ∑ m : Fin (2 * K + 4), s j (.inr (.inl ((p, τ), m))) * X (.inr (.inl ((p, τ), m)))
        ≤ ∑ c, s j (.inr c) * X (.inr c) := by
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      have hu : 0 ≤ ∑ u : Unit, s j (.inr (.inr u)) * X (.inr (.inr u)) :=
        Finset.sum_nonneg fun _ _ => hF _
      have hi := Finset.single_le_sum
        (f := fun c : Idx n K => ∑ m : Fin (2 * K + 4), s j (.inr (.inl (c, m))) *
          X (.inr (.inl (c, m))))
        (fun c _ => Finset.sum_nonneg fun _ _ => hF _) (Finset.mem_univ (p, τ))
      linarith
    have hC : ((K : ℝ) + 1) * (t j (.inl (p, k0)) * X E) ≤
        ∑ m : Fin (2 * K + 4), s j (.inr (.inl ((p, τ), m))) * X (.inr (.inl ((p, τ), m))) := by
      rw [← sum_range_ite]
      refine Finset.sum_le_sum fun m _ => ?_
      split_ifs with hm
      · rw [hcopy m hm]
      · exact hF _
    rw [hsE] at hA
    linarith
  have hL := pad_load R hfeas K hρ (cnt κ) ht j
  have hpos : 0 < ((K : ℝ) + 2) * t j (.inl (p, k0)) := by positivity
  rw [le_div_iff₀ hpos]
  show X E * _ ≤ _
  nlinarith [hlow, hL]

end UZ

/-! ### Shifting a box average by a unit vector -/
section Shift
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem shift_avg (K : ℕ) (ψ : (ι → ℕ) → ℝ) (hψ : ∀ μ, 0 ≤ ψ μ ∧ ψ μ ≤ 1) (c : ι) :
    |(1 / (Fintype.card (ι → Fin (K + 2)) : ℝ)) *
        ∑ κ : ι → Fin (K + 2), ψ (Function.update (fun x => K + 1 + (κ x : ℕ)) c
          (K + 1 + (κ c : ℕ) + 1)) -
      (1 / (Fintype.card (ι → Fin (K + 2)) : ℝ)) *
        ∑ κ : ι → Fin (K + 2), ψ (fun x => K + 1 + (κ x : ℕ))| ≤ 1 / ((K : ℝ) + 2) := by
  set W := {j // j ≠ c} → Fin (K + 2)
  set e := Equiv.funSplitAt c (Fin (K + 2))
  set h : W → ℕ → ℝ := fun w v =>
    ψ (fun x => if hx : x = c then K + 1 + v else K + 1 + (w ⟨x, hx⟩ : ℕ))
  have hcard : (Fintype.card (ι → Fin (K + 2)) : ℝ) = ((K : ℝ) + 2) * Fintype.card W := by
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin]; push_cast; ring
  have hW : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hsplit : ∀ F : (ι → Fin (K + 2)) → ℝ,
      ∑ κ, F κ = ∑ w : W, ∑ v : Fin (K + 2), F (e.symm (v, w)) := by
    intro F
    rw [Fintype.sum_equiv e F (fun vw => F (e.symm vw)) (fun x => by simp),
      Fintype.sum_prod_type, Finset.sum_comm]
  have hg : ∀ (v : Fin (K + 2)) (w : W),
      (fun x => K + 1 + ((e.symm (v, w)) x : ℕ)) =
        (fun x => if hx : x = c then K + 1 + (v : ℕ) else K + 1 + (w ⟨x, hx⟩ : ℕ)) := by
    intro v w; funext x
    by_cases hx : x = c
    · subst hx; simp [e]
    · simp [e, hx]
  have hf : ∀ (v : Fin (K + 2)) (w : W),
      Function.update (fun x => K + 1 + ((e.symm (v, w)) x : ℕ)) c
          (K + 1 + ((e.symm (v, w)) c : ℕ) + 1) =
        (fun x => if hx : x = c then K + 1 + ((v : ℕ) + 1) else K + 1 + (w ⟨x, hx⟩ : ℕ)) := by
    intro v w; funext x
    by_cases hx : x = c
    · subst hx; simp [e]; ring
    · simp [e, hx]
  rw [← mul_sub, hsplit, hsplit, ← Finset.sum_sub_distrib]
  have htel : ∀ w : W, ∑ v : Fin (K + 2),
      (ψ (Function.update (fun x => K + 1 + ((e.symm (v, w)) x : ℕ)) c
        (K + 1 + ((e.symm (v, w)) c : ℕ) + 1)) - ψ (fun x => K + 1 + ((e.symm (v, w)) x : ℕ))) =
        h w (K + 2) - h w 0 := by
    intro w
    rw [Finset.sum_congr rfl (g := fun v : Fin (K + 2) => h w ((v : ℕ) + 1) - h w v)
      (fun v _ => by rw [hf, hg])]
    rw [Fin.sum_univ_eq_sum_range (fun v => h w (v + 1) - h w v) (K + 2),
      Finset.sum_range_sub (h w)]
  rw [Finset.sum_congr rfl fun w _ => (Finset.sum_sub_distrib _ _).symm.trans (htel w)]
  rw [abs_mul, hcard]
  have hb : |∑ w : W, (h w (K + 2) - h w 0)| ≤ Fintype.card W := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : W, |h w (K + 2) - h w 0| ≤ ∑ _w : W, (1 : ℝ) := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [abs_le]
          constructor <;> linarith [(hψ (fun x => if hx : x = c then K + 1 + (K + 2) else
            K + 1 + (w ⟨x, hx⟩ : ℕ))).1, (hψ (fun x => if hx : x = c then K + 1 + (K + 2) else
            K + 1 + (w ⟨x, hx⟩ : ℕ))).2, (hψ (fun x => if hx : x = c then K + 1 + 0 else
            K + 1 + (w ⟨x, hx⟩ : ℕ))).1, (hψ (fun x => if hx : x = c then K + 1 + 0 else
            K + 1 + (w ⟨x, hx⟩ : ℕ))).2]
      _ = Fintype.card W := by simp
  have h1 : |1 / (((K : ℝ) + 2) * Fintype.card W)| = 1 / (((K : ℝ) + 2) * Fintype.card W) :=
    abs_of_pos (by positivity)
  rw [h1]
  calc 1 / (((K : ℝ) + 2) * Fintype.card W) * |∑ w : W, (h w (K + 2) - h w 0)|
      ≤ 1 / (((K : ℝ) + 2) * Fintype.card W) * Fintype.card W :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 / ((K : ℝ) + 2) := by field_simp

end Shift

/-! ### Zero-type irrelevance -/
section ZTI
variable [NeZero n] (R : (m : ℕ) → FracMech n (Fin m)) {ℓ K : ℕ}

theorem slotVal_congr {κ κ' : Idx n K → ℕ} (v : Fin n) (c : Res n K)
    (h : (c.2 : ℕ) < κ' c.1 ↔ (c.2 : ℕ) < κ c.1) : slotVal K κ' v c = slotVal K κ v c := by
  unfold slotVal
  by_cases h' : (c.2 : ℕ) < κ c.1
  · rw [if_pos (h.2 h'), if_pos h']
  · rw [if_neg (fun hh => h' (h.1 hh)), if_neg h']

def shiftκ (cτ cσ : Idx n K) (κ : Idx n K → ℕ) : Idx n K → ℕ :=
  Function.update (Function.update κ cτ (κ cτ + 1)) cσ (κ cσ - 1)

theorem cycle_eq (κ : Idx n K → ℕ) {t t' : Fin n → CoreTask n ℓ → ℝ} (ht : IsGraphInput t)
    (ht' : IsGraphInput t') (p : Pair n) (k0 : Fin ℓ)
    (hagree : ∀ u f, f ≠ (Sum.inl (p, k0) : CoreTask n ℓ) → t u f = t' u f)
    (τ σ : Ty K) (hτσ : τ ≠ σ)
    (hτ1 : tyv1 τ = t p.1.1 (.inl (p, k0))) (hτ2 : tyv2 τ = t p.1.2 (.inl (p, k0)))
    (hσ1 : tyv1 σ = t' p.1.1 (.inl (p, k0))) (hσ2 : tyv2 σ = t' p.1.2 (.inl (p, k0)))
    (hτlt : κ (p, τ) < 2 * K + 4) (hσlt : κ (p, σ) < 2 * K + 4) (hσpos : 1 ≤ κ (p, σ))
    (u : Fin n) (f : CoreTask n ℓ) (hf : f ≠ .inl (p, k0)) :
    (Xs R ℓ K).x (pad K κ t) u (.inl f) =
      (Xs R ℓ K).x (pad K (shiftκ (p, τ) (p, σ) κ) t') u (.inl f) := by
  set E : T n ℓ K := .inl (.inl (p, k0)) with hEdef
  set Sτ : T n ℓ K := .inr (.inl ((p, τ), ⟨κ (p, τ), hτlt⟩)) with hSτdef
  set Sσ : T n ℓ K := .inr (.inl ((p, σ), ⟨κ (p, σ) - 1, by omega⟩)) with hSσdef
  set κ' := shiftκ (p, τ) (p, σ) κ with hκ'def
  have hne : (p, τ) ≠ (p, σ) := fun h => hτσ (Prod.ext_iff.1 h).2
  have hκ'τ : κ' (p, τ) = κ (p, τ) + 1 := by
    simp [κ', shiftκ, Function.update_of_ne hne]
  have hκ'σ : κ' (p, σ) = κ (p, σ) - 1 := by simp [κ', shiftκ]
  have hκ'o : ∀ c, c ≠ (p, τ) → c ≠ (p, σ) → κ' c = κ c := by
    intro c h1 h2; simp [κ', shiftκ, Function.update_of_ne h1, Function.update_of_ne h2]
  have hESτ : E ≠ Sτ := Sum.inl_ne_inr
  have hESσ : E ≠ Sσ := Sum.inl_ne_inr
  have hSτσ : Sτ ≠ Sσ := by
    intro h
    simp only [Sτ, Sσ, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
    exact hτσ h.1.2
  set γ := Equiv.swap E Sσ * Equiv.swap E Sτ with hγdef
  have hγ : γ ∈ G n ℓ K := mul_mem (swap_mem_G rfl) (swap_mem_G rfl)
  have γE : γ E = Sτ := by
    simp only [γ, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hESτ.symm hSτσ
  have γSσ : γ Sσ = E := by
    simp only [γ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hESσ.symm hSτσ.symm, Equiv.swap_apply_right]
  have γSτ : γ Sτ = Sσ := by
    simp only [γ, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  have γo : ∀ a, a ≠ E → a ≠ Sτ → a ≠ Sσ → γ a = a := by
    intro a h1 h2 h3
    simp only [γ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h1 h3]
  have hrel : relabel γ (pad K κ' t') = pad K κ t := by
    funext v a
    simp only [relabel]
    rcases eq_or_ne a E with rfl | haE
    · rw [γE]
      calc pad K κ' t' v Sτ = pad K κ' t v Sτ := rfl
        _ = pad K κ' t v E :=
          slot_eq_core κ' ht p k0 τ hτ1 hτ2 _ (by simp only [hκ'τ]; omega) v
        _ = pad K κ t v E := rfl
    rcases eq_or_ne a Sσ with rfl | haσ
    · rw [γSσ]
      calc pad K κ' t' v E = pad K κ t' v E := rfl
        _ = pad K κ t' v Sσ :=
          (slot_eq_core κ ht' p k0 σ hσ1 hσ2 _ (by simp only; omega) v).symm
        _ = pad K κ t v Sσ := rfl
    rcases eq_or_ne a Sτ with rfl | haτ
    · rw [γSτ]
      simp [Sσ, Sτ, pad, rowmap, slotVal, hκ'σ]
    rw [γo a haE haτ haσ]
    rcases a with g | (⟨cc, m⟩ | w)
    · have hg : g ≠ .inl (p, k0) := fun h => haE (by rw [h])
      simp only [pad, rowmap, hagree v g hg]
    · show slotVal K κ' v (cc, m) = slotVal K κ v (cc, m)
      refine slotVal_congr v (cc, m) ?_
      simp only
      by_cases h1 : cc = (p, τ)
      · subst h1
        have hm : (m : ℕ) ≠ κ (p, τ) := fun hm => haτ (by rw [hSτdef]; congr 3; exact Fin.ext hm)
        rw [hκ'τ]; omega
      · by_cases h2 : cc = (p, σ)
        · subst h2
          have hm : (m : ℕ) ≠ κ (p, σ) - 1 :=
            fun hm => haσ (by rw [hSσdef]; congr 3; exact Fin.ext hm)
          rw [hκ'σ]; omega
        · rw [hκ'o cc h1 h2]
    · rfl
  have hx := (Xs_equivariant R K hγ (pad K κ' t') u (.inl f)).1
  rw [hrel] at hx
  rw [hx, γo _ (fun h => hf (Sum.inl_injective h)) Sum.inl_ne_inr Sum.inl_ne_inr]

theorem stage_zti (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) {t t' : Fin n → CoreTask n ℓ → ℝ}
    (ht : IsGraphInput t) (ht' : IsGraphInput t') (p : Pair n) (k0 : Fin ℓ)
    (hagree : ∀ u f, f ≠ (Sum.inl (p, k0) : CoreTask n ℓ) → t u f = t' u f)
    (τ σ : Ty K)
    (hτ1 : tyv1 τ = t p.1.1 (.inl (p, k0))) (hτ2 : tyv2 τ = t p.1.2 (.inl (p, k0)))
    (hσ1 : tyv1 σ = t' p.1.1 (.inl (p, k0))) (hσ2 : tyv2 σ = t' p.1.2 (.inl (p, k0)))
    (u : Fin n) (f : CoreTask n ℓ) (hf : f ≠ .inl (p, k0)) :
    |(stageM R ℓ K).x t u f - (stageM R ℓ K).x t' u f| ≤ 4 / ((K : ℝ) + 2) := by
  have h4 : (0 : ℝ) ≤ 4 / ((K : ℝ) + 2) := by positivity
  by_cases hτσ : τ = σ
  · subst hτσ
    have htt : t = t' := by
      funext v g
      by_cases hg : g = .inl (p, k0)
      · subst hg
        by_cases hv1 : v = p.1.1
        · subst hv1; rw [← hτ1, hσ1]
        · by_cases hv2 : v = p.1.2
          · subst hv2; rw [← hτ2, hσ2]
          · have hni : ¬ incident v (Sum.inl (p, k0) : CoreTask n ℓ) := by
              simp [incident, hv1, hv2]
            rw [(ht v _).2 hni, (ht' v _).2 hni]
      · exact hagree v g hg
    subst htt
    simpa using h4
  have hne : (p, τ) ≠ (p, σ) := fun h => hτσ (Prod.ext_iff.1 h).2
  set φ : (Idx n K → ℕ) → ℝ := fun μ => (Xs R ℓ K).x (pad K μ t') u (.inl f)
  set ψ : (Idx n K → ℕ) → ℝ := fun ν => φ (Function.update ν (p, σ) (ν (p, σ) - 1))
  have hψ : ∀ μ, 0 ≤ ψ μ ∧ ψ μ ≤ 1 := fun μ =>
    (Xs_feasible R hfeas K _ (pad_nonneg _ ht')).1 u _
  have hA1 := shift_avg K ψ hψ (p, τ)
  have hA2 := shift_avg K ψ hψ (p, σ)
  have hx : (stageM R ℓ K).x t u f = (1 / (Fintype.card (Box n K) : ℝ)) *
      ∑ κ : Box n K, ψ (Function.update (fun x => K + 1 + (κ x : ℕ)) (p, τ)
        (K + 1 + (κ (p, τ) : ℕ) + 1)) := by
    simp only [stageM]
    congr 1
    refine Finset.sum_congr rfl fun κ _ => ?_
    have h1 := (κ (p, τ)).isLt
    have h2 := (κ (p, σ)).isLt
    rw [cycle_eq R (cnt κ) ht ht' p k0 hagree τ σ hτσ hτ1 hτ2 hσ1 hσ2
      (by simp only [cnt]; omega) (by simp only [cnt]; omega) (by simp only [cnt]; omega) u f hf]
    simp only [ψ, φ, shiftκ, Function.update_of_ne hne.symm]
    rfl
  have hx' : (stageM R ℓ K).x t' u f = (1 / (Fintype.card (Box n K) : ℝ)) *
      ∑ κ : Box n K, ψ (Function.update (fun x => K + 1 + (κ x : ℕ)) (p, σ)
        (K + 1 + (κ (p, σ) : ℕ) + 1)) := by
    simp only [stageM]
    congr 1
    refine Finset.sum_congr rfl fun κ _ => ?_
    simp only [ψ, φ, Function.update_self, Function.update_idem, Nat.add_sub_cancel]
    congr 2
    funext x
    by_cases hx : x = (p, σ)
    · subst hx; simp [cnt]
    · simp [cnt, Function.update_of_ne hx]
  rw [hx, hx']
  set A := (1 / (Fintype.card (Box n K) : ℝ)) *
      ∑ κ : Box n K, ψ (Function.update (fun x => K + 1 + (κ x : ℕ)) (p, τ)
        (K + 1 + (κ (p, τ) : ℕ) + 1))
  set B := (1 / (Fintype.card (Box n K) : ℝ)) *
      ∑ κ : Box n K, ψ (Function.update (fun x => K + 1 + (κ x : ℕ)) (p, σ)
        (K + 1 + (κ (p, σ) : ℕ) + 1))
  set D := (1 / (Fintype.card (Box n K) : ℝ)) * ∑ κ : Box n K, ψ (fun x => K + 1 + (κ x : ℕ))
  have hAD : |A - D| ≤ 1 / ((K : ℝ) + 2) := hA1
  have hBD : |B - D| ≤ 1 / ((K : ℝ) + 2) := hA2
  calc |A - B| = |(A - D) - (B - D)| := by ring_nf
    _ ≤ |A - D| + |B - D| := abs_sub _ _
    _ ≤ 1 / ((K : ℝ) + 2) + 1 / ((K : ℝ) + 2) := add_le_add hAD hBD
    _ ≤ 4 / ((K : ℝ) + 2) := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

end ZTI

end FracTruthSched.FTSPE

open FracTruthSched FracTruthSched.FTSPE in
theorem solution {n : ℕ} [NeZero n]
    (R : (m : ℕ) → FracMech n (Fin m))
    (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (htruth : ∀ m, IsTruthfulOn Nonneg (R m))
    (ρ : ℝ) (hρ : ∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
      makespan (R m) t ≤ ρ * opt t) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    Nonempty (PaddingSequence R ρ ℓ) := by
  refine ⟨{ M := fun K => stageM R ℓ K
            feasible := fun K => stage_feasible R hfeas K
            truthful := fun K => stage_truthful R htruth K
            symmetric := fun K => stage_symmetric R K
            load := ?_
            eligibility := ?_
            unique_zeros := ?_
            zero_type_irrelevance := ?_ }⟩
  · intro ρ' hρ' K t ht i
    exact stage_load R hfeas K hρ' ht i
  · intro K t ht i e he
    exact stage_elig R hfeas K hρ ht i e he
  · intro t ht e i j he hi hj hij hti htj
    rcases e with ⟨p, k0⟩ | k
    · have hz : t p.1.1 (.inl (p, k0)) = 0 ∨ t p.1.2 (.inl (p, k0)) = 0 := by
        simp only [incident] at hi
        rcases hi with h | h
        · left; rw [← h]; exact hti
        · right; rw [← h]; exact hti
      obtain ⟨K₀, hK₀⟩ := zero_type _ _ hz (ht.1 _ _).1 (ht.1 _ _).1 (ht.2 _ _) (ht.2 _ _)
      refine ⟨K₀, fun K hK => ?_⟩
      obtain ⟨τ, h1, h2⟩ := hK₀ K hK
      exact stage_uz R hfeas hρ ht.1 p k0 τ h1 h2 j hj htj
    · simp at he
  · intro t t' ht ht' e he hagree hz hz'
    rcases e with ⟨p, k0⟩ | k
    · have zt : ∀ s : Fin n → CoreTask n ℓ → ℝ, (∃ u, incident u (Sum.inl (p, k0) : CoreTask n ℓ)
          ∧ s u (.inl (p, k0)) = 0) → s p.1.1 (.inl (p, k0)) = 0 ∨ s p.1.2 (.inl (p, k0)) = 0 := by
        rintro s ⟨u, hu, h0⟩
        simp only [incident] at hu
        rcases hu with h | h
        · left; rw [← h]; exact h0
        · right; rw [← h]; exact h0
      obtain ⟨K₁, hK₁⟩ := zero_type _ _ (zt t hz) (ht.1 _ _).1 (ht.1 _ _).1 (ht.2 _ _) (ht.2 _ _)
      obtain ⟨K₂, hK₂⟩ := zero_type _ _ (zt t' hz') (ht'.1 _ _).1 (ht'.1 _ _).1 (ht'.2 _ _)
        (ht'.2 _ _)
      refine ⟨max K₁ K₂, fun K hK u f hf => ?_⟩
      obtain ⟨τ, h1, h2⟩ := hK₁ K (le_of_max_le_left hK)
      obtain ⟨σ, h3, h4⟩ := hK₂ K (le_of_max_le_right hK)
      exact stage_zti R hfeas ht.1 ht'.1 p k0 (fun u f hf => hagree u f hf) τ σ h1 h2 h3 h4 u f hf
    · simp at he
